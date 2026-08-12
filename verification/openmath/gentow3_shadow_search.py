#!/usr/bin/env python3
from __future__ import annotations

import ast
import contextlib
import copy
import dataclasses
import hashlib
import importlib
import inspect
import io
import itertools
import json
import os
import pprint
import subprocess
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[2]
READER_NAMES = (
    "gentow3_checks",
    "gentow3_pe1_fresh",
    "gentow3_pe2_fresh",
    "gentow3_pe3_fresh",
    "gentow3_pe5_fresh",
)
READER_PATHS = {
    name: ROOT / "verification" / "openmath" / f"{name}.py"
    for name in READER_NAMES
}
MODULE_PREFIX = ""
sys.path.insert(0, str(Path(__file__).resolve().parent))

INF = ("DISTINGUISHED_ABSENT_PIN",)
MISSING = object()

FALLBACK = r"""## S8.4 [GT3-r5] RESIDUAL D1b SCOPE CORRECTION
## (2026-08-12 — dated append; activated only after the committed
## full-output collision search returns EMPTY on its complete roster)

The residual search compared members only within an identical
committed reader frame and required equality of the ENTIRE
verdict-level honest output: pins, deciding residues, sigma, and
labels. It found no pair on the committed roster having that full
honest-output tuple identical and shadow content different at
heights >= THETA_j. An EMPTY finite-roster search does not prove
that no such pair exists on the full tower locus; it shows that
the committed evidence does not establish the stronger
full-verdict-output scope.

**S8.2 supersession.** The S8.2 corrected sentence beginning
"The shadow read's content at heights >= THETA_j is not a
function of the honest read's OUTPUT" is WITHDRAWN. Its reference
to the full verdict-level tuple "(pins, deciding residues, sigma,
labels)" is likewise WITHDRAWN.

**Final corrected claim.** The shadow read's content at heights
>= THETA_j is not a function of the honest read's sigma.

**Proof from the committed instances.** PE1-0 and PE1-1 have the
same honest sigma, namely {(8,1)}, while their shadow reads differ:
PE1-0 has shadow pins (21,14) and label tRAM, whereas PE1-1 has
shadow pins (28,14) and label tINERT. In particular their shadow
content differs at coordinate 0 at heights >= THETA_0 = 21.
Hence equal honest sigma can have different shadow content, so no
function of honest sigma alone determines that content. The same
fixed-honest-sigma variation is also visible across the full PE1
triple. No non-functionality claim for the larger tuple of honest
pins, deciding residues, sigma, and labels is retained.

This correction changes only S8.2's non-functionality scope.
S8.1's repaired margin proof, THEOREM GENTOW-3(i)-(iii), the
certificate-scoped persistence statement, and the accepted
machine records are untouched."""


def norm_name(name: str) -> str:
    return "".join(ch.lower() for ch in name if ch.isalnum())


def sort_key(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def canonical(value: Any, active: set[int] | None = None) -> Any:
    """Exact, hashable canonicalization; deliberately rejects floats/repr fallbacks."""
    if active is None:
        active = set()

    if value is None:
        return None
    if isinstance(value, bool):
        return ("bool", value)
    if isinstance(value, int):
        return ("int", value)
    if isinstance(value, Fraction):
        return ("fraction", value.numerator, value.denominator)
    if isinstance(value, str):
        return ("str", value)
    if isinstance(value, bytes):
        return ("bytes", tuple(value))
    if isinstance(value, float):
        raise TypeError("floating-point data are forbidden")

    oid = id(value)
    if oid in active:
        raise TypeError("cyclic object is not a canonical exact value")

    active.add(oid)
    try:
        if dataclasses.is_dataclass(value) and not isinstance(value, type):
            fields = tuple(
                (field.name, canonical(getattr(value, field.name), active))
                for field in dataclasses.fields(value)
            )
            return ("record", type(value).__qualname__, fields)

        if isinstance(value, Mapping):
            items = [
                (canonical(k, active), canonical(v, active))
                for k, v in value.items()
            ]
            items.sort(key=sort_key)
            return ("map", tuple(items))

        if isinstance(value, (tuple, list)):
            return ("seq", tuple(canonical(x, active) for x in value))

        if isinstance(value, (set, frozenset)):
            items = [canonical(x, active) for x in value]
            items.sort(key=sort_key)
            return ("multisetless-set", tuple(items))

        if hasattr(value, "coeffs") and not callable(value.coeffs):
            return (
                "coeff-object",
                type(value).__qualname__,
                canonical(value.coeffs, active),
            )

        if hasattr(value, "coefficients"):
            coeffs = value.coefficients
            if callable(coeffs):
                coeffs = coeffs()
            return (
                "coefficient-object",
                type(value).__qualname__,
                canonical(coeffs, active),
            )

        if hasattr(value, "__dict__"):
            public = {
                k: v
                for k, v in vars(value).items()
                if not k.startswith("_") and not callable(v)
            }
            if public:
                return (
                    "object",
                    type(value).__qualname__,
                    canonical(public, active),
                )

        raise TypeError(f"unsupported exact value type: {type(value).__qualname__}")
    finally:
        active.remove(oid)


def plain(value: Any) -> Any:
    """Readable exact representation for certificates."""
    if value is INF:
        return "INF"
    if value is None or isinstance(value, (bool, int, str)):
        return value
    if isinstance(value, Fraction):
        return {"numerator": value.numerator, "denominator": value.denominator}
    if isinstance(value, bytes):
        return tuple(value)
    if dataclasses.is_dataclass(value) and not isinstance(value, type):
        return {
            field.name: plain(getattr(value, field.name))
            for field in dataclasses.fields(value)
        }
    if isinstance(value, Mapping):
        return tuple(
            sorted(
                ((plain(k), plain(v)) for k, v in value.items()),
                key=sort_key,
            )
        )
    if isinstance(value, (tuple, list)):
        return tuple(plain(x) for x in value)
    if isinstance(value, (set, frozenset)):
        return tuple(sorted((plain(x) for x in value), key=sort_key))
    if hasattr(value, "coeffs") and not callable(value.coeffs):
        return plain(value.coeffs)
    if hasattr(value, "coefficients"):
        coeffs = value.coefficients
        return plain(coeffs() if callable(coeffs) else coeffs)
    if hasattr(value, "__dict__"):
        return {
            k: plain(v)
            for k, v in vars(value).items()
            if not k.startswith("_") and not callable(v)
        }
    raise TypeError(f"cannot print nonexact object {type(value).__qualname__}")


def safe_copy(value: Any) -> Any:
    try:
        return copy.deepcopy(value)
    except Exception:
        return value


def snapshot(namespace: Mapping[str, Any]) -> dict[str, Any]:
    answer: dict[str, Any] = {}
    for key, value in namespace.items():
        if key.startswith("__") or inspect.ismodule(value) or callable(value):
            continue
        try:
            canonical(value)
        except Exception:
            continue
        answer[key] = safe_copy(value)
    return answer


@dataclasses.dataclass
class Event:
    module: str
    function: str
    entry: dict[str, Any]
    exit: dict[str, Any]
    result: Any


@dataclasses.dataclass
class Record:
    source_tags: list[str]
    module: str
    frame_display: Any
    frame_key: Any
    polynomial: Any
    polynomial_key: Any
    pins: Any = MISSING
    pins_key: Any = MISSING
    residues: Any = MISSING
    residues_key: Any = MISSING
    sigma: Any = MISSING
    sigma_key: Any = MISSING
    labels: Any = MISSING
    labels_key: Any = MISSING
    shadow_arrays: Any = MISSING
    shadow_key: Any = MISSING
    theta: Any = MISSING
    t_maps: Any = MISSING
    t_key: Any = MISSING
    reasons: list[str] = dataclasses.field(default_factory=list)

    @property
    def eligible(self) -> bool:
        return not self.reasons

    @property
    def honest_key(self) -> Any:
        return (
            self.pins_key,
            self.residues_key,
            self.sigma_key,
            self.labels_key,
        )


def import_readers() -> dict[str, Any]:
    modules: dict[str, Any] = {}
    captured = io.StringIO()
    import importlib.util
    with contextlib.redirect_stdout(captured), contextlib.redirect_stderr(captured):
        for name in READER_NAMES:
            spec = importlib.util.spec_from_file_location(name, READER_PATHS[name])
            mod = importlib.util.module_from_spec(spec)
            sys.modules[name] = mod
            try:
                spec.loader.exec_module(mod)
            except SystemExit:
                # sealed runner exits at module level after its battery;
                # its definitions are complete in the module object we hold
                pass
            modules[name] = mod
    return modules


def trace_reader_entrypoints(modules: Mapping[str, Any]) -> list[Event]:
    events: list[Event] = []
    entries: dict[int, dict[str, Any]] = {}
    reader_files = {path.resolve() for path in READER_PATHS.values()}

    def tracer(frame: Any, event: str, arg: Any) -> Any:
        try:
            filename = Path(frame.f_code.co_filename).resolve()
        except Exception:
            return tracer
        if filename not in reader_files:
            return tracer

        fid = id(frame)
        if event == "call":
            entries[fid] = snapshot(frame.f_locals)
        elif event == "return":
            result = safe_copy(arg)
            try:
                canonical(result)
            except Exception:
                result = MISSING
            events.append(
                Event(
                    module=frame.f_globals.get("__name__", ""),
                    function=frame.f_code.co_name,
                    entry=entries.pop(fid, {}),
                    exit=snapshot(frame.f_locals),
                    result=result,
                )
            )
        elif event == "exception":
            pass
        return tracer

    for module in modules.values():
        entrypoints = []
        for name in ("main", "run", "run_checks", "check_all"):
            function = getattr(module, name, None)
            if not callable(function) or function in entrypoints:
                continue
            try:
                signature = inspect.signature(function)
            except (TypeError, ValueError):
                continue
            required = [
                p
                for p in signature.parameters.values()
                if p.default is inspect.Parameter.empty
                and p.kind
                in (
                    inspect.Parameter.POSITIONAL_ONLY,
                    inspect.Parameter.POSITIONAL_OR_KEYWORD,
                    inspect.Parameter.KEYWORD_ONLY,
                )
            ]
            if not required:
                entrypoints.append(function)

        for function in entrypoints:
            sink = io.StringIO()
            previous = sys.gettrace()
            try:
                sys.settrace(tracer)
                with contextlib.redirect_stdout(sink), contextlib.redirect_stderr(sink):
                    function()
            except SystemExit as exc:
                if exc.code not in (None, 0):
                    raise RuntimeError(
                        f"{module.__name__}.{function.__name__} exited with {exc.code}"
                    )
            finally:
                sys.settrace(previous)

    return events


def children(value: Any) -> Iterable[tuple[str, Any]]:
    if isinstance(value, Mapping):
        for key, item in value.items():
            if isinstance(key, str):
                yield key, item
    elif dataclasses.is_dataclass(value) and not isinstance(value, type):
        for field in dataclasses.fields(value):
            yield field.name, getattr(value, field.name)
    elif hasattr(value, "__dict__"):
        for key, item in vars(value).items():
            if not key.startswith("_"):
                yield key, item


def find_named(
    roots: Sequence[Any],
    aliases: Sequence[str],
    *,
    max_depth: int = 5,
) -> Any:
    wanted = {norm_name(alias) for alias in aliases}
    queue: list[tuple[Any, int]] = [(root, 0) for root in roots]
    seen: set[int] = set()

    while queue:
        value, depth = queue.pop(0)
        oid = id(value)
        if oid in seen:
            continue
        seen.add(oid)

        for key, item in children(value):
            if norm_name(key) in wanted:
                return item
        if depth >= max_depth:
            continue
        for _, item in children(value):
            if isinstance(item, Mapping) or dataclasses.is_dataclass(item):
                queue.append((item, depth + 1))
            elif hasattr(item, "__dict__") and not inspect.ismodule(item):
                queue.append((item, depth + 1))
    return MISSING


def all_strings(value: Any, max_depth: int = 5) -> list[str]:
    found: list[str] = []
    queue = [(value, 0)]
    seen: set[int] = set()
    while queue:
        item, depth = queue.pop(0)
        oid = id(item)
        if oid in seen:
            continue
        seen.add(oid)
        if isinstance(item, str):
            found.append(item)
            continue
        if depth >= max_depth:
            continue
        if isinstance(item, Mapping):
            queue.extend((x, depth + 1) for x in item.values())
        elif isinstance(item, (tuple, list, set, frozenset)):
            queue.extend((x, depth + 1) for x in item)
        elif dataclasses.is_dataclass(item) and not isinstance(item, type):
            queue.extend(
                (getattr(item, f.name), depth + 1)
                for f in dataclasses.fields(item)
            )
    return found


def looks_like_polynomial(value: Any) -> bool:
    if value is MISSING or isinstance(value, (str, bytes, bool, float)):
        return False
    if hasattr(value, "coeffs") or hasattr(value, "coefficients"):
        try:
            canonical(value)
            return True
        except Exception:
            return False
    if isinstance(value, (tuple, list)) and value:
        try:
            canonical(value)
        except Exception:
            return False

        def exact_scalar(x: Any) -> bool:
            return isinstance(x, (int, bool, Fraction))

        return all(
            exact_scalar(x)
            or (
                isinstance(x, (tuple, list))
                and all(exact_scalar(y) for y in x)
            )
            for x in value
        )
    return False


def extract_polynomial(roots: Sequence[Any]) -> Any:
    aliases = (
        "member_f",
        "member_polynomial",
        "polynomial",
        "poly",
        "input_f",
        "f_coeffs",
        "coeffs",
        "f",
    )
    value = find_named(roots, aliases)
    return value if looks_like_polynomial(value) else MISSING


def extract_tags(roots: Sequence[Any], module: str, function: str) -> list[str]:
    preferred = find_named(
        roots,
        (
            "source_tag",
            "source_tags",
            "member_tag",
            "row_tag",
            "tag",
            "name",
            "member_name",
            "family",
            "fam",
            "label",
        ),
    )
    strings = all_strings(preferred) if preferred is not MISSING else []
    accepted = []
    markers = (
        "FAM-",
        "A7-BAND",
        "PE1-",
        "FR-GL",
        "FR-M3",
        "W-A",
        "W-B",
        "W-",
        "FR5X",
    )
    for string in strings:
        if any(marker in string.upper() for marker in markers):
            accepted.append(string)

    if not accepted:
        for root in roots:
            for string in all_strings(root, max_depth=2):
                if any(marker in string.upper() for marker in markers):
                    accepted.append(string)

    if not accepted:
        accepted = [f"{module.rsplit('.', 1)[-1]}:{function}"]
    return list(dict.fromkeys(accepted))


def excluded_nonmember(tags: Sequence[str]) -> bool:
    text = " ".join(tags).upper()
    forbidden = (
        "MUTANT",
        "ALTERED-EXPECTED",
        "ALTERED_EXPECTED",
        "THRESHOLD",
        "TOOTH",
        "CARRIER-ONLY",
        "CARRIER_ONLY",
        "PREDICATE",
    )
    return any(word in text for word in forbidden)


FRAME_FIELDS = (
    ("p", ("p", "prime", "residue_characteristic")),
    ("Q", ("Q", "q", "residue_field_size")),
    ("Phi_prime", ("Phi_prime", "PhiPrime", "PHIP", "phi_prime")),
    ("e1", ("e1",)),
    ("f1", ("f1",)),
    ("h", ("h",)),
    ("eta", ("eta",)),
    ("e2", ("e2",)),
    ("f2", ("f2",)),
    ("u2", ("u2",)),
    ("mu2", ("mu2",)),
    ("Phi2", ("Phi2", "phi2", "phi_2")),
    ("N", ("N", "precision", "consultation_bound")),
)


def extract_options(roots: Sequence[Any]) -> tuple[tuple[str, Any], ...]:
    selected: dict[str, Any] = {}
    keywords = (
        "normalizer",
        "normalisation",
        "normalization",
        "gauge",
        "basis",
        "slotorder",
        "slotgrid",
        "window",
        "consultationwindow",
        "labelorder",
        "coordinateorder",
    )
    for root in roots:
        if not isinstance(root, Mapping):
            continue
        for key, value in root.items():
            if not isinstance(key, str):
                continue
            nk = norm_name(key)
            if not any(word in nk for word in keywords):
                continue
            if callable(value) or inspect.ismodule(value):
                continue
            try:
                canonical(value)
            except Exception:
                continue
            selected[key] = value
    return tuple(sorted(selected.items()))


def extract_frame(roots: Sequence[Any]) -> tuple[Any, Any, list[str]]:
    displayed = []
    missing = []
    for label, aliases in FRAME_FIELDS:
        value = find_named(roots, aliases)
        if value is MISSING:
            missing.append(label)
            displayed.append((label, "<UNAVAILABLE>"))
        else:
            displayed.append((label, plain(value)))

    options = extract_options(roots)
    displayed.insert(-1, ("normalizer/gauge/options", plain(options)))
    try:
        key = canonical(tuple(displayed))
    except Exception as exc:
        missing.append(f"noncanonical-frame:{exc}")
        key = MISSING
    return tuple(displayed), key, missing


def normalize_pins(value: Any) -> Any:
    if value is None:
        return INF
    if isinstance(value, Mapping):
        return {
            key: normalize_pins(item)
            for key, item in value.items()
        }
    if isinstance(value, (tuple, list)):
        return tuple(normalize_pins(item) for item in value)
    return value


def normalize_sigma(value: Any) -> Any:
    if value is None or value is MISSING:
        return MISSING
    if isinstance(value, Mapping):
        expanded = []
        for pair, multiplicity in value.items():
            if not isinstance(multiplicity, int) or multiplicity < 0:
                return value
            expanded.extend([pair] * multiplicity)
        return tuple(sorted(expanded, key=lambda x: sort_key(canonical(x))))
    if isinstance(value, (tuple, list, set, frozenset)):
        return tuple(sorted(tuple(value), key=lambda x: sort_key(canonical(x))))
    return value


def normalize_labels(value: Any) -> Any:
    if value is MISSING or value is None:
        return MISSING
    if isinstance(value, (set, frozenset)):
        return MISSING
    if isinstance(value, str):
        return (value,)
    if isinstance(value, (tuple, list)):
        return tuple(value)
    return (value,)


def integer_from_exact(value: Any) -> int | None:
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    return None


def theta_vector(theta: Any, coordinates: int) -> tuple[int, ...] | None:
    if isinstance(theta, int):
        return (theta,) * coordinates
    if isinstance(theta, Mapping):
        answer = []
        for j in range(coordinates):
            value = theta.get(j, theta.get(str(j), MISSING))
            if not isinstance(value, int):
                return None
            answer.append(value)
        return tuple(answer)
    if isinstance(theta, (tuple, list)) and len(theta) >= coordinates:
        answer = tuple(theta[:coordinates])
        return answer if all(isinstance(x, int) for x in answer) else None
    return None


def explicit_digit_rows(value: Any) -> list[tuple[int, int, int, Any]]:
    rows: list[tuple[int, int, int, Any]] = []

    if isinstance(value, Mapping):
        for key, digit in value.items():
            if (
                isinstance(key, (tuple, list))
                and len(key) == 3
                and all(isinstance(x, int) for x in key)
            ):
                rows.append((key[0], key[1], key[2], digit))
                continue
            if isinstance(digit, Mapping):
                height = find_named((digit,), ("height", "m"))
                x_slot = find_named((digit,), ("x_slot", "xslot", "a"))
                phi_slot = find_named((digit,), ("phi_slot", "phislot", "b"))
                residue = find_named(
                    (digit,),
                    ("digit", "residue", "value", "coefficient", "coeff"),
                )
                if all(
                    isinstance(x, int)
                    for x in (height, x_slot, phi_slot)
                ) and residue is not MISSING:
                    rows.append((height, x_slot, phi_slot, residue))

    if isinstance(value, (tuple, list)):
        for item in value:
            if isinstance(item, Mapping):
                height = find_named((item,), ("height", "m"))
                x_slot = find_named((item,), ("x_slot", "xslot", "a"))
                phi_slot = find_named((item,), ("phi_slot", "phislot", "b"))
                residue = find_named(
                    (item,),
                    ("digit", "residue", "value", "coefficient", "coeff"),
                )
                if all(
                    isinstance(x, int)
                    for x in (height, x_slot, phi_slot)
                ) and residue is not MISSING:
                    rows.append((height, x_slot, phi_slot, residue))
    return rows


def nested_grid_rows(value: Any) -> list[tuple[int, int, int, Any]]:
    """
    Accept only the committed canonical [height][x_slot][phi_slot] grid form.
    No p-adic digit arithmetic is reconstructed here.
    """
    rows = []
    if not isinstance(value, (tuple, list)):
        return rows
    for height, x_grid in enumerate(value):
        if not isinstance(x_grid, (tuple, list)):
            return []
        for x_slot, phi_grid in enumerate(x_grid):
            if not isinstance(phi_grid, (tuple, list)):
                return []
            for phi_slot, digit in enumerate(phi_grid):
                try:
                    canonical(digit)
                except Exception:
                    return []
                rows.append((height, x_slot, phi_slot, digit))
    return rows


def is_exact_zero(value: Any) -> bool:
    if isinstance(value, bool):
        return not value
    if isinstance(value, int):
        return value == 0
    if isinstance(value, Fraction):
        return value == 0
    if isinstance(value, (tuple, list)):
        return all(is_exact_zero(x) for x in value)
    if hasattr(value, "is_zero"):
        marker = value.is_zero
        marker = marker() if callable(marker) else marker
        if isinstance(marker, bool):
            return marker
    return canonical(value) == canonical(0)


def shadow_to_t_maps(
    shadow: Any,
    theta: Any,
    explicit_high: Any = MISSING,
) -> Any:
    if explicit_high is not MISSING:
        return explicit_high

    if isinstance(shadow, Mapping):
        coordinate_values = [
            shadow[key]
            for key in sorted(shadow, key=lambda x: sort_key(canonical(x)))
        ]
    elif isinstance(shadow, (tuple, list)):
        coordinate_values = list(shadow)
    else:
        return MISSING

    thetas = theta_vector(theta, len(coordinate_values))
    if thetas is None:
        return MISSING

    answer = []
    for coordinate, coordinate_shadow in enumerate(coordinate_values):
        rows = explicit_digit_rows(coordinate_shadow)
        if not rows:
            rows = nested_grid_rows(coordinate_shadow)
        if not rows and coordinate_shadow not in ({}, (), []):
            return MISSING

        sparse = {}
        for height, x_slot, phi_slot, digit in rows:
            if height >= thetas[coordinate] and not is_exact_zero(digit):
                sparse[(height, x_slot, phi_slot)] = digit
        answer.append(
            tuple(
                sorted(
                    sparse.items(),
                    key=lambda item: item[0],
                )
            )
        )
    return tuple(answer)


def context_roots(
    event: Event,
    module_globals: Mapping[str, Any],
) -> tuple[Any, ...]:
    roots: list[Any] = [event.exit, event.entry]
    if event.result is not MISSING:
        roots.append(event.result)
    roots.append(module_globals)
    return tuple(roots)


def event_is_member_candidate(event: Event, roots: Sequence[Any]) -> bool:
    name = norm_name(event.function)
    if "membercheck" in name or "memberread" in name or "runmember" in name:
        return True
    polynomial = extract_polynomial(roots)
    if polynomial is MISSING:
        return False
    c_value = find_named(
        roots,
        ("C", "honest_C", "composed_coefficients", "honest_coefficients"),
    )
    shadow = find_named(
        roots,
        ("ShC", "shadow_C", "shadow_coordinates", "stage_shadow"),
    )
    return c_value is not MISSING and shadow is not MISSING


def discover_seed_events(
    modules: Mapping[str, Any],
    events: Sequence[Event],
) -> list[tuple[Event, tuple[Any, ...]]]:
    seeds = []
    for event in events:
        short = event.module.rsplit(".", 1)[-1]
        if short not in modules:
            continue
        roots = context_roots(event, vars(modules[short]))
        if event_is_member_candidate(event, roots):
            seeds.append((event, roots))
    return seeds


def aggregate_roots_for_polynomial(
    module_name: str,
    polynomial_key: Any,
    seed_roots: Sequence[Any],
    events: Sequence[Event],
    module_globals: Mapping[str, Any],
) -> tuple[Any, ...]:
    roots = list(seed_roots)
    for event in events:
        if event.module != module_name:
            continue
        event_roots = (event.exit, event.entry, event.result)
        candidate = extract_polynomial(event_roots)
        if candidate is MISSING:
            continue
        try:
            same = canonical(candidate) == polynomial_key
        except Exception:
            same = False
        if same:
            roots.extend(event_roots)
    roots.append(module_globals)
    return tuple(root for root in roots if root is not MISSING)


def build_record(
    event: Event,
    seed_roots: Sequence[Any],
    modules: Mapping[str, Any],
    events: Sequence[Event],
) -> Record | None:
    short = event.module.rsplit(".", 1)[-1]
    polynomial = extract_polynomial(seed_roots)
    if polynomial is MISSING:
        return None
    polynomial_key = canonical(polynomial)
    roots = aggregate_roots_for_polynomial(
        event.module,
        polynomial_key,
        seed_roots,
        events,
        vars(modules[short]),
    )
    tags = extract_tags(roots, event.module, event.function)
    if excluded_nonmember(tags):
        return None

    frame_display, frame_key, frame_missing = extract_frame(roots)
    record = Record(
        source_tags=tags,
        module=event.module,
        frame_display=frame_display,
        frame_key=frame_key,
        polynomial=polynomial,
        polynomial_key=polynomial_key,
    )
    if frame_key is MISSING:
        record.reasons.extend(frame_missing)

    pins = find_named(
        roots,
        (
            "honest_pins",
            "composed_pins",
            "pin_vector",
            "pins",
            "honest_pin",
        ),
    )
    residues = find_named(
        roots,
        (
            "deciding_residues",
            "honest_deciding_residues",
            "consulted_residues",
            "decision_residues",
            "deciding_digits",
            "decision_trace",
        ),
    )
    sigma = find_named(
        roots,
        (
            "honest_sigma",
            "sigma_honest",
            "sigma",
            "splitting_type",
        ),
    )
    labels = find_named(
        roots,
        (
            "honest_labels",
            "verdict_labels",
            "labels_honest",
            "labels",
        ),
    )
    shadow = find_named(
        roots,
        (
            "ShC",
            "shadow_C",
            "shadow_coordinates",
            "stage_shadow",
            "shadow_content_arrays",
        ),
    )
    theta = find_named(
        roots,
        (
            "Theta",
            "THETA",
            "theta",
            "theta_vector",
            "thresholds",
        ),
    )
    explicit_high = find_named(
        roots,
        (
            "shadow_at_or_above_theta",
            "high_shadow_content",
            "shadow_high_map",
            "T_map",
            "T",
        ),
    )

    if pins is MISSING:
        record.reasons.append("honest pins unavailable")
    else:
        record.pins = normalize_pins(pins)
        record.pins_key = canonical(record.pins)

    if residues is MISSING or residues is None:
        record.reasons.append("deciding-residue array unavailable")
    else:
        record.residues = residues
        record.residues_key = canonical(residues)

    record.sigma = normalize_sigma(sigma)
    if record.sigma is MISSING:
        record.reasons.append("honest sigma unavailable")
    else:
        record.sigma_key = canonical(record.sigma)

    record.labels = normalize_labels(labels)
    if record.labels is MISSING:
        record.reasons.append("ordered honest labels unavailable")
    else:
        record.labels_key = canonical(record.labels)

    if shadow is MISSING:
        record.reasons.append("complete shadow coordinate arrays unavailable")
    else:
        record.shadow_arrays = shadow
        record.shadow_key = canonical(shadow)

    if theta is MISSING:
        record.reasons.append("THETA vector unavailable")
    else:
        record.theta = theta

    if shadow is not MISSING and theta is not MISSING:
        t_maps = shadow_to_t_maps(shadow, theta, explicit_high)
        if t_maps is MISSING:
            record.reasons.append(
                "committed canonical high-shadow slot map unavailable"
            )
        else:
            record.t_maps = t_maps
            record.t_key = canonical(t_maps)

    return record


def deduplicate(records: Sequence[Record]) -> list[Record]:
    unique: dict[tuple[Any, Any], Record] = {}
    for record in records:
        if record.frame_key is MISSING:
            key = (("missing-frame", record.module), record.polynomial_key)
        else:
            key = (record.frame_key, record.polynomial_key)
        if key not in unique:
            unique[key] = record
        else:
            present = unique[key]
            present.source_tags = list(
                dict.fromkeys(present.source_tags + record.source_tags)
            )
            present.reasons = list(dict.fromkeys(present.reasons + record.reasons))
    return list(unique.values())


def tag_text(record: Record) -> str:
    return " | ".join(record.source_tags)


def pair_priority(pair: tuple[Record, Record]) -> tuple[Any, ...]:
    left, right = pair
    tags = {tag_text(left), tag_text(right)}
    pe1_first = any("PE1-1" in tag for tag in tags) and any(
        "PE1-2" in tag for tag in tags
    )
    return (
        0 if pe1_first else 1,
        sort_key(left.frame_key),
        tag_text(left),
        tag_text(right),
        sort_key(left.polynomial_key),
        sort_key(right.polynomial_key),
    )


def make_pairs(
    records: Sequence[Record],
) -> tuple[list[tuple[Record, Record]], Counter[Any]]:
    by_frame: dict[Any, list[Record]] = defaultdict(list)
    for record in records:
        if record.eligible:
            by_frame[record.frame_key].append(record)

    pairs = []
    tested_by_frame: Counter[Any] = Counter()
    for frame_key, frame_records in by_frame.items():
        frame_records.sort(
            key=lambda r: (tag_text(r), sort_key(r.polynomial_key))
        )
        for left, right in itertools.combinations(frame_records, 2):
            if left.polynomial_key == right.polynomial_key:
                continue
            pairs.append((left, right))
            tested_by_frame[frame_key] += 1

    pairs.sort(key=pair_priority)
    return pairs, tested_by_frame


def first_shadow_difference(left: Record, right: Record) -> tuple[Any, Any, Any]:
    def flatten(t_maps: Any) -> dict[tuple[int, int, int, int], Any]:
        answer = {}
        for coordinate, coordinate_map in enumerate(t_maps):
            for slot, digit in coordinate_map:
                height, x_slot, phi_slot = slot
                answer[(coordinate, height, x_slot, phi_slot)] = digit
        return answer

    left_map = flatten(left.t_maps)
    right_map = flatten(right.t_maps)
    zero = 0
    for key in sorted(set(left_map) | set(right_map)):
        a = left_map.get(key, zero)
        b = right_map.get(key, zero)
        if canonical(a) != canonical(b):
            coordinate, height, x_slot, phi_slot = key
            return (
                (coordinate, height, (x_slot, phi_slot)),
                a,
                b,
            )
    raise AssertionError("unequal canonical T maps had no differing digit")


def git_head() -> str:
    return subprocess.check_output(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
    ).strip()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def pp(label: str, value: Any) -> None:
    print(f"{label}:")
    print(pprint.pformat(plain(value), width=120, sort_dicts=False))


def print_provenance() -> None:
    print(f"HEAD: {git_head()}")
    print("READER SHA256:")
    for name in READER_NAMES:
        print(f"  {READER_PATHS[name].relative_to(ROOT)}  {sha256_file(READER_PATHS[name])}")


def frame_census(records: Sequence[Record]) -> dict[Any, dict[str, Any]]:
    result: dict[Any, dict[str, Any]] = {}
    grouped: dict[Any, list[Record]] = defaultdict(list)
    for record in records:
        grouped[record.frame_key].append(record)
    for key, rows in grouped.items():
        result[key] = {
            "frame": rows[0].frame_display,
            "rows": len(rows),
            "eligible": sum(row.eligible for row in rows),
            "ineligible": sum(not row.eligible for row in rows),
        }
    return result


def print_census(
    raw_count: int,
    records: Sequence[Record],
    tested_by_frame: Counter[Any],
) -> None:
    print("ROSTER CENSUS:")
    print(f"  semantic rows before exact (frame, polynomial) deduplication: {raw_count}")
    print(f"  rows after exact semantic deduplication: {len(records)}")
    print(f"  eligible rows: {sum(row.eligible for row in records)}")
    print(f"  ineligible rows: {sum(not row.eligible for row in records)}")
    print("  totals by frame:")
    census = frame_census(records)
    ordered = sorted(census.items(), key=lambda item: sort_key(item[0]))
    for index, (frame_key, data) in enumerate(ordered):
        print(
            f"    frame[{index}]: rows={data['rows']} "
            f"eligible={data['eligible']} ineligible={data['ineligible']} "
            f"pairs_tested={tested_by_frame.get(frame_key, 0)}"
        )
        print(f"      key={pprint.pformat(data['frame'], width=110)}")

    print("INELIGIBLE ROWS:")
    ineligible = sorted(
        (record for record in records if not record.eligible),
        key=lambda record: (record.module, tag_text(record)),
    )
    if not ineligible:
        print("  []")
    else:
        for record in ineligible:
            print(
                f"  tags={record.source_tags!r}; module={record.module}; "
                f"reasons={record.reasons!r}"
            )


def print_hit(index: int, left: Record, right: Record) -> None:
    print(f"HIT CERTIFICATE {index}")
    print(f"LEFT SOURCE TAGS: {left.source_tags!r}")
    print(f"RIGHT SOURCE TAGS: {right.source_tags!r}")
    pp("EXACT FRAME KEY", left.frame_display)
    pp("LEFT EXACT MEMBER POLYNOMIAL", left.polynomial)
    pp("RIGHT EXACT MEMBER POLYNOMIAL", right.polynomial)

    left_h = (left.pins, left.residues, left.sigma, left.labels)
    right_h = (right.pins, right.residues, right.sigma, right.labels)
    pp("LEFT COMPLETE HONEST TUPLE H", left_h)
    pp("RIGHT COMPLETE HONEST TUPLE H", right_h)

    print(f"PINS EQUAL: {left.pins_key == right.pins_key}")
    print(
        "DECIDING RESIDUES EQUAL: "
        f"{left.residues_key == right.residues_key}"
    )
    print(f"HONEST SIGMA EQUAL: {left.sigma_key == right.sigma_key}")
    print(f"HONEST LABELS EQUAL: {left.labels_key == right.labels_key}")

    pp("LEFT COMPLETE SHADOW COORDINATE ARRAYS", left.shadow_arrays)
    pp("RIGHT COMPLETE SHADOW COORDINATE ARRAYS", right.shadow_arrays)
    pp("LEFT T-MAPS", left.t_maps)
    pp("RIGHT T-MAPS", right.t_maps)

    location, left_digit, right_digit = first_shadow_difference(left, right)
    coordinate, height, slot = location
    print(
        "LEXICOGRAPHICALLY FIRST DIFFERING "
        f"(coordinate, height, slot): {(coordinate, height, slot)!r}"
    )
    pp("LEFT DIGIT", left_digit)
    pp("RIGHT DIGIT", right_digit)
    print("VERDICT: HIT")


def main() -> None:
    os.chdir(ROOT)
    modules = import_readers()
    events = trace_reader_entrypoints(modules)
    seeds = discover_seed_events(modules, events)

    raw_records = []
    for event, roots in seeds:
        record = build_record(event, roots, modules, events)
        if record is not None:
            raw_records.append(record)

    records = deduplicate(raw_records)
    pairs, tested_by_frame = make_pairs(records)

    hits = []
    for left, right in pairs:
        if left.frame_key != right.frame_key:
            continue
        if left.polynomial_key == right.polynomial_key:
            continue
        if left.pins_key != right.pins_key:
            continue
        if left.residues_key != right.residues_key:
            continue
        if left.sigma_key != right.sigma_key:
            continue
        if left.labels_key != right.labels_key:
            continue
        if left.t_key == right.t_key:
            continue
        hits.append((left, right))

    print_provenance()
    print_census(len(raw_records), records, tested_by_frame)
    print(f"SAME-FRAME DISTINCT-POLYNOMIAL PAIRS TESTED: {len(pairs)}")

    if hits:
        print(f"HITS: {len(hits)}")
        for index, (left, right) in enumerate(hits, 1):
            print_hit(index, left, right)
        print("FINAL VERDICT: HIT")
        return

    if any(not record.eligible for record in records):
        print("NO COLLISION AMONG ELIGIBLE ROWS")
        print(
            "SEARCH INCOMPLETE: rows lacking a defined full honest tuple or "
            "canonical high-shadow map cannot support EMPTY"
        )
        raise SystemExit(2)

    print("HITS: 0")
    print("FINAL VERDICT: EMPTY")
    print()
    print(FALLBACK)


if __name__ == "__main__":
    main()
