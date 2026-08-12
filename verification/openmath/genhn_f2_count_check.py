#!/usr/bin/env python3
"""
GENHN-ERR-1: direct corrected-floor stage-count experiment.

Exact arithmetic; Python standard library only.

We enumerate the Phi'-development coefficient digits, grouped
bijectively into complete K = F_4 slots.  This is not an enumeration
of ambient quartics or octics.

Count normalization:
    raw finite-stage node cardinality;
    no ambient opening fiber, sibling fiber, key-center/ghost factor,
    or PARI/sigma oracle.

The reader uses the untwisted count gauge on K[[t]].  J-D0 identifies
this gauge with the canonical twisted slot gauge by a count-preserving
bijection.  Thus labels of alpha letters are gauge names, while all
reported cardinalities are intrinsic.
"""

from collections import Counter
from dataclasses import dataclass


# ----------------------------------------------------------------------
# F_4 = F_2[a]/(a^2 + a + 1), represented as c0 + c1*a in two bits.
# ----------------------------------------------------------------------

Q = 2
K_SIZE = 4
GF4_MODULUS = 0b111  # x^2 + x + 1


def k_add(x, y):
    return x ^ y


def k_mul(x, y):
    z = 0
    a = x
    b = y
    while b:
        if b & 1:
            z ^= a
        b >>= 1
        a <<= 1
        if a & 0b100:
            a ^= GF4_MODULUS
    return z & 0b11


def k_square(x):
    return k_mul(x, x)


def k_name(x):
    return {
        0: "0",
        1: "1",
        2: "a",
        3: "1+a",
    }[x]


def quadratic_type(a, b):
    """Classify T^2 + a*T + b over F_4; b is assumed nonzero."""
    roots = [
        x for x in range(K_SIZE)
        if k_add(k_add(k_mul(x, x), k_mul(a, x)), b) == 0
    ]
    if len(roots) == 0:
        return "INERT", None
    if len(roots) == 2:
        return "SPLITEQ", None
    if len(roots) == 1:
        return "ALPHA", roots[0]
    raise AssertionError(("impossible root census", a, b, roots))


# ----------------------------------------------------------------------
# Stage geometry.
# ----------------------------------------------------------------------

@dataclass(frozen=True)
class Genre:
    name: str
    e1: int
    f1: int
    mu: int
    h: int
    cap: int
    common_coefficient_window: int

    @property
    def Dprime(self):
        return self.e1 * self.f1

    @property
    def S(self):
        return self.e1 * self.h

    @property
    def B(self):
        # Corrected node parameter D' h.
        return self.Dprime * self.h


GENRES = (
    Genre(
        name="F=(e1,f1,mu)=(1,2,2)",
        e1=1,
        f1=2,
        mu=2,
        h=1,
        cap=7,
        common_coefficient_window=7,
    ),
    Genre(
        name="MIXED=(e1,f1,mu)=(2,2,2)",
        e1=2,
        f1=2,
        mu=2,
        h=1,
        cap=11,
        common_coefficient_window=6,
    ),
)


def component_positions(g, m):
    """
    Return the two actual F_2 coefficient-digit positions forming the
    K-slot of dv-height m.

    A returned entry (s,i,r) means that the eta^s component is the
    pi^r digit of the x^i coefficient, and

        e1*r + i*h = m.
    """
    representatives = [
        i0 for i0 in range(g.e1)
        if (i0 * g.h - m) % g.e1 == 0
    ]
    assert len(representatives) == 1
    i0 = representatives[0]

    ans = []
    for s in range(g.f1):
        i = i0 + g.e1 * s
        numerator = m - i * g.h
        assert numerator % g.e1 == 0
        r = numerator // g.e1
        ans.append((s, i, r))
    return tuple(ans)


def corrected_floor(g, j, i):
    """
    Least coefficient valuation satisfying

        e1*v(a_{j,i}) + i*h > (mu-j)*D'*h.
    """
    threshold = (g.mu - j) * g.B
    return (threshold - i * g.h) // g.e1 + 1


def coefficient_cap(g, i):
    """Largest r retained by the component-complete dv cap."""
    return (g.cap - i * g.h) // g.e1


def make_layout(g):
    """
    Each layout item is one K-slot, but its 'components' field records
    the exact underlying F_2 coefficient digits.  Enumerating all four
    values of the slot is exactly enumerating those two binary digits.
    """
    layout = []
    for j in (1, 0):
        threshold = (g.mu - j) * g.B
        for m in range(threshold + 1, g.cap + 1):
            components = component_positions(g, m)
            assert len(components) == g.f1
            for _, i, r in components:
                assert 0 <= i < g.Dprime
                assert r >= corrected_floor(g, j, i)
                assert r <= coefficient_cap(g, i)
                assert g.e1 * r + i * g.h == m
            layout.append((j, m, components))

    # Audit that every retained Phi'-coefficient digit occurs once.
    seen = set()
    for j, _, components in layout:
        for s, i, r in components:
            key = (j, i, r)
            assert key not in seen
            seen.add(key)

    expected = set()
    for j in (1, 0):
        for i in range(g.Dprime):
            lo = corrected_floor(g, j, i)
            hi = coefficient_cap(g, i)
            for r in range(lo, hi + 1):
                expected.add((j, i, r))
    assert seen == expected

    return tuple(layout)


def node_volume(b, cap):
    """Raw cardinality of the complete-slot mu=2 node."""
    a1_slots = max(0, cap - b)
    a0_slots = max(0, cap - 2 * b)
    return K_SIZE ** (a1_slots + a0_slots)


# ----------------------------------------------------------------------
# Complete-slot finite-window stage reader.
# ----------------------------------------------------------------------

def series_value(series):
    for m, coefficient in enumerate(series):
        if coefficient:
            return m
    return None


def translate_alpha(a0, a1, kappa, s, cap):
    """
    Count-gauge substitution Y = Z + s*t^kappa in characteristic 2:

        A1' = A1,
        A0' = A0 + s*t^kappa*A1 + s^2*t^(2*kappa).

    This is the untwisted count gauge; canonical cocycle twists merely
    permute the nonzero K letters.
    """
    new_a1 = list(a1)
    new_a0 = list(a0)

    for degree, coefficient in enumerate(a1):
        target = degree + kappa
        if coefficient and target <= cap:
            new_a0[target] = k_add(
                new_a0[target],
                k_mul(coefficient, s),
            )

    target = 2 * kappa
    if target <= cap:
        new_a0[target] = k_add(new_a0[target], k_square(s))

    return new_a0, new_a1


def read_stage(a0, a1, cap, history=()):
    w = series_value(a1)
    u = series_value(a0)

    if u is None:
        # Every completion has u >= cap+1.
        if w is not None and 2 * w < cap + 1:
            return history + (f"SPLTAIL(w={w})",)
        return history + ("UND",)

    if w is not None and u > 2 * w:
        return history + (f"2SIDED(w={w},u={u})",)

    # Here u <= 2w, interpreting w=None as infinity.
    if u & 1:
        return history + (f"RAM(u={u})",)

    kappa = u // 2
    a = a1[kappa] if kappa <= cap else 0
    b = a0[u]
    kind, root = quadratic_type(a, b)

    if kind == "INERT":
        return history + (f"INERT(k={kappa})",)
    if kind == "SPLITEQ":
        return history + (f"SPLITEQ(k={kappa})",)

    assert kind == "ALPHA"
    assert root is not None and root != 0

    new_a0, new_a1 = translate_alpha(
        a0, a1, kappa, root, cap
    )

    new_w = series_value(new_a1)
    new_u = series_value(new_a0)
    assert new_w is None or new_w > kappa
    assert new_u is None or new_u > 2 * kappa

    return read_stage(
        new_a0,
        new_a1,
        cap,
        history + (f"ALPHA(k={kappa},s={k_name(root)})",),
    )


def enumerate_stage(g):
    """
    Enumerate all direct Phi'-development digit states.

    A base-4 slot digit is simply the pair of its two independent
    F_2 coefficient digits, in the basis (1, eta).
    """
    layout = make_layout(g)
    number_of_states = K_SIZE ** len(layout)
    histogram = Counter()

    for state_number in range(number_of_states):
        code = state_number
        series = [
            [0] * (g.cap + 1),  # A0
            [0] * (g.cap + 1),  # A1
        ]

        for j, m, components in layout:
            slot_digit = code & 0b11
            code >>= 2

            # Explicit coefficient-digit audit.
            rebuilt = 0
            for s, i, r in components:
                bit = (slot_digit >> s) & 1
                if bit:
                    rebuilt ^= 1 << s
                assert g.e1 * r + i * g.h == m
            assert rebuilt == slot_digit

            series[j][m] = slot_digit

        assert code == 0
        histogram[read_stage(series[0], series[1], g.cap)] += 1

    assert sum(histogram.values()) == number_of_states
    return layout, histogram


# ----------------------------------------------------------------------
# Independent closed-form count prediction.
# ----------------------------------------------------------------------

def add_count(counter, key, amount):
    if amount:
        counter[key] += amount


def predict_node(b, cap):
    """
    Closed-form mu=2 cell-law prediction in raw node normalization.
    Keys include alpha letters, so no hidden |K|-1 factor remains.
    """
    out = Counter()

    # A0 is zero through the cap.
    first_undecided_w = max(b + 1, (cap + 2) // 2)
    und_count = (
        K_SIZE ** (cap - first_undecided_w + 1)
        if first_undecided_w <= cap
        else 1
    )
    add_count(out, ("UND",), und_count)

    for w in range(b + 1, cap + 1):
        if 2 * w < cap + 1:
            count_a1 = (K_SIZE - 1) * K_SIZE ** (cap - w)
            add_count(out, (f"SPLTAIL(w={w})",), count_a1)

    # A0 has exact value u.
    for u in range(2 * b + 1, cap + 1):
        count_a0 = (K_SIZE - 1) * K_SIZE ** (cap - u)

        # Two distinct polygon sides.
        for w in range(b + 1, (u - 1) // 2 + 1):
            count_a1 = (K_SIZE - 1) * K_SIZE ** (cap - w)
            add_count(
                out,
                (f"2SIDED(w={w},u={u})",),
                count_a0 * count_a1,
            )

        if u & 1:
            lo = max(b + 1, (u + 1) // 2)
            count_a1 = (
                K_SIZE ** (cap - lo + 1)
                if lo <= cap
                else 1
            )
            add_count(
                out,
                (f"RAM(u={u})",),
                count_a0 * count_a1,
            )
            continue

        kappa = u // 2

        # After fixing the residual coefficients, these are the free
        # tail digits in A0 and A1.
        tail = K_SIZE ** (
            (cap - 2 * kappa) + (cap - kappa)
        )

        split_census = (K_SIZE - 1) * (K_SIZE - 2) // 2
        inert_census = K_SIZE * (K_SIZE - 1) // 2

        add_count(
            out,
            (f"SPLITEQ(k={kappa})",),
            split_census * tail,
        )
        add_count(
            out,
            (f"INERT(k={kappa})",),
            inert_census * tail,
        )

        # For each fixed nonzero repeated-root letter, refine transfer
        # is a bijection onto the node at kappa.
        child = predict_node(kappa, cap)
        for s in range(1, K_SIZE):
            alpha = f"ALPHA(k={kappa},s={k_name(s)})"
            for child_key, child_count in child.items():
                add_count(out, (alpha,) + child_key, child_count)

    expected_total = node_volume(b, cap)
    assert sum(out.values()) == expected_total, (
        b,
        cap,
        sum(out.values()),
        expected_total,
    )
    return out


# Literal preregistration, independent of the predictor's formulas.
SEALED_EXPECTED = {
    "F=(e1,f1,mu)=(1,2,2)": {
        "UND": 256,
        "SPLTAIL(w=3)": 768,
        "RAM(u=5)": 49152,
        "SPLITEQ(k=3)": 3072,
        "INERT(k=3)": 6144,
        "ALPHA(k=3,s=1) -> UND": 1024,
        "ALPHA(k=3,s=a) -> UND": 1024,
        "ALPHA(k=3,s=1+a) -> UND": 1024,
        "2SIDED(w=3,u=7)": 2304,
        "RAM(u=7)": 768,
    },
    "MIXED=(e1,f1,mu)=(2,2,2)": {
        "UND": 4096,
        "SPLTAIL(w=5)": 12288,
        "RAM(u=9)": 786432,
        "SPLITEQ(k=5)": 49152,
        "INERT(k=5)": 98304,
        "ALPHA(k=5,s=1) -> UND": 16384,
        "ALPHA(k=5,s=a) -> UND": 16384,
        "ALPHA(k=5,s=1+a) -> UND": 16384,
        "2SIDED(w=5,u=11)": 36864,
        "RAM(u=11)": 12288,
    },
}


def key_string(key):
    return " -> ".join(key)


# ----------------------------------------------------------------------
# Boundary-band census Q^comp - 1.
# ----------------------------------------------------------------------

def boundary_census_checks(g):
    """
    Use a common coefficient window r < N, unlike the component-
    complete cap used by the main count table.  This separately tests
    the ERRATUM-E2 boundary census.
    """
    N = g.common_coefficient_window
    max_visible_height = max(
        g.e1 * (N - 1) + i * g.h
        for i in range(g.Dprime)
    )

    rows = []
    for m in range(g.B + 1, max_visible_height + 1):
        positions = component_positions(g, m)
        visible = [
            (s, i, r)
            for s, i, r in positions
            if 0 <= r < N
        ]

        comp = len(visible)
        if not (0 < comp < g.f1):
            continue

        measured_nonzero = 0
        for assignment in range(1 << comp):
            element = 0
            for local_index, (s, _, _) in enumerate(visible):
                if (assignment >> local_index) & 1:
                    element ^= 1 << s
            if element != 0:
                measured_nonzero += 1

        predicted_nonzero = Q ** comp - 1
        rows.append(
            (m, comp, measured_nonzero, predicted_nonzero)
        )

    assert rows, ("no boundary rows", g)
    return rows


# ----------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------

def main():
    mismatches = []

    print("GENHN-ERR-1 CORRECTED-FLOOR STAGE COUNT")
    print("Q=2, K=F_4, count gauge=untwisted, arithmetic=exact")
    print()

    for g in GENRES:
        print("=" * 78)
        print(g.name)
        print(
            f"D'={g.Dprime}  S=e1*h={g.S}  "
            f"B=D'*h={g.B}  stage-cap M={g.cap}"
        )

        print("CORRECTED PHI'-COEFFICIENT RANGES")
        for j in (1, 0):
            for i in range(g.Dprime):
                lo = corrected_floor(g, j, i)
                hi = coefficient_cap(g, i)
                text = f"{lo}..{hi}" if lo <= hi else "EMPTY"
                print(f"  A{j}: i={i}: coefficient heights r={text}")

        layout, measured = enumerate_stage(g)
        predicted = predict_node(g.B, g.cap)
        sealed = SEALED_EXPECTED[g.name]

        measured_total = sum(measured.values())
        corrected_total = node_volume(g.B, g.cap)
        old_total = node_volume(g.S, g.cap)

        print(
            f"SLOTS={len(layout)}  "
            f"MEASURED-TOTAL={measured_total}  "
            f"CORRECTED-PREDICTED-TOTAL={corrected_total}"
        )
        print(
            f"OLD-S-NODE-TOTAL={old_total}  "
            f"OLD/CORRECTED={old_total // corrected_total}"
        )

        if measured_total != corrected_total:
            mismatches.append(f"{g.name}:NODE-TOTAL")
        if old_total == measured_total:
            mismatches.append(f"{g.name}:OLD-S-NODE-NOT-REJECTED")

        measured_strings = {
            key_string(k): v for k, v in measured.items()
        }
        predicted_strings = {
            key_string(k): v for k, v in predicted.items()
        }

        print("PER-KEY TABLE")
        all_keys = sorted(
            set(measured_strings)
            | set(predicted_strings)
            | set(sealed)
        )
        for key in all_keys:
            obs = measured_strings.get(key, 0)
            pred = predicted_strings.get(key, 0)
            prereg = sealed.get(key, 0)
            ok = obs == pred == prereg
            print(
                f"  {key:42s} "
                f"measured={obs:10d} "
                f"predicted={pred:10d} "
                f"sealed={prereg:10d} "
                f"{'OK' if ok else 'MISMATCH'}"
            )
            if not ok:
                mismatches.append(f"{g.name}:{key}")

        # Raw alpha-fiber checks.  This is the count normalization
        # actually present in the enumerated node.
        for kappa in range(g.B + 1, g.cap // 2 + 1):
            prefix = f"ALPHA(k={kappa},"
            observed_alpha = sum(
                count
                for key, count in measured_strings.items()
                if key.startswith(prefix)
            )
            expected_alpha = (
                (K_SIZE - 1) * node_volume(kappa, g.cap)
            )
            print(
                f"  RAW-ALPHA-FIBER k={kappa}: "
                f"measured={observed_alpha} "
                f"predicted={expected_alpha}"
            )
            if observed_alpha != expected_alpha:
                mismatches.append(
                    f"{g.name}:RAW-ALPHA-FIBER({kappa})"
                )

            mass_bracket = (
                (K_SIZE - 1) * K_SIZE ** (2 * kappa - 1)
            )
            print(
                f"  MASS-BRACKET-REFERENCE k={kappa}: "
                f"{mass_bracket} "
                f"(not scored: different ghost normalization)"
            )

        print("BOUNDARY-PIN CENSUS")
        for m, comp, obs, pred in boundary_census_checks(g):
            ok = obs == pred
            print(
                f"  height={m} comp={comp}: "
                f"measured={obs} predicted=Q^comp-1={pred} "
                f"{'OK' if ok else 'MISMATCH'}"
            )
            if not ok:
                mismatches.append(
                    f"{g.name}:BAND(m={m},comp={comp})"
                )

        print()

    if mismatches:
        unique = sorted(set(mismatches))
        print("FINAL VERDICT: MISMATCH (" + ", ".join(unique) + ")")
    else:
        print("FINAL VERDICT: COUNTS-CONFIRMED")


if __name__ == "__main__":
    main()
