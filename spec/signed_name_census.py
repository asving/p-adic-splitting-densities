#!/usr/bin/env python3
"""Signed-name census instrument (AUDIT 2026-08-20).

Extracts every SIGNED statement name from `leanspec/Leanspec/Chap*.lean` and
cross-checks it against landed declarations in `leanfinal/`.

Design notes (why it is built this way):

* Lean comments are stripped FIRST, with nested `/- ... -/` handled.  This is
  the fix for the `package_three_of_drainage` false-PROVED trap: a naive
  name-grep hits declaration syntax quoted inside a module docstring's fenced
  code block.  Nothing inside any comment is ever a declaration here.
* The leanspec carries signed names in FOUR syntactic forms:
    1. `axiom NAME ...`               -- signed, not yet landed (stub form)
    2. `theorem/lemma NAME ...`       -- signed with a leanspec-local proof
    3. `def/abbrev/structure/...`     -- the definitional layer (carriers)
    4. `example ... := NAME (args)`   -- RETIREMENT FORM: the stub was deleted
       and replaced by an `example` that *uses* the landed declaration, so the
       leanspec elaborating is itself a type-level check that the landed name
       has the signed type.  The signed name is the head identifier of the
       example's body.
* Node labels (`**G.01**`, `**H.122**`) live in the docstring immediately
  preceding the declaration; they are captured for the report but are NOT the
  unit of the census (finding #2 of the charge: node headings != signed names).
"""

import re
import sys
import os
import json

REPO = "/data/users/asvin/math-and-lean/p-adic-splitting-densities"

DECL_KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "inductive",
              "class", "instance", "axiom", "opaque", "example")
MODIFIERS = ("noncomputable", "private", "protected", "partial", "unsafe",
             "scoped", "local", "nonrec")


def strip_comments(src):
    """Replace every Lean comment with equivalent-length whitespace.

    Line/column positions are preserved exactly, so a hit's line number in the
    stripped text is its line number in the original file.
    """
    out = list(src)
    i, n = 0, len(src)
    while i < n:
        # skip string literals so `"--"` inside a string is not a comment
        if src[i] == '"':
            j = i + 1
            while j < n:
                if src[j] == '\\':
                    j += 2
                    continue
                if src[j] == '"':
                    break
                j += 1
            i = j + 1
            continue
        if src.startswith("/-", i):
            depth = 1
            j = i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1
                    j += 2
                elif src.startswith("-/", j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            for k in range(i, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            if j == -1:
                j = n
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        i += 1
    return "".join(out)


# An inline `@[attr]` (or several) prefixing the decl keyword ON THE SAME LINE
# (e.g. `@[reducible] def ladderState_wf ...`) used to be invisible: DECL_RE
# required whitespace/known MODIFIERS right after the line-start, so the whole
# line silently failed to match and the declaration was never indexed. An
# attribute on its OWN line was already fine (it's not a decl line at all; the
# decl keyword still starts its own line below it) -- only the same-line case
# was broken. `[^\]\n]*` deliberately keeps this single-line only.
ATTR_RE = r"(?:@\[[^\]\n]*\][ \t]*)*"

DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<attr>%s)(?P<mods>(?:(?:%s)[ \t]+)*)(?P<kind>%s)(?![A-Za-z0-9_'])"
    % (ATTR_RE, "|".join(MODIFIERS), "|".join(DECL_KINDS)),
    re.M)

NAME_RE = re.compile(r"[A-Za-z_α-ωΑ-Ω][A-Za-z0-9_'!?₀-₉.α-ωΑ-Ω₁-₉]*")


def decls(path):
    """Yield dicts for every real declaration in `path` (comments stripped)."""
    src = open(path, encoding="utf-8").read()
    clean = strip_comments(src)
    raw_lines = src.split("\n")
    hits = list(DECL_RE.finditer(clean))
    for idx, m in enumerate(hits):
        start = m.start()
        end = hits[idx + 1].start() if idx + 1 < len(hits) else len(clean)
        body = clean[start:end]
        # A declaration's text ends at the first column-0 line that opens a new
        # top-level command (`end`, `#print axioms`, `section`, `namespace`,
        # `open`, `variable`, `set_option`, an attribute, a macro, ...).  Without
        # this the definiens leaks over `end Uniformity.Density #print axioms ...`
        # and a `True` body stops looking like `True` -- which is exactly the
        # I-D12 placeholder class this census exists to count.
        stop = re.search(
            r"\n(?:end\b|namespace\b|section\b|open\b|variable\b|universe\b"
            r"|set_option\b|#|attribute\b|@\[|notation\b|macro\b|elab\b"
            r"|syntax\b|deriving\b|local\b|scoped\b|declare_syntax_cat\b)",
            body)
        if stop:
            body = body[:stop.start()]
        line = clean[:start].count("\n") + 1
        kind = m.group("kind")
        rest = clean[m.end():end]
        if kind == "example":
            name = None
        else:
            # The declared name lives in the HEADER: the text before the first
            # depth-0 `:` or the first binder bracket.  Requiring this kills the
            # anonymous-instance artifact (`instance : DecidableEq F4 := ...`
            # otherwise reports a signed name `DecidableEq`) and it kills
            # `def f : Foo := ...` reporting `Foo`.
            hdr = re.split(r"[:\(\{\[⦃⟦]", rest, maxsplit=1)[0]
            nm = NAME_RE.search(hdr)
            name = nm.group(0) if nm else None
        # node label: nearest `**X.NN**` in the ORIGINAL text above this decl
        label = None
        for back in range(line - 1, max(0, line - 30), -1):
            lm = re.search(r"\*\*([A-Z]\.[0-9]+[A-Za-z0-9]*)\*\*", raw_lines[back - 1])
            if lm:
                label = lm.group(1)
                break
        # immediately-preceding `/-- ... -/` docstring (from the ORIGINAL source)
        doc = ""
        k = src.rfind("/--", 0, start)
        if k != -1:
            e = src.find("-/", k)
            if e != -1 and src[e + 2:start].strip() == "":
                doc = src[k:e]
        yield dict(path=path, line=line, kind=kind, mods=m.group("mods").strip(),
                   name=name, body=body, label=label, doc=doc)


def example_target(body):
    """Head identifier of an `example`'s definiens (the retirement-form name)."""
    # the body is `example <binders> : <type> := <term>` ; find the top-level `:=`
    depth = 0
    i = 0
    while i < len(body):
        c = body[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif body.startswith(":=", i) and depth == 0:
            term = body[i + 2:].strip()
            # strip a leading `by` / `fun` / open paren chain
            term = re.sub(r"^\(+", "", term).strip()
            for pref in ("by ", "by\n", "fun ", "λ ", "⟨", "rfl", "trivial",
                         "Iff.rfl", "True.intro", "id ", "congr"):
                if term.startswith(pref):
                    return None
            nm = NAME_RE.match(term)
            if not nm:
                return None
            cand = nm.group(0)
            # `inferInstance` is a generic Lean-core term, not a declared name:
            # `example : DecidableEq X := inferInstance` is a typeclass-resolution
            # check ("some instance exists"), not a check that a SPECIFIC signed
            # name landed. Treating it as a retirement target manufactures a
            # census row for a name nobody ever declared.
            if cand == "inferInstance":
                return None
            # reject projections off a LOCAL binder (`h.a2`, `hcfg.1`,
            # `gate_two_padic_two_exact.1`): a retirement-form target is a
            # global declaration, never a numeric/field projection of a hyp.
            if re.match(r"^[a-z][A-Za-z0-9_']{0,5}\.", cand):
                return None
            if re.search(r"\.[0-9]", cand):
                return None
            return cand
        i += 1
    return None


# ---------------------------------------------------------------------------
# leanfinal index
# ---------------------------------------------------------------------------

def leanfinal_files():
    out = []
    for root, dirs, files in os.walk(REPO + "/leanfinal"):
        if ".lake" in root or "/scratch" in root:
            continue
        for f in files:
            if f.endswith(".lean") and not f.startswith("scratch_"):
                out.append(os.path.join(root, f))
    return sorted(out)


# A landed `structure`/`inductive` auto-generates a projection per field or a
# constructor per `|` arm. These are real, landed, Lean-checked names the
# instant the parent declaration lands -- but `decls()` never emits a DECL_RE
# hit for them (there is no `def`/`theorem` line to match), so the leanfinal
# index used to have no entry for e.g. `CertFamily.m` or `CubicFamilyIndex.sep`
# even though `structure CertFamily ... where m : ℕ ...` / `inductive
# CubicFamilyIndex | sep : ... ` landed them. leanspec's retirement-form
# `example`s (`example : ... := CertFamily.m`, `example : Fin 3 → CubicFamilyIndex
# := CubicFamilyIndex.sep`) deliberately cite these as signed names to check —
# so the fix is to make the leanfinal SIDE recognize them, at their parent's
# landed declaration, rather than remove them from the signed-name universe.
# (leanspec itself never restates the `structure`/`inductive` body, only these
# retirement `example`s, so this expansion cannot double-count anything on the
# leanspec side -- see verdict_CFIX.md's denominator note.)

FIELD_RE = re.compile(r"(?m)^([ \t]*)(%s)[ \t]*:(?!=)" % NAME_RE.pattern)


def structure_fields(body, base_line):
    """[(field_name, line)]: auto-generated projections of a `structure ...
    where` body, restricted to the indentation of the first field (so a
    multi-line field's continuation lines are never mistaken for new fields)."""
    m = re.search(r"\bwhere\b", body)
    if not m:
        return []
    out = []
    base_indent = None
    for lm in FIELD_RE.finditer(body, m.end()):
        indent = len(lm.group(1))
        if base_indent is None:
            base_indent = indent
        elif indent != base_indent:
            continue
        line = base_line + body[:lm.start()].count("\n")
        out.append((lm.group(2), line))
    return out


def inductive_ctors(body, base_line):
    """[(ctor_name, line)]: constructor names of an `inductive ... | ctor ...`
    body, found as the identifier following each top-level (depth-0) `|`."""
    out = []
    depth = 0
    i, n = 0, len(body)
    while i < n:
        c = body[i]
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        elif c == "|" and depth == 0:
            j = i + 1
            while j < n and body[j] in " \t\n":
                j += 1
            nm = NAME_RE.match(body, j)
            if nm:
                line = base_line + body[:j].count("\n")
                out.append((nm.group(0), line))
                i = nm.end()
                continue
        i += 1
    return out


def build_index():
    """name -> list of (path, line, kind, mods, body) for every landed decl."""
    idx = {}
    for p in leanfinal_files():
        for d in decls(p):
            if d["kind"] == "example" or not d["name"]:
                continue
            short = d["name"].split(".")[-1]
            for key in {d["name"], short}:
                idx.setdefault(key, []).append(d)
            if d["kind"] == "structure":
                members = structure_fields(d["body"], d["line"])
            elif d["kind"] == "inductive":
                members = inductive_ctors(d["body"], d["line"])
            else:
                members = []
            for mname, mline in members:
                full = f'{d["name"]}.{mname}'
                entry = dict(d, name=full, line=mline, kind="def")
                # FULLY-QUALIFIED key only -- deliberately NOT also under the
                # bare `mname` short key. A bare field/ctor name is common
                # (`stageSigma`, `ram`, ...) and registering it as a short key
                # collided with an UNRELATED top-level declaration of the same
                # bare name elsewhere (`Uniformity.Density.Induction.stageSigma`
                # the def vs. `StageInterface.stageSigma` the field), silently
                # swapping in the wrong landing site for an already-correct
                # census row. The retirement-form targets this census ever
                # looks up are always fully qualified (`CertFamily.m`,
                # `CubicFamilyIndex.sep`, ...), so the short key buys nothing
                # here and only risks exactly that collision.
                idx.setdefault(full, []).append(entry)
    return idx


CITES = ("exists_slope_factorization", "fgmn_residual_mul", "agnprw_termination",
         "bBox1_cite", "exists_dvDissection", "fgmn_dvDissection_factor_eq")


def split_sig(body, kind, name):
    """Return (signature, definiens) for a declaration body.

    `signature` is everything between the name and the top-level `:=`
    (binders + `:` + type); `definiens` is what follows.  `structure`/
    `inductive` have no `:=`, so the whole tail is the signature.
    """
    i = body.find(name)
    tail = body[i + len(name):] if i >= 0 else body
    depth = 0
    j = 0
    while j < len(tail):
        c = tail[j]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif tail.startswith(":=", j) and depth == 0:
            return tail[:j], tail[j + 2:]
        j += 1
    return tail, ""


def norm(t):
    return re.sub(r"\s+", " ", t).strip()


def result_type(sig):
    """Crude last-arrow / after-colon result type of a signature."""
    s = norm(sig)
    # drop binders: take text after the last top-level `:` that starts the type
    depth = 0
    cut = None
    for i, c in enumerate(s):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == ":" and depth == 0 and not s.startswith("::", i):
            cut = i
            break
    ty = s[cut + 1:] if cut is not None else s
    return ty.strip()


# ---------------------------------------------------------------------------
# content-free (PLACEHOLDER-BODY) detection
# ---------------------------------------------------------------------------

def _top_comma(t):
    """Index of the first depth-0 `,` in `t`, or -1."""
    depth = 0
    for i, c in enumerate(t):
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        elif c == "," and depth == 0:
            return i
    return -1


def strip_quantifiers(t):
    """Peel leading `∀ … ,` / `∃ … ,` binder groups off a proposition."""
    t = t.strip()
    guard = 0
    while guard < 60:
        guard += 1
        m = re.match(r"^[\(\s]*[∀∃]", t)
        if not m:
            break
        j = _top_comma(t)
        if j == -1:
            break
        t = t[j + 1:].strip()
    return t.strip().rstrip(")").strip()


def top_conjuncts(t):
    """Split a proposition on depth-0 `∧`."""
    parts, depth, cur = [], 0, ""
    i = 0
    while i < len(t):
        c = t[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        if depth == 0 and c == "∧":
            parts.append(cur)
            cur = ""
        else:
            cur += c
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts]


TRIVIAL_TERMS = {"True", "True.intro", "trivial", "⟨⟩", "rfl", "Trivial"}


def content_free(prop):
    """`prop` asserts nothing: it is `True` under any prefix of binders."""
    core = strip_quantifiers(prop)
    core = core.strip().strip("()").strip()
    if core in TRIVIAL_TERMS:
        return True, "reduces to `True` after peeling binders"
    # implication whose conclusion is `True`
    parts = re.split(r"→", core)
    if len(parts) > 1 and parts[-1].strip() in TRIVIAL_TERMS:
        return True, "implication with conclusion `True`"
    cj = top_conjuncts(core)
    if len(cj) > 1 and all(strip_quantifiers(c).strip("() ") in TRIVIAL_TERMS for c in cj):
        return True, "conjunction of `True`s"
    return False, ""


def has_True_conjunct(prop):
    cj = top_conjuncts(strip_quantifiers(prop))
    if len(cj) < 2:
        return False
    return any(strip_quantifiers(c).strip("() ") in TRIVIAL_TERMS for c in cj)


# ---------------------------------------------------------------------------
# signed-vs-landed drift (the CONDITIONAL detector)
# ---------------------------------------------------------------------------

def binder_groups(sig):
    """Top-level binder groups of a signature, as (bracket, text) pairs."""
    out = []
    depth = 0
    i = 0
    cur = None
    while i < len(sig):
        c = sig[i]
        if c in "({[⦃":
            if depth == 0:
                cur = [c, ""]
            else:
                cur[1] += c
            depth += 1
        elif c in ")}]⦄":
            depth -= 1
            if depth == 0:
                out.append((cur[0], cur[1]))
                cur = None
            else:
                cur[1] += c
        elif depth == 0 and c == ":":
            break
        else:
            if depth:
                cur[1] += c
        i += 1
    return out


def hyp_binders(sig):
    """Explicit hypothesis binders, identified by the repo's `h…` naming."""
    out = []
    for br, txt in binder_groups(sig):
        if br not in "({":
            continue
        head = txt.split(":")[0].strip()
        names = head.split()
        if names and all(re.match(r"^h", n) for n in names):
            out.append(norm(txt))
    return out


def arrow_antecedents(sig):
    """Depth-0 `→` antecedents of the result type."""
    rt = result_type(sig)
    parts, depth, cur = [], 0, ""
    i = 0
    while i < len(rt):
        c = rt[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        if depth == 0 and rt.startswith("→", i):
            parts.append(norm(cur))
            cur = ""
            i += 1
            continue
        cur += c
        i += 1
    return parts  # antecedents only (conclusion dropped)


def hypothesis_count(sig):
    return len(hyp_binders(sig)) + len(arrow_antecedents(sig))
