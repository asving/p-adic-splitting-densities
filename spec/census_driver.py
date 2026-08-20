#!/usr/bin/env python3
"""Driver for the signed-name census (AUDIT 2026-08-20).

Uses the parsing instrument in `signed_name_census.py` (comment-stripping,
declaration extraction, retirement-form `example` targets, content-free
detection) and emits a per-chapter classification.

MECHANICAL PASS ONLY.  Every judgement this driver cannot make safely is
routed to UNRESOLVED rather than guessed — per the audit charge, an honest
unresolved list beats a tidy wrong table.

Buckets
  CITE             the name is one of the six signed literature cites
  PLACEHOLDER-BODY the SIGNED result type is content-free (`True` etc.) —
                   landing it asserts nothing.  Checked on the leanspec, not
                   on leanfinal, because it is the SIGNED statement that is
                   empty.  This is the I-D12 / E.51 class.
  PROVED           landed in leanfinal as theorem/lemma with the same
                   hypothesis count as signed
  CONDITIONAL      landed as theorem/lemma but with MORE hypotheses than
                   signed (an added binder / carried clause / restricted
                   stratum — the H.122 and C.114 shape)
  CARRIER          landed only as def/abbrev/structure — names the statement,
                   asserts nothing by itself
  UNLANDED         no landed declaration of that name
  UNRESOLVED       anything else (fewer hypotheses than signed, several
                   landed candidates of differing kinds, unparseable sig)

Run: python3 spec/census_driver.py [CHAPTER ...]
"""

import sys
import os
import collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import signed_name_census as SNC

SPECDIR = SNC.REPO + "/leanspec/Leanspec"

# leanspec kinds that constitute a SIGNED STATEMENT obligation.
# `axiom` = signed stub awaiting a landing.  theorem/lemma = signed with a
# leanspec-local proof.  def/abbrev/structure = the definitional layer.
PROP_KINDS = ("axiom", "theorem", "lemma")
DEF_KINDS = ("def", "abbrev", "structure", "inductive", "class", "instance",
             "opaque")


def signed_names(chapter):
    """[(name, kind, line, sig, label)] for one chapter's leanspec."""
    path = f"{SPECDIR}/Chap{chapter}.lean"
    if not os.path.exists(path):
        return None
    out = []
    for d in SNC.decls(path):
        if d["kind"] == "example":
            tgt = SNC.example_target(d["body"])
            if tgt:
                # retirement form: the stub was deleted and replaced by an
                # example USING the landed decl, so the leanspec elaborating
                # is itself the type-level check.
                out.append((tgt, "example-retired", d["line"], "", d["label"], ""))
            continue
        if not d["name"]:
            continue
        if d["kind"] not in PROP_KINDS + DEF_KINDS:
            continue
        try:
            sig, definiens = SNC.split_sig(d["body"], d["kind"], d["name"])
        except Exception:
            sig, definiens = "", ""
        out.append((d["name"], d["kind"], d["line"], sig, d["label"], definiens))
    return out


def classify(name, kind, sig, definiens, idx):
    short = name.split(".")[-1]
    if short in SNC.CITES:
        return "CITE", "one of the six signed cites"

    # Is the SIGNED statement content-free?  Computed here but NOT returned
    # yet: PLACEHOLDER-BODY must mean "LANDED and asserts nothing" -- a green
    # tick that proves nothing -- so landedness is checked first.  Ranking
    # placeholder-ness above landedness double-counts unlanded placeholders
    # (`CanonicalLadderConfig` is signed `True` but has no landed decl at all);
    # the chapter-I hand audit got this precedence right and this driver did not.
    empty, empty_why = False, ""
    if kind in PROP_KINDS and sig:
        try:
            rt = SNC.result_type(sig)
            cf, why = SNC.content_free(rt)
            if cf:
                empty, empty_why = True, f"signed result type asserts nothing ({why}): {rt.strip()[:50]}"
        except Exception:
            pass
    if kind in DEF_KINDS and definiens:
        d = definiens.strip().rstrip("\n").strip()
        if d in SNC.TRIVIAL_TERMS:
            empty, empty_why = True, f"signed definiens is `{d}` — asserts nothing"
        else:
            # ...and the same under a binder prefix (`∀ x, True`). A raw string
            # compare misses those: the hand audit found NS7Termination's
            # conclusion to be `True` where this driver first said CARRIER.
            try:
                cf, why = SNC.content_free(d)
                if cf:
                    empty, empty_why = True, f"signed definiens asserts nothing ({why}): {d[:50]}"
            except Exception:
                pass

    cands = idx.get(name) or idx.get(short) or []
    if not cands:
        if empty:
            return ("UNLANDED",
                    f"no landed declaration — AND the signature is a placeholder ({empty_why})")
        return "UNLANDED", "no landed declaration of this name"
    if empty:
        return "PLACEHOLDER-BODY", empty_why

    kinds = {c["kind"] for c in cands}
    where = f"{os.path.relpath(cands[0]['path'], SNC.REPO)}:{cands[0]['line']}"

    if kind in DEF_KINDS:
        # definitional layer: a landed def NAMES the statement; it does not
        # prove anything.  Same bucket the chapter-I unit used.
        if kinds & set(DEF_KINDS):
            return "CARRIER", f"definition landed at {where}"
        return "UNRESOLVED", f"signed as {kind} but landed as {sorted(kinds)} at {where}"

    # RETIREMENT FORM.  The leanspec deleted its stub and left an `example`
    # that USES the landed declaration, so the leanspec elaborating is itself a
    # type-level check that the landed name carries the signed type.  That is
    # the STRONGEST evidence available -- stronger than the hypothesis-count
    # heuristic below, which only compares binder arity textually.  Filing
    # these as UNRESOLVED (for want of a signature string) is what produced a
    # spurious 100/148 unresolved bucket in chapters G and H.
    if kind == "example-retired":
        if kinds & {"theorem", "lemma"}:
            thm = [c for c in cands if c["kind"] in ("theorem", "lemma")][0]
            where = f"{os.path.relpath(thm['path'], SNC.REPO)}:{thm['line']}"
            return "PROVED", f"retirement form: leanspec `example` type-checks the landed theorem at {where}"
        if kinds & set(DEF_KINDS):
            return "CARRIER", f"retirement form resolves to a definition at {where}"
        return "UNRESOLVED", f"retirement form but landed as {sorted(kinds)} at {where}"

    # signed as a Prop obligation
    if kinds & {"theorem", "lemma"}:
        thm = [c for c in cands if c["kind"] in ("theorem", "lemma")][0]
        where = f"{os.path.relpath(thm['path'], SNC.REPO)}:{thm['line']}"
        if not sig:
            return "UNRESOLVED", f"landed theorem at {where} but signed sig unparseable"
        try:
            lsig, _ = SNC.split_sig(thm["body"], thm["kind"], thm["name"])
            n_signed = SNC.hypothesis_count(sig)
            n_landed = SNC.hypothesis_count(lsig)
        except Exception:
            return "UNRESOLVED", f"landed theorem at {where}; signature comparison failed"
        if n_landed == n_signed:
            return "PROVED", f"theorem landed at {where} ({n_landed} hyps, matches signed)"
        if n_landed > n_signed:
            return ("CONDITIONAL",
                    f"landed at {where} with {n_landed} hyps vs {n_signed} signed "
                    f"(+{n_landed - n_signed} added binder/stratum)")
        return ("UNRESOLVED",
                f"landed at {where} with FEWER hyps ({n_landed}) than signed ({n_signed}) "
                "— stronger than signed, or a binder-counting artifact; needs a human read")
    if kinds & set(DEF_KINDS):
        return "CARRIER", f"landed only as {sorted(kinds & set(DEF_KINDS))} at {where}"
    return "UNRESOLVED", f"landed as {sorted(kinds)} at {where}"


ORDER = ["CITE", "PROVED", "CONDITIONAL", "CARRIER", "PLACEHOLDER-BODY",
         "UNLANDED", "UNRESOLVED"]


def main():
    chapters = sys.argv[1:] or list("BCDEFGHI")
    idx = SNC.build_index()
    grand = collections.Counter()
    for ch in chapters:
        names = signed_names(ch)
        if names is None:
            print(f"\n### chapter {ch}: NO leanspec file")
            continue
        buckets = collections.defaultdict(list)
        seen = set()
        for name, kind, line, sig, label, definiens in names:
            if (name, line) in seen:
                continue
            seen.add((name, line))
            b, why = classify(name, kind, sig, definiens, idx)
            buckets[b].append((name, kind, line, label, why))
        total = sum(len(v) for v in buckets.values())
        counts = {b: len(buckets[b]) for b in ORDER if buckets[b]}
        print(f"\n### chapter {ch}: {total} signed names  {counts}")
        for b in ORDER:
            for name, kind, line, label, why in sorted(buckets[b]):
                print(f"  {b:17s} {name:52s} [{kind};L{line};{label}] {why}")
        for b in buckets:
            grand[b] += len(buckets[b])
    print(f"\n### GRAND TOTAL {sum(grand.values())} signed names")
    for b in ORDER:
        if grand[b]:
            print(f"  {b:17s} {grand[b]}")


if __name__ == "__main__":
    main()
