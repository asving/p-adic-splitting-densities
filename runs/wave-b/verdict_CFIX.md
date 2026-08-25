# Unit CFIX verdict — fixing the census's three parser-artifact genres (XSC's finding)

Source of the bug report: `runs/wave-b/verdict_XSC.md` ("24 false-positives / parser
artifacts" across chapters E, G, H). Touched file: `spec/signed_name_census.py` only
(`spec/census_driver.py` needed no change — the bug was entirely in the shared parsing
instrument, not in the classification driver). No Lean files touched. No commit made.

## Genre 1 — auto-generated structure-field / inductive-constructor names

**Symptom.** `CertFamily.m` (G.05a), `CubicFamilyIndex.{sep,dbl,tierI,tierII,bTier}`
(G.62a), `CapBranch.{ram,twoSided,und}` (H.88), `LeafE.{ram,twoSided,splitEq,inert,
splTail,und}` (H.91), `StageLeaf.{ram,twoSided,inert}` (H.73) all read UNLANDED although
they are landed the instant their parent `structure`/`inductive` lands.

**Root cause.** `decls()` only ever matches `DECL_RE` (an explicit `def`/`theorem`/...
keyword at line-start). A field inside `structure X where field : T` or a constructor
`| ctor : T` inside `inductive X | ctor ...` never gets its own `DECL_RE` hit — Lean
auto-generates `X.field`/`X.ctor`, but the census's declaration scanner has no line to
match for it. `build_index()` (leanfinal side) therefore never had an entry for these
names at all.

**Denominator investigation (as directed).** Checked whether leanspec's own parsing of
these same names double-counts them: grepped every `leanspec/Leanspec/Chap*.lean` for a
literal `structure`/`inductive` restatement of `CertFamily`, `CubicFamilyIndex`,
`CapBranch`, `LeafE`, `StageLeaf` — none exists. leanspec only ever *names* these members
via **retirement-form `example`s** (`example : CertFamily O n N → ℕ := CertFamily.m`,
`example : Fin 3 → CubicFamilyIndex := CubicFamilyIndex.sep`, one `example` per member —
confirmed at `leanspec/Leanspec/ChapG.lean:179,990-994` and the `ChapH.lean:1287-1514`
block). Each such `example` is already exactly ONE signed-name entry in
`signed_names()`'s output; there is no parallel expansion on the leanspec side that would
create a second entry for the same member. **Conclusion: match constructors/fields to
their parent's landed declaration (option (a) of the two offered), not exclude them from
the universe** — excluding them would be wrong (leanspec is deliberately asserting these
typed retirement checks; they should resolve, not vanish), and matching them touches only
`build_index()`, which `signed_names()` (the function that produces the denominator) never
calls. This genre changes zero denominators, chapter-by-chapter or grand total.

**Fix.** Added `structure_fields(body, base_line)` and `inductive_ctors(body, base_line)`
to `signed_name_census.py`, invoked only from `build_index()` (never from `signed_names()`,
which is what walks leanspec — this is the mechanism that keeps the denominator
untouched). Each auto-member is registered as a synthetic `kind="def"` entry keyed by its
**fully-qualified** name only (`CertFamily.m`, `CubicFamilyIndex.sep`, ...) — deliberately
NOT also under the bare short key `m`/`sep`/... (see the false-start below).

**False start caught before landing.** The first draft also registered the bare short key
(mirroring how non-synthetic decls register both `d["name"]` and its short form). This
collided: `StageInterface.stageSigma` (an unrelated structure field,
`leanfinal/Uniformity/ChapH/H09.lean:89`) and `Uniformity.Density.Induction.stageSigma`
(the real top-level `def`, `leanfinal/Uniformity/ChapH/H73.lean:61`) share the bare name
`stageSigma`. Registering the synthetic field under the bare key made it collide with the
genuine `stageSigma` def already in the index, and since `H09.lean` sorts before
`H73.lean`, the already-correct CARRIER row for `stageSigma` (H.73/H.74 dictionary) started
reporting the wrong landing site (`H09.lean:89` instead of `H73.lean:61`) — same bucket,
wrong evidence. Caught by diffing the full census output before/after and noticing a row
whose **location** changed with no genre explanation. Fixed by keying synthetic members
under the fully-qualified name only; retirement-form targets are always fully qualified
in this repo, so nothing is lost.

## Genre 2 — `inferInstance` term-level false identifier hits

**Symptom.** `inferInstance` reads as five separate UNLANDED "signed names"
(`leanspec/Leanspec/ChapH.lean:1290,1291,1450,1515,1516`).

**Root cause.** `example_target()` extracts the head identifier of an `example`'s `:=`
term as the retirement-form target. For `example : DecidableEq StageLeaf := inferInstance`,
that head identifier is the generic Lean-core term `inferInstance` itself — not a
declared name. This is a typeclass-resolution check ("some instance exists"), categorically
different from `example : CertFamily O n N → ℕ := CertFamily.m` (which does name a specific
declaration). `inferInstance` was never a name anyone declared, so it can never resolve to
anything and manufactures a UNLANDED row for a non-name every time it appears.

**Fix.** One added check in `example_target()`, right after the candidate identifier is
extracted: `if cand == "inferInstance": return None`. This is an exact-identifier check
(not the tuple's `startswith` style used for `by `/`fun `/etc.), so it cannot false-positive
on some other name that merely starts with the same letters.

**Denominator effect (expected and correct).** Excluding `inferInstance` genuinely shrinks
the signed-name universe by exactly the 5 occurrences in chapter H — these were never real
signed names, so removing them is not a "genre exception to the invariant," it is the
invariant working as intended (garbage was never supposed to be in the universe).

## Genre 3 — inline-attribute declarations invisible to `DECL_RE`

**Symptom.** `ladderState_wf` (E.19) reads UNLANDED although
`leanfinal/Uniformity/ChapE/E19.lean:127` has `@[reducible] def ladderState_wf ...`.

**Root cause.** `DECL_RE` required the decl keyword (after optional `MODIFIERS`) to start
right after line-start whitespace. An inline `@[attr]` on the same line as the keyword
was invisible — the line matched nothing, so the whole declaration silently vanished from
`decls()`'s output. (An attribute on its OWN line was already fine and remains fine: the
decl keyword still starts its own line below it, so nothing new is needed there.)

**Fix.** Added an optional, single-line-only attribute-prefix group to `DECL_RE`:
`ATTR_RE = r"(?:@\[[^\]\n]*\][ \t]*)*"`, inserted between `indent` and `mods`.

**Denominator investigation (this genre, both sides — not asked for explicitly but
necessary since `DECL_RE` is shared code).** Grepped every `leanspec/Leanspec/Chap*.lean`
for the same inline-attribute pattern (attribute, then zero or more `MODIFIERS`, then a
decl keyword, all on one line) and found exactly **one** hit that a plain
"`@\[...\]` immediately followed by a kind keyword" grep had missed on the first pass
(the intervening `noncomputable` modifier hid it from that narrower check):
`leanspec/Leanspec/ChapB.lean:572`, `@[reducible] noncomputable def instFieldResField
{φ : Polynomial O} (hφ : IsKey φ) : Field (resField φ) := ...` (node **B.25b**). This
declaration was previously invisible to the census **on both sides at once** — it was
never even attempted as a signed name, let alone marked UNLANDED. Fixing the shared
`decls()` parser necessarily surfaces it now (it is landed verbatim at
`leanfinal/Uniformity/ChapB/B25.lean:89`, so it resolves straight to CARRIER).

**Decision: keep it, disclosed.** This is not the constructor/field genre's "excluded vs.
matched" choice — there is no leanspec-side double-count to worry about (there is exactly
one occurrence, and it was never counted at all before). Special-casing the `DECL_RE` fix
to apply only inside `leanfinal/` (to protect the denominator) would leave a known,
identified parser blind spot in place on the signed side, in a repo whose explicit
discipline is "never paper over a gap." Chapter B's total therefore rises by exactly 1
(141 → 142), and it lands as CARRIER (not a bucket change requiring any judgment call).

## Before / after (full run, `python3 spec/census_driver.py`, all 8 chapters)

| chapter | before | after | Δ | what moved |
|---|---|---|---|---|
| B | 141 {CARRIER 24} | 142 {CARRIER 25} | denom +1 | `instFieldResField` newly surfaced (genre 3 side-effect), UNLANDED→n/a, straight to CARRIER |
| C | 356 {UNLANDED 72} | 356 {UNLANDED 72} | 0 | untouched (out of scope; no genre-3/1/2 hits changed anything here) |
| D | 130 {UNLANDED 3} | 130 {UNLANDED 3} | 0 | untouched (D's 3 remaining UNLANDED are the DESIGN-voided names XSC already found; not this genre) |
| E | 119 {CARRIER 47, UNLANDED 3} | 119 {CARRIER 48, UNLANDED 2} | 0 | `ladderState_wf` UNLANDED→CARRIER (genre 3) |
| F | 60 {CARRIER 45} | 60 {CARRIER 45} | 0 | untouched |
| G | 139 {CARRIER 32, UNLANDED 7} | 139 {CARRIER 38, UNLANDED 1} | 0 | 6 names UNLANDED→CARRIER (genre 1): `CertFamily.m` + 5× `CubicFamilyIndex.*` |
| H | 276 {CARRIER 57, UNLANDED 22} | 271 {CARRIER 69, UNLANDED 5} | denom −5 | 12 names UNLANDED→CARRIER (genre 1: `CapBranch.*`×3, `LeafE.*`×6, `StageLeaf.*`×3); 5× `inferInstance` removed entirely (genre 2) |
| I | 18 {UNLANDED 9} | 18 {UNLANDED 9} | 0 | untouched (I's 9 are DESIGN/BLOCKED fire-banned names, not this genre) |
| **GRAND TOTAL** | **1239** | **1235** | **−4** | = +1 (B, genre 3) − 5 (H, genre 2) exactly |
| GRAND CARRIER | 463 | 483 | +20 | = 1(B) + 1(`CertFamily.m`) + 5(`CubicFamilyIndex.*`) + 3(`CapBranch.*`) + 6(`LeafE.*`) + 3(`StageLeaf.*`) + 1(`ladderState_wf`) |
| GRAND UNLANDED | 116 | 92 | −24 | = 6(G) + 12(H genre 1) + 5(H genre 2) + 1(E) |
| GRAND PROVED | 647 | 647 | **0** | unchanged — the invariant that mattered |
| GRAND CONDITIONAL | 5 | 5 | 0 | unchanged |
| GRAND CITE | 2 | 2 | 0 | unchanged |
| GRAND PLACEHOLDER-BODY | 5 | 5 | 0 | unchanged |
| GRAND UNRESOLVED | 1 | 1 | 0 | unchanged |

**PROVED/CONDITIONAL/CITE/PLACEHOLDER-BODY are byte-identical before and after** — the
fix touched only UNLANDED rows belonging to the three named artifact genres (plus the one
disclosed genre-3 side effect in B, which is also a pure UNLANDED-universe/CARRIER
question, not a PROVED one). Chapters C, D, F, I are untouched line-for-line.

## Diff of every affected row (`diff <before> <after>`, chapter-total lines + row moves)

```
2c2
< ### chapter B: 141 signed names  {'CITE': 1, 'PROVED': 113, 'CONDITIONAL': 3, 'CARRIER': 24}
> ### chapter B: 142 signed names  {'CITE': 1, 'PROVED': 113, 'CONDITIONAL': 3, 'CARRIER': 25}
+  CARRIER   instFieldResField   [def;L572;B.25b] definition landed at leanfinal/Uniformity/ChapB/B25.lean:89

635c636
< ### chapter E: 119 signed names  {..., 'CARRIER': 47, 'UNLANDED': 3}
> ### chapter E: 119 signed names  {..., 'CARRIER': 48, 'UNLANDED': 2}
+  CARRIER   ladderState_wf   [axiom;L599;E.19] landed only as ['def'] at leanfinal/Uniformity/ChapE/E19.lean:127
-  UNLANDED  ladderState_wf   [axiom;L599;E.19] no landed declaration of this name

818c819
< ### chapter G: 139 signed names  {'PROVED': 100, 'CARRIER': 32, 'UNLANDED': 7}
> ### chapter G: 139 signed names  {'PROVED': 100, 'CARRIER': 38, 'UNLANDED': 1}
+  CARRIER   CertFamily.m               [example-retired;L179;G.05a] retirement form resolves to a definition at leanfinal/Uniformity/ChapG/G05.lean:37
+  CARRIER   CubicFamilyIndex.bTier     [example-retired;L994;G.62a] ... leanfinal/Uniformity/ChapG/G62.lean:83
+  CARRIER   CubicFamilyIndex.dbl       [example-retired;L991;G.62a] ... leanfinal/Uniformity/ChapG/G62.lean:80
+  CARRIER   CubicFamilyIndex.sep       [example-retired;L990;G.62a] ... leanfinal/Uniformity/ChapG/G62.lean:79
+  CARRIER   CubicFamilyIndex.tierI     [example-retired;L992;G.62a] ... leanfinal/Uniformity/ChapG/G62.lean:81
+  CARRIER   CubicFamilyIndex.tierII    [example-retired;L993;G.62a] ... leanfinal/Uniformity/ChapG/G62.lean:82
-  UNLANDED  (the same 6 names)         no landed declaration of this name

959c960
< ### chapter H: 276 signed names  {'PROVED': 197, 'CARRIER': 57, 'UNLANDED': 22}
> ### chapter H: 271 signed names  {'PROVED': 197, 'CARRIER': 69, 'UNLANDED': 5}
+  CARRIER   CapBranch.ram/twoSided/und            -> leanfinal/Uniformity/ChapH/H88.lean:42
+  CARRIER   LeafE.ram/twoSided/splitEq/inert/splTail/und  -> leanfinal/Uniformity/ChapH/H91.lean:56
+  CARRIER   StageLeaf.ram/twoSided/inert          -> leanfinal/Uniformity/ChapH/H73.lean:55/56/57
-  UNLANDED  (the same 12 names)        no landed declaration of this name
-  UNLANDED  inferInstance (x5, L1290/1291/1450/1515/1516)   -- removed entirely, not reclassified

1257c1253
< ### GRAND TOTAL 1239 signed names
> ### GRAND TOTAL 1235 signed names
  CARRIER    463 -> 483
  UNLANDED   116 -> 92
  (PROVED 647, CONDITIONAL 5, CITE 2, PLACEHOLDER-BODY 5, UNRESOLVED 1 -- all unchanged)
```

Chapters C, D, F, I: zero diff lines (confirmed via full `diff` of the two complete runs;
not excerpted above since there is nothing to show).

## Reproduction

```
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
python3 spec/census_driver.py > /tmp/after.txt         # current tree (fix applied)
git stash push -- spec/signed_name_census.py            # revert the fix only
python3 spec/census_driver.py > /tmp/before.txt
git stash pop                                            # restore the fix
diff /tmp/before.txt /tmp/after.txt
```
