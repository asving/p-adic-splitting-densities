/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H06
import Uniformity.ChapH.H11
import Uniformity.ChapH.H12
import Uniformity.ChapH.H18
import Uniformity.ChapH.H20
import Uniformity.ChapH.H26
import Uniformity.ChapH.H28
import Uniformity.ChapH.H38
import Uniformity.ChapH.H40
import Uniformity.ChapH.H42
import Uniformity.ChapH.H45
import Uniformity.ChapH.H60
import Uniformity.ChapH.H62
import Uniformity.ChapH.H70
import Uniformity.ChapH.H71
import Uniformity.ChapH.H72
import Uniformity.ChapH.H76
import Uniformity.ChapH.H96
import Uniformity.ChapH.H98

/-!
# Uniformity.ChapH.H99 — CHAPTER H'S CENSUS GATE

**Chapter H, NODE H.99** (`blueprint/CHAP-H_general_induction.md` §13), the chapter's last node.
Not a proof — a build-time census, in the style of chapter G's `G.78` and the landed
`Gates.lean:589` / `Drainage.lean:1160` blocks. Three columns:

1. **the axiom footprints** of every capstone-facing chapter-H declaration. Each line must print
   `[propext, Classical.choice, Quot.sound]` **or a subset of it**; anything else is a
   **stop-the-line** event (repo `CLAUDE.md`: *"Ground truth for the trusted base"*). In
   particular a `native_decide` anywhere in chapter H would surface here as `Lean.ofReduceBool`.
   (The blueprint's sketch says *"exactly"*; two lines in fact print the strict subset
   `[propext, Quot.sound]` — `TriangularUnitPivot.bijective` and `not_occupied_genreA2witness`
   never invoke choice. A strictly smaller footprint is a strengthening, so the gate's rule is
   stated as `⊆` here, matching `G.78`'s own wording *"or a subset of it"*.);
2. **the two-column numeric audits** at `q = 2` **and** `q = 3`, made executable. Every audit
   block in §§4–7 of the blueprint states its values at both columns; this is where they become
   machine-checked;
3. **the non-vacuity of the schema layer**, by exhibiting the three witness data.

## ⚠ Two deliberate departures from the blueprint's sketch, both strengthenings

**(a) The import list is explicit, not the chapter roll-up.** The blueprint's ENVIRONMENT line
says *"the census file imports the chapter roll-up"*, and `G.78` does exactly that
(`import Uniformity.ChapG`). Here the modules censused are listed one by one instead. The gate
then cannot silently lose a line to a roll-up that has not yet been regenerated — regenerating
`Uniformity/ChapH.lean` is the orchestrator's job, and a census that depends on it would report
a *stale* chapter. Nothing is lost: every name below is reached by one of the imports above, and
the file elaborates only if all of them exist.

**(b) Every `#eval` is paired with a `#guard`.** The blueprint's column (ii) is `#eval` plus an
expected-value comment. `#eval` *prints*; it does not fail. The `#guard` lines below assert the
same values as propositions, so a value drift is a **build error**, not a comment that quietly
stops matching. The `#eval`s are kept, verbatim from the blueprint, because the printed column is
what a human reads at review time.

**⚠ THIS FILE IS NOT IN ANY ROLL-UP.** Like `G.78` — which imports `Uniformity.ChapG` and is
therefore wired in the ROOT (`Uniformity.lean`) rather than in the chapter roll-up, to avoid an
import cycle — `H.99` is wired by the orchestrator, not by `Uniformity/ChapH.lean`. Its own
imports are individual node modules (departure (a)), so no cycle is possible either way; keeping
it out of the roll-up preserves the `G.78` shape and keeps the gate at the top of the graph.

**⚠ THE `#eval` COLUMN IS THE CHAPTER'S ARITHMETIC-AUDIT REGRESSION** (blueprint, carried
forward). If a future edit to `alphaBracket`, `uTwo`, `lawE`, `lawF`, `lawV1E2` or the censuses
changes any value, the change is caught **before** any proof breaks. That is the mechanism the
`G.23` refutation shows is needed: the refuted formula *proved fine* at `q = 2`, because the two
candidate laws `q^{2N−2k−1}` and `q^{2N−2k−2}` agree exactly there and every cross-check in that
chapter ran at `q = 2`. Hence the standing rule (H.29): **`q = 3` is mandatory in every column**.

DEPENDS: every node named below. **PROOF:** none (a census block).

**TEETH.** this gate IS the chapter's teeth roll-up; §16's disposition table is its index.

## Status

No declarations, public or private. Sorry-free, axiom-free — which is exactly what column (i)
asserts.
-/

set_option linter.style.longLine false

/-! ## (i) Axiom footprints — every line must print exactly
`[propext, Classical.choice, Quot.sound]`. -/

section AxCheck

-- H.98, the assembly (`GENIND.B` Step 5 ONLY — NOT `THEOREM GENIND.B`)
#print axioms Uniformity.Density.uniformity_of_package
#print axioms Uniformity.Density.drainage_of_package

-- H.96, the one unconditional base case
#print axioms Uniformity.Density.package_two

-- H.70, H.76 — the density-side lemmas the assembly rests on
#print axioms Uniformity.Density.undecidedSeq_antitone
#print axioms Uniformity.Density.efPair_forced_of_dvd

-- §§4–7, the arithmetic layer
#print axioms Uniformity.Density.Induction.alphaBracket_closed
#print axioms Uniformity.Density.Induction.uTwo_closed
#print axioms Uniformity.Density.Induction.uTwo_ratio_le

-- §10, the rate calculus
#print axioms Uniformity.Density.Induction.rate_close
#print axioms Uniformity.Density.Induction.rate_lossPriced

-- §8, the pivot layer, and its refuted-toy companion
#print axioms Uniformity.Density.Induction.TriangularUnitPivot.bijective
#print axioms Uniformity.Density.Induction.codexToy_not_surjective

-- §1, the schema layer's non-vacuity theorems
#print axioms Uniformity.Density.Induction.infinite_genreDatum_of_schema
#print axioms Uniformity.Density.Induction.not_occupied_genreA2witness

end AxCheck

/-! ## (ii) The two-column numeric audits, evaluated — and guarded.
The `#eval` lines are the blueprint's, with its expected values in the comments; each is
immediately followed by the `#guard` that turns a drift into a build error. -/

section NumericCensus

open Uniformity.Density.Induction

/-! H.18/H.20/H.21 — the α-prefix aggregate `b_{m,d}(μ)`. -/
#eval (alphaBracket 2 1 3, alphaBracket 3 1 2, alphaBracket 4 1 2)   -- expect (32, 54, 192)

#guard (alphaBracket 2 1 3, alphaBracket 3 1 2, alphaBracket 4 1 2) == (32, 54, 192)

/-! H.23/H.26/H.29 — the `m = 2` conservative complement, at both mandatory columns. -/
#eval (uTwo 2 6, uTwo 3 6)                                            -- expect (64, 567)

#guard (uTwo 2 6, uTwo 3 6) == (64, 567)

/-! H.38 — the `E`-law `(q−1)·q^(4N−5h−3)`, at `q = 2, 3, 5`. -/
#eval (lawE 2 6 1, lawE 3 4 1, lawE 5 3 1)                            -- expect (65536, 13122, 2500)

#guard (lawE 2 6 1, lawE 3 4 1, lawE 5 3 1) == (65536, 13122, 2500)

/-! H.40, H.42 — the `F`-law and the `V1E2` law. -/
#eval (lawF 2 6 1, lawV1E2 2 5 1)                                     -- expect (1024, 12288)

#guard (lawF 2 6 1, lawV1E2 2 5 1) == (1024, 12288)

/-! H.45 — the two quartic-stage censuses at `Q = 3`. -/
#eval (splitEqCensus 3, inertCensus 3)                                -- expect (1, 3)

#guard (splitEqCensus 3, inertCensus 3) == (1, 3)

/-! The `q = 3` column of the `m = 2` closed form and its rate, spelled out (H.26, H.27): the
letter factor `(Q − 1)` is invisible at `Q = 2`, so this column is the one that can see it. -/
#eval (uTwo 3 1, uTwo 3 2, uTwo 3 3, uTwo 3 4, uTwo 3 5, uTwo 3 6)    -- expect (1, 3, 15, 45, 189, 567)

#guard (uTwo 3 1, uTwo 3 2, uTwo 3 3, uTwo 3 4, uTwo 3 5, uTwo 3 6) == (1, 3, 15, 45, 189, 567)

#guard [2, 3, 4, 9].all fun Q => [1, 2, 3, 4, 5, 6, 7, 8, 9].all fun N =>
  uTwo Q N ≤ N * Q ^ (N - 1)

end NumericCensus

/-! ## (iii) Non-vacuity of the schema layer — the three witness data. -/

section NonVacuity

#check (Uniformity.Density.Induction.genreE2 0 : Uniformity.Density.Induction.GenreDatum)
#check (Uniformity.Density.Induction.genreA2witness : Uniformity.Density.Induction.GenreDatum)
#check (Uniformity.Density.Induction.genreD2bwitness : Uniformity.Density.Induction.GenreDatum)

end NonVacuity
