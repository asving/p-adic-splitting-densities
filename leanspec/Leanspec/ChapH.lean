import Uniformity

/-!
# Chapter H — THE GENERAL INDUCTION: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-H_general_induction.md` (99 nodes, **192 written / 190 signed**
declarations), landed in the isolated `leanspec` environment **before** the chapter-H fleet fires,
in the blueprint's node order `H.01 … H.99` (`H.99` is a gate/census block, not a declaration).

**STATE (read this first): RETIRED, 2026-08-15.** Chapter H is complete in `leanfinal`, so every
stub here has been diffed against its landed declaration and replaced by an `example` — no `axiom`
remains. **191 declarations retired / 261 retirement `example`s / 5 findings (R1–R5) / 0 deliberate
residues / 0 substantive divergences.** Full accounting in the RETIREMENT CENSUS below; everything
above it in this header is the pre-retirement gate record.

**AMENDED 2026-08-15 (later the same day): R3 IS CLOSED and the last residue is GONE.** The one
declaration this file kept as a real local `def` — `stageIfaceE`, the only `StageInterface`
inhabitant in the repo — has been landed in `leanfinal` (`Uniformity/ChapH/H09w.lean`, the H.09
witness file, together with the genre-F witness `stageIfaceF` that §16 TODO item 14 owed) and is now
retired here like every other declaration: 190 + 1 = **191** retired, 253 + 8 = **261** `example`s
(one type diff + seven field `rfl`s). Nothing in this file is a local definition any more.

## FILE LAYOUT AND NAMESPACE (the two governing deviations, both recorded)

* **ONE file**, `leanspec/Leanspec/ChapH.lean`, per CHAP-H §15 ("one file", chapter G's convention).
  It is NOT added to `leanspec/Leanspec.lean` by this unit — the orchestrator wires the roll-up
  import (concurrent stub-gate agents share `leanspec/`); build it with the module target
  `lake build Leanspec.ChapH` or `lake env lean Leanspec/ChapH.lean`.
* **Everything is wrapped in `namespace LeanspecH`, per PA-4 / GC-6.6 of
  `blueprint/CONVENTIONS_2026-08-15.md`** — this OVERRIDES CHAP-H §15's "with the real namespaces"
  phrasing, which would reproduce the ~190-collision structure chapter G hit (PA-2). Consequently
  the blueprint's `namespace Uniformity.Density.Induction` / `namespace Uniformity.Density` headers
  in the SIGNATURE blocks are DROPPED here and every declaration is flat inside `LeanspecH`; the
  landed-side namespace assignment (definitions → `Uniformity.Density.Induction`, theorems about
  landed objects → `Uniformity.Density`) is recorded per node in the comments below and is what the
  fleet must land. The one textual consequence inside a signature: H.95's `Induction.RateSpecies`
  is written `RateSpecies` here (same declaration, one namespace level flattened away).
* **Environments.** CHAP-H's ENV-H1…ENV-H5 need NO section `variable` blocks: every SIGNATURE in
  the blueprint carries its binders inline (`{O : Type*} [CommRing O] …`, `{F K : Type*} …`,
  `{R : Type*} [CommRing R]`). Nothing here is bound by a section variable, so no ENV under- or
  over-binding of the chapter-G `D4` kind is possible in this file.

## What is real and what is a stub

Per stage-0e rule 1 (CHAP-H §15 rule 1): the definitional layer lands as REAL BODIES — 5
`structure`s (`GenreDatum`, `StageInterface`, `TriangularUnitPivot`, `RecursionLegs`, `A1Cell`), 3
`inductive`s (`StageLeaf`, `CapBranch`, `LeafE`) and the `def`s (incl. the three witness data
`genreE2`, `genreA2witness`, `genreD2bwitness`, whose proof fields must elaborate — §15's "sharpest
test of §3"). Theorem-shaped nodes land as `axiom` stubs at the exact signed type. **No `sorry`.**
This file is never imported by `leanfinal` or `leancheck`; it carried `axiom`s by design and proves
nothing. **As of the 0e closing pass (2026-08-15) it carries none:** every stub is retired to an
`example` against its landed declaration — see the RETIREMENT CENSUS below. The paragraphs of this
header that describe the pre-retirement state are kept as the gate's record and read in the past
tense; the census is the current state.

## Withdrawn / not signed (CHAP-H §15 rules 2–4)

* **`GenreDatum.normIdx` (H.54) is NOT signed** — §15 rule 2: H.54's SIGNATURE NOTE withdraws the
  `Exists.choose` form in favour of `stageLift'`, which is what is signed below. The blueprint's
  `stageLift` (the `normIdx`-valued variant) is therefore also not signed: it is the same node's
  superseded form, and its body cannot be written without `normIdx`.
* **`package_three_of_drainage` (H.97) is NOT signed** — §15 rule 3; `package_three_of_rate` is
  signed in its place, at the type displayed in H.97's own ⚠ SIGNATURE NOTE (blueprint line 5923).
* **`w11_node_shape` (H.84) IS signed** (§15 rule 4 leaves it to the stub agent's discretion; it is
  a one-line `And` of two `rfl`s and costs nothing to carry).

Count reconciliation. §15's 190 is reproduced exactly: 192 declarations are written in the
SIGNATURE blocks; drop `normIdx` and its dependent `stageLift` (rule 2) and
`package_three_of_drainage` (rule 3), and add back the two replacement types the blueprint displays
in its own SIGNATURE NOTES, `stageLift'` and `package_three_of_rate` — 192 − 3 + 1 = **190
signable**. Of those, TWO are withdrawn HERE because the gate REFUTED them —
`rate_lossPriced` (H.72, D4) and `band_not_consulted` (H.89, D8) — leaving **188 signed**:
mechanically, **146 `axiom` + 5 `structure` + 3 `inductive` + 33 `def` + 1 `noncomputable def`**,
where 146 is §15's `theorem` column (148) minus the two refutations. The file carries exactly ONE
declaration that is not a signed blueprint declaration: `stageIfaceE`, the `StageInterface` witness
that F2 records as missing and that D4's refutation needs (34 `def`s appear in a grep).

## RETIREMENT CENSUS (stage-0e CLOSING pass, 2026-08-15 — chapter H is COMPLETE in `leanfinal`)

Chapter H landed in full: 99 node files `leanfinal/Uniformity/ChapH/H01.lean … H99.lean`, build
green. **Every signed stub in this file has been retired**, i.e. moved to the LANDED state of the
`Leanspec.lean` stub lifecycle — the local declaration is deleted and replaced by a bodyless
`example` at the EXACT signed type, applied to the landed constant with every binder reapplied BY
NAME. `grep -c '^axiom' Leanspec/ChapH.lean` is now **0**, and `open Uniformity.Density.Induction`
was added to the header block so the flat `LeanspecH` names below resolve to the landed
declarations — that resolution IS the diff.

**RETIRED: 190 declarations / 253 retirement `example`s / 5 findings (R1–R5) / 1 deliberate
residue.**

* **146** theorem-shaped (was `axiom`) → 146 `example`s, one each. Every one applies the landed
  constant with all binders named, so a divergence in binder NAME, binder COUNT, implicit/explicit
  status, universe, or instance telescope is a hard error here. **All 146 typechecked on the first
  pass with zero repairs**: no binder-name, binder-order, universe or instance divergence anywhere
  in the chapter (the chapter-G `D4` class of ENV under-binding cannot arise here — every CHAP-H
  signature binds inline).
* **42** definitional (5 `structure`, 3 `inductive`, 33 `def`, 1 `noncomputable def`) → 105
  `example`s. `def`s are retired at BOTH available strengths (the §A-5 / G.66 precedent): the
  type-level `example`, plus a `rfl` (or `Iff.rfl`) diff of the BODY, per equation for the
  `match`-defined ones. The two well-founded recursions (`alphaBracket`, `uTwo`) do not reduce by
  `rfl`, so their bodies are diffed through the landed equation lemmas (`by rw [alphaBracket]`,
  `by rw [uTwo]`) — three equations for `uTwo` including D1's cured DEPENDENT guard — and again
  numerically: the `#eval` gates at the bottom of this file now execute on the **landed** bodies.
  `structure`s get two checks each, an anonymous-constructor `example` pinning FIELD ORDER and every
  field type, and a `have` block pinning every field NAME with its projected type; `inductive`s get
  one `example` per constructor plus `inferInstance` for each `deriving` class.
* **2** declarations the gate had REFUTED and WITHDRAWN, `rate_lossPriced` (H.72, D4) and
  `band_not_consulted` (H.89, D8), which the blueprint repaired IN PLACE (AMENDMENT A-H.1/D4 and
  A-H.1/D8) and the fleet landed at the repaired types. Retired at the **amended** types — see
  findings R1 and R2 at the nodes themselves. 188 signed + 2 amended = **190** = §15's signable
  count.
* **1** declaration that is not a blueprint node at all, `stageIfaceE` → 8 `example`s (type +
  seven field `rfl`s). It was this pass's one deliberate residue — a real local `def`, kept because
  it had NO landed counterpart to retire against, and load-bearing here as the only
  `StageInterface` inhabitant in the repo (finding R3) and the witness that makes D4's refutation
  machine-checked. **CLOSED later on 2026-08-15**: it is landed in
  `leanfinal/Uniformity/ChapH/H09w.lean` (verbatim, proof terms included) and retired here, so the
  residue count is now zero. 190 blueprint declarations + this one = 191 retired.

### FINDINGS (the product of this pass)

* **R1 / R2 — two nodes' signed types CHANGED between the stub gate and the landing.** H.72
  `rate_lossPriced` landed at the gate's CANDIDATE A, H.89 `band_not_consulted` landed with the
  `1 ≤ N` guard. Both changes are sanctioned blueprint amendments (A-H.1/D4, /D8) triggered by this
  file's own refutations, and the landed types are byte-identical to the amended SIGNATURE blocks —
  **not** silent drift. Recorded at the nodes, where the refuted displays are also retained verbatim
  as provenance. *The reader must not treat those commented displays as what is proved.*
* **R3 — F2 WAS STILL OPEN, and it had moved into `leanfinal`; CLOSED the same day.** As found:
  the landed corpus contained **no** inhabitant of `StageInterface` (`grep -rn ': StageInterface'
  leanfinal/` found only binders and docstrings, 2026-08-15), so `leanfinal`'s H.72 was a theorem
  about a possibly-empty type; the repo's only witness was `stageIfaceE` here, and `leanspec` is
  never imported by `leanfinal`. **Closure (2026-08-15, de-vacuity unit):**
  `leanfinal/Uniformity/ChapH/H09w.lean` lands `stageIfaceE` (ported verbatim from this file, proof
  terms included) AND `stageIfaceF (N H : ℕ) (l : StageLeaf) : StageInterface genreD2bwitness N H 4`,
  the genre-F instance §3's design note claimed and §16 TODO item 14 owed — over the `f₁ = 2` datum
  item 14 names, where `hbracket`'s MASS normalization is visible (the witness's bracket at
  `κ = μ = 2` is H.21's certified `alphaBracket 4 1 2 = 192 = ghost 16 × letters 12`, and the
  letter-sum candidate is machine-checked NOT to satisfy `hbracket` there). Both footprints are Lean
  core only. What is NOT closed: `(CS-1Q)`/`(CS-3)` still have no teeth anywhere in the corpus and
  `HYP.36` stays CARRY — inhabitation is not per-genre verification.
* **R4 — D5 IS CLOSED: `A1Cell.deltaSubst`'s stub-side determination was landed unchanged.** The
  blueprint's PROOF field pinned only `expCoeff`; the three `rfl` diffs at H.94 confirm the fleet
  landed this file's choice for all seven unpinned fields (`offset`, `stride`, `expConst`,
  `visCoeff`, `visConst`, `coeff`, `σ`). `A1Cell.prod` matches likewise, field by field.
* **R5 — D7 IS CLOSED, and D1/D2/D3/D6 are confirmed cured on the landed side.** `RecursionLegs`
  landed with `hdesc`'s `1 ≤ N` guard and `halpha`'s `m * (k + 1) < N` window (A-H.1/D7, A-H.2), one
  name per field (D6); `rate_close` landed with `hmc : m < c`. The stub had already been RE-SIGNED to
  those repaired forms, and the structure retirement's constructor + field-name diff certifies the
  two sides agree exactly. D1 (`uTwo`'s dependent guard), D2 (`alphaBracket`'s `decreasing_by`) and
  D3 (H.06's `Nat.coprime_two_right`) are cured identically in `leanfinal`; D3 is unobservable from
  outside (`hcop` is a proof field), so it is certified only by `leanfinal` building.
* **Bookkeeping slip in this file's own header, pre-existing (not a `leanfinal` finding):** the D8
  bullet below says "Signed count is therefore **189**, not 190", while the count-reconciliation
  paragraph above says **188**. 188 is correct — TWO declarations were withdrawn (D4 and D8), not
  one. The retirement census above supersedes both numbers.

**No substantive divergence between any signed stub type and its landed declaration was found.**
Zero repairs were needed to make the 253 diffs typecheck. The diff was negative-controlled
(2026-08-15): perturbing a theorem's conclusion, a `def` body's `rfl`, a `structure` field name, a
well-founded equation, and one `deltaSubst` field each produced a hard error on this file, and the
field-name control's message named `Uniformity.Density.Induction.GenreDatum`, confirming that
resolution really goes to the LANDED declarations and not to a surviving local stub.

## DEFECT LIST (stage-0e gate, 2026-08-15; recorded here, NOT repaired in the blueprint)

* **D1 — H.23 `uTwo` DOES NOT TERMINATE AS WRITTEN (elaboration failure; CURED stub-side,
  minimally).** The body's recursive call `uTwo Q (N + 2 - 2 * k)` sits inside a non-dependent
  `if 1 ≤ k ∧ 2 * k ≤ N + 1 then … else 0`, so the well-founded-recursion goal is
  `N + 2 - 2 * k < N + 2` with `k` unconstrained — FALSE at `k = 0`. Cured by writing the
  guard as a DEPENDENT `if h : …`, which puts `1 ≤ k` in the termination context, plus
  `decreasing_by omega`. Zero semantic change (`dite` and `ite` are equal on a `Decidable`
  proposition); the recursion's VALUES are unaffected and are certified below (`#guard`, H.29's six
  values at `q = 2` and six at `q = 3`).
* **D2 — H.18 `alphaBracket` needs an explicit `decreasing_by` (incomplete body).** Same class,
  benign: the goal `μ - k < μ + 1` is unconditionally true, so only the tactic is missing.
* **D3 — H.06 `genreE2.hcop` cites a mathlib name that does not exist at the pin
  (`v4.31.0`).** `Nat.coprime_two_right_iff_odd` is not in this mathlib; the lemma is
  `Nat.coprime_two_right : n.Coprime 2 ↔ Odd n` (`Mathlib/Data/Nat/Prime/Basic.lean:148`). Landed
  with the corrected name. Class: stale-Mathlib-name (training-data smell), no semantic content.
* **D4 — H.72 `rate_lossPriced` IS FALSE (REFUTED, machine-checked; withdrawn, not signed).**
  This is the node §16 item 1 calls *"the one node where a wrong statement would be invisible to
  the stub gate"*. It is not invisible: it is refuted here.
  1. *The refutation.* `stageIfaceE` (in the gate section) is a genuine `StageInterface (genreE2 0)
     2 0 4` — genre E at `t = 0`, `stageWindow = 2`, `stageLoss = entryCodim = slack = 0`, all
     eleven fields proved, `stageLoss = 0` being exactly the `EFF.GENIND.199` exemption §3's design
     note invokes. At it, H.72's conclusion reads `4 ≥ 8`, and `example : ¬ (…) := by decide`
     checks that. Had the axiom been signed, `rate_lossPriced stageIfaceE` would prove `False`.
  2. *Not a one-point accident.* A sweep over five genre data × `N < 7` × `H < 5` × four side
     lengths × `stageWindow`, `stageLoss`, `entryCodim`, `slack < 6`, filtered by `hS`/`hwin`/
     `hprice` exactly as the structure imposes them, finds 29 418 counterexamples among 2 777 911
     admissible configurations (independent Python sweep; the Lean gate re-runs a smaller grid).
  3. *The diagnosis — WHICH terms of the `2*`-clearing are wrong.* Chain `hwin` and `hprice`
     directly: multiply `hwin` by `2·f₁` to get `2·keyDeg·(N−1−H) ≤ 2·f₁·M_G + 2·f₁·Δ_G`, bound
     `2·f₁·Δ_G` by `hprice`, then add `2·keyDeg·H + H` to both sides (using `S ≥ 2·keyDeg`, which
     `hS` + H.33 give, so `(S − 2·keyDeg)` does not truncate). What comes out is
     **CANDIDATE A: `2·(f₁·M_G) + (S+1)·H + 2·C_G^extra + 2·O_G ≥ 2·keyDeg·(N−1−H) + 2·keyDeg·H + H`**
     — zero counterexamples on the whole sweep, and checked in the gate. The signed display is
     Candidate A with **every term doubled EXCEPT the window term `2·(f₁·M_G)` and the lone `+H`**,
     and with the slack moved to the right as a subtraction. So the `2*`-clearing was applied to
     five of the seven terms. **CANDIDATE B** (Candidate A uniformly doubled:
     `4·(f₁·M_G) + 2·(S+1)·H + 4·C + 4·O ≥ 4·keyDeg·(N−1−H) + 4·keyDeg·H + 2·H`) also has zero
     counterexamples, so either repair is available; the blueprint must pick and re-derive
     `(C2Q.1)` from `(CS-1Q.a)`+`(CS-1Q.b)` as its own SIGNATURE NOTE demands.
  4. *Secondary, and now moot:* the docstring's claim that the inequality is *"stated over `ℤ` so
     no `ℕ`-truncation can hide a sign"* is false of the signed type — every term is `ℕ`. But the
     truncation is NOT the cause of the falsity: the sweep with the slack moved to the left (no
     truncation anywhere) fails at exactly the same 29 418 points.
* **D5 — H.94 `A1Cell.prod` and `A1Cell.deltaSubst` are `def`s with NO body in the SIGNATURE
  block** (the same class as chapter G's D2, `CubicFamilyIndex.schema`). The PROOF field describes
  `prod` completely (`Fin.append` on the four vectors, `+` on the constants, `*` on the
  coefficient, `⟨C.σ.data + D.σ.data⟩` on σ) and that body is landed below. For `deltaSubst` the
  PROOF field pins only the exponent data ("the new exponent's coefficients are
  `(expCoeff 0 + expCoeff 1, expCoeff 1)`") and leaves `offset`, `stride`, `visCoeff`, `visConst`
  and `coeff` UNSPECIFIED; the body below transports the visibility form by the same substitution
  (`visCoeff := ![v 0 + v 1, v 1]`, `visConst := visConst + visCoeff 1`) and keeps `offset`,
  `stride`, `coeff`, `σ`. That choice is a STUB-SIDE DETERMINATION, not a blueprint reading: it is
  the unique choice under which `deltaSubst_exp` (signed) holds and the visibility form transports
  by the same affine map, but the blueprint must confirm it.
* **D6 — H.71 `RecursionLegs` HAS A SYNTAX-LEVEL FIELD DEFECT (elaboration failure; CURED
  stub-side, minimally).** The blueprint declares `head alpha beta : ℕ → ℕ → ℝ` and
  `B' c' n₀ : ℕ`, i.e. three (resp. three) fields on one line. **Lean 4 structure fields do not
  admit multiple names**: `f a b : T` declares ONE field `f` of type `(a : _) → (b : _) → T`
  (with `a`, `b` auto-bound), so the structure as written has `alpha`, `beta`, `c'` and `n₀`
  MISSING, and `hsplit`/`halpha`/`hbeta`/`hdesc`/`rate_close` all fail with "unknown identifier"
  or an `HPow ℝ ((c' : ?) → ? → ℕ)` instance failure. Cured by splitting to one name per field
  (seven fields where the blueprint wrote two lines); the intent is unambiguous from the
  hypothesis fields that consume them. **This was the only elaboration failure in the chapter
  outside H.23** — the chapter's 190 signatures are otherwise type-correct as committed.
* **D7 — H.71 `RecursionLegs.hdesc` IS UNSATISFIABLE AT `N = 0`, which all but empties H.71
  (statement-level; NOT repaired here).** Two problems in one field,
  `hdesc : ∀ D N k, k < n₀ → 1 ≤ m * (k + 1) → N - m * (k + 1) < N`.
  (a) `D` occurs nowhere else in the field, so Lean cannot infer its type and the line does not
  elaborate ("failed to infer type of binder `D`"); annotated `(D N k : ℕ)` below, which is
  minimal and semantics-preserving. (b) **The field has no `1 ≤ N` guard, unlike its three sibling
  fields `hsplit`/`hhead`/`halpha`/`hbeta`, which all carry one.** At `N = 0`, `k = 0` the
  antecedents are satisfiable whenever `1 ≤ m` and `1 ≤ n₀`, and the conclusion is `0 - m·1 < 0`,
  i.e. `0 < 0` — FALSE. So `RecursionLegs Q m c u` is UNINHABITED whenever `1 ≤ m ∧ 1 ≤ n₀`; and
  `rate_close` hypothesizes `1 ≤ m`, so it survives only in the corner `n₀ = 0`, where `halpha`'s
  sum is empty and hence forces `alpha D N ≤ 0` — the α-leg, which is the whole point of
  `GENIND.C′`, is switched off. **Recommended repair (blueprint-side): add `1 ≤ N →` to `hdesc`**
  (with `1 ≤ N` the statement is true and the field is a genuine descent witness). Not applied
  stub-side: weakening a hypothesis field is a statement change.
* **D8 — H.89 `band_not_consulted` IS FALSE AS SIGNED (REFUTED; withdrawn, not signed).**
  `theorem band_not_consulted {m N h : ℕ} (hband : 2 * N ≤ m) : ¬ (m ≤ 2 * N - 1)` fails at
  `(N, m) = (0, 0)`: the antecedent `2 * 0 ≤ 0` holds and `2 * 0 - 1 = 0` in ℕ, so the conclusion
  is `¬ (0 ≤ 0)`. Found by the ARITHMETIC GATE at the bottom of this file (brute force over
  `m < 16`, `N < 9`; `(0,0)` is the only counterexample in that box, and the statement is true
  everywhere else on a 40 × 20 grid once either `1 ≤ N` or `1 ≤ m` is added — both repairs are
  checked at the gate). Commented out at H.89 per the `G.23a` precedent rather than signed as a
  false axiom. Signed count is therefore **189**, not 190. Note that the three sibling lemmas of
  H.89 (`consulted_ram`, `consulted_twoSided`, `consulted_refine`) all DO carry the guard that this
  one drops — `consulted_ram` even takes `1 ≤ N` explicitly — so the omission looks like a
  transcription slip, not a considered scope.
* **F2 — `StageInterface` HAS NO EXHIBITED INSTANCE ANYWHERE IN THE CHAPTER** (vacuity-witness gap;
  finding, not a typing failure). §3's design note asserts *"Two instances are exhibited (H.38's
  genre E and H.42's genre F) with `stageLoss = 0`"*, but `grep StageInterface` over the blueprint
  finds the identifier in exactly two SIGNATURE blocks — its own (H.09) and its consumer's (H.72) —
  and H.38/H.42 sign only `lawE`/`lawF` and exponent lemmas. So nothing in chapter H witnesses that
  `StageInterface G N H S` is inhabited, and H.72 (`rate_lossPriced`) is a theorem about a
  possibly-empty type. Contrast `GenreDatum`, which the chapter instantiates three times
  (`genreE2`, `genreA2witness`, `genreD2bwitness`) — exactly the chapter-G `CertFamily` discipline
  ("all the work sits in the instances"). Either the two claimed instances need signatures, or the
  design note's claim needs withdrawing. **Partly closed here:** this file constructed
  `stageIfaceE : StageInterface (genreE2 0) 2 0 4` (gate section) — so the structure is inhabited
  and its eleven fields are jointly satisfiable, which is also what makes D4's refutation bite. The
  chapter still signs no instance of its own, and the genre-F instance §3 claims is still absent.
  [**FULLY CLOSED 2026-08-15**, after this record was written: both witnesses are landed in
  `leanfinal/Uniformity/ChapH/H09w.lean` and this file's `stageIfaceE` is retired against the landed
  one — see finding R3 in the retirement census above. This bullet reads in the past tense.]
* **(NOT a defect — recorded so the count reconciles.)** Two of the 190 signed types are NOT in
  their node's SIGNATURE block but in that node's ⚠ SIGNATURE NOTE, which is where the blueprint
  cures its own two declared defects: H.54's `stageLift'` (line 3413) and H.97's
  `package_three_of_rate` (line 5923). Both are signed below at the note's type, verbatim; the
  superseded `normIdx`/`stageLift` and `package_three_of_drainage` are not signed. A mechanical
  SIGNATURE-block-only extractor sees 192 − 2 = 190 written declarations and MISSES these two,
  which is worth knowing for any future automated 0e diff of this chapter.
* **O1 — ORDERING: §3 is not in DAG order.** H.09 `StageInterface`'s `hbracket` field mentions
  `clusterC`, which is H.13 (§4) — H.09's own DEPENDS field says so ("H.01, H.02, H.13
  (`clusterC`)"). §15's instruction to land the stubs "in the section ordering" is therefore
  unsatisfiable as written. `clusterC` (H.13) is HOISTED above H.09 below, and the fleet must
  order the `leanfinal` roll-up the same way (`ChapH/H13.lean` before `ChapH/H09.lean`).

## Numeric content EXECUTED at this gate (GC-11 / §15 recommended order (c))

Every closed-form numeric claim in the chapter is re-executed at the bottom of this file with
`#guard` (which FAILS THE BUILD if the proposition evaluates to `false`), at `q = 2` **and**
`q = 3` wherever the claim has a `q`: H.21's bracket audit, H.29's twelve `uTwo` values, H.41's
quartic-law audit, H.40's below-floor `ℤ` value, H.42's headroom instance, H.45's censuses, H.62's
two fibre cardinalities, H.75's σ instances, H.88's `capBranch` trichotomy instance, H.84's node
shapes, plus H.99's own `#eval` column against the blueprint's expected values. Anything a
`#guard` cannot evaluate (a `Classical.dec`-backed instance) is recorded at the block.
-/

namespace LeanspecH

-- 0e RETIREMENT (2026-08-15): every local stub body is gone, so `Induction` must be opened for
-- the flat names below to resolve to the LANDED declarations (that resolution IS the diff).
open Uniformity Uniformity.Density Uniformity.Density.Induction

-- `autoImplicit` is ON by default at this pin (the leanspec lakefile sets no `leanOptions`), and it
-- is what turned CHAP-H's D6 field defect into a confusing `HPow` error instead of a name error.
-- Turned OFF here so that ANY unbound identifier in a signed signature is a hard error: that is
-- precisely the gate's job. Verified: all 190 signatures elaborate with it off.
set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Every `axiom` binder is "unused" by construction; the linter would emit ~400 useless warnings.
set_option linter.unusedVariables false

/-! ## §3 — THE GENRE SCHEMA AND THE STAGE INTERFACE (H.01–H.12) -/

/-! ### NODE H.01 [def] — `GenreDatum` (real body; lands in `Uniformity.Density.Induction`) -/

/-- A **genre datum** `G = (Q; e₁, f₁, μ; h)`: the local invariants of a composite-stage opening
(`GENHN.CLASS`(i)). The residual factor `ψ` has degree `f₁` and multiplicity `μ`; the side carrying
it has slope `h / e₁` in lowest terms. -/
-- 0e RETIREMENT (structure). Two checks, per the `Leanspec.lean` lifecycle rule: (i) the
-- anonymous-constructor `example` pins the FIELD ORDER and every field's type; (ii) the `have`
-- block pins every field NAME together with its projected type.
example (Q e₁ f₁ μ h : ℕ) (hQ : 2 ≤ Q) (he₁ : 1 ≤ e₁) (hh : 1 ≤ h) (hkey : 2 ≤ e₁ * f₁)
    (hmul : 2 ≤ μ) (hcop : Nat.Coprime h e₁) : GenreDatum :=
  ⟨Q, e₁, f₁, μ, h, hQ, he₁, hh, hkey, hmul, hcop⟩

example (G : GenreDatum) : True := by
  have _ : ℕ := G.Q
  have _ : ℕ := G.e₁
  have _ : ℕ := G.f₁
  have _ : ℕ := G.μ
  have _ : ℕ := G.h
  have _ : 2 ≤ G.Q := G.hQ
  have _ : 1 ≤ G.e₁ := G.he₁
  have _ : 1 ≤ G.h := G.hh
  have _ : 2 ≤ G.e₁ * G.f₁ := G.hkey
  have _ : 2 ≤ G.μ := G.hmul
  have _ : Nat.Coprime G.h G.e₁ := G.hcop
  trivial

/-! ### NODE H.02 [def] — the derived stage data (real bodies) -/

/-- `D′ = e₁ f₁`, the entry key's degree. -/
example (G : GenreDatum) : ℕ := GenreDatum.keyDeg (G := G)
example (G : GenreDatum) : G.keyDeg = G.e₁ * G.f₁ := rfl

/-- `|K| = Q ^ f₁`, the stage residue cardinality. -/
example (G : GenreDatum) : ℕ := GenreDatum.stageCard (G := G)
example (G : GenreDatum) : G.stageCard = G.Q ^ G.f₁ := rfl

/-- `L = e₁ μ f₁`, the abscissa length the composite block occupies. -/
example (G : GenreDatum) : ℕ := GenreDatum.sideLen (G := G)
example (G : GenreDatum) : G.sideLen = G.e₁ * G.μ * G.f₁ := rfl

/-- The stage-initial node floor at coordinate `j`, in `dv`-units:
`dv(A_j) ≥ (μ − j) · D′ h + 1`.  This is the `[r1]`-CORRECTED floor of `GENHN.A`(i); the sealed
`(μ − j) · e₁ h + 1` is the `f₁ = 1` specialization (H.08). -/
example (G : GenreDatum) (j : ℕ) : ℕ := GenreDatum.nodeHeight (G := G) (j := j)
example (G : GenreDatum) (j : ℕ) : G.nodeHeight j = (G.μ - j) * G.keyDeg * G.h + 1 := rfl

/-! ### NODE H.03 [lemma] -/

example (G : GenreDatum) : 4 ≤ G.sideLen :=
  GenreDatum.four_le_sideLen (G := G)

/-! ### NODE H.04 [lemma] -/

example {e f : ℕ} (h : e * f = 2) : (e = 2 ∧ f = 1) ∨ (e = 1 ∧ f = 2) :=
  keyDeg_two_cases (e := e) (f := f) (h := h)

example {e f m : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ e * f) (h : e * m * f = 4) :
    (e = 2 ∧ f = 1 ∧ m = 2) ∨ (e = 1 ∧ f = 2 ∧ m = 2) :=
  sideLen_four_cases (e := e) (f := f) (m := m) (hm := hm) (hk := hk) (h := h)

example {G : GenreDatum} {m D n : ℕ} (hD : 1 ≤ D)
    (hLm : G.sideLen ≤ m) (hmn : m * D ≤ n) : 4 ≤ m ∧ 4 ≤ n :=
  four_le_of_sideLen_le (G := G) (m := m) (D := D) (n := n) (hD := hD) (hLm := hLm) (hmn := hmn)

/-! ### NODE H.05 [theorem] — the schema set is finite -/

/-- The schema set at degree `n`: the triples `(e₁, f₁, μ)` a degree-`n` read can realize. -/
example (n : ℕ) : Set (ℕ × ℕ × ℕ) := schemaSet (n := n)
example (n : ℕ) :
    schemaSet n = {p | 2 ≤ p.1 * p.2.1 ∧ 2 ≤ p.2.2 ∧ p.1 * p.2.2 * p.2.1 ≤ n} := rfl

example (n : ℕ) : (schemaSet n).Finite :=
  finite_schemaSet (n := n)

example (n : ℕ) : Nat.card (schemaSet n) ≤ n ^ 3 :=
  card_schemaSet_le (n := n)

/-! ### NODE H.06 [theorem] — the DATUM set is infinite (the A2 refutation)

`hcop`'s cited lemma name is DEFECT D3: `Nat.coprime_two_right_iff_odd` does not exist at the pin;
`Nat.coprime_two_right` does. -/

/-- The genre-E datum at `Q = 2` with slope numerator `2t+1`. -/
example (t : ℕ) : GenreDatum := genreE2 (t := t)
-- The DATA fields, `rfl`-diffed (the six proof fields are proof-irrelevant, so nothing to diff;
-- D3's cured `hcop` cite is not observable from outside — it is checked by `leanfinal` building).
example (t : ℕ) :
    ((genreE2 t).Q, (genreE2 t).e₁, (genreE2 t).f₁, (genreE2 t).μ, (genreE2 t).h)
      = (2, 2, 1, 2, 2 * t + 1) := rfl

example : Function.Injective genreE2 :=
  genreE2_injective

example :
    {G : GenreDatum | G.Q = 2 ∧ G.e₁ = 2 ∧ G.f₁ = 1 ∧ G.μ = 2}.Infinite :=
  infinite_genreDatum_of_schema

/-! ### NODE H.07 [def] — the occupied-height predicate (real body) -/

/-- `G.Occupied m`: the `dv`-height `m` admits an INTEGRAL normalizer monomial
`n(m) = x^{i} π^{a}` with `0 ≤ i < e₁` and `a ≥ 0`.  This is the TERMINAL scope word of
`GENHN.A`(ii) after the post-D2b corrigendum. -/
example (G : GenreDatum) (m : ℕ) : Prop := GenreDatum.Occupied (G := G) (m := m)
example (G : GenreDatum) (m : ℕ) :
    G.Occupied m ↔ ∃ i a : ℕ, i < G.e₁ ∧ i * G.h + G.e₁ * a = m := Iff.rfl

/-! ### NODE H.08 [lemma] -/

example (G : GenreDatum) {j : ℕ} (hj : j < G.μ) :
    G.keyDeg * G.h < G.nodeHeight j :=
  GenreDatum.keyDeg_mul_h_lt_nodeHeight (G := G) (j := j) (hj := hj)

example (G : GenreDatum) (hf : G.f₁ = 1) (j : ℕ) :
    G.nodeHeight j = (G.μ - j) * G.e₁ * G.h + 1 :=
  GenreDatum.nodeHeight_of_f_one (G := G) (hf := hf) (j := j)

/-! ### NODE H.13 [def] — `clusterC`, **HOISTED** out of §4

FINDING O1: H.09's `hbracket` field mentions `clusterC`, so the blueprint's own §3-before-§4
section order cannot be the landing order. H.09's DEPENDS field already lists H.13. -/

/-- `c(m) = m(m−1)/2`, the α-bracket's exponent coefficient offset (`GENIND` §S1). Defined as
`m.choose 2` so that `2 * clusterC m = m * (m − 1)` is exact in `ℕ` with no floor. -/
example (m : ℕ) : ℕ := clusterC (m := m)
example (m : ℕ) : clusterC m = m.choose 2 := rfl

/-! ### NODE H.09 [def] — `StageInterface` (real body; §15's fragile signature #1) -/

/-- **The stage interface.** Every field is a clause of `[GENIND-H]` in its TERMINAL wording:
`(CS-1Q.a)`/`(CS-1Q.b)` (ledger `HYP.36`, disposition CARRY), `(CS-2)` (the stage bracket, in the
MASS normalization), `(CS-EXACT)`, and the degree-consistency half of `(CS-3)`.  **Nothing in this
structure is proved by chapter H**; the chapter proves the count and rate theorems of §10 FROM these
fields. -/
-- 0e RETIREMENT (structure): constructor order + every field type, then every field name.
example (G : GenreDatum) (N H S : ℕ) (stageWindow stageLoss entryCodim slack : ℕ)
    (bracket : ℕ → ℕ) (drainFrac : ℕ → ℝ) (stageSigma : FactorizationType)
    (hS : G.sideLen ≤ S)
    (hwin : G.e₁ * (N - 1 - H) ≤ stageWindow + stageLoss)
    (hprice : 2 * (G.f₁ * stageLoss) ≤ 2 * entryCodim + (S - 2 * G.keyDeg) * H + 2 * slack)
    (hbracket : ∀ κ, 1 ≤ κ →
      bracket κ * G.stageCard = (G.stageCard - 1) * G.stageCard ^ ((clusterC G.μ + 1) * κ))
    (hdrain_nonneg : ∀ M, 0 ≤ drainFrac M) (hdrain_le_one : ∀ M, drainFrac M ≤ 1)
    (hsigma : G.μ = 2 → stageSigma.degree = 2 * G.keyDeg) :
    StageInterface G N H S :=
  ⟨stageWindow, stageLoss, entryCodim, slack, bracket, drainFrac, stageSigma, hS, hwin, hprice,
    hbracket, hdrain_nonneg, hdrain_le_one, hsigma⟩

example {G : GenreDatum} {N H S : ℕ} (I : StageInterface G N H S) : True := by
  have _ : ℕ := I.stageWindow
  have _ : ℕ := I.stageLoss
  have _ : ℕ := I.entryCodim
  have _ : ℕ := I.slack
  have _ : ℕ → ℕ := I.bracket
  have _ : ℕ → ℝ := I.drainFrac
  have _ : FactorizationType := I.stageSigma
  have _ : G.sideLen ≤ S := I.hS
  have _ : G.e₁ * (N - 1 - H) ≤ I.stageWindow + I.stageLoss := I.hwin
  have _ : 2 * (G.f₁ * I.stageLoss)
      ≤ 2 * I.entryCodim + (S - 2 * G.keyDeg) * H + 2 * I.slack := I.hprice
  have _ : ∀ κ, 1 ≤ κ →
      I.bracket κ * G.stageCard
        = (G.stageCard - 1) * G.stageCard ^ ((clusterC G.μ + 1) * κ) := I.hbracket
  have _ : ∀ M, 0 ≤ I.drainFrac M := I.hdrain_nonneg
  have _ : ∀ M, I.drainFrac M ≤ 1 := I.hdrain_le_one
  have _ : G.μ = 2 → I.stageSigma.degree = 2 * G.keyDeg := I.hsigma
  trivial

/-! ### NODE H.10 [lemma] -/

example (G : GenreDatum) {m : ℕ}
    (hm : G.keyDeg * G.h < m) : G.Occupied m :=
  GenreDatum.occupied_of_keyDeg_mul_h_lt (G := G) (m := m) (hm := hm)

example (G : GenreDatum) {j : ℕ} (hj : j < G.μ) :
    G.Occupied (G.nodeHeight j) :=
  GenreDatum.occupied_nodeHeight (G := G) (j := j) (hj := hj)

/-! ### NODE H.11 [lemma] — the A2/R4 unoccupied-height witness -/

/-- The A2/R4 witness datum `(Q; e₁, f₁, μ; h) = (2; 3, 1, 2; 2)`. -/
example : GenreDatum := genreA2witness
example : (genreA2witness.Q, genreA2witness.e₁, genreA2witness.f₁, genreA2witness.μ,
    genreA2witness.h) = (2, 3, 1, 2, 2) := rfl

example : ¬ genreA2witness.Occupied 1 :=
  not_occupied_genreA2witness

/-! ### NODE H.12 [lemma] — the post-D2b witness -/

/-- The post-D2b witness datum `(Q; e₁, f₁, μ; h) = (2; 1, 2, 2; 1)`. -/
example : GenreDatum := genreD2bwitness
example : (genreD2bwitness.Q, genreD2bwitness.e₁, genreD2bwitness.f₁, genreD2bwitness.μ,
    genreD2bwitness.h) = (2, 1, 2, 2, 1) := rfl

example : genreD2bwitness.Occupied 0 :=
  occupied_zero_genreD2bwitness

example :
    ¬ (genreD2bwitness.keyDeg * genreD2bwitness.h < 0) :=
  not_keyDeg_mul_h_lt_zero_genreD2bwitness

/-! ## §4 — ARITHMETIC I: THE α SPECIES (H.13–H.22)

`clusterC` (H.13) is hoisted above H.09 — see FINDING O1. -/

/-! ### NODE H.14 [lemma] -/

example (m : ℕ) : 2 * clusterC m = m * (m - 1) :=
  two_mul_clusterC (m := m)

example (m : ℕ) : clusterC m = ∑ j ∈ Finset.range m, j :=
  clusterC_eq_sum (m := m)

example :
    clusterC 2 + 1 = 2 ∧ clusterC 3 + 1 = 4 ∧ clusterC 4 + 1 = 7 ∧ clusterC 5 + 1 = 11 :=
  clusterC_succ_values

/-! ### NODE H.15 [def] -/

/-- The α(k)-locus's free-digit exponent, written in the TRANSPORTED coordinate `W = N − 1 − mk`:
`alphaExp m W k = m·W + k·c(m)` — the reduced-window exponent plus the ghost exponent.  H.16
identifies it with `GENIND`'s displayed `m(N−1) − k·m(m+1)/2`. -/
example (m W k : ℕ) : ℕ := alphaExp (m := m) (W := W) (k := k)
example (m W k : ℕ) : alphaExp m W k = m * W + k * clusterC m := rfl

/-! ### NODE H.16 [lemma] -/

example (m W k : ℕ) :
    ∑ j ∈ Finset.range m, (W + j * k) = alphaExp m W k :=
  sum_alphaSlots (m := m) (W := W) (k := k)

example (m W k : ℕ) :
    2 * alphaExp m W k + k * (m * (m + 1)) = 2 * (m * (W + m * k)) :=
  two_mul_alphaExp_add (m := m) (W := W) (k := k)

/-! ### NODE H.17 [lemma] -/

example (m k : ℕ) : ∑ j ∈ Finset.range m, j * k = k * clusterC m :=
  ghostSlots_eq (m := m) (k := k)

example (m W k : ℕ) :
    k * clusterC m + m * W = alphaExp m W k :=
  ghost_add_child_eq_alphaExp (m := m) (W := W) (k := k)

/-! ### NODE H.18 [def] — `alphaBracket` (real body)

DEFECT D2: the blueprint body carries no `decreasing_by`; the goal `μ - k < μ + 1` is
unconditionally true, so the tactic below is the whole repair. -/

/-- The α-prefix aggregate `b_{m,d}(μ)`, defined by the composition recursion (peel the first
step).  `alphaBracket Q c μ = Σ over compositions (k₁,…,k_r) of μ with kᵢ ≥ 1 of
Π (Q−1)Q^{c kᵢ}`, and `alphaBracket Q c 0 = 1`. -/
example (Q c : ℕ) : ℕ → ℕ := alphaBracket (Q := Q) (c := c)
-- Well-founded recursion: `rfl` does not reduce it, so the BODY is diffed by its two equations
-- (`rw` through the landed equation lemmas) and, numerically, by the `#eval` gate at the bottom of
-- this file, which now runs on the LANDED body.
example (Q c : ℕ) : alphaBracket Q c 0 = 1 := by rw [alphaBracket]
example (Q c μ : ℕ) : alphaBracket Q c (μ + 1)
    = ∑ k ∈ Finset.range (μ + 1), (Q - 1) * Q ^ (c * (k + 1)) * alphaBracket Q c (μ - k) := by
  rw [alphaBracket]

/-! ### NODE H.19 [lemma] -/

example (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    alphaBracket Q c (μ + 1) = Q ^ (c + 1) * alphaBracket Q c μ :=
  alphaBracket_succ (Q := Q) (c := c) (hQ := hQ) (hc := hc) (μ := μ) (hμ := hμ)

/-! ### NODE H.20 [theorem] — the general bracket (SPLIT-MANDATED into 2) -/

example (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    Q * alphaBracket Q c μ = (Q - 1) * Q ^ ((c + 1) * μ) :=
  alphaBracket_closed (Q := Q) (c := c) (hQ := hQ) (hc := hc) (μ := μ) (hμ := hμ)

/-- The corpus's displayed form, for consumers that prefer it. -/
example (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    alphaBracket Q c μ = (Q - 1) * Q ^ ((c + 1) * μ - 1) :=
  alphaBracket_eq (Q := Q) (c := c) (hQ := hQ) (hc := hc) (μ := μ) (hμ := hμ)

/-! ### NODE H.21 [lemma] — the `(CS-2)` numeric certificate (EXECUTED at the gate below) -/

example :
    alphaBracket 4 1 2 = 192 ∧ alphaBracket 3 1 2 = 54 ∧ alphaBracket 2 1 3 = 32 :=
  alphaBracket_audit

example :
    (4 : ℕ) ^ 2 * ((4 - 1) * 4 ^ 1) = alphaBracket 4 1 2 :=
  massNorm_eq_ghost_mul_letters

/-! ### NODE H.22 [lemma] -/

example (d m N : ℕ) (hm : 1 ≤ m) :
    d * (m - 1) * (N - 1) + d * (N - 1) = d * m * (N - 1) :=
  drain_codim (d := d) (m := m) (N := N) (hm := hm)

example (d m : ℕ) (hm : 1 ≤ m) :
    d * m * (1 - 1) = 0 ∧ d * (m - 1) * (1 - 1) = 0 ∧ ¬ ∃ k, 1 ≤ k ∧ m * k ≤ 0 :=
  window_one_exponents (d := d) (m := m) (hm := hm)

/-! ## §5 — ARITHMETIC II: THE `m = 2` DRAINAGE SPECIES (H.23–H.29) -/

/-! ### NODE H.23 [def] — `uTwo` (real body)

**DEFECT D1 (elaboration failure, cured minimally).** The blueprint writes the guard as a
non-dependent `if 1 ≤ k ∧ 2 * k ≤ N + 1 then …`, under which the well-founded-recursion goal is
`N + 2 - 2 * k < N + 2` with `k` unconstrained — false at `k = 0`, so the definition does not
elaborate. Written below with the DEPENDENT `if h : …` (so `1 ≤ k` reaches the termination goal)
plus `decreasing_by omega`. `dite` and `ite` agree on a `Decidable` proposition, so the function's
values are unchanged; they are certified at the gate (`#guard`, twelve values). -/

/-- The conservative-undecided count of the `(2, d)` cluster system at window `N`, in `Q = q^d`
units, by `GENIND` §S5.2's first-step recursion specialized to `m = 2` (where the recursion has no
β-terms: `m = 2 < 4` excludes CS, and a repeated linear `e = 1` factor at `m = 2` spans the whole
polygon, i.e. is α). -/
example (Q : ℕ) : ℕ → ℕ := uTwo (Q := Q)
-- Well-founded recursion (D1's cured DEPENDENT guard): body diffed by its three equations plus the
-- `#eval` gate at the bottom, which now runs on the LANDED body (twelve values, q = 2 and q = 3).
example (Q : ℕ) : uTwo Q 0 = 1 := by rw [uTwo]
example (Q : ℕ) : uTwo Q 1 = 1 := by rw [uTwo]
example (Q N : ℕ) : uTwo Q (N + 2) = Q ^ (N + 1) +
    ∑ k ∈ Finset.range (N + 2),
      if h : 1 ≤ k ∧ 2 * k ≤ N + 1 then (Q - 1) * Q ^ k * uTwo Q (N + 2 - 2 * k) else 0 := by
  rw [uTwo]

/-! ### NODE H.24 [lemma] -/

example (Q : ℕ) : uTwo Q 1 = 1 :=
  uTwo_one (Q := Q)

example (Q : ℕ) : uTwo Q 2 = Q :=
  uTwo_two (Q := Q)

/-! ### NODE H.25 [theorem] -/

example (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 3 ≤ N) :
    uTwo Q N + Q ^ (N - 2) = Q ^ (N - 1) + Q ^ 2 * uTwo Q (N - 2) :=
  uTwo_rec (Q := Q) (hQ := hQ) (N := N) (hN := hN)

/-! ### NODE H.26 [theorem] — the `m = 2` closed form (SPLIT-MANDATED into 2) -/

example (Q : ℕ) (hQ : 2 ≤ Q) {M : ℕ} (hM : 2 ≤ M) :
    uTwo Q M = Q ^ (M - 1) + ((M - 1) / 2) * ((Q - 1) * Q ^ (M - 2)) :=
  uTwo_closed (Q := Q) (hQ := hQ) (M := M) (hM := hM)

example (Q : ℕ) (hQ : 2 ≤ Q) {l : ℕ} (hl : 1 ≤ l) :
    uTwo Q (2 * l) + (l - 1) * Q ^ (2 * l - 2) = l * Q ^ (2 * l - 1) :=
  uTwo_even (Q := Q) (hQ := hQ) (l := l) (hl := hl)

example (Q : ℕ) (hQ : 2 ≤ Q) (l : ℕ) :
    uTwo Q (2 * l + 1) + l * Q ^ (2 * l - 1) = (l + 1) * Q ^ (2 * l) :=
  uTwo_odd (Q := Q) (hQ := hQ) (l := l)

/-! ### NODE H.27 [lemma] -/

example (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 1 ≤ N) : uTwo Q N ≤ N * Q ^ (N - 1) :=
  uTwo_le (Q := Q) (hQ := hQ) (N := N) (hN := hN)

/-! ### NODE H.28 [theorem] — the `(A2-RATE)` ground instance -/

example (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 1 ≤ N) :
    (uTwo Q N : ℝ) / (Q : ℝ) ^ (2 * (N - 1)) ≤ (N : ℝ) / (Q : ℝ) ^ (N - 1) :=
  uTwo_ratio_le (Q := Q) (hQ := hQ) (N := N) (hN := hN)

/-! ### NODE H.29 [lemma] — the two-prime numeric audit (EXECUTED at the gate below) -/

example :
    uTwo 2 1 = 1 ∧ uTwo 2 2 = 2 ∧ uTwo 2 3 = 6 ∧ uTwo 2 4 = 12 ∧ uTwo 2 5 = 32 ∧ uTwo 2 6 = 64 :=
  uTwo_audit_two

example :
    uTwo 3 1 = 1 ∧ uTwo 3 2 = 3 ∧ uTwo 3 3 = 15 ∧ uTwo 3 4 = 45 ∧ uTwo 3 5 = 189 ∧ uTwo 3 6 = 567 :=
  uTwo_audit_three

/-! ## §6 — ARITHMETIC III: THE PRICING INEQUALITIES (H.30–H.37) -/

/-! ### NODE H.30 [lemma] -/

example (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ ≤ 1 :=
  alpha_geom_partial_le_one (Q := Q) (c := c) (hQ := hQ) (hc := hc) (n := n)

/-! ### NODE H.31 [lemma] (SPLIT CANDIDATE) -/

example (Q : ℕ) (hQ : 2 ≤ Q) (n : ℕ) :
    ∑ H ∈ Finset.range n, ((Q : ℝ) ^ (H : ℝ))⁻¹ ^ ((1:ℝ)/2)
      ≤ (1 - ((2:ℝ) ^ ((1:ℝ)/2))⁻¹)⁻¹ :=
  height_geom_partial_le (Q := Q) (hQ := hQ) (n := n)

/-! ### NODE H.32 [lemma] -/

example (S H : ℕ) :
    2 * (∑ r ∈ Finset.range S, (r + 1) * H) = S * (S + 1) * H :=
  two_mul_supportLine_sum (S := S) (H := H)

/-! ### NODE H.33 [lemma] -/

example {e f m : ℕ} (hm : 2 ≤ m) : 2 * (e * f) ≤ e * m * f :=
  two_mul_a_le_sideLen (e := e) (f := f) (m := m) (hm := hm)

example {e f m S : ℕ} (hm : 2 ≤ m) (hS : e * m * f ≤ S) :
    2 * (e * f) ≤ S :=
  two_mul_a_le_S (e := e) (f := f) (m := m) (S := S) (hm := hm) (hS := hS)

/-! ### NODE H.34 [lemma] -/

example {D M N c : ℕ} (hD : 1 ≤ D) (hc : c ≤ M) (h : D + M = N) :
    (D - 1) + (M - c) = N - 1 - c :=
  exp_compose (D := D) (M := M) (N := N) (c := c) (hD := hD) (hc := hc) (h := h)

example {Q : ℕ} (hQ : 2 ≤ Q) {D M N c : ℕ} (hD : 1 ≤ D) (hc : c ≤ M)
    (h : D + M = N) {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹) (hδ : δ ≤ ((Q : ℝ) ^ (M - c))⁻¹) :
    ρ * δ ≤ ((Q : ℝ) ^ (N - 1 - c))⁻¹ :=
  mul_le_of_exp_compose (Q := Q) (hQ := hQ) (D := D) (M := M) (N := N) (c := c) (hD := hD)
    (hc := hc) (h := h) (ρ := ρ) (δ := δ) (hρ0 := hρ0) (hδ0 := hδ0) (hρ := hρ) (hδ := hδ)

/-! ### NODE H.35 [lemma] -/

example {N m B : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (hB : 1 ≤ B) :
    (N - m) ^ B + m * (N - m) ^ (B - 1) ≤ N ^ B :=
  pow_sub_dominance (N := N) (m := m) (B := B) (hm := hm) (hmN := hmN) (hB := hB)

/-! ### NODE H.36 [lemma] -/

example (d D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N) :
    d * (D - 1) + d * (N - D) = d * (N - 1) :=
  entry_codim (d := d) (D := D) (N := N) (hD := hD) (hDN := hDN)

/-! ### NODE H.37 [lemma] -/

example (m N : ℕ) :
    Nat.card {s : Fin m → ℕ // ∀ i, 1 ≤ s i ∧ s i ≤ N - 1} ≤ N ^ m :=
  card_slopeTuples_le (m := m) (N := N)

/-! ## §7 — ARITHMETIC IV: THE GENRE LAWS, FLOORS, TOWER THRESHOLDS (H.38–H.50) -/

/-! ### NODE H.38 [def+lemma] -/

/-- `CS4-E(h)` — the quartic e-first genre's per-centre opening locus, `(q−1)q^{4N−5h−3}`
(`GENIND` §S5.3 = `W-12` §S2.5's `QRT-G2(h;(1²))`).  Total by construction; the visibility floor
`2h ≤ N−1` is a hypothesis of `lawE_floor_*`, not of the definition. -/
example (q N h : ℕ) : ℕ := lawE (q := q) (N := N) (h := h)
example (q N h : ℕ) : lawE q N h = (q - 1) * q ^ (4 * N - 5 * h - 3) := rfl

example {N h : ℕ} (hfl : 2 * h + 1 ≤ N) : 5 * h + 3 ≤ 4 * N :=
  lawE_exp_honest (N := N) (h := h) (hfl := hfl)

example {q : ℕ} (hq : 2 ≤ q) :
    ¬ (2 * 1 + 1 ≤ 2) ∧ lawE q 2 1 ≠ 0 :=
  lawE_floor_fails_at_two_one (q := q) (hq := hq)

/-! ### NODE H.39 [lemma] -/

example {N t : ℕ} (hN : 4 * t + 3 ≤ N) :
    (N - (t + 1)) + (N - 1 - (2 * t + 1)) + (N - (3 * t + 2)) + (N - 1 - (4 * t + 2))
      + (10 * t + 8) = 4 * N :=
  lawE_exp_four_summands (N := N) (t := t) (hN := hN)

example {N t : ℕ} (hN : 4 * t + 3 ≤ N) :
    4 * N - 5 * (2 * t + 1) - 3 = 4 * N - (10 * t + 8) :=
  lawE_exp_odd (N := N) (t := t) (hN := hN)

/-! ### NODE H.40 [def+lemma] -/

/-- `CS4-F(k)` — the quartic f-first genre's per-centre opening locus,
`(q(q−1)/2)·q^{4N−10k−4}` (`GENIND` §S5.3; `#ψ = q(q−1)/2` monic irreducible quadratics). -/
example (q N k : ℕ) : ℕ := lawF (q := q) (N := N) (k := k)
example (q N k : ℕ) : lawF q N k = (q * (q - 1) / 2) * q ^ (4 * N - 10 * k - 4) := rfl

example {N k : ℕ} (hfl : 4 * k + 1 ≤ N) : 10 * k + 4 ≤ 4 * N :=
  lawF_exp_honest (N := N) (k := k) (hfl := hfl)

example : (4 : ℤ) * 2 - 10 * 1 - 4 = -6 :=
  lawF_exp_neg_below_floor

/-! ### NODE H.41 [lemma] — the quartic-law audit (EXECUTED at the gate below) -/

example :
    lawE 2 6 1 = 65536 ∧ lawE 3 4 1 = 13122 ∧ lawE 5 3 1 = 2500 ∧
    lawF 2 6 1 = 1024 ∧ lawF 2 5 1 = 64 ∧ lawE 2 6 1 + lawF 2 6 1 = 66560 :=
  quartic_law_audit

/-! ### NODE H.42 [def+lemma] -/

/-- `CS5-V1E2(h)` — the quintic vertex-at-1 genre: `CS4-E`'s law times the split root's headroom
fibre `(q^{N−(5h+1)/2} − 1)` (`GENIND` §S5.3). -/
example (q N h : ℕ) : ℕ := lawV1E2 (q := q) (N := N) (h := h)
example (q N h : ℕ) : lawV1E2 q N h = lawE q N h * (q ^ (N - (5 * h + 1) / 2) - 1) := rfl

example (t : ℕ) : (5 * (2 * t + 1) + 1) / 2 = 5 * t + 3 :=
  headroom_exp_odd (t := t)

example {q N t : ℕ} (hq : 2 ≤ q) :
    lawV1E2 q N (2 * t + 1) = 0 ↔ (N ≤ 5 * t + 3 ∨ lawE q N (2 * t + 1) = 0) :=
  lawV1E2_eq_zero_iff (q := q) (N := N) (t := t) (hq := hq)

/-! ### NODE H.43 [lemma] -/

example {v₄ t : ℕ} (hv : 1 ≤ v₄) (h : 2 * v₄ < 2 * t + 1) :
    2 * v₄ + 1 ≤ 2 * t + 1 :=
  v4e2_vertex_condition (v₄ := v₄) (t := t) (hv := hv) (h := h)

example {v₄ t : ℕ} (hv : 1 ≤ v₄) (hvc : 2 * v₄ + 1 ≤ 2 * t + 1) :
    7 ≤ v₄ + 2 * (2 * t + 1) :=
  v4e2_first_visible (v₄ := v₄) (t := t) (hv := hv) (hvc := hvc)

example {v₄ t N : ℕ} (hv : 1 ≤ v₄) (hvc : 2 * v₄ + 1 ≤ 2 * t + 1)
    (hvis : v₄ + 2 * (2 * t + 1) ≤ N - 1) : 8 ≤ N :=
  v4e2_needs_eight (v₄ := v₄) (t := t) (N := N) (hv := hv) (hvc := hvc) (hvis := hvis)

/-! ### NODE H.44 [lemma] -/

/-- The pin census at a slot of `F_q`-dimension `c`: the nonzero readable vectors of an
`F_q`-subspace of dimension `c`. -/
example (q c : ℕ) : ℕ := pinCensus (q := q) (c := c)
example (q c : ℕ) : pinCensus q c = q ^ c - 1 := rfl

example (q : ℕ) : pinCensus q 1 = q - 1 :=
  pinCensus_genreE (q := q)

example (q : ℕ) : pinCensus q 2 = q ^ 2 - 1 :=
  pinCensus_genreF_interior (q := q)

example {q : ℕ} (hq : 2 ≤ q) :
    pinCensus q 1 ≠ pinCensus q 2 :=
  pinCensus_band_ne_interior (q := q) (hq := hq)

/-! ### NODE H.45 [lemma] -/

/-- `#{unordered pairs of distinct nonzero elements}` over a `Q`-element field — the `SPLITEQ`
residual census. -/
example (Q : ℕ) : ℕ := splitEqCensus (Q := Q)
example (Q : ℕ) : splitEqCensus Q = (Q - 1) * (Q - 2) / 2 := rfl

/-- `#{monic irreducible quadratics}` over a `Q`-element field — the `INERT` residual census. -/
example (Q : ℕ) : ℕ := inertCensus (Q := Q)
example (Q : ℕ) : inertCensus Q = Q * (Q - 1) / 2 := rfl

example (Q : ℕ) : 2 * splitEqCensus Q = (Q - 1) * (Q - 2) :=
  two_mul_splitEqCensus (Q := Q)

example (Q : ℕ) : 2 * inertCensus Q = Q * (Q - 1) :=
  two_mul_inertCensus (Q := Q)

/-! ### NODE H.46 [lemma] (SPLIT-MANDATED into 2) -/

/-- The odd (`α₁`-borne) `dv`-heights of the `A₁` string at genre E. -/
example (N h : ℕ) : Finset ℕ := slotOdd (N := N) (h := h)
example (N h : ℕ) :
    slotOdd N h = (Finset.Icc ((h + 1) / 2) (N - 1)).image (fun v => 2 * v + h) := rfl

/-- The even (`α₀`-borne) `dv`-heights of the `A₁` string at genre E. -/
example (N h : ℕ) : Finset ℕ := slotEven (N := N) (h := h)
example (N h : ℕ) :
    slotEven N h = (Finset.Icc (h + 1) (N - 1)).image (fun v => 2 * v) := rfl

example (N t : ℕ) (hN : 2 * t + 2 ≤ N) :
    ((slotOdd N (2 * t + 1)).filter (fun m => 2 * N ≤ m)).card = t :=
  raggedBand_card (N := N) (t := t) (hN := hN)

example (N : ℕ) (hN : 2 ≤ N) :
    ((slotOdd N 1).filter (fun m => 2 * N ≤ m)) = ∅ :=
  raggedBand_empty_of_h_one (N := N) (hN := hN)

/-! ### NODE H.47 [lemma] -/

example {N h : ℕ} (hfl : 2 * h + 1 ≤ N) :
    (N + h - 1) + (N - 1 - 2 * h) = 2 * N - h - 2 :=
  genh4B_aggregate_exp (N := N) (h := h) (hfl := hfl)

example {N t : ℕ} (hN : 1 ≤ N) :
    N + ((2 * t + 1) - 1) / 2 = N + (2 * t + 1) - 1 ↔ t = 0 :=
  und_exp_coincide_iff_h_one (N := N) (t := t) (hN := hN)

/-! ### NODE H.48 [lemma] -/

example {l k : ℕ} (hk : 1 ≤ k) :
    2 * ((2 * l + 1) / 2) + 2 * k - 1 = (2 * l + 1) + 2 * k - 2 :=
  genh4B_F_odd_exp (l := l) (k := k) (hk := hk)

example (q N k : ℕ) (hq : 1 ≤ q) :
    q ^ (N + 2 * k - 1) + (q - 1) * q ^ (N + 2 * k - 1) = q ^ (N + 2 * k) ∨ N + 2 * k = 0 :=
  genh4B_F_even_sum (q := q) (N := N) (k := k) (hq := hq)

/-! ### NODE H.49 [lemma] -/

example {k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h)
    (hlt : 2 * k + 2 * h < 6) : k = 1 ∧ h = 1 :=
  mixed_six_childE_lt_six (k := k) (h := h) (hk := hk) (hh := hh) (hlt := hlt)

example {k h : ℕ} (hk : 1 ≤ k) (hst : 2 * k + 1 ≤ h) :
    8 ≤ 2 * k + 2 * h :=
  mixed_six_stage_steeper (k := k) (h := h) (hk := hk) (hst := hst)

example {k : ℕ} (hk : 1 ≤ k) : 6 ≤ 6 * k :=
  mixed_six_sameSide (k := k) (hk := hk)

example {k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h) (hne : h ≠ k) :
    8 ≤ 2 * k + 4 * h :=
  mixed_six_distinctSide (k := k) (h := h) (hk := hk) (hh := hh) (hne := hne)

/-! ### NODE H.50 [lemma] -/

example {e f μ n : ℕ} (hef : 2 ≤ e * f) (hμ : 4 ≤ μ) (hn : e * f * μ ≤ n) :
    8 ≤ n :=
  tower_needs_eight (e := e) (f := f) (μ := μ) (n := n) (hef := hef) (hμ := hμ) (hn := hn)

example {D μ₁ e₂ f₂ μ₂ n : ℕ} (hD : 2 ≤ D) (h2 : 2 ≤ e₂ * f₂)
    (hμ₂ : 4 ≤ μ₂) (h1 : e₂ * f₂ * μ₂ ≤ μ₁) (hn : D * μ₁ ≤ n) : 16 ≤ n :=
  depth_three_needs_sixteen (D := D) (μ₁ := μ₁) (e₂ := e₂) (f₂ := f₂) (μ₂ := μ₂) (n := n) (hD := hD)
    (h2 := h2) (hμ₂ := hμ₂) (h1 := h1) (hn := hn)

/-! ## §8 — THE SLOT / LIFT LAYER (H.51–H.58) — **the `H → B` split point**

GC-5: chapters B and E may consume H.51–H.58 by name and nothing else of chapter H. -/

/-! ### NODE H.51 [lemma] -/

example {h e : ℕ} (hcop : Nat.Coprime h e) {i i' : ℕ} (hi : i < e) (hi' : i' < e)
    (hmod : i * h % e = i' * h % e) : i = i' :=
  class_sep (h := h) (e := e) (hcop := hcop) (i := i) (i' := i') (hi := hi) (hi' := hi')
    (hmod := hmod)

example {h e : ℕ} (hcop : Nat.Coprime h e) :
    Set.BijOn (fun i => i * h % e) (Finset.range e) (Finset.range e) :=
  class_sep_bij (h := h) (e := e) (hcop := hcop)

/-! ### NODE H.52 [lemma] -/

example {h e : ℕ} (hcop : Nat.Coprime h e) {i i' v v' : ℕ}
    (hi : i < e) (hi' : i' < e) (heq : e * v + i * h = e * v' + i' * h) :
    i = i' ∧ v = v' :=
  slot_height_injective (h := h) (e := e) (hcop := hcop) (i := i) (i' := i') (v := v) (v' := v')
    (hi := hi) (hi' := hi') (heq := heq)

example {h e : ℕ} (hcop : Nat.Coprime h e) (he : 0 < e)
    (v : ℕ → ℕ) {i i' : ℕ} (hi : i < e) (hi' : i' < e)
    (hmin : e * v i + i * h = e * v i' + i' * h) : i = i' :=
  slot_min_unique (h := h) (e := e) (hcop := hcop) (he := he) (v := v) (i := i) (i' := i')
    (hi := hi) (hi' := hi') (hmin := hmin)

/-! ### NODE H.53 [lemma] — §15's fragile signature #2 (the `finrank`/`minpoly` shape) -/

example {F K : Type*} [Field F] [Field K] [Algebra F K] {η : K}
    (hgen : (minpoly F η).natDegree = Module.finrank F K) (hint : IsIntegral F η)
    {f : ℕ} (hf : f = Module.finrank F K) (l : Fin f → F)
    (hsum : ∑ t : Fin f, algebraMap F K (l t) * η ^ (t : ℕ) = 0) :
    ∀ t, l t = 0 :=
  eta_independent (F := F) (K := K) (η := η) (hgen := hgen) (hint := hint) (f := f) (hf := hf)
    (l := l) (hsum := hsum)

/-! ### NODE H.54 [def] — §15's fragile signature #3; `normIdx` **WITHDRAWN** (§15 rule 2)

The blueprint's SIGNATURE block form is recorded here for provenance ONLY and is NOT signed:
```
noncomputable def GenreDatum.normIdx (G : GenreDatum) (M : ℕ) : ℕ × ℕ :=
  if hM : G.keyDeg * G.h < M then (G.occupied_of_keyDeg_mul_h_lt hM).choose ... else (0, M)
noncomputable def stageLift ... (uses G.normIdx M)
```
— note that the recorded form is not even syntactically complete (`.choose ...`, an ellipsis), which
is why §15 rule 2 withdraws it. The SIGNED form is `stageLift'` (H.54's ⚠ SIGNATURE NOTE, blueprint
line 3413), which takes `i` and `a` as arguments; H.55/H.56 carry the defining equation as a
hypothesis, exactly as the note prescribes. -/

/-- `L_M(λ)` — the exact-height `K`-lift of `LEMMA GENHN-LIFT`, as a coefficient vector over the
ambient ring: `L_M(λ) = Σ_{s<f₁} λ̃_s · x^{i+e₁ s} π^{a−s h}`.  **The signed form** (H.54's
SIGNATURE NOTE): `i`, `a` explicit, no `Exists.choose`. -/
noncomputable example {O : Type*} [CommRing O] (G : GenreDatum) (π : O)
    (i a : ℕ) (lift : ℕ → O) : Polynomial O :=
  stageLift' (O := O) (G := G) (π := π) (i := i) (a := a) (lift := lift)

example {O : Type*} [CommRing O] (G : GenreDatum) (π : O) (i a : ℕ) (lift : ℕ → O) :
    stageLift' G π i a lift
      = ∑ s ∈ Finset.range G.f₁,
          Polynomial.C (lift s * π ^ (a - s * G.h)) * Polynomial.X ^ (i + G.e₁ * s) := rfl

/-! ### NODE H.55 [lemma] -/

example (G : GenreDatum) {i s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁) :
    i + G.e₁ * s < G.keyDeg :=
  stageLift_index_lt (G := G) (i := i) (s := s) (hi := hi) (hs := hs)

example (G : GenreDatum) {i a M s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁)
    (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M) : s * G.h ≤ a :=
  stageLift_integral (G := G) (i := i) (a := a) (M := M) (s := s) (hi := hi) (hs := hs) (hM := hM)
    (hbig := hbig)

example (G : GenreDatum) {i a M s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁)
    (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M) :
    G.e₁ * (a - s * G.h) + (i + G.e₁ * s) * G.h = M :=
  stageLift_height (G := G) (i := i) (a := a) (M := M) (s := s) (hi := hi) (hs := hs) (hM := hM)
    (hbig := hbig)

/-! ### NODE H.56 [lemma] -/

/-- The quotient identity: the `s`-th summand of `L_M(λ)` equals the normalizer `x^i π^a` times
`(x^{e₁} π^{−h})^s`, in the cleared form `π^{s h} · (summand) = n(M) · (x^{e₁})^s · lift s`. -/
example {O : Type*} [CommRing O] (G : GenreDatum) (π : O)
    {i a s : ℕ} (hsa : s * G.h ≤ a) (c : O) :
    (Polynomial.C (π ^ (s * G.h)) : Polynomial O) *
        (Polynomial.C (c * π ^ (a - s * G.h)) * Polynomial.X ^ (i + G.e₁ * s))
      = (Polynomial.C (π ^ a) * Polynomial.X ^ i) *
        (Polynomial.C c * Polynomial.X ^ (G.e₁ * s)) :=
  stageLift_summand_eq (O := O) (G := G) (π := π) (i := i) (a := a) (s := s) (hsa := hsa) (c := c)

/-! ### NODE H.57 [lemma] -/

example (r i e : ℕ) (he : 0 < e) :
    r * i = r * i % e + e * (r * i / e) ∧ r * i % e < e :=
  wrap_div_mod (r := r) (i := i) (e := e) (he := he)

/-- The height bookkeeping behind the wrap: if `i·h + e·a = M` then
`r·M = (r·i % e)·h + e·(r·a + W·h)` with `W = r·i / e`. -/
example {i a M h e r : ℕ} (he : 0 < e) (hM : i * h + e * a = M) :
    r * M = (r * i % e) * h + e * (r * a + (r * i / e) * h) :=
  wrap_height (i := i) (a := a) (M := M) (h := h) (e := e) (r := r) (he := he) (hM := hM)

/-! ### NODE H.58 [lemma] -/

example (D r : ℕ) (hD : 0 < D) :
    Set.BijOn (fun p : ℕ × ℕ => p.1 + p.2 * D)
      (Finset.range D ×ˢ Finset.range r) (Finset.range (D * r)) :=
  divMod_bij (D := D) (r := r) (hD := hD)

example (D r : ℕ) (hD : 0 < D) :
    (Finset.range D ×ˢ Finset.range r).card = D * r :=
  card_composedBasis (D := D) (r := r) (hD := hD)

/-! ## §9 — THE UNIT-PIVOT LAYER (H.59–H.62) -/

/-! ### NODE H.59 [def] — `TriangularUnitPivot` (real body) -/

/-- **Triangular with unit pivots.**  `Φ` solves each output slot as `unit × (its input slot) +
(a function of strictly earlier input slots)`.  This is the condition ANNEX R R2 identifies as the
missing displayed step of `GENIND-6(c)`: triangularity ALONE does not give surjectivity or constant
fibres over a truncated DVR (H.62). -/
-- 0e RETIREMENT (structure): constructor order + field types, then every field name.
example {R : Type*} [CommRing R] {n : ℕ} (Φ : (Fin n → R) → (Fin n → R))
    (pivot : Fin n → R) (tail : (i : Fin n) → (Fin n → R) → R)
    (pivot_isUnit : ∀ i, IsUnit (pivot i))
    (tail_lower : ∀ i v w, (∀ j : Fin n, j < i → v j = w j) → tail i v = tail i w)
    (apply_eq : ∀ v i, Φ v i = pivot i * v i + tail i v) : TriangularUnitPivot Φ :=
  ⟨pivot, tail, pivot_isUnit, tail_lower, apply_eq⟩

example {R : Type*} [CommRing R] {n : ℕ} {Φ : (Fin n → R) → (Fin n → R)}
    (T : TriangularUnitPivot Φ) : True := by
  have _ : Fin n → R := T.pivot
  have _ : (i : Fin n) → (Fin n → R) → R := T.tail
  have _ : ∀ i, IsUnit (T.pivot i) := T.pivot_isUnit
  have _ : ∀ i v w, (∀ j : Fin n, j < i → v j = w j) → T.tail i v = T.tail i w := T.tail_lower
  have _ : ∀ v i, Φ v i = T.pivot i * v i + T.tail i v := T.apply_eq
  trivial

/-! ### NODE H.60 [theorem] — the back-substitution construction ([NEEDS-DERIVATION-EXPANSION]) -/

example {R : Type*} [CommRing R] {n : ℕ}
    {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) : Function.Bijective Φ :=
  TriangularUnitPivot.bijective (R := R) (n := n) (Φ := Φ) (T := T)

/-! ### NODE H.61 [lemma] — §15's fragile signature #4 (the `Fintype`/`Nat.card` mix) -/

example {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {n : ℕ} {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) (P : Finset (Fin n))
    (t : Fin n → R) :
    Nat.card {v : Fin n → R // ∀ i ∈ P, Φ v i = t i}
      = Fintype.card R ^ (n - P.card) :=
  TriangularUnitPivot.card_fibre (R := R) (n := n) (Φ := Φ) (T := T) (P := P) (t := t)

/-! ### NODE H.62 [lemma] — the R2 counterexample (EXECUTED at the gate below) -/

/-- Codex's toy (`ANNEX R R2.0`): `(x, y) ↦ (x, (x+π)y)` mod `π²`, at `π = 2`, `R = ZMod 4`. -/
example (v : Fin 2 → ZMod 4) : Fin 2 → ZMod 4 := codexToy (v := v)
example (v : Fin 2 → ZMod 4) : codexToy v = ![v 0, (v 0 + 2) * v 1] := rfl

example : ¬ Function.Surjective codexToy :=
  codexToy_not_surjective

example :
    (Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![0, 0])).card = 2 ∧
    (Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![1, 0])).card = 1 :=
  codexToy_fibre_not_constant

/-! ## §10 — THE DRAINAGE-RATE CALCULUS (H.63–H.72) -/

/-! ### NODE H.63 [theorem] — the union bound (SPLIT-MANDATED into 2)

Parse check performed at this gate: Mathlib's `∏ x ∈ s, f` body parses at precedence 67 and `-` is
`infixl:65`, so `∏ i ∈ s, T i - ∏ i ∈ s, (T i - u i)` DOES split at the subtraction as intended
(the `∑ … , u i * ∏ …` on the right, at `*`'s level 70, does NOT split). No parenthesization added;
recorded because the reading is load-bearing and not obvious. -/

example {ι : Type*} [DecidableEq ι] (s : Finset ι) (u T : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (huT : ∀ i ∈ s, u i ≤ T i) :
    ∏ i ∈ s, T i - ∏ i ∈ s, (T i - u i) ≤ ∑ i ∈ s, u i * ∏ j ∈ s.erase i, T j :=
  prod_sub_prod_le_sum (ι := ι) (s := s) (u := u) (T := T) (hu := hu) (huT := huT)

/-! ### NODE H.64 [lemma] -/

example {ι : Type*} (s : Finset ι) (u v T : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ u i) (huv : ∀ i ∈ s, u i ≤ v i) (hvT : ∀ i ∈ s, v i ≤ T i) :
    ∏ i ∈ s, (T i - v i) ≤ ∏ i ∈ s, (T i - u i) :=
  prod_sub_antitone (ι := ι) (s := s) (u := u) (v := v) (T := T) (h0 := h0) (huv := huv)
    (hvT := hvT)

/-! ### NODE H.65 [def] — `RateSpecies` (real body) -/

/-- **(A2-RATE)** — the species pinned onto `P(k)`'s fourth member (`ANNEX R R1.1`): a normalized
conservative complement decays with a POLYNOMIAL coefficient and an EXPONENTIAL deficit, with
constants depending on the degree data only. -/
example (Q : ℕ) (K : ℝ) (B c : ℕ) (f : ℕ → ℝ) : Prop :=
  RateSpecies (Q := Q) (K := K) (B := B) (c := c) (f := f)

example (Q : ℕ) (K : ℝ) (B c : ℕ) (f : ℕ → ℝ) :
    RateSpecies Q K B c f ↔ ∀ M, 1 ≤ M → f M ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹ := Iff.rfl

/-! ### NODE H.66 [lemma] -/

example {Q : ℕ} {K : ℝ} {B c : ℕ} {f g : ℕ → ℝ}
    (h : RateSpecies Q K B c f) (hg : ∀ M, 1 ≤ M → g M ≤ f M) : RateSpecies Q K B c g :=
  RateSpecies.of_le (Q := Q) (K := K) (B := B) (c := c) (f := f) (g := g) (h := h) (hg := hg)

example {Q : ℕ} (hQ : 2 ≤ Q) {K K' : ℝ} {B B' c c' : ℕ} {f : ℕ → ℝ}
    (h : RateSpecies Q K B c f) (hK : K ≤ K') (hK0 : 0 ≤ K) (hB : B ≤ B') (hc : c ≤ c') :
    RateSpecies Q K' B' c' f :=
  RateSpecies.mono (Q := Q) (hQ := hQ) (K := K) (K' := K') (B := B) (B' := B') (c := c) (c' := c')
    (f := f) (h := h) (hK := hK) (hK0 := hK0) (hB := hB) (hc := hc)

/-! ### NODE H.67 [theorem] -/

example {Q : ℕ} (hQ : 2 ≤ Q) {K : ℝ} {B c D M N : ℕ} (hK : 0 ≤ K)
    (hD : 1 ≤ D) (hc : c ≤ M) (hDM : D + M = N) {ρ δ : ℝ}
    (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹)
    (hδ : δ ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹) :
    ρ * δ ≤ K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - c))⁻¹ :=
  rate_growing (Q := Q) (hQ := hQ) (K := K) (B := B) (c := c) (D := D) (M := M) (N := N) (hK := hK)
    (hD := hD) (hc := hc) (hDM := hDM) (ρ := ρ) (δ := δ) (hρ0 := hρ0) (hδ0 := hδ0) (hρ := hρ)
    (hδ := hδ)

/-! ### NODE H.68 [theorem] -/

example {Q : ℕ} (hQ : 2 ≤ Q) {D M N c₀ : ℕ} (hD : 1 ≤ D) (hDM : D + M = N)
    (hM : M ≤ c₀) {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹) :
    ρ * δ ≤ ((Q : ℝ) ^ (N - c₀ - 1))⁻¹ :=
  rate_bounded (Q := Q) (hQ := hQ) (D := D) (M := M) (N := N) (c₀ := c₀) (hD := hD) (hDM := hDM)
    (hM := hM) (ρ := ρ) (δ := δ) (hρ0 := hρ0) (hδ0 := hδ0) (hδ1 := hδ1) (hρ := hρ)

/-! ### NODE H.69 [lemma] -/

example {Q : ℕ} (hQ : 2 ≤ Q) {K : ℝ} {B c c₀ N m p r : ℕ} (hK : 0 ≤ K)
    (hN : 1 ≤ N) (g : Fin r → ℝ) (hg0 : ∀ i, 0 ≤ g i)
    (hg : ∀ i, g i ≤ K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹) :
    (p * N ^ m : ℝ) * ∑ i, g i
      ≤ (r * p : ℝ) * (N : ℝ) ^ m * (K * (N : ℝ) ^ B) * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹ :=
  rate_sum_over_family (Q := Q) (hQ := hQ) (K := K) (B := B) (c := c) (c₀ := c₀) (N := N) (m := m)
    (p := p) (r := r) (hK := hK) (hN := hN) (g := g) (hg0 := hg0) (hg := hg)

/-! ### NODE H.70 [theorem] — `undecidedSeq` is ANTITONE (SPLIT-MANDATED into 2)

Lands in `Uniformity.Density` (theorems about landed objects), NOT in `.Induction`. -/

example {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] {n T W : ℕ} (h : T ≤ W) :
    undecidedSet O n W ⊆ coeffFactor (O := O) (n := n) h ⁻¹' undecidedSet O n T :=
  undecidedSet_preimage_subset (O := O) (n := n) (T := T) (W := W) (h := h)

example {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (n : ℕ) :
    Antitone (undecidedSeq O n) :=
  undecidedSeq_antitone (O := O) (n := n)

/-! ### NODE H.71 [theorem] — the lexicographic closure (SPLIT-MANDATED into 3) -/

/-- The three-leg recursion hypothesis of `GENIND.C′`, packaged so the induction can be stated. -/
-- 0e RETIREMENT (structure): constructor order + field types, then every field name. This is the
-- A-H.1/D6+D7 and A-H.2/α-0 RE-SIGNED form (seven scalar fields one-per-name; `hdesc` guarded by
-- `1 ≤ N`; `halpha` windowed by `m * (k + 1) < N`) — the diff below is against the landed
-- `Uniformity.Density.Induction.RecursionLegs`, i.e. it certifies that the fleet landed the
-- REPAIRED structure and not the committed one.
example (Q m c : ℕ) (u : ℕ → ℕ → ℝ)
    (head alpha beta : ℕ → ℕ → ℝ) (K' : ℝ) (B' c' n₀ : ℕ) (hK' : 0 ≤ K')
    (hsplit : ∀ D N, 1 ≤ N → u D N ≤ head D N + alpha D N + beta D N)
    (hu0 : ∀ D N, 0 ≤ u D N)
    (hhead : ∀ D N, 1 ≤ N → head D N ≤ ((Q : ℝ) ^ (N - 1))⁻¹)
    (halpha : ∀ D N, 1 ≤ N → alpha D N ≤
      ∑ k ∈ Finset.range n₀ with m * (k + 1) < N,
        ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ * u D (N - m * (k + 1)))
    (hbeta : ∀ D N, 1 ≤ N → beta D N ≤ K' * (N : ℝ) ^ (m + B') * ((Q : ℝ) ^ (N - c' - 1))⁻¹)
    (hdesc : ∀ (D N k : ℕ), 1 ≤ N → k < n₀ → 1 ≤ m * (k + 1) → N - m * (k + 1) < N) :
    RecursionLegs Q m c u :=
  ⟨head, alpha, beta, K', B', c', n₀, hK', hsplit, hu0, hhead, halpha, hbeta, hdesc⟩

example {Q m c : ℕ} {u : ℕ → ℕ → ℝ} (L : RecursionLegs Q m c u) : True := by
  have _ : ℕ → ℕ → ℝ := L.head
  have _ : ℕ → ℕ → ℝ := L.alpha
  have _ : ℕ → ℕ → ℝ := L.beta
  have _ : ℝ := L.K'
  have _ : ℕ := L.B'
  have _ : ℕ := L.c'
  have _ : ℕ := L.n₀
  have _ : 0 ≤ L.K' := L.hK'
  have _ : ∀ D N, 1 ≤ N → u D N ≤ L.head D N + L.alpha D N + L.beta D N := L.hsplit
  have _ : ∀ D N, 0 ≤ u D N := L.hu0
  have _ : ∀ D N, 1 ≤ N → L.head D N ≤ ((Q : ℝ) ^ (N - 1))⁻¹ := L.hhead
  have _ : ∀ D N, 1 ≤ N → L.alpha D N ≤
      ∑ k ∈ Finset.range L.n₀ with m * (k + 1) < N,
        ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ * u D (N - m * (k + 1)) := L.halpha
  have _ : ∀ D N, 1 ≤ N →
      L.beta D N ≤ L.K' * (N : ℝ) ^ (m + L.B') * ((Q : ℝ) ^ (N - L.c' - 1))⁻¹ := L.hbeta
  have _ : ∀ (D N k : ℕ), 1 ≤ N → k < L.n₀ → 1 ≤ m * (k + 1) → N - m * (k + 1) < N := L.hdesc
  trivial

-- [repaired: A-H.2/α-rate] `hmc : m < c` added: H.30's geometric bound fires at the recomposed
-- slope `γ = c − m`, and `1 ≤ γ` is exactly `hmc`. Without it the axiom is FALSE even windowed
-- (counterexamples at `c = m` in `verification/rate_close_ah2_check.py`), and signing the
-- committed form would have made this file's axiom set INCONSISTENT (the D4 precedent): with the
-- A-H.1/D7 structure inhabited, `rate_close` + the fleet's `legsWindowZero` derives `False`.
-- At the intended instantiation `c = m(m+1)/2` (the NORMALIZED α-locus slope; `clusterC m` is the
-- recomposed one), `hmc` ⟺ `m ≥ 2` — GENIND.A's own scope. See AMENDMENT A-H.2.
example {Q m c : ℕ} (hQ : 2 ≤ Q) (hc : 1 ≤ c) (hm : 1 ≤ m) (hmc : m < c)
    {u : ℕ → ℕ → ℝ} (L : RecursionLegs Q m c u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D, RateSpecies Q K (m + L.B' + 1) (L.c' + 1) (u D) :=
  rate_close (Q := Q) (m := m) (c := c) (hQ := hQ) (hc := hc) (hm := hm) (hmc := hmc) (u := u)
    (L := L)

/-! ### NODE H.72 [theorem] — §15's fragile signature #5, and **DEFECT D4**

The docstring below is the blueprint's, VERBATIM — and it says the inequality is "stated over `ℤ`",
which the signed type contradicts: every term is `ℕ`, so the trailing `- 2 * (2 * I.slack)` is
TRUNCATED. Signed verbatim anyway (the type elaborates); see D4 in the header. This is the one node
§16 item 1 names as invisible to the stub gate, and the ℕ/ℤ carrier mismatch is the part of it that
IS visible. -/

-- **DEFECT D4 — REFUTED, THEREFORE NOT SIGNED** (the `G.23a` precedent again; and signing it would
-- make this file's axiom set INCONSISTENT — see the machine-checked refutation in the gate section,
-- which derives the false `4 ≥ 8` from a genuine `StageInterface` witness).  The blueprint's H.72 is
--
--   /-- **(C2Q.1)** — the loss-priced stage-drain exponent, in the `2*`-cleared form.  The
--   conclusion's exponent inequality is stated over `ℤ` so no `ℕ`-truncation can hide a sign. -/
--   theorem rate_lossPriced {G : GenreDatum} {N H S : ℕ} (I : StageInterface G N H S) :
--       2 * (G.f₁ * I.stageWindow) + 2 * ((S + 1) * H) + 2 * (2 * I.entryCodim)
--         ≥ 2 * (2 * G.keyDeg * (N - 1 - H)) + 2 * (2 * G.keyDeg * H) + H
--           - 2 * (2 * I.slack)
--
-- and it is FALSE.  Smallest witness (genre E at `t = 0`, i.e. `(Q,e₁,f₁,μ,h) = (2,2,1,2,1)`,
-- `N = 2`, `H = 0`, `S = 4`, `stageWindow = 2`, `stageLoss = entryCodim = slack = 0`): all of
-- `hS` (`4 ≤ 4`), `hwin` (`2·(2−1−0) = 2 ≤ 2+0`) and `hprice` (`0 ≤ 0`) hold, LHS `= 4`,
-- RHS `= 8`.  The instance is CONSTRUCTED in the gate section (`stageIfaceE`), so this is a
-- machine-checked refutation, not a numerical suspicion.  See D4 in the header for the diagnosis
-- (which terms of the `2*`-clearing were missed) and the verified candidate repair.

/-- **RETIREMENT FINDING R1 — H.72 IS RETIRED AGAINST THE AMENDMENT, NOT AGAINST THE DISPLAY THIS
FILE ORIGINALLY GATED.** The blueprint adopted the gate's CANDIDATE A *in place*
(`[repaired: A-H.1/D4]`, CHAP-H `**SIGNATURE.**` block of H.72) and the fleet landed exactly that
type, so this node's signed type CHANGED between the stub gate and the landing. The refuted display
is retained verbatim above as provenance; the `example` below diffs the AMENDED type against
`Uniformity.Density.Induction.rate_lossPriced`. Class: sanctioned statement change, not silent
drift — but the reader must not treat the commented display above as what is proved.

**F2/R3, RESOLVED 2026-08-15 (was: STILL OPEN, and it had moved):** at retirement the landed corpus
contained NO inhabitant of `StageInterface` anywhere, so `leanfinal`'s H.72 was a theorem about a
possibly-empty type and the repo's ONLY witness was `stageIfaceE` in this file's gate section below —
in a file `leanfinal` never imports. Both witnesses now live in `leanfinal`
(`Uniformity/ChapH/H09w.lean`: `stageIfaceE` at genre E, `stageIfaceF` at genre F), and the `example`
below is therefore a diff of a theorem with an EXHIBITED hypothesis type. -/
example {G : GenreDatum} {N H S : ℕ} (I : StageInterface G N H S) :
    2 * (G.f₁ * I.stageWindow) + (S + 1) * H + 2 * I.entryCodim + 2 * I.slack
      ≥ 2 * G.keyDeg * (N - 1 - H) + 2 * G.keyDeg * H + H :=
  rate_lossPriced (G := G) (N := N) (H := H) (S := S) (I := I)

/-! ## §11 — THE σ DICTIONARY AND THE `(e, f)`-FORCING CHAIN (`μ = 2` ONLY) (H.73–H.79) -/

/-! ### NODE H.73 [def] — `StageLeaf` + `stageSigma` (real bodies; GC-4's dictionary pattern) -/

/-- The three decided leaf labels of a `μ = 2` stage read (`GENHN.C`; `SPLITEQ` and `SPLTAIL` share
`twoSided`'s σ-block, per the dictionary's own grouping). -/
example : StageLeaf := StageLeaf.ram
example : StageLeaf := StageLeaf.twoSided
example : StageLeaf := StageLeaf.inert
example : DecidableEq StageLeaf := inferInstance
example : Fintype StageLeaf := inferInstance

/-- `GENHN.C`'s leaf dictionary, relative to the ambient. -/
example (G : GenreDatum) : StageLeaf → FactorizationType := stageSigma (G := G)
example (G : GenreDatum) : stageSigma G .ram = ⟨{(2 * G.e₁, G.f₁)}⟩ := rfl
example (G : GenreDatum) : stageSigma G .twoSided = ⟨{(G.e₁, G.f₁), (G.e₁, G.f₁)}⟩ := rfl
example (G : GenreDatum) : stageSigma G .inert = ⟨{(G.e₁, 2 * G.f₁)}⟩ := rfl

/-! ### NODE H.74 [lemma] — GC-4's mandatory degree-conservation lemma -/

example (G : GenreDatum) (l : StageLeaf) :
    (stageSigma G l).degree = 2 * G.keyDeg :=
  stageSigma_degree (G := G) (l := l)

/-! ### NODE H.75 [lemma] -/

example (t : ℕ) :
    stageSigma (genreE2 t) .ram = ⟨{(4, 1)}⟩ ∧
    stageSigma (genreE2 t) .twoSided = ⟨{(2, 1), (2, 1)}⟩ ∧
    stageSigma (genreE2 t) .inert = ⟨{(2, 2)}⟩ :=
  stageSigma_genreE (t := t)

example (t : ℕ) :
    (stageSigma (genreE2 t) .ram).degree = 4 ∧
    (stageSigma genreA2witness .ram).degree = 6 ∧
    (stageSigma genreD2bwitness .ram).degree = 4 :=
  stageSigma_degree_instances (t := t)

/-! ### NODE H.76 [theorem] — the `(e, f)`-forcing chain (lands in `Uniformity.Density`) -/

example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {g : Polynomial O} (hg : g.Monic) {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f)
    (hdeg : g.natDegree = e * f) {p : ℕ × ℕ} (hp : (typeOf g).data = {p})
    (hpe : e ∣ p.1) (hpf : f ∣ p.2) : p = (e, f) :=
  efPair_forced_of_dvd (O := O) (g := g) (hg := hg) (e := e) (f := f) (he := he) (hf := hf)
    (hdeg := hdeg) (p := p) (hp := hp) (hpe := hpe) (hpf := hpf)

/-! ### NODE H.77 [lemma] -/

example {u e : ℕ} (hu : Odd u) : Odd (Nat.gcd u e) :=
  gcd_odd_of_odd (u := u) (e := e) (hu := hu)

example {u e : ℕ} (he : 1 ≤ e) (hu : Odd u) :
    Nat.lcm e (2 * e / Nat.gcd u e) = 2 * e :=
  lcm_ram_value_group (u := u) (e := e) (he := he) (hu := hu)

/-! ### NODE H.78 [def] -/

/-- `T(b)′`(iii)'s composed dictionary: the σ-composition FORMULA `(e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s)` —
the part of the REFUTED `T(b)` that SURVIVES, applied to the composed-key pins. -/
example (G : GenreDatum) (e₂ f₂ : ℕ) : StageLeaf → FactorizationType :=
  composedSigma (G := G) (e₂ := e₂) (f₂ := f₂)
example (G : GenreDatum) (e₂ f₂ : ℕ) :
    composedSigma G e₂ f₂ .ram = ⟨{(2 * (G.e₁ * e₂), G.f₁ * f₂)}⟩ := rfl
example (G : GenreDatum) (e₂ f₂ : ℕ) :
    composedSigma G e₂ f₂ .twoSided
      = ⟨{(G.e₁ * e₂, G.f₁ * f₂), (G.e₁ * e₂, G.f₁ * f₂)}⟩ := rfl
example (G : GenreDatum) (e₂ f₂ : ℕ) :
    composedSigma G e₂ f₂ .inert = ⟨{(G.e₁ * e₂, 2 * (G.f₁ * f₂))}⟩ := rfl

/-! ### NODE H.79 [lemma] -/

example (G : GenreDatum) (e₂ f₂ : ℕ) (l : StageLeaf) :
    (composedSigma G e₂ f₂ l).degree = 2 * (G.keyDeg * (e₂ * f₂)) :=
  composedSigma_degree (G := G) (e₂ := e₂) (f₂ := f₂) (l := l)

example (G : GenreDatum) (e₂ f₂ : ℕ) :
    G.keyDeg * (e₂ * f₂) = (G.e₁ * e₂) * (G.f₁ * f₂) :=
  composedDeg_eq (G := G) (e₂ := e₂) (f₂ := f₂)

/-! ## §12 — THE `n = 4` TEMPLATE (H.80–H.92) -/

/-! ### NODE H.80 [lemma] -/

open Polynomial in
example {R : Type*} [CommRing R] (s a₁ a₀ b₁ b₀ : R) :
    ((X ^ 2 - C s) ^ 2 + (C a₁ * X + C a₀) * (X ^ 2 - C s) + (C b₁ * X + C b₀))
      = X ^ 4 + C a₁ * X ^ 3 + C (a₀ - 2 * s) * X ^ 2 + C (b₁ - s * a₁) * X
        + C (b₀ - s * a₀ + s ^ 2) :=
  quartic_dev_E (R := R) (s := s) (a₁ := a₁) (a₀ := a₀) (b₁ := b₁) (b₀ := b₀)

/-! ### NODE H.81 [lemma] -/

open Polynomial in
example {R : Type*} [CommRing R] (p₁ p₀ a₁ a₀ b₁ b₀ : R) :
    ((X ^ 2 + C p₁ * X + C p₀) ^ 2 + (C a₁ * X + C a₀) * (X ^ 2 + C p₁ * X + C p₀)
        + (C b₁ * X + C b₀))
      = X ^ 4 + C (2 * p₁ + a₁) * X ^ 3 + C (p₁ ^ 2 + 2 * p₀ + a₁ * p₁ + a₀) * X ^ 2
        + C (2 * p₁ * p₀ + a₁ * p₀ + a₀ * p₁ + b₁) * X + C (p₀ ^ 2 + a₀ * p₀ + b₀) :=
  quartic_dev_F (R := R) (p₁ := p₁) (p₀ := p₀) (a₁ := a₁) (a₀ := a₀) (b₁ := b₁) (b₀ := b₀)

/-! ### NODE H.82 [lemma] (SPLIT CANDIDATE) -/

example (t : ℕ) :
    (2 * t + 1 + 1) / 2 = t + 1 ∧ (2 * t + 1) + 1 = 2 * t + 2 ∧
    (3 * (2 * t + 1) + 1) / 2 = 3 * t + 2 ∧ 2 * (2 * t + 1) + 1 = 4 * t + 3 :=
  quartic_floors_E (t := t)

example (t : ℕ) :
    min (2 * (t + 1) + (2 * t + 1)) (2 * (2 * t + 2)) = 2 * (2 * t + 1) + 1 ∧
    min (2 * (3 * t + 2) + (2 * t + 1)) (2 * (4 * t + 3)) = 4 * (2 * t + 1) + 1 :=
  quartic_node_E (t := t)

/-! ### NODE H.83 [lemma] (SPLIT CANDIDATE) -/

example {N k : ℕ} (hN : 4 * k + 1 ≤ N) :
    (N - k - 1) + (N - 2 * k - 1) + (N - 3 * k - 1) + (N - 4 * k - 1) + (10 * k + 4) = 4 * N :=
  quartic_total_F (N := N) (k := k) (hN := hN)

example (k : ℕ) :
    min ((k + 1) + k) (2 * k + 1) = 2 * k + 1 ∧ min ((3 * k + 1) + k) (4 * k + 1) = 4 * k + 1 :=
  quartic_node_F (k := k)

/-! ### NODE H.84 [lemma] — `w11_node_shape` retained (§15 rule 4 left it to discretion) -/

example (S : ℕ) : 2 * S + 1 = 2 * S + 1 ∧ S + 1 = S + 1 :=
  w11_node_shape (S := S)

example (h : ℕ) : (4 * h + 1, 2 * h + 1) = (2 * (2 * h) + 1, (2 * h) + 1) :=
  w11_node_E (h := h)

example (k : ℕ) : (4 * k + 1, 2 * k + 1) = (2 * (2 * k) + 1, (2 * k) + 1) :=
  w11_node_F (k := k)

/-! ### NODE H.85 [lemma] -/

example {h va vb : ℕ} (hh : Odd h) : 2 * va + h ≠ 2 * vb :=
  dv_parity_ne (h := h) (va := va) (vb := vb) (hh := hh)

example {h va vb : ℕ} (hh : Odd h) :
    min (2 * va + h) (2 * vb) = 2 * va + h ∨ min (2 * va + h) (2 * vb) = 2 * vb :=
  dv_parity_min_unique (h := h) (va := va) (vb := vb) (hh := hh)

/-! ### NODE H.86 [lemma] -/

example {h dμ va : ℕ} (hh : 1 ≤ h) (hd : 2 * h + 1 ≤ dμ) (hva : h + 1 ≤ 2 * va) :
    dμ < min (2 * (dμ - h)) (2 * va + (dμ - h)) :=
  carry_height_gt (h := h) (dμ := dμ) (va := va) (hh := hh) (hd := hd) (hva := hva)

/-! ### NODE H.87 [lemma] — the carry cancellation, both characteristics -/

example {R : Type*} [CommRing R] {z s S₀ : R} (h : S₀ = z * s ^ 2) :
    S₀ + z * s ^ 2 - 2 * (z * s ^ 2) = 0 :=
  carry_cancel (R := R) (z := z) (s := s) (S₀ := S₀) (h := h)

example {R : Type*} [CommRing R] (hR : (2 : R) = 0) (z s : R) :
    z * s ^ 2 + z * s ^ 2 = 0 :=
  carry_cancel_char_two (R := R) (hR := hR) (z := z) (s := s)

example {R : Type*} [CommRing R] {S₁ s : R} (h : S₁ = -(2 * s)) : S₁ + 2 * s = 0 :=
  refine_kill_A₁ (R := R) (S₁ := S₁) (s := s) (h := h)

/-! ### NODE H.88 [lemma] — `CapBranch` + `capBranch` (real bodies) + the trichotomy -/

/-- The three exits of the `dv0 = N` boundary read, with PAIRWISE-DISJOINT antecedents
(`GENH4-CAP`, as re-derived at `[r3, PE3 MINOR 1]` from `GENH4-3(i)`'s own "else (ii)"). -/
example : CapBranch := CapBranch.twoSided
example : CapBranch := CapBranch.ram
example : CapBranch := CapBranch.und
example : DecidableEq CapBranch := inferInstance

example (N w : ℕ) : CapBranch := capBranch (N := N) (w := w)
example (N w : ℕ) :
    capBranch N w = if 2 * w < N then .twoSided else if N % 2 = 1 then .ram else .und := rfl

example (N w : ℕ) :
    (capBranch N w = .twoSided ↔ 2 * w < N) ∧
    (capBranch N w = .ram ↔ (N ≤ 2 * w ∧ N % 2 = 1)) ∧
    (capBranch N w = .und ↔ (N ≤ 2 * w ∧ N % 2 = 0)) :=
  capBranch_trichotomy (N := N) (w := w)

example : capBranch 7 3 = .twoSided :=
  capBranch_seven_three

/-! ### NODE H.89 [lemma] -/

example {u h N : ℕ} (hh : 1 ≤ h) (hu : u ≤ 2 * N - 1) (hN : 1 ≤ N) :
    (u - h) / 2 ≤ N - 1 :=
  consulted_ram (u := u) (h := h) (N := N) (hh := hh) (hu := hu) (hN := hN)

example {w N : ℕ} (hw : w ≤ 2 * N - 2) : w / 2 ≤ N - 1 :=
  consulted_twoSided (w := w) (N := N) (hw := hw)

example {dμ N : ℕ} (hd : 2 * dμ ≤ 2 * N - 2) : dμ ≤ N - 1 :=
  consulted_refine (dμ := dμ) (N := N) (hd := hd)

-- **DEFECT D8 — REFUTED, THEREFORE NOT SIGNED** (the `G.23a card_resStratum` precedent: a refuted
-- statement is commented out, never signed as an axiom).  The blueprint's fourth H.89 declaration is
--
--   theorem band_not_consulted {m N h : ℕ} (hband : 2 * N ≤ m) : ¬ (m ≤ 2 * N - 1)
--
-- and it is FALSE at `(N, m) = (0, 0)`: the antecedent `2 * 0 ≤ 0` holds, and the conclusion
-- `¬ (0 ≤ 2 * 0 - 1)` is `¬ (0 ≤ 0)`, because ℕ-truncated `2 * 0 - 1 = 0`.  Found by the arithmetic
-- gate below (brute force over `m < 16`, `N < 9`; `(0,0)` is the only counterexample in that box).
-- Two minimal repairs both hold on a 40 × 20 grid and are checked below: add `1 ≤ N` (the guard its
-- three sibling H.89 lemmas all carry) or add `1 ≤ m`.  `h` is unused in the statement either way.
-- The blueprint must choose; this file signs neither form.

/-- **RETIREMENT FINDING R2 — H.89 IS RETIRED AGAINST THE AMENDMENT.** The blueprint chose the
sibling guard `(hN : 1 ≤ N)` and restored it in place (`[repaired: A-H.1/D8]`), and the fleet landed
exactly that type. Same class as R1: a sanctioned statement change between gate and landing, so the
`example` below is at the AMENDED type, not the commented display above. `h` remains unused in the
statement (the landed declaration keeps it, so the named application must supply it). -/
example {m N h : ℕ} (hN : 1 ≤ N) (hband : 2 * N ≤ m) : ¬ (m ≤ 2 * N - 1) :=
  band_not_consulted (m := m) (N := N) (h := h) (hN := hN) (hband := hband)

/-! ### NODE H.90 [lemma] -/

example {dμ h : ℕ} (hd : 2 * h + 2 ≤ dμ) : h + 1 ≤ dμ / 2 :=
  invariant_even (dμ := dμ) (h := h) (hd := hd)

example {dμ h : ℕ} (hd : 2 * h + 1 ≤ dμ) : (h + 1) / 2 ≤ (dμ - h) / 2 :=
  invariant_odd (dμ := dμ) (h := h) (hd := hd)

/-! ### NODE H.91 [lemma] — `LeafE` + `leafFactorE` (real bodies) -/

/-- The six decided/undecided leaf labels of a genre-E stage read, and their letter/census factors
(`THEOREM GENH4.A`'s four-slot model, §S6.1's table). -/
example : LeafE := LeafE.ram
example : LeafE := LeafE.twoSided
example : LeafE := LeafE.splitEq
example : LeafE := LeafE.inert
example : LeafE := LeafE.splTail
example : LeafE := LeafE.und
example : DecidableEq LeafE := inferInstance
example : Fintype LeafE := inferInstance

example (q : ℕ) : LeafE → ℕ := leafFactorE (q := q)
example (q : ℕ) :
    (leafFactorE q .ram, leafFactorE q .twoSided, leafFactorE q .splitEq,
      leafFactorE q .inert, leafFactorE q .splTail, leafFactorE q .und)
      = (q - 1, (q - 1) ^ 2, splitEqCensus q, inertCensus q, q - 1, 1) := rfl

example {q : ℕ} (hq : 3 ≤ q) (l : LeafE) : 0 < leafFactorE q l :=
  leafFactorE_pos (q := q) (hq := hq) (l := l)

/-! ### NODE H.92 [lemma] -/

example {ι : Type*} [DecidableEq ι] (D : Finset ι) (L : ℕ) :
    ∑ H ∈ D.powerset, L ^ H.card = (1 + L) ^ D.card :=
  subset_sum_pow (ι := ι) (D := D) (L := L)

example (q δ : ℕ) (hq : 1 ≤ q) :
    1 + ∑ j ∈ Finset.range δ, (q - 1) * q ^ j = q ^ δ :=
  bracket_telescope_E (q := q) (δ := δ) (hq := hq)

example (q Δ μ : ℕ) : q ^ (2 * (Δ * μ)) = (q ^ 2) ^ (Δ * μ) :=
  macroscopic_rate (q := q) (Δ := Δ) (μ := μ)

/-! ## §13 — THE ASSEMBLY (H.93–H.99) -/

/-! ### NODE H.93 [def] — `A1Cell` + its three derived defs (real bodies; SPLIT-MANDATED into 2) -/

/-- One cell of an `(A1)`-admissible family: a shifted product of arithmetic progressions in `ℕ ^ r`
with an affine positive-coefficient exponent, an affine visibility form, a coefficient, and a
σ-label.  **The σ-label field is W-12's r4 STRENGTHENING of `(A1)`** — see the note. -/
-- 0e RETIREMENT (structure): constructor order + field types, then every field name.
example (r : ℕ) (offset stride : Fin r → ℕ) (stride_pos : ∀ i, 0 < stride i)
    (expCoeff : Fin r → ℕ) (expCoeff_pos : ∀ i, 0 < expCoeff i) (expConst : ℕ)
    (visCoeff : Fin r → ℕ) (visConst coeff : ℕ) (σ : FactorizationType) : A1Cell r :=
  ⟨offset, stride, stride_pos, expCoeff, expCoeff_pos, expConst, visCoeff, visConst, coeff, σ⟩

example {r : ℕ} (C : A1Cell r) : True := by
  have _ : Fin r → ℕ := C.offset
  have _ : Fin r → ℕ := C.stride
  have _ : ∀ i, 0 < C.stride i := C.stride_pos
  have _ : Fin r → ℕ := C.expCoeff
  have _ : ∀ i, 0 < C.expCoeff i := C.expCoeff_pos
  have _ : ℕ := C.expConst
  have _ : Fin r → ℕ := C.visCoeff
  have _ : ℕ := C.visConst
  have _ : ℕ := C.coeff
  have _ : FactorizationType := C.σ
  trivial

/-- The parameter locus of a cell: the shifted product of arithmetic progressions. -/
example {r : ℕ} (C : A1Cell r) : Set (Fin r → ℕ) := A1Cell.locus (r := r) (C := C)
example {r : ℕ} (C : A1Cell r) :
    C.locus = {p | ∀ i, ∃ t : ℕ, p i = C.offset i + C.stride i * t} := rfl

/-- The cell's exponent at a parameter point. -/
example {r : ℕ} (C : A1Cell r) (p : Fin r → ℕ) : ℕ := A1Cell.exp (r := r) (C := C) (p := p)
example {r : ℕ} (C : A1Cell r) (p : Fin r → ℕ) :
    C.exp p = C.expConst + ∑ i, C.expCoeff i * p i := rfl

/-- An `(A1)`-admissible family is a finite list of cells. -/
example (r : ℕ) : Type := A1Family (r := r)
example (r : ℕ) : A1Family r = List (A1Cell r) := rfl

/-! ### NODE H.94 [theorem] — closure of `(A1)` (SPLIT-MANDATED into 3); **DEFECT D5**

`prod`'s body is the PROOF field's, verbatim in content (`Fin.append` on the four vectors).
`deltaSubst`'s body is a STUB-SIDE DETERMINATION: the blueprint pins only the exponent data, and
the choice below (transport the visibility form by the same substitution, keep `offset`, `stride`,
`coeff`, `σ`) is the one under which the signed `deltaSubst_exp` holds. See D5. -/

/-- (i) The product of two cells. -/
example {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) : A1Cell (r₁ + r₂) :=
  A1Cell.prod (r₁ := r₁) (r₂ := r₂) (C := C) (D := D)

-- The nine data fields, `rfl`-diffed (`stride_pos`/`expCoeff_pos` are proofs, so proof-irrelevant).
-- D5 named `prod` as fully specified by the blueprint's PROOF field; this is that check.
example {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) :
    ((C.prod D).offset, (C.prod D).stride, (C.prod D).expCoeff, (C.prod D).visCoeff)
      = (Fin.append C.offset D.offset, Fin.append C.stride D.stride,
          Fin.append C.expCoeff D.expCoeff, Fin.append C.visCoeff D.visCoeff) := rfl

example {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) :
    ((C.prod D).expConst, (C.prod D).visConst, (C.prod D).coeff, (C.prod D).σ)
      = (C.expConst + D.expConst, C.visConst + D.visConst, C.coeff * D.coeff,
          ⟨C.σ.data + D.σ.data⟩) := rfl

example {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) (p : Fin (r₁ + r₂) → ℕ) :
    (C.prod D).exp p = C.exp (fun i => p (Fin.castAdd r₂ i)) + D.exp (fun j => p (Fin.natAdd r₁ j)) :=
  A1Cell.prod_exp (r₁ := r₁) (r₂ := r₂) (C := C) (D := D) (p := p)

example {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) :
    (C.prod D).σ.degree = C.σ.degree + D.σ.degree :=
  A1Cell.prod_σ_degree (r₁ := r₁) (r₂ := r₂) (C := C) (D := D)

/-- (iii) The `δ`-substitution `w₂ = w₁ + 1 + δ` of `W-12` §S3.4's 2SIDED instance. -/
example (C : A1Cell 2) : A1Cell 2 := A1Cell.deltaSubst (C := C)

-- **THE D5 CHECK.** `deltaSubst`'s body is a STUB-SIDE DETERMINATION (the blueprint's PROOF field
-- pins only `expCoeff`); these `rfl`s certify that the fleet landed the SAME determination for
-- `offset`, `stride`, `expConst`, `visCoeff`, `visConst`, `coeff` and `σ`, not a different one.
example (C : A1Cell 2) :
    ((C.deltaSubst).offset, (C.deltaSubst).stride, (C.deltaSubst).coeff, (C.deltaSubst).σ)
      = (C.offset, C.stride, C.coeff, C.σ) := rfl

example (C : A1Cell 2) :
    ((C.deltaSubst).expCoeff, (C.deltaSubst).expConst)
      = (![C.expCoeff 0 + C.expCoeff 1, C.expCoeff 1], C.expConst + C.expCoeff 1) := rfl

example (C : A1Cell 2) :
    ((C.deltaSubst).visCoeff, (C.deltaSubst).visConst)
      = (![C.visCoeff 0 + C.visCoeff 1, C.visCoeff 1], C.visConst + C.visCoeff 1) := rfl

example (C : A1Cell 2) (w δ : ℕ) :
    (C.deltaSubst).exp ![w, δ] = C.exp ![w, w + 1 + δ] :=
  A1Cell.deltaSubst_exp (C := C) (w := w) (δ := δ)

/-! ### NODE H.95 [def] — `InductionPackage` (real body; lands in `Uniformity.Density`)

`Induction.RateSpecies` is written `RateSpecies` here — the LeanspecH namespace flattening. -/

/-- **`P(n)`** — the degree-`n` package `{history-resolved exact menu + finite (A1)-admissible
aggregate menu + (A0) + exact-complement (A2)}` of `THEOREM GENIND.B`, in the form `leanfinal`'s API
can state: a covering menu, the certified densities, and the complement's RATE species
(`(A2-RATE)`, `ANNEX R R1.1`). -/
example (n : ℕ) : Prop := InductionPackage (n := n)
example (n : ℕ) :
    InductionPackage n ↔
      ∃ (K : ℝ) (B c : ℕ), 0 ≤ K ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
          [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
          (∃ S : Finset FactorizationType, CoveringMenu O n S) ∧
            RateSpecies (residueCard O) K B c (undecidedSeq O n) := Iff.rfl

/-! ### NODE H.96 [theorem] -/

example : InductionPackage 2 :=
  package_two

/-! ### NODE H.97 [theorem] — `package_three_of_rate` (§15 rule 3)

NOT SIGNED, per §15 rule 3 (the blueprint declares it a defect and adopts the rate form):
```
theorem package_three_of_drainage (hd : DrainageAt 3) : InductionPackage 3
```
The adopted form, from H.97's ⚠ SIGNATURE NOTE (blueprint line 5923), is signed below. -/

example
    (hrate : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      RateSpecies (residueCard O) 1 1 0 (undecidedSeq O 3)) :
    InductionPackage 3 :=
  package_three_of_rate (hrate := hrate)

/-! ### NODE H.98 [theorem] — the capstone, conditionally -/

/-- `GENIND.B` Step 5: the package's `(A2)` member delivers drainage at every degree. -/
example (hp : ∀ n, InductionPackage n) : ∀ n, DrainageAt n :=
  drainage_of_package (hp := hp)

/-- The capstone, assembled: certified densities + package ⟹ `UniformityStatement`. -/
example (hdec : UniformityStatementDecided)
    (hp : ∀ n, InductionPackage n) : UniformityStatement :=
  uniformity_of_package (hdec := hdec) (hp := hp)

/-! ### NODE H.99 [gate] — EXECUTED HERE (GC-11; §15's recommended gate order step (c))

`#print axioms` is not runnable at stub stage (nothing has landed; every name here is an `axiom` by
construction), so the census half of H.99 is deferred to `leanfinal`. The two-column NUMERIC half
is executed below, at `q = 2` AND `q = 3` (GC-11), plus the non-vacuity `#check`s.

**FINDING F1 (recorded, not a defect):** `DecidableEq FactorizationType` is `noncomputable` in the
landed kernel (`Uniformity/Density/LocalData.lean:56`, `Classical.decEq`), so σ-VALUED equalities —
H.75's first three conjuncts, and any `stageSigma`/`composedSigma` value check — CANNOT be executed
at this or any gate. Only their `degree` projections can (Multiset `map`/`sum` are computable), and
that is exactly what GC-4's mandatory degree-conservation lemma gives. σ-value claims are
theorem-only for the whole project. -/

section NumericGate

/-! H.99(ii), the blueprint's own `#eval` column, with its expected values. -/
#eval (alphaBracket 2 1 3, alphaBracket 3 1 2, alphaBracket 4 1 2)   -- expect (32, 54, 192)
#eval (uTwo 2 6, uTwo 3 6)                                            -- expect (64, 567)
#eval (lawE 2 6 1, lawE 3 4 1, lawE 5 3 1)                            -- expect (65536, 13122, 2500)
#eval (lawF 2 6 1, lawV1E2 2 5 1)                                     -- expect (1024, 12288)
#eval (splitEqCensus 3, inertCensus 3)                                -- expect (1, 3)

/-! Every closed-form numeric claim of the chapter, EXECUTED. A false line aborts elaboration of
this file, so this block is a build-time gate, not a print-out. Two primes minimum everywhere
(GC-11); `q = 5` carried too where the blueprint audits it. -/
#eval show IO Unit from do
  let chk (name : String) (b : Bool) : IO Unit :=
    unless b do throw (IO.userError s!"NUMERIC GATE FAILURE: {name}")
  -- H.21 (the `(CS-2)` certificate: the corpus's ONLY guard on the MASS normalization)
  chk "H.21 alphaBracket 4 1 2 = 192" (alphaBracket 4 1 2 == 192)
  chk "H.21 alphaBracket 3 1 2 = 54" (alphaBracket 3 1 2 == 54)
  chk "H.21 alphaBracket 2 1 3 = 32" (alphaBracket 2 1 3 == 32)
  chk "H.21 massNorm 16*12 = 192" ((4 ^ 2 * ((4 - 1) * 4 ^ 1) : ℕ) == alphaBracket 4 1 2)
  -- H.20's closed form against the recursion, at q = 2 and q = 3, μ = 1..5
  chk "H.20 closed form q=2" (List.all [1,2,3,4,5] fun m =>
    2 * alphaBracket 2 1 m == (2 - 1) * 2 ^ (2 * m))
  chk "H.20 closed form q=3" (List.all [1,2,3,4,5] fun m =>
    3 * alphaBracket 3 1 m == (3 - 1) * 3 ^ (2 * m))
  chk "H.19 alphaBracket_succ q=3 c=2" (List.all [1,2,3,4] fun m =>
    alphaBracket 3 2 (m + 1) == 3 ^ 3 * alphaBracket 3 2 m)
  -- H.29, both primes (twelve values)
  chk "H.29 uTwo audit q=2" ([uTwo 2 1, uTwo 2 2, uTwo 2 3, uTwo 2 4, uTwo 2 5, uTwo 2 6]
    == [1, 2, 6, 12, 32, 64])
  chk "H.29 uTwo audit q=3" ([uTwo 3 1, uTwo 3 2, uTwo 3 3, uTwo 3 4, uTwo 3 5, uTwo 3 6]
    == [1, 3, 15, 45, 189, 567])
  -- H.24, H.25, H.26, H.27 spot-checked against the recursion at q = 2, 3 (N ≤ 9)
  chk "H.24 uTwo_two" (List.all [2,3,5,7] fun q => uTwo q 2 == q)
  chk "H.25 uTwo_rec q=2" (List.all [3,4,5,6,7,8,9] fun N =>
    uTwo 2 N + 2 ^ (N - 2) == 2 ^ (N - 1) + 2 ^ 2 * uTwo 2 (N - 2))
  chk "H.25 uTwo_rec q=3" (List.all [3,4,5,6,7,8,9] fun N =>
    uTwo 3 N + 3 ^ (N - 2) == 3 ^ (N - 1) + 3 ^ 2 * uTwo 3 (N - 2))
  chk "H.26 uTwo_closed q=2" (List.all [2,3,4,5,6,7,8,9] fun M =>
    uTwo 2 M == 2 ^ (M - 1) + ((M - 1) / 2) * ((2 - 1) * 2 ^ (M - 2)))
  chk "H.26 uTwo_closed q=3" (List.all [2,3,4,5,6,7,8,9] fun M =>
    uTwo 3 M == 3 ^ (M - 1) + ((M - 1) / 2) * ((3 - 1) * 3 ^ (M - 2)))
  chk "H.27 uTwo_le q=2" (List.all [1,2,3,4,5,6,7,8,9] fun N => uTwo 2 N ≤ N * 2 ^ (N - 1))
  chk "H.27 uTwo_le q=3" (List.all [1,2,3,4,5,6,7,8,9] fun N => uTwo 3 N ≤ N * 3 ^ (N - 1))
  -- H.41 (the quartic-law audit, verbatim) and H.38/H.40/H.42's instances
  chk "H.41 quartic audit" (lawE 2 6 1 == 65536 && lawE 3 4 1 == 13122 && lawE 5 3 1 == 2500
    && lawF 2 6 1 == 1024 && lawF 2 5 1 == 64 && lawE 2 6 1 + lawF 2 6 1 == 66560)
  chk "H.38 lawE below floor is nonzero at (q,N,h)=(2,2,1)" (lawE 2 2 1 != 0)
  chk "H.38 lawE below floor is nonzero at (q,N,h)=(3,2,1)" (lawE 3 2 1 != 0)
  chk "H.40 lawF_exp_neg_below_floor" (((4 : Int) * 2 - 10 * 1 - 4) == -6)
  chk "H.42 headroom_exp_odd" (List.all [0,1,2,3,4] fun t => (5 * (2 * t + 1) + 1) / 2 == 5 * t + 3)
  chk "H.42 lawV1E2 2 5 1 = 12288" (lawV1E2 2 5 1 == 12288)
  chk "H.42 lawV1E2 3 5 1" (lawV1E2 3 5 1 == lawE 3 5 1 * (3 ^ 2 - 1))
  -- H.44 / H.45: the censuses at q = 2 and q = 3
  chk "H.44 pinCensus" (pinCensus 2 1 == 1 && pinCensus 2 2 == 3 && pinCensus 3 1 == 2
    && pinCensus 3 2 == 8)
  chk "H.45 splitEqCensus" (splitEqCensus 2 == 0 && splitEqCensus 3 == 1 && splitEqCensus 4 == 3)
  chk "H.45 inertCensus" (inertCensus 2 == 1 && inertCensus 3 == 3 && inertCensus 4 == 6)
  chk "H.45 two_mul identities" (List.all [2,3,4,5,7] fun Q =>
    2 * splitEqCensus Q == (Q - 1) * (Q - 2) && 2 * inertCensus Q == Q * (Q - 1))
  -- H.46: the ragged band count (t heights above 2N) and its h = 1 collapse
  chk "H.46 raggedBand_card" (List.all [(4,1),(6,2),(8,3),(9,3)] fun p =>
    ((slotOdd p.1 (2 * p.2 + 1)).filter (fun m => 2 * p.1 ≤ m)).card == p.2)
  chk "H.46 raggedBand_empty_of_h_one" (List.all [2,3,4,5,6] fun N =>
    ((slotOdd N 1).filter (fun m => 2 * N ≤ m)) == (∅ : Finset ℕ))
  -- H.62: the R2 counterexample — the two fibre cardinalities
  chk "H.62 fibre over (0,0) has 2 points"
    ((Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![0, 0])).card == 2)
  chk "H.62 fibre over (1,0) has 1 point"
    ((Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![1, 0])).card == 1)
  chk "H.62 codexToy is not surjective"
    ((Finset.univ.image codexToy).card < Fintype.card (Fin 2 → ZMod 4))
  -- H.74/H.75: σ DEGREES only (F1: σ values are noncomputable)
  chk "H.75 degree instances" ((stageSigma (genreE2 0) .ram).degree == 4
    && (stageSigma genreA2witness .ram).degree == 6
    && (stageSigma genreD2bwitness .ram).degree == 4)
  chk "H.74 stageSigma_degree at three data, three leaves"
    (List.all [genreE2 0, genreE2 3, genreA2witness, genreD2bwitness] fun G =>
      List.all [StageLeaf.ram, StageLeaf.twoSided, StageLeaf.inert] fun l =>
        (stageSigma G l).degree == 2 * G.keyDeg)
  chk "H.79 composedSigma_degree" (List.all [(1,1),(2,1),(1,2),(3,2)] fun p =>
    List.all [StageLeaf.ram, StageLeaf.twoSided, StageLeaf.inert] fun l =>
      (composedSigma (genreE2 1) p.1 p.2 l).degree == 2 * ((genreE2 1).keyDeg * (p.1 * p.2)))
  -- H.84, H.88, H.91, H.92: the remaining decidable spot values
  chk "H.84 w11 node shapes" (List.all [0,1,2,3] fun h =>
    (4 * h + 1, 2 * h + 1) == (2 * (2 * h) + 1, (2 * h) + 1))
  chk "H.88 capBranch 7 3 = twoSided" (capBranch 7 3 == CapBranch.twoSided)
  chk "H.88 capBranch trichotomy on a grid" (List.all [0,1,2,3,4,5,6,7,8] fun N =>
    List.all [0,1,2,3,4] fun w =>
      (capBranch N w == CapBranch.twoSided) == decide (2 * w < N)
      && (capBranch N w == CapBranch.ram) == decide (N ≤ 2 * w && N % 2 == 1)
      && (capBranch N w == CapBranch.und) == decide (N ≤ 2 * w && N % 2 == 0))
  chk "H.91 leafFactorE positive at q = 3, 4, 5" (List.all [3,4,5] fun q =>
    List.all [LeafE.ram, LeafE.twoSided, LeafE.splitEq, LeafE.inert, LeafE.splTail, LeafE.und]
      fun l => 0 < leafFactorE q l)
  chk "H.91 leafFactorE FAILS to be positive at q = 2 (the hypothesis 3 ≤ q is needed)"
    (leafFactorE 2 LeafE.splitEq == 0)
  chk "H.92 bracket_telescope_E at q = 2, 3" (List.all [2,3] fun q =>
    List.all [0,1,2,3,4] fun d => 1 + (List.range d).foldl (fun acc j => acc + (q - 1) * q ^ j) 0
      == q ^ d)
  IO.println "CHAP-H NUMERIC GATE: all checks PASS (q = 2 and q = 3 throughout)"


/-! ### THE ARITHMETIC GATE — every DECIDABLE ℕ/ℤ statement signed above, brute-forced

Beyond GC-11's numeric-audit requirement: the chapter's arithmetic layer is its bulk (§0.4) and its
statements are `ℕ`-subtraction/division-heavy, which is precisely the class the elaboration gate
CANNOT see (§15's own warning, and the reason G.23 was refuted by brute force rather than by the
gate). So every signed statement that is decidable over `ℕ`/`ℤ` — 66 of them, including all of
H.03/H.04/H.08/H.14/H.16/H.17/H.19/H.20/H.22/H.32–H.36/H.38–H.40/H.42–H.52/H.55/H.57/H.58/H.77/
H.79/H.82–H.86/H.89/H.90/H.92 — is checked here on a grid (witness data for the `GenreDatum`-indexed
ones). A failure throws, so this is a build-time gate.

**It found exactly one false statement: H.89 `band_not_consulted` (DEFECT D8).** Everything else in
the chapter's decidable arithmetic is true on the grid (79 `chk` lines below cover the 66
statements; several statements are checked in more than one regime).

**The ℝ-valued statements cannot be executed here** (`ℝ` is noncomputable), so they were swept
EXTERNALLY, in floating point, with the same intent: H.30 (`Q ≤ 7`, `c ≤ 4`, partial sums to 40),
H.31 (`Q ≤ 7`, partial sums to 60), H.63 and H.64 (200 000 random nonneg configurations each,
`|s| ≤ 5`), H.67/H.68 (all `Q ≤ 5`, `K ∈ {0, ½, 1, 3}`, `B ≤ 3`, `c, c₀ ≤ 8`, `D ≤ 6`, `M ≤ 8` at
the extremal `ρ`, `δ`), H.69 (`Q ≤ 4`, `K ≤ 2`, `B, c, c₀ ≤ 3`, `N ≤ 6`, `m, p, r ≤ 3`).
**Zero counterexamples**, and each also has a one-line hand derivation (H.66/H.67/H.68 are
`(D−1) + (M−c) = N−1−c` (H.34) plus monotonicity; H.30 is `(Q−1)/(Q^c − 1) ≤ 1`; H.31 is the
`2^{−1/2}`-ratio geometric bound; H.63/H.64 are the standard telescoping/monotone product bounds).
H.28 is implied by H.27, which IS executed below. -/

#eval show IO Unit from do
  let chk (name : String) (b : Bool) : IO Unit :=
    unless b do throw (IO.userError s!"ARITHMETIC GATE FAILURE: {name}")
  let R (n : ℕ) := List.range n
  -- H.03 / H.08 at the three witness data
  chk "H.03 four_le_sideLen" (List.all [genreE2 0, genreE2 2, genreA2witness, genreD2bwitness]
    fun G => 4 ≤ G.sideLen)
  chk "H.08 keyDeg_mul_h_lt_nodeHeight" (List.all [genreE2 0, genreE2 2, genreA2witness,
      genreD2bwitness] fun G => List.all (R G.μ) fun j => G.keyDeg * G.h < G.nodeHeight j)
  chk "H.08 nodeHeight_of_f_one" (List.all [genreE2 0, genreE2 2, genreA2witness] fun G =>
    List.all (R 4) fun j => G.nodeHeight j == (G.μ - j) * G.e₁ * G.h + 1)
  -- H.04
  chk "H.04 keyDeg_two_cases" (List.all (R 9) fun e => List.all (R 9) fun f =>
    !(e * f == 2) || ((e == 2 && f == 1) || (e == 1 && f == 2)))
  chk "H.04 sideLen_four_cases" (List.all (R 9) fun e => List.all (R 9) fun f =>
    List.all (R 9) fun m => !(2 ≤ m && 2 ≤ e * f && e * m * f == 4) ||
      ((e == 2 && f == 1 && m == 2) || (e == 1 && f == 2 && m == 2)))
  -- H.14, H.16, H.17
  chk "H.14 two_mul_clusterC" (List.all (R 13) fun m => 2 * clusterC m == m * (m - 1))
  chk "H.14 clusterC_eq_sum" (List.all (R 13) fun m =>
    clusterC m == (List.range m).foldl (· + ·) 0)
  chk "H.14 clusterC_succ_values" (clusterC 2 + 1 == 2 && clusterC 3 + 1 == 4
    && clusterC 4 + 1 == 7 && clusterC 5 + 1 == 11)
  chk "H.16 sum_alphaSlots" (List.all (R 7) fun m => List.all (R 7) fun W => List.all (R 7) fun k =>
    (List.range m).foldl (fun acc j => acc + (W + j * k)) 0 == alphaExp m W k)
  chk "H.16 two_mul_alphaExp_add" (List.all (R 7) fun m => List.all (R 7) fun W =>
    List.all (R 7) fun k => 2 * alphaExp m W k + k * (m * (m + 1)) == 2 * (m * (W + m * k)))
  chk "H.17 ghostSlots_eq" (List.all (R 7) fun m => List.all (R 7) fun k =>
    (List.range m).foldl (fun acc j => acc + j * k) 0 == k * clusterC m)
  chk "H.17 ghost_add_child" (List.all (R 7) fun m => List.all (R 7) fun W => List.all (R 7) fun k =>
    k * clusterC m + m * W == alphaExp m W k)
  -- H.19, H.20 (Q = 2..5, c = 1..3, mu = 1..4)
  chk "H.19 alphaBracket_succ" (List.all [2,3,4,5] fun Q => List.all [1,2,3] fun c =>
    List.all [1,2,3,4] fun m => alphaBracket Q c (m + 1) == Q ^ (c + 1) * alphaBracket Q c m)
  chk "H.20 alphaBracket_closed" (List.all [2,3,4,5] fun Q => List.all [1,2,3] fun c =>
    List.all [1,2,3,4] fun m => Q * alphaBracket Q c m == (Q - 1) * Q ^ ((c + 1) * m))
  chk "H.20 alphaBracket_eq" (List.all [2,3,4,5] fun Q => List.all [1,2,3] fun c =>
    List.all [1,2,3,4] fun m => alphaBracket Q c m == (Q - 1) * Q ^ ((c + 1) * m - 1))
  -- H.22
  chk "H.22 drain_codim" (List.all (R 7) fun d => List.all [1,2,3,4,5,6] fun m =>
    List.all (R 7) fun N => d * (m - 1) * (N - 1) + d * (N - 1) == d * m * (N - 1))
  chk "H.22 window_one_exponents" (List.all (R 7) fun d => List.all [1,2,3,4,5,6] fun m =>
    d * m * (1 - 1) == 0 && d * (m - 1) * (1 - 1) == 0
      && List.all [1,2,3,4,5,6,7,8] (fun k => !(m * k ≤ 0)))
  -- H.32, H.33, H.34, H.35, H.36
  chk "H.32 two_mul_supportLine_sum" (List.all (R 9) fun S => List.all (R 9) fun H =>
    2 * ((List.range S).foldl (fun acc r => acc + (r + 1) * H) 0) == S * (S + 1) * H)
  chk "H.33 two_mul_a_le_sideLen" (List.all (R 7) fun e => List.all (R 7) fun f =>
    List.all [2,3,4,5,6] fun m => 2 * (e * f) ≤ e * m * f)
  chk "H.33 two_mul_a_le_S" (List.all (R 7) fun e => List.all (R 7) fun f =>
    List.all [2,3,4,5,6] fun m => List.all (R 9) fun S =>
      !(e * m * f ≤ S) || 2 * (e * f) ≤ S)
  chk "H.34 exp_compose" (List.all [1,2,3,4,5,6,7,8] fun D => List.all (R 9) fun M =>
    List.all (R 9) fun c => !(c ≤ M && D + M ≤ 8) || ((D - 1) + (M - c) == (D + M) - 1 - c))
  chk "H.35 pow_sub_dominance" (List.all (R 8) fun N => List.all [1,2,3,4,5,6,7] fun m =>
    List.all [1,2,3,4] fun B => !(m ≤ N) || (N - m) ^ B + m * (N - m) ^ (B - 1) ≤ N ^ B)
  chk "H.36 entry_codim" (List.all (R 7) fun d => List.all [1,2,3,4,5,6] fun D =>
    List.all (R 9) fun N => !(D ≤ N) || d * (D - 1) + d * (N - D) == d * (N - 1))
  -- H.38, H.39, H.40, H.42, H.43
  chk "H.38 lawE_exp_honest" (List.all (R 14) fun N => List.all (R 14) fun h =>
    !(2 * h + 1 ≤ N) || 5 * h + 3 ≤ 4 * N)
  chk "H.38 lawE_floor_fails_at_two_one" (List.all [2,3,4,5] fun q =>
    !(2 * 1 + 1 ≤ 2) && lawE q 2 1 != 0)
  chk "H.39 lawE_exp_four_summands" (List.all (R 20) fun N => List.all (R 6) fun t =>
    !(4 * t + 3 ≤ N) || ((N - (t + 1)) + (N - 1 - (2 * t + 1)) + (N - (3 * t + 2))
      + (N - 1 - (4 * t + 2)) + (10 * t + 8) == 4 * N))
  chk "H.39 lawE_exp_odd" (List.all (R 20) fun N => List.all (R 6) fun t =>
    !(4 * t + 3 ≤ N) || (4 * N - 5 * (2 * t + 1) - 3 == 4 * N - (10 * t + 8)))
  chk "H.40 lawF_exp_honest" (List.all (R 20) fun N => List.all (R 6) fun k =>
    !(4 * k + 1 ≤ N) || 10 * k + 4 ≤ 4 * N)
  chk "H.42 headroom_exp_odd" (List.all (R 8) fun t => (5 * (2 * t + 1) + 1) / 2 == 5 * t + 3)
  chk "H.42 lawV1E2_eq_zero_iff" (List.all [2,3,4] fun q => List.all (R 12) fun N =>
    List.all (R 4) fun t => (lawV1E2 q N (2 * t + 1) == 0)
      == (decide (N ≤ 5 * t + 3) || (lawE q N (2 * t + 1) == 0)))
  chk "H.43 v4e2_vertex_condition" (List.all [1,2,3,4,5] fun v => List.all (R 8) fun t =>
    !(2 * v < 2 * t + 1) || 2 * v + 1 ≤ 2 * t + 1)
  chk "H.43 v4e2_first_visible" (List.all [1,2,3,4,5] fun v => List.all (R 8) fun t =>
    !(2 * v + 1 ≤ 2 * t + 1) || 7 ≤ v + 2 * (2 * t + 1))
  chk "H.43 v4e2_needs_eight" (List.all [1,2,3,4,5] fun v => List.all (R 8) fun t =>
    List.all (R 20) fun N => !(2 * v + 1 ≤ 2 * t + 1 && v + 2 * (2 * t + 1) ≤ N - 1) || 8 ≤ N)
  -- H.44, H.45
  chk "H.44 pinCensus_genreE/F" (List.all (R 8) fun q =>
    pinCensus q 1 == q - 1 && pinCensus q 2 == q ^ 2 - 1)
  chk "H.44 pinCensus_band_ne_interior" (List.all [2,3,4,5,6,7] fun q =>
    pinCensus q 1 != pinCensus q 2)
  chk "H.45 two_mul censuses" (List.all (R 10) fun Q =>
    2 * splitEqCensus Q == (Q - 1) * (Q - 2) && 2 * inertCensus Q == Q * (Q - 1))
  -- H.46
  chk "H.46 raggedBand_card" (List.all (R 6) fun t => List.all (R 16) fun N =>
    !(2 * t + 2 ≤ N) || ((slotOdd N (2 * t + 1)).filter (fun m => 2 * N ≤ m)).card == t)
  chk "H.46 raggedBand_empty_of_h_one" (List.all (R 16) fun N =>
    !(2 ≤ N) || (((slotOdd N 1).filter (fun m => 2 * N ≤ m)) == (∅ : Finset ℕ)))
  -- H.47, H.48
  chk "H.47 genh4B_aggregate_exp" (List.all (R 14) fun N => List.all (R 7) fun h =>
    !(2 * h + 1 ≤ N) || ((N + h - 1) + (N - 1 - 2 * h) == 2 * N - h - 2))
  chk "H.47 und_exp_coincide_iff_h_one" (List.all [1,2,3,4,5,6,7,8] fun N =>
    List.all (R 6) fun t =>
      (N + ((2 * t + 1) - 1) / 2 == N + (2 * t + 1) - 1) == (t == 0))
  chk "H.48 genh4B_F_odd_exp" (List.all (R 8) fun l => List.all [1,2,3,4,5] fun k =>
    2 * ((2 * l + 1) / 2) + 2 * k - 1 == (2 * l + 1) + 2 * k - 2)
  chk "H.48 genh4B_F_even_sum" (List.all [1,2,3,4,5] fun q => List.all (R 8) fun N =>
    List.all (R 5) fun k => (q ^ (N + 2 * k - 1) + (q - 1) * q ^ (N + 2 * k - 1)
      == q ^ (N + 2 * k)) || (N + 2 * k == 0))
  -- H.49, H.50
  chk "H.49 mixed_six_childE_lt_six" (List.all [1,2,3,4,5] fun k => List.all [1,2,3,4,5] fun h =>
    !(2 * k + 2 * h < 6) || (k == 1 && h == 1))
  chk "H.49 mixed_six_stage_steeper" (List.all [1,2,3,4,5] fun k => List.all (R 12) fun h =>
    !(2 * k + 1 ≤ h) || 8 ≤ 2 * k + 2 * h)
  chk "H.49 mixed_six_sameSide" (List.all [1,2,3,4,5,6] fun k => 6 ≤ 6 * k)
  chk "H.49 mixed_six_distinctSide" (List.all [1,2,3,4,5] fun k => List.all [1,2,3,4,5] fun h =>
    !(h != k) || 8 ≤ 2 * k + 4 * h)
  chk "H.50 tower_needs_eight" (List.all (R 7) fun e => List.all (R 7) fun f =>
    List.all (R 9) fun m => List.all (R 20) fun n =>
      !(2 ≤ e * f && 4 ≤ m && e * f * m ≤ n) || 8 ≤ n)
  chk "H.50 depth_three_needs_sixteen" (List.all [2,3,4] fun D => List.all (R 20) fun m1 =>
    List.all (R 5) fun e2 => List.all (R 5) fun f2 => List.all (R 9) fun m2 =>
      List.all (R 40) fun n =>
        !(2 ≤ e2 * f2 && 4 ≤ m2 && e2 * f2 * m2 ≤ m1 && D * m1 ≤ n) || 16 ≤ n)
  -- H.51, H.52
  chk "H.51 class_sep" (List.all [1,2,3,4,5,6,7] fun e => List.all (R 10) fun h =>
    !(Nat.gcd h e == 1) || (List.all (R e) fun i => List.all (R e) fun i' =>
      !(i * h % e == i' * h % e) || i == i'))
  chk "H.52 slot_height_injective" (List.all [1,2,3,4,5] fun e => List.all (R 8) fun h =>
    !(Nat.gcd h e == 1) || (List.all (R e) fun i => List.all (R e) fun i' =>
      List.all (R 6) fun v => List.all (R 6) fun v' =>
        !(e * v + i * h == e * v' + i' * h) || (i == i' && v == v')))
  -- H.55 at the witness data
  chk "H.55 stageLift_index_lt" (List.all [genreE2 0, genreE2 2, genreA2witness, genreD2bwitness]
    fun G => List.all (R G.e₁) fun i => List.all (R G.f₁) fun s => i + G.e₁ * s < G.keyDeg)
  chk "H.55 stageLift_integral" (List.all [genreE2 0, genreE2 2, genreA2witness, genreD2bwitness]
    fun G => List.all (R G.e₁) fun i => List.all (R G.f₁) fun s => List.all (R 12) fun a =>
      !(G.keyDeg * G.h < i * G.h + G.e₁ * a) || s * G.h ≤ a)
  chk "H.55 stageLift_height" (List.all [genreE2 0, genreE2 2, genreA2witness, genreD2bwitness]
    fun G => List.all (R G.e₁) fun i => List.all (R G.f₁) fun s => List.all (R 12) fun a =>
      !(G.keyDeg * G.h < i * G.h + G.e₁ * a)
        || G.e₁ * (a - s * G.h) + (i + G.e₁ * s) * G.h == i * G.h + G.e₁ * a)
  -- H.57, H.58
  chk "H.57 wrap_div_mod" (List.all (R 8) fun r => List.all (R 8) fun i =>
    List.all [1,2,3,4,5,6] fun e => r * i == r * i % e + e * (r * i / e) && r * i % e < e)
  chk "H.57 wrap_height" (List.all (R 6) fun r => List.all (R 6) fun i => List.all (R 6) fun a =>
    List.all (R 6) fun h => List.all [1,2,3,4,5] fun e =>
      r * (i * h + e * a) == (r * i % e) * h + e * (r * a + (r * i / e) * h))
  chk "H.58 card_composedBasis" (List.all [1,2,3,4] fun D => List.all (R 5) fun r =>
    (Finset.range D ×ˢ Finset.range r).card == D * r)
  -- H.77
  chk "H.77 gcd_odd_of_odd" (List.all (R 9) fun j => List.all (R 16) fun e =>
    (Nat.gcd (2 * j + 1) e) % 2 == 1)
  chk "H.77 lcm_ram_value_group" (List.all [1,2,3,4,5,6,7,8] fun e => List.all (R 9) fun j =>
    Nat.lcm e (2 * e / Nat.gcd (2 * j + 1) e) == 2 * e)
  -- H.79 at the witnesses
  chk "H.79 composedDeg_eq" (List.all [genreE2 0, genreA2witness, genreD2bwitness] fun G =>
    List.all (R 5) fun e2 => List.all (R 5) fun f2 =>
      G.keyDeg * (e2 * f2) == (G.e₁ * e2) * (G.f₁ * f2))
  -- H.82, H.83, H.84
  chk "H.82 quartic_floors_E" (List.all (R 9) fun t =>
    (2 * t + 1 + 1) / 2 == t + 1 && (2 * t + 1) + 1 == 2 * t + 2
      && (3 * (2 * t + 1) + 1) / 2 == 3 * t + 2 && 2 * (2 * t + 1) + 1 == 4 * t + 3)
  chk "H.82 quartic_node_E" (List.all (R 9) fun t =>
    min (2 * (t + 1) + (2 * t + 1)) (2 * (2 * t + 2)) == 2 * (2 * t + 1) + 1
      && min (2 * (3 * t + 2) + (2 * t + 1)) (2 * (4 * t + 3)) == 4 * (2 * t + 1) + 1)
  chk "H.83 quartic_total_F" (List.all (R 22) fun N => List.all (R 6) fun k =>
    !(4 * k + 1 ≤ N) || ((N - k - 1) + (N - 2 * k - 1) + (N - 3 * k - 1) + (N - 4 * k - 1)
      + (10 * k + 4) == 4 * N))
  chk "H.83 quartic_node_F" (List.all (R 9) fun k =>
    min ((k + 1) + k) (2 * k + 1) == 2 * k + 1 && min ((3 * k + 1) + k) (4 * k + 1) == 4 * k + 1)
  chk "H.84 w11_node_E/F" (List.all (R 9) fun h =>
    (4 * h + 1, 2 * h + 1) == (2 * (2 * h) + 1, (2 * h) + 1))
  -- H.85, H.86
  chk "H.85 dv_parity_ne" (List.all (R 6) fun j => List.all (R 8) fun va => List.all (R 8) fun vb =>
    2 * va + (2 * j + 1) != 2 * vb)
  chk "H.85 dv_parity_min_unique" (List.all (R 6) fun j => List.all (R 8) fun va =>
    List.all (R 8) fun vb =>
      (min (2 * va + (2 * j + 1)) (2 * vb) == 2 * va + (2 * j + 1))
        || (min (2 * va + (2 * j + 1)) (2 * vb) == 2 * vb))
  chk "H.86 carry_height_gt" (List.all [1,2,3,4,5] fun h => List.all (R 16) fun dm =>
    List.all (R 8) fun va => !(2 * h + 1 ≤ dm && h + 1 ≤ 2 * va)
      || dm < min (2 * (dm - h)) (2 * va + (dm - h)))
  -- H.89 (the four consulted-height bounds)
  chk "H.89 consulted_ram" (List.all [1,2,3,4,5] fun h => List.all (R 16) fun u =>
    List.all (R 9) fun N => !(1 ≤ N && u ≤ 2 * N - 1) || (u - h) / 2 ≤ N - 1)
  chk "H.89 consulted_twoSided" (List.all (R 16) fun w => List.all (R 9) fun N =>
    !(w ≤ 2 * N - 2) || w / 2 ≤ N - 1)
  chk "H.89 consulted_refine" (List.all (R 16) fun dm => List.all (R 9) fun N =>
    !(2 * dm ≤ 2 * N - 2) || dm ≤ N - 1)
  -- H.89 `band_not_consulted` IS REFUTED AS SIGNED (DEFECT D8): at `(N, m) = (0, 0)` the
  -- antecedent `2 * N ≤ m` holds and the conclusion `¬ (m ≤ 2 * N - 1)` is FALSE, because
  -- `2 * 0 - 1 = 0` in ℕ. The axiom is WITHDRAWN (commented out at H.89 below, the G.23a
  -- precedent). Checked here in the REPAIRED form, with BOTH candidate guards, so the blueprint
  -- can pick either: `1 ≤ N` (matches the sibling lemmas of H.89) or `1 ≤ m`.
  -- [0e RETIREMENT, 2026-08-15] The blueprint picked `1 ≤ N` (A-H.1/D8) and the fleet landed it, so
  -- the node is now RETIRED at that amended type (finding R2). The two checks below are kept as the
  -- record of how the choice was validated; the third records the original refutation.
  chk "H.89 band_not_consulted, REPAIRED with 1 ≤ N" (List.all (R 40) fun m =>
    List.all (R 20) fun N => !(1 ≤ N && 2 * N ≤ m) || !(m ≤ 2 * N - 1))
  chk "H.89 band_not_consulted, REPAIRED with 1 ≤ m" (List.all (R 40) fun m =>
    List.all (R 20) fun N => !(1 ≤ m && 2 * N ≤ m) || !(m ≤ 2 * N - 1))
  chk "H.89 band_not_consulted, REFUTED as signed: (N,m) = (0,0) is a counterexample"
    (2 * 0 ≤ 0 && 0 ≤ 2 * 0 - 1)
  -- H.90
  chk "H.90 invariant_even" (List.all (R 8) fun h => List.all (R 20) fun dm =>
    !(2 * h + 2 ≤ dm) || h + 1 ≤ dm / 2)
  chk "H.90 invariant_odd" (List.all (R 8) fun h => List.all (R 20) fun dm =>
    !(2 * h + 1 ≤ dm) || (h + 1) / 2 ≤ (dm - h) / 2)
  -- H.92
  chk "H.92 subset_sum_pow" (List.all [1,2,3,4] fun L => List.all (R 5) fun d =>
    (Finset.range d).powerset.sum (fun H => L ^ H.card) == (1 + L) ^ d)
  chk "H.92 macroscopic_rate" (List.all [2,3] fun q => List.all (R 4) fun D =>
    List.all (R 4) fun m => q ^ (2 * (D * m)) == (q ^ 2) ^ (D * m))
  -- H.11 / H.12 (bounded Occupied searches)
  chk "H.11 not_occupied_genreA2witness (bounded i<3, a<=8)"
    (List.all (R 3) fun i => List.all (R 9) fun a => i * 2 + 3 * a != 1)
  chk "H.12 occupied_zero_genreD2bwitness" (0 * 1 + 1 * 0 == 0)
  IO.println "CHAP-H ARITHMETIC GATE: 66 signed ℕ/ℤ statements brute-forced on a grid — all PASS (H.89 band_not_consulted excluded as REFUTED, D8)"

/-! ### THE H.72 REFUTATION, MACHINE-CHECKED — and the `StageInterface` witness F2 asked for

Two artifacts the blueprint did not have. `stageIfaceE` is a genuine `StageInterface` instance (F2:
no chapter node exhibits one, though §3's design note claimed two), at genre E with `stageLoss = 0` —
the `EFF.GENIND.199` exemption the design note names. Instantiating H.72's signed inequality at it
gives `4 ≥ 8`, so H.72 is FALSE as signed (DEFECT D4) and is withdrawn above rather than signed.

**R3 IS CLOSED, 2026-08-15 — the witness IS LANDED and this file's copy is RETIRED.** `stageIfaceE`
was this file's one deliberate residue: built here, in a file `leanfinal` never imports, so
`leanfinal`'s `StageInterface` consumers (H.72) were still theorems about a possibly-empty type. It
has been ported to `leanfinal/Uniformity/ChapH/H09w.lean` (the H.09 witness file, **not** a blueprint
node) as `Uniformity.Density.Induction.stageIfaceE` — verbatim, proof terms included — together with
the genre-F witness §16 TODO item 14 owed (`stageIfaceF`, over `genreD2bwitness`). So the local `def`
is deleted; the name below now resolves through the header's `open Uniformity.Density.Induction` to
the LANDED declaration, which means every `decide` in the refutation and sweep material that follows
runs on the landed fields. THAT resolution is the diff. Retirement form per this file's `def`
protocol: the type, then the body field by field.

The landed witness's genre E datum is `(Q,e₁,f₁,μ,h) = (2,2,1,2,1)` at window `N = 2`, entry height
`H = 0`, side length `S = 4`, `stageLoss = 0` — the same eleven fields this file proved. -/

-- 0e RETIREMENT (def; landed 2026-08-15 as `Uniformity.Density.Induction.stageIfaceE` in
-- `leanfinal/Uniformity/ChapH/H09w.lean`). Type first, then every field of the body by `rfl`.
example : StageInterface (genreE2 0) 2 0 4 := stageIfaceE
example : stageIfaceE.stageWindow = 2 := rfl
example : stageIfaceE.stageLoss = 0 := rfl
example : stageIfaceE.entryCodim = 0 := rfl
example : stageIfaceE.slack = 0 := rfl
example : stageIfaceE.bracket = fun κ => 2 ^ (2 * κ - 1) := rfl
example : stageIfaceE.drainFrac = fun _ => (0 : ℝ) := rfl
example : stageIfaceE.stageSigma = stageSigma (genreE2 0) .ram := rfl

/-- **H.72 `rate_lossPriced` IS FALSE.** Its conclusion, instantiated at `stageIfaceE`, is `4 ≥ 8`.
Had the axiom been signed, `rate_lossPriced stageIfaceE` would have proved `False` and every
`example` in this file would have become vacuous — which is why it is withdrawn, not signed. -/
example : ¬ (2 * ((genreE2 0).f₁ * stageIfaceE.stageWindow) + 2 * ((4 + 1) * 0)
      + 2 * (2 * stageIfaceE.entryCodim)
    ≥ 2 * (2 * (genreE2 0).keyDeg * (2 - 1 - 0)) + 2 * (2 * (genreE2 0).keyDeg * 0) + 0
      - 2 * (2 * stageIfaceE.slack)) := by decide

/-- The candidate repair (D4's CANDIDATE A) at the same witness: `4 ≥ 4`. -/
example : 2 * ((genreE2 0).f₁ * stageIfaceE.stageWindow) + (4 + 1) * 0
      + 2 * stageIfaceE.entryCodim + 2 * stageIfaceE.slack
    ≥ 2 * (genreE2 0).keyDeg * (2 - 1 - 0) + 2 * (genreE2 0).keyDeg * 0 + 0 := by decide

/-! The same two facts as a SWEEP over the `StageInterface` field data, so the refutation is not a
one-point accident and the repair is not a one-point coincidence. `hS`/`hwin`/`hprice` are imposed
as filters exactly as the structure imposes them (`(S - 2·keyDeg)` truncated, as written). -/
#eval show IO Unit from do
  let chk (name : String) (b : Bool) : IO Unit :=
    unless b do throw (IO.userError s!"H.72 SWEEP FAILURE: {name}")
  -- (Q, e₁, f₁, μ, h) tuples: genre E (two slopes), the A2 witness, the D2b witness, a q = 3 datum
  let data : List (ℕ × ℕ × ℕ × ℕ) := [(2,1,2,1), (2,1,2,3), (3,1,2,2), (1,2,2,1), (2,2,2,1)]
  let mutBad := data.any fun (e₁, f₁, μ, _h) =>
    let keyDeg := e₁ * f₁
    let sideLen := e₁ * μ * f₁
    (List.range 7).any fun N => (List.range 5).any fun H =>
      (List.range 4).any fun dS => (List.range 6).any fun win =>
        (List.range 6).any fun loss => (List.range 5).any fun ec =>
          (List.range 5).any fun sl =>
            let S := sideLen + dS
            (e₁ * (N - 1 - H) ≤ win + loss) &&
            (2 * (f₁ * loss) ≤ 2 * ec + (S - 2 * keyDeg) * H + 2 * sl) &&
            !(2 * (f₁ * win) + 2 * ((S + 1) * H) + 2 * (2 * ec)
                ≥ 2 * (2 * keyDeg * (N - 1 - H)) + 2 * (2 * keyDeg * H) + H - 2 * (2 * sl))
  chk "H.72 AS SIGNED is refuted somewhere in the sweep (expected: true)" mutBad
  let repairOk := data.all fun (e₁, f₁, μ, _h) =>
    let keyDeg := e₁ * f₁
    let sideLen := e₁ * μ * f₁
    (List.range 7).all fun N => (List.range 5).all fun H =>
      (List.range 4).all fun dS => (List.range 6).all fun win =>
        (List.range 6).all fun loss => (List.range 5).all fun ec =>
          (List.range 5).all fun sl =>
            let S := sideLen + dS
            !((e₁ * (N - 1 - H) ≤ win + loss) &&
              (2 * (f₁ * loss) ≤ 2 * ec + (S - 2 * keyDeg) * H + 2 * sl)) ||
            (2 * (f₁ * win) + (S + 1) * H + 2 * ec + 2 * sl
              ≥ 2 * keyDeg * (N - 1 - H) + 2 * keyDeg * H + H)
  chk "H.72 CANDIDATE A holds on the whole sweep" repairOk
  IO.println "CHAP-H H.72 SWEEP: signed form REFUTED, candidate repair HOLDS"

/-! H.99(iii): non-vacuity of the schema layer — the three witness data elaborate. -/
#check (genreE2 0 : GenreDatum)
#check (genreA2witness : GenreDatum)
#check (genreD2bwitness : GenreDatum)
#check (fun t => genreE2 t : ℕ → GenreDatum)

end NumericGate

/-! ## RESUME COMMENT (storm discipline)

**Status at this line: chapter H's leanspec interface is RETIRED (0e closing pass, 2026-08-15;
amended the same day when R3 closed).** All 190 signable declarations are landed in `leanfinal`
(H.01 … H.98; H.99 is the census block) and diffed here — plus `stageIfaceE`, the one
non-blueprint declaration, so **191 retired / 261 retirement `example`s**, zero `axiom`s, zero
`sorry`s, zero local definitions, `autoImplicit` off, three executed gate blocks green (and the
numeric gates now run on the LANDED bodies, including the landed `stageIfaceE`'s fields). Nothing is
outstanding IN THIS FILE. Findings R1–R5 are in the RETIREMENT CENSUS in the header; the
pre-retirement gate record (defect list D1–D8, findings F1/F2, O1) is kept below it verbatim and
reads in the past tense.

Disposition of the gate's own list, as of retirement:

* **CLOSED by blueprint amendment + landing.** D4 (H.72 → CANDIDATE A, A-H.1/D4), D8 (H.89 → the
  `1 ≤ N` guard, A-H.1/D8), D7 (H.71 `hdesc` → guarded, A-H.1/D7, with A-H.2's window and `hmc`),
  D5 (H.94 `A1Cell.deltaSubst` → the stub-side determination confirmed field by field, R4).
* **CLOSED mechanically on the landed side, still worth fixing in the blueprint text.** D1 (H.23's
  `if` → `if h :` plus `decreasing_by`), D2 (H.18's `decreasing_by`), D3 (H.06's mathlib name), D6
  (H.71's multi-name fields), O1 (order `H.13` before `H.09`).
* **CLOSED by a landing, after the retirement pass.** **F2 (R3)** — the landed corpus exhibited no
  `StageInterface` inhabitant at all; now it exhibits two,
  `leanfinal/Uniformity/ChapH/H09w.lean`'s `stageIfaceE` (genre E, ported verbatim from this file)
  and `stageIfaceF` (genre F over `genreD2bwitness`, the `f₁ = 2` datum §16 TODO item 14 named). H.72
  is a theorem about a non-empty type, §3's repaired design note is true for the first time, and this
  file's copy of the witness is retired against the landed one. Teeth are unchanged: `(CS-1Q)`/`(CS-3)`
  still have none anywhere and `HYP.36` stays CARRY.
* **STILL OPEN.** F1 (σ VALUES are not machine-checkable at any gate — `degree` only; unchanged, it
  is a property of the landed `DecidableEq FactorizationType`). -/

end LeanspecH

/-!
# §17 — THE T-1 COMPLETION LAYER (nodes H.100–H.124): SIGNATURE-ELABORATION SCRATCH

(unit T-1 BLUEPRINT-CONVERSION, 2026-08-16; provenance: OM-2,
`docs/openmath-campaign/OM-2_genind-b_2026-08-16.md` §4, under owner mandate #66's queue.)

**Lifecycle position (the file header's lifecycle governs).** The `LeanspecH` block above is
RETIRED (H.01–H.99 landed). THIS block is the opposite end of the lifecycle: the **pre-0e
SIGNATURE-ELABORATION scratch** for the NEW §17 nodes of
`blueprint/CHAP-H_general_induction.md` (H.100–H.124, dated extension 2026-08-16). Its only
claim: **every §17 SIGNATURE elaborates against the landed `Uniformity` API.** It is NOT the
§17 0e gate: theorem stubs are unsigned `axiom`s awaiting the fleet stage. As committed by T-1,
TWO definitional carriers (`alphaChild`, `betaChild` — the heavy extraction bodies) were
carried in axiom form as OPAQUE CONSTANTS so their consumers' signatures elaborate, with real
bodies owed at the §17 0e gate (recorded deviation from 0e rule 1). **UPDATED by AMENDMENT
A-H.5 (2026-08-16): both carriers now have REAL, CENTRE-PINNED BODIES and the deviation is
CLOSED.** A-H.5 also adds the canonical lift pair (`resSect`, `classSect`, `recFrame`,
`divPow`, with `residue_resSect` / `proj_classSect` / `divPow_spec` PROVED) and re-signs the two
clause-(i) stubs, whose committed ∀-lift-pair form was refuted by explicit `ℤ₅` witnesses
(`verification/openmath/OM2_h115_h116_centre_shift_refutation.py`, exit 0 = refuted). Every
definitional carrier in this block is now a REAL body; ZERO opaque constants remain.

**Namespace discipline (PA-4 / GC-6.6):** flat inside `LeanspecH17`; the landed-side
assignment (recorded per node in the blueprint §17) is `Uniformity.Density.Induction` for the
new defs and the theorems about them, `Uniformity.Density` for `FullClusterRateBound` /
`inductionPackage_of_clusterRates` (consumers of the landed `InductionPackage`).

**Binder discipline:** every declaration binds INLINE — the B.42 landing rule
(`leanfinal/Uniformity/ChapB/B42.lean`, "The completeness binder"): a hypothesis a statement's
truth depends on is never left to section auto-inclusion.
-/

namespace LeanspecH17

open Uniformity Uniformity.Density Uniformity.Density.Induction Uniformity.Density.Leaf
open IsLocalRing Polynomial

/-! ### H.100 — the level-0 stratum -/

/-- **H.100 (def half).** The level-0 stratum of a residue polynomial `g`: the level-`N`
classes ALL of whose monic lifts reduce to `g`. (∀-lift form; the ∃-lift transport is the
lemma half.) -/
def levelZeroStratum (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n N : ℕ) (g : Polynomial (ResidueField O)) : Set (Coeff O n N) :=
  {c | ∀ a : Fin n → O, proj O n N a = c → (monicPoly a).map (residue O) = g}

/-- **H.100 (lemma half).** At `1 ≤ N` the reduction is class-determined, so the ∀-lift and
∃-lift readings agree. -/
axiom mem_levelZeroStratum_iff {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {n N : ℕ} (hN : 1 ≤ N)
    (g : Polynomial (ResidueField O)) (c : Coeff O n N) :
    c ∈ levelZeroStratum O n N g ↔
      ∃ a : Fin n → O, proj O n N a = c ∧ (monicPoly a).map (residue O) = g

/-! ### H.101 — class multiplication -/

/-- **H.101 (def half).** The product of two monic coefficient classes, computed entirely in
`(Res O N)[X]` — no lift is consulted. -/
noncomputable def mulClass {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n₁ n₂ N : ℕ} (c₁ : Coeff O n₁ N) (c₂ : Coeff O n₂ N) : Coeff O (n₁ + n₂) N :=
  fun i =>
    ((X ^ n₁ + ∑ j : Fin n₁, Polynomial.C (c₁ j) * X ^ (j : ℕ)) *
      (X ^ n₂ + ∑ j : Fin n₂, Polynomial.C (c₂ j) * X ^ (j : ℕ))).coeff (i : ℕ)

/-- **H.101 (lemma half).** `mulClass` computes the class of a product of monic lifts. -/
axiom mulClass_proj {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n₁ n₂ N : ℕ} (a₁ : Fin n₁ → O) (a₂ : Fin n₂ → O) :
    proj O (n₁ + n₂) N (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))
      = mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)

/-! ### H.102 — the Hensel class bijection (N-1a) -/

/-- **H.102 (bijection).** Binary Hensel class transport: over coprime monic residue factors,
`mulClass` is a bijection of the product of the factor strata onto the product stratum — with
NO precision loss (the level-0 resultants are units). -/
axiom bijOn_mulClass {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂) :
    Set.BijOn (fun p : Coeff O n₁ N × Coeff O n₂ N => mulClass p.1 p.2)
      ((levelZeroStratum O n₁ N g₁) ×ˢ (levelZeroStratum O n₂ N g₂))
      (levelZeroStratum O (n₁ + n₂) N (g₁ * g₂))

/-- **H.102 (count corollary).** -/
axiom card_levelZeroStratum_mul {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂) :
    Nat.card (levelZeroStratum O (n₁ + n₂) N (g₁ * g₂))
      = Nat.card (levelZeroStratum O n₁ N g₁) * Nat.card (levelZeroStratum O n₂ N g₂)

/-! ### H.103 — σ-additive decidedness assembly (⟸ direction) -/

/-- **H.103.** Decided factors assemble: the product class is decided at the multiset sum.
(The per-type ⟹ direction is REFUTED — finding F-1's `split⊎inert = inert⊎split` collision —
so no iff is stated at the σ level; the predicate-level iff is H.104.) -/
axiom decidedAt_mulClass {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂)
    {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    (hc₁ : c₁ ∈ levelZeroStratum O n₁ N g₁) (hc₂ : c₂ ∈ levelZeroStratum O n₂ N g₂)
    {σ₁ σ₂ : FactorizationType}
    (h₁ : DecidedAt O n₁ σ₁ N c₁) (h₂ : DecidedAt O n₂ σ₂ N c₂) :
    DecidedAt O (n₁ + n₂) ⟨σ₁.data + σ₂.data⟩ N (mulClass c₁ c₂)

/-! ### H.104 — the drain/decidedness composition on the PREDICATE (N-1b) -/

/-- **H.104.** The predicate-level composition: the product class is undecided iff SOME factor
class is (multiset cancellation + the H.102 bijection). -/
axiom undecidedAt_mulClass_iff {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂)
    {c₁ : Coeff O n₁ N} {c₂ : Coeff O n₂ N}
    (hc₁ : c₁ ∈ levelZeroStratum O n₁ N g₁) (hc₂ : c₂ ∈ levelZeroStratum O n₂ N g₂) :
    UndecidedAt O (n₁ + n₂) N (mulClass c₁ c₂)
      ↔ UndecidedAt O n₁ N c₁ ∨ UndecidedAt O n₂ N c₂

/-! ### H.105 — the per-stratum undecided count (N-1c, per-stratum binary form) -/

/-- **H.105.** The exact per-stratum composed count `T₁T₂ − (T₁−u₁)(T₂−u₂)`, written
subtraction-safely with decided-within-stratum complements. -/
axiom card_undecided_mulClass {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {n₁ n₂ N : ℕ} (hN : 1 ≤ N)
    {g₁ g₂ : Polynomial (ResidueField O)} (hg₁ : g₁.Monic) (hg₂ : g₂.Monic)
    (hd₁ : g₁.natDegree = n₁) (hd₂ : g₂.natDegree = n₂) (hcop : IsCoprime g₁ g₂) :
    Nat.card
        ((undecidedSet O (n₁ + n₂) N ∩ levelZeroStratum O (n₁ + n₂) N (g₁ * g₂) :
          Set (Coeff O (n₁ + n₂) N)))
      = Nat.card (levelZeroStratum O n₁ N g₁) * Nat.card (levelZeroStratum O n₂ N g₂)
        - Nat.card ((levelZeroStratum O n₁ N g₁ \ undecidedSet O n₁ N : Set (Coeff O n₁ N)))
          * Nat.card ((levelZeroStratum O n₂ N g₂ \ undecidedSet O n₂ N : Set (Coeff O n₂ N)))

end LeanspecH17

namespace LeanspecH17

open Uniformity Uniformity.Density Uniformity.Density.Induction Uniformity.Density.Leaf
open IsLocalRing Polynomial

/-! ### H.106 — the cluster-state carrier -/

/-- **H.106 (def half).** The `(m, d = 1, N)` cluster system: level-`N` classes with every
coefficient residually zero (the recentred `Φ`-adic development, `Φ = X`). -/
def ClusterState (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m N : ℕ) : Type _ :=
  {c : Coeff O m N //
    ∀ i, c i ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))}

/-- **H.106 (lemma half).** The state-space census `Q^{m(N−1)}` (`EFF.GENIND.07`). -/
axiom card_clusterState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (m N : ℕ) (hN : 1 ≤ N) :
    Nat.card (ClusterState O m N) = residueCard O ^ (m * (N - 1))

/-! ### H.107 — the windowed valuation on `Res O N` -/

/-- **H.107 (def half).** The windowed (conservative) valuation of a truncated element:
the largest `k ≤ N` with `x` in the image of `𝔪^k`. `resOrd x = N` means INVISIBLE
(`x = 0` in the window), never "valuation `= N`". -/
noncomputable def resOrd {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N : ℕ} (x : Res O N) : ℕ :=
  sSup {k | k ≤ N ∧ x ∈ ((maximalIdeal O) ^ k).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N))}

/-- **H.107 (lemma half, clause i).** Representative transport: for `k ≤ N`,
`k ≤ resOrd (mk a) ↔ π^k ∣ a`. -/
axiom resOrd_ge_iff {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {N k : ℕ} (hk : k ≤ N) (a : O) :
    k ≤ resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) a) ↔ π ^ k ∣ a

/-- **H.107 (lemma half, clause ii).** Invisibility: `resOrd x = N ↔ x = 0`. -/
axiom resOrd_eq_iff {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {N : ℕ} (x : Res O N) : resOrd x = N ↔ x = 0

/-! ### H.108 — the drain predicate and the capped content -/

/-- **H.108 (def half, a).** DRAIN: the constant coefficient is invisible — the conservative
reader exits UNDECIDED (S-1: it decides on visible data only). -/
def IsDrainState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m N : ℕ} (c : ClusterState O m N) : Prop :=
  ∀ h : 0 < m, c.1 ⟨0, h⟩ = 0

/-- **H.108 (def half, b).** The CAPPED slope-`k` content
`D = min_j (min(v(a_j), N) + j·k)` (`GENIND-3`'s terminal `[r3]`-capped display,
`EFF.GENIND.24`), computed on the class — no lift consulted. -/
noncomputable def betaContent {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {m N : ℕ} (c : ClusterState O m N) (k : ℕ) : ℕ :=
  Finset.inf' (Finset.range (m + 1)) (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m))
    (fun j => if h : j < m then resOrd (c.1 ⟨j, h⟩) + j * k else m * k)

/-- **H.108 (lemma half).** On non-drain states the content sits below the window:
`D ≤ N − 1` (hence every extracted child window `N − D` is `≥ 1`). -/
axiom betaContent_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) (c : ClusterState O m N)
    (h0 : ¬ IsDrainState c) (k : ℕ) : betaContent c k ≤ N - 1

/-! ### H.109 — the child events -/

/-- **H.109 (def half).** `HasChildAt π c μ k z`: the slope-`k` residual has the NONZERO root
`z` with multiplicity `μ ≥ 2` — stated conservatively (∀-lift) through the recentring
`x ↦ π^k(y + ẑ)` and π-divisibility of the recentred coefficients at the capped content. -/
def HasChildAt {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) (μ k : ℕ) (z : ResidueField O) : Prop :=
  2 ≤ μ ∧ 1 ≤ k ∧ z ≠ 0 ∧
    ∀ (a : Fin m → O) (w : O), proj O m N a = c.1 → residue O w = z →
      (∀ j, π ^ betaContent c k ∣
        ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff j) ∧
      (∀ j < μ, π ^ (betaContent c k + 1) ∣
        ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff j) ∧
      ¬ π ^ (betaContent c k + 1) ∣
        ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff μ

/-- **H.109 (lemma half).** Conservativity/lift-independence: on non-drain states with
`1 ≤ N`, the ∀-lift clauses hold as soon as they hold at ONE lift pair (every threshold is
`≤ N`, so every consulted digit is class-determined). -/
axiom hasChildAt_of_exists {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hN : 1 ≤ N)
    {c : ClusterState O m N} (h0 : ¬ IsDrainState c) {μ k : ℕ} {z : ResidueField O}
    (hμ : 2 ≤ μ) (hk : 1 ≤ k) (hz : z ≠ 0)
    (a : Fin m → O) (w : O) (ha : proj O m N a = c.1) (hw : residue O w = z)
    (h1 : ∀ j, π ^ betaContent c k ∣
      ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff j)
    (h2 : ∀ j < μ, π ^ (betaContent c k + 1) ∣
      ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff j)
    (h3 : ¬ π ^ (betaContent c k + 1) ∣
      ((monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C w))).coeff μ) :
    HasChildAt π c μ k z

/-! ### H.110 — the composite-stage (CS) bucket -/

/-- **H.110 (def half).** CS: some side of the visible polygon carries a repeated irreducible
residual factor `ψ` with block size `ℓ·deg ψ ≥ 2` — the conservative reader exits UNDECIDED
at depth 0 (the pessimistic reading; DECISION D-H17.1: stage data is HYP-gated, never read
here). ∀-lift form; `H₀` pinned at `sideMin` per GC-1. -/
def IsCSState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) : Prop :=
  ¬ IsDrainState c ∧
    ∀ (a : Fin m → O), proj O m N a = c.1 →
      ∃ (u ℓ : ℕ) (hne : (sideSet X (monicPoly a) u ℓ).Nonempty) (H₀ : ℕ),
        0 < ℓ ∧ Nat.Coprime u ℓ ∧
        npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hne) = (H₀ : ℕ∞) ∧
        ∃ ψ : Polynomial (resField (X : Polynomial O)),
          Irreducible ψ ∧ 2 ≤ ℓ * ψ.natDegree ∧
          ψ ^ 2 ∣ resPoly π X (monicPoly a) u ℓ hne H₀

/-! ### H.111 — the five-case partition (N-2a's shell) -/

/-- **H.111 (def a).** α: a FULL-multiplicity child (`μ = m`) at integer slope `k` — the
whole cluster recenters. -/
def IsAlphaState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) (k : ℕ) (z : ResidueField O) : Prop :=
  ¬ IsDrainState c ∧ ¬ IsCSState π c ∧ HasChildAt π c m k z

/-- **H.111 (def b).** β: fracture — a child exists but no full-multiplicity child. -/
def IsBetaState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) : Prop :=
  ¬ IsDrainState c ∧ ¬ IsCSState π c ∧
    (∃ μ k z, HasChildAt π c μ k z) ∧ ¬ ∃ k z, HasChildAt π c m k z

/-- **H.111 (def c).** DEC: no drain, no CS, no child — every residual factor is simple and
the conservative reader DECIDES (the pieces' `(e,f)` read is chapter B's leaf layer). -/
def IsDecState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) : Prop :=
  ¬ IsDrainState c ∧ ¬ IsCSState π c ∧ ¬ ∃ μ k z, HasChildAt π c μ k z

/-- **H.111 (lemma half, totality).** Every state is drain, CS, α, β or DEC. -/
axiom cluster_partition {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) :
    IsDrainState c ∨ IsCSState π c ∨ (∃ k z, IsAlphaState π c k z) ∨
      IsBetaState π c ∨ IsDecState π c

/-- **H.111 (lemma half, the one non-definitional disjointness).** -/
axiom alpha_not_beta {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} {m N : ℕ} {c : ClusterState O m N} {k : ℕ} {z : ResidueField O} :
    IsAlphaState π c k z → ¬ IsBetaState π c

/-! ### H.112 — event well-formedness (window, uniqueness, finiteness) -/

/-- **H.112 (clause i).** The α event is unique. -/
axiom alpha_event_unique {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 2 ≤ m) {c : ClusterState O m N}
    {k k' : ℕ} {z z' : ResidueField O} :
    IsAlphaState π c k z → IsAlphaState π c k' z' → k = k' ∧ z = z'

/-- **H.112 (clause ii).** The α content is exactly `m·k` and the event sits in the window:
`m·k ≤ N − 1` (the A-H.2 window condition, AUTOMATIC on true events). -/
axiom alpha_content {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 2 ≤ m) (hN : 1 ≤ N)
    {c : ClusterState O m N} {k : ℕ} {z : ResidueField O} (h : IsAlphaState π c k z) :
    betaContent c k = m * k ∧ 1 ≤ k ∧ m * k ≤ N - 1

/-- **H.112 (clause iii).** The child set is finite. -/
axiom childSet_finite {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : ClusterState O m N) :
    {p : ℕ × ℕ × ResidueField O | HasChildAt π c p.1 p.2.1 p.2.2}.Finite

/-! ### H.113 — the drain census -/

/-- **H.113.** `#DRAIN = Q^{(m−1)(N−1)}`. -/
axiom card_drainState {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (m N : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    Nat.card {c : ClusterState O m N // IsDrainState c}
      = residueCard O ^ ((m - 1) * (N - 1))

/-! ### H.114 — the α-locus law -/

/-- **H.114.** `#α(k) = (Q−1)·Q^{m(N−1) − k·m(m+1)/2}` at realized `k` (`1 ≤ k`,
`m·k ≤ N−1`); the slope is `clusterC (m+1) = m(m+1)/2`. -/
axiom card_alphaSlice {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) {m N k : ℕ}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1) :
    Nat.card {c : ClusterState O m N // ∃ z, IsAlphaState π c k z}
      = (residueCard O - 1) * residueCard O ^ (m * (N - 1) - k * clusterC (m + 1))

/-! ### A-H.5 §1 — the canonical lift pair (the pinned centre)

AMENDMENT A-H.5 (2026-08-16): clause (i) of H.115/H.116 universally quantified the CENTRE and
was REFUTED (`verification/openmath/OM2_h115_h116_centre_shift_refutation.py`, exit 0). The
repair pins the centre IN THE DEF through a fixed section of `residue`, and the class lift
through a fixed section of `proj` (H.100's `Finite`-free `proj_surjective'`). Landing site:
the head of `leanfinal/Uniformity/ChapH/H115.lean`, imported by `ChapH/H116.lean`.
`resSect` is the pattern already machine-checked in this repo at
`leancheck/UniformityCheck/N3Recur.lean`. -/

/-- **A-H.5 §1.** The pinned centre: a section of the residue map, a function of the residue
alone — the Lean counterpart of the battery's `RB.lift_res(z)`. -/
noncomputable def resSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ResidueField O → O :=
  Function.surjInv IsLocalRing.residue_surjective

theorem residue_resSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (x : ResidueField O) : residue O (resSect O x) = x :=
  Function.surjInv_eq _ x

/-- **A-H.5 §1.** The pinned class lift: a section of `proj`, inverting H.100's
`proj_surjective'`. -/
noncomputable def classSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m N : ℕ) : Coeff O m N → (Fin m → O) :=
  Function.surjInv (proj_surjective' O m N)

theorem proj_classSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m N : ℕ) (c : Coeff O m N) : proj O m N (classSect O m N c) = c :=
  Function.surjInv_eq _ c

/-- **A-H.5 §1.** The recentred frame of a CLASS at the pinned lift pair — the object both
child extractions read. -/
noncomputable def recFrame {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N : ℕ} (c : Coeff O m N) (k : ℕ) (z : ResidueField O) : Polynomial O :=
  (monicPoly (classSect O m N c)).comp (C (π ^ k) * (X + C (resSect O z)))

/-- **A-H.5 §2.** Exact division by `π ^ n`, totalized (junk `0` off the divisibility
locus). -/
noncomputable def divPow {O : Type*} [CommRing O] (π : O) (n : ℕ) (x : O) : O :=
  letI : Decidable (π ^ n ∣ x) := Classical.dec _
  if h : π ^ n ∣ x then h.choose else 0

theorem divPow_spec {O : Type*} [CommRing O] {π : O} {n : ℕ} {x : O} (h : π ^ n ∣ x) :
    x = π ^ n * divPow π n x := by
  unfold divPow
  rw [dif_pos h]
  exact h.choose_spec

/-! ### H.115 — the α-shear transport (N-2b) -/

set_option linter.unusedVariables false in
/-- **H.115 (def half — REAL BODY, A-H.5 §2).** The recentred, content-divided,
window-truncated α child, extracted at the PINNED lift pair. α needs no factorization (the
divided frame is already monic), so the child is an explicit division of `recFrame`. The
subtype guard totalizes the α-membership `b i ∈ 𝔪` without hiding it: clause (i) is FALSE
whenever the junk branch fires, so the membership stays an obligation of clause (i).

`h` is the domain guard and the inference handle for the implicit `{k}`, `{z}`; it is unused
in the body (B77a precedent for the linter silencing). -/
noncomputable def alphaChild {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) {m N k : ℕ} {z : ResidueField O}
    (c : ClusterState O m N) (h : IsAlphaState π c k z) : ClusterState O m (N - m * k) :=
  let b : Fin m → O := fun j => divPow π (m * k) ((recFrame π c.1 k z).coeff (j : ℕ))
  letI : Decidable (∀ i, proj O m (N - m * k) b i
      ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ (N - m * k)))) :=
    Classical.dec _
  if hb : ∀ i, proj O m (N - m * k) b i
      ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ (N - m * k)))
    then ⟨proj O m (N - m * k) b, hb⟩
    else ⟨fun _ => 0, fun _ => Ideal.zero_mem _⟩

/-- **H.115 (clause i) [RE-SIGNED: A-H.5 §4].** The extraction is what it says: AT THE
CANONICAL CENTRE `resSect O z` and at every lift `a` of the class, the recentred polynomial is
EXACTLY `π^{mk} ·` a monic cluster development lifting the child.

The committed `∀ (a) (w), … residue O w = z → …` form was REFUTED (a centre shift by `d ∈ 𝔪`
moves the child by `m·d ∈ 𝔪 ∖ 𝔪²` while the child is read at window `N − mk ≥ 2`). At
`a := classSect O m N c.1` this statement is exactly the battery's `extract_child` semantics.
The surviving `∀ a` is a strengthening beyond the battery's tested point, licensed by H.109's
`pow_dvd_coeff_comp_sub` (`π^N` for ANY recentring — the full child window), not by teeth. -/
axiom alphaChild_spec {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N k : ℕ} {z : ResidueField O} (hm : 2 ≤ m)
    (hN : 1 ≤ N) (c : ClusterState O m N) (h : IsAlphaState π c k z) :
    ∀ a : Fin m → O, proj O m N a = c.1 →
      ∃ b : Fin m → O, (∀ i, b i ∈ maximalIdeal O) ∧
        (monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C (resSect O z)))
          = Polynomial.C (π ^ (m * k)) * monicPoly b ∧
        proj O m (N - m * k) b = (alphaChild π c h).1

/-- **H.115 (clause ii).** The shear is ONTO the full window-`(N−mk)` state space. -/
axiom alphaChild_surjective {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N k : ℕ} {z : ResidueField O}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1) (hz : z ≠ 0) :
    ∀ d : ClusterState O m (N - m * k),
      ∃ (c : ClusterState O m N) (h : IsAlphaState π c k z), alphaChild π c h = d

/-- **H.115 (clause iii).** Every ghost fibre has cardinality `Q^{k·c(m)}`,
`c(m) = clusterC m = m(m−1)/2` (the R2 unit-pivot mechanism, H.60). -/
axiom card_alphaFiber {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) {m N k : ℕ}
    {z : ResidueField O} (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1)
    (hz : z ≠ 0) (d : ClusterState O m (N - m * k)) :
    Nat.card {c : ClusterState O m N | ∃ h : IsAlphaState π c k z, alphaChild π c h = d}
      = residueCard O ^ (k * clusterC m)

/-! ### H.116 — the β-extraction at the capped window (N-2c) -/

set_option linter.unusedVariables false in
/-- **H.116 (def half — REAL BODY, A-H.5 §3).** The `(μ, k, z)`-child of a state, read at an
EXPLICIT window `M` (DECISION D-H17.2: the window is an argument, so genre-level statements
avoid dependent-index casts; the genuine child is at `M = N − betaContent c k`. D-H17.2 is
UNAFFECTED by A-H.5 — the refuted item was the centre quantifier, not the explicit window).

Unlike α (a division formula) β needs a FACTORIZATION, so the body is a DEFINITION BY
DESCRIPTION at the pinned centre: the child state whose lift `b` (degree `μ`, coefficients in
`𝔪`) exhibits the pinned frame's `π^D`-factorization. Its two obligations are node-side:
EXISTENCE (H.102's coprime split + `exists_monic_factorization_finset`) and UNIQUENESS AT A
FIXED CENTRE (H.102's `InjOn` plus the `𝔪`-coefficient condition). Until existence is proved
the description sits on its junk branch and clause (i) is false — nothing smuggled. -/
noncomputable def betaChild {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (π : O) {m N μ k : ℕ} {z : ResidueField O}
    (c : ClusterState O m N) (h : HasChildAt π c μ k z) (M : ℕ) : ClusterState O μ M :=
  letI : Decidable (∃ d : ClusterState O μ M, ∃ (b : Fin μ → O) (H' : Polynomial O),
        (∀ i, b i ∈ maximalIdeal O) ∧
        recFrame π c.1 k z = C (π ^ betaContent c k) * (monicPoly b * H') ∧
        proj O μ M b = d.1) := Classical.dec _
  if hb : ∃ d : ClusterState O μ M, ∃ (b : Fin μ → O) (H' : Polynomial O),
        (∀ i, b i ∈ maximalIdeal O) ∧
        recFrame π c.1 k z = C (π ^ betaContent c k) * (monicPoly b * H') ∧
        proj O μ M b = d.1
    then hb.choose
    else ⟨fun _ => 0, fun _ => Ideal.zero_mem _⟩

/-- **H.116 (clause i) [RE-SIGNED: A-H.5 §4].** The extraction factors every lift of the class
AT THE CANONICAL CENTRE `resSect O z`: recentred = `π^D ·` (monic degree-`μ` cluster lift of the
child) `×` (co-factor), exactly.

The committed `∀ (a) (w), … residue O w = z → …` form was REFUTED: at `O = ℤ₅`,
`f = (x−5)²(x−10)` (`m = 3, N = 6, k = 1, z = 1, μ = 2`, so `D = 3`, window 3) the centres
`w = 1` and `w = 6` give the children `(0, 0)` and `(25, 10)` mod `5³`, each the UNIQUE monic
degree-`μ` factor with coefficients in `𝔪` at its centre. `∀ a` survives (H.109's
`pow_dvd_coeff_comp_sub` + H.102's `InjOn` at window `N − D`). -/
axiom betaChild_spec {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π)
    {m N μ k : ℕ} {z : ResidueField O} (hm : 2 ≤ m) (hN : 1 ≤ N)
    (c : ClusterState O m N) (h : HasChildAt π c μ k z) (h0 : ¬ IsDrainState c) :
    ∀ a : Fin m → O, proj O m N a = c.1 →
      ∃ (b : Fin μ → O) (H' : Polynomial O), (∀ i, b i ∈ maximalIdeal O) ∧
        (monicPoly a).comp (Polynomial.C (π ^ k) * (X + Polynomial.C (resSect O z)))
          = Polynomial.C (π ^ betaContent c k) * (monicPoly b * H') ∧
        proj O μ (N - betaContent c k) b
          = (betaChild π c h (N - betaContent c k)).1

/-- **H.116 (clause ii).** Per genre (fixed child set `L` and fixed windows `D`), the joint
child map has EQUICARDINAL fibres — the composed-count mechanism
`census_g · [ΠT_l − Π(T_l − u_l)]` of the battery's P1(f). -/
axiom betaExtract_fiber_card {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π) {m N : ℕ}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (L : Finset (ℕ × ℕ × ResidueField O)) (hL : L.Nonempty)
    (D : ℕ × ℕ × ResidueField O → ℕ) :
    ∃ F : ℕ, ∀ t : ∀ p ∈ L, ClusterState O p.1 (N - D p),
      Nat.card {c : ClusterState O m N |
        IsBetaState π c ∧
        (∀ p : ℕ × ℕ × ResidueField O, HasChildAt π c p.1 p.2.1 p.2.2 ↔ p ∈ L) ∧
        (∀ p ∈ L, betaContent c p.2.1 = D p) ∧
        (∀ (p : ℕ × ℕ × ResidueField O) (hp : p ∈ L)
            (hc : HasChildAt π c p.1 p.2.1 p.2.2),
          betaChild π c hc (N - D p) = t p hp)} = F

/-! ### H.117 — the CS criterion (fires H.03/H.04) -/

/-- **H.117 (clause i).** No CS event below `m = 4`. -/
axiom isCSState_four_le {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (c : ClusterState O m N) (h : IsCSState π c) : 4 ≤ m

/-- **H.117 (clause ii).** Every CS block obeys `4 ≤ ℓ·μ·deg ψ ≤ m`. -/
axiom cs_block_bounds {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {π : O} (hπ : Irreducible π) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    (c : ClusterState O m N) (h0 : ¬ IsDrainState c)
    (a : Fin m → O) (ha : proj O m N a = c.1) (u ℓ : ℕ)
    (hne : (sideSet X (monicPoly a) u ℓ).Nonempty) (H₀ : ℕ) (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ)
    (hpin : npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hne) = (H₀ : ℕ∞))
    (ψ : Polynomial (resField (X : Polynomial O))) (hψ : Irreducible ψ) (μ : ℕ)
    (hμ : 2 ≤ μ) (hblock : 2 ≤ ℓ * ψ.natDegree)
    (hdvd : ψ ^ μ ∣ resPoly π X (monicPoly a) u ℓ hne H₀) :
    4 ≤ ℓ * μ * ψ.natDegree ∧ ℓ * μ * ψ.natDegree ≤ m

end LeanspecH17

namespace LeanspecH17

open Uniformity Uniformity.Density Uniformity.Density.Induction Uniformity.Density.Leaf
open IsLocalRing Polynomial

/-! ### H.118 — the conservative verdict (S-1's CONSERVATIVE object) -/

/-- **H.118.** The conservative reader's UNDECIDED set, as the least predicate closed under
the four propagation rules — DRAIN and CS exit undecided at depth 0 (DECISION D-H17.1,
pessimistic on stage data), α recurses at the sheared child (same degree, window `−mk`),
β propagates from ANY undecided child at its capped window. Well-founded by the lexicographic
measure (degree, window) — `EFF.GENIND.202`'s repair, the same measure H.71's closure runs
on. `DecidedAt`-side inversion: a state outside this predicate is DEC-resolved along its
whole recursion tree (H.119's iff). **This is the conservative complement `u_{m,d}`, NOT the
semantic `undecidedSet` — identifying them is REFUTED on F-2's witnesses (the S-1 fence).** -/
inductive ClusterUndecided (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (π : O) :
    ∀ (m N : ℕ), ClusterState O m N → Prop
  | drain {m N : ℕ} (c : ClusterState O m N) :
      IsDrainState c → ClusterUndecided O π m N c
  | cs {m N : ℕ} (c : ClusterState O m N) :
      IsCSState π c → ClusterUndecided O π m N c
  | alpha {m N k : ℕ} {z : ResidueField O} (c : ClusterState O m N)
      (h : IsAlphaState π c k z) :
      ClusterUndecided O π m (N - m * k) (alphaChild π c h) → ClusterUndecided O π m N c
  | beta {m N μ k : ℕ} {z : ResidueField O} (c : ClusterState O m N)
      (hβ : IsBetaState π c) (h : HasChildAt π c μ k z) :
      ClusterUndecided O π μ (N - betaContent c k)
          (betaChild π c h (N - betaContent c k)) →
      ClusterUndecided O π m N c

/-! ### H.119 — the conservative complement and its boundary -/

/-- **H.119 (def a).** `u_{m,1}(N)`: the conservative undecided count. -/
noncomputable def uCluster (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (π : O) (m N : ℕ) : ℕ :=
  Nat.card {c : ClusterState O m N // ClusterUndecided O π m N c}

/-- **H.119 (def b).** The normalized conservative complement `û(N) = u(N)/Q^{m(N−1)}`. -/
noncomputable def uClusterNorm (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] (π : O) (m N : ℕ) : ℝ :=
  (uCluster O π m N : ℝ) / (residueCard O : ℝ) ^ (m * (N - 1))

/-- **H.119 (lemma a).** The window-1 boundary `u(1) = 1` (`ANNEX R R3`, `EFF.GENIND.160`;
OM-2 row 0d): at window 1 the unique state is drain. -/
axiom uCluster_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] (π : O) (hπ : Irreducible π) (m : ℕ)
    (hm : 1 ≤ m) : uCluster O π m 1 = 1

/-- **H.119 (lemma b).** The recursion identity / inversion (battery P1(e)): the inductive
predicate is EXACTLY the reader's verdict equations. -/
axiom clusterUndecided_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π) {m N : ℕ}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (c : ClusterState O m N) :
    ClusterUndecided O π m N c ↔
      IsDrainState c ∨ IsCSState π c ∨
      (∃ (k : ℕ) (z : ResidueField O) (h : IsAlphaState π c k z),
        ClusterUndecided O π m (N - m * k) (alphaChild π c h)) ∨
      (IsBetaState π c ∧ ∃ (μ k : ℕ) (z : ResidueField O) (h : HasChildAt π c μ k z),
        ClusterUndecided O π μ (N - betaContent c k)
          (betaChild π c h (N - betaContent c k)))

/-! ### H.120 — cluster-level C2D (debt D-4) -/

/-- **H.120.** Window-truncation monotonicity of the NORMALIZED conservative complement —
H.70's argument on the `ClusterState` carrier. -/
axiom uClusterNorm_antitone {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) (m : ℕ) (hm : 2 ≤ m) :
    ∀ T W, 1 ≤ T → T ≤ W → uClusterNorm O π m W ≤ uClusterNorm O π m T

/-! ### H.121 — the three legs on true data (N-3's instantiation layer) -/

/-- **H.121 (clause i, the split — hsplit as an EQUALITY).** At `m ≤ 3` the CS bucket is
empty (H.117) and the conservative complement splits exactly. -/
axiom uCluster_split {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3) (N : ℕ) (hN : 1 ≤ N) :
    uCluster O π m N
      = Nat.card {c : ClusterState O m N // IsDrainState c}
        + Nat.card {c : ClusterState O m N //
            (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π m N c}
        + Nat.card {c : ClusterState O m N //
            IsBetaState π c ∧ ClusterUndecided O π m N c}

/-- **H.121 (clause ii, the α leg — halpha as an EQUALITY, UNBOUNDED windowed range).**
The α-undecided mass recurses with the structure slope `clusterC (m+1) − clusterC m`
recomposition, i.e. absolute coefficient `(Q−1)·Q^{k·clusterC m}` against the child count at
window `N − mk` — summed over ALL realized `k` (`1 ≤ k`, `mk ≤ N−1`). ⚠ The realized range
is WINDOW-DEPENDENT: no fixed `n₀` covers it (finding F-H17.1 → PA-H17.1 at H.71). -/
axiom uCluster_alpha_leg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) (N : ℕ) (hN : 1 ≤ N) :
    Nat.card {c : ClusterState O m N //
        (∃ k z, IsAlphaState π c k z) ∧ ClusterUndecided O π m N c}
      = ∑ k ∈ (Finset.range N).filter (fun k => 1 ≤ k ∧ m * k ≤ N - 1),
          (residueCard O - 1) * residueCard O ^ (k * clusterC m) * uCluster O π m (N - m * k)

/-- **H.121 (clause iii, the β leg — hbeta at `(K', B', c') = (1, 0, 1)`).** Certified shape:
the battery measures `K' ≤ 0.0004` at this envelope (`m ∈ {2,3}`, both rings), so `K' = 1` is
safe; the proof route is the degree-descent (children have degree `< m`) through H.63/H.67/
H.68. Stated unnormalized. -/
axiom uCluster_beta_leg {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) (hm3 : m ≤ 3) (N : ℕ) (hN : 1 ≤ N) :
    (Nat.card {c : ClusterState O m N //
        IsBetaState π c ∧ ClusterUndecided O π m N c} : ℝ)
      ≤ (N : ℝ) ^ m * (residueCard O : ℝ) ^ (m * (N - 1))
          * ((residueCard O : ℝ) ^ (N - 2))⁻¹

/-! ### H.122 — the cluster rate species -/

/-- **H.122.** The conservative cluster complement has the `(A2-RATE)` species at
`(K, B, c) = (1, 1, 1)` for `2 ≤ m ≤ 3` — `EFF.GENIND.150`'s ground sharpness, certified on
true data (battery P3). Proof route: H.121's legs closed by the H.71 lexicographic induction
at the UNBOUNDED windowed α-range (PA-H17.1), constants via H.30/H.66. -/
axiom uClusterNorm_rateSpecies {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 2 ≤ m) (hm3 : m ≤ 3) :
    RateSpecies (residueCard O) 1 1 1 (fun N => uClusterNorm O π m N)

/-! ### H.123 — THE S-1 BRIDGE (INEQUALITY ONLY) -/

/-- **H.123.** Reader-decided ⟹ `DecidedAt`, per full-cluster stratum at `d = 1`:
the SEMANTIC undecided count of the stratum is at most the CONSERVATIVE complement.
**INEQUALITY ONLY** — the two objects differ from `(n, N) = (2, 3)` on (F-2's witnesses:
conservative `q·hex3R = 12` vs the landed semantic law `q^N = 8` at `q = 2, N = 3`); any
equality form is REFUTED. Consumes B.42 (footprint-visible) + B.48/B.58/B.63 contracts. -/
axiom undecidedCount_le_uCluster {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)]
    [IsAdicComplete (maximalIdeal O) O] {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 2 ≤ m) (N : ℕ) (hN : 1 ≤ N) (zbar : ResidueField O) :
    Nat.card
        ((undecidedSet O m N ∩
          levelZeroStratum O m N ((X - Polynomial.C zbar) ^ m) : Set (Coeff O m N)))
      ≤ uCluster O π m N

/-! ### H.124 — the terminal composed reduction (T-1's honest conditional Lean form) -/

/-- **H.124 (def half).** The full-cluster rate hypothesis at degree `n`: constants
`(K, B, c)` chosen ONCE (outside `∀ O`), bounding the SEMANTIC per-stratum undecided count of
every full-cluster stratum (`m ≥ 2`, `m·d = n`) relative to the stratum total. -/
def FullClusterRateBound (n : ℕ) (K : ℝ) (B c : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
    ∀ (p : Polynomial (IsLocalRing.ResidueField O)) (m d : ℕ), 2 ≤ m → m * d = n →
      p.Monic → Irreducible p → p.natDegree = d →
      ∀ M, 1 ≤ M →
        (Nat.card ((undecidedSet O n M ∩ levelZeroStratum O n M (p ^ m) :
            Set (Coeff O n M))) : ℝ)
          ≤ K * (M : ℝ) ^ B * ((residueCard O : ℝ) ^ (M - c))⁻¹
            * (Nat.card (levelZeroStratum O n M (p ^ m)) : ℝ)

/-- **H.124 (theorem half).** THE REDUCTION, composed: `(IH) + full-cluster rates ⟹ P(n)`.
This is `GENIND.B` Steps 1 + 4h as a single implication — the menu clause is landed
(`exists_coveringMenu`, S-0), the level-0 transport is H.100–H.105, and the full-cluster
hypothesis is exactly where Steps 2–4's cluster layer (H.106–H.123 at `m ≤ 3, d = 1`;
HYP.36/81/82- and `B-BOX-1`-gated beyond) discharges. **NOT `THEOREM GENIND.B` itself**: the
hypothesis is carried, never claimed (the H.98 fence stands). -/
axiom inductionPackage_of_clusterRates (n : ℕ) (hn : 2 ≤ n)
    (ih : ∀ k, 2 ≤ k → k < n → InductionPackage k)
    (hfc : ∃ (K : ℝ) (B c : ℕ), 0 ≤ K ∧ FullClusterRateBound n K B c) :
    InductionPackage n

end LeanspecH17
