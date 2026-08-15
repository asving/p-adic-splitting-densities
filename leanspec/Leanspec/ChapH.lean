import Uniformity

/-!
# Chapter H — THE GENERAL INDUCTION: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-H_general_induction.md` (99 nodes, **192 written / 190 signed**
declarations), landed in the isolated `leanspec` environment **before** the chapter-H fleet fires,
in the blueprint's node order `H.01 … H.99` (`H.99` is a gate/census block, not a declaration).

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
This file is never imported by `leanfinal` or `leancheck`; it carries `axiom`s by design and
proves nothing.

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
  design note's claim needs withdrawing. **Partly closed here:** this file constructs
  `stageIfaceE : StageInterface (genreE2 0) 2 0 4` (gate section) — so the structure is inhabited
  and its eleven fields are jointly satisfiable, which is also what makes D4's refutation bite. The
  chapter still signs no instance of its own, and the genre-F instance §3 claims is still absent.
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

open Uniformity Uniformity.Density

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
structure GenreDatum where
  /-- The ambient cluster's residue cardinality `Q = q ^ d`. -/
  Q : ℕ
  /-- The slope denominator; the stage's value-group index `E = e₁`. -/
  e₁ : ℕ
  /-- The residual factor's degree; the stage residue field is `F_(Q ^ f₁)`. -/
  f₁ : ℕ
  /-- The residual factor's multiplicity, `= the stage multiplicity`. -/
  μ : ℕ
  /-- The slope numerator. -/
  h : ℕ
  hQ : 2 ≤ Q
  he₁ : 1 ≤ e₁
  hh : 1 ≤ h
  hkey : 2 ≤ e₁ * f₁
  hmul : 2 ≤ μ
  hcop : Nat.Coprime h e₁

/-! ### NODE H.02 [def] — the derived stage data (real bodies) -/

/-- `D′ = e₁ f₁`, the entry key's degree. -/
def GenreDatum.keyDeg (G : GenreDatum) : ℕ := G.e₁ * G.f₁

/-- `|K| = Q ^ f₁`, the stage residue cardinality. -/
def GenreDatum.stageCard (G : GenreDatum) : ℕ := G.Q ^ G.f₁

/-- `L = e₁ μ f₁`, the abscissa length the composite block occupies. -/
def GenreDatum.sideLen (G : GenreDatum) : ℕ := G.e₁ * G.μ * G.f₁

/-- The stage-initial node floor at coordinate `j`, in `dv`-units:
`dv(A_j) ≥ (μ − j) · D′ h + 1`.  This is the `[r1]`-CORRECTED floor of `GENHN.A`(i); the sealed
`(μ − j) · e₁ h + 1` is the `f₁ = 1` specialization (H.08). -/
def GenreDatum.nodeHeight (G : GenreDatum) (j : ℕ) : ℕ := (G.μ - j) * G.keyDeg * G.h + 1

/-! ### NODE H.03 [lemma] -/

axiom GenreDatum.four_le_sideLen (G : GenreDatum) : 4 ≤ G.sideLen

/-! ### NODE H.04 [lemma] -/

axiom keyDeg_two_cases {e f : ℕ} (h : e * f = 2) : (e = 2 ∧ f = 1) ∨ (e = 1 ∧ f = 2)

axiom sideLen_four_cases {e f m : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ e * f) (h : e * m * f = 4) :
    (e = 2 ∧ f = 1 ∧ m = 2) ∨ (e = 1 ∧ f = 2 ∧ m = 2)

axiom four_le_of_sideLen_le {G : GenreDatum} {m D n : ℕ} (hD : 1 ≤ D)
    (hLm : G.sideLen ≤ m) (hmn : m * D ≤ n) : 4 ≤ m ∧ 4 ≤ n

/-! ### NODE H.05 [theorem] — the schema set is finite -/

/-- The schema set at degree `n`: the triples `(e₁, f₁, μ)` a degree-`n` read can realize. -/
def schemaSet (n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {p | 2 ≤ p.1 * p.2.1 ∧ 2 ≤ p.2.2 ∧ p.1 * p.2.2 * p.2.1 ≤ n}

axiom finite_schemaSet (n : ℕ) : (schemaSet n).Finite

axiom card_schemaSet_le (n : ℕ) : Nat.card (schemaSet n) ≤ n ^ 3

/-! ### NODE H.06 [theorem] — the DATUM set is infinite (the A2 refutation)

`hcop`'s cited lemma name is DEFECT D3: `Nat.coprime_two_right_iff_odd` does not exist at the pin;
`Nat.coprime_two_right` does. -/

/-- The genre-E datum at `Q = 2` with slope numerator `2t+1`. -/
def genreE2 (t : ℕ) : GenreDatum where
  Q := 2; e₁ := 2; f₁ := 1; μ := 2; h := 2 * t + 1
  hQ := le_refl 2
  he₁ := by omega
  hh := by omega
  hkey := by omega
  hmul := le_refl 2
  hcop := Nat.coprime_two_right.2 ⟨t, rfl⟩

axiom genreE2_injective : Function.Injective genreE2

axiom infinite_genreDatum_of_schema :
    {G : GenreDatum | G.Q = 2 ∧ G.e₁ = 2 ∧ G.f₁ = 1 ∧ G.μ = 2}.Infinite

/-! ### NODE H.07 [def] — the occupied-height predicate (real body) -/

/-- `G.Occupied m`: the `dv`-height `m` admits an INTEGRAL normalizer monomial
`n(m) = x^{i} π^{a}` with `0 ≤ i < e₁` and `a ≥ 0`.  This is the TERMINAL scope word of
`GENHN.A`(ii) after the post-D2b corrigendum. -/
def GenreDatum.Occupied (G : GenreDatum) (m : ℕ) : Prop :=
  ∃ i a : ℕ, i < G.e₁ ∧ i * G.h + G.e₁ * a = m

/-! ### NODE H.08 [lemma] -/

axiom GenreDatum.keyDeg_mul_h_lt_nodeHeight (G : GenreDatum) {j : ℕ} (hj : j < G.μ) :
    G.keyDeg * G.h < G.nodeHeight j

axiom GenreDatum.nodeHeight_of_f_one (G : GenreDatum) (hf : G.f₁ = 1) (j : ℕ) :
    G.nodeHeight j = (G.μ - j) * G.e₁ * G.h + 1

/-! ### NODE H.13 [def] — `clusterC`, **HOISTED** out of §4

FINDING O1: H.09's `hbracket` field mentions `clusterC`, so the blueprint's own §3-before-§4
section order cannot be the landing order. H.09's DEPENDS field already lists H.13. -/

/-- `c(m) = m(m−1)/2`, the α-bracket's exponent coefficient offset (`GENIND` §S1). Defined as
`m.choose 2` so that `2 * clusterC m = m * (m − 1)` is exact in `ℕ` with no floor. -/
def clusterC (m : ℕ) : ℕ := m.choose 2

/-! ### NODE H.09 [def] — `StageInterface` (real body; §15's fragile signature #1) -/

/-- **The stage interface.** Every field is a clause of `[GENIND-H]` in its TERMINAL wording:
`(CS-1Q.a)`/`(CS-1Q.b)` (ledger `HYP.36`, disposition CARRY), `(CS-2)` (the stage bracket, in the
MASS normalization), `(CS-EXACT)`, and the degree-consistency half of `(CS-3)`.  **Nothing in this
structure is proved by chapter H**; the chapter proves the count and rate theorems of §10 FROM these
fields. -/
structure StageInterface (G : GenreDatum) (N H S : ℕ) where
  /-- The common uniform stage window `M_G`. -/
  stageWindow : ℕ
  /-- `Δ_G = λ_G + r_G`: the sibling-Hensel loss plus the ragged truncation loss. -/
  stageLoss : ℕ
  /-- `C_G^{extra}`: the entry codimension beyond the supporting-line price. -/
  entryCodim : ℕ
  /-- `O_G(1)`: the genre-local slack. -/
  slack : ℕ
  /-- The stage's own α-aggregation bracket, per stage-slope-sum `κ`. -/
  bracket : ℕ → ℕ
  /-- The stage's conservative-drain fraction at stage window `M`. -/
  drainFrac : ℕ → ℝ
  /-- The σ-multiset the stage's decided leaves carry. -/
  stageSigma : FactorizationType
  /-- The actual side length dominates the block's own length. -/
  hS : G.sideLen ≤ S
  /-- **(CS-1Q.a)** — the ragged/loss-corrected stage-window supply. -/
  hwin : G.e₁ * (N - 1 - H) ≤ stageWindow + stageLoss
  /-- **(CS-1Q.b)** — every lost `K`-digit is paid by entry codimension or supporting-line slack. -/
  hprice : 2 * (G.f₁ * stageLoss) ≤ 2 * entryCodim + (S - 2 * G.keyDeg) * H + 2 * slack
  /-- **(CS-2)** — the stage bracket is `GENIND-2(b)` inside the stage, MASS-normalized. -/
  hbracket : ∀ κ, 1 ≤ κ →
    bracket κ * G.stageCard = (G.stageCard - 1) * G.stageCard ^ ((clusterC G.μ + 1) * κ)
  /-- The drain fraction is a genuine fraction. -/
  hdrain_nonneg : ∀ M, 0 ≤ drainFrac M
  hdrain_le_one : ∀ M, drainFrac M ≤ 1
  /-- **(CS-3)**, degree half — at `μ = 2` the leaf dictionary exhausts the block degree. -/
  hsigma : G.μ = 2 → stageSigma.degree = 2 * G.keyDeg

/-! ### NODE H.10 [lemma] -/

axiom GenreDatum.occupied_of_keyDeg_mul_h_lt (G : GenreDatum) {m : ℕ}
    (hm : G.keyDeg * G.h < m) : G.Occupied m

axiom GenreDatum.occupied_nodeHeight (G : GenreDatum) {j : ℕ} (hj : j < G.μ) :
    G.Occupied (G.nodeHeight j)

/-! ### NODE H.11 [lemma] — the A2/R4 unoccupied-height witness -/

/-- The A2/R4 witness datum `(Q; e₁, f₁, μ; h) = (2; 3, 1, 2; 2)`. -/
def genreA2witness : GenreDatum where
  Q := 2; e₁ := 3; f₁ := 1; μ := 2; h := 2
  hQ := le_refl 2
  he₁ := by omega
  hh := by omega
  hkey := by omega
  hmul := le_refl 2
  hcop := by decide

axiom not_occupied_genreA2witness : ¬ genreA2witness.Occupied 1

/-! ### NODE H.12 [lemma] — the post-D2b witness -/

/-- The post-D2b witness datum `(Q; e₁, f₁, μ; h) = (2; 1, 2, 2; 1)`. -/
def genreD2bwitness : GenreDatum where
  Q := 2; e₁ := 1; f₁ := 2; μ := 2; h := 1
  hQ := le_refl 2
  he₁ := le_refl 1
  hh := le_refl 1
  hkey := by omega
  hmul := le_refl 2
  hcop := by decide

axiom occupied_zero_genreD2bwitness : genreD2bwitness.Occupied 0

axiom not_keyDeg_mul_h_lt_zero_genreD2bwitness :
    ¬ (genreD2bwitness.keyDeg * genreD2bwitness.h < 0)

/-! ## §4 — ARITHMETIC I: THE α SPECIES (H.13–H.22)

`clusterC` (H.13) is hoisted above H.09 — see FINDING O1. -/

/-! ### NODE H.14 [lemma] -/

axiom two_mul_clusterC (m : ℕ) : 2 * clusterC m = m * (m - 1)

axiom clusterC_eq_sum (m : ℕ) : clusterC m = ∑ j ∈ Finset.range m, j

axiom clusterC_succ_values :
    clusterC 2 + 1 = 2 ∧ clusterC 3 + 1 = 4 ∧ clusterC 4 + 1 = 7 ∧ clusterC 5 + 1 = 11

/-! ### NODE H.15 [def] -/

/-- The α(k)-locus's free-digit exponent, written in the TRANSPORTED coordinate `W = N − 1 − mk`:
`alphaExp m W k = m·W + k·c(m)` — the reduced-window exponent plus the ghost exponent.  H.16
identifies it with `GENIND`'s displayed `m(N−1) − k·m(m+1)/2`. -/
def alphaExp (m W k : ℕ) : ℕ := m * W + k * clusterC m

/-! ### NODE H.16 [lemma] -/

axiom sum_alphaSlots (m W k : ℕ) :
    ∑ j ∈ Finset.range m, (W + j * k) = alphaExp m W k

axiom two_mul_alphaExp_add (m W k : ℕ) :
    2 * alphaExp m W k + k * (m * (m + 1)) = 2 * (m * (W + m * k))

/-! ### NODE H.17 [lemma] -/

axiom ghostSlots_eq (m k : ℕ) : ∑ j ∈ Finset.range m, j * k = k * clusterC m

axiom ghost_add_child_eq_alphaExp (m W k : ℕ) :
    k * clusterC m + m * W = alphaExp m W k

/-! ### NODE H.18 [def] — `alphaBracket` (real body)

DEFECT D2: the blueprint body carries no `decreasing_by`; the goal `μ - k < μ + 1` is
unconditionally true, so the tactic below is the whole repair. -/

/-- The α-prefix aggregate `b_{m,d}(μ)`, defined by the composition recursion (peel the first
step).  `alphaBracket Q c μ = Σ over compositions (k₁,…,k_r) of μ with kᵢ ≥ 1 of
Π (Q−1)Q^{c kᵢ}`, and `alphaBracket Q c 0 = 1`. -/
def alphaBracket (Q c : ℕ) : ℕ → ℕ
  | 0 => 1
  | (μ + 1) => ∑ k ∈ Finset.range (μ + 1),
      (Q - 1) * Q ^ (c * (k + 1)) * alphaBracket Q c (μ - k)
  decreasing_by omega

/-! ### NODE H.19 [lemma] -/

axiom alphaBracket_succ (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    alphaBracket Q c (μ + 1) = Q ^ (c + 1) * alphaBracket Q c μ

/-! ### NODE H.20 [theorem] — the general bracket (SPLIT-MANDATED into 2) -/

axiom alphaBracket_closed (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    Q * alphaBracket Q c μ = (Q - 1) * Q ^ ((c + 1) * μ)

/-- The corpus's displayed form, for consumers that prefer it. -/
axiom alphaBracket_eq (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) {μ : ℕ} (hμ : 1 ≤ μ) :
    alphaBracket Q c μ = (Q - 1) * Q ^ ((c + 1) * μ - 1)

/-! ### NODE H.21 [lemma] — the `(CS-2)` numeric certificate (EXECUTED at the gate below) -/

axiom alphaBracket_audit :
    alphaBracket 4 1 2 = 192 ∧ alphaBracket 3 1 2 = 54 ∧ alphaBracket 2 1 3 = 32

axiom massNorm_eq_ghost_mul_letters :
    (4 : ℕ) ^ 2 * ((4 - 1) * 4 ^ 1) = alphaBracket 4 1 2

/-! ### NODE H.22 [lemma] -/

axiom drain_codim (d m N : ℕ) (hm : 1 ≤ m) :
    d * (m - 1) * (N - 1) + d * (N - 1) = d * m * (N - 1)

axiom window_one_exponents (d m : ℕ) (hm : 1 ≤ m) :
    d * m * (1 - 1) = 0 ∧ d * (m - 1) * (1 - 1) = 0 ∧ ¬ ∃ k, 1 ≤ k ∧ m * k ≤ 0

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
def uTwo (Q : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (N + 2) => Q ^ (N + 1) +
      ∑ k ∈ Finset.range (N + 2),
        if h : 1 ≤ k ∧ 2 * k ≤ N + 1 then (Q - 1) * Q ^ k * uTwo Q (N + 2 - 2 * k) else 0
  decreasing_by omega

/-! ### NODE H.24 [lemma] -/

axiom uTwo_one (Q : ℕ) : uTwo Q 1 = 1

axiom uTwo_two (Q : ℕ) : uTwo Q 2 = Q

/-! ### NODE H.25 [theorem] -/

axiom uTwo_rec (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 3 ≤ N) :
    uTwo Q N + Q ^ (N - 2) = Q ^ (N - 1) + Q ^ 2 * uTwo Q (N - 2)

/-! ### NODE H.26 [theorem] — the `m = 2` closed form (SPLIT-MANDATED into 2) -/

axiom uTwo_closed (Q : ℕ) (hQ : 2 ≤ Q) {M : ℕ} (hM : 2 ≤ M) :
    uTwo Q M = Q ^ (M - 1) + ((M - 1) / 2) * ((Q - 1) * Q ^ (M - 2))

axiom uTwo_even (Q : ℕ) (hQ : 2 ≤ Q) {l : ℕ} (hl : 1 ≤ l) :
    uTwo Q (2 * l) + (l - 1) * Q ^ (2 * l - 2) = l * Q ^ (2 * l - 1)

axiom uTwo_odd (Q : ℕ) (hQ : 2 ≤ Q) (l : ℕ) :
    uTwo Q (2 * l + 1) + l * Q ^ (2 * l - 1) = (l + 1) * Q ^ (2 * l)

/-! ### NODE H.27 [lemma] -/

axiom uTwo_le (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 1 ≤ N) : uTwo Q N ≤ N * Q ^ (N - 1)

/-! ### NODE H.28 [theorem] — the `(A2-RATE)` ground instance -/

axiom uTwo_ratio_le (Q : ℕ) (hQ : 2 ≤ Q) {N : ℕ} (hN : 1 ≤ N) :
    (uTwo Q N : ℝ) / (Q : ℝ) ^ (2 * (N - 1)) ≤ (N : ℝ) / (Q : ℝ) ^ (N - 1)

/-! ### NODE H.29 [lemma] — the two-prime numeric audit (EXECUTED at the gate below) -/

axiom uTwo_audit_two :
    uTwo 2 1 = 1 ∧ uTwo 2 2 = 2 ∧ uTwo 2 3 = 6 ∧ uTwo 2 4 = 12 ∧ uTwo 2 5 = 32 ∧ uTwo 2 6 = 64

axiom uTwo_audit_three :
    uTwo 3 1 = 1 ∧ uTwo 3 2 = 3 ∧ uTwo 3 3 = 15 ∧ uTwo 3 4 = 45 ∧ uTwo 3 5 = 189 ∧ uTwo 3 6 = 567

/-! ## §6 — ARITHMETIC III: THE PRICING INEQUALITIES (H.30–H.37) -/

/-! ### NODE H.30 [lemma] -/

axiom alpha_geom_partial_le_one (Q c : ℕ) (hQ : 2 ≤ Q) (hc : 1 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ ≤ 1

/-! ### NODE H.31 [lemma] (SPLIT CANDIDATE) -/

axiom height_geom_partial_le (Q : ℕ) (hQ : 2 ≤ Q) (n : ℕ) :
    ∑ H ∈ Finset.range n, ((Q : ℝ) ^ (H : ℝ))⁻¹ ^ ((1:ℝ)/2)
      ≤ (1 - ((2:ℝ) ^ ((1:ℝ)/2))⁻¹)⁻¹

/-! ### NODE H.32 [lemma] -/

axiom two_mul_supportLine_sum (S H : ℕ) :
    2 * (∑ r ∈ Finset.range S, (r + 1) * H) = S * (S + 1) * H

/-! ### NODE H.33 [lemma] -/

axiom two_mul_a_le_sideLen {e f m : ℕ} (hm : 2 ≤ m) : 2 * (e * f) ≤ e * m * f

axiom two_mul_a_le_S {e f m S : ℕ} (hm : 2 ≤ m) (hS : e * m * f ≤ S) :
    2 * (e * f) ≤ S

/-! ### NODE H.34 [lemma] -/

axiom exp_compose {D M N c : ℕ} (hD : 1 ≤ D) (hc : c ≤ M) (h : D + M = N) :
    (D - 1) + (M - c) = N - 1 - c

axiom mul_le_of_exp_compose {Q : ℕ} (hQ : 2 ≤ Q) {D M N c : ℕ} (hD : 1 ≤ D) (hc : c ≤ M)
    (h : D + M = N) {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹) (hδ : δ ≤ ((Q : ℝ) ^ (M - c))⁻¹) :
    ρ * δ ≤ ((Q : ℝ) ^ (N - 1 - c))⁻¹

/-! ### NODE H.35 [lemma] -/

axiom pow_sub_dominance {N m B : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) (hB : 1 ≤ B) :
    (N - m) ^ B + m * (N - m) ^ (B - 1) ≤ N ^ B

/-! ### NODE H.36 [lemma] -/

axiom entry_codim (d D N : ℕ) (hD : 1 ≤ D) (hDN : D ≤ N) :
    d * (D - 1) + d * (N - D) = d * (N - 1)

/-! ### NODE H.37 [lemma] -/

axiom card_slopeTuples_le (m N : ℕ) :
    Nat.card {s : Fin m → ℕ // ∀ i, 1 ≤ s i ∧ s i ≤ N - 1} ≤ N ^ m

/-! ## §7 — ARITHMETIC IV: THE GENRE LAWS, FLOORS, TOWER THRESHOLDS (H.38–H.50) -/

/-! ### NODE H.38 [def+lemma] -/

/-- `CS4-E(h)` — the quartic e-first genre's per-centre opening locus, `(q−1)q^{4N−5h−3}`
(`GENIND` §S5.3 = `W-12` §S2.5's `QRT-G2(h;(1²))`).  Total by construction; the visibility floor
`2h ≤ N−1` is a hypothesis of `lawE_floor_*`, not of the definition. -/
def lawE (q N h : ℕ) : ℕ := (q - 1) * q ^ (4 * N - 5 * h - 3)

axiom lawE_exp_honest {N h : ℕ} (hfl : 2 * h + 1 ≤ N) : 5 * h + 3 ≤ 4 * N

axiom lawE_floor_fails_at_two_one {q : ℕ} (hq : 2 ≤ q) :
    ¬ (2 * 1 + 1 ≤ 2) ∧ lawE q 2 1 ≠ 0

/-! ### NODE H.39 [lemma] -/

axiom lawE_exp_four_summands {N t : ℕ} (hN : 4 * t + 3 ≤ N) :
    (N - (t + 1)) + (N - 1 - (2 * t + 1)) + (N - (3 * t + 2)) + (N - 1 - (4 * t + 2))
      + (10 * t + 8) = 4 * N

axiom lawE_exp_odd {N t : ℕ} (hN : 4 * t + 3 ≤ N) :
    4 * N - 5 * (2 * t + 1) - 3 = 4 * N - (10 * t + 8)

/-! ### NODE H.40 [def+lemma] -/

/-- `CS4-F(k)` — the quartic f-first genre's per-centre opening locus,
`(q(q−1)/2)·q^{4N−10k−4}` (`GENIND` §S5.3; `#ψ = q(q−1)/2` monic irreducible quadratics). -/
def lawF (q N k : ℕ) : ℕ := (q * (q - 1) / 2) * q ^ (4 * N - 10 * k - 4)

axiom lawF_exp_honest {N k : ℕ} (hfl : 4 * k + 1 ≤ N) : 10 * k + 4 ≤ 4 * N

axiom lawF_exp_neg_below_floor : (4 : ℤ) * 2 - 10 * 1 - 4 = -6

/-! ### NODE H.41 [lemma] — the quartic-law audit (EXECUTED at the gate below) -/

axiom quartic_law_audit :
    lawE 2 6 1 = 65536 ∧ lawE 3 4 1 = 13122 ∧ lawE 5 3 1 = 2500 ∧
    lawF 2 6 1 = 1024 ∧ lawF 2 5 1 = 64 ∧ lawE 2 6 1 + lawF 2 6 1 = 66560

/-! ### NODE H.42 [def+lemma] -/

/-- `CS5-V1E2(h)` — the quintic vertex-at-1 genre: `CS4-E`'s law times the split root's headroom
fibre `(q^{N−(5h+1)/2} − 1)` (`GENIND` §S5.3). -/
def lawV1E2 (q N h : ℕ) : ℕ := lawE q N h * (q ^ (N - (5 * h + 1) / 2) - 1)

axiom headroom_exp_odd (t : ℕ) : (5 * (2 * t + 1) + 1) / 2 = 5 * t + 3

axiom lawV1E2_eq_zero_iff {q N t : ℕ} (hq : 2 ≤ q) :
    lawV1E2 q N (2 * t + 1) = 0 ↔ (N ≤ 5 * t + 3 ∨ lawE q N (2 * t + 1) = 0)

/-! ### NODE H.43 [lemma] -/

axiom v4e2_vertex_condition {v₄ t : ℕ} (hv : 1 ≤ v₄) (h : 2 * v₄ < 2 * t + 1) :
    2 * v₄ + 1 ≤ 2 * t + 1

axiom v4e2_first_visible {v₄ t : ℕ} (hv : 1 ≤ v₄) (hvc : 2 * v₄ + 1 ≤ 2 * t + 1) :
    7 ≤ v₄ + 2 * (2 * t + 1)

axiom v4e2_needs_eight {v₄ t N : ℕ} (hv : 1 ≤ v₄) (hvc : 2 * v₄ + 1 ≤ 2 * t + 1)
    (hvis : v₄ + 2 * (2 * t + 1) ≤ N - 1) : 8 ≤ N

/-! ### NODE H.44 [lemma] -/

/-- The pin census at a slot of `F_q`-dimension `c`: the nonzero readable vectors of an
`F_q`-subspace of dimension `c`. -/
def pinCensus (q c : ℕ) : ℕ := q ^ c - 1

axiom pinCensus_genreE (q : ℕ) : pinCensus q 1 = q - 1

axiom pinCensus_genreF_interior (q : ℕ) : pinCensus q 2 = q ^ 2 - 1

axiom pinCensus_band_ne_interior {q : ℕ} (hq : 2 ≤ q) :
    pinCensus q 1 ≠ pinCensus q 2

/-! ### NODE H.45 [lemma] -/

/-- `#{unordered pairs of distinct nonzero elements}` over a `Q`-element field — the `SPLITEQ`
residual census. -/
def splitEqCensus (Q : ℕ) : ℕ := (Q - 1) * (Q - 2) / 2

/-- `#{monic irreducible quadratics}` over a `Q`-element field — the `INERT` residual census. -/
def inertCensus (Q : ℕ) : ℕ := Q * (Q - 1) / 2

axiom two_mul_splitEqCensus (Q : ℕ) : 2 * splitEqCensus Q = (Q - 1) * (Q - 2)

axiom two_mul_inertCensus (Q : ℕ) : 2 * inertCensus Q = Q * (Q - 1)

/-! ### NODE H.46 [lemma] (SPLIT-MANDATED into 2) -/

/-- The odd (`α₁`-borne) `dv`-heights of the `A₁` string at genre E. -/
def slotOdd (N h : ℕ) : Finset ℕ :=
  (Finset.Icc ((h + 1) / 2) (N - 1)).image (fun v => 2 * v + h)

/-- The even (`α₀`-borne) `dv`-heights of the `A₁` string at genre E. -/
def slotEven (N h : ℕ) : Finset ℕ :=
  (Finset.Icc (h + 1) (N - 1)).image (fun v => 2 * v)

axiom raggedBand_card (N t : ℕ) (hN : 2 * t + 2 ≤ N) :
    ((slotOdd N (2 * t + 1)).filter (fun m => 2 * N ≤ m)).card = t

axiom raggedBand_empty_of_h_one (N : ℕ) (hN : 2 ≤ N) :
    ((slotOdd N 1).filter (fun m => 2 * N ≤ m)) = ∅

/-! ### NODE H.47 [lemma] -/

axiom genh4B_aggregate_exp {N h : ℕ} (hfl : 2 * h + 1 ≤ N) :
    (N + h - 1) + (N - 1 - 2 * h) = 2 * N - h - 2

axiom und_exp_coincide_iff_h_one {N t : ℕ} (hN : 1 ≤ N) :
    N + ((2 * t + 1) - 1) / 2 = N + (2 * t + 1) - 1 ↔ t = 0

/-! ### NODE H.48 [lemma] -/

axiom genh4B_F_odd_exp {l k : ℕ} (hk : 1 ≤ k) :
    2 * ((2 * l + 1) / 2) + 2 * k - 1 = (2 * l + 1) + 2 * k - 2

axiom genh4B_F_even_sum (q N k : ℕ) (hq : 1 ≤ q) :
    q ^ (N + 2 * k - 1) + (q - 1) * q ^ (N + 2 * k - 1) = q ^ (N + 2 * k) ∨ N + 2 * k = 0

/-! ### NODE H.49 [lemma] -/

axiom mixed_six_childE_lt_six {k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h)
    (hlt : 2 * k + 2 * h < 6) : k = 1 ∧ h = 1

axiom mixed_six_stage_steeper {k h : ℕ} (hk : 1 ≤ k) (hst : 2 * k + 1 ≤ h) :
    8 ≤ 2 * k + 2 * h

axiom mixed_six_sameSide {k : ℕ} (hk : 1 ≤ k) : 6 ≤ 6 * k

axiom mixed_six_distinctSide {k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h) (hne : h ≠ k) :
    8 ≤ 2 * k + 4 * h

/-! ### NODE H.50 [lemma] -/

axiom tower_needs_eight {e f μ n : ℕ} (hef : 2 ≤ e * f) (hμ : 4 ≤ μ) (hn : e * f * μ ≤ n) :
    8 ≤ n

axiom depth_three_needs_sixteen {D μ₁ e₂ f₂ μ₂ n : ℕ} (hD : 2 ≤ D) (h2 : 2 ≤ e₂ * f₂)
    (hμ₂ : 4 ≤ μ₂) (h1 : e₂ * f₂ * μ₂ ≤ μ₁) (hn : D * μ₁ ≤ n) : 16 ≤ n

/-! ## §8 — THE SLOT / LIFT LAYER (H.51–H.58) — **the `H → B` split point**

GC-5: chapters B and E may consume H.51–H.58 by name and nothing else of chapter H. -/

/-! ### NODE H.51 [lemma] -/

axiom class_sep {h e : ℕ} (hcop : Nat.Coprime h e) {i i' : ℕ} (hi : i < e) (hi' : i' < e)
    (hmod : i * h % e = i' * h % e) : i = i'

axiom class_sep_bij {h e : ℕ} (hcop : Nat.Coprime h e) :
    Set.BijOn (fun i => i * h % e) (Finset.range e) (Finset.range e)

/-! ### NODE H.52 [lemma] -/

axiom slot_height_injective {h e : ℕ} (hcop : Nat.Coprime h e) {i i' v v' : ℕ}
    (hi : i < e) (hi' : i' < e) (heq : e * v + i * h = e * v' + i' * h) :
    i = i' ∧ v = v'

axiom slot_min_unique {h e : ℕ} (hcop : Nat.Coprime h e) (he : 0 < e)
    (v : ℕ → ℕ) {i i' : ℕ} (hi : i < e) (hi' : i' < e)
    (hmin : e * v i + i * h = e * v i' + i' * h) : i = i'

/-! ### NODE H.53 [lemma] — §15's fragile signature #2 (the `finrank`/`minpoly` shape) -/

axiom eta_independent {F K : Type*} [Field F] [Field K] [Algebra F K] {η : K}
    (hgen : (minpoly F η).natDegree = Module.finrank F K) (hint : IsIntegral F η)
    {f : ℕ} (hf : f = Module.finrank F K) (l : Fin f → F)
    (hsum : ∑ t : Fin f, algebraMap F K (l t) * η ^ (t : ℕ) = 0) :
    ∀ t, l t = 0

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
noncomputable def stageLift' {O : Type*} [CommRing O] (G : GenreDatum) (π : O)
    (i a : ℕ) (lift : ℕ → O) : Polynomial O :=
  ∑ s ∈ Finset.range G.f₁,
    Polynomial.C (lift s * π ^ (a - s * G.h)) * Polynomial.X ^ (i + G.e₁ * s)

/-! ### NODE H.55 [lemma] -/

axiom stageLift_index_lt (G : GenreDatum) {i s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁) :
    i + G.e₁ * s < G.keyDeg

axiom stageLift_integral (G : GenreDatum) {i a M s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁)
    (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M) : s * G.h ≤ a

axiom stageLift_height (G : GenreDatum) {i a M s : ℕ} (hi : i < G.e₁) (hs : s < G.f₁)
    (hM : i * G.h + G.e₁ * a = M) (hbig : G.keyDeg * G.h < M) :
    G.e₁ * (a - s * G.h) + (i + G.e₁ * s) * G.h = M

/-! ### NODE H.56 [lemma] -/

/-- The quotient identity: the `s`-th summand of `L_M(λ)` equals the normalizer `x^i π^a` times
`(x^{e₁} π^{−h})^s`, in the cleared form `π^{s h} · (summand) = n(M) · (x^{e₁})^s · lift s`. -/
axiom stageLift_summand_eq {O : Type*} [CommRing O] (G : GenreDatum) (π : O)
    {i a s : ℕ} (hsa : s * G.h ≤ a) (c : O) :
    (Polynomial.C (π ^ (s * G.h)) : Polynomial O) *
        (Polynomial.C (c * π ^ (a - s * G.h)) * Polynomial.X ^ (i + G.e₁ * s))
      = (Polynomial.C (π ^ a) * Polynomial.X ^ i) *
        (Polynomial.C c * Polynomial.X ^ (G.e₁ * s))

/-! ### NODE H.57 [lemma] -/

axiom wrap_div_mod (r i e : ℕ) (he : 0 < e) :
    r * i = r * i % e + e * (r * i / e) ∧ r * i % e < e

/-- The height bookkeeping behind the wrap: if `i·h + e·a = M` then
`r·M = (r·i % e)·h + e·(r·a + W·h)` with `W = r·i / e`. -/
axiom wrap_height {i a M h e r : ℕ} (he : 0 < e) (hM : i * h + e * a = M) :
    r * M = (r * i % e) * h + e * (r * a + (r * i / e) * h)

/-! ### NODE H.58 [lemma] -/

axiom divMod_bij (D r : ℕ) (hD : 0 < D) :
    Set.BijOn (fun p : ℕ × ℕ => p.1 + p.2 * D)
      (Finset.range D ×ˢ Finset.range r) (Finset.range (D * r))

axiom card_composedBasis (D r : ℕ) (hD : 0 < D) :
    (Finset.range D ×ˢ Finset.range r).card = D * r

/-! ## §9 — THE UNIT-PIVOT LAYER (H.59–H.62) -/

/-! ### NODE H.59 [def] — `TriangularUnitPivot` (real body) -/

/-- **Triangular with unit pivots.**  `Φ` solves each output slot as `unit × (its input slot) +
(a function of strictly earlier input slots)`.  This is the condition ANNEX R R2 identifies as the
missing displayed step of `GENIND-6(c)`: triangularity ALONE does not give surjectivity or constant
fibres over a truncated DVR (H.62). -/
structure TriangularUnitPivot {R : Type*} [CommRing R] {n : ℕ}
    (Φ : (Fin n → R) → (Fin n → R)) where
  /-- The pivots. -/
  pivot : Fin n → R
  /-- The strictly-earlier part. -/
  tail : (i : Fin n) → (Fin n → R) → R
  /-- Each pivot is a unit. -/
  pivot_isUnit : ∀ i, IsUnit (pivot i)
  /-- The tail at `i` depends only on coordinates `< i`. -/
  tail_lower : ∀ i v w, (∀ j : Fin n, j < i → v j = w j) → tail i v = tail i w
  /-- The displayed form. -/
  apply_eq : ∀ v i, Φ v i = pivot i * v i + tail i v

/-! ### NODE H.60 [theorem] — the back-substitution construction ([NEEDS-DERIVATION-EXPANSION]) -/

axiom TriangularUnitPivot.bijective {R : Type*} [CommRing R] {n : ℕ}
    {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) : Function.Bijective Φ

/-! ### NODE H.61 [lemma] — §15's fragile signature #4 (the `Fintype`/`Nat.card` mix) -/

axiom TriangularUnitPivot.card_fibre {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {n : ℕ} {Φ : (Fin n → R) → (Fin n → R)} (T : TriangularUnitPivot Φ) (P : Finset (Fin n))
    (t : Fin n → R) :
    Nat.card {v : Fin n → R // ∀ i ∈ P, Φ v i = t i}
      = Fintype.card R ^ (n - P.card)

/-! ### NODE H.62 [lemma] — the R2 counterexample (EXECUTED at the gate below) -/

/-- Codex's toy (`ANNEX R R2.0`): `(x, y) ↦ (x, (x+π)y)` mod `π²`, at `π = 2`, `R = ZMod 4`. -/
def codexToy (v : Fin 2 → ZMod 4) : Fin 2 → ZMod 4 := ![v 0, (v 0 + 2) * v 1]

axiom codexToy_not_surjective : ¬ Function.Surjective codexToy

axiom codexToy_fibre_not_constant :
    (Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![0, 0])).card = 2 ∧
    (Finset.univ.filter (fun v : Fin 2 → ZMod 4 => codexToy v = ![1, 0])).card = 1

/-! ## §10 — THE DRAINAGE-RATE CALCULUS (H.63–H.72) -/

/-! ### NODE H.63 [theorem] — the union bound (SPLIT-MANDATED into 2)

Parse check performed at this gate: Mathlib's `∏ x ∈ s, f` body parses at precedence 67 and `-` is
`infixl:65`, so `∏ i ∈ s, T i - ∏ i ∈ s, (T i - u i)` DOES split at the subtraction as intended
(the `∑ … , u i * ∏ …` on the right, at `*`'s level 70, does NOT split). No parenthesization added;
recorded because the reading is load-bearing and not obvious. -/

axiom prod_sub_prod_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (u T : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (huT : ∀ i ∈ s, u i ≤ T i) :
    ∏ i ∈ s, T i - ∏ i ∈ s, (T i - u i) ≤ ∑ i ∈ s, u i * ∏ j ∈ s.erase i, T j

/-! ### NODE H.64 [lemma] -/

axiom prod_sub_antitone {ι : Type*} (s : Finset ι) (u v T : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ u i) (huv : ∀ i ∈ s, u i ≤ v i) (hvT : ∀ i ∈ s, v i ≤ T i) :
    ∏ i ∈ s, (T i - v i) ≤ ∏ i ∈ s, (T i - u i)

/-! ### NODE H.65 [def] — `RateSpecies` (real body) -/

/-- **(A2-RATE)** — the species pinned onto `P(k)`'s fourth member (`ANNEX R R1.1`): a normalized
conservative complement decays with a POLYNOMIAL coefficient and an EXPONENTIAL deficit, with
constants depending on the degree data only. -/
def RateSpecies (Q : ℕ) (K : ℝ) (B c : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ M, 1 ≤ M → f M ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹

/-! ### NODE H.66 [lemma] -/

axiom RateSpecies.of_le {Q : ℕ} {K : ℝ} {B c : ℕ} {f g : ℕ → ℝ}
    (h : RateSpecies Q K B c f) (hg : ∀ M, 1 ≤ M → g M ≤ f M) : RateSpecies Q K B c g

axiom RateSpecies.mono {Q : ℕ} (hQ : 2 ≤ Q) {K K' : ℝ} {B B' c c' : ℕ} {f : ℕ → ℝ}
    (h : RateSpecies Q K B c f) (hK : K ≤ K') (hK0 : 0 ≤ K) (hB : B ≤ B') (hc : c ≤ c') :
    RateSpecies Q K' B' c' f

/-! ### NODE H.67 [theorem] -/

axiom rate_growing {Q : ℕ} (hQ : 2 ≤ Q) {K : ℝ} {B c D M N : ℕ} (hK : 0 ≤ K)
    (hD : 1 ≤ D) (hc : c ≤ M) (hDM : D + M = N) {ρ δ : ℝ}
    (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹)
    (hδ : δ ≤ K * (M : ℝ) ^ B * ((Q : ℝ) ^ (M - c))⁻¹) :
    ρ * δ ≤ K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - c))⁻¹

/-! ### NODE H.68 [theorem] -/

axiom rate_bounded {Q : ℕ} (hQ : 2 ≤ Q) {D M N c₀ : ℕ} (hD : 1 ≤ D) (hDM : D + M = N)
    (hM : M ≤ c₀) {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hρ : ρ ≤ ((Q : ℝ) ^ (D - 1))⁻¹) :
    ρ * δ ≤ ((Q : ℝ) ^ (N - c₀ - 1))⁻¹

/-! ### NODE H.69 [lemma] -/

axiom rate_sum_over_family {Q : ℕ} (hQ : 2 ≤ Q) {K : ℝ} {B c c₀ N m p r : ℕ} (hK : 0 ≤ K)
    (hN : 1 ≤ N) (g : Fin r → ℝ) (hg0 : ∀ i, 0 ≤ g i)
    (hg : ∀ i, g i ≤ K * (N : ℝ) ^ B * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹) :
    (p * N ^ m : ℝ) * ∑ i, g i
      ≤ (r * p : ℝ) * (N : ℝ) ^ m * (K * (N : ℝ) ^ B) * ((Q : ℝ) ^ (N - 1 - max c c₀))⁻¹

/-! ### NODE H.70 [theorem] — `undecidedSeq` is ANTITONE (SPLIT-MANDATED into 2)

Lands in `Uniformity.Density` (theorems about landed objects), NOT in `.Induction`. -/

axiom undecidedSet_preimage_subset {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] {n T W : ℕ} (h : T ≤ W) :
    undecidedSet O n W ⊆ coeffFactor (O := O) (n := n) h ⁻¹' undecidedSet O n T

axiom undecidedSeq_antitone {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (n : ℕ) :
    Antitone (undecidedSeq O n)

/-! ### NODE H.71 [theorem] — the lexicographic closure (SPLIT-MANDATED into 3) -/

/-- The three-leg recursion hypothesis of `GENIND.C′`, packaged so the induction can be stated. -/
structure RecursionLegs (Q m c : ℕ) (u : ℕ → ℕ → ℝ) where
  -- DEFECT D6: the blueprint writes `head alpha beta : ℕ → ℕ → ℝ` and `B' c' n₀ : ℕ`, which is NOT
  -- Lean 4 structure syntax — `f a b : T` declares ONE field `f` of type `(a : _) → (b : _) → T`,
  -- so the structure silently loses `alpha`, `beta`, `c'`, `n₀` and every later field breaks.
  -- Split one-name-per-field below; the intent is unambiguous from `hsplit`/`halpha`/`hbeta`.
  head : ℕ → ℕ → ℝ
  alpha : ℕ → ℕ → ℝ
  beta : ℕ → ℕ → ℝ
  K' : ℝ
  B' : ℕ
  c' : ℕ
  n₀ : ℕ
  hK' : 0 ≤ K'
  hsplit : ∀ D N, 1 ≤ N → u D N ≤ head D N + alpha D N + beta D N
  hu0 : ∀ D N, 0 ≤ u D N
  hhead : ∀ D N, 1 ≤ N → head D N ≤ ((Q : ℝ) ^ (N - 1))⁻¹
  halpha : ∀ D N, 1 ≤ N → alpha D N ≤
    ∑ k ∈ Finset.range n₀, ((Q : ℝ) - 1) * ((Q : ℝ) ^ (c * (k + 1)))⁻¹ * u D (N - m * (k + 1))
  hbeta : ∀ D N, 1 ≤ N → beta D N ≤ K' * (N : ℝ) ^ (m + B') * ((Q : ℝ) ^ (N - c' - 1))⁻¹
  -- DEFECT D7 (statement-level, NOT repaired here): `D` is unused in this field, so its type is
  -- uninferable and the blueprint's line does not elaborate; `(D N k : ℕ)` is annotated as the
  -- minimal semantics-preserving repair. The field is ALSO unsatisfiable at `N = 0` — see D7.
  hdesc : ∀ (D N k : ℕ), k < n₀ → 1 ≤ m * (k + 1) → N - m * (k + 1) < N

axiom rate_close {Q m c : ℕ} (hQ : 2 ≤ Q) (hc : 1 ≤ c) (hm : 1 ≤ m)
    {u : ℕ → ℕ → ℝ} (L : RecursionLegs Q m c u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ D, RateSpecies Q K (m + L.B' + 1) (L.c' + 1) (u D)

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

/-! ## §11 — THE σ DICTIONARY AND THE `(e, f)`-FORCING CHAIN (`μ = 2` ONLY) (H.73–H.79) -/

/-! ### NODE H.73 [def] — `StageLeaf` + `stageSigma` (real bodies; GC-4's dictionary pattern) -/

/-- The three decided leaf labels of a `μ = 2` stage read (`GENHN.C`; `SPLITEQ` and `SPLTAIL` share
`twoSided`'s σ-block, per the dictionary's own grouping). -/
inductive StageLeaf where
  | ram
  | twoSided
  | inert
  deriving DecidableEq, Fintype

/-- `GENHN.C`'s leaf dictionary, relative to the ambient. -/
def stageSigma (G : GenreDatum) : StageLeaf → FactorizationType
  | .ram      => ⟨{(2 * G.e₁, G.f₁)}⟩
  | .twoSided => ⟨{(G.e₁, G.f₁), (G.e₁, G.f₁)}⟩
  | .inert    => ⟨{(G.e₁, 2 * G.f₁)}⟩

/-! ### NODE H.74 [lemma] — GC-4's mandatory degree-conservation lemma -/

axiom stageSigma_degree (G : GenreDatum) (l : StageLeaf) :
    (stageSigma G l).degree = 2 * G.keyDeg

/-! ### NODE H.75 [lemma] -/

axiom stageSigma_genreE (t : ℕ) :
    stageSigma (genreE2 t) .ram = ⟨{(4, 1)}⟩ ∧
    stageSigma (genreE2 t) .twoSided = ⟨{(2, 1), (2, 1)}⟩ ∧
    stageSigma (genreE2 t) .inert = ⟨{(2, 2)}⟩

axiom stageSigma_degree_instances (t : ℕ) :
    (stageSigma (genreE2 t) .ram).degree = 4 ∧
    (stageSigma genreA2witness .ram).degree = 6 ∧
    (stageSigma genreD2bwitness .ram).degree = 4

/-! ### NODE H.76 [theorem] — the `(e, f)`-forcing chain (lands in `Uniformity.Density`) -/

axiom efPair_forced_of_dvd {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {g : Polynomial O} (hg : g.Monic) {e f : ℕ} (he : 1 ≤ e) (hf : 1 ≤ f)
    (hdeg : g.natDegree = e * f) {p : ℕ × ℕ} (hp : (typeOf g).data = {p})
    (hpe : e ∣ p.1) (hpf : f ∣ p.2) : p = (e, f)

/-! ### NODE H.77 [lemma] -/

axiom gcd_odd_of_odd {u e : ℕ} (hu : Odd u) : Odd (Nat.gcd u e)

axiom lcm_ram_value_group {u e : ℕ} (he : 1 ≤ e) (hu : Odd u) :
    Nat.lcm e (2 * e / Nat.gcd u e) = 2 * e

/-! ### NODE H.78 [def] -/

/-- `T(b)′`(iii)'s composed dictionary: the σ-composition FORMULA `(e, f) ↦ (e₁e₂·e_s, f₁f₂·f_s)` —
the part of the REFUTED `T(b)` that SURVIVES, applied to the composed-key pins. -/
def composedSigma (G : GenreDatum) (e₂ f₂ : ℕ) : StageLeaf → FactorizationType
  | .ram      => ⟨{(2 * (G.e₁ * e₂), G.f₁ * f₂)}⟩
  | .twoSided => ⟨{(G.e₁ * e₂, G.f₁ * f₂), (G.e₁ * e₂, G.f₁ * f₂)}⟩
  | .inert    => ⟨{(G.e₁ * e₂, 2 * (G.f₁ * f₂))}⟩

/-! ### NODE H.79 [lemma] -/

axiom composedSigma_degree (G : GenreDatum) (e₂ f₂ : ℕ) (l : StageLeaf) :
    (composedSigma G e₂ f₂ l).degree = 2 * (G.keyDeg * (e₂ * f₂))

axiom composedDeg_eq (G : GenreDatum) (e₂ f₂ : ℕ) :
    G.keyDeg * (e₂ * f₂) = (G.e₁ * e₂) * (G.f₁ * f₂)

/-! ## §12 — THE `n = 4` TEMPLATE (H.80–H.92) -/

/-! ### NODE H.80 [lemma] -/

open Polynomial in
axiom quartic_dev_E {R : Type*} [CommRing R] (s a₁ a₀ b₁ b₀ : R) :
    ((X ^ 2 - C s) ^ 2 + (C a₁ * X + C a₀) * (X ^ 2 - C s) + (C b₁ * X + C b₀))
      = X ^ 4 + C a₁ * X ^ 3 + C (a₀ - 2 * s) * X ^ 2 + C (b₁ - s * a₁) * X
        + C (b₀ - s * a₀ + s ^ 2)

/-! ### NODE H.81 [lemma] -/

open Polynomial in
axiom quartic_dev_F {R : Type*} [CommRing R] (p₁ p₀ a₁ a₀ b₁ b₀ : R) :
    ((X ^ 2 + C p₁ * X + C p₀) ^ 2 + (C a₁ * X + C a₀) * (X ^ 2 + C p₁ * X + C p₀)
        + (C b₁ * X + C b₀))
      = X ^ 4 + C (2 * p₁ + a₁) * X ^ 3 + C (p₁ ^ 2 + 2 * p₀ + a₁ * p₁ + a₀) * X ^ 2
        + C (2 * p₁ * p₀ + a₁ * p₀ + a₀ * p₁ + b₁) * X + C (p₀ ^ 2 + a₀ * p₀ + b₀)

/-! ### NODE H.82 [lemma] (SPLIT CANDIDATE) -/

axiom quartic_floors_E (t : ℕ) :
    (2 * t + 1 + 1) / 2 = t + 1 ∧ (2 * t + 1) + 1 = 2 * t + 2 ∧
    (3 * (2 * t + 1) + 1) / 2 = 3 * t + 2 ∧ 2 * (2 * t + 1) + 1 = 4 * t + 3

axiom quartic_node_E (t : ℕ) :
    min (2 * (t + 1) + (2 * t + 1)) (2 * (2 * t + 2)) = 2 * (2 * t + 1) + 1 ∧
    min (2 * (3 * t + 2) + (2 * t + 1)) (2 * (4 * t + 3)) = 4 * (2 * t + 1) + 1

/-! ### NODE H.83 [lemma] (SPLIT CANDIDATE) -/

axiom quartic_total_F {N k : ℕ} (hN : 4 * k + 1 ≤ N) :
    (N - k - 1) + (N - 2 * k - 1) + (N - 3 * k - 1) + (N - 4 * k - 1) + (10 * k + 4) = 4 * N

axiom quartic_node_F (k : ℕ) :
    min ((k + 1) + k) (2 * k + 1) = 2 * k + 1 ∧ min ((3 * k + 1) + k) (4 * k + 1) = 4 * k + 1

/-! ### NODE H.84 [lemma] — `w11_node_shape` retained (§15 rule 4 left it to discretion) -/

axiom w11_node_shape (S : ℕ) : 2 * S + 1 = 2 * S + 1 ∧ S + 1 = S + 1

axiom w11_node_E (h : ℕ) : (4 * h + 1, 2 * h + 1) = (2 * (2 * h) + 1, (2 * h) + 1)

axiom w11_node_F (k : ℕ) : (4 * k + 1, 2 * k + 1) = (2 * (2 * k) + 1, (2 * k) + 1)

/-! ### NODE H.85 [lemma] -/

axiom dv_parity_ne {h va vb : ℕ} (hh : Odd h) : 2 * va + h ≠ 2 * vb

axiom dv_parity_min_unique {h va vb : ℕ} (hh : Odd h) :
    min (2 * va + h) (2 * vb) = 2 * va + h ∨ min (2 * va + h) (2 * vb) = 2 * vb

/-! ### NODE H.86 [lemma] -/

axiom carry_height_gt {h dμ va : ℕ} (hh : 1 ≤ h) (hd : 2 * h + 1 ≤ dμ) (hva : h + 1 ≤ 2 * va) :
    dμ < min (2 * (dμ - h)) (2 * va + (dμ - h))

/-! ### NODE H.87 [lemma] — the carry cancellation, both characteristics -/

axiom carry_cancel {R : Type*} [CommRing R] {z s S₀ : R} (h : S₀ = z * s ^ 2) :
    S₀ + z * s ^ 2 - 2 * (z * s ^ 2) = 0

axiom carry_cancel_char_two {R : Type*} [CommRing R] (hR : (2 : R) = 0) (z s : R) :
    z * s ^ 2 + z * s ^ 2 = 0

axiom refine_kill_A₁ {R : Type*} [CommRing R] {S₁ s : R} (h : S₁ = -(2 * s)) : S₁ + 2 * s = 0

/-! ### NODE H.88 [lemma] — `CapBranch` + `capBranch` (real bodies) + the trichotomy -/

/-- The three exits of the `dv0 = N` boundary read, with PAIRWISE-DISJOINT antecedents
(`GENH4-CAP`, as re-derived at `[r3, PE3 MINOR 1]` from `GENH4-3(i)`'s own "else (ii)"). -/
inductive CapBranch where | twoSided | ram | und
  deriving DecidableEq

def capBranch (N w : ℕ) : CapBranch :=
  if 2 * w < N then .twoSided else if N % 2 = 1 then .ram else .und

axiom capBranch_trichotomy (N w : ℕ) :
    (capBranch N w = .twoSided ↔ 2 * w < N) ∧
    (capBranch N w = .ram ↔ (N ≤ 2 * w ∧ N % 2 = 1)) ∧
    (capBranch N w = .und ↔ (N ≤ 2 * w ∧ N % 2 = 0))

axiom capBranch_seven_three : capBranch 7 3 = .twoSided

/-! ### NODE H.89 [lemma] -/

axiom consulted_ram {u h N : ℕ} (hh : 1 ≤ h) (hu : u ≤ 2 * N - 1) (hN : 1 ≤ N) :
    (u - h) / 2 ≤ N - 1

axiom consulted_twoSided {w N : ℕ} (hw : w ≤ 2 * N - 2) : w / 2 ≤ N - 1

axiom consulted_refine {dμ N : ℕ} (hd : 2 * dμ ≤ 2 * N - 2) : dμ ≤ N - 1

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

/-! ### NODE H.90 [lemma] -/

axiom invariant_even {dμ h : ℕ} (hd : 2 * h + 2 ≤ dμ) : h + 1 ≤ dμ / 2

axiom invariant_odd {dμ h : ℕ} (hd : 2 * h + 1 ≤ dμ) : (h + 1) / 2 ≤ (dμ - h) / 2

/-! ### NODE H.91 [lemma] — `LeafE` + `leafFactorE` (real bodies) -/

/-- The six decided/undecided leaf labels of a genre-E stage read, and their letter/census factors
(`THEOREM GENH4.A`'s four-slot model, §S6.1's table). -/
inductive LeafE where | ram | twoSided | splitEq | inert | splTail | und
  deriving DecidableEq, Fintype

def leafFactorE (q : ℕ) : LeafE → ℕ
  | .ram      => q - 1
  | .twoSided => (q - 1) ^ 2
  | .splitEq  => splitEqCensus q
  | .inert    => inertCensus q
  | .splTail  => q - 1
  | .und      => 1

axiom leafFactorE_pos {q : ℕ} (hq : 3 ≤ q) (l : LeafE) : 0 < leafFactorE q l

/-! ### NODE H.92 [lemma] -/

axiom subset_sum_pow {ι : Type*} [DecidableEq ι] (D : Finset ι) (L : ℕ) :
    ∑ H ∈ D.powerset, L ^ H.card = (1 + L) ^ D.card

axiom bracket_telescope_E (q δ : ℕ) (hq : 1 ≤ q) :
    1 + ∑ j ∈ Finset.range δ, (q - 1) * q ^ j = q ^ δ

axiom macroscopic_rate (q Δ μ : ℕ) : q ^ (2 * (Δ * μ)) = (q ^ 2) ^ (Δ * μ)

/-! ## §13 — THE ASSEMBLY (H.93–H.99) -/

/-! ### NODE H.93 [def] — `A1Cell` + its three derived defs (real bodies; SPLIT-MANDATED into 2) -/

/-- One cell of an `(A1)`-admissible family: a shifted product of arithmetic progressions in `ℕ ^ r`
with an affine positive-coefficient exponent, an affine visibility form, a coefficient, and a
σ-label.  **The σ-label field is W-12's r4 STRENGTHENING of `(A1)`** — see the note. -/
structure A1Cell (r : ℕ) where
  /-- Per-coordinate offset. -/
  offset : Fin r → ℕ
  /-- Per-coordinate stride (positive). -/
  stride : Fin r → ℕ
  stride_pos : ∀ i, 0 < stride i
  /-- The exponent's positive coefficients and constant. -/
  expCoeff : Fin r → ℕ
  expCoeff_pos : ∀ i, 0 < expCoeff i
  expConst : ℕ
  /-- The visibility form. -/
  visCoeff : Fin r → ℕ
  visConst : ℕ
  /-- The family's `q`-independent coefficient. -/
  coeff : ℕ
  /-- **The σ-label** (W-12 r4). -/
  σ : FactorizationType

/-- The parameter locus of a cell: the shifted product of arithmetic progressions. -/
def A1Cell.locus {r : ℕ} (C : A1Cell r) : Set (Fin r → ℕ) :=
  {p | ∀ i, ∃ t : ℕ, p i = C.offset i + C.stride i * t}

/-- The cell's exponent at a parameter point. -/
def A1Cell.exp {r : ℕ} (C : A1Cell r) (p : Fin r → ℕ) : ℕ :=
  C.expConst + ∑ i, C.expCoeff i * p i

/-- An `(A1)`-admissible family is a finite list of cells. -/
def A1Family (r : ℕ) : Type := List (A1Cell r)

/-! ### NODE H.94 [theorem] — closure of `(A1)` (SPLIT-MANDATED into 3); **DEFECT D5**

`prod`'s body is the PROOF field's, verbatim in content (`Fin.append` on the four vectors).
`deltaSubst`'s body is a STUB-SIDE DETERMINATION: the blueprint pins only the exponent data, and
the choice below (transport the visibility form by the same substitution, keep `offset`, `stride`,
`coeff`, `σ`) is the one under which the signed `deltaSubst_exp` holds. See D5. -/

/-- (i) The product of two cells. -/
def A1Cell.prod {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) : A1Cell (r₁ + r₂) where
  offset := Fin.append C.offset D.offset
  stride := Fin.append C.stride D.stride
  stride_pos := by
    refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · simpa [Fin.append_left] using C.stride_pos k
    · simpa [Fin.append_right] using D.stride_pos k
  expCoeff := Fin.append C.expCoeff D.expCoeff
  expCoeff_pos := by
    refine Fin.addCases (fun k => ?_) (fun k => ?_)
    · simpa [Fin.append_left] using C.expCoeff_pos k
    · simpa [Fin.append_right] using D.expCoeff_pos k
  expConst := C.expConst + D.expConst
  visCoeff := Fin.append C.visCoeff D.visCoeff
  visConst := C.visConst + D.visConst
  coeff := C.coeff * D.coeff
  σ := ⟨C.σ.data + D.σ.data⟩

axiom A1Cell.prod_exp {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) (p : Fin (r₁ + r₂) → ℕ) :
    (C.prod D).exp p = C.exp (fun i => p (Fin.castAdd r₂ i)) + D.exp (fun j => p (Fin.natAdd r₁ j))

axiom A1Cell.prod_σ_degree {r₁ r₂ : ℕ} (C : A1Cell r₁) (D : A1Cell r₂) :
    (C.prod D).σ.degree = C.σ.degree + D.σ.degree

/-- (iii) The `δ`-substitution `w₂ = w₁ + 1 + δ` of `W-12` §S3.4's 2SIDED instance. -/
def A1Cell.deltaSubst (C : A1Cell 2) : A1Cell 2 where
  offset := C.offset
  stride := C.stride
  stride_pos := C.stride_pos
  expCoeff := ![C.expCoeff 0 + C.expCoeff 1, C.expCoeff 1]
  expCoeff_pos := by
    have h0 := C.expCoeff_pos 0
    have h1 := C.expCoeff_pos 1
    intro i
    fin_cases i
    · show 0 < C.expCoeff 0 + C.expCoeff 1
      omega
    · show 0 < C.expCoeff 1
      omega
  expConst := C.expConst + C.expCoeff 1
  visCoeff := ![C.visCoeff 0 + C.visCoeff 1, C.visCoeff 1]
  visConst := C.visConst + C.visCoeff 1
  coeff := C.coeff
  σ := C.σ

axiom A1Cell.deltaSubst_exp (C : A1Cell 2) (w δ : ℕ) :
    (C.deltaSubst).exp ![w, δ] = C.exp ![w, w + 1 + δ]

/-! ### NODE H.95 [def] — `InductionPackage` (real body; lands in `Uniformity.Density`)

`Induction.RateSpecies` is written `RateSpecies` here — the LeanspecH namespace flattening. -/

/-- **`P(n)`** — the degree-`n` package `{history-resolved exact menu + finite (A1)-admissible
aggregate menu + (A0) + exact-complement (A2)}` of `THEOREM GENIND.B`, in the form `leanfinal`'s API
can state: a covering menu, the certified densities, and the complement's RATE species
(`(A2-RATE)`, `ANNEX R R1.1`). -/
def InductionPackage (n : ℕ) : Prop :=
  ∃ (K : ℝ) (B c : ℕ), 0 ≤ K ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      (∃ S : Finset FactorizationType, CoveringMenu O n S) ∧
        RateSpecies (residueCard O) K B c (undecidedSeq O n)

/-! ### NODE H.96 [theorem] -/

axiom package_two : InductionPackage 2

/-! ### NODE H.97 [theorem] — `package_three_of_rate` (§15 rule 3)

NOT SIGNED, per §15 rule 3 (the blueprint declares it a defect and adopts the rate form):
```
theorem package_three_of_drainage (hd : DrainageAt 3) : InductionPackage 3
```
The adopted form, from H.97's ⚠ SIGNATURE NOTE (blueprint line 5923), is signed below. -/

axiom package_three_of_rate
    (hrate : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      RateSpecies (residueCard O) 1 1 0 (undecidedSeq O 3)) :
    InductionPackage 3

/-! ### NODE H.98 [theorem] — the capstone, conditionally -/

/-- `GENIND.B` Step 5: the package's `(A2)` member delivers drainage at every degree. -/
axiom drainage_of_package (hp : ∀ n, InductionPackage n) : ∀ n, DrainageAt n

/-- The capstone, assembled: certified densities + package ⟹ `UniformityStatement`. -/
axiom uniformity_of_package (hdec : UniformityStatementDecided)
    (hp : ∀ n, InductionPackage n) : UniformityStatement

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

/-! ### THE H.72 REFUTATION, MACHINE-CHECKED — and the `StageInterface` witness F2 asks for

Two artifacts the blueprint does not have. `stageIfaceE` is a genuine `StageInterface` instance (F2:
the chapter exhibits none, though §3's design note claims two), at genre E with `stageLoss = 0` — the
`EFF.GENIND.199` exemption the design note names. Instantiating H.72's signed inequality at it gives
`4 ≥ 8`, so H.72 is FALSE as signed (DEFECT D4) and is withdrawn above rather than signed. -/

/-- A genuine `StageInterface` instance: genre E at `t = 0` (`(Q,e₁,f₁,μ,h) = (2,2,1,2,1)`), window
`N = 2`, entry height `H = 0`, side length `S = 4`, `stageLoss = 0`. This is the non-vacuity witness
F2 records as missing from the chapter; it also makes the H.72 refutation below a statement about a
NON-EMPTY hypothesis. -/
def stageIfaceE : StageInterface (genreE2 0) 2 0 4 where
  stageWindow := 2
  stageLoss := 0
  entryCodim := 0
  slack := 0
  bracket := fun κ => 2 ^ (2 * κ - 1)
  drainFrac := fun _ => 0
  stageSigma := stageSigma (genreE2 0) .ram
  hS := by decide
  hwin := by decide
  hprice := by decide
  hbracket := by
    intro κ hκ
    have hc : (clusterC (genreE2 0).μ + 1) * κ = 2 * κ - 1 + 1 := by
      simp [clusterC, genreE2]
      omega
    have hsc : (genreE2 0).stageCard = 2 := by decide
    rw [hc, hsc, pow_succ]
    ring
  hdrain_nonneg := by intro M; norm_num
  hdrain_le_one := by intro M; norm_num
  hsigma := by intro _; decide

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

Status at this line: chapter H's stub gate is COMPLETE. 188 of the 190 signable declarations are
landed (H.01 … H.98), one file, `namespace LeanspecH`, no `sorry`, `autoImplicit` off, three
executed gate blocks green. Nothing is outstanding IN THIS FILE.

The outstanding items are all BLUEPRINT-side, and per §15 rule 5 they are recorded here and
repaired there (dated append), never patched in `leanspec`:

* **Must be decided BEFORE the fleet fires on the affected node.** D4 — H.72 `rate_lossPriced` is
  REFUTED; adopt CANDIDATE A or B (both verified) and re-derive `(C2Q.1)`. D8 — H.89
  `band_not_consulted` is REFUTED; add `1 ≤ N` or `1 ≤ m`. D7 — H.71 `RecursionLegs.hdesc` is
  unsatisfiable at `N = 0`, which empties the structure; add `1 ≤ N →`. D5 — H.94
  `A1Cell.deltaSubst`'s body is a stub-side determination and needs confirming.
* **Mechanical, already cured here, worth fixing in the blueprint text.** D1 (H.23's `if` → `if h :`
  plus `decreasing_by`), D2 (H.18's `decreasing_by`), D3 (H.06's mathlib name), D6 (H.71's
  multi-name fields), O1 (order `H.13` before `H.09`).
* **Findings.** F1 (σ VALUES are not machine-checkable at any gate — degree only). F2 (the chapter
  exhibits no `StageInterface`; one is built here). -/

end LeanspecH
