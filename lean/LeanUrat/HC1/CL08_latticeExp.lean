/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.CL07_heightLattice

/-!
# HC1.CL08_latticeExp — LatticeExp + wE + the four carrier laws (BP5 CL-08)

**Unit CL-08** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4; §3.2
displays (7) and "The carrier laws for (7)"; risk R-8).

**Informal statement.** The lattice-supported graded expansion space
`LatticeExp T = { B : ∀ γ : ℚ, T.grQ γ // ∀ γ, B γ ≠ 0 → ∃ n : ℕ, γ = n/strTop }`
(display (7)) is an AddCommGroup (componentwise — the support condition is closed
under `+`, `−`, `0`), carries the least-populated-level weight `wE` and the
evaluation class map `evalE`, and `(LatticeExp T, T.grQ, wE, evalE)` satisfies the
four `GradedCarrierR` laws — packaged as `gradedExpCarrier T : GradedCarrierR p`
with `Gr := T.grQ` (the non-vacuity pin CL-09 re-exposes as `packE_gr_pin`).

**Proof sketches (per law, blueprint §3.2).**
* `CL08_wE_add` (w_add): the least populated level of `B + B'` is ≥ the min of the
  two leasts (componentwise addition: below both leasts every component is 0).
* `CL08_evalE_add` (inγ_add): evaluation is additive UNCONDITIONALLY — stronger than
  the law; the structure field discards the two weight hypotheses.
* `CL08_evalE_kills` (inγ_kills): below the least populated level every component is
  0 — minimality of `Nat.find` on lattice points + the support condition off-lattice.
* `CL08_evalE_detects` (inγ_detects): at `wE B` the component is nonzero — the
  `Nat.find` spec.
* AddCommGroup closure legs: `(B+B') γ ≠ 0 → B γ ≠ 0 ∨ B' γ ≠ 0`, `(-B) γ ≠ 0 →
  B γ ≠ 0`, `0 γ = 0` — elementary.

**E-phase resolutions recorded.**
* **R-8 resolution (this writer's pick, recorded per the blueprint's charge).**
  `wE` is defined by dichotomy on `h : ∃ n : ℕ, B (n/strTop) ≠ 0` with
  `Nat.find h` (Classical decidability via `open scoped Classical`; the populated
  ℕ-set needs NO upper bound — nonemptiness suffices for `Nat.find`). The
  blueprint's `if h : B = 0 then ⊤ else …` clause is replaced by this EQUIVALENT
  ∃-dichotomy (equivalent BY the support condition: the ∃-form fails iff every
  component vanishes iff B = 0): the `B = 0` form would need a separate existence
  lemma INSIDE the def body, i.e. a sorried term the value depends on at E-phase.
  The `sInf`-on-ℚ fallback (R-8) was NOT needed — the WithTop ℚ plumbing here is a
  single coercion. Any later change of `wE`'s body is a DEFINITION change
  (fence-flagged), including a switch to the fallback.
* The AddCommGroup instance is given directly on the display-(7) subtype
  (componentwise data, law fields sorried for the prover) rather than through an
  `AddSubgroup` of the Pi group — keeps `LatticeExp` LITERALLY display (7) and
  keeps `(B + B').1 γ = B.1 γ + B'.1 γ` definitional. SPLIT RULE watch: the
  instance is 3 data + 5 law fields; if its proof pass exceeds ~40 lines the prover
  spins it off as its own unit per the CL-08 split rule.
* The four laws are emitted as STANDALONE named theorems (sorry bodies) and the
  `gradedExpCarrier` structure consumes them — so the prover closes one obligation
  at a time and the structure itself carries no direct sorry.

**Deps.** CL-07 (LAT: the lattice/divisibility arithmetic behind kills/detects).
difficulty: routine-opus (fiddly WithTop bookkeeping, no ideas). Size: ~120.
hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open scoped Classical

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **Display (7)**: the lattice-supported graded expansion space — functions picking
one class in every graded piece, supported on the nonnegative `(1/strTop)`-lattice. -/
def LatticeExp (T : Tower p F) : Type :=
  { B : ∀ γ : ℚ, T.grQ γ // ∀ γ, B γ ≠ 0 → ∃ n : ℕ, γ = (n : ℚ) / (T.strTop : ℚ) }

/-- Componentwise zero (the support condition holds vacuously). -/
noncomputable instance instLatticeExpZero (T : Tower p F) : Zero (LatticeExp T) :=
  ⟨⟨fun _ => 0, by intro γ h; exact absurd rfl h⟩⟩

/-- Componentwise addition (the support condition is closed under `+`). -/
noncomputable instance instLatticeExpAdd (T : Tower p F) : Add (LatticeExp T) :=
  ⟨fun B B' => ⟨fun γ => B.1 γ + B'.1 γ, by
    intro γ h
    have h' : B.1 γ + B'.1 γ ≠ 0 := h
    by_cases hB : B.1 γ = 0
    · by_cases hB' : B'.1 γ = 0
      · exact absurd (show B.1 γ + B'.1 γ = 0 by rw [hB, hB', add_zero]) h'
      · exact B'.2 γ hB'
    · exact B.2 γ hB⟩⟩

/-- Componentwise negation (the support condition is closed under `−`). -/
noncomputable instance instLatticeExpNeg (T : Tower p F) : Neg (LatticeExp T) :=
  ⟨fun B => ⟨fun γ => -(B.1 γ), by
    intro γ h
    exact B.2 γ (neg_ne_zero.mp h)⟩⟩

/-- Componentwise AddCommGroup on `LatticeExp` (display (7)'s "AddCommGroup:
componentwise"; the three closure legs above and the five laws here are the sorried
Prop obligations — data honest). -/
noncomputable instance instLatticeExpAddCommGroup (T : Tower p F) :
    AddCommGroup (LatticeExp T) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intro a b c; apply Subtype.ext; funext γ; exact add_assoc (a.1 γ) (b.1 γ) (c.1 γ)
  zero_add := by
    intro a; apply Subtype.ext; funext γ; exact zero_add (a.1 γ)
  add_zero := by
    intro a; apply Subtype.ext; funext γ; exact add_zero (a.1 γ)
  neg_add_cancel := by
    intro a; apply Subtype.ext; funext γ; exact neg_add_cancel (a.1 γ)
  add_comm := by
    intro a b; apply Subtype.ext; funext γ; exact add_comm (a.1 γ) (b.1 γ)

/-- **wE** (display (7)): the least populated lattice level `n/strTop` (via
`Nat.find` on the ∃-form — R-8 resolution in the file header), `⊤` when no level is
populated (⟺ `B = 0` by the support condition). -/
noncomputable def wE (T : Tower p F) (B : LatticeExp T) : WithTop ℚ :=
  if h : ∃ n : ℕ, B.1 ((n : ℚ) / (T.strTop : ℚ)) ≠ 0 then
    (((Nat.find h : ℚ) / (T.strTop : ℚ) : ℚ) : WithTop ℚ)
  else ⊤

/-- **evalE** (display (7)): the class map — evaluation of the expansion at `γ`. -/
def evalE (T : Tower p F) (γ : ℚ) (B : LatticeExp T) : T.grQ γ := B.1 γ

/-! ## Private toolkit: strTop positivity + the `wE` upper-bound at a populated level. -/

private lemma cl08_strTop_pos (T : Tower p F) : 0 < T.strTop := by
  have haux : ∀ n : ℕ, 0 < T.strAux n := by
    intro n
    induction n with
    | zero => norm_num [Tower.strAux]
    | succ k ih =>
      rw [Tower.strAux]
      apply Nat.mul_pos ih
      split
      · exact (T.stg _).he
      · exact Nat.one_pos
  rw [Tower.strTop, Tower.str]
  exact Nat.mul_pos (haux _) (T.stg (Fin.last T.K)).he

/-- If `B` is populated at the lattice level `n/strTop`, then `wE T B ≤ n/strTop`. -/
private lemma cl08_wE_le (T : Tower p F) (B : LatticeExp T) (n : ℕ)
    (hn : B.1 ((n : ℚ) / (T.strTop : ℚ)) ≠ 0) :
    wE T B ≤ (((n : ℚ) / (T.strTop : ℚ) : ℚ) : WithTop ℚ) := by
  have hstrpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast cl08_strTop_pos T
  have hex : ∃ m : ℕ, B.1 ((m : ℚ) / (T.strTop : ℚ)) ≠ 0 := ⟨n, hn⟩
  rw [wE, dif_pos hex]
  have hc : (Nat.find hex : ℚ) ≤ (n : ℚ) := by
    have hle : Nat.find hex ≤ n := Nat.find_le hn
    exact_mod_cast hle
  have hle : (Nat.find hex : ℚ) / (T.strTop : ℚ) ≤ (n : ℚ) / (T.strTop : ℚ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hc (le_of_lt (inv_pos.mpr hstrpos))
  exact_mod_cast hle

/-- Carrier law `w_add`: the least populated level of a componentwise sum is at least
the min of the two least populated levels. -/
theorem CL08_wE_add (T : Tower p F) (B B' : LatticeExp T) :
    min (wE T B) (wE T B') ≤ wE T (B + B') := by
  by_cases h3 : ∃ n : ℕ, (B + B').1 ((n : ℚ) / (T.strTop : ℚ)) ≠ 0
  · have hrhs : wE T (B + B') = (((Nat.find h3 : ℚ) / (T.strTop : ℚ) : ℚ) : WithTop ℚ) := by
      rw [wE, dif_pos h3]
    rw [hrhs]
    have hne : (B + B').1 ((Nat.find h3 : ℚ) / (T.strTop : ℚ)) ≠ 0 := Nat.find_spec h3
    have hval : (B + B').1 ((Nat.find h3 : ℚ) / (T.strTop : ℚ))
        = B.1 ((Nat.find h3 : ℚ) / (T.strTop : ℚ))
          + B'.1 ((Nat.find h3 : ℚ) / (T.strTop : ℚ)) := rfl
    rw [hval] at hne
    by_cases hB : B.1 ((Nat.find h3 : ℚ) / (T.strTop : ℚ)) = 0
    · have hB' : B'.1 ((Nat.find h3 : ℚ) / (T.strTop : ℚ)) ≠ 0 :=
        fun h => hne (by rw [hB, h, add_zero])
      exact le_trans (min_le_right _ _) (cl08_wE_le T B' (Nat.find h3) hB')
    · exact le_trans (min_le_left _ _) (cl08_wE_le T B (Nat.find h3) hB)
  · have hrhs : wE T (B + B') = ⊤ := by rw [wE, dif_neg h3]
    rw [hrhs]; exact le_top

/-- Carrier law `inγ_add`, UNCONDITIONAL form (stronger than the `GradedCarrierR`
field, which carries two weight hypotheses this instance never needs): evaluation is
additive. -/
theorem CL08_evalE_add (T : Tower p F) (γ : ℚ) (B B' : LatticeExp T) :
    evalE T γ (B + B') = evalE T γ B + evalE T γ B' := rfl

/-- Carrier law `inγ_kills`: strictly below the least populated level every component
vanishes (Nat.find minimality on-lattice; the support condition off-lattice). -/
theorem CL08_evalE_kills (T : Tower p F) (γ : ℚ) (B : LatticeExp T)
    (hlt : (γ : WithTop ℚ) < wE T B) : evalE T γ B = 0 := by
  by_contra hne
  have hBγ : B.1 γ ≠ 0 := hne
  obtain ⟨n, hn⟩ := B.2 γ hBγ
  have hBn : B.1 ((n : ℚ) / (T.strTop : ℚ)) ≠ 0 := by rw [← hn]; exact hBγ
  have hb := cl08_wE_le T B n hBn
  rw [← hn] at hb
  exact absurd hlt (not_lt.mpr hb)

/-- Carrier law `inγ_detects`: at the least populated level the component is nonzero
(the Nat.find spec). -/
theorem CL08_evalE_detects (T : Tower p F) (γ : ℚ) (B : LatticeExp T)
    (hw : wE T B = (γ : WithTop ℚ)) : evalE T γ B ≠ 0 := by
  by_cases hex : ∃ n : ℕ, B.1 ((n : ℚ) / (T.strTop : ℚ)) ≠ 0
  · rw [wE, dif_pos hex] at hw
    have hval : B.1 ((Nat.find hex : ℚ) / (T.strTop : ℚ)) ≠ 0 := Nat.find_spec hex
    have hγeq : γ = (Nat.find hex : ℚ) / (T.strTop : ℚ) := by exact_mod_cast hw.symm
    rw [hγeq]; exact hval
  · rw [wE, dif_neg hex] at hw
    exact absurd hw.symm WithTop.coe_ne_top

/-- **The graded-expansion carrier** (display (7) packaged): `Coeff := LatticeExp T`,
`Gr := T.grQ` — THE non-vacuity pin (CL-09's `packE_gr_pin` is `rfl` on this field) —
with weight `wE` and class map `evalE`, laws by the four theorems above. -/
noncomputable def gradedExpCarrier (T : Tower p F) : GradedCarrierR p where
  Coeff := LatticeExp T
  Gr := T.grQ
  w := wE T
  inγ := fun γ B => evalE T γ B
  w_add := CL08_wE_add T
  inγ_add := fun γ B B' _ _ => CL08_evalE_add T γ B B'
  inγ_kills := CL08_evalE_kills T
  inγ_detects := CL08_evalE_detects T

end LeanUrat.HC1

#print axioms LeanUrat.HC1.gradedExpCarrier
