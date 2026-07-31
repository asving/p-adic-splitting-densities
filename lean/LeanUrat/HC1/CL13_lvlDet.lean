/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.CL12_nclAssembly
import LeanUrat.HC1.T4_slotMinHt

/-!
# HC1.CL13_lvlDet — LVL-DET: level detection in the graded piece (BP5 CL-13)

**Unit CL-13** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4; §3.2
display (9)). Downstream of the NCL gate (CL-10 → CL-11 → CL-12 → THIS): if NCL
falls, this falls with it.

**Informal statement (display (9)).** For `y ≠ 0` supported inside the (finite)
level set `levelSet b γ`: `T.inGr γ (T.slotCoeff b y) ≠ 0` — the class of the slot
coefficient in the height-γ graded piece is DETECTED, not just the polynomial
nonzero. This is the lemma CL-14's (i-b) minimality contradiction reads at every
lower populated height.

**Proof sketch (LVL-DET = NCL + T4 + T6-detects).** NCL (`CL12_ncl`) gives
`T.slotCoeff b y ≠ 0`; `T4_slotMinHt` on `y` (its `hfin` from T7's
`levelSet_finite'`, its `hsupp` from the level-set support, and every support
height = γ) pins `T.wQ (T.slotCoeff b y) = γ` EXACTLY (the attained minimum over a
constant-height support — no weight jump possible); then
`(T6_carrierLaws T).2`'s `inγ_detects` leg gives `T.inGr γ … ≠ 0`. On-lattice note:
the support is nonempty, so `γ = ht c` for a coordinate and CL-07's LAT + T3 put
`strTop·γ ∈ ℤ` — `inGr`'s lattice dif-condition is satisfiable, no extra
hypothesis.

**E-phase resolutions recorded.**
* Display (9)'s ŷ-extension form is stated on full-domain assignments with
  level-set support, EXACTLY as CL-12 (and the CL-10 probe) state it — so the
  chain composes without re-indexing through the subtype.
* Statement-minimal imports: the proof-time deps `T4_slotMinHt`, `T6_carrierLaws`,
  `T7_alphabetSpan` (for `levelSet_finite'` — private there; re-derive or route via
  T12's boxes), `T3_htChainWeight`, and `CL07_heightLattice` are NOT imported here
  at E-phase; the prover adds them (statement needs only DefsCar, via CL-12's
  chain).

**PROVER NOTES (as-built, 2026-07-30).**
* Proof-time imports added: `T4_slotMinHt` (T12/T6 arrive transitively via CL-12
  and T4). The `levelSet_finite` copy rides T12's box exactly as in CL-12.
* `inγ_detects` is packaged in `T6_carrierLaws` ONLY on the `CoeffTop` subtype;
  `slotCoeff` need not live there (the top slot is unbounded), so the detects
  argument is COPIED from T6's leg-4 proof body onto raw polynomials
  (`cl13_wQ_detects` below) — the original proof never uses the subtype bound.
* CL-07 is NOT consumed: the on-lattice fact is delivered by T4's exact weight pin
  (`wQ = γ` forces the lattice condition inside the detects computation), as the
  header's on-lattice note anticipated.

**Deps.** CL-12 (+ T4/T6/T3/T7/CL-07 at proof time). difficulty: routine-opus.
Size: ~35. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## Private toolkit (copies: T6's quotient plumbing + the level-set finiteness) -/

private lemma cl13_strTop_pos (T : Tower p F) : 0 < T.strTop := by
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

private lemma cl13_inGr_on (T : Tower p F) {γ : ℚ} (honL : T.onLattice γ) (f : Polynomial ℤ_[p])
    (hf : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w f) :
    T.inGr γ f = Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge (⌊(T.strTop : ℚ) * γ⌋)) := by
  rw [Tower.inGr, dif_pos ⟨honL, hf⟩]

private lemma cl13_mk_eq_zero_iff (T : Tower p F) (m : ℤ) (f : Polynomial ℤ_[p])
    (hf : f ∈ T.side.ge m) :
    (Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge m) : T.side.grPiece m) = 0
      ↔ (↑m : WithTop ℤ) < T.side.w f := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

/-- Weight detection on RAW polynomials (T6's `inγ_detects` leg, copied off the
`CoeffTop` subtype — the original argument never uses the degree bound). -/
private lemma cl13_wQ_detects (T : Tower p F) (γ : ℚ) (f : Polynomial ℤ_[p])
    (heq : T.wQ f = (γ : WithTop ℚ)) : T.inGr γ f ≠ 0 := by
  have hSpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast cl13_strTop_pos T
  cases hw : T.side.w f with
  | top =>
    exfalso
    simp only [Tower.wQ, hw, WithTop.map_top] at heq
    exact (by simp : (⊤ : WithTop ℚ) ≠ ↑γ) heq
  | coe k =>
    simp only [Tower.wQ, hw, WithTop.map_coe] at heq
    have hSne : (T.strTop : ℚ) ≠ 0 := ne_of_gt hSpos
    have hkg : (k : ℚ) / (T.strTop : ℚ) = γ := by exact_mod_cast heq
    have hstg : (T.strTop : ℚ) * γ = (k : ℚ) := by rw [← hkg]; field_simp
    have hfloor : ⌊(T.strTop : ℚ) * γ⌋ = k := by rw [hstg]; exact Int.floor_intCast k
    have honL : T.onLattice γ := by
      show (↑(⌊(T.strTop : ℚ) * γ⌋) : ℚ) = (T.strTop : ℚ) * γ
      rw [hfloor, hstg]
    have hle : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) ≤ T.side.w f := by
      rw [hfloor, hw]
    rw [cl13_inGr_on T honL _ hle]
    intro hzero
    have hlt : (↑(⌊(T.strTop : ℚ) * γ⌋) : WithTop ℤ) < T.side.w f :=
      (cl13_mk_eq_zero_iff T (⌊(T.strTop : ℚ) * γ⌋) f hle).mp hzero
    rw [hfloor, hw] at hlt
    exact absurd hlt (lt_irrefl _)

private lemma cl13_kappa_nonneg (T : Tower p F) (r : Fin (T.K + 1)) : 0 ≤ T.kappa r := by
  rw [Tower.kappa]
  positivity

/-- The level set is finite (copy of C2_TYPa's private `levelSet_finite`, via T12's box). -/
private lemma cl13_levelSet_finite (T : Tower p F) (b : ℕ) (γ : ℚ) :
    (T.levelSet b γ).Finite := by
  apply Set.Finite.subset ((T12_coordFin T (⌊γ⌋.toNat + 1) (b + 1)).1)
  rintro c ⟨hblk, hht⟩
  constructor
  · have hle : (c.l : ℚ) ≤ γ := by
      rw [← hht, Tower.ht]
      have hsum : 0 ≤ ∑ r, (c.slot r : ℚ) * T.kappa r :=
        Finset.sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg _) (cl13_kappa_nonneg T r)
      linarith
    have h1 : (c.l : ℤ) ≤ ⌊γ⌋ := Int.le_floor.mpr (by exact_mod_cast hle)
    omega
  · have hb : c.slot (Fin.last T.K) = b := hblk
    omega

/-- **CL-13 (display (9), LVL-DET)**: a nonzero digit assignment supported inside
one level set has DETECTED class at its level — `inGr γ (slotCoeff b y) ≠ 0`
(NCL pins the polynomial nonzero, T4 pins its weight to exactly γ, T6's
`inγ_detects` reads it off). -/
theorem CL13_lvlDet {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (y : T.Coord → ↥(T.stg 0).FQ)
    (hne : ∃ c : T.Coord, y c ≠ 0)
    (hsupp : ∀ c : T.Coord, y c ≠ 0 → c ∈ T.levelSet b γ) :
    T.inGr γ (T.slotCoeff b y) ≠ 0 := by
  classical
  -- NCL: the polynomial is nonzero
  have hpoly : T.slotCoeff b y ≠ 0 := CL12_ncl T b γ y hne hsupp
  -- T4: the weight is pinned to the minimal support height, which is γ
  have hfin : (Function.support y).Finite :=
    (cl13_levelSet_finite T b γ).subset (fun c hc => hsupp c (Function.mem_support.mp hc))
  have hblk : ∀ c : T.Coord, y c ≠ 0 → T.blk c = b := fun c hc => (hsupp c hc).1
  obtain ⟨c₀, hc₀ne, hwQ, -⟩ := T4_slotMinHt T b y hfin hblk hpoly
  have hht : T.ht c₀ = γ := (hsupp c₀ hc₀ne).2
  rw [hht] at hwQ
  -- T6-detects on the raw polynomial
  exact cl13_wQ_detects T γ _ hwQ

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL13_lvlDet
