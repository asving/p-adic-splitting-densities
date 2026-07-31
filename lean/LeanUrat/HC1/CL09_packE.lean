/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.R1_LSTStmt
import LeanUrat.HC1.CL08_latticeExp
import LeanUrat.HC1.CL07_heightLattice
import LeanUrat.HC1.CL15a_packEmonoWeight

/-!
# HC1.CL09_packE — packE + the Gr-pin (BP5 CL-09)

**Unit CL-09** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4; §3.2
display (8)).

**Informal statement.** The graded-expansion carrier pack `packE T rl :
CarrierPackR p` (display (8)): `G := gradedExpCarrier T` (CL-08), trivial history,
the tower's real coordinates/heights/blocks/level sets, digits in the base residue
field `F_Q`, `slotCoeff` = the per-level display `γ ↦ inGr γ (T.slotCoeff b
(y↾lvl b γ))` (the MOVES 3795–3807 display itself), `mono := monoE` (the per-level
expansion of the basis monomial), lines/interiors/floor from the realizability data
`rl` with the `i > K` guard `interiorEnd := 0`, `window ≡ True`. Plus THE
non-vacuity clause: `packE_gr_pin : ∀ γ, (packE T rl).G.Gr γ = T.grQ γ := fun _ =>
rfl`.

**Proof obligations left as sorries (the unit's proof work).**
* the lattice-support leg of `packE.slotCoeff`: each component lives at
  `γ = n/strTop` — LAT (CL-07) at any level-set member + levelSet-emptiness ⇒ zero
  component elsewhere (empty restriction gives the zero polynomial, `inGr` of 0 is
  0; off-lattice γ has `inGr = 0` by the DefsCar dif-convention).
* the lattice-support leg of `monoE`: nonzero only at `γ = ht c` (T3 + `mono_ne`,
  CL-27(a)), which is on the lattice by CL-07.

**E-phase resolutions recorded.**
* **UNIVERSE PIN (flagged for the orchestrator).** `CarrierPackR` fixes
  `Digit : Type` (universe 0), and display (8) sets `Digit := ↥(T.stg 0).FQ`, a
  subtype of the ambient `F`. This file therefore pins `F : Type` (universe 0) —
  `↥FQ : Type u` cannot inhabit `Digit : Type` for `u > 0`, and `CarrierPackR` is an
  EXISTING file (new-files-only discipline: not re-keyed here). CONSUMER IMPLICATION
  (CL-14…CL-19, other cluster): `R6_carrierInstance` is stated over `{F : Type*}`;
  the CL-19 assembly via `packE` discharges it at universe-0 instances only — either
  the R6 statement's universe is ratified down to `Type`, or a `Digit` shrink is
  added, at CL-19. Every planned gate instance (`GaloisField 2 2`) lives in `Type`.
* `packE.slotCoeff`'s restriction is transcribed with `if c ∈ T.levelSet b γ then
  y c else 0` (classical `if` on Set membership) — display (8) verbatim.
* `interiorEnd`'s guard is transcribed `if i ≤ T.K then rl.interiorEnd i else 0`
  (display (8); makes DOM's `i > K` leg vacuous — CL-18).
* `Hist := Unit` (display (8)); all `Hist`-indexed fields discard the argument.

**Deps.** CL-07, CL-08 (+ R1's `CarrierPackR`; statement-only — independent of the
CL-06 (i-b) repair, which edits `LSTStmt'`, not the pack shape). difficulty:
routine-opus. Size: ~80. hyp: `TowerRealizable T` (the `rl` argument).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial

open scoped Classical

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

/-! ## Private toolkit for the two lattice-support legs. -/

private lemma cl09_strTop_pos (T : Tower p F) : 0 < T.strTop := by
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

/-- On-lattice + nonnegative ⟹ a genuine `n/strTop` witness (`n : ℕ`). -/
private lemma cl09_lattice_of (T : Tower p F) {γ : ℚ} (honL : T.onLattice γ) (hpos : 0 ≤ γ) :
    ∃ n : ℕ, γ = (n : ℚ) / (T.strTop : ℚ) := by
  have hstrpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast cl09_strTop_pos T
  rw [Tower.onLattice] at honL
  have hfloor_nonneg : 0 ≤ ⌊(T.strTop : ℚ) * γ⌋ := by
    rw [Int.le_floor]; push_cast; exact mul_nonneg (le_of_lt hstrpos) hpos
  refine ⟨(⌊(T.strTop : ℚ) * γ⌋).toNat, ?_⟩
  have hcast : ((⌊(T.strTop : ℚ) * γ⌋).toNat : ℚ) = (⌊(T.strTop : ℚ) * γ⌋ : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hfloor_nonneg
  rw [hcast, honL, eq_div_iff (ne_of_gt hstrpos)]; ring

/-- `digLift 0 = 0` (copy of ScratchC6's private `digLift_zero`). -/
private lemma cl09_digLift_zero (T : Tower p F) : T.digLift (0 : ↥(T.stg 0).FQ) = 0 := by
  rw [Tower.digLift, dif_neg]
  rintro ⟨B, hB0, _, _, hBR⟩
  have hz : (⟨((0 : ↥(T.stg 0).FQ) : F), (T.stg 0).hFQ_le (0 : ↥(T.stg 0).FQ).2⟩ :
      ↥(T.stg 0).K) = 0 := by ext; simp
  rw [hz, map_zero, zero_mul] at hBR
  exact (T.stg 0).hRne B hB0 hBR

/-- `inGr γ 0 = 0` (the class of the zero polynomial vanishes in every piece). -/
private lemma cl09_inGr_zero (T : Tower p F) (γ : ℚ) :
    T.inGr γ (0 : Polynomial ℤ_[p]) = 0 := by
  rw [Tower.inGr]
  split
  · exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.zero_mem _)
  · rfl

/-- **monoE** (display (8)): the graded expansion of a basis monomial — the class of
`T.mono c` in every piece (nonzero only at `γ = ht c`, on the lattice by CL-07). -/
noncomputable def monoE (T : Tower p F) (c : T.Coord) : LatticeExp T :=
  ⟨fun γ => T.inGr γ (T.mono c), by
    intro γ hne0
    have hne : T.inGr γ (T.mono c) ≠ 0 := hne0
    have honL : T.onLattice γ := by
      by_contra hcon
      exact hne (by rw [Tower.inGr, dif_neg (fun hh => hcon hh.1)])
    have hge : T.ht c ≤ γ := by
      by_contra hcon
      exact hne ((CL15a_packE_ia T c).2 γ (not_le.mp hcon))
    have hpos : 0 ≤ γ := le_trans (CL07_heightLattice T c).1 hge
    exact cl09_lattice_of T honL hpos⟩

/-- **Display (8), packE**: the graded-expansion carrier pack over the real tower
data — `G := gradedExpCarrier T` (so `Gr = T.grQ`, the non-vacuity pin), real
coordinates/heights/blocks/level sets, `F_Q`-digits, the per-level `slotCoeff`
display, `monoE` monomials, `rl`-lines with the `i > K` interior guard, and the
trivial window. -/
noncomputable def packE (T : Tower p F) (rl : TowerRealizable T) : CarrierPackR p where
  G := gradedExpCarrier T
  Hist := Unit
  Coord := T.Coord
  Digit := ↥(T.stg 0).FQ
  kIdx _ := T.K
  ht _ := T.ht
  blk _ := T.blk
  lvl _ b γ := T.levelSet b γ
  slotCoeff _ b y :=
    (⟨fun γ => T.inGr γ (T.slotCoeff b (fun c => if c ∈ T.levelSet b γ then y c else 0)),
      by
        intro γ h0
        have h : T.inGr γ (T.slotCoeff b
            (fun c => if c ∈ T.levelSet b γ then y c else 0)) ≠ 0 := h0
        rcases Set.eq_empty_or_nonempty (T.levelSet b γ) with hempty | ⟨c₀, hc₀⟩
        · exfalso
          apply h
          have hfun : (fun c => if c ∈ T.levelSet b γ then y c else 0)
              = (fun _ => (0 : ↥(T.stg 0).FQ)) := by funext c; simp [hempty]
          have hsc : T.slotCoeff b (fun _ => (0 : ↥(T.stg 0).FQ)) = 0 := by
            rw [Tower.slotCoeff]; simp only [cl09_digLift_zero, zero_mul, finsum_zero]
          rw [hfun, hsc, cl09_inGr_zero]
        · obtain ⟨n, hn⟩ := (CL07_heightLattice T c₀).2
          exact ⟨n, by rw [← hc₀.2]; exact hn⟩⟩ : LatticeExp T)
  aDim _ := T.aDim
  lines _ := rl.line
  blockEdge _ := T.blockEdge
  interiorEnd _ i := if i ≤ T.K then rl.interiorEnd i else 0
  window _ _ := True
  mono _ := monoE T
  floorB _ := rl.floorB

/-- **The Gr-pin** (the non-vacuity clause of R6, display (8)): packE's graded pieces
ARE the tower's real pieces, definitionally. -/
theorem packE_gr_pin (T : Tower p F) (rl : TowerRealizable T) :
    ∀ γ : ℚ, (packE T rl).G.Gr γ = T.grQ γ := fun _ => rfl

end LeanUrat.HC1

#print axioms LeanUrat.HC1.packE
#print axioms LeanUrat.HC1.packE_gr_pin
