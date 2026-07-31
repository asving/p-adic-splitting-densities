/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.T3_htChainWeight
import LeanUrat.HC1.T6_carrierLaws

/-!
# HC1.CL15a_packEmonoWeight — LST leg (i-a) at `packE`, unfolded (BP5 CL-15a)

**Unit CL-15a** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §3.2 + §4
CL-15, split per REVISION 2 finding 10: one unit per leg, so failure in one leg
never blocks the other three).

**Informal statement.** Leg (i-a) of `LSTStmt'` at `packE T rl`:
`wE (monoE c) = ht c` — the expansion of a basis monomial has weight exactly the
coordinate's height. `monoE c := ⟨fun γ => T.inGr γ (T.mono c), _⟩` (display (8))
has exactly one nonzero component, at `γ = ht c`.

**Proof sketch (blueprint §3.2 (i-a)).** Detect at `ht c`: T3
(`w_top(mono c) = strTop·ht c`, with `MonoNZ` discharged by `mono_ne`:
`mono = C(p^l)·∏Φ^s ≠ 0` from `hmonic` — lift the ScratchC6 private into this
unit's file or re-prove, ~10 lines), then the exact-weight class is nonzero
(T6-detects-style argument on the graded piece). Kill below: for on-lattice
`γ < ht c` the integers `strTop·γ < strTop·ht c` differ by ≥ 1, so `mono c` lies in
the strictly deeper filtration step and its class in piece `⌊strTop·γ⌋` is 0; for
off-lattice γ, `inGr γ = 0` by the dif-condition. (The kill ABOVE `ht c` also holds
— the `inGr` dif-condition fails — but is NOT needed for the `wE` fold-back and is
not stated.)

**Deps.** CL-07 (LAT — fold-back only: `ht c` lies on the `(1/strTop)·ℕ` lattice so
`wE`'s search reaches it), CL-09 (fold-back only); `T3_htChainWeight` (PROVED
Lean-core at HEAD), `mono_ne` (ScratchC6 private — lift or re-prove).

**E-PHASE RESOLUTIONS RECORDED.** CL-09's `packE`/`monoE` and CL-08's `wE` have NOT
landed at HEAD (sibling cluster); this unit states the leg's DEFINITIONAL UNFOLDING
in tower vocabulary: `monoE c`'s γ-component ↦ `T.inGr γ (T.mono c)`, and
`wE (monoE c) = (T.ht c : WithTop ℚ)` ↦ its least-populated-level spec
(component nonzero AT `ht c`, all components zero strictly BELOW — valid for any
implementation of the least populated level, `Nat.find` or the R-8 `sInf`
fallback). Fold-back to the literal pack leg = CL-19 glue via CL-08's `wE` spec +
CL-07's LAT; `rl` does not occur in the unfolded leg and is omitted.

difficulty: routine-opus. Size: ~25 of CL-15's ~90 total.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- strTop positivity (copy of CL13's private toolkit). -/
private lemma cl15a_strTop_pos (T : Tower p F) : 0 < T.strTop := by
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

/-- The basis monomial never vanishes (copy of ScratchC6's private `mono_ne`). -/
private lemma cl15a_mono_ne (T : Tower p F) (c : T.Coord) : T.mono c ≠ 0 := by
  rw [Tower.mono]
  refine mul_ne_zero ?_ ?_
  · rw [Ne, Polynomial.C_eq_zero]
    exact pow_ne_zero _ PadicInt.prime_p.ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun r _ => pow_ne_zero _ (T.stg r).hmonic.ne_zero)

/-- **CL-15a** — leg (i-a) at `packE`, unfolded (see the module docstring): the
basis-monomial expansion `monoE c = (fun γ => T.inGr γ (T.mono c))` detects at the
coordinate's height and vanishes strictly below it — i.e. `wE (monoE c) = ht c`
through the least-populated-level characterization. -/
theorem CL15a_packE_ia {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (c : T.Coord) :
    T.inGr (T.ht c) (T.mono c) ≠ 0 ∧
    ∀ γ : ℚ, γ < T.ht c → T.inGr γ (T.mono c) = 0 := by
  have hμne : T.mono c ≠ 0 := cl15a_mono_ne T c
  have hsideW : T.side.w (T.mono c)
      = (((T.stg (Fin.last T.K)).w (T.mono c) : ℤ) : WithTop ℤ) :=
    T.side_w (T6_carrierLaws T).1 hμne
  have hT3 := T3_htChainWeight T c hμne
  have hstrpos : (0 : ℚ) < (T.strTop : ℚ) := by exact_mod_cast cl15a_strTop_pos T
  -- the quotient-kernel iff (copy of ScratchC6/CL13 plumbing)
  have mk_zero : ∀ (m : ℤ) (f : Polynomial ℤ_[p]) (hf : f ∈ T.side.ge m),
      (Submodule.Quotient.mk (⟨f, hf⟩ : T.side.ge m) : T.side.grPiece m) = 0
        ↔ ((m : WithTop ℤ) < T.side.w f) := by
    intro m f hf; rw [Submodule.Quotient.mk_eq_zero]; exact Iff.rfl
  refine ⟨?_, ?_⟩
  · -- detection at ht c
    have honL : T.onLattice (T.ht c) := by
      rw [Tower.onLattice, ← hT3, Int.floor_intCast]
    have hfl : ⌊(T.strTop : ℚ) * T.ht c⌋ = (T.stg (Fin.last T.K)).w (T.mono c) := by
      rw [← hT3, Int.floor_intCast]
    have hcondeq : ((⌊(T.strTop : ℚ) * T.ht c⌋ : ℤ) : WithTop ℤ) = T.side.w (T.mono c) := by
      rw [hsideW, hfl]
    rw [Tower.inGr, dif_pos ⟨honL, le_of_eq hcondeq⟩]
    intro hcontra
    have hlt := (mk_zero _ _ _).mp hcontra
    rw [hsideW, hfl] at hlt
    exact lt_irrefl _ hlt
  · -- kill strictly below ht c
    intro γ hγ
    by_cases hcond2 : T.onLattice γ ∧
        ((⌊(T.strTop : ℚ) * γ⌋ : WithTop ℤ) ≤ T.side.w (T.mono c))
    · rw [Tower.inGr, dif_pos hcond2]
      refine (mk_zero _ _ _).mpr ?_
      rw [hsideW]
      have hlt2 : (T.strTop : ℚ) * γ < (T.strTop : ℚ) * T.ht c :=
        mul_lt_mul_of_pos_left hγ hstrpos
      have hstep : (⌊(T.strTop : ℚ) * γ⌋ : ℚ) < ((T.stg (Fin.last T.K)).w (T.mono c) : ℚ) := by
        rw [hT3]; exact lt_of_le_of_lt (Int.floor_le _) hlt2
      have hint : ⌊(T.strTop : ℚ) * γ⌋ < (T.stg (Fin.last T.K)).w (T.mono c) := by
        exact_mod_cast hstep
      exact_mod_cast hint
    · rw [Tower.inGr, dif_neg hcond2]

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL15a_packE_ia
