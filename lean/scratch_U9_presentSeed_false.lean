/- SCRATCH (escalation prover, U9): verify that `PresentSeed` is inconsistent —
`False` from `S : PresentSeed p F H n N keys` alone, via
`zcSeed.downsets_literal` at i = 0 against `pres_zero`, with f := C(p^N).
NOT part of the corpus; delete after check. -/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

theorem presentSeed_false {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) : False := by
  classical
  have h0 : 0 < H.nodes.length := List.length_pos_of_ne_nil H.nonempty
  set ν : Node p F := H.nodes[0]'h0 with hν
  -- the witness polynomial: all its box digits vanish (box levels are < N)
  set f : Polynomial ℤ_[p] := Polynomial.C ((p : ℤ_[p]) ^ N) with hf
  have hpne : (p : ℤ_[p]) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hfne : f ≠ 0 := by
    rw [hf, Ne, Polynomial.C_eq_zero]
    exact pow_ne_zero N hpne
  -- its digit reading
  set x : Fin (n * N) → ZMod p :=
    fun j => baseDigit p (boxChart n N j).1 (f.coeff (boxChart n N j).2) with hx
  have hpres : S.pres 0 x f := (S.pres_zero x f).mpr (fun j => rfl)
  -- the one-slot development B 0 = f
  set B : ℕ → Polynomial ℤ_[p] := fun j => if j = 0 then f else 0 with hB
  have hdev : IsDevelopment ν.σ.Φ f B 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hΦdeg : 1 ≤ ν.σ.Φ.degree := by
        have := ν.σ.hdeg
        have hΦne : ν.σ.Φ ≠ 0 := ν.σ.hmonic.ne_zero
        rw [Polynomial.degree_eq_natDegree hΦne]
        exact_mod_cast this
      by_cases hj : j = 0
      · subst hj
        simp only [hB, if_pos rfl, hf]
        calc (Polynomial.C ((p : ℤ_[p]) ^ N)).degree ≤ 0 := Polynomial.degree_C_le
          _ < 1 := by norm_num
          _ ≤ ν.σ.Φ.degree := hΦdeg
      · simp only [hB, if_neg hj]
        calc (0 : Polynomial ℤ_[p]).degree = ⊥ := Polynomial.degree_zero
          _ < 1 := by norm_num
          _ ≤ ν.σ.Φ.degree := hΦdeg
    · intro j hj
      have : j ≠ 0 := by omega
      simp [hB, this]
    · simp [hB]
  -- every box digit of f vanishes
  have hxzero : ∀ c : Fin (n * N), x c = 0 := by
    intro c
    have hlN : (boxChart n N c).1 < N := (boxChart_lt n N c).1
    show baseDigit p (boxChart n N c).1 (f.coeff (boxChart n N c).2) = 0
    rcases Nat.eq_zero_or_pos (boxChart n N c).2 with hb | hb
    · -- coeff 0 of C(p^N) is p^N; its digits below level N vanish
      rw [hb]
      simp only [hf, Polynomial.coeff_C_zero]
      unfold baseDigit
      have hker : PadicInt.toZModPow ((boxChart n N c).1 + 1) ((p : ℤ_[p]) ^ N) = 0 := by
        have hmem : ((p : ℤ_[p]) ^ N) ∈
            RingHom.ker (PadicInt.toZModPow ((boxChart n N c).1 + 1)) := by
          rw [PadicInt.ker_toZModPow]
          exact Ideal.mem_span_singleton.mpr
            (pow_dvd_pow (p : ℤ_[p]) (by omega))
        exact hmem
      rw [hker]
      simp
    · -- other coefficients of a constant are 0
      have : f.coeff (boxChart n N c).2 = 0 := by
        rw [hf]
        exact Polynomial.coeff_C_of_ne_zero (by omega)
      rw [this]
      unfold baseDigit
      simp
  -- fire the seed law at slot 0, threshold w(B 0) + 1
  have hdl := S.zcSeed.downsets_literal 0 h0 x f B 1 hpres hdev 0
      (((ν.σ.w (B 0) : ℚ)) / (H.strFrame 0 : ℚ) + 1)
  have hrhs : ∀ c : Fin (n * N),
      (H.nodes[0]'h0).fineSlot ((boxChart n N c)).2 = 0 →
      H.htH 0 (boxChart n N c) < ((ν.σ.w (B 0) : ℚ)) / (H.strFrame 0 : ℚ) + 1 →
      x c = 0 := fun c _ _ => hxzero c
  have hlhs := hdl.mpr hrhs
  rcases hlhs with hb0 | hle
  · exact absurd hb0 (by simpa [hB] using hfne)
  · linarith

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.presentSeed_false
