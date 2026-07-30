/-
Unit D1c.encTargetP_card  (MovesD campaign, E-phase)  [AUX]
moves_ref: (L11's codomain count ∏_r Q_r^{d_r}·m̄_r).
deps: E2.
sketch: Pi/product cards; (card pool)^{d} ≤ (p^w)^d; regroup = p^W·Mfac.
difficulty: medium.  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}

open Polynomial in
/-- The pool `{x : F | x^{p^w} = x}` has at most `p^w` elements: they are roots of the
nonzero polynomial `X^{p^w} − X`, whose degree is at most `p^w`. (Self-contained copy of
unit E2 so this unit is sorry-free independently of E2's discharge.) -/
private lemma pool_card_le' {w : ℕ} (hp : 2 ≤ p) (hw : 1 ≤ w) :
    Nat.card ↥(pool p w F) ≤ p ^ w := by
  set q := p ^ w with hqdef
  have hq2 : 1 < q := by
    have hpq : p ≤ q := Nat.le_self_pow (by omega) p
    omega
  set f : Polynomial F := X ^ q - X with hf
  have hfne : f ≠ 0 := by
    intro h0
    have hc : f.coeff q = 1 := by
      simp [hf, Polynomial.coeff_X_pow, Polynomial.coeff_X, (show (1 : ℕ) ≠ q from by omega)]
    rw [h0] at hc
    simp at hc
  have hdeg : f.natDegree ≤ q := by
    have h1 : f.natDegree ≤ max (X ^ q : Polynomial F).natDegree (X : Polynomial F).natDegree :=
      Polynomial.natDegree_sub_le _ _
    have h2 : (X ^ q : Polynomial F).natDegree = q := Polynomial.natDegree_X_pow q
    have h3 : (X : Polynomial F).natDegree = 1 := Polynomial.natDegree_X
    rw [h2, h3] at h1
    omega
  have hsub : pool p w F ⊆ f.rootSet F := by
    intro x hx
    rw [Polynomial.mem_rootSet]
    refine ⟨hfne, ?_⟩
    have hxp : x ^ q = x := by
      have : x ∈ pool p w F := hx
      simpa [pool, hqdef] using this
    simp [hf, map_sub, map_pow, hxp]
  calc Nat.card ↥(pool p w F) = (pool p w F).ncard := rfl
    _ ≤ (f.rootSet F).ncard := Set.ncard_le_ncard hsub (f.rootSet F).toFinite
    _ ≤ f.natDegree := Polynomial.ncard_rootSet_le f F
    _ ≤ q := hdeg

/-- L11's codomain count: the encoding target has at most M(P̂)·p^{W(P̂)} elements. -/
theorem encTargetP_card {P : Shape n} (hp : 2 ≤ p) :
    Nat.card (EncTargetP p F (P : ShapePrefix))
      ≤ (P : ShapePrefix).Mfac * p ^ (P : ShapePrefix).W := by
  set Q := (P : ShapePrefix) with hQ
  -- Split the encoding target's cardinality into a product over the reads.
  have hLHS : Nat.card (EncTargetP p F Q)
      = ∏ r : Fin Q.reads.length,
          Nat.card ↥(pool p (Q.reads.get r).w F) ^ (Q.reads.get r).d * (Q.reads.get r).mbar := by
    unfold EncTargetP
    rw [Nat.card_pi]
    refine Finset.prod_congr rfl (fun r _ => ?_)
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_fin]
  rw [hLHS]
  -- Bound each factor: (card pool)^d ≤ (p^w)^d = p^{w·d}.
  have hbound : ∀ r : Fin Q.reads.length,
      Nat.card ↥(pool p (Q.reads.get r).w F) ^ (Q.reads.get r).d * (Q.reads.get r).mbar
        ≤ (Q.reads.get r).mbar * p ^ ((Q.reads.get r).w * (Q.reads.get r).d) := by
    intro r
    have hw : 1 ≤ (Q.reads.get r).w := (Q.reads.get r).hw
    have hpool := pool_card_le' (F := F) hp hw
    calc Nat.card ↥(pool p (Q.reads.get r).w F) ^ (Q.reads.get r).d * (Q.reads.get r).mbar
        ≤ (p ^ (Q.reads.get r).w) ^ (Q.reads.get r).d * (Q.reads.get r).mbar :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpool _)
      _ = (Q.reads.get r).mbar * p ^ ((Q.reads.get r).w * (Q.reads.get r).d) := by
          rw [← pow_mul]; ring
  calc ∏ r : Fin Q.reads.length,
          Nat.card ↥(pool p (Q.reads.get r).w F) ^ (Q.reads.get r).d * (Q.reads.get r).mbar
      ≤ ∏ r : Fin Q.reads.length,
          (Q.reads.get r).mbar * p ^ ((Q.reads.get r).w * (Q.reads.get r).d) :=
        Finset.prod_le_prod (fun r _ => Nat.zero_le _) (fun r _ => hbound r)
    _ = (∏ r : Fin Q.reads.length, (Q.reads.get r).mbar)
          * ∏ r : Fin Q.reads.length, p ^ ((Q.reads.get r).w * (Q.reads.get r).d) := by
        rw [Finset.prod_mul_distrib]
    _ = Q.Mfac * p ^ Q.W := by
        congr 1
        · rw [ShapePrefix.Mfac, ← Fin.prod_univ_fun_getElem Q.reads ShapeRead.mbar]
          simp [List.get_eq_getElem]
        · rw [Finset.prod_pow_eq_pow_sum, ShapePrefix.W,
            ← Fin.sum_univ_fun_getElem Q.reads (fun R => R.w * R.d)]
          simp [List.get_eq_getElem]

end LeanUrat.MovesD
