import Mathlib

/-!
# M1 — QuotientBox: the level-`N` box count as a finite cardinality (no Haar measure)

For the unramified core `K = ℚ_p` we have `O_K = ℤ_[p]` and `O_K / p^N ≅ ZMod (p^N)` (a *finite* ring,
via `PadicInt.toZModPow`). The "box" of monic degree-`n` polynomials over this finite ring has
cardinality `(p^N)^n = q^{nN}` — the partition total of `CountingModel.box_partition`, realized as a
genuine `Nat.card`, with **no measure theory**.

This is blueprint module M1. Build-risk noted in the blueprint (`Module.natCard_eq_pow_finrank` needs a
`DivisionRing`) is avoided here by the `degreeLTEquiv` + `Nat.card_pi` route, which needs only a
`CommRing` / `Finite` instance.
-/

namespace LeanUrat.OM.QuotientBox

open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

/-- The level-`N` residue ring `O_K / p^N`, realized as `ZMod (p^N)` (unramified core `K = ℚ_p`). -/
abbrev ResidueRing (N : ℕ) : Type := ZMod (p ^ N)

instance instNeZeroPow (N : ℕ) : NeZero (p ^ N) := ⟨pow_ne_zero N hp.out.ne_zero⟩

/-- `#(O_K/p^N) = p^N`. -/
theorem card_residueRing (N : ℕ) : Nat.card (ResidueRing p N) = p ^ N := by
  rw [ResidueRing, Nat.card_eq_fintype_card, ZMod.card]

/-- Monic degree-`n` polynomials over the residue ring — the level-`N` "box". -/
abbrev monicBox (N n : ℕ) : Type :=
  {f : (ResidueRing p N)[X] // f.Monic ∧ f.natDegree = n}

/-- **The box count (no Haar measure).** `#{monic degree-n over ZMod(p^N)} = (p^N)^n`.

Proof: the map `g ↦ X^n + g` is a bijection `degreeLT R n ≃ monicBox`, then
`degreeLTEquiv : degreeLT R n ≃ₗ (Fin n → R)` and `Nat.card (Fin n → R) = (#R)^n`. Needs `0 < N`
so that `R = ZMod(p^N)` is nontrivial (the trivial ring `ZMod 1` at `N = 0` is the unused mod-1 level). -/
theorem card_monicBox (N n : ℕ) (hN : 0 < N) :
    Nat.card (monicBox p N n) = (p ^ N) ^ n := by
  haveI : Fact (1 < p ^ N) := ⟨Nat.one_lt_pow hN.ne' hp.out.one_lt⟩
  -- bijection  toMonic : degreeLT R n → monicBox p N n,  g ↦ X^n + g
  have hdeg : ∀ g : degreeLT (ResidueRing p N) n,
      (X ^ n + (g : (ResidueRing p N)[X])).Monic ∧
      (X ^ n + (g : (ResidueRing p N)[X])).natDegree = n := by
    intro g
    have hdlt : (g : (ResidueRing p N)[X]).degree < (X ^ n : (ResidueRing p N)[X]).degree := by
      rw [degree_X_pow]; exact mem_degreeLT.1 g.2
    refine ⟨(monic_X_pow n).add_of_left hdlt, natDegree_eq_of_degree_eq_some ?_⟩
    rw [add_comm, degree_add_eq_right_of_degree_lt hdlt, degree_X_pow]
  let toMonic : degreeLT (ResidueRing p N) n → monicBox p N n :=
    fun g => ⟨X ^ n + (g : (ResidueRing p N)[X]), hdeg g⟩
  have hbij : Function.Bijective toMonic := by
    constructor
    · exact fun g₁ g₂ h => Subtype.ext (add_left_cancel (congrArg Subtype.val h))
    · rintro ⟨q, hqmonic, hqdeg⟩
      have hq0 : q ≠ 0 := hqmonic.ne_zero
      have hqdeg' : q.degree = (n : WithBot ℕ) := by rw [degree_eq_natDegree hq0, hqdeg]
      have hqX : (q - X ^ n).degree < (n : WithBot ℕ) := by
        have := degree_sub_lt (hqdeg'.trans (degree_X_pow n).symm) hq0
          (by rw [hqmonic.leadingCoeff, (monic_X_pow n).leadingCoeff])
        rwa [hqdeg'] at this
      exact ⟨⟨q - X ^ n, mem_degreeLT.2 hqX⟩,
        Subtype.ext (by change X ^ n + (q - X ^ n) = q; ring)⟩
  rw [← Nat.card_eq_of_bijective toMonic hbij,
      Nat.card_congr (degreeLTEquiv (ResidueRing p N) n).toEquiv, Nat.card_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, card_residueRing]

end LeanUrat.OM.QuotientBox
