/-
HDISCHARGE_H7 §3.4 — `H7/ResTrans.lean`: the KL-1a order-1 count face (unit H7-C2).
Statement transcribed VERBATIM from `lean/blueprints/HDISCHARGE_H7.md` §3.4
(probe-typed). Deps: Mathlib only.
-/
import Mathlib.Algebra.Polynomial.FieldDivision

namespace LeanUrat.Scaffold.HDischarge.H7

/-- H7-C2 [EASY-MED]: ω-blindness of coprime cofactors — multiplying by a ψ-coprime
cofactor changes no ψ-power divisibility read (ψ irreducible over a field). SCOPE
(REV 2, review finding 17): this is KL-1a's COUNT FACE at order 1 ONLY — it proves
none of KL-1b/1c, KL-2 transport, KL-3 constancy, KL-4 pullback, or KL-0. Proof:
ψ irreducible ⟹ prime; induct with `Prime.pow_dvd_of_dvd_mul_right`. -/
theorem pow_dvd_mul_iff_of_coprime_cofactor {F : Type*} [Field F]
    {ψ g : Polynomial F} (hψ : Irreducible ψ) (hg : ¬ ψ ∣ g)
    (f : Polynomial F) (k : ℕ) :
    ψ ^ k ∣ f * g ↔ ψ ^ k ∣ f := by
  constructor
  · intro h
    exact hψ.prime.pow_dvd_of_dvd_mul_right k hg h
  · intro h
    exact h.mul_right g

end LeanUrat.Scaffold.HDischarge.H7
