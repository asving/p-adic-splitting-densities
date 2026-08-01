/-
BP_II §1.7 — Fact F (`Scaffold/O12/FactF.lean`), units II-F1, II-F2.
Units in this file: II-F1 (`Mpoly` · `fallingFac` · `multiplicityCount` ·
`degreeCount` · `patternFactor` · `Npoly` · `Ppoly`) — the ℚ[q]-POLYNOMIAL half
of Fact F (all that Theorem 2 consumes; MECH transcription);
II-F2 (`gram_Npoly` · `gram_Ppoly`) — the (g1) grammar status of the count
polynomials.
-/
import Mathlib
import LeanUrat.Scaffold.O12.Core

/-!
# Fact F, polynomial half: the count polynomials [unit II-F1]

**PROVENANCE.**

* Blueprint: `lean/blueprints/BP_II.md` §1.7 (unit II-F1; row table §2, MECH).
* Math source of record: the verified leaf
  `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md` §2.3 (count polynomials).
* Deps: none (first unit of the FactF module). Later units II-F2..F9 (the Gram
  bracket, `patternOf`, and the finite-field counts) extend this file.
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU (Gram)

/-- M_D(q) = D⁻¹ Σ_{δ|D} μ(δ) q^{D/δ} ∈ ℚ[q] (Fact F, brief §2.3). -/
noncomputable def Mpoly (D : ℕ+) : Polynomial ℚ :=
  Polynomial.C (1 / (D : ℚ)) * ∑ δ ∈ (D : ℕ).divisors,
    Polynomial.C (ArithmeticFunction.moebius δ : ℚ) * Polynomial.X ^ ((D : ℕ) / δ)

noncomputable def fallingFac (P : Polynomial ℚ) (r : ℕ) : Polynomial ℚ :=
  ∏ i ∈ Finset.range r, (P - Polynomial.C (i : ℚ))

/-- N_ρ(q), P_ρ(q) for a pattern ρ : Multiset (ℕ+ × ℕ+) of atoms (D, m):
N_ρ = ∏_D (M_D)_{r_D} / ∏_m c_{D,m}!, and P_ρ = the same with the D = 1 supply
M_1 = q replaced by q − 1 (z-free). -/
noncomputable def multiplicityCount
    (ρ : Multiset (ℕ+ × ℕ+)) (D m : ℕ+) : ℕ :=
  ρ.count (D, m)

noncomputable def degreeCount
    (ρ : Multiset (ℕ+ × ℕ+)) (D : ℕ+) : ℕ :=
  (ρ.filter fun x => x.1 = D).card

noncomputable def patternFactor
    (supply : ℕ+ → Polynomial ℚ)
    (ρ : Multiset (ℕ+ × ℕ+)) (D : ℕ+) : Polynomial ℚ :=
  fallingFac (supply D) (degreeCount ρ D) *
    Polynomial.C
      ((∏ m ∈ ρ.map Prod.snd |>.toFinset,
        (Nat.factorial (multiplicityCount ρ D m) : ℚ))⁻¹)

noncomputable def Npoly (ρ : Multiset (ℕ+ × ℕ+)) : Polynomial ℚ :=
  ∏ D ∈ ρ.map Prod.fst |>.toFinset, patternFactor Mpoly ρ D

noncomputable def Ppoly (ρ : Multiset (ℕ+ × ℕ+)) : Polynomial ℚ :=
  ∏ D ∈ ρ.map Prod.fst |>.toFinset,
    patternFactor
      (fun E => if E = 1 then Polynomial.X - 1 else Mpoly E) ρ D

/-! ## Unit II-F2 — (g1) status of the count polynomials (`Gram.poly`) -/

/-- **(g1) for N_ρ** [unit II-F2]: the count polynomial `Npoly ρ`, viewed in the
ambient field `Qq = RatFunc ℚ`, lies in the grammar 𝒢 (leaf (g1): polynomials). -/
theorem gram_Npoly (ρ) : Gram (algebraMap (Polynomial ℚ) Qq (Npoly ρ)) :=
  Gram.poly (Npoly ρ)

/-- **(g1) for P_ρ** [unit II-F2]: the z-free count polynomial `Ppoly ρ`, viewed in
the ambient field `Qq = RatFunc ℚ`, lies in the grammar 𝒢 (leaf (g1)). -/
theorem gram_Ppoly (ρ) : Gram (algebraMap (Polynomial ℚ) Qq (Ppoly ρ)) :=
  Gram.poly (Ppoly ρ)

end LeanUrat.Scaffold
