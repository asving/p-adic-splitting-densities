/-
BP_II §1.7 — Fact F (`Scaffold/O12/FactF.lean`), unit II-F1.
Units in this file: II-F1 (`Mpoly` · `fallingFac` · `multiplicityCount` ·
`degreeCount` · `patternFactor` · `Npoly` · `Ppoly`) — the ℚ[q]-POLYNOMIAL half
of Fact F (all that Theorem 2 consumes; MECH transcription).
-/
import Mathlib

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

end LeanUrat.Scaffold
