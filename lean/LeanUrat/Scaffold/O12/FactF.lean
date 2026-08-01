/-
BP_II §1.7 — Fact F (`Scaffold/O12/FactF.lean`), units II-F1, II-F2, II-F3.
Units in this file: II-F1 (`Mpoly` · `fallingFac` · `multiplicityCount` ·
`degreeCount` · `patternFactor` · `Npoly` · `Ppoly`) — the ℚ[q]-POLYNOMIAL half
of Fact F (all that Theorem 2 consumes; MECH transcription);
II-F2 (`gram_Npoly` · `gram_Ppoly`) — the (g1) grammar status of the count
polynomials;
II-F3 (`patternOf` · `patternOf_smul_unit`) — the factorization pattern of a
polynomial over a field (REV2 finding 9: `Multiset (ℕ+ × ℕ+)` with positivity
witnesses) and its unit-scalar invariance.
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

/-! ## Unit II-F3 — the factorization pattern `patternOf` + unit invariance

TRANSCRIPTION NOTE (II-F3). `patternOf_smul_unit` is stated VERBATIM from
BP_II.md §1.7. The `patternOf` SIGNATURE is verbatim; its displayed BODY cannot
compile as written, for three mechanical reasons (each verified against this
toolchain, errors on record in the unit report):
1. bare `[Field F]` cannot even elaborate `normalizedFactors h` — instance
   synthesis fails with `failed to synthesize NormalizationMonoid (Polynomial F)`
   (Mathlib's chain `CommGroupWithZero.instNormalizedGCDMonoid` →
   `Polynomial.instNormalizationMonoid` needs `DecidableEq F`); repaired by the
   section-local `attribute [local instance] Classical.decEq`;
2. the blueprint maps over `normalizedFactors h` directly yet takes projections
   `f.1`/`f.2` of the running element (error: `Invalid projection: Index 2 is
   invalid for this structure; the only valid index is 1`); the intended
   positivity witnesses require `.attach.map`, whence `f.natDegree ↦
   f.1.natDegree` and witness arguments `f.2` (the membership proof — the
   blueprint's `f.1` in the second slot is inconsistent with its own `f.2` in
   the first);
3. `h.factorization f`: Mathlib's Finsupp-valued multiplicity function is the
   ROOT-level `factorization` (`RingTheory/UniqueFactorizationDomain/Finsupp`),
   so dot-notation `Polynomial.factorization` cannot resolve; repaired to
   `factorization h f.1`.
The semantic content is exactly REV2 finding 9: each normalized (monic)
irreducible factor contributes the atom (degree, multiplicity), positivity
extracted from irreducibility resp. positive multiplicity. -/

section PatternOf

attribute [local instance] Classical.decEq

/-- Helper [unit II-F3]: a normalized factor of `h` has positive degree —
the positivity witness extracted from irreducibility (REV2 finding 9). -/
theorem irreducible_natDegree_pos {F : Type*} [Field F] {h g : Polynomial F}
    (hg : g ∈ UniqueFactorizationMonoid.normalizedFactors h) : 0 < g.natDegree :=
  (UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg).natDegree_pos

/-- Helper [unit II-F3]: a normalized factor of `h` has positive multiplicity
in the factorization Finsupp `factorization h` (REV2 finding 9). -/
theorem factorization_pos_of_mem_normalizedFactors {F : Type*} [Field F]
    {h g : Polynomial F}
    (hg : g ∈ UniqueFactorizationMonoid.normalizedFactors h) :
    0 < factorization h g := by
  rw [factorization_eq_count]
  exact Multiset.count_pos.mpr hg

/-- The factorization pattern of h ∈ F[z]: each distinct monic irreducible factor
contributes the atom (its degree, its multiplicity). Unit-scalar invariant.
[unit II-F3] -/
noncomputable def patternOf {F : Type*} [Field F] (h : Polynomial F) :
    Multiset (ℕ+ × ℕ+) :=
  (UniqueFactorizationMonoid.normalizedFactors h).attach.map
    (fun f =>
      (⟨f.1.natDegree, irreducible_natDegree_pos f.2⟩,
       ⟨factorization h f.1, factorization_pos_of_mem_normalizedFactors f.2⟩))

/-- Value-level shadow [unit II-F3]: forgetting the positivity witnesses,
`patternOf h` is the plain multiset of (degree, multiplicity) pairs over the
normalized factors of `h`. Downstream counting units (II-F8, II-T1) can work
here and pull back along `PNat.coe_injective`. -/
theorem patternOf_map_val {F : Type*} [Field F] (h : Polynomial F) :
    (patternOf h).map (fun x => ((x.1 : ℕ), (x.2 : ℕ)))
      = (UniqueFactorizationMonoid.normalizedFactors h).map
          (fun f => (f.natDegree, factorization h f)) := by
  simp only [patternOf]
  rw [Multiset.map_map]
  exact Multiset.attach_map_val' (UniqueFactorizationMonoid.normalizedFactors h)
    (fun f => (f.natDegree, factorization h f))

/-- **Unit-scalar invariance of the pattern** [unit II-F3, statement verbatim
BP_II.md §1.7]: scaling by a unit of `F` is an associate, so the normalized
factors — hence the pattern — do not move. -/
theorem patternOf_smul_unit {F} [Field F] (u : Fˣ) (h : Polynomial F) :
    patternOf ((u : F) • h) = patternOf h := by
  have hassoc : Associated ((u : F) • h) h := by
    rw [Polynomial.smul_eq_C_mul]
    exact associated_unit_mul_left h (Polynomial.C (u : F))
      (Polynomial.isUnit_C.mpr u.isUnit)
  have hnf : UniqueFactorizationMonoid.normalizedFactors ((u : F) • h)
      = UniqueFactorizationMonoid.normalizedFactors h :=
    hassoc.normalizedFactors_eq
  have hfac : factorization ((u : F) • h) = factorization h := by
    ext p
    rw [factorization_eq_count, factorization_eq_count, hnf]
  have hinj : Function.Injective
      (fun x : ℕ+ × ℕ+ => ((x.1 : ℕ), (x.2 : ℕ))) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hx
    simp only [Prod.mk.injEq] at hx ⊢
    exact ⟨PNat.coe_injective hx.1, PNat.coe_injective hx.2⟩
  apply Multiset.map_injective hinj
  rw [patternOf_map_val, patternOf_map_val, hnf, hfac]

end PatternOf

end LeanUrat.Scaffold
