/-
BP_II §1.7 — Fact F (`Scaffold/O12/FactF.lean`), units II-F1, II-F2, II-F3.
Units in this file: II-F1 (`Mpoly` · `fallingFac` · `multiplicityCount` ·
`degreeCount` · `patternFactor` · `Npoly` · `Ppoly`) — the ℚ[q]-POLYNOMIAL half
of Fact F (all that Theorem 2 consumes; MECH transcription);
II-F2 (`gram_Npoly` · `gram_Ppoly`) — the (g1) grammar status of the count
polynomials;
II-F3 (`patternOf` · `patternOf_smul_unit`) — the factorization pattern of a
polynomial over a field (REV2 finding 9: `Multiset (ℕ+ × ℕ+)` with positivity
witnesses) and its unit-scalar invariance;
II-F4 (`X_pow_card_prod_irreducibles` + fenced sub-lemmas II-F4a/b/c) — Fact
F(i) factorization: X^{q^D} − X = ∏ monic irreducibles of degree ∣ D,
squarefree (see its transcription note: the blueprint display is elided);
II-F5 (`card_irred_degree_sum`) — Fact F(i) degree count q^D = Σ_{δ|D} δ·I_δ
(see its transcription note: the blueprint display is elided).
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

/-! ## Unit II-F4 — Fact F(i): X^{q^D} − X = ∏ monic irreducibles of degree ∣ D

TRANSCRIPTION NOTE (II-F4). BP_II.md §1.7 displays this unit's statement as
`theorem X_pow_card_prod_irreducibles ...` — the Lean statement is ELIDED in
the blueprint (there is no verbatim text to transcribe). Per the §2 row
instruction ("split into ≤3 sub-lemmas in-file"), the prose spec "X^{q^D} − X
= ∏ (monic irreducibles of degree ∣ D), squarefree" is formalized as the
conjunction of (a) squarefreeness, (b) the `normalizedFactors` membership
characterization (monic ∧ irreducible ∧ degree ∣ D), and (c) the product
identity over the (nodup, by (a)) factor Finset — each factor exactly once.
FIXED STATEMENT, FLAGGED FOR REVIEW per the trust boundary. Sub-lemmas
II-F4a/b/c below are the fenced split; II-F5 consumes them directly. -/

section FactFi

open Polynomial UniqueFactorizationMonoid

attribute [local instance] Classical.decEq

variable (F : Type*) [Field F] [Fintype F]

/-- Sub-lemma [II-F4a]: `X^{q^D} − X` is squarefree over the finite field `F`
(derivative = −1 route, packaged in Mathlib as separability of the Galois
polynomial `galois_poly_separable`). -/
theorem X_pow_card_pow_sub_X_squarefree (D : ℕ+) :
    Squarefree ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X) := by
  obtain ⟨p, hCharP⟩ := CharP.exists F
  haveI := hCharP
  obtain ⟨n, hprime, hcard⟩ := FiniteField.card F p
  have hpq : p ∣ Fintype.card F ^ (D : ℕ) := by
    refine dvd_pow ?_ D.pos.ne'
    rw [hcard]
    exact dvd_pow_self p n.pos.ne'
  exact (galois_poly_separable p _ hpq).squarefree

/-- Sub-lemma [II-F4b]: the converse divisibility — an irreducible of degree
dividing `D` divides `X^{q^D} − X`. Route (blueprint hint
`FieldTheory/Finite/Extension` roots): the adjoin-root field of `f` has
`q^(deg f)` elements, so its root is fixed by `x ↦ x^{q^D}`; conclude via
`AdjoinRoot.mk_eq_zero`. -/
theorem dvd_X_pow_card_pow_sub_X_of_natDegree_dvd {f : Polynomial F}
    (hirr : Irreducible f) {D : ℕ} (hdeg : f.natDegree ∣ D) :
    f ∣ (Polynomial.X : Polynomial F) ^ Fintype.card F ^ D - Polynomial.X := by
  haveI := Fact.mk hirr
  have hne : f ≠ 0 := hirr.ne_zero
  haveI : Module.Finite F (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite F
  haveI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  obtain ⟨m, hm⟩ := hdeg
  have hcardL : Fintype.card (AdjoinRoot f) = Fintype.card F ^ f.natDegree := by
    rw [Module.card_eq_pow_finrank (K := F) (V := AdjoinRoot f),
      (AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim]
  have hroot : AdjoinRoot.root f ^ Fintype.card F ^ D = AdjoinRoot.root f := by
    rw [hm, pow_mul, ← hcardL]
    exact FiniteField.pow_card_pow m (AdjoinRoot.root f)
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, hroot, sub_self]

/-- Sub-lemma [II-F4c]: the normalized (monic) irreducible factors of
`X^{q^D} − X` are EXACTLY the monic irreducibles of degree dividing `D`
(dvd direction: Mathlib's `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`;
converse: [II-F4b]). -/
theorem mem_normalizedFactors_X_pow_card_pow_sub_X (D : ℕ+) (f : Polynomial F) :
    f ∈ UniqueFactorizationMonoid.normalizedFactors
        ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X) ↔
      f.Monic ∧ Irreducible f ∧ f.natDegree ∣ (D : ℕ) := by
  have hne : ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero F D.pos.ne' Fintype.one_lt_card
  rw [mem_normalizedFactors_iff' hne]
  constructor
  · rintro ⟨hirr, hnorm, hdvd⟩
    refine ⟨(normalize_eq_self_iff_monic hirr.ne_zero).mp hnorm, hirr, ?_⟩
    exact hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
      (by rwa [Nat.card_eq_fintype_card])
  · rintro ⟨hmonic, hirr, hdeg⟩
    exact ⟨hirr, hmonic.normalize_eq_self,
      dvd_X_pow_card_pow_sub_X_of_natDegree_dvd F hirr hdeg⟩

/-- **Unit II-F4, Fact F(i) factorization** (BP_II §1.7; statement fixed from
the blueprint's ELIDED display — see the transcription note above): over a
finite field `F` with `q = Fintype.card F`, the polynomial `X^{q^D} − X` is
squarefree, its normalized factors are exactly the monic irreducibles of
degree dividing `D`, and it is the product of those factors, each exactly
once. -/
theorem X_pow_card_prod_irreducibles (D : ℕ+) :
    Squarefree ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X) ∧
      (∀ f : Polynomial F,
        f ∈ UniqueFactorizationMonoid.normalizedFactors
            ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X) ↔
          f.Monic ∧ Irreducible f ∧ f.natDegree ∣ (D : ℕ)) ∧
      (Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X =
        ∏ f ∈ (UniqueFactorizationMonoid.normalizedFactors
            ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ)
              - Polynomial.X)).toFinset, f := by
  have hsf := X_pow_card_pow_sub_X_squarefree F D
  have hne : ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero F D.pos.ne' Fintype.one_lt_card
  refine ⟨hsf, mem_normalizedFactors_X_pow_card_pow_sub_X F D, ?_⟩
  have hmonic : ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ)
      - Polynomial.X).Monic := by
    apply (monic_X_pow _).sub_of_left
    rw [degree_X_pow, degree_X]
    exact_mod_cast Nat.one_lt_pow D.pos.ne' Fintype.one_lt_card
  have hnodup : (UniqueFactorizationMonoid.normalizedFactors
      ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X)).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hne).mp hsf
  have hprod := prod_normalizedFactors_eq hne
  rw [hmonic.normalize_eq_self] at hprod
  have hval := Finset.prod_val (UniqueFactorizationMonoid.normalizedFactors
      ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X)).toFinset
  rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup] at hval
  exact hprod.symm.trans hval

/-! ## Unit II-F5 — Fact F(i) degree count: q^D = Σ_{δ|D} δ·I_δ

TRANSCRIPTION NOTE (II-F5). BP_II.md §1.7 displays this unit's statement as
`theorem card_irred_degree_sum ...` — ELIDED like II-F4 (no verbatim text to
transcribe). The prose spec "q^D = Σ_{δ|D} δ·I_δ" is formalized with
I_δ := `Nat.card` of the subtype of monic irreducibles of degree δ; for
δ = (E : ℕ+) this subtype is DEFINITIONALLY the blueprint's
`MonicIrreducibleDegree F E` (displayed under II-F6, which consumes this
count directly). FIXED STATEMENT, FLAGGED FOR REVIEW per the trust boundary.
Proof per the §2 row sketch: take `natDegree` across II-F4's product identity
(`Polynomial.natDegree_prod`) and fiber the factor Finset by degree. -/

/-- **Unit II-F5, Fact F(i) degree count** (BP_II §1.7; statement fixed from
the blueprint's ELIDED display — see the transcription note above): over a
finite field `F` with `q = Fintype.card F`, counting degrees in the II-F4
factorization of `X^{q^D} − X` gives q^D = Σ_{δ∣D} δ·I_δ, where I_δ is the
number of monic irreducible polynomials of degree δ over `F`. -/
theorem card_irred_degree_sum (D : ℕ+) :
    Fintype.card F ^ (D : ℕ) =
      ∑ δ ∈ (D : ℕ).divisors,
        δ * Nat.card {f : Polynomial F // f.Monic ∧ Irreducible f ∧ f.natDegree = δ} := by
  obtain ⟨-, hmem, hprod⟩ := X_pow_card_prod_irreducibles F D
  set S : Finset (Polynomial F) :=
    (UniqueFactorizationMonoid.normalizedFactors
      ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ) - Polynomial.X)).toFinset
    with hS
  have hmemS : ∀ f : Polynomial F,
      f ∈ S ↔ f.Monic ∧ Irreducible f ∧ f.natDegree ∣ (D : ℕ) := fun f =>
    (Multiset.mem_toFinset).trans (hmem f)
  -- degree of the left side: natDegree (X^{q^D} − X) = q^D
  have hdeg : ((Polynomial.X : Polynomial F) ^ Fintype.card F ^ (D : ℕ)
      - Polynomial.X).natDegree = Fintype.card F ^ (D : ℕ) :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq F D.pos.ne' Fintype.one_lt_card
  -- degree of the right side: natDegree of the product = Σ of factor degrees
  have hne0 : ∀ f ∈ S, f ≠ 0 := fun f hf => ((hmemS f).mp hf).2.1.ne_zero
  have hsum : Fintype.card F ^ (D : ℕ) = ∑ f ∈ S, f.natDegree := by
    conv_lhs => rw [← hdeg, hprod]
    exact Polynomial.natDegree_prod S id hne0
  -- every factor degree is a divisor of D
  have hfib : ∀ f ∈ S, f.natDegree ∈ (D : ℕ).divisors := fun f hf =>
    Nat.mem_divisors.mpr ⟨((hmemS f).mp hf).2.2, D.pos.ne'⟩
  -- fiber count = I_δ
  have hcard : ∀ δ ∈ (D : ℕ).divisors,
      (S.filter fun f => f.natDegree = δ).card
        = Nat.card {f : Polynomial F // f.Monic ∧ Irreducible f ∧ f.natDegree = δ} := by
    intro δ hδ
    have hset : {f : Polynomial F | f.Monic ∧ Irreducible f ∧ f.natDegree = δ}
        = ↑(S.filter fun f => f.natDegree = δ) := by
      ext f
      constructor
      · rintro ⟨hm, hi, hd⟩
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨(hmemS f).mpr ⟨hm, hi, by rw [hd]; exact (Nat.mem_divisors.mp hδ).1⟩, hd⟩)
      · intro hf
        obtain ⟨hfS, hd⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
        obtain ⟨hm, hi, -⟩ := (hmemS f).mp hfS
        exact ⟨hm, hi, hd⟩
    have h1 : Nat.card {f : Polynomial F // f.Monic ∧ Irreducible f ∧ f.natDegree = δ}
        = ({f : Polynomial F | f.Monic ∧ Irreducible f ∧ f.natDegree = δ}
            : Set (Polynomial F)).ncard := Nat.card_coe_set_eq _
    rw [h1, hset, Set.ncard_coe_finset]
  -- assemble: fiber the degree sum over the divisors of D
  calc Fintype.card F ^ (D : ℕ)
      = ∑ f ∈ S, f.natDegree := hsum
    _ = ∑ δ ∈ (D : ℕ).divisors, ∑ f ∈ S with f.natDegree = δ, δ :=
        (Finset.sum_fiberwise_of_maps_to' hfib id).symm
    _ = ∑ δ ∈ (D : ℕ).divisors,
          δ * Nat.card {f : Polynomial F // f.Monic ∧ Irreducible f ∧ f.natDegree = δ} := by
        refine Finset.sum_congr rfl fun δ hδ => ?_
        rw [Finset.sum_const, smul_eq_mul, hcard δ hδ, mul_comm]

end FactFi

end LeanUrat.Scaffold
