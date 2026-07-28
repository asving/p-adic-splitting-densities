/-
Unit U17b.galois_normalize  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD `EtaGalEq`/`canonRoot` defs; §0.6 root-normalization gate.
deps: mathlib finite-field Galois (Frobenius closure), MovesD `fieldEnum`.
difficulty: hard — PRE-SPLIT (blueprint): U17b-1 single-read root swap; U17b-2 tower
composition; U17b-3 data transport. The E-phase renderings below are the elaborator's
typeable carriers (flagged in MANIFEST; prover refinement authorized — a full Node/Stage
transport definition is NOT authorized in the Defs layer, so U17b-3 is stated in
∃-transported form).  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

open Classical in
/-- `canonRoot ν` really is a root of `ψImage ν` as soon as `ψImage ν` has a root in `F`
(the `fieldEnum`-least element of a nonempty root set is a member of that set). -/
private lemma canonRoot_mem_roots (ν : Node p F)
    (hne : ((ψImage ν).roots.toFinset.image (fieldEnum F)).Nonempty) :
    canonRoot ν ∈ (ψImage ν).roots.toFinset := by
  classical
  set T := (ψImage ν).roots.toFinset.image (fieldEnum F) with hT
  have hmin : T.min = (↑(T.min' hne) : WithTop (Fin (Nat.card F))) :=
    (Finset.coe_min' hne).symm
  have hcanon : canonRoot ν = (fieldEnum F).symm (T.min' hne) := by
    rw [canonRoot, ← hT, hmin]; rfl
  rw [hcanon]
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp (T.min'_mem hne)
  rw [← hxeq, Equiv.symm_apply_apply]
  exact hx

open Classical in
/-- U17b-1 — single-read root swap: some ambient automorphism fixes the frame subfield
pointwise and carries the recorded residue root to the canonical one (both are roots of
the same `ψImage`, irreducible over the frame field; Frobenius power). -/
theorem galois_root_swap (ν : Node p F) :
    ∃ φ : F ≃+* F, (∀ x ∈ ν.σ.K, φ x = x) ∧
      φ ((ν.zbar : Fˣ) : F) = canonRoot ν := by
  classical
  set K := ν.σ.K with hKdef
  set z : F := ((ν.zbar : Fˣ) : F) with hzdef
  set r : F := canonRoot ν with hrdef
  letI : Algebra ↥K F := K.subtype.toAlgebra
  haveI : Finite ↥K := inferInstance
  -- z is a root of the K-irreducible ψ
  have hzaeval : (Polynomial.aeval z ν.ψ : F) = 0 := ν.hzbarRoot
  have hminz : minpoly ↥K z = ν.ψ :=
    (minpoly.eq_of_irreducible_of_monic ν.hψirr hzaeval ν.hψmonic).symm
  -- ψImage ν is monic (hence nonzero) and has z as a root, so its root set is nonempty
  have hψImg_ne : ψImage ν ≠ 0 := (ν.hψmonic.map ν.σ.K.subtype).ne_zero
  have hz_root_img : (ψImage ν).eval z = 0 := by
    show (ν.ψ.map ν.σ.K.subtype).eval z = 0
    rw [Polynomial.eval_map]; exact ν.hzbarRoot
  have hz_mem : z ∈ (ψImage ν).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hψImg_ne]; exact hz_root_img
  have hne : ((ψImage ν).roots.toFinset.image (fieldEnum F)).Nonempty :=
    ⟨fieldEnum F z, Finset.mem_image.mpr ⟨z, hz_mem, rfl⟩⟩
  -- r = canonRoot ν is a root of ψImage ν too
  have hr_mem : r ∈ (ψImage ν).roots.toFinset := canonRoot_mem_roots ν hne
  have hr_root_img : (ψImage ν).eval r = 0 := by
    have h := Multiset.mem_toFinset.mp hr_mem
    rw [Polynomial.mem_roots hψImg_ne] at h; exact h
  have hraeval : (Polynomial.aeval r ν.ψ : F) = 0 := by
    have h1 : (ψImage ν).eval r = Polynomial.aeval r ν.ψ := by
      show (ν.ψ.map ν.σ.K.subtype).eval r = _
      rw [Polynomial.eval_map]; rfl
    rw [← h1]; exact hr_root_img
  have hminr : minpoly ↥K r = ν.ψ :=
    (minpoly.eq_of_irreducible_of_monic ν.hψirr hraeval ν.hψmonic).symm
  -- z and r are conjugate roots over K; a normal (finite ⇒ Galois) extension supplies φ
  have hconj : IsConjRoot ↥K r z := by
    show minpoly ↥K r = minpoly ↥K z
    rw [hminr, hminz]
  obtain ⟨φ, hφ⟩ := hconj.exists_algEquiv
  refine ⟨φ.toRingEquiv, ?_, ?_⟩
  · intro x hx
    have key : φ (algebraMap ↥K F ⟨x, hx⟩) = algebraMap ↥K F ⟨x, hx⟩ := φ.commutes ⟨x, hx⟩
    rw [AlgEquiv.coe_ringEquiv]
    exact key
  · rw [AlgEquiv.coe_ringEquiv]; exact hφ

/-! ### φ-transport infrastructure (U17b-3 route; private)

The blueprint bars a Node/Stage transport definition from the DEFS layer only; U17b-3's
∃-form is discharged by building the transported history privately HERE. Keystone: in the
finite ambient `F` every subfield is SETWISE stable under every ring automorphism (a
subfield is exactly the root set of `X^|K| − X`, and automorphisms permute roots), so the
transported stage keeps the SAME `K : Subfield F` — the dependent types `↥σ.K` never move
and the transport is field-by-field. -/

section TransportInfra

/-- Finite ambient field: every ring automorphism maps every subfield INTO itself. -/
private lemma subfield_map_le (φ : F ≃+* F) (K : Subfield F) :
    K.map (φ : F →+* F) ≤ K := by
  classical
  cases nonempty_fintype F
  set q : ℕ := Nat.card ↥K with hq
  have hq1 : 1 < q := by
    rw [hq, Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hpow : ∀ x : F, x ∈ K → x ^ q = x := by
    intro x hx
    have h := FiniteField.pow_card (⟨x, hx⟩ : ↥K)
    have h2 : x ^ Fintype.card ↥K = x := by simpa using congrArg Subtype.val h
    rwa [← Nat.card_eq_fintype_card, ← hq] at h2
  set P : Polynomial F := Polynomial.X ^ q - Polynomial.X with hP
  have hPne : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hq1
  have hPdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq F hq1
  have hroot : ∀ x : F, x ^ q = x → x ∈ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne]
    simp [hP, Polynomial.IsRoot, hx]
  have hKsub : (K : Set F) ⊆ (P.roots.toFinset : Set F) := fun x hx => hroot x (hpow x hx)
  have hKcard : (K : Set F).ncard = q := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hq]
  have hRcard : ((P.roots.toFinset : Finset F) : Set F).ncard ≤ q := by
    rw [Set.ncard_coe_finset]
    exact le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' P) hPdeg.le)
  have hEq : (K : Set F) = (P.roots.toFinset : Set F) :=
    Set.eq_of_subset_of_ncard_le hKsub (by rw [hKcard]; exact hRcard) (Set.toFinite _)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.mp hy
  have hφx : φ x ^ q = φ x := by rw [← map_pow, hpow x hx]
  have hmem : φ x ∈ (P.roots.toFinset : Set F) := hroot _ hφx
  rw [← hEq] at hmem
  exact hmem

private lemma mem_map_self (φ : F ≃+* F) (K : Subfield F) {x : F} (hx : x ∈ K) :
    φ x ∈ K :=
  subfield_map_le φ K (Subfield.mem_map.mpr ⟨x, hx, rfl⟩)

private lemma subfield_map_eq (φ : F ≃+* F) (K : Subfield F) :
    K.map (φ : F →+* F) = K := by
  refine le_antisymm (subfield_map_le φ K) fun x hx => ?_
  exact Subfield.mem_map.mpr ⟨φ.symm x, mem_map_self φ.symm K hx, φ.apply_symm_apply x⟩

/-- The automorphism of `↥K` induced by restricting `φ` (K is φ-stable in finite F). -/
private noncomputable def resAut (φ : F ≃+* F) (K : Subfield F) : ↥K ≃+* ↥K where
  toFun x := ⟨φ x, mem_map_self φ K x.2⟩
  invFun x := ⟨φ.symm x, mem_map_self φ.symm K x.2⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x)
  right_inv x := Subtype.ext (φ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul φ (x : F) (y : F))
  map_add' x y := Subtype.ext (map_add φ (x : F) (y : F))

@[simp] private lemma resAut_coe (φ : F ≃+* F) (K : Subfield F) (x : ↥K) :
    ((resAut φ K x : ↥K) : F) = φ (x : F) := rfl

@[simp] private lemma resAut_symm_coe (φ : F ≃+* F) (K : Subfield F) (x : ↥K) :
    (((resAut φ K).symm x : ↥K) : F) = φ.symm (x : F) := rfl

private lemma subtype_comp_resAut (φ : F ≃+* F) (K : Subfield F) :
    K.subtype.comp ((resAut φ K : ↥K ≃+* ↥K) : ↥K →+* ↥K) = (φ : F →+* F).comp K.subtype :=
  RingHom.ext fun _ => rfl

private lemma resAut_eq_refl (φ : F ≃+* F) (K : Subfield F) (hfix : ∀ x ∈ K, φ x = x) :
    resAut φ K = RingEquiv.refl ↥K :=
  RingEquiv.ext fun x => Subtype.ext (hfix (x : F) x.2)

/-- Coefficient map on Laurent polynomials, as a ring hom. -/
private noncomputable def lmap {K L : Type*} [CommSemiring K] [CommSemiring L]
    (χ : K →+* L) : LaurentPolynomial K →+* LaurentPolynomial L :=
  AddMonoidAlgebra.mapRingHom ℤ χ

private lemma lmap_single {K L : Type*} [CommSemiring K] [CommSemiring L] (χ : K →+* L)
    (n : ℤ) (r : K) :
    lmap χ (AddMonoidAlgebra.single n r) = AddMonoidAlgebra.single n (χ r) :=
  AddMonoidAlgebra.mapRingHom_single χ n r

private lemma lmap_C_mul_T {K L : Type*} [CommSemiring K] [CommSemiring L] (χ : K →+* L)
    (r : K) (n : ℤ) :
    lmap χ (LaurentPolynomial.C r * LaurentPolynomial.T n)
      = LaurentPolynomial.C (χ r) * LaurentPolynomial.T n := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, lmap_single,
    LaurentPolynomial.single_eq_C_mul_T]

private lemma lmap_C {K L : Type*} [CommSemiring K] [CommSemiring L] (χ : K →+* L) (r : K) :
    lmap χ (LaurentPolynomial.C r) = LaurentPolynomial.C (χ r) := by
  have h := lmap_C_mul_T χ r 0
  simpa [LaurentPolynomial.T_zero] using h

private lemma lmap_T {K L : Type*} [CommSemiring K] [CommSemiring L] (χ : K →+* L) (n : ℤ) :
    lmap χ (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  have h := lmap_C_mul_T χ 1 n
  simpa using h

private lemma lmap_injective {K L : Type*} [CommSemiring K] [CommSemiring L] (χ : K ≃+* L) :
    Function.Injective (lmap (χ : K →+* L)) := by
  intro a b h
  ext m
  have h1 := congrArg (fun z : LaurentPolynomial L => z m) h
  simp only [lmap, AddMonoidAlgebra.mapRingHom_apply] at h1
  exact χ.injective h1

private lemma lmap_eq_self {K : Type*} [CommSemiring K] (χ : K →+* K)
    (hχ : ∀ x, χ x = x) (l : LaurentPolynomial K) : lmap χ l = l := by
  have h : χ = RingHom.id K := RingHom.ext hχ
  rw [h]
  show AddMonoidAlgebra.mapRingHom ℤ (RingHom.id K) l = l
  rw [AddMonoidAlgebra.mapRingHom_id]
  rfl

private lemma eval₂_lmap {K L S : Type*} [CommSemiring K] [CommSemiring L] [CommSemiring S]
    (χ : K →+* L) (f : L →+* S) (x : Sˣ) (l : LaurentPolynomial K) :
    LaurentPolynomial.eval₂ f x (lmap χ l) = LaurentPolynomial.eval₂ (f.comp χ) x l := by
  have h : (LaurentPolynomial.eval₂ f x).comp (lmap χ)
      = LaurentPolynomial.eval₂ (f.comp χ) x := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      simp only [RingHom.coe_comp, Function.comp_apply,
        LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
      rw [lmap_C_mul_T]
      simp
    · intro m
      simp only [RingHom.coe_comp, Function.comp_apply,
        LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
      rw [lmap_T, LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_T]
  exact DFunLike.congr_fun h l

private lemma hom_eval₂_laurent {K S S' : Type*} [CommSemiring K] [CommSemiring S]
    [CommSemiring S'] (f : K →+* S) (g : S →+* S') (x : Sˣ) (l : LaurentPolynomial K) :
    g (LaurentPolynomial.eval₂ f x l)
      = LaurentPolynomial.eval₂ (g.comp f) (Units.map g.toMonoidHom x) l := by
  have h : g.comp (LaurentPolynomial.eval₂ f x)
      = LaurentPolynomial.eval₂ (g.comp f) (Units.map g.toMonoidHom x) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      simp [LaurentPolynomial.single_eq_C_mul_T]
    · intro m
      simp only [RingHom.coe_comp, Function.comp_apply,
        LaurentPolynomial.single_eq_C_mul_T, map_one, one_mul]
      have hz : ((Units.map g.toMonoidHom x ^ m : S'ˣ) : S') = g ((x ^ m : Sˣ) : S) := by
        rw [← map_zpow (Units.map g.toMonoidHom) x m, Units.coe_map]
        rfl
      rw [LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_T, hz]
  exact DFunLike.congr_fun h l

private lemma umap_coe (φ : F ≃+* F) (z : Fˣ) :
    ((Units.map (φ : F →+* F).toMonoidHom z : Fˣ) : F) = φ (z : F) := rfl

/-- The φ-transported stage: same ℤ_p-side data, same `K`/`FQ` (φ-stable in finite F),
residual map conjugated coefficientwise by the induced automorphism of `↥K`. -/
private noncomputable def stageMap (φ : F ≃+* F) (σ : Stage p F) : Stage p F :=
  { σ with
    R := fun f => lmap ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K) (σ.R f)
    hR0 := by rw [σ.hR0, map_zero]
    hRne := fun f hf h =>
      σ.hRne f hf (lmap_injective (resAut φ σ.K) (h.trans (map_zero _).symm))
    hRmul := fun f g hf hg => by rw [σ.hRmul f g hf hg, map_mul]
    hRadd := fun f g hf hg hfg hw hww => by rw [σ.hRadd f g hf hg hfg hw hww, map_add]
    hRlt := fun f g hf hg hfg hlt => by rw [σ.hRlt f g hf hg hfg hlt]
    hRΦ := by rw [σ.hRΦ, lmap_T]
    hS5 := by
      intro B hB hBC
      obtain ⟨c, hc⟩ := σ.hS5 B hB hBC
      exact ⟨Units.map ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K).toMonoidHom c,
        by rw [hc, lmap_C_mul_T]; rfl⟩
    hS6a := by
      intro ν hν c hcF
      set c₀ : (↥σ.K)ˣ :=
        Units.map (((resAut φ σ.K).symm : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K).toMonoidHom c
        with hc₀
      have hmem : ((c₀ : ↥σ.K) : F) ∈ σ.FQ := by
        have h1 : ((c₀ : ↥σ.K) : F) = φ.symm ((c : ↥σ.K) : F) := rfl
        rw [h1]
        exact mem_map_self φ.symm σ.FQ hcF
      obtain ⟨B, hB0, hBC, hBw, hBR⟩ := σ.hS6a ν hν c₀ hmem
      refine ⟨B, hB0, hBC, hBw, ?_⟩
      rw [hBR, lmap_C_mul_T]
      have h2 : ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K)
            ((c₀ : (↥σ.K)ˣ) : ↥σ.K) = ((c : (↥σ.K)ˣ) : ↥σ.K) :=
        (resAut φ σ.K).apply_symm_apply _
      rw [h2]
    hS6b := by
      intro ν a hν
      set a₀ : (↥σ.K)ˣ :=
        Units.map (((resAut φ σ.K).symm : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K).toMonoidHom a
        with ha₀
      obtain ⟨B, hB0, hBC, hBw, hBR⟩ := σ.hS6b ν a₀ hν
      refine ⟨B, hB0, hBC, hBw, ?_⟩
      rw [hBR, lmap_C_mul_T]
      have h2 : ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K)
            ((a₀ : (↥σ.K)ˣ) : ↥σ.K) = ((a : (↥σ.K)ˣ) : ↥σ.K) :=
        (resAut φ σ.K).apply_symm_apply _
      rw [h2] }

private lemma stageMap_R (φ : F ≃+* F) (σ : Stage p F) (f : Polynomial ℤ_[p]) :
    (stageMap φ σ).R f
      = lmap ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K) (σ.R f) := rfl

/-- `digPrime` is φ-equivariant under the stage transport. -/
private lemma digPrime_stageMap (φ : F ≃+* F) (σ : Stage p F) (z : Fˣ)
    (B : Polynomial ℤ_[p]) :
    (stageMap φ σ).digPrime (Units.map (φ : F →+* F).toMonoidHom z) B
      = φ (σ.digPrime z B) := by
  show LaurentPolynomial.eval₂ σ.K.subtype _
      (lmap ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K) (σ.R B)) = _
  rw [eval₂_lmap, subtype_comp_resAut]
  exact (hom_eval₂_laurent σ.K.subtype (φ : F →+* F) z (σ.R B)).symm

private lemma poly_map_equiv_dvd_iff {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (a b : Polynomial R) :
    a.map (e : R →+* S) ∣ b.map (e : R →+* S) ↔ a ∣ b := by
  constructor
  · intro h
    have h2 := map_dvd (Polynomial.mapRingHom (e.symm : S →+* R)) h
    have hcomp : ((e.symm : S →+* R)).comp (e : R →+* S) = RingHom.id R :=
      RingEquiv.symm_toRingHom_comp_toRingHom e
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_map, hcomp,
      Polynomial.map_id] at h2
    exact h2
  · exact fun h => map_dvd (Polynomial.mapRingHom (e : R →+* S)) h

/-- The φ-transported node: same frame `K` (φ-stable), residue-side data conjugated by
the induced automorphism, ℤ_p-side and numeric data unchanged. -/
private noncomputable def nodeMap (φ : F ≃+* F) (ν : Node p F) : Node p F :=
  { ν with
    σ := stageMap φ ν.σ
    zbar := Units.map (φ : F →+* F).toMonoidHom ν.zbar
    center := resAut φ ν.σ.K ν.center
    ψ := ν.ψ.map ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K)
    pat := fun k => resAut φ ν.σ.K (ν.pat k)
    Ranch := ν.Ranch.map ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K)
    hDwidth := ν.hDwidth
    hψmonic := ν.hψmonic.map _
    hψdeg := by rw [Polynomial.natDegree_map]; exact ν.hψdeg
    hψirr := by
      have h := Irreducible.map (Polynomial.mapEquiv (resAut φ ν.σ.K)) ν.hψirr
      rwa [Polynomial.mapEquiv_apply] at h
    hRanch := by
      rw [ν.hRanch, Polynomial.map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
      rfl
    hpat0 := by
      intro h
      apply ν.hpat0
      have h' : (resAut φ ν.σ.K) (ν.pat 0) = (0 : ↥ν.σ.K) := h
      have h2 := congrArg (resAut φ ν.σ.K).symm h'
      rwa [RingEquiv.symm_apply_apply, map_zero] at h2
    hpatTop := by
      intro h
      apply ν.hpatTop
      have h' : (resAut φ ν.σ.K) (ν.pat (ν.wSide / ν.e)) = (0 : ↥ν.σ.K) := h
      have h2 := congrArg (resAut φ ν.σ.K).symm h'
      rwa [RingEquiv.symm_apply_apply, map_zero] at h2
    hOrd := by
      show OrdPsiPoly
        (ν.ψ.map ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K))
        (ν.Ranch.map ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K)) ν.μ
      obtain ⟨h1, h2⟩ := ν.hOrd
      constructor
      · have h3 := map_dvd (Polynomial.mapRingHom
          ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K)) h1
        simpa [Polynomial.map_pow] using h3
      · intro hdvd
        apply h2
        rw [← Polynomial.map_pow] at hdvd
        exact (poly_map_equiv_dvd_iff (resAut φ ν.σ.K) _ _).mp hdvd
    hzbarRoot := by
      show Polynomial.eval₂ ν.σ.K.subtype
          ((Units.map (φ : F →+* F).toMonoidHom ν.zbar : Fˣ) : F)
          (ν.ψ.map ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K)) = 0
      rw [Polynomial.eval₂_map, subtype_comp_resAut]
      have h := Polynomial.hom_eval₂ ν.ψ ν.σ.K.subtype (φ : F →+* F) ((ν.zbar : Fˣ) : F)
      rw [ν.hzbarRoot, map_zero] at h
      exact h.symm
    hspecRecCenter := by
      intro hspec
      obtain ⟨h1, h2⟩ := ν.hspecRecCenter hspec
      constructor
      · rw [h1, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        rfl
      · show φ ((ν.zbar : Fˣ) : F) = _
        exact congrArg φ h2 }

@[simp] private lemma nodeMap_species (φ : F ≃+* F) (ν : Node p F) :
    (nodeMap φ ν).species = ν.species := rfl
@[simp] private lemma nodeMap_K (φ : F ≃+* F) (ν : Node p F) :
    (nodeMap φ ν).σ.K = ν.σ.K := rfl
@[simp] private lemma nodeMap_zbar_coe (φ : F ≃+* F) (ν : Node p F) :
    (((nodeMap φ ν).zbar : Fˣ) : F) = φ ((ν.zbar : Fˣ) : F) := rfl
@[simp] private lemma nodeMap_sideDigit (φ : F ≃+* F) (ν : Node p F) (k : ℕ) :
    (nodeMap φ ν).sideDigit k = φ (ν.sideDigit k) := rfl
@[simp] private lemma nodeMap_childWidth (φ : F ≃+* F) (ν : Node p F) :
    (nodeMap φ ν).childWidth = ν.childWidth := rfl
@[simp] private lemma nodeMap_mhat (φ : F ≃+* F) (ν : Node p F) :
    (nodeMap φ ν).mhat = ν.mhat := rfl

/-- The φ-transported history. -/
private noncomputable def historyMap (φ : F ≃+* F) (H : History p F) : History p F where
  nodes := H.nodes.map (nodeMap φ)
  nonempty := fun h => H.nonempty (List.map_eq_nil_iff.mp h)
  root_iff := by
    intro j hj
    have hj' : j < H.nodes.length := by simpa using hj
    rw [List.getElem_map]
    exact H.root_iff j hj'

@[simp] private lemma historyMap_length (φ : F ≃+* F) (H : History p F) :
    (historyMap φ H).nodes.length = H.nodes.length := by
  show (H.nodes.map (nodeMap φ)).length = _
  simp

private lemma historyMap_getElem (φ : F ≃+* F) (H : History p F) (r : ℕ)
    (hr : r < (historyMap φ H).nodes.length) (hr' : r < H.nodes.length) :
    (historyMap φ H).nodes[r]'hr = nodeMap φ (H.nodes[r]'hr') :=
  List.getElem_map _

private lemma historyMap_strFrame (φ : F ≃+* F) (H : History p F) (i : ℕ) :
    (historyMap φ H).strFrame i = H.strFrame i := by
  show (((H.nodes.map (nodeMap φ)).take i).map Node.e).prod
      = ((H.nodes.take i).map Node.e).prod
  rw [← List.map_take, List.map_map]
  rfl

private lemma psiImage_nodeMap (φ : F ≃+* F) (ν : Node p F) :
    ψImage (nodeMap φ ν) = (ψImage ν).map (φ : F →+* F) := by
  show (ν.ψ.map ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K)).map
      ν.σ.K.subtype = (ν.ψ.map ν.σ.K.subtype).map (φ : F →+* F)
  rw [Polynomial.map_map, Polynomial.map_map, subtype_comp_resAut]

private lemma canonRoot_nodeMap_of_fix (φ : F ≃+* F) (ν : Node p F)
    (hfix : ∀ x ∈ ν.σ.K, φ x = x) :
    canonRoot (nodeMap φ ν) = canonRoot ν := by
  have hψ : ψImage (nodeMap φ ν) = ψImage ν := by
    rw [psiImage_nodeMap]
    ext k
    rw [Polynomial.coeff_map]
    have hc : (ψImage ν).coeff k ∈ ν.σ.K := by
      show (ν.ψ.map ν.σ.K.subtype).coeff k ∈ ν.σ.K
      rw [Polynomial.coeff_map]
      exact (ν.ψ.coeff k).2
    exact hfix _ hc
  simp only [canonRoot, hψ]

private lemma matches_nodeMap (φ : F ≃+* F) (R : ShapeRead) (ν : Node p F)
    (hm : R.Matches ν) : R.Matches (nodeMap φ ν) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hm
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, fun hmt => ?_⟩
  rw [nodeMap_sideDigit, h13 hmt, map_one]

private lemma matchesHist_historyMap (φ : F ≃+* F) (P : ShapePrefix) (H : History p F)
    (hm : P.MatchesHist H) : P.MatchesHist (historyMap φ H) := by
  obtain ⟨hlen, hall⟩ := hm
  refine ⟨by simpa using hlen, ?_⟩
  intro r hr
  have hr' : r < H.nodes.length := by simpa using hr
  rw [historyMap_getElem φ H r hr hr']
  exact matches_nodeMap φ _ _ (hall r hr')

private lemma vtxPoly_nodeMap (φ : F ≃+* F) (ν : Node p F) :
    (nodeMap φ ν).vtxPoly
      = ν.vtxPoly.map ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K) := by
  show ((ν.Ranch.map _) /ₘ (ν.ψ.map _) ^ ν.μ) %ₘ (ν.ψ.map _) = _
  rw [← Polynomial.map_pow, ← Polynomial.map_divByMonic _ (ν.hψmonic.pow _),
    ← Polynomial.map_modByMonic _ ν.hψmonic]
  rfl

private lemma vtx_nodeMap (φ : F ≃+* F) (ν : Node p F) :
    (nodeMap φ ν).vtx = φ ν.vtx := by
  simp only [Node.vtx]
  rw [vtxPoly_nodeMap, map_mul]
  congr 1
  · show ((Units.map (φ : F →+* F).toMonoidHom ν.zbar
        ^ (ν.a - (ν.μ : ℤ) * (nodeMap φ ν).mhat) : Fˣ) : F) = _
    rw [nodeMap_mhat, ← map_zpow (Units.map (φ : F →+* F).toMonoidHom) ν.zbar,
      Units.coe_map]
    rfl
  · show Polynomial.eval₂ ν.σ.K.subtype
        ((Units.map (φ : F →+* F).toMonoidHom ν.zbar : Fˣ) : F) (ν.vtxPoly.map _) = _
    rw [Polynomial.eval₂_map, subtype_comp_resAut]
    exact (Polynomial.hom_eval₂ _ ν.σ.K.subtype (φ : F →+* F) _).symm

private lemma etaData_historyMap (φ : F ≃+* F) (P : ShapePrefix) (H : History p F)
    (r : Fin P.reads.length) :
    ((etaData P (historyMap φ H) r).1 = fun k => φ ((etaData P H r).1 k)) ∧
    ((etaData P (historyMap φ H) r).2 = fun k => φ ((etaData P H r).2 k)) := by
  have hopt : (historyMap φ H).nodes[(r : ℕ)]? = (H.nodes[(r : ℕ)]?).map (nodeMap φ) :=
    List.getElem?_map ..
  cases hcase : H.nodes[(r : ℕ)]? with
  | none =>
    constructor <;>
    · funext k
      simp [etaData, hopt, hcase]
  | some ν =>
    constructor
    · funext k
      simp only [etaData, hopt, hcase, Option.map_some, Option.elim]
      rfl
    · funext k
      simp only [etaData, hopt, hcase, Option.map_some, Option.elim]
      show (((ν.ψ.map _).coeff (k : ℕ) : ↥ν.σ.K) : F) = φ ((ν.ψ.coeff (k : ℕ) : ↥ν.σ.K) : F)
      rw [Polynomial.coeff_map]
      rfl

private lemma zbar_historyMap (φ : F ≃+* F) (H : History p F) (r : ℕ)
    (hr : r < (historyMap φ H).nodes.length) (hr' : r < H.nodes.length) :
    ((((historyMap φ H).nodes[r]'hr).zbar : Fˣ) : F)
      = φ (((H.nodes[r]'hr').zbar : Fˣ) : F) := by
  rw [historyMap_getElem φ H r hr hr']
  rfl

private lemma subfield_map_closure (f : F →+* F) (s : Set F) :
    (Subfield.closure s).map f = Subfield.closure (f '' s) := by
  apply le_antisymm
  · exact (Subfield.gc_map_comap f).l_le (Subfield.closure_le.mpr fun x hx =>
      Subfield.subset_closure (Set.mem_image_of_mem f hx))
  · refine Subfield.closure_le.mpr ?_
    rw [Subfield.coe_map]
    exact Set.image_mono Subfield.subset_closure

private lemma nextField_stageMap (φ : F ≃+* F) (σ : Stage p F) (z : Fˣ) :
    (stageMap φ σ).nextField (Units.map (φ : F →+* F).toMonoidHom z)
      = (σ.nextField z).map (φ : F →+* F) := by
  show Subfield.closure
      (↑σ.K ∪ {((Units.map (φ : F →+* F).toMonoidHom z : Fˣ) : F)})
    = (Subfield.closure (↑σ.K ∪ {((z : Fˣ) : F)})).map (φ : F →+* F)
  rw [subfield_map_closure, Set.image_union, Set.image_singleton]
  have hK : (φ : F →+* F) '' ↑σ.K = ↑σ.K := by
    rw [← Subfield.coe_map, subfield_map_eq]
  rw [hK]
  rfl

private lemma ratJ_nzd (φ : F ≃+* F) :
    nonZeroDivisors (Polynomial F) ≤ Submonoid.comap
      (Polynomial.mapRingHom (φ : F →+* F)) (nonZeroDivisors (Polynomial F)) := by
  intro q hq
  rw [Submonoid.mem_comap]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hq ⊢
  intro h
  exact hq ((Polynomial.map_eq_zero_iff φ.injective).mp h)

/-- The φ-induced ring endomorphism of `RatFunc F`. -/
private noncomputable def ratJ (φ : F ≃+* F) : RatFunc F →+* RatFunc F :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (φ : F →+* F)) (ratJ_nzd φ)

private lemma ratJ_algebraMap_poly (φ : F ≃+* F) (q : Polynomial F) :
    ratJ φ (algebraMap (Polynomial F) (RatFunc F) q)
      = algebraMap (Polynomial F) (RatFunc F) (q.map (φ : F →+* F)) := by
  have h := RatFunc.map_apply_div (Polynomial.mapRingHom (φ : F →+* F)) (ratJ_nzd φ) q 1
  simp only [map_one, div_one, Polynomial.coe_mapRingHom] at h
  show RatFunc.map (Polynomial.mapRingHom (φ : F →+* F)) (ratJ_nzd φ) _ = _
  rw [h]

private lemma ratJ_ratX (φ : F ≃+* F) :
    Units.map (ratJ φ).toMonoidHom (ratX F) = ratX F := by
  apply Units.ext
  show ratJ φ RatFunc.X = RatFunc.X
  rw [← RatFunc.algebraMap_X, ratJ_algebraMap_poly, Polynomial.map_X]

private lemma ratRes_stageMap (φ : F ≃+* F) (σ : Stage p F) (f : Polynomial ℤ_[p]) :
    (stageMap φ σ).ratRes f = ratJ φ (σ.ratRes f) := by
  show LaurentPolynomial.eval₂ ((algebraMap F (RatFunc F)).comp σ.K.subtype) (ratX F)
      (lmap ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K) (σ.R f))
    = ratJ φ (LaurentPolynomial.eval₂
        ((algebraMap F (RatFunc F)).comp σ.K.subtype) (ratX F) (σ.R f))
  rw [eval₂_lmap]
  have hhom : ((algebraMap F (RatFunc F)).comp σ.K.subtype).comp
      ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K)
      = (ratJ φ).comp ((algebraMap F (RatFunc F)).comp σ.K.subtype) := by
    apply RingHom.ext
    intro x
    show algebraMap F (RatFunc F) (φ (x : F)) = ratJ φ (algebraMap F (RatFunc F) (x : F))
    rw [IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F),
      IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F),
      ratJ_algebraMap_poly]
    congr 1
    show Polynomial.C (φ (x : F)) = (Polynomial.C ((x : ↥σ.K) : F)).map (φ : F →+* F)
    rw [Polynomial.map_C]
    rfl
  rw [hhom]
  have h2 := hom_eval₂_laurent ((algebraMap F (RatFunc F)).comp σ.K.subtype) (ratJ φ)
    (ratX F) (σ.R f)
  rw [ratJ_ratX] at h2
  exact h2.symm

private lemma resAut_ne_zero (φ : F ≃+* F) (K : Subfield F) {x : ↥K} (hx : x ≠ 0) :
    resAut φ K x ≠ 0 := by
  intro h
  apply hx
  have h2 := congrArg (resAut φ K).symm h
  rwa [RingEquiv.symm_apply_apply, map_zero] at h2

private lemma isRecentering_map (φ : F ≃+* F) {σ σ' : Stage p F} {cc : ↥σ.K}
    {tt : Polynomial ℤ_[p]} (h : IsRecentering σ σ' cc tt) :
    IsRecentering (stageMap φ σ) (stageMap φ σ') (resAut φ σ.K cc) tt := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨h1, h2, resAut_ne_zero φ σ.K h3, h4, h5, h6, ?_, h8, h9, h10, h11, h12, h13, ?_⟩
  · show lmap ((resAut φ σ.K : ↥σ.K ≃+* ↥σ.K) : ↥σ.K →+* ↥σ.K) (σ.R tt) = _
    rw [h7, lmap_C_mul_T]
    rfl
  · intro B hB hBC z
    have hz : z = Units.map (φ : F →+* F).toMonoidHom
        (Units.map (φ.symm : F →+* F).toMonoidHom z) :=
      Units.ext (φ.apply_symm_apply (z : F)).symm
    rw [hz, digPrime_stageMap, digPrime_stageMap, h14 B hB hBC _]

private lemma isRecenteringCore_map (φ : F ≃+* F) {σ σ' : Stage p F} {cc : ↥σ.K}
    {tt : Polynomial ℤ_[p]} (h : IsRecenteringCore σ σ' cc tt) :
    IsRecenteringCore (stageMap φ σ) (stageMap φ σ') (resAut φ σ.K cc) tt where
  base := isRecentering_map φ h.base
  coeff_R := fun B hBC => by
    rw [ratRes_stageMap, ratRes_stageMap, h.coeff_R B hBC]
  reps_eq := h.reps_eq
  Tvec_eq := h.Tvec_eq

private lemma transitionData_map (φ : F ≃+* F) {σ σ' : Stage p F}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {z : Fˣ}
    (h : TransitionData σ σ' Φhat e' h' z) :
    TransitionData (stageMap φ σ) (stageMap φ σ') Φhat e' h'
      (Units.map (φ : F →+* F).toMonoidHom z) where
  child_key := h.child_key
  child_e := h.child_e
  child_h := h.child_h
  child_field := by
    show σ'.K = (stageMap φ σ).nextField (Units.map (φ : F →+* F).toMonoidHom z)
    rw [nextField_stageMap]
    calc σ'.K = σ'.K.map (φ : F →+* F) := (subfield_map_eq φ σ'.K).symm
    _ = (σ.nextField z).map (φ : F →+* F) := by rw [h.child_field]
  field_grow := h.field_grow
  child_base := h.child_base
  child_wPrev := h.child_wPrev
  threshold := h.threshold
  child_slotmin := h.child_slotmin
  child_reps := h.child_reps

private lemma isNodeLift_map (φ : F ≃+* F) (ν : Node p F) (Φhat : Polynomial ℤ_[p])
    (h : IsNodeLift ν Φhat) : IsNodeLift (nodeMap φ ν) Φhat := by
  obtain ⟨tt, h0, hlt, hsum⟩ := h
  refine ⟨tt, ?_, ?_, hsum⟩
  · intro k hk
    apply h0 k
    have hk' : (ν.ψ.map ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K)).coeff k
        = 0 := hk
    rw [Polynomial.coeff_map] at hk'
    have hk'' : (resAut φ ν.σ.K) (ν.ψ.coeff k) = 0 := hk'
    have h2 := congrArg (resAut φ ν.σ.K).symm hk''
    rwa [RingEquiv.symm_apply_apply, map_zero] at h2
  · intro k hklt hkne
    have hkne' : ν.ψ.coeff k ≠ 0 := by
      intro h0'
      apply hkne
      show (ν.ψ.map ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K)).coeff k = 0
      rw [Polynomial.coeff_map, h0', map_zero]
    obtain ⟨ht1, ht2, ht3, ht4⟩ := hlt k hklt hkne'
    refine ⟨ht1, ht2, ht3, ?_⟩
    show lmap ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K) (ν.σ.R (tt k)) = _
    rw [ht4, lmap_C_mul_T]
    have hco : (nodeMap φ ν).ψ.coeff k
        = ((resAut φ ν.σ.K : ↥ν.σ.K ≃+* ↥ν.σ.K) : ↥ν.σ.K →+* ↥ν.σ.K) (ν.ψ.coeff k) :=
      Polynomial.coeff_map _ _
    rw [hco]
    rfl

private lemma transitionCoreL_map (φ : F ≃+* F) {σ σ' : Stage p F}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {z : Fˣ}
    (h : TransitionCoreL σ σ' Φhat e' h' z) :
    TransitionCoreL (stageMap φ σ) (stageMap φ σ') Φhat e' h'
      (Units.map (φ : F →+* F).toMonoidHom z) where
  base := transitionData_map φ h.base
  child_Tvec := h.child_Tvec
  child_dig_frame := by
    obtain ⟨mfun, hm⟩ := h.child_dig_frame
    refine ⟨mfun, fun B hB hBC => ?_⟩
    obtain ⟨c', hc1, hc2⟩ := hm B hB hBC
    refine ⟨Units.map ((resAut φ σ'.K : ↥σ'.K ≃+* ↥σ'.K) : ↥σ'.K →+* ↥σ'.K).toMonoidHom c',
      ?_, ?_⟩
    · show lmap ((resAut φ σ'.K : ↥σ'.K ≃+* ↥σ'.K) : ↥σ'.K →+* ↥σ'.K) (σ'.R B) = _
      rw [hc1, lmap_C_mul_T]
      rfl
    · show φ ((c' : ↥σ'.K) : F) = _
      rw [hc2, map_mul]
      congr 1
      · exact (digPrime_stageMap φ σ z B).symm
      · rw [← map_zpow (Units.map (φ : F →+* F).toMonoidHom) z, Units.coe_map]
        rfl

/-- Coherence transports along φ. -/
private lemma historyCoherent_historyMap (φ : F ≃+* F) (H : History p F)
    (hcoh : HistoryCoherent H) : HistoryCoherent (historyMap φ H) := by
  obtain ⟨hroot, hslope, hgam, hstep⟩ := hcoh
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hj
    have hj' : 0 < H.nodes.length := by simpa using hj
    rw [historyMap_getElem φ H 0 hj hj']
    exact hroot hj'
  · intro i hi
    have hi' : i < H.nodes.length := by simpa using hi
    rw [historyMap_getElem φ H i hi hi', historyMap_strFrame]
    exact hslope i hi'
  · intro i hi
    have hi' : i < H.nodes.length := by simpa using hi
    rw [historyMap_getElem φ H i hi hi', historyMap_strFrame]
    exact hgam i hi'
  · intro i hi
    have hi1 : i + 1 < H.nodes.length := by simpa using hi
    have hi0 : i < H.nodes.length := by omega
    obtain ⟨hrec, hnonrec, hs, ht, hwin, hDw, hlt⟩ := hstep i hi1
    rw [historyMap_getElem φ H i (by omega) hi0, historyMap_getElem φ H (i + 1) hi hi1]
    refine ⟨fun hsp => ?_, fun hsp => ?_, hs, ht, hwin, hDw, hlt⟩
    · exact isRecenteringCore_map φ (hrec hsp)
    · obtain ⟨hlift, hcore⟩ := hnonrec hsp
      exact ⟨isNodeLift_map φ _ _ hlift, transitionCoreL_map φ hcore⟩

private lemma transitionAdmissible_map (φ : F ≃+* F) (νp ν : Node p F)
    (h : TransitionAdmissible νp ν) :
    TransitionAdmissible (nodeMap φ νp) (nodeMap φ ν) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun heq => ?_, h3, h4⟩
  show ((resAut φ ν.σ.K (ν.pat (ν.wSide / ν.e)) : ↥ν.σ.K) : F) = (nodeMap φ νp).vtx
  rw [vtx_nodeMap, resAut_coe]
  exact congrArg φ (h2 heq)

private lemma realizable_historyMap (φ : F ≃+* F) (H : History p F)
    (hreal : Realizable H) : Realizable (historyMap φ H) := by
  intro i hi
  have hi1 : i + 1 < H.nodes.length := by simpa using hi
  have hi0 : i < H.nodes.length := by omega
  rw [historyMap_getElem φ H i (by omega) hi0, historyMap_getElem φ H (i + 1) hi hi1]
  exact transitionAdmissible_map φ _ _ (hreal i hi1)

private lemma inBox_historyMap (φ : F ≃+* F) (n : ℕ) (H : History p F)
    (hbox : InBox n H) : InBox n (historyMap φ H) := by
  intro hj
  have hj' : 0 < H.nodes.length := by simpa using hj
  rw [historyMap_getElem φ H 0 hj hj']
  exact hbox hj'

private lemma etaGalEq_refl (P : ShapePrefix) (d : EtaData F P) : EtaGalEq d d :=
  ⟨RingEquiv.refl F, fun _ => ⟨funext fun _ => rfl, funext fun _ => rfl⟩⟩

private lemma etaGalEq_step (φ : F ≃+* F) (P : ShapePrefix) (H H₁ : History p F)
    (h : EtaGalEq (etaData P H) (etaData P H₁)) :
    EtaGalEq (etaData P H) (etaData P (historyMap φ H₁)) := by
  obtain ⟨φ₀, h₀⟩ := h
  refine ⟨φ₀.trans φ, fun r => ?_⟩
  obtain ⟨ha, hb⟩ := etaData_historyMap φ P H₁ r
  obtain ⟨ha₀, hb₀⟩ := h₀ r
  constructor
  · rw [ha, ha₀]
    funext k
    rfl
  · rw [hb, hb₀]
    funext k
    rfl

/-- Tower containment from coherence: every earlier frame subfield, and every earlier
recorded root, lies inside the current frame subfield (recentering keeps `K` and the root
IS the center; a genuine transition grows `K' = K⟮z̄⟯ ∋ z̄`). -/
private lemma tower_mem (H : History p F) (hcoh : HistoryCoherent H) :
    ∀ i (hi : i < H.nodes.length) r (hr : r < i),
      (H.nodes[r]'(by omega)).σ.K ≤ (H.nodes[i]'hi).σ.K ∧
      (((H.nodes[r]'(by omega)).zbar : Fˣ) : F) ∈ (H.nodes[i]'hi).σ.K := by
  intro i
  induction i with
  | zero => intro hi r hr; omega
  | succ n ih =>
    intro hi r hr
    obtain ⟨hroot, hslope, hgam, hstep⟩ := hcoh
    have hn1 : n + 1 < H.nodes.length := hi
    have hn : n < H.nodes.length := by omega
    have hKle : (H.nodes[n]'hn).σ.K ≤ (H.nodes[n + 1]'hn1).σ.K ∧
        (((H.nodes[n]'hn).zbar : Fˣ) : F) ∈ (H.nodes[n + 1]'hn1).σ.K := by
      obtain ⟨hrec, hnonrec, _, _, _, _, _⟩ := hstep n hn1
      by_cases hsp : (H.nodes[n]'hn).species = ReadSpecies.recentering
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, hK, _, _, _⟩ := (hrec hsp).base
        constructor
        · rw [hK]
        · rw [hK]
          obtain ⟨_, hcen⟩ := (H.nodes[n]'hn).hspecRecCenter hsp
          rw [hcen]
          exact ((H.nodes[n]'hn).center).2
      · obtain ⟨_, hcore⟩ := hnonrec hsp
        refine ⟨hcore.base.field_grow, ?_⟩
        rw [hcore.base.child_field]
        exact Subfield.subset_closure (Set.mem_union_right _ rfl)
    rcases Nat.lt_or_ge r n with hrn | hrn
    · obtain ⟨ih1, ih2⟩ := ih hn r hrn
      exact ⟨le_trans ih1 hKle.1, hKle.1 ih2⟩
    · have hrn' : r = n := by omega
      subst hrn'
      exact hKle

end TransportInfra

/-- U17b-3 — data transport: an ambient automorphism transports a coherent realizable
history to a coherent realizable history with φ-conjugated η-data and φ-mapped roots
(a ring-iso commutes with every clause in Node's Prop fields — mechanical but long). -/
theorem galois_transport (φ : F ≃+* F) (H : History p F)
    (hcoh : HistoryCoherent H) (hreal : Realizable H) :
    ∃ H' : History p F,
      HistoryCoherent H' ∧ Realizable H' ∧
      H'.nodes.length = H.nodes.length ∧
      (∀ P : ShapePrefix, P.MatchesHist H → P.MatchesHist H') ∧
      (∀ P : ShapePrefix, P.MatchesHist H →
        ∀ r : Fin P.reads.length,
          ((etaData P H' r).1 = fun k => φ ((etaData P H r).1 k)) ∧
          ((etaData P H' r).2 = fun k => φ ((etaData P H r).2 k))) ∧
      (∀ (r : ℕ) (hr : r < H'.nodes.length) (hr' : r < H.nodes.length),
        (((H'.nodes[r]'hr).zbar : Fˣ) : F) = φ (((H.nodes[r]'hr').zbar : Fˣ) : F)) :=
  ⟨historyMap φ H, historyCoherent_historyMap φ H hcoh, realizable_historyMap φ H hreal,
    historyMap_length φ H, fun P hm => matchesHist_historyMap φ P H hm,
    fun P _ r => etaData_historyMap φ P H r,
    fun r hr hr' => zbar_historyMap φ H r hr hr'⟩

/-- U17b-2 — tower composition: normalize the roots of the first `i` reads (induction
carrier; the automorphism group of a finite field is cyclic, extension over the recorded
subfield tower is elementary Galois theory of finite fields). -/
theorem galois_normalize_upTo {n : ℕ} {P : Shape n} (H : History p F)
    (hm : (P : ShapePrefix).MatchesHist H) (hcoh : HistoryCoherent H)
    (hreal : Realizable H) (hbox : InBox n H) (i : ℕ) :
    ∃ H' : History p F,
      (P : ShapePrefix).MatchesHist H' ∧
      EtaGalEq (etaData (P : ShapePrefix) H) (etaData (P : ShapePrefix) H') ∧
      HistoryCoherent H' ∧ Realizable H' ∧ InBox n H' ∧
      (∀ (r : ℕ) (hr : r < H'.nodes.length), r < i →
        (((H'.nodes[r]'hr).zbar : Fˣ) : F) = canonRoot (H'.nodes[r]'hr)) := by
  induction i with
  | zero =>
    exact ⟨H, hm, etaGalEq_refl _ _, hcoh, hreal, hbox,
      fun r _ hri => absurd hri (Nat.not_lt_zero r)⟩
  | succ i ih =>
    obtain ⟨H₁, hm₁, hEta₁, hcoh₁, hreal₁, hbox₁, hnorm₁⟩ := ih
    by_cases hi : i < H₁.nodes.length
    · -- normalize read i via a root swap fixing its frame subfield pointwise
      obtain ⟨φ, hfix, hswap⟩ := galois_root_swap (H₁.nodes[i]'hi)
      refine ⟨historyMap φ H₁, matchesHist_historyMap φ _ H₁ hm₁,
        etaGalEq_step φ _ H H₁ hEta₁, historyCoherent_historyMap φ H₁ hcoh₁,
        realizable_historyMap φ H₁ hreal₁, inBox_historyMap φ n H₁ hbox₁, ?_⟩
      intro r hr hri
      have hr₁ : r < H₁.nodes.length := by simpa using hr
      rw [historyMap_getElem φ H₁ r hr hr₁]
      rcases Nat.lt_or_ge r i with hrlt | hrge
      · -- r < i: φ fixes the whole of node r's data (tower containment)
        obtain ⟨hKle, hzmem⟩ := tower_mem H₁ hcoh₁ i hi r hrlt
        have hfixr : ∀ x ∈ (H₁.nodes[r]'hr₁).σ.K, φ x = x := fun x hx => hfix x (hKle hx)
        have hzfix : φ (((H₁.nodes[r]'hr₁).zbar : Fˣ) : F)
            = (((H₁.nodes[r]'hr₁).zbar : Fˣ) : F) := hfix _ hzmem
        rw [nodeMap_zbar_coe, hzfix, canonRoot_nodeMap_of_fix φ _ hfixr]
        exact hnorm₁ r hr₁ hrlt
      · -- r = i: the swap lands the root on the canonical one
        have hri' : r = i := by omega
        subst hri'
        rw [nodeMap_zbar_coe, canonRoot_nodeMap_of_fix φ _ hfix]
        exact hswap
    · -- i beyond the history: nothing new to normalize
      refine ⟨H₁, hm₁, hEta₁, hcoh₁, hreal₁, hbox₁, fun r hr hri => hnorm₁ r hr ?_⟩
      omega

/-- U17b assembled — GALOIS NORMALIZATION: every matched coherent realizable in-box
history has a fully root-normalized Galois class-mate. -/
theorem galois_normalize {n : ℕ} {P : Shape n} (H : History p F)
    (hm : (P : ShapePrefix).MatchesHist H) (hcoh : HistoryCoherent H)
    (hreal : Realizable H) (hbox : InBox n H) :
    ∃ (φ : F ≃+* F) (H' : History p F),
      (P : ShapePrefix).MatchesHist H' ∧
      (∀ (r : ℕ) (hr : r < H'.nodes.length),
        (((H'.nodes[r]'hr).zbar : Fˣ) : F) = canonRoot (H'.nodes[r]'hr)) ∧
      (∀ r : Fin (P : ShapePrefix).reads.length,
        ((etaData (P : ShapePrefix) H' r).1
            = fun k => φ ((etaData (P : ShapePrefix) H r).1 k)) ∧
        ((etaData (P : ShapePrefix) H' r).2
            = fun k => φ ((etaData (P : ShapePrefix) H r).2 k))) ∧
      EtaGalEq (etaData (P : ShapePrefix) H) (etaData (P : ShapePrefix) H') ∧
      HistoryCoherent H' ∧ Realizable H' ∧ InBox n H' := by
  -- Normalize every read (`i := #reads`); the Galois witness of `EtaGalEq` is the `φ` sought.
  obtain ⟨H', hM', hEta, hcoh', hreal', hbox', hnorm⟩ :=
    galois_normalize_upTo H hm hcoh hreal hbox ((P : ShapePrefix).reads.length)
  obtain ⟨hlen', hmatch'⟩ := hM'
  obtain ⟨φ, hφ⟩ := hEta
  exact ⟨φ, H', ⟨hlen', hmatch'⟩,
    (fun r hr => hnorm r hr (hlen' ▸ hr)), hφ, ⟨φ, hφ⟩, hcoh', hreal', hbox'⟩

end LeanUrat.MovesJ
