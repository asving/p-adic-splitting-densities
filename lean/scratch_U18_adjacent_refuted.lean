/- SCRATCH (U18 obstruction, 2026-07-28): CONDITIONAL REFUTATION of the K3-RESTATED
`presentNorm_unique` — the form that GAINS `AdjacentReads H`/`AdjacentReads H'`.

CLAIM UNDER TEST: adding the adjacency hypotheses closes the Frobenius-conjugation escape.
IT DOES NOT. At an ADJACENT recentering, realizability's (HV) clause fires, but (HV) pins
ONLY the TOP pattern digit `pat(wSide/e) = νp.vtx` (`TransitionAdmissible`'s (HV) conjunct)
— a SINGLE field element. The CENTER (`ψ.coeff 0 = −center`, and `zbar = center`) is a
DIFFERENT element, and `canonRoot` is TRIVIAL at a recentering (ψ = X − C center has a
singleton root set), so canonicity does not pin it either. Hence a Frobenius-moved center
whose PARENT VERTEX VALUE `νp.vtx` is squaring-fixed (∈ 𝔽₂) still produces a SECOND PrefSet
member that is ADJACENT, same shape, EtaGalEq-related, with DISTINCT η-data.

This file MACHINE-CHECKS that: ANY 2-node witness (H = [ν₀, ν₁] ∈ PrefSet, read-0 residue
field squaring-fixed, ν₁ an ADJACENT recentering (s0+wSide = ν₀.μ), parent vertex value
ν₀.vtx squaring-fixed, (center)² ≠ center) refutes the K3-restated statement. The added
hypothesis vs. the non-adjacent scratch is exactly `hvtxfix : (ν₀.vtx)² = ν₀.vtx` (the
consequence of transporting (HV) through the conjugation), and `hnonadj` becomes `hadj`.

NOT part of the corpus; the standing machine record that the K3 adjacency guard is
INSUFFICIENT for U18 as typed. -/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-! ### The squaring automorphism (Frobenius) and its subfield restriction -/

/-- The squaring automorphism of a finite field of characteristic 2. -/
noncomputable def sqEquiv (E : Type*) [Field E] [Finite E] [CharP E 2] : E ≃+* E :=
  RingEquiv.ofBijective (frobenius E 2)
    (Finite.injective_iff_bijective.mp (frobenius E 2).injective)

lemma sqEquiv_apply (E : Type*) [Field E] [Finite E] [CharP E 2] (x : E) :
    sqEquiv E x = x ^ 2 := by
  simp [sqEquiv, frobenius_def]

/-- Commutation: the subfield squaring map is the ambient squaring on images. -/
lemma sqEquiv_coe {K : Subfield F4} (x : ↥K) :
    ((sqEquiv ↥K x : ↥K) : F4) = ((x : ↥K) : F4) ^ 2 := by
  simp [sqEquiv, frobenius_def]

/-- Round trip: mapping a polynomial by a ring equiv then by its inverse is the identity. -/
lemma map_map_symm {K : Type*} [Field K] (e : K ≃+* K) (f : Polynomial K) :
    (f.map (e : K →+* K)).map (e.symm : K →+* K) = f := by
  rw [Polynomial.map_map]
  have h : ((e.symm : K →+* K).comp (e : K →+* K)) = RingHom.id K := by
    ext x; simp
  rw [h, Polynomial.map_id]

/-- `canonRoot` of a node with linear ψ = X − C c is the center image. -/
lemma canonRoot_of_linear (ν : Node 2 F4) (c : ↥ν.σ.K)
    (hψ : ν.ψ = Polynomial.X - Polynomial.C c) :
    canonRoot ν = ((c : ↥ν.σ.K) : F4) := by
  unfold canonRoot ψImage
  rw [hψ]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C,
    Multiset.toFinset_singleton, Finset.image_singleton, Finset.min_singleton]
  exact (fieldEnum F4).symm_apply_apply _

/-! ### The conjugated recentering node -/

section ConjNode

variable (ν : Node 2 F4) (hrec : ν.species = ReadSpecies.recentering)

private noncomputable abbrev φK (ν : Node 2 F4) : ↥ν.σ.K ≃+* ↥ν.σ.K := sqEquiv ↥ν.σ.K

/-- The Frobenius-conjugate of a recentering node (lift field NOT yet re-normalized). -/
noncomputable def conjNode : Node 2 F4 :=
  { ν with
    zbar := ν.zbar ^ 2
    center := φK ν ν.center
    ψ := ν.ψ.map (φK ν : ↥ν.σ.K →+* ↥ν.σ.K)
    pat := fun k => φK ν (ν.pat k)
    Ranch := ν.Ranch.map (φK ν : ↥ν.σ.K →+* ↥ν.σ.K)
    hψmonic := by
      rw [(ν.hspecRecCenter hrec).1]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      exact monic_X_sub_C _
    hψdeg := by
      rw [(ν.hspecRecCenter hrec).1]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        natDegree_X_sub_C]
      exact ((ν.hspecRec hrec).2).symm
    hψirr := by
      rw [(ν.hspecRecCenter hrec).1]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      exact Polynomial.irreducible_X_sub_C _
    hRanch := by
      rw [ν.hRanch, Polynomial.map_sum]
      simp [Polynomial.map_mul, Polynomial.map_pow]
    hpat0 := by simpa using ν.hpat0
    hpatTop := by simpa using ν.hpatTop
    hOrd := by
      constructor
      · obtain ⟨q, hq⟩ := ν.hOrd.1
        exact ⟨q.map (φK ν : ↥ν.σ.K →+* ↥ν.σ.K), by
          rw [hq]; simp [Polynomial.map_mul, Polynomial.map_pow]⟩
      · rintro ⟨q, hq⟩
        refine ν.hOrd.2 ⟨q.map ((φK ν).symm : ↥ν.σ.K →+* ↥ν.σ.K), ?_⟩
        have := congrArg (Polynomial.map ((φK ν).symm : ↥ν.σ.K →+* ↥ν.σ.K)) hq
        rwa [map_map_symm, Polynomial.map_mul, Polynomial.map_pow, map_map_symm] at this
    hzbarRoot := by
      rw [(ν.hspecRecCenter hrec).1]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]
      rw [Units.val_pow_eq_pow_val, (ν.hspecRecCenter hrec).2]
      exact (sqEquiv_coe ν.center).symm
    hspecRecCenter := fun _ => ⟨by
        rw [(ν.hspecRecCenter hrec).1]
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        rfl, by
        rw [Units.val_pow_eq_pow_val, (ν.hspecRecCenter hrec).2]
        exact (sqEquiv_coe ν.center).symm⟩ }

/-- The conjugated node with the polOM-canonical lift installed. -/
noncomputable def conjNodeL : Node 2 F4 :=
  { conjNode ν hrec with lift := (polOM 2 F4).liftOf (conjNode ν hrec) }

@[simp] lemma conjNodeL_species : (conjNodeL ν hrec).species = ν.species := rfl
@[simp] lemma conjNodeL_σ : (conjNodeL ν hrec).σ = ν.σ := rfl
@[simp] lemma conjNodeL_e : (conjNodeL ν hrec).e = ν.e := rfl
@[simp] lemma conjNodeL_h : (conjNodeL ν hrec).h = ν.h := rfl
@[simp] lemma conjNodeL_s : (conjNodeL ν hrec).s = ν.s := rfl
@[simp] lemma conjNodeL_t : (conjNodeL ν hrec).t = ν.t := rfl
@[simp] lemma conjNodeL_g : (conjNodeL ν hrec).g = ν.g := rfl
@[simp] lemma conjNodeL_μ : (conjNodeL ν hrec).μ = ν.μ := rfl
@[simp] lemma conjNodeL_a : (conjNodeL ν hrec).a = ν.a := rfl
@[simp] lemma conjNodeL_s0 : (conjNodeL ν hrec).s0 = ν.s0 := rfl
@[simp] lemma conjNodeL_wSide : (conjNodeL ν hrec).wSide = ν.wSide := rfl
@[simp] lemma conjNodeL_Dwidth : (conjNodeL ν hrec).Dwidth = ν.Dwidth := rfl
@[simp] lemma conjNodeL_line : (conjNodeL ν hrec).line = ν.line := rfl
@[simp] lemma conjNodeL_ustar : (conjNodeL ν hrec).ustar = ν.ustar := rfl
@[simp] lemma conjNodeL_gam : (conjNodeL ν hrec).gam = ν.gam := rfl
@[simp] lemma conjNodeL_zbar : (conjNodeL ν hrec).zbar = ν.zbar ^ 2 := rfl
@[simp] lemma conjNodeL_center : (conjNodeL ν hrec).center = φK ν ν.center := rfl
@[simp] lemma conjNodeL_ψ :
    (conjNodeL ν hrec).ψ = ν.ψ.map (φK ν : ↥ν.σ.K →+* ↥ν.σ.K) := rfl
@[simp] lemma conjNodeL_pat : (conjNodeL ν hrec).pat = fun k => φK ν (ν.pat k) := rfl

/-- The polOM lift law holds at the conjugated node (blindness of the policy). -/
lemma conjNodeL_lift : (conjNodeL ν hrec).lift = (polOM 2 F4).liftOf (conjNodeL ν hrec) :=
  ((polOM 2 F4).blind (conjNode ν hrec) _).symm

/-- The conjugated side digits are the squares of the recorded ones. -/
lemma conjNodeL_sideDigit (k : ℕ) :
    (conjNodeL ν hrec).sideDigit k = (ν.sideDigit k) ^ 2 := by
  unfold Node.sideDigit
  exact sqEquiv_coe (ν.pat k)

/-- The conjugated ψ-coefficient images are the squares of the recorded ones. -/
lemma conjNodeL_ψcoeff (k : ℕ) :
    (((conjNodeL ν hrec).ψ.coeff k : ↥(conjNodeL ν hrec).σ.K) : F4)
      = ((ν.ψ.coeff k : ↥ν.σ.K) : F4) ^ 2 := by
  show (((ν.ψ.map (φK ν : ↥ν.σ.K →+* ↥ν.σ.K)).coeff k : ↥ν.σ.K) : F4) = _
  rw [Polynomial.coeff_map]
  exact sqEquiv_coe (ν.ψ.coeff k)

end ConjNode

/-! ### The refutation of the K3-restated (adjacency-guarded) statement -/

/-- **U18 (K3 FORM) REFUTED BY ANY SUCH WITNESS**: a 2-node PrefSet member whose root read's
residue field is squaring-fixed elementwise and whose last node is an ADJACENT recentering
with a Frobenius-moved center — the parent vertex value squaring-fixed — refutes the
K3-restated `presentNorm_unique` (WITH the `AdjacentReads` hypotheses) at p = 2, F = F4. -/
theorem presentNorm_unique_K3_refuted_by_witness
    {n : ℕ} {P : Shape n} (H : History 2 F4) (ν₀ ν₁ : Node 2 F4)
    (hnodes : H.nodes = [ν₀, ν₁])
    (hH : H ∈ PrefSet n (polOM 2 F4) P)
    (hK0 : ∀ x : ↥ν₀.σ.K, ((x : ↥ν₀.σ.K) : F4) ^ 2 = ((x : ↥ν₀.σ.K) : F4))
    (hrec : ν₁.species = ReadSpecies.recentering)
    (hadj : ν₁.s0 + ν₁.wSide = ν₀.μ)
    (hvtxfix : (ν₀.vtx : F4) ^ 2 = ν₀.vtx)
    (hmove : ((ν₁.center : ↥ν₁.σ.K) : F4) ^ 2 ≠ ((ν₁.center : ↥ν₁.σ.K) : F4)) :
    ¬ (∀ H1 H2 : History 2 F4,
        H1 ∈ PrefSet n (polOM 2 F4) P → H2 ∈ PrefSet n (polOM 2 F4) P →
        AdjacentReads H1 → AdjacentReads H2 →
        EtaGalEq (etaData (P : ShapePrefix) H1) (etaData (P : ShapePrefix) H2) →
        etaData (P : ShapePrefix) H1 = etaData (P : ShapePrefix) H2) := by
  intro hU18
  classical
  obtain ⟨nodes, hne0, hri0⟩ := H
  have hnodes' : nodes = [ν₀, ν₁] := hnodes
  subst hnodes'
  have hne := hne0
  have hri := hri0
  obtain ⟨hMatch, hCoh, hReal, hBox, hCanon, hZbar⟩ := hH
  have hroot' : ∀ (j : ℕ) (hj : j < ([ν₀, conjNodeL ν₁ hrec] : List (Node 2 F4)).length),
      (([ν₀, conjNodeL ν₁ hrec] : List (Node 2 F4))[j]'hj).species = ReadSpecies.root
        ↔ j = 0 := by
    intro j hj
    match j with
    | 0 => simpa using hri 0 (by simp)
    | 1 =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, conjNodeL_species, hrec]
      simp
    | (m+2) => exact absurd (by simpa using hj) (by omega)
  have hne' : ([ν₀, conjNodeL ν₁ hrec] : List (Node 2 F4)) ≠ [] := by simp
  -- membership of the conjugated history
  have hH'mem : (⟨[ν₀, conjNodeL ν₁ hrec], hne', hroot'⟩ : History 2 F4)
      ∈ PrefSet n (polOM 2 F4) P := by
    obtain ⟨hlen, hmr⟩ := hMatch
    refine ⟨⟨hlen, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · -- MatchesHist (read-wise)
      intro r hr
      match r with
      | 0 => exact hmr 0 (by simp)
      | 1 =>
        obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13⟩ :=
          hmr 1 (by simp)
        refine ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, ?_⟩
        intro hm
        have h13 : ∀ k, ν₁.sideDigit k = 1 → (conjNodeL ν₁ hrec).sideDigit k = 1 := by
          intro k hk
          rw [conjNodeL_sideDigit, hk]
          norm_num
        exact h13 _ (m13 hm)
      | (m+2) => exact absurd (by simpa using hr) (by omega)
    · -- HistoryCoherent
      obtain ⟨c1, c2, c3, c4⟩ := hCoh
      refine ⟨fun hj => c1 (by simp), ?_, ?_, ?_⟩
      · intro i hi
        match i with
        | 0 => exact c2 0 (by simp)
        | 1 => exact c2 1 (by simp)
        | (m+2) => exact absurd (by simpa using hi) (by omega)
      · intro i hi
        match i with
        | 0 => exact c3 0 (by simp)
        | 1 => exact c3 1 (by simp)
        | (m+2) => exact absurd (by simpa using hi) (by omega)
      · intro i hi
        match i with
        | 0 => exact c4 0 (by simp)
        | (m+1) => exact absurd (by simpa using hi) (by omega)
    · -- Realizable — the ADJACENT branch: (NA)/(SAE) transfer (geometry-invariant);
      -- (HV) transfers because ν₀.vtx is squaring-fixed (hvtxfix).
      intro i hi
      match i with
      | 0 =>
        obtain ⟨r1, r2, r3, r4⟩ := hReal 0 (by simp)
        refine ⟨r1, ?_, r3, r4⟩
        intro _
        simp only [List.getElem_cons_succ, List.getElem_cons_zero, conjNodeL_pat,
          conjNodeL_wSide, conjNodeL_e]
        have hpat : ((ν₁.pat (ν₁.wSide / ν₁.e) : ↥ν₁.σ.K) : F4) = ν₀.vtx := r2 hadj
        have hstep : ((φK ν₁ (ν₁.pat (ν₁.wSide / ν₁.e)) : ↥ν₁.σ.K) : F4)
            = ((ν₁.pat (ν₁.wSide / ν₁.e) : ↥ν₁.σ.K) : F4) ^ 2 :=
          sqEquiv_coe (ν₁.pat (ν₁.wSide / ν₁.e))
        rw [hstep, hpat, hvtxfix]
      | (m+1) => exact absurd (by simpa using hi) (by omega)
    · -- InBox
      intro hj
      exact hBox (by simp)
    · -- IsCanon
      intro r hr
      match r with
      | 0 => exact hCanon 0 (by simp)
      | 1 => exact conjNodeL_lift ν₁ hrec
      | (m+2) => exact absurd (by simpa using hr) (by omega)
    · -- canonical residue roots
      intro r hr
      match r with
      | 0 => exact hZbar 0 (by simp)
      | 1 =>
        show (((conjNodeL ν₁ hrec).zbar : F4ˣ) : F4) = canonRoot (conjNodeL ν₁ hrec)
        rw [canonRoot_of_linear (conjNodeL ν₁ hrec) (conjNodeL ν₁ hrec).center
          (((conjNodeL ν₁ hrec).hspecRecCenter hrec).1)]
        exact ((conjNodeL ν₁ hrec).hspecRecCenter hrec).2
      | (m+2) => exact absurd (by simpa using hr) (by omega)
  -- AdjacentReads for both histories (2-node: the single i = 0 clause = hadj)
  have hAdjH : AdjacentReads (⟨[ν₀, ν₁], hne, hri⟩ : History 2 F4) := by
    intro i hi1
    match i with
    | 0 => exact hadj
    | (m+1) => exact absurd (by simpa using hi1) (by omega)
  have hAdjH' : AdjacentReads (⟨[ν₀, conjNodeL ν₁ hrec], hne', hroot'⟩ : History 2 F4) := by
    intro i hi1
    match i with
    | 0 => exact hadj
    | (m+1) => exact absurd (by simpa using hi1) (by omega)
  -- lengths
  have hPlen : (P : ShapePrefix).reads.length = 2 := by
    obtain ⟨hlen, -⟩ := hMatch
    simpa using hlen.symm
  -- the Galois relation between the two η-data (Frobenius on F4)
  have hGal : EtaGalEq (etaData (P : ShapePrefix) (⟨[ν₀, ν₁], hne, hri⟩ : History 2 F4))
      (etaData (P : ShapePrefix)
        (⟨[ν₀, conjNodeL ν₁ hrec], hne', hroot'⟩ : History 2 F4)) := by
    refine ⟨sqEquiv F4, ?_⟩
    intro r
    have hr2 : (r : ℕ) < 2 := by rw [← hPlen]; exact r.isLt
    constructor
    · funext k
      match hrv : (r : ℕ), hr2 with
      | 0, _ =>
        simp only [etaData, hrv, List.getElem?_cons_zero, Option.elim_some, sqEquiv_apply]
        exact (hK0 (ν₀.pat k)).symm
      | 1, _ =>
        simp only [etaData, hrv, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.elim_some, sqEquiv_apply]
        exact conjNodeL_sideDigit ν₁ hrec k
      | (m+2), h => exact absurd h (by omega)
    · funext k
      match hrv : (r : ℕ), hr2 with
      | 0, _ =>
        simp only [etaData, hrv, List.getElem?_cons_zero, Option.elim_some, sqEquiv_apply]
        exact (hK0 (ν₀.ψ.coeff k)).symm
      | 1, _ =>
        simp only [etaData, hrv, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.elim_some, sqEquiv_apply]
        exact conjNodeL_ψcoeff ν₁ hrec k
      | (m+2), h => exact absurd h (by omega)
  -- the η-data nevertheless differ (at read 1, ψ-coefficient 0 = −center)
  have hcoeff0 : ((ν₁.ψ.coeff 0 : ↥ν₁.σ.K) : F4) = ((ν₁.center : ↥ν₁.σ.K) : F4) := by
    rw [(ν₁.hspecRecCenter hrec).1]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub]
    have hneg : ((-(ν₁.center) : ↥ν₁.σ.K) : F4) = -((ν₁.center : ↥ν₁.σ.K) : F4) := by
      push_cast; ring
    rw [hneg]
    exact CharTwo.neg_eq _
  have hdiff : etaData (P : ShapePrefix) (⟨[ν₀, ν₁], hne, hri⟩ : History 2 F4)
      ≠ etaData (P : ShapePrefix)
        (⟨[ν₀, conjNodeL ν₁ hrec], hne', hroot'⟩ : History 2 F4) := by
    intro heq
    have h1lt : 1 < (P : ShapePrefix).reads.length := by omega
    have h0lt : 0 < ((P : ShapePrefix).reads.get ⟨1, h1lt⟩).g + 1 := by omega
    have hv : ((ν₁.ψ.coeff 0 : ↥ν₁.σ.K) : F4)
        = (((conjNodeL ν₁ hrec).ψ.coeff 0 : ↥(conjNodeL ν₁ hrec).σ.K) : F4) := by
      have := congrArg (fun d => (d ⟨1, h1lt⟩).2 ⟨0, h0lt⟩) heq
      simpa [etaData] using this
    rw [conjNodeL_ψcoeff ν₁ hrec 0, hcoeff0] at hv
    exact hmove hv.symm
  exact hdiff
    (hU18 _ _ ⟨hMatch, hCoh, hReal, hBox, hCanon, hZbar⟩ hH'mem hAdjH hAdjH' hGal)

-- axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms presentNorm_unique_K3_refuted_by_witness

end LeanUrat.MovesJ
