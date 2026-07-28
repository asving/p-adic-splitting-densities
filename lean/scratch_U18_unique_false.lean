/- SCRATCH (escalation prover, U18, 2026-07-28): CONDITIONAL REFUTATION of
`presentNorm_unique` AS STATED (and hence of `OmUniqHyp` as typed).

THE SEMANTIC GAP (the exact obstruction, sharpened from the first prover's G2):
`PrefSet` histories carry NO polynomial f, and a RECENTERING read records its center as
FREE data in ↥σ.K: for a LAST node ν₁ with ν₁.species = recentering,
  * coherence binds ν₁ only through σ₁ = ν₁.σ and numeric fields (there is no i+1 clause);
  * realizability's (HV) clause is vacuous at a NON-ADJACENT read (s0+wSide < μ₀);
  * canonicity's `canonRoot` pin is TRIVIAL at a recentering: ψ = X − C center has a
    SINGLETON root set, so `canonRoot ν₁ = center` for EVERY center — the least-root
    normalization has no normalizing power at recenterings.
Hence conjugating ONLY the last node's own data (ψ, pat, Ranch, zbar, center) by the
squaring automorphism (Frobenius of F4) produces a SECOND PrefSet member H' with
EtaGalEq (etaData H) (etaData H') but etaData H ≠ etaData H' whenever the center is
moved (center ∉ 𝔽₂). This file machine-checks that whole step: ANY witness
(H = [ν₀, ν₁] ∈ PrefSet, read-0 residue field squaring-fixed, ν₁ a non-adjacent
recentering with (center:F4)² ≠ center) refutes the U18 statement.

WHAT REMAINS UNFORMALIZED (the recorded gap; mathematically true, note-supported):
the INSTANCE — a 2-node witness needs the order-1 stage σ₁ over the inert-type key
(e.g. bStage-parent, root read (e,h)=(1,3), g=2, ψ₀=z²+z+1, Φ₁=X²+8X+64, MacLane-legal
since h'=3 > e'·w₀(Φ₁)=2) plus `TransitionCoreL bStage σ₁ Φ₁ 1 3 zbar₀` — the standard
Montes order-1 stage, i.e. HC-1 S9 territory. Its Lean construction is a dedicated unit.

NOT part of the corpus; keep as the standing machine record of the U18 adjudication. -/
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

/-- `canonRoot` of a node with linear ψ = X − C c is the center image — the least-root
normalization is enumeration-free (hence trivial) at recenterings. -/
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

/-- The Frobenius-conjugate of a recentering node (lift field NOT yet re-normalized):
same frame σ, same numeric data; ψ, pat, Ranch, zbar, center conjugated. -/
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

/-! ### The refutation -/

/-- **U18 REFUTED BY ANY SUCH WITNESS**: a 2-node PrefSet member whose root read's residue
field is squaring-fixed elementwise and whose last node is a NON-ADJACENT recentering with
a Frobenius-moved center refutes `presentNorm_unique` as stated (p = 2, F = F4). -/
theorem presentNorm_unique_refuted_by_witness
    {n : ℕ} {P : Shape n} (H : History 2 F4) (ν₀ ν₁ : Node 2 F4)
    (hnodes : H.nodes = [ν₀, ν₁])
    (hH : H ∈ PrefSet n (polOM 2 F4) P)
    (hK0 : ∀ x : ↥ν₀.σ.K, ((x : ↥ν₀.σ.K) : F4) ^ 2 = ((x : ↥ν₀.σ.K) : F4))
    (hrec : ν₁.species = ReadSpecies.recentering)
    (hnonadj : ν₁.s0 + ν₁.wSide < ν₀.μ)
    (hmove : ((ν₁.center : ↥ν₁.σ.K) : F4) ^ 2 ≠ ((ν₁.center : ↥ν₁.σ.K) : F4)) :
    ¬ (∀ H1 H2 : History 2 F4,
        H1 ∈ PrefSet n (polOM 2 F4) P → H2 ∈ PrefSet n (polOM 2 F4) P →
        EtaGalEq (etaData (P : ShapePrefix) H1) (etaData (P : ShapePrefix) H2) →
        etaData (P : ShapePrefix) H1 = etaData (P : ShapePrefix) H2) := by
  intro hU18
  classical
  obtain ⟨nodes, hne0, hri0⟩ := H
  have hnodes' : nodes = [ν₀, ν₁] := hnodes
  subst hnodes'
  have hne := hne0
  have hri := hri0
  -- unpack the membership
  obtain ⟨hMatch, hCoh, hReal, hBox, hCanon, hZbar⟩ := hH
  -- the conjugated history
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
    · -- Realizable
      intro i hi
      match i with
      | 0 =>
        obtain ⟨r1, r2, r3, r4⟩ := hReal 0 (by simp)
        exact ⟨r1, fun hadj => absurd hadj hnonadj.ne, r3,
          fun hadj => absurd hadj hnonadj.ne⟩
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
  -- lengths
  have hPlen : (P : ShapePrefix).reads.length = 2 := by
    obtain ⟨hlen, -⟩ := hMatch
    simpa using hlen.symm
  -- the Galois relation between the two η-data
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
  exact hdiff (hU18 _ _ ⟨hMatch, hCoh, hReal, hBox, hCanon, hZbar⟩ hH'mem hGal)

/-- **The recorded fallback `OmUniqHyp` is FALSE as typed** at any witness-admitting
`(n, P)`: consumers carrying it at such shapes carry an unsatisfiable hypothesis. -/
theorem omUniqHyp_refuted_by_witness
    {n : ℕ} {P : Shape n} (H : History 2 F4) (ν₀ ν₁ : Node 2 F4)
    (hnodes : H.nodes = [ν₀, ν₁])
    (hH : H ∈ PrefSet n (polOM 2 F4) P)
    (hK0 : ∀ x : ↥ν₀.σ.K, ((x : ↥ν₀.σ.K) : F4) ^ 2 = ((x : ↥ν₀.σ.K) : F4))
    (hrec : ν₁.species = ReadSpecies.recentering)
    (hnonadj : ν₁.s0 + ν₁.wSide < ν₀.μ)
    (hmove : ((ν₁.center : ↥ν₁.σ.K) : F4) ^ 2 ≠ ((ν₁.center : ↥ν₁.σ.K) : F4))
    (huniq : OmUniqHyp n (polOM 2 F4) P) : False :=
  presentNorm_unique_refuted_by_witness H ν₀ ν₁ hnodes hH hK0 hrec hnonadj hmove huniq

-- axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms presentNorm_unique_refuted_by_witness
#print axioms omUniqHyp_refuted_by_witness

end LeanUrat.MovesJ
