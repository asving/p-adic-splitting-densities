/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG9

/-!
# Uniformity.ChapI.IFCG10 — [GCF 2026-08-29] the strong bridge and disjointness on the strong
carrier (genre-cover repair legs (a) and (c))

**Uniform-a0 campaign, UNIT GCF**, the successor demanded by `runs/wave-c/verdict_GC.md` §GC2:
IFCG9 proved the weak realization surface formally insufficient for DISJOINT
(`realizes_repeatedLinear_iff_simpleQuadratic`) and defined the exact repaired carrier
`StrongRealizesFaceAt`; IFCG8's bridge built the UFD residual factorization internally and then
DISCARDED it.  This file closes both repair legs:

* **§1 UFD pattern read-off (the new mathematics of leg (c)).**  Over a field, two lists of
  pairwise-distinct monic irreducibles with positive multiplicity labels and EQUAL power
  products carry the SAME `(degree, multiplicity)` label multiset —
  `residualPattern_eq_of_prod_eq`.  Mechanism: `normalizedFactors` of the common product equals
  the expanded multiset (`normalizedFactors_ers_prod`), and the label multiset is a canonical
  function of that expansion (`labels_eq_canon`).  Mathlib's `normalizedFactors_mul/pow/
  irreducible` + `Monic.normalize_eq_self`; no new axiom.
* **§2 pin invariance + the strong carrier's uniqueness (leg (c)).**
  `dvResPoly_pin_congr` — C.25's residual polynomial does not depend on which side-nonemptiness
  / pin certificate is supplied (proof irrelevance + `ℕ∞`-cast injectivity).
  `strongRealizesFaceAt_unique` ★ — one block strong-realizes at most ONE face at ONE
  numerator: IFCG7's `realizesFaceAt_param_unique` pins `(u, b)`, pin invariance aligns the two
  witnesses' residual polynomials, §1 pins the pattern.
  `strongRealizes_skeleton_unique` ★ — the whole-skeleton form: two strong realizations by the
  SAME blocks have equal mass, equal skeleton LISTS, and equal numerators (via
  `mass_eq_of_realizes_same_blocks` + per-face uniqueness + `List.ext_get`).
  `strong_repeatedLinear_simpleQuadratic_discriminated` ★ — **the GC countermodel is
  DISTINGUISHED**: no block strong-realizes both `{(1,2)}` and `{(2,1)}` (at any numerators) —
  exactly the discrimination the weak carrier provably lacks.
* **§3 THE STRONG BRIDGE (leg (a)).**  `exists_strongFace_of_dissection_slope` re-plumbs
  IFCG8 §3 KEEPING the `exists_ers_of_monic` factorization: the produced face comes with its
  `ResidualPatternWitnessAt`.  `exists_strongRealizesSkeletonAt_of_dissection` ★ re-plumbs
  IFCG8 §4 on top of it: every monic `f` with trivial below-floor remainder strong-realizes a
  member of the finite bank.  `exists_strongRealizesSkeletonAt_of_degreeExhausted` is the
  IFCG9-§3 interface (hypothesis `DissectionDegreeExhausted`, not `hbelow1`).
* **§4 the assembled cover, conditional on ONLY the exhaustion kernel.**
  `StrongCoverExhaustive` / `StrongCoverDisjoint` state the cover clauses over the strong
  carrier; `strongCoverDisjoint_all` is UNCONDITIONAL, and
  `finiteGenreCoverAt_strong_of_kernel` ★ derives EXHAUSTIVE ∧ DISJOINT ∧ DECREASING from the
  single carried hypothesis `RecentredClusterDegreeExhaustionStatement` — the campaign's last
  GC piece is exactly that kernel.

## Private plumbing (credited)

`isKey_X₂` / `localFieldStageField₂` re-derive `C133mh14.lean`/`IFCG6.lean`/`IFCG8.lean`'s
private stage-field plumbing (byte-identical mechanism; private there, hence unreachable;
none of those files edited); `exists_pin₂`, `list_prod_monic₂`, `list_prod_natDegree_sum₂`,
`list_mul_sum₂` likewise re-derive IFCG8's private list plumbing.

## Status

Sorry-free.  AxCheck footer: §1/§2 Lean core only (`propext`, `Classical.choice`,
`Quot.sound`); §3's per-slope theorem Lean core (it consumes an already-given dissection);
§3's two bridges and §4's exhaustive/package theorems Lean core + the allowlisted C.33
dissection cite `Uniformity.Density.Tower.exists_dvDissection`, and NOTHING else.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG10

open Uniformity (FactorizationType)
open Uniformity.Density.IFCG5 Uniformity.Density.IFCG6 Uniformity.Density.IFCG7
open Uniformity.Density.IFCG8 Uniformity.Density.IFCG9

/-! ## §1 — UFD pattern read-off over a field (leg (c)'s new mathematics)

Two `schema_split`-shaped factorizations of the SAME polynomial carry the same
`(degree, multiplicity)` label multiset.  Everything is stated over an abstract field `k`;
the stage field enters only in §2. -/

section PatternUnique

open UniqueFactorizationMonoid

variable {k : Type*} [Field k] [DecidableEq k] [DecidableEq (Polynomial k)]

/-- The expansion of an `ers` list into the multiset of its irreducibles WITH multiplicity:
`(D, μ, r)`-entries contribute `μ` copies of `r`. -/
private def ersExpand (l : List ((ℕ × ℕ) × Polynomial k)) : Multiset (Polynomial k) :=
  (l.map (fun x => Multiset.replicate x.1.2 x.2)).sum

@[simp] private theorem ersExpand_nil :
    ersExpand ([] : List ((ℕ × ℕ) × Polynomial k)) = 0 := rfl

@[simp] private theorem ersExpand_cons (x : (ℕ × ℕ) × Polynomial k)
    (t : List ((ℕ × ℕ) × Polynomial k)) :
    ersExpand (x :: t) = Multiset.replicate x.1.2 x.2 + ersExpand t := by
  unfold ersExpand
  rw [List.map_cons, List.sum_cons]

/-- Every member of the expansion is some entry's irreducible. -/
private theorem mem_snd_of_mem_ersExpand {l : List ((ℕ × ℕ) × Polynomial k)}
    {r : Polynomial k} (h : r ∈ ersExpand l) : ∃ x ∈ l, r = x.2 := by
  induction l with
  | nil => simp at h
  | cons x t ih =>
      rw [ersExpand_cons, Multiset.mem_add] at h
      rcases h with h | h
      · exact ⟨x, List.mem_cons_self, Multiset.eq_of_mem_replicate h⟩
      · obtain ⟨y, hy, rfl⟩ := ih h
        exact ⟨y, List.mem_cons_of_mem _ hy, rfl⟩

private theorem list_prod_pow_monic {l : List ((ℕ × ℕ) × Polynomial k)}
    (hmon : ∀ x ∈ l, x.2.Monic) :
    ((l.map (fun x : (ℕ × ℕ) × Polynomial k => x.2 ^ x.1.2)).prod).Monic := by
  induction l with
  | nil => simp
  | cons x t ih =>
      rw [List.map_cons, List.prod_cons]
      exact ((hmon x List.mem_cons_self).pow _).mul
        (ih fun y hy => hmon y (List.mem_cons_of_mem _ hy))

/-- **The normalized factors of an `ers` power product are its expansion** — monic
irreducibles are their own normalizations, so mathlib's UFD factorization recovers exactly
the declared multiset. -/
private theorem normalizedFactors_ers_prod {l : List ((ℕ × ℕ) × Polynomial k)}
    (hval : ∀ x ∈ l, x.2.Monic ∧ Irreducible x.2) :
    normalizedFactors ((l.map (fun x : (ℕ × ℕ) × Polynomial k => x.2 ^ x.1.2)).prod)
      = ersExpand l := by
  induction l with
  | nil => simp [UniqueFactorizationMonoid.normalizedFactors_one]
  | cons x t ih =>
      have hxm : x.2.Monic := (hval x List.mem_cons_self).1
      have hxi : Irreducible x.2 := (hval x List.mem_cons_self).2
      have hval' : ∀ y ∈ t, y.2.Monic ∧ Irreducible y.2 :=
        fun y hy => hval y (List.mem_cons_of_mem _ hy)
      have hxne : x.2 ^ x.1.2 ≠ 0 := (hxm.pow _).ne_zero
      have htne : ((t.map (fun x => x.2 ^ x.1.2)).prod) ≠ 0 :=
        (list_prod_pow_monic (fun y hy => (hval' y hy).1)).ne_zero
      rw [List.map_cons, List.prod_cons, normalizedFactors_mul hxne htne, ih hval',
        normalizedFactors_pow, normalizedFactors_irreducible hxi, hxm.normalize_eq_self,
        Multiset.nsmul_singleton, ersExpand_cons]

/-- **The label multiset is a canonical function of the expansion**: for a pairwise-distinct
`ers` list, the `(D, μ)` labels are exactly `(deg r, count r)` over the expansion's support. -/
private theorem labels_eq_canon :
    ∀ {l : List ((ℕ × ℕ) × Polynomial k)},
      (∀ x ∈ l, x.2.natDegree = x.1.1 ∧ 1 ≤ x.1.2) →
      l.Pairwise (fun x y => x.2 ≠ y.2) →
      (↑(l.map Prod.fst) : Multiset (ℕ × ℕ))
        = (ersExpand l).toFinset.val.map
            (fun r => (r.natDegree, (ersExpand l).count r)) := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x t ih =>
      intro hval hdist
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdist
      have hval' : ∀ y ∈ t, y.2.natDegree = y.1.1 ∧ 1 ≤ y.1.2 :=
        fun y hy => hval y (List.mem_cons_of_mem _ hy)
      have hxdeg : x.2.natDegree = x.1.1 := (hval x List.mem_cons_self).1
      have hxμ : 1 ≤ x.1.2 := (hval x List.mem_cons_self).2
      -- the head irreducible does not occur in the tail expansion
      have hxnot : x.2 ∉ ersExpand t := by
        intro hmem
        obtain ⟨y, hy, hyx⟩ := mem_snd_of_mem_ersExpand hmem
        exact hhead y hy hyx
      -- support of the cons expansion
      have htf : (ersExpand (x :: t)).toFinset = insert x.2 (ersExpand t).toFinset := by
        rw [ersExpand_cons, Multiset.toFinset_add, Multiset.toFinset_replicate,
          if_neg (by omega : ¬ x.1.2 = 0), Finset.singleton_union]
      have hxtf : x.2 ∉ (ersExpand t).toFinset :=
        fun h => hxnot (Multiset.mem_toFinset.mp h)
      have hval2 : (insert x.2 (ersExpand t).toFinset).val
          = x.2 ::ₘ (ersExpand t).toFinset.val := by
        rw [Finset.insert_val, Multiset.ndinsert_of_notMem hxtf]
      -- counts: the head counts its own multiplicity, tail counts are untouched
      have hcx : (ersExpand (x :: t)).count x.2 = x.1.2 := by
        rw [ersExpand_cons, Multiset.count_add, Multiset.count_replicate_self,
          Multiset.count_eq_zero_of_notMem hxnot]
        omega
      have hcother : ∀ r ∈ (ersExpand t).toFinset.val,
          (ersExpand (x :: t)).count r = (ersExpand t).count r := by
        intro r hr
        have hrmem : r ∈ ersExpand t := Multiset.mem_toFinset.mp hr
        have hrne : ¬ x.2 = r := fun he => hxnot (he ▸ hrmem)
        rw [ersExpand_cons, Multiset.count_add, Multiset.count_replicate, if_neg hrne]
        omega
      calc (↑((x :: t).map Prod.fst) : Multiset (ℕ × ℕ))
          = x.1 ::ₘ ↑(t.map Prod.fst) := by
            rw [List.map_cons]
            exact (Multiset.cons_coe _ _).symm
        _ = x.1 ::ₘ (ersExpand t).toFinset.val.map
              (fun r => (r.natDegree, (ersExpand t).count r)) := by
            rw [ih hval' htail]
        _ = (ersExpand (x :: t)).toFinset.val.map
              (fun r => (r.natDegree, (ersExpand (x :: t)).count r)) := by
            rw [htf, hval2, Multiset.map_cons, hcx, hxdeg]
            congr 1
            exact Multiset.map_congr rfl (fun r hr => by rw [hcother r hr])

/-- ★ **UFD pattern read-off** (leg (c)'s residual half): two pairwise-distinct
monic-irreducible power factorizations of the SAME polynomial carry the same
`(degree, multiplicity)` label multiset. -/
theorem residualPattern_eq_of_prod_eq {ers ers' : List ((ℕ × ℕ) × Polynomial k)}
    (hval : ∀ x ∈ ers, x.2.Monic ∧ Irreducible x.2 ∧ x.2.natDegree = x.1.1 ∧
      1 ≤ x.1.1 ∧ 1 ≤ x.1.2)
    (hval' : ∀ x ∈ ers', x.2.Monic ∧ Irreducible x.2 ∧ x.2.natDegree = x.1.1 ∧
      1 ≤ x.1.1 ∧ 1 ≤ x.1.2)
    (hdist : ers.Pairwise (fun x y => x.2 ≠ y.2))
    (hdist' : ers'.Pairwise (fun x y => x.2 ≠ y.2))
    (hprod : (ers.map (fun x : (ℕ × ℕ) × Polynomial k => x.2 ^ x.1.2)).prod
      = (ers'.map (fun x : (ℕ × ℕ) × Polynomial k => x.2 ^ x.1.2)).prod) :
    (↑(ers.map Prod.fst) : Multiset (ℕ × ℕ)) = ↑(ers'.map Prod.fst) := by
  have hexp : ersExpand ers = ersExpand ers' := by
    rw [← normalizedFactors_ers_prod (fun x hx => ⟨(hval x hx).1, (hval x hx).2.1⟩),
      ← normalizedFactors_ers_prod (fun x hx => ⟨(hval' x hx).1, (hval' x hx).2.1⟩), hprod]
  rw [labels_eq_canon (fun x hx => ⟨(hval x hx).2.2.1, (hval x hx).2.2.2.2⟩) hdist,
    labels_eq_canon (fun x hx => ⟨(hval' x hx).2.2.1, (hval' x hx).2.2.2.2⟩) hdist', hexp]

end PatternUnique

/-! ## §2 — pin invariance, the strong skeleton carrier, and DISJOINTNESS (leg (c))

No `IsAdicComplete` in this section — matching IFCG9's carrier section: uniqueness is pure
read-off, no Hensel engine. -/

section StrongUnique

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- Local D9 reconstruction (source: `C133mh14.lean`/`IFCG6.lean`/`IFCG8.lean`'s private
`isKey_X`; byte-identical mechanism; private there, hence unreachable; none edited). -/
private theorem isKey_X₂ : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

/-- The stage field's `Field` instance (source: `C133mh14.lean`/`IFCG6.lean`/`IFCG8.lean`'s
private `localFieldStageField`; byte-identical mechanism; private there, hence unreachable). -/
@[reducible] private noncomputable def localFieldStageField₂ (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X₂
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- **Pin invariance of the residual polynomial**: C.25's `dvResPoly` does not depend on
WHICH nonemptiness/pin certificates are supplied — the level `M` is pinned by `ℕ∞`-cast
injectivity and everything else is proof-irrelevant. -/
theorem dvResPoly_pin_congr {F : KeyFrame O π} (H₀ : ℕ) (hpin : F.Pin H₀)
    {g : Polynomial O} {u ℓ : ℕ}
    (hne hne' : (dvSideSet F g u ℓ).Nonempty) {M M' : ℕ}
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M : ℕ∞))
    (hp' : dvHgt F g (dvSideMin F g u ℓ hne') = (M' : ℕ∞)) :
    dvResPoly F H₀ hpin g u ℓ hne M hp = dvResPoly F H₀ hpin g u ℓ hne' M' hp' := by
  have hnee : hne = hne' := rfl
  subst hnee
  have hM : M = M' := by
    have h0 : (M : ℕ∞) = (M' : ℕ∞) := hp.symm.trans hp'
    exact_mod_cast h0
  subst hM
  rfl

/-- **The strong skeleton carrier** (the whole-skeleton form of IFCG9's
`StrongRealizesFaceAt`): slope-ordered numerators and one STRONG face realization per index —
each block carries its residual-factorization witness. -/
def StrongRealizesSkeletonAt (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀) {m : ℕ}
    (S : ClusterSkeleton m) (num : Fin S.1.length → ℕ)
    (blocks : Fin S.1.length → Polynomial O) : Prop :=
  SlopesOrdered S.1 num ∧
    ∀ i, StrongRealizesFaceAt H₀ hpin (blocks i) (num i) (S.1.get i)

/-- A strong skeleton realization is in particular a weak one. -/
theorem strongRealizesSkeletonAt_realizes {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {m : ℕ} {S : ClusterSkeleton m} {num : Fin S.1.length → ℕ}
    {blocks : Fin S.1.length → Polynomial O}
    (h : StrongRealizesSkeletonAt F H₀ hpin S num blocks) :
    RealizesSkeletonAt F S num blocks :=
  ⟨h.1, fun i => (h.2 i).1⟩

/-- ★ **Face-level uniqueness on the strong carrier** (leg (c), per face): one block
strong-realizes at most one numerator AND one face — including the residual PATTERN, the
component the weak carrier provably forgets (IFCG9's falsifier).  IFCG7's
`realizesFaceAt_param_unique` pins `(u, b, len, resdeg)`; pin invariance aligns the two
witnesses' residual polynomials; §1's UFD read-off pins the pattern. -/
theorem strongRealizesFaceAt_unique {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {g : Polynomial O} {u u' : ℕ} {face face' : FaceShape} (hf : ValidFace face)
    (h : StrongRealizesFaceAt H₀ hpin g u face)
    (h' : StrongRealizesFaceAt H₀ hpin g u' face') :
    u = u' ∧ face = face' := by
  obtain ⟨b, σ⟩ := face
  obtain ⟨b', σ'⟩ := face'
  obtain ⟨hw, hne, M, hp, ers, hval, hdist, hdata, hres⟩ := h
  obtain ⟨hw', hne', M', hp', ers', hval', hdist', hdata', hres'⟩ := h'
  obtain ⟨huu, hbb, -, -⟩ := realizesFaceAt_param_unique hf hw hw'
  subst huu
  have hbb' : b = b' := hbb
  subst hbb'
  letI : Field (F.stageField H₀ hpin) := localFieldStageField₂ F H₀ hpin
  haveI : DecidableEq (F.stageField H₀ hpin) := Classical.decEq _
  haveI : DecidableEq (Polynomial (F.stageField H₀ hpin)) := Classical.decEq _
  have hpins : dvResPoly F H₀ hpin g u b hne M hp = dvResPoly F H₀ hpin g u b hne' M' hp' :=
    dvResPoly_pin_congr H₀ hpin hne hne' hp hp'
  have hprod : (ers.map (fun x => x.2 ^ x.1.2)).prod = (ers'.map (fun x => x.2 ^ x.1.2)).prod :=
    hres.symm.trans (hpins.trans hres')
  have hpat := residualPattern_eq_of_prod_eq hval hval' hdist hdist' hprod
  have hσσ : σ = σ' := FactorizationType.ext (hdata.trans (hpat.trans hdata'.symm))
  exact ⟨rfl, by rw [hσσ]⟩

/-- ★ **DISJOINTNESS ON THE STRONG CARRIER** (leg (c), the unit's target): two strong
skeleton realizations by the SAME blocks have equal mass, equal skeleton lists — residual
patterns INCLUDED — and equal numerators.  A monic block family strong-realizes at most one
member of the bank. -/
theorem strongRealizes_skeleton_unique {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    {m m' : ℕ} {S : ClusterSkeleton m} {S' : ClusterSkeleton m'}
    (hlen : S.1.length = S'.1.length)
    {num : Fin S.1.length → ℕ} {blocks : Fin S.1.length → Polynomial O}
    {num' : Fin S'.1.length → ℕ} {blocks' : Fin S'.1.length → Polynomial O}
    (h1 : StrongRealizesSkeletonAt F H₀ hpin S num blocks)
    (h2 : StrongRealizesSkeletonAt F H₀ hpin S' num' blocks')
    (hbk : ∀ i : Fin S.1.length, blocks i = blocks' (Fin.cast hlen i)) :
    m = m' ∧ S.1 = S'.1 ∧ ∀ i : Fin S.1.length, num i = num' (Fin.cast hlen i) := by
  have hm : m = m' :=
    mass_eq_of_realizes_same_blocks hlen (strongRealizesSkeletonAt_realizes h1)
      (strongRealizesSkeletonAt_realizes h2) hbk
  have hface : ∀ i : Fin S.1.length,
      num i = num' (Fin.cast hlen i) ∧ S.1.get i = S'.1.get (Fin.cast hlen i) := by
    intro i
    have hfv : ValidFace (S.1.get i) := S.valid.1 _ (List.get_mem S.1 i)
    have hs1 : StrongRealizesFaceAt H₀ hpin (blocks i) (num i) (S.1.get i) := h1.2 i
    have hs2 : StrongRealizesFaceAt H₀ hpin (blocks i) (num' (Fin.cast hlen i))
        (S'.1.get (Fin.cast hlen i)) := by
      rw [hbk i]
      exact h2.2 (Fin.cast hlen i)
    exact strongRealizesFaceAt_unique hfv hs1 hs2
  refine ⟨hm, ?_, fun i => (hface i).1⟩
  apply List.ext_get hlen
  intro n h1n h2n
  exact (hface ⟨n, h1n⟩).2

/-- The same-mass corollary, at the subtype: the strong realization pins the bank member
itself. -/
theorem strongRealizes_skeleton_unique_same_mass {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} {m : ℕ} {S S' : ClusterSkeleton m}
    (hlen : S.1.length = S'.1.length)
    {num : Fin S.1.length → ℕ} {blocks : Fin S.1.length → Polynomial O}
    {num' : Fin S'.1.length → ℕ} {blocks' : Fin S'.1.length → Polynomial O}
    (h1 : StrongRealizesSkeletonAt F H₀ hpin S num blocks)
    (h2 : StrongRealizesSkeletonAt F H₀ hpin S' num' blocks')
    (hbk : ∀ i : Fin S.1.length, blocks i = blocks' (Fin.cast hlen i)) :
    S = S' ∧ ∀ i : Fin S.1.length, num i = num' (Fin.cast hlen i) :=
  ⟨Subtype.ext (strongRealizes_skeleton_unique hlen h1 h2 hbk).2.1,
    (strongRealizes_skeleton_unique hlen h1 h2 hbk).2.2⟩

/-- ★ **The GC countermodel is DISTINGUISHED on the strong carrier**: IFCG9 proved every
weak realization of `{(1,2)}` (repeated linear) is a weak realization of `{(2,1)}` (simple
quadratic); on the strong carrier NO block realizes both, at ANY numerators. -/
theorem strong_repeatedLinear_simpleQuadratic_discriminated {F : KeyFrame O π} {H₀ : ℕ}
    {hpin : F.Pin H₀} {g : Polynomial O} {u u' : ℕ}
    (h1 : StrongRealizesFaceAt H₀ hpin g u repeatedLinearFace)
    (h2 : StrongRealizesFaceAt H₀ hpin g u' simpleQuadraticFace) : False :=
  repeatedLinearFace_ne_simpleQuadraticFace
    (strongRealizesFaceAt_unique repeatedLinearFace_valid h1 h2).2

end StrongUnique

/-! ## §3 — THE STRONG BRIDGE (leg (a)): IFCG8 re-plumbed to KEEP the factorization -/

section StrongBridge

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {π : O}

/-- Pin existence (re-derived; mechanism byte-identical to `C133mh14.lean`/`IFCG6.lean`/
`IFCG8.lean`'s private `exists_pin`; private there, hence unreachable; none edited). -/
private theorem exists_pin₂ (F : KeyFrame O π) {g : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F g u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F g (dvSideMin F g u ℓ hne) = (M : ℕ∞) := by
  have hmem : dvSideMin F g u ℓ hne ∈ dvSideSet F g u ℓ := Finset.min'_mem _ hne
  have hon : DvOnSide F g u ℓ (dvSideMin F g u ℓ hne) := dvOnSide_of_mem_dvSideSet hmem
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.mp hon.2
  exact ⟨M, hM.symm⟩

private theorem list_prod_monic₂ {R : Type*} [CommSemiring R] :
    ∀ {l : List (Polynomial R)}, (∀ p ∈ l, p.Monic) → l.prod.Monic := by
  intro l
  induction l with
  | nil => intro _; exact Polynomial.monic_one
  | cons a t ih =>
      intro h
      rw [List.prod_cons]
      exact (h a List.mem_cons_self).mul (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- The list-`prod` degree law (source mechanism: IFCG8's private
`list_prod_natDegree_sum`). -/
private theorem list_prod_natDegree_sum₂ {R : Type*} [CommSemiring R] :
    ∀ {l : List (Polynomial R)}, (∀ p ∈ l, p.Monic) →
      l.prod.natDegree = (l.map Polynomial.natDegree).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have ha := h a List.mem_cons_self
      have ht : ∀ p ∈ t, p.Monic := fun p hp => h p (List.mem_cons_of_mem _ hp)
      rw [List.prod_cons, List.map_cons, List.sum_cons,
        ha.natDegree_mul (list_prod_monic₂ ht), ih ht]

set_option maxHeartbeats 1600000 in
/-- **The per-slope face, STRONG form** (leg (a)'s §3): identical to IFCG8's
`exists_face_of_dissection_slope` — same dissection slope, same UFD grouping — but the
`exists_ers_of_monic` factorization is KEPT and returned as the face's
`ResidualPatternWitnessAt` instead of being discarded.  Proof mechanism byte-adapted from
IFCG8 §3 (IFCG8 not edited).  Lean-core: consumes an already-given dissection. -/
theorem exists_strongFace_of_dissection_slope
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {f : Polynomial O} (D : DvDissection F f) {p : ℕ × ℕ} (hp : p ∈ D.slopes) :
    ∃ σ : FactorizationType, ValidFace (p.2, σ) ∧
      StrongRealizesFaceAt H₀ hpin (D.factor p) p.1 (p.2, σ) ∧
      (F.e₁ * F.f₁) * (p.2 * σ.degree) = (D.factor p).natDegree := by
  classical
  letI : Field (F.stageField H₀ hpin) := localFieldStageField₂ F H₀ hpin
  have hslopes := D.hslopes p hp
  have hℓ : 0 < p.2 := hslopes.1
  have hcop : Nat.Coprime p.1 p.2 := hslopes.2.1
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  obtain ⟨hne_f, hdf_pos⟩ := (D.hsides p.1 p.2 hℓ hcop hslopes.2.2).mp hp
  have hgdeg : (D.factor p).natDegree
      = (F.e₁ * F.f₁) * (p.2 * dvSideDeg F f p.1 p.2 hne_f) := D.hdeg p hp hne_f
  have hgpos : 0 < (D.factor p).natDegree := by
    rw [hgdeg]; exact Nat.mul_pos hDpos (Nat.mul_pos hℓ hdf_pos)
  have hfd : (F.e₁ * F.f₁) ∣ (D.factor p).natDegree :=
    ⟨p.2 * dvSideDeg F f p.1 p.2 hne_f, hgdeg⟩
  have hmon : (D.factor p).Monic := D.hmonic p hp
  have hpureD : IsDvPure F (D.factor p) p.1 p.2 := D.hpure p hp
  have hne_own : (dvSideSet F (D.factor p) p.1 p.2).Nonempty :=
    dvSideSet_nonempty F hmon.ne_zero p.1 hℓ
  obtain ⟨M₀, hpinM⟩ := exists_pin₂ F hne_own
  set R : Polynomial (F.stageField H₀ hpin) :=
    dvResPoly F H₀ hpin (D.factor p) p.1 p.2 hne_own M₀ hpinM with hRdef
  have hRmon : R.Monic :=
    C133mh4.dvResPoly_monic_of_isDvPure F hπ hh H₀ hpin hmon hgpos hℓ hcop hpureD hfd hne_own hpinM
  obtain ⟨hRdeg, hRcoeff0⟩ :=
    natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne_own hpinM
  -- own-side residual degree agrees with `f`'s own-side residual degree
  have hdivown : (D.factor p).natDegree / (F.e₁ * F.f₁)
      = p.2 * dvSideDeg F (D.factor p) p.1 p.2 hne_own :=
    natDegree_div_eq_of_isDvPure hℓ hcop hpureD hne_own
  have hdivf : (D.factor p).natDegree / (F.e₁ * F.f₁) = p.2 * dvSideDeg F f p.1 p.2 hne_f := by
    rw [hgdeg]; exact Nat.mul_div_cancel_left _ hDpos
  have hdeq : dvSideDeg F (D.factor p) p.1 p.2 hne_own = dvSideDeg F f p.1 p.2 hne_f := by
    have h1 : p.2 * dvSideDeg F (D.factor p) p.1 p.2 hne_own
        = p.2 * dvSideDeg F f p.1 p.2 hne_f := by rw [← hdivown, hdivf]
    exact Nat.eq_of_mul_eq_mul_left hℓ h1
  have hRpos : 0 < R.natDegree := by
    rw [hRdeg, hdeq]; exact hdf_pos
  obtain ⟨ers, hval, hdist, hReq⟩ := exists_ers_of_monic R hRmon hRpos
  set σ : FactorizationType := ⟨(↑(ers.map Prod.fst) : Multiset (ℕ × ℕ))⟩ with hσdef
  have hσdeg : σ.degree = R.natDegree := by
    have hmonpow : ∀ x ∈ ers, (x.2 ^ x.1.2).Monic := fun x hx => (hval x hx).1.pow _
    have hsum : (ers.map (fun x => (x.2 ^ x.1.2).natDegree)).sum = R.natDegree := by
      rw [hReq, list_prod_natDegree_sum₂
        (l := ers.map (fun x => x.2 ^ x.1.2)) (by
          intro g hg; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg; exact hmonpow x hx),
        List.map_map]
      rfl
    have hσdeg' : σ.degree = (ers.map (fun x => x.1.1 * x.1.2)).sum := by
      show (((↑(ers.map Prod.fst) : Multiset (ℕ × ℕ))).map (fun q => q.1 * q.2)).sum = _
      rw [Multiset.map_coe, Multiset.sum_coe, List.map_map]
      rfl
    rw [hσdeg', ← hsum]
    congr 1
    apply List.map_congr_left
    intro x hx
    obtain ⟨hxm, hxi, hxd, hx1, hx2⟩ := hval x hx
    rw [hxm.natDegree_pow, hxd, Nat.mul_comm]
  have hσdeg_pos : 1 ≤ σ.degree := by rw [hσdeg]; omega
  have hσdeg_eq : σ.degree = dvSideDeg F f p.1 p.2 hne_f := by rw [hσdeg, hRdeg, hdeq]
  have hweak : RealizesFaceAt F (D.factor p) p.1 (p.2, σ) := by
    have hu : 1 ≤ p.1 := by have := hslopes.2.2; omega
    refine realizesFaceAt_of_pure hu hcop hpureD ?_
    rw [hσdeg_eq]; exact hdivf
  have hwitness : ResidualPatternWitnessAt H₀ hpin (D.factor p) p.1 (p.2, σ) := by
    refine ⟨hne_own, M₀, hpinM, ers, hval, hdist, ?_, ?_⟩
    · rw [hσdef]
    · rw [← hRdef]; exact hReq
  refine ⟨σ, ⟨hℓ, hσdeg_pos, ?_⟩, ⟨hweak, hwitness⟩, ?_⟩
  · intro q hq
    have hqmem : q ∈ (↑(ers.map Prod.fst) : Multiset (ℕ × ℕ)) := hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.mp hqmem)
    exact ⟨(hval x hx).2.2.2.1, (hval x hx).2.2.2.2⟩
  · rw [hσdeg_eq, hgdeg]

/-- Scalar multiplication distributes over a `List.sum` (source mechanism: IFCG8's private
`list_mul_sum`). -/
private theorem list_mul_sum₂ {c : ℕ} : ∀ (l : List ℕ), c * l.sum = (l.map (c * ·)).sum
  | [] => by simp
  | a :: t => by rw [List.sum_cons, List.map_cons, List.sum_cons, Nat.mul_add, list_mul_sum₂ t]

set_option maxHeartbeats 4000000 in
/-- ★ **THE STRONG BRIDGE (leg (a))**: for a monic `f` with `D′ ∣ deg f` whose C.33
dissection has trivial below-floor remainder, `StrongRealizesSkeletonAt` is inhabited at mass
`m = deg f / D′` — the bank member comes with per-face residual-factorization witnesses, the
data IFCG8's weak bridge discarded.  Proof mechanism byte-adapted from IFCG8 §4 (IFCG8 not
edited).  Footprint: Lean core + the allowlisted C.33 dissection cite `exists_dvDissection`. -/
theorem exists_strongRealizesSkeletonAt_of_dissection
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f)
    (hbelow1 : ∀ D : DvDissection F f, D.below = 1)
    {m : ℕ} (hm : f.natDegree = (F.e₁ * F.f₁) * m) :
    ∃ (S : ClusterSkeleton m) (num : Fin S.1.length → ℕ)
      (blocks : Fin S.1.length → Polynomial O),
      S ∈ genreSkeletonFinset m ∧ StrongRealizesSkeletonAt F H₀ hpin S num blocks := by
  classical
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  obtain ⟨D⟩ := exists_dvDissection F hπ hf hkey
  obtain ⟨l, hlfin, hlnodup, hlchain⟩ :=
    exists_sorted_list_of_finset D.slopes (fun p hp => (D.hslopes p hp).1)
      (fun p hp q hq hne => D.hdistinct p hp q hq hne)
  have hmem_l : ∀ i : Fin l.length, l.get i ∈ D.slopes := fun i => by
    rw [← hlfin]; exact List.mem_toFinset.mpr (List.get_mem l i)
  choose σface hVal hReal hDegEq using
    (fun i : Fin l.length => exists_strongFace_of_dissection_slope hπ hh H₀ hpin D (hmem_l i))
  set S1 : List FaceShape := List.ofFn (fun i => ((l.get i).2, σface i)) with hS1def
  have hS1get : ∀ i : Fin S1.length,
      S1.get i = ((l.get (Fin.cast (List.length_ofFn) i)).2,
        σface (Fin.cast (List.length_ofFn) i)) :=
    fun i => List.get_ofFn (fun i => ((l.get i).2, σface i)) i
  -- validity
  have hS1val : ∀ face ∈ S1, ValidFace face := by
    intro face hface
    have hface' : face ∈ Set.range (fun i : Fin l.length => ((l.get i).2, σface i)) :=
      List.mem_ofFn' _ _ |>.mp hface
    obtain ⟨i, hi⟩ := hface'
    rw [← hi]
    exact hVal i
  -- mass, via the below-trivial hypothesis + the strong per-slope's exact degree identity
  have hfdeg : f.natDegree = ∑ p ∈ D.slopes, (D.factor p).natDegree := by
    conv_lhs => rw [D.hprod, hbelow1 D, one_mul,
      Polynomial.natDegree_prod_of_monic D.slopes D.factor (fun p hp => D.hmonic p hp)]
  have hval_eq : D.slopes.val = (↑l : Multiset (ℕ × ℕ)) := by
    rw [← hlfin, List.toFinset_val, List.dedup_eq_self.2 hlnodup]
  have hsumconv : ∀ (g : ℕ × ℕ → ℕ), ∑ p ∈ D.slopes, g p = (l.map g).sum := by
    intro g
    rw [Finset.sum_eq_multiset_sum, hval_eq, Multiset.map_coe, Multiset.sum_coe]
  have hfdeg2 : f.natDegree = (l.map (fun p => (D.factor p).natDegree)).sum := by
    rw [hfdeg, hsumconv]
  have hmass : (S1.map faceLen).sum = m := by
    have hsum1 : (S1.map faceLen).sum
        = ((List.finRange l.length).map (fun i => faceLen ((l.get i).2, σface i))).sum := by
      rw [hS1def, List.map_ofFn, List.ofFn_eq_map]
      rfl
    have hsum3 : ((List.finRange l.length).map (fun i => (D.factor (l.get i)).natDegree)).sum
        = (l.map (fun p => (D.factor p).natDegree)).sum := by
      rw [show (fun i : Fin l.length => (D.factor (l.get i)).natDegree)
          = (fun p => (D.factor p).natDegree) ∘ l.get from rfl,
        ← List.ofFn_eq_map, ← List.map_ofFn, List.ofFn_get]
    have hsum2 : (F.e₁ * F.f₁) * ((List.finRange l.length).map
          (fun i => faceLen ((l.get i).2, σface i))).sum
        = ((List.finRange l.length).map (fun i => (D.factor (l.get i)).natDegree)).sum := by
      rw [list_mul_sum₂, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro i _
      exact hDegEq i
    have hkey2 : (F.e₁ * F.f₁) * (S1.map faceLen).sum = f.natDegree := by
      rw [hsum1, hsum2, hsum3, ← hfdeg2]
    rw [hm] at hkey2
    exact Nat.eq_of_mul_eq_mul_left hDpos hkey2
  refine ⟨ClusterSkeleton.ofValid (m := m) (s := S1) ⟨hS1val, hmass⟩,
    fun j => (l.get (Fin.cast List.length_ofFn j)).1,
    fun j => D.factor (l.get (Fin.cast List.length_ofFn j)), Finset.mem_univ _, ?_, ?_⟩
  · -- `SlopesOrdered`
    show SlopesOrdered S1 (fun j => (l.get (Fin.cast List.length_ofFn j)).1)
    have hb : ∀ face ∈ S1, 1 ≤ face.1 := fun face hface => (hS1val face hface).1
    rw [slopesOrdered_iff_chain hb]
    intro i h
    have h' : i + 1 < l.length := by
      have hlen : S1.length = l.length := List.length_ofFn
      omega
    have hchain := hlchain i h'
    show (l.get (Fin.cast List.length_ofFn ⟨i, Nat.lt_of_succ_lt h⟩)).1
        * (S1.get ⟨i + 1, h⟩).1
      < (l.get (Fin.cast List.length_ofFn ⟨i + 1, h⟩)).1
        * (S1.get ⟨i, Nat.lt_of_succ_lt h⟩).1
    rw [hS1get ⟨i, Nat.lt_of_succ_lt h⟩, hS1get ⟨i + 1, h⟩]
    exact hchain
  · -- `StrongRealizesFaceAt` per index — the KEPT witness flows through
    intro j
    show StrongRealizesFaceAt H₀ hpin (D.factor (l.get (Fin.cast List.length_ofFn j)))
      (l.get (Fin.cast List.length_ofFn j)).1 (S1.get j)
    rw [hS1get j]
    exact hReal (Fin.cast List.length_ofFn j)

/-- **The strong bridge at IFCG9's normalization interface**: hypothesis
`DissectionDegreeExhausted` (the honest coefficient-side formulation), conclusion in the
finite bank with the strong carrier.  Footprint: Lean core + the C.33 dissection cite. -/
theorem exists_strongRealizesSkeletonAt_of_degreeExhausted
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f)
    (hnorm : DissectionDegreeExhausted F f)
    {m : ℕ} (hm : f.natDegree = (F.e₁ * F.f₁) * m) :
    ∃ (S : ClusterSkeleton m) (num : Fin S.1.length → ℕ)
      (blocks : Fin S.1.length → Polynomial O),
      S ∈ genreSkeletonFinset m ∧ StrongRealizesSkeletonAt F H₀ hpin S num blocks :=
  exists_strongRealizesSkeletonAt_of_dissection hπ hh H₀ hpin hf hkey
    (fun D => below_eq_one_of_degreeExhausted hnorm D) hm

end StrongBridge

/-! ## §4 — the assembled cover over the strong carrier, conditional on ONLY the kernel

The carried-hypothesis pattern: `RecentredClusterDegreeExhaustionStatement` (IFCG9's exact
missing coefficient-side theorem) is the SOLE remaining input; everything else below is
proved.  The statements quantify over `O : Type` because the kernel does. -/

section AssembledCover

open Polynomial Uniformity.Density Uniformity.Density.Tower

/-- **The EXHAUSTIVE clause over the strong carrier**: every recentred monic above-floor
context strong-realizes a member of the finite bank. -/
def StrongCoverExhaustive : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (π : O), Irreducible π → ∀ (F : KeyFrame O π), 0 < F.h →
    ∀ (H₀ : ℕ) (hpin : F.Pin H₀) (f : Polynomial O),
      f.Monic → ¬ F.key ∣ f → StrictlyRecentredAboveFloor F f →
      ∀ m : ℕ, f.natDegree = (F.e₁ * F.f₁) * m →
        ∃ (S : ClusterSkeleton m) (num : Fin S.1.length → ℕ)
          (blocks : Fin S.1.length → Polynomial O),
          S ∈ genreSkeletonFinset m ∧ StrongRealizesSkeletonAt F H₀ hpin S num blocks

/-- **The DISJOINT clause over the strong carrier**: same blocks, same bank member — mass,
skeleton list (patterns included), and numerators all pinned. -/
def StrongCoverDisjoint : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (F : KeyFrame O π) (H₀ : ℕ) (hpin : F.Pin H₀)
    (m m' : ℕ) (S : ClusterSkeleton m) (S' : ClusterSkeleton m')
    (hlen : S.1.length = S'.1.length)
    (num : Fin S.1.length → ℕ) (blocks : Fin S.1.length → Polynomial O)
    (num' : Fin S'.1.length → ℕ) (blocks' : Fin S'.1.length → Polynomial O),
    StrongRealizesSkeletonAt F H₀ hpin S num blocks →
    StrongRealizesSkeletonAt F H₀ hpin S' num' blocks' →
    (∀ i : Fin S.1.length, blocks i = blocks' (Fin.cast hlen i)) →
    m = m' ∧ S.1 = S'.1 ∧ ∀ i : Fin S.1.length, num i = num' (Fin.cast hlen i)

/-- **DISJOINT holds unconditionally** — leg (c), packaged.  Lean-core. -/
theorem strongCoverDisjoint_all : StrongCoverDisjoint := by
  unfold StrongCoverDisjoint
  intro O _ _ _ π F H₀ hpin m m' S S' hlen num blocks num' blocks' h1 h2 hbk
  exact strongRealizes_skeleton_unique hlen h1 h2 hbk

/-- **EXHAUSTIVE holds given the kernel** — the strong bridge fired through IFCG9's
normalization dictionary.  Footprint: Lean core + the C.33 dissection cite. -/
theorem strongCoverExhaustive_of_kernel
    (hker : RecentredClusterDegreeExhaustionStatement) : StrongCoverExhaustive := by
  unfold StrongCoverExhaustive
  intro O _ _ _ _ π hπ F hh H₀ hpin f hmon hkey hrec m hm
  have hnorm : DissectionDegreeExhausted F f := hker O π hπ F f hmon hkey hrec
  exact exists_strongRealizesSkeletonAt_of_degreeExhausted hπ hh H₀ hpin hmon hkey hnorm hm

/-- ★ **THE ASSEMBLED COVER'S REMAINING SHAPE** (the unit's clause 3, stated — not forced):
conditional on the SINGLE carried hypothesis `RecentredClusterDegreeExhaustionStatement`
(IFCG9's exact missing coefficient-side theorem, the campaign's last GC piece), the finite
genre cover holds over the strong carrier: EXHAUSTIVE ∧ DISJOINT ∧ DECREASING.  DISJOINT and
DECREASING are unconditional; only EXHAUSTIVE consumes the kernel. -/
theorem finiteGenreCoverAt_strong_of_kernel
    (hker : RecentredClusterDegreeExhaustionStatement) :
    StrongCoverExhaustive ∧ StrongCoverDisjoint ∧ ∀ m : ℕ, DecreasingGenreBankAt m :=
  ⟨strongCoverExhaustive_of_kernel hker, strongCoverDisjoint_all, decreasingGenreBankAt_all⟩

end AssembledCover

end Uniformity.Density.IFCG10

end

/-! ## AXCHECK FOOTER

Expect Lean core `{propext, Classical.choice, Quot.sound}` on §1 (UFD read-off), §2 (pin
invariance + uniqueness + the countermodel discrimination), §3's per-slope theorem, and §4's
disjoint clause; Lean core + exactly the allowlisted C.33 dissection cite
`Uniformity.Density.Tower.exists_dvDissection` on the two bridges and the two kernel-fed §4
theorems.  No other axiom anywhere. -/

#print axioms Uniformity.Density.IFCG10.residualPattern_eq_of_prod_eq
#print axioms Uniformity.Density.IFCG10.dvResPoly_pin_congr
#print axioms Uniformity.Density.IFCG10.strongRealizesSkeletonAt_realizes
#print axioms Uniformity.Density.IFCG10.strongRealizesFaceAt_unique
#print axioms Uniformity.Density.IFCG10.strongRealizes_skeleton_unique
#print axioms Uniformity.Density.IFCG10.strongRealizes_skeleton_unique_same_mass
#print axioms Uniformity.Density.IFCG10.strong_repeatedLinear_simpleQuadratic_discriminated
#print axioms Uniformity.Density.IFCG10.exists_strongFace_of_dissection_slope
#print axioms Uniformity.Density.IFCG10.exists_strongRealizesSkeletonAt_of_dissection
#print axioms Uniformity.Density.IFCG10.exists_strongRealizesSkeletonAt_of_degreeExhausted
#print axioms Uniformity.Density.IFCG10.strongCoverDisjoint_all
#print axioms Uniformity.Density.IFCG10.strongCoverExhaustive_of_kernel
#print axioms Uniformity.Density.IFCG10.finiteGenreCoverAt_strong_of_kernel
