/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG7
import Uniformity.ChapC.C33Cite
import Uniformity.ChapC.C133mh4

/-!
# Uniformity.ChapI.IFCG8 — the dissection-skeleton bridge (GC0's doorstep)

**Uniform-a0 campaign, the pre-GC bridge unit** flagged by `runs/wave-c/verdict_A0G7.md`'s
GC-readiness assessment: "a useful pre-GC bridge unit is now nearly mechanical: compose the
C.33 dissection (per-slope factors) with per-slope `schema_split` and the stage field's UFD
factorization of `dvResPoly` … to get a whole-skeleton existence theorem 'every context
realizes SOME valid skeleton' — i.e. `RealizesSkeletonAt` inhabited."  **LANDED.**

## What's here

* **§1** `exists_sorted_list_of_finset` — pure `ℕ` combinatorics: any `Finset (ℕ × ℕ)` of
  IFCG5-slope-distinct pairs lists into strictly increasing cross-multiplied order.
* **§2** `exists_ers_of_monic` — every monic polynomial over a field groups into
  `IFCG6.schema_split`'s `ers` shape via mathlib's `UniqueFactorizationMonoid.normalizedFactors`
  (the "UFD residual factorization" leg; no new axiom, existence only).
* **§3** `exists_face_of_dissection_slope` — one C.33 dissection slope `(u, ℓ) ∈ D.slopes`
  yields an `IFCG5.FaceShape (ℓ, σ)` with `ValidFace`, `RealizesFaceAt F (D.factor p) u (ℓ, σ)`,
  and the exact degree identity `D'·faceLen(ℓ, σ) = deg(D.factor p)` §4 sums. Lean-core (no
  cite: it never invokes `exists_dvDissection`, only consumes an already-given dissection).
* **§4** `exists_realizesSkeletonAt_of_dissection` — **THE BRIDGE**: for a monic `f` with
  `D' ∣ deg f` whose C.33 dissection has a trivial below-floor remainder, `RealizesSkeletonAt`
  is inhabited at mass `m = deg f / D'`. Sorts the dissection's slopes (§1), certifies each
  slope's face (§3), and recovers IFCG5's D5 exact mass law by summing §3's degree identity
  against `Polynomial.natDegree_prod_of_monic` on the dissection's own `f = below · ∏ factor`
  law. Footprint: Lean core + the allowlisted C.33 dissection cite `exists_dvDissection`
  (verified below — the ONLY declaration in this file that carries it).

## The honest scope boundary — `hbelow1`

`exists_dvDissection` alone does **not** pin `D.below`: `DvDissection.below` is the remainder
below the frame floor, and nothing in C.33's existence axiom forces it to be trivial for a
general monic `f`. §4's bridge therefore takes `hbelow1 : ∀ D : DvDissection F f, D.below = 1`
as an explicit hypothesis — the exact missing leg flagged by the unit charge. Discharging it
(from the coefficient-box side: recentred size-`m` clusters have all `m` roots of positive
valuation, so their dissection's below-floor part IS trivial) is **GC1's opening work** — the
recentring walk from a raw coefficient vector to its pure stages that this bridge explicitly
does not attempt (per the A0G7 verdict: "What that bridge still would NOT give is GC1's real
content"). A partial bridge — §1–§3, and §4 conditional on `hbelow1` — is what's landed.

## Status

Sorry-free. AxCheck footer: §1–§3 Lean core only; §4's `exists_realizesSkeletonAt_of_dissection`
Lean core + `Uniformity.Density.Tower.exists_dvDissection` and NOTHING else.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG8

open Uniformity (FactorizationType)
open Uniformity.Density.IFCG5 Uniformity.Density.IFCG6 Uniformity.Density.IFCG7

/-! ## §1 — Sorting a `Finset (ℕ × ℕ)` of distinct slopes into increasing cross-multiplied
order.  Pure `ℕ` combinatorics: no frame, no engine. -/

/-- Strong-induction core: every finite set of pairs with positive second coordinate and
pairwise-distinct cross ratio (`hdist`, IFCG5-slope-distinctness) can be listed in strictly
increasing cross-multiplied order.  Induction on cardinality, peeling the ℚ-minimal element via
`Finset.exists_min_image`. -/
theorem exists_sorted_list_of_finset :
    ∀ (s : Finset (ℕ × ℕ)), (∀ p ∈ s, 0 < p.2) →
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.1 * q.2 ≠ q.1 * p.2) →
    ∃ l : List (ℕ × ℕ), l.toFinset = s ∧ l.Nodup ∧
      ∀ i : ℕ, ∀ h : i + 1 < l.length,
        (l.get ⟨i, Nat.lt_of_succ_lt h⟩).1 * (l.get ⟨i + 1, h⟩).2
          < (l.get ⟨i + 1, h⟩).1 * (l.get ⟨i, Nat.lt_of_succ_lt h⟩).2 := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hpos hdist
    rcases s.eq_empty_or_nonempty with hs | hs
    · exact ⟨[], by simp [hs], by simp, by simp⟩
    · obtain ⟨p₀, hp₀mem, hp₀min⟩ :=
        Finset.exists_min_image s (fun p => (p.1 : ℚ) / (p.2 : ℚ)) hs
      have hp₀pos : 0 < p₀.2 := hpos p₀ hp₀mem
      have hssub : s.erase p₀ ⊂ s := Finset.erase_ssubset hp₀mem
      obtain ⟨l', hl'fin, hl'nodup, hl'chain⟩ := ih (s.erase p₀) hssub
        (fun p hp => hpos p (Finset.mem_of_mem_erase hp))
        (fun p hp q hq => hdist p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq))
      refine ⟨p₀ :: l', ?_, ?_, ?_⟩
      · simp [List.toFinset_cons, hl'fin, Finset.insert_erase hp₀mem]
      · rw [List.nodup_cons]
        refine ⟨?_, hl'nodup⟩
        intro hmem
        have : p₀ ∈ s.erase p₀ := by rw [← hl'fin]; simpa using hmem
        exact (Finset.mem_erase.mp this).1 rfl
      · intro i h
        match i, h with
        | 0, h =>
          have hlen : 0 < l'.length := by
            have : 1 < (p₀ :: l').length := h
            simpa using this
          have hhead : l'.get ⟨0, hlen⟩ ∈ l' := List.get_mem l' ⟨0, hlen⟩
          have hheadmem : l'.get ⟨0, hlen⟩ ∈ s.erase p₀ := by
            rw [← hl'fin]; exact List.mem_toFinset.mpr hhead
          have hheadmem' : l'.get ⟨0, hlen⟩ ∈ s := Finset.mem_of_mem_erase hheadmem
          have hne : l'.get ⟨0, hlen⟩ ≠ p₀ := (Finset.mem_erase.mp hheadmem).1
          have hle : (p₀.1 : ℚ) / p₀.2 ≤ (l'.get ⟨0, hlen⟩).1 / (l'.get ⟨0, hlen⟩).2 :=
            hp₀min _ hheadmem'
          have hb2 : 0 < (l'.get ⟨0, hlen⟩).2 := hpos _ hheadmem'
          have hb1n : (p₀.2 : ℚ) ≠ 0 := by exact_mod_cast hp₀pos.ne'
          have hb2n : ((l'.get ⟨0, hlen⟩).2 : ℚ) ≠ 0 := by exact_mod_cast hb2.ne'
          have hqne : (p₀.1 : ℚ) / p₀.2 ≠ (l'.get ⟨0, hlen⟩).1 / (l'.get ⟨0, hlen⟩).2 := by
            intro heq
            apply hdist p₀ hp₀mem (l'.get ⟨0, hlen⟩) hheadmem' (Ne.symm hne)
            rw [div_eq_div_iff hb1n hb2n] at heq
            exact_mod_cast heq
          have hlt : (p₀.1 : ℚ) / p₀.2 < (l'.get ⟨0, hlen⟩).1 / (l'.get ⟨0, hlen⟩).2 :=
            lt_of_le_of_ne hle hqne
          rw [div_lt_div_iff₀ (by exact_mod_cast hp₀pos) (by exact_mod_cast hb2)] at hlt
          have e1 : (p₀ :: l').get ⟨0, Nat.lt_of_succ_lt h⟩ = p₀ := rfl
          have e2 : (p₀ :: l').get ⟨1, h⟩ = l'.get ⟨0, hlen⟩ := rfl
          rw [e1, e2]
          exact_mod_cast hlt
        | Nat.succ k, h =>
          have hk : k + 1 < l'.length := by
            have : k + 1 + 1 < (p₀ :: l').length := h
            simpa using this
          have e1 : (p₀ :: l').get ⟨k + 1, Nat.lt_of_succ_lt h⟩ = l'.get ⟨k, Nat.lt_of_succ_lt hk⟩ :=
            rfl
          have e2 : (p₀ :: l').get ⟨k + 1 + 1, h⟩ = l'.get ⟨k + 1, hk⟩ := rfl
          rw [e1, e2]
          exact hl'chain k hk

/-! ## §2 — The UFD residual factorization: grouping a monic factorization into
`schema_split`'s `ers` shape (mathlib's `normalizedFactors`, no new axiom). -/

open UniqueFactorizationMonoid in
/-- **Every monic, positive-degree polynomial over a field groups into `schema_split`'s `ers`
shape**: pairwise-distinct monic irreducible factors with explicit `(degree, multiplicity)`
labels, whose declared powers reconstruct `G` exactly.  `mathlib`'s `normalizedFactors` supplies
existence (a field's polynomial ring is a UFD; `normalize = id` on monic polynomials), and
`Multiset.count` supplies the grouping. -/
theorem exists_ers_of_monic {k : Type*} [Field k] (G : Polynomial k) (hG : G.Monic)
    (_hGpos : 0 < G.natDegree) :
    ∃ ers : List ((ℕ × ℕ) × Polynomial k),
      (∀ x ∈ ers, x.2.Monic ∧ Irreducible x.2 ∧ x.2.natDegree = x.1.1 ∧
        1 ≤ x.1.1 ∧ 1 ≤ x.1.2) ∧
      ers.Pairwise (fun x y => x.2 ≠ y.2) ∧
      G = (ers.map (fun x => x.2 ^ x.1.2)).prod := by
  classical
  have hG0 : G ≠ 0 := hG.ne_zero
  set factors := normalizedFactors G with hfactors
  set ers : List ((ℕ × ℕ) × Polynomial k) :=
    factors.toFinset.toList.map (fun r => ((r.natDegree, factors.count r), r)) with hers
  refine ⟨ers, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    have hrmem : r ∈ factors.toFinset := Finset.mem_toList.mp hr
    have hrmemf : r ∈ factors := Multiset.mem_toFinset.mp hrmem
    have hriff := (Polynomial.mem_normalizedFactors_iff hG0 (p := r))
    rw [← hfactors] at hriff
    obtain ⟨hirr, hmon, _⟩ := hriff.mp hrmemf
    refine ⟨hmon, hirr, rfl, hirr.natDegree_pos, ?_⟩
    exact Multiset.one_le_count_iff_mem.mpr hrmemf
  · rw [hers, List.pairwise_map]
    exact Finset.nodup_toList _
  · have hlisteq : ers.map (fun x => x.2 ^ x.1.2)
        = factors.toFinset.toList.map (fun r => r ^ factors.count r) := by
      rw [hers, List.map_map]; rfl
    have hprodcount : (ers.map (fun x => x.2 ^ x.1.2)).prod
        = ∏ r ∈ factors.toFinset, r ^ factors.count r := by
      rw [hlisteq, Finset.prod_map_toList]
    rw [hprodcount, ← Finset.prod_multiset_count factors, hfactors,
      UniqueFactorizationMonoid.prod_normalizedFactors_eq hG0, hG.normalize_eq_self]

/-! ## §3 — the per-slope face: combining the C.33 dissection's slope factor with the UFD
grouping (§2) into an `IFCG5.FaceShape` + `ValidFace` + `RealizesFaceAt` certificate. -/

section DvBinding

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {π : O}

/-- Local D9 reconstruction (source: `C133mh14.lean`/`IFCG6.lean`'s private `isKey_X`; byte-
identical mechanism; private there, hence unreachable; neither file edited). -/
private theorem isKey_X' : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by simpa using (Polynomial.irreducible_X (R := IsLocalRing.ResidueField O))

/-- The stage field's `Field` instance (source: `C133mh14.lean`/`IFCG6.lean`'s private
`localFieldStageField`; byte-identical mechanism; private there, hence unreachable). -/
@[reducible] private noncomputable def localFieldStageField' (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : F.Pin H₀) : Field (F.stageField H₀ hpin) :=
  letI : Field (resField (Polynomial.X : Polynomial O)) := instFieldResField isKey_X'
  haveI : Fact (Irreducible (F.frameRes H₀ hpin)) := ⟨(F.hresirr H₀ hpin).1⟩
  AdjoinRoot.instField

/-- Pin existence: the side-min abscissa of a nonempty side has FINITE level height
(re-derived; mechanism byte-identical to `C133mh14.lean`/`IFCG6.lean`'s private `exists_pin`,
off the public `dvOnSide_of_mem_dvSideSet`; private there, hence unreachable; neither file
edited). -/
private theorem exists_pin_of_nonempty (F : KeyFrame O π) {g : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F g u ℓ).Nonempty) :
    ∃ M : ℕ, dvHgt F g (dvSideMin F g u ℓ hne) = (M : ℕ∞) := by
  have hmem : dvSideMin F g u ℓ hne ∈ dvSideSet F g u ℓ := Finset.min'_mem _ hne
  have hon : DvOnSide F g u ℓ (dvSideMin F g u ℓ hne) := dvOnSide_of_mem_dvSideSet hmem
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.mp hon.2
  exact ⟨M, hM.symm⟩

private theorem list_prod_monic'' {R : Type*} [CommSemiring R] :
    ∀ {l : List (Polynomial R)}, (∀ p ∈ l, p.Monic) → l.prod.Monic := by
  intro l
  induction l with
  | nil => intro _; exact Polynomial.monic_one
  | cons a t ih =>
      intro h
      rw [List.prod_cons]
      exact (h a List.mem_cons_self).mul (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- The list-`prod` analogue of `Polynomial.natDegree_multiset_prod_of_monic`, needed since
`exists_ers_of_monic`'s conclusion is `List.prod`-shaped. -/
private theorem list_prod_natDegree_sum {R : Type*} [CommSemiring R] :
    ∀ {l : List (Polynomial R)}, (∀ p ∈ l, p.Monic) →
      l.prod.natDegree = (l.map Polynomial.natDegree).sum := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have ha := h a List.mem_cons_self
      have ht : ∀ p ∈ t, p.Monic := fun p hp => h p (List.mem_cons_of_mem _ hp)
      rw [List.prod_cons, List.map_cons, List.sum_cons, ha.natDegree_mul (list_prod_monic'' ht),
        ih ht]

set_option maxHeartbeats 1600000 in
/-- **The per-slope face** (§3's core): a C.33 dissection slope `p = (u, ℓ) ∈ D.slopes` yields
an `IFCG5.FaceShape` `(ℓ, σ)` — `σ` the UFD-grouped factorization pattern of the slope factor's
level residual — with `ValidFace (ℓ, σ)`, `RealizesFaceAt F (D.factor p) u (ℓ, σ)`, and (the
mass bookkeeping §4 needs) the exact degree identity `D'·faceLen(ℓ,σ) = deg(D.factor p)`. -/
theorem exists_face_of_dissection_slope
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {f : Polynomial O} (D : DvDissection F f) {p : ℕ × ℕ} (hp : p ∈ D.slopes) :
    ∃ σ : FactorizationType, ValidFace (p.2, σ) ∧
      RealizesFaceAt F (D.factor p) p.1 (p.2, σ) ∧
      (F.e₁ * F.f₁) * (p.2 * σ.degree) = (D.factor p).natDegree := by
  classical
  letI : Field (F.stageField H₀ hpin) := localFieldStageField' F H₀ hpin
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
  obtain ⟨M₀, hpinM⟩ := exists_pin_of_nonempty F hne_own
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
      rw [hReq, list_prod_natDegree_sum
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
  refine ⟨σ, ⟨hℓ, ?_, ?_⟩, ?_, ?_⟩
  · exact hσdeg_pos
  · intro q hq
    have hqmem : q ∈ (↑(ers.map Prod.fst) : Multiset (ℕ × ℕ)) := hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.mp hqmem)
    exact ⟨(hval x hx).2.2.2.1, (hval x hx).2.2.2.2⟩
  · have hu : 1 ≤ p.1 := by have := hslopes.2.2; omega
    refine realizesFaceAt_of_pure hu hcop hpureD ?_
    rw [hσdeg_eq]; exact hdivf
  · rw [hσdeg_eq, hgdeg]

/-! ## §4 — assembly: `RealizesSkeletonAt` is inhabited (THE BRIDGE)

Sort the C.33 dissection's slopes (§1), certify each slope's face (§3), and sum the exact
degree identity §3 hands back to recover IFCG5's D5 mass law — **conditional on the
dissection's below-floor remainder being trivial**, since `exists_dvDissection` alone does not
pin `D.below`.  This is the honest scope boundary: discharging `hbelow1` from the coefficient-
box side is GC1's opening work (per the A0G7 verdict's GC-readiness note). -/

/-- Scalar multiplication distributes over a `List.sum`. -/
private theorem list_mul_sum {c : ℕ} : ∀ (l : List ℕ), c * l.sum = (l.map (c * ·)).sum
  | [] => by simp
  | a :: t => by rw [List.sum_cons, List.map_cons, List.sum_cons, Nat.mul_add, list_mul_sum t]

set_option maxHeartbeats 4000000 in
/-- **THE BRIDGE (GC0's doorstep).** For a monic `f` with `D' ∣ deg f` whose C.33 dissection
has trivial below-floor remainder, `RealizesSkeletonAt` is inhabited at mass `m = deg f / D'`:
every such `f` realizes SOME valid skeleton from IFCG5's finite `clusterSkeletonFinset`.
Footprint: Lean core + the allowlisted C.33 dissection cite `exists_dvDissection`. -/
theorem exists_realizesSkeletonAt_of_dissection
    (hπ : Irreducible π) {F : KeyFrame O π} (hh : 0 < F.h) (H₀ : ℕ) (hpin : F.Pin H₀)
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f)
    (hbelow1 : ∀ D : DvDissection F f, D.below = 1)
    {m : ℕ} (hm : f.natDegree = (F.e₁ * F.f₁) * m) :
    ∃ (S : ClusterSkeleton m) (num : Fin S.1.length → ℕ)
      (blocks : Fin S.1.length → Polynomial O),
      RealizesSkeletonAt F S num blocks := by
  classical
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  obtain ⟨D⟩ := exists_dvDissection F hπ hf hkey
  obtain ⟨l, hlfin, hlnodup, hlchain⟩ :=
    exists_sorted_list_of_finset D.slopes (fun p hp => (D.hslopes p hp).1)
      (fun p hp q hq hne => D.hdistinct p hp q hq hne)
  have hmem_l : ∀ i : Fin l.length, l.get i ∈ D.slopes := fun i => by
    rw [← hlfin]; exact List.mem_toFinset.mpr (List.get_mem l i)
  choose σface hVal hReal hDegEq using
    (fun i : Fin l.length => exists_face_of_dissection_slope hπ hh H₀ hpin D (hmem_l i))
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
  -- mass, via the below-trivial hypothesis + §3's exact degree identity summed over `D.slopes`
  have hprodmon : (∏ p ∈ D.slopes, D.factor p).Monic :=
    Polynomial.monic_prod_of_monic D.slopes D.factor (fun p hp => D.hmonic p hp)
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
      rw [list_mul_sum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro i _
      exact hDegEq i
    have hkey : (F.e₁ * F.f₁) * (S1.map faceLen).sum = f.natDegree := by
      rw [hsum1, hsum2, hsum3, ← hfdeg2]
    rw [hm] at hkey
    exact Nat.eq_of_mul_eq_mul_left hDpos hkey
  refine ⟨ClusterSkeleton.ofValid (m := m) (s := S1) ⟨hS1val, hmass⟩,
    fun j => (l.get (Fin.cast List.length_ofFn j)).1,
    fun j => D.factor (l.get (Fin.cast List.length_ofFn j)), ?_, ?_⟩
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
  · -- `RealizesFaceAt` per index
    intro j
    show RealizesFaceAt F (D.factor (l.get (Fin.cast List.length_ofFn j)))
      (l.get (Fin.cast List.length_ofFn j)).1 (S1.get j)
    rw [hS1get j]
    exact hReal (Fin.cast List.length_ofFn j)

end DvBinding

end Uniformity.Density.IFCG8

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` on the §1/§2
combinatorics and §3's per-slope face, and Lean core + the allowlisted C.33 dissection cite
`Uniformity.Density.Tower.exists_dvDissection` on §4's bridge (the only declaration that invokes
`exists_dvDissection`). -/

#print axioms Uniformity.Density.IFCG8.exists_sorted_list_of_finset
#print axioms Uniformity.Density.IFCG8.exists_ers_of_monic
#print axioms Uniformity.Density.IFCG8.exists_face_of_dissection_slope
#print axioms Uniformity.Density.IFCG8.exists_realizesSkeletonAt_of_dissection
