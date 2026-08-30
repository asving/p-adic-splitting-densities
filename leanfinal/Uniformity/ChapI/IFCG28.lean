/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG26

/-!
# Uniformity.ChapI.IFCG28 — [WFR 2026-08-30] the pigeonhole decision, the staircase
sector, and the class-stable residual polynomial

Stage WFR of the cone census (design record `runs/wave-c/verdict_WFR.md`).  CRL
(`IFCG26`) closed `ConeRemainderLaw 3` and re-based the census front to the `e ≥ 4`
remainder laws; its design finding — width pins are FREE by pigeonhole when every
visible face carries only its two endpoints — is realized here at FULL strength:

* **§1 ★★ `decidedAt_of_two_point_sides` (THE PIGEONHOLE DECISION)**: a stratum-height
  class carrying pairwise-distinct visible coprime slopes `(uᵢ, ℓᵢ)`, each attained at
  two abscissae, with `Σ ℓᵢ = m`, is DECIDED with type `⟨{(ℓᵢ, 1)}ᵢ⟩`.  B.42's
  dissection gives one pure block per slope with `ℓᵢ ∣ deg` and `deg > 0`; the degree
  total `m` pins every block to width exactly `ℓᵢ` with NO width lemma; IFCG26 §4
  decides each block.  This closes the whole general-position sector (every side of
  residual degree 1) of every `ConeRemainderLaw e σ` at once.
  **★★ `decidedAt_of_two_point_sides_off_one` (THE OFF-ONE PIGEONHOLE)**: the same with
  `Σ ℓᵢ = m − 1` and every `ℓᵢ ≥ 2` — the one leftover degree cannot hide inside a
  fractional block (`ℓᵢ ∣ deg`), so it is a FORCED extra monic linear factor: type
  `⟨{(ℓᵢ, 1)}ᵢ + {(1, 1)}⟩`.  CRL's m = 3 mixed decision (visible corner) is the
  instance `T = {(1, 2)}`; at every `m ≥ 4` this decides the whole
  fractional-sides-plus-one-leftover genre.
* **§2 the staircase sector**: `decidedAt_staircase` — the charge's literal target: a
  strictly convex all-integer-slope class polygon decides TOTALLY SPLIT (the `ℓ ≡ 1`
  instance of §1); `card_exactBox` counts each staircase cell exactly (the CN4
  monomial genre).  ★ THE HONEST SCOPING THEOREM (`mem_deepBox_of_staircase`,
  `staircase_not_shallow`): strict convexity of integer slopes FORCES `vᵢ ≥ m − i` —
  every staircase class is Eisenstein-deep, so the totally-split staircase sector
  belongs to the zero-centre recentring range (the recursion), NOT to the cone
  remainder carrier.  Corollary recorded: every SHALLOW all-two-point class carries at
  least one fractional side.
* **§3 CN1-FOR-RESIDUALS (Lean-core)**: below the frame floor, the side set of EVERY
  lift is the class attainment set (`sideSet_monicPoly_eq`), the side data
  (`sideMin`/`sideMax`/`sideDeg`, the left height `H₀`) are class-pinned, and the side
  residual polynomial is a CLASS INVARIANT (`resPoly_monicPoly_eq`): any two lifts of
  `c` read the same `resPoly` at the x-frame.  Engine: the digit lemma `digAt_congr`
  (digits strictly below the window are level-`K` data) pushed through `dev`/`resMk`,
  plus IFCG26 §1's general-position bridge.  This is exactly the input the wide-face
  (`sideDeg ≥ 2`) refinement consumes: the residual's factorization is class data.

## Axiom fence

§0 helpers, §2 counting/scoping and ALL of §3 are Lean core.  §1 and the §2 decision
theorems consume exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42) — the same single cite as
IFCG26.  The C.33 (r = 1) cites do NOT occur; no ChapC import.

## The honest fence (what stays open after this file)

`ConeRemainderLaw e σ` at `e ≥ 4` now rests on exactly:
1. the CARRIER PARTITION/COUNT: enumerate the shallow stratum classes off the pure
   faces by polygon shape and sum the cells (§1 decides every visible all-two-point
   shape, with or without one leftover degree; `card_exactBox` + IFCG24's box toolkit
   count each cell) — a counting campaign, no new decision engine needed for that
   sector;
2. the INVISIBLE-CORNER cells: both §1 theorems require the corner visible
   (`v₀ < K`, B.42's `dev ≠ 0` gate).  Cells whose steep block hides the corner
   (`v₀ ≥ K`, `a₀ = 0` included) need the class-level X-strip (IFCG26 §2's induction
   lifted from lifts to classes: an invisible-corner class of mass `m` strips to a
   mass-`m − 1` class) — named, mechanism known, not landed;
3. the WIDE-FACE cells (some side of residual degree `sideDeg ≥ 2`): §3 makes the side
   residual class data; the surviving Hensel input is the x-frame block split along a
   coprime factorization of the residual (C133mh's `theoremA` at the KeyFrame — the
   x-frame instance is in neither the corpus nor mathlib; B.63's
   `typeOf_of_separable_residuals` consumes B.42 alone but carries the open perimeter
   (inertia-divisibility) supply at `ψ.natDegree ≥ 2`), plus the recursion of the
   refined blocks to smaller-mass cones.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG28

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le
  classCoeffVal_exact le_classCoeffVal_iff_dvd classCoeffVal_le exists_npAttains)
open Uniformity.Density.IFCG23 (le_npHgt_monicPoly npHgt_monicPoly_eq npHgt_monicPoly_top)
open Uniformity.Density.IFCG24 (npHeight_coe deepBox shallowSet card_pi_set
  card_setOf_resOrd_eq card_setOf_le_resOrd)
open Uniformity.Density.IFCG26 (mem_sideSet_of_onSide onSide_monicPoly_of_npAttains
  dvd_natDegree_of_isPure irreducible_of_isPure_natDegree_eq monicFactors_of_irreducible
  monicPoly_zero' npHgt_X_eq_top)

attribute [local instance] Classical.propDecidable

/-! ## §0 — supply: the linear key, singleton sums, product factorizations -/

section Supply

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- Summing singletons over a `Finset` is mapping over its multiset. -/
private theorem sum_singleton_eq_map {ι α : Type*} (t : Finset ι) (g : ι → α) :
    ∑ i ∈ t, ({g i} : Multiset α) = t.val.map g := by
  induction t using Finset.cons_induction with
  | empty => rfl
  | cons a t hat ih =>
      rw [Finset.sum_cons, ih, Finset.cons_val, Multiset.map_cons,
        ← Multiset.singleton_add]

/-- Mapping over a sum of singletons. -/
private theorem map_sum_singleton {ι α β : Type*} (t : Finset ι) (g : ι → α) (f : α → β) :
    (∑ i ∈ t, ({g i} : Multiset α)).map f = ∑ i ∈ t, ({f (g i)} : Multiset β) := by
  rw [sum_singleton_eq_map, sum_singleton_eq_map, Multiset.map_map]
  rfl

/-- The monic factor multiset of `1` is empty. -/
theorem monicFactors_one : monicFactors (1 : Polynomial O) = 0 :=
  monicFactors_eq ⟨fun p hp => absurd hp (Multiset.notMem_zero p), Multiset.prod_zero⟩

/-- Monic factorizations add over `Finset` products (CN-02 `monicFactors_mul`,
iterated). -/
theorem monicFactors_prod {ι : Type*} (s : Finset ι) (F : ι → Polynomial O)
    (hmon : ∀ p ∈ s, (F p).Monic) :
    monicFactors (∏ p ∈ s, F p) = ∑ p ∈ s, monicFactors (F p) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact monicFactors_one
  | cons a t hat ih =>
      rw [Finset.prod_cons, Finset.sum_cons,
        monicFactors_mul (hmon a (Finset.mem_cons_self a t))
          (Polynomial.monic_prod_of_monic t F
            (fun p hp => hmon p (Finset.mem_cons_of_mem hp))),
        ih (fun p hp => hmon p (Finset.mem_cons_of_mem hp))]

/-- `Finset.min'` transports along an equality of finsets. -/
private theorem min'_congr {α : Type*} [LinearOrder α] {s t : Finset α} (h : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.min' hs = t.min' ht := by
  subst h; rfl

/-- `Finset.max'` transports along an equality of finsets. -/
private theorem max'_congr {α : Type*} [LinearOrder α] {s t : Finset α} (h : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.max' hs = t.max' ht := by
  subst h; rfl

end Supply

/-! ## §1 — ★★ THE PIGEONHOLE DECISION: two-point sides totalling `m` decide the class -/

section Pigeonhole

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- `hu` is kept for signature honesty (the guard against the vacuous slope datum
-- `u = 0`, exactly as IFCG26's `he'`); B.42's own clause 1 re-supplies it for members,
-- so this proof happens not to consume it.
set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- ★★ **THE PIGEONHOLE DECISION** (CRL's design finding at full strength): a class all
of whose visible heights are `≥ 1` (the stratum shape), whose corner is visible
(`v₀ < K`), carrying `r` pairwise-distinct coprime slopes `(uᵢ, ℓᵢ)` — each visible and
attained at two abscissae — with `Σᵢ ℓᵢ = m`, is DECIDED with type `⟨{(ℓᵢ, 1)}ᵢ⟩`.

Mechanism: B.42 dissects every lift into one monic `(u,ℓ)`-pure block per two-point
slope of positive degree with `ℓ ∣ deg` (IFCG26 §4); the degree total `m` then pins
`deg = ℓᵢ` for every block AND excludes any further block — no width lemma, no
simultaneous face bookkeeping.  IFCG26 §4 decides each block irreducible `(ℓᵢ, 1)`. -/
theorem decidedAt_of_two_point_sides {m K r : ℕ} (hm : 0 < m) {c : Coeff O m K}
    {u ℓ : Fin r → ℕ}
    (hu : ∀ i, 0 < u i) (hl : ∀ i, 0 < ℓ i) (hcop : ∀ i, Nat.Coprime (u i) (ℓ i))
    (hdist : ∀ i j, i ≠ j → u i * ℓ j ≠ u j * ℓ i)
    (hsum : ∑ i, ℓ i = m)
    (hstr : ∀ i : Fin m, 1 ≤ classCoeffVal c i)
    (h0vis : classCoeffVal c ⟨0, hm⟩ < K)
    (hface : ∀ i, ∃ j j', j < j' ∧ NPAttains c (u i) (ℓ i) j ∧ NPAttains c (u i) (ℓ i) j')
    (hvis : ∀ i, NPVisibleAt c (u i) (ℓ i)) :
    DecidedAt O m ⟨Finset.univ.val.map (fun i : Fin r => ((ℓ i : ℕ), (1 : ℕ)))⟩ K c := by
  intro a ha
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hK1 : 1 ≤ K := by omega
  -- STEP 1: the stratum reduction `f̄ = X̄^m` (all class heights `≥ 1`).
  have hres : (monicPoly a).map (residue O) = X ^ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree, map_monicPoly]
    have hzero : (fun i => residue O (a i)) = (fun _ : Fin m => (0 : ResidueField O)) := by
      funext i
      have h7 := (le_classCoeffVal_iff_dvd hπ hK1 ha i).1 (hstr i)
      rw [pow_one] at h7
      exact (IsLocalRing.residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hπ _).2 h7)
    rw [hzero, monicPoly_zero']
  -- STEP 2: the corner does not vanish (its exact valuation is visible).
  have ha0 : a ⟨0, hm⟩ ≠ 0 := by
    intro h
    exact (classCoeffVal_exact hπ ha h0vis).2 (h ▸ dvd_zero _)
  have hdev : dev X (monicPoly a) 0 ≠ 0 := by
    rw [dev_X, monicPoly_coeff_lt a hm]
    intro hC
    exact ha0 (by simpa using hC)
  -- STEP 3: B.42 fires — the slope dissection of the lift.
  have hdegpos : 0 < (monicPoly a).natDegree := by rw [monicPoly_natDegree]; exact hm
  obtain ⟨s, F, hs1, hs2, hs3, hprod, hs5, hs6⟩ :=
    exists_slope_factorization (μ := (monicPoly a).natDegree) hπ isKey_X
      (monicPoly_monic a) hdegpos (by rw [Polynomial.map_X]; exact hres) hdev
  -- STEP 4: every input slope is a two-point side of the lift (IFCG26 §1's bridge).
  have hmem : ∀ i : Fin r, (u i, ℓ i) ∈ s := by
    intro i
    obtain ⟨j, j', hjj', hAj, hAj'⟩ := hface i
    obtain ⟨hOj, -⟩ := onSide_monicPoly_of_npAttains hπ (hl i) (hvis i) hAj ha
    obtain ⟨hOj', -⟩ := onSide_monicPoly_of_npAttains hπ (hl i) (hvis i) hAj' ha
    refine (hs5 (u i) (ℓ i) (hl i) (hcop i)).1 ?_
    refine Finset.one_lt_card.mpr
      ⟨j, mem_sideSet_of_onSide ?_ hOj, j', mem_sideSet_of_onSide ?_ hOj', by omega⟩
    · rw [monicPoly_natDegree]; exact hAj.1
    · rw [monicPoly_natDegree]; exact hAj'.1
  -- STEP 5: THE PIGEONHOLE — block degrees `≥ ℓᵢ` totalling `m = Σ ℓᵢ` pin everything.
  have hmon : ∀ p ∈ s, (F p).Monic := fun p hp => (hs3 p hp).1
  have hdegsum : ∑ p ∈ s, (F p).natDegree = m := by
    have h1 := Polynomial.natDegree_prod_of_monic s F hmon
    rw [← hprod, monicPoly_natDegree] at h1
    exact h1.symm
  have hdegge : ∀ p ∈ s, p.2 ≤ (F p).natDegree := by
    intro p hp
    obtain ⟨-, hl', hcop'⟩ := hs1 p hp
    obtain ⟨hFm, hFp, -, -, hFd⟩ := hs3 p hp
    exact Nat.le_of_dvd hFd (dvd_natDegree_of_isPure hπ hFm hl' hcop' hFp)
  have hginj : ∀ x ∈ (Finset.univ : Finset (Fin r)), ∀ y ∈ Finset.univ,
      (fun i : Fin r => (u i, ℓ i)) x = (fun i : Fin r => (u i, ℓ i)) y → x = y := by
    intro x _ y _ hxy
    by_contra hne
    simp only [Prod.mk.injEq] at hxy
    exact hdist x y hne (by rw [hxy.1, hxy.2])
  have hTsub : Finset.univ.image (fun i : Fin r => (u i, ℓ i)) ⊆ s :=
    Finset.image_subset_iff.mpr (fun i _ => hmem i)
  have hsumT : ∑ p ∈ Finset.univ.image (fun i : Fin r => (u i, ℓ i)), p.2 = m := by
    rw [Finset.sum_image hginj]
    exact hsum
  have hchain : m ≤ ∑ p ∈ s, p.2 := by
    rw [← hsumT]
    exact Finset.sum_le_sum_of_subset hTsub
  have hle2 : ∑ p ∈ s, p.2 ≤ ∑ p ∈ s, (F p).natDegree := Finset.sum_le_sum hdegge
  have hseq : ∑ p ∈ s, p.2 = m := le_antisymm (by omega) hchain
  have hsT : s = Finset.univ.image (fun i : Fin r => (u i, ℓ i)) := by
    refine Finset.Subset.antisymm ?_ hTsub
    intro p hp
    by_contra hpT
    have hsplit := Finset.sum_sdiff (f := fun p : ℕ × ℕ => p.2) hTsub
    have hppos : 0 < p.2 := (hs1 p hp).2.1
    have hpmem : p ∈ s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i)) :=
      Finset.mem_sdiff.mpr ⟨hp, hpT⟩
    have h4 : p.2 ≤ ∑ q ∈ s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i)), q.2 :=
      Finset.single_le_sum (fun q _ => Nat.zero_le q.2) hpmem
    omega
  have hdegeq : ∀ p ∈ s, (F p).natDegree = p.2 := by
    intro p hp
    by_contra hne
    have hlt : p.2 < (F p).natDegree := lt_of_le_of_ne (hdegge p hp) (fun h => hne h.symm)
    have h2 := Finset.sum_lt_sum hdegge ⟨p, hp, hlt⟩
    omega
  -- STEP 6: the unit-width decision on every block (IFCG26 §4).
  have hFdec : ∀ p ∈ s, Irreducible (F p) ∧ efPair (F p) = (p.2, 1) := by
    intro p hp
    obtain ⟨-, hl', hcop'⟩ := hs1 p hp
    obtain ⟨hFm, hFp, -, -, -⟩ := hs3 p hp
    exact irreducible_of_isPure_natDegree_eq hπ hFm hl' hcop' hFp (hdegeq p hp)
  -- STEP 7: assemble the type.
  have hfactors : monicFactors (monicPoly a)
      = ∑ p ∈ s, ({F p} : Multiset (Polynomial O)) := by
    rw [hprod, monicFactors_prod s F hmon]
    exact Finset.sum_congr rfl fun p hp =>
      monicFactors_of_irreducible (hmon p hp) (hFdec p hp).1
  have hdata : (typeOf (monicPoly a)).data
      = Finset.univ.val.map (fun i : Fin r => ((ℓ i : ℕ), (1 : ℕ))) := by
    rw [typeOf_data, hfactors]
    rw [map_sum_singleton s F efPair]
    have hsing : ∀ p ∈ s, ({efPair (F p)} : Multiset (ℕ × ℕ)) = {(p.2, 1)} := by
      intro p hp
      rw [(hFdec p hp).2]
    rw [Finset.sum_congr rfl hsing, hsT, Finset.sum_image hginj]
    exact sum_singleton_eq_map Finset.univ (fun i : Fin r => ((ℓ i : ℕ), (1 : ℕ)))
  exact FactorizationType.ext hdata

-- `hu` kept for signature honesty, as in the main theorem.
set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- ★★ **THE OFF-ONE PIGEONHOLE** (the mixed genre at every mass, CRL §5's mechanism
generalized): visible pairwise-distinct two-point slopes `(uᵢ, ℓᵢ)` with EVERY `ℓᵢ ≥ 2`
and `Σᵢ ℓᵢ = m − 1` decide the class with type `⟨{(ℓᵢ, 1)}ᵢ + {(1, 1)}⟩` — the one
leftover degree cannot hide inside a fractional block (`ℓᵢ ∣ deg` with `ℓᵢ ≥ 2` forbids
excess `1`), so B.42's dissection is FORCED to carry exactly one extra block, monic
linear, hence split `(1, 1)`.  At `m = 3`, `T = {(1, 2)}` this is IFCG26 §5's mixed
cubic decision (visible-corner case). -/
theorem decidedAt_of_two_point_sides_off_one {m K r : ℕ} (hm : 0 < m) {c : Coeff O m K}
    {u ℓ : Fin r → ℕ}
    (hu : ∀ i, 0 < u i) (hl : ∀ i, 2 ≤ ℓ i) (hcop : ∀ i, Nat.Coprime (u i) (ℓ i))
    (hdist : ∀ i j, i ≠ j → u i * ℓ j ≠ u j * ℓ i)
    (hsum : (∑ i, ℓ i) + 1 = m)
    (hstr : ∀ i : Fin m, 1 ≤ classCoeffVal c i)
    (h0vis : classCoeffVal c ⟨0, hm⟩ < K)
    (hface : ∀ i, ∃ j j', j < j' ∧ NPAttains c (u i) (ℓ i) j ∧ NPAttains c (u i) (ℓ i) j')
    (hvis : ∀ i, NPVisibleAt c (u i) (ℓ i)) :
    DecidedAt O m
      ⟨Finset.univ.val.map (fun i : Fin r => ((ℓ i : ℕ), (1 : ℕ))) + {(1, 1)}⟩ K c := by
  intro a ha
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hK1 : 1 ≤ K := by omega
  -- STEPS 1–4 as in the main theorem.
  have hres : (monicPoly a).map (residue O) = X ^ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree, map_monicPoly]
    have hzero : (fun i => residue O (a i)) = (fun _ : Fin m => (0 : ResidueField O)) := by
      funext i
      have h7 := (le_classCoeffVal_iff_dvd hπ hK1 ha i).1 (hstr i)
      rw [pow_one] at h7
      exact (IsLocalRing.residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hπ _).2 h7)
    rw [hzero, monicPoly_zero']
  have ha0 : a ⟨0, hm⟩ ≠ 0 := by
    intro h
    exact (classCoeffVal_exact hπ ha h0vis).2 (h ▸ dvd_zero _)
  have hdev : dev X (monicPoly a) 0 ≠ 0 := by
    rw [dev_X, monicPoly_coeff_lt a hm]
    intro hC
    exact ha0 (by simpa using hC)
  have hdegpos : 0 < (monicPoly a).natDegree := by rw [monicPoly_natDegree]; exact hm
  obtain ⟨s, F, hs1, hs2, hs3, hprod, hs5, hs6⟩ :=
    exists_slope_factorization (μ := (monicPoly a).natDegree) hπ isKey_X
      (monicPoly_monic a) hdegpos (by rw [Polynomial.map_X]; exact hres) hdev
  have hmem : ∀ i : Fin r, (u i, ℓ i) ∈ s := by
    intro i
    obtain ⟨j, j', hjj', hAj, hAj'⟩ := hface i
    obtain ⟨hOj, -⟩ := onSide_monicPoly_of_npAttains hπ (by have := hl i; omega)
      (hvis i) hAj ha
    obtain ⟨hOj', -⟩ := onSide_monicPoly_of_npAttains hπ (by have := hl i; omega)
      (hvis i) hAj' ha
    refine (hs5 (u i) (ℓ i) (by have := hl i; omega) (hcop i)).1 ?_
    refine Finset.one_lt_card.mpr
      ⟨j, mem_sideSet_of_onSide ?_ hOj, j', mem_sideSet_of_onSide ?_ hOj', by omega⟩
    · rw [monicPoly_natDegree]; exact hAj.1
    · rw [monicPoly_natDegree]; exact hAj'.1
  -- STEP 5': the off-one accounting.
  have hmon : ∀ p ∈ s, (F p).Monic := fun p hp => (hs3 p hp).1
  have hdegsum : ∑ p ∈ s, (F p).natDegree = m := by
    have h1 := Polynomial.natDegree_prod_of_monic s F hmon
    rw [← hprod, monicPoly_natDegree] at h1
    exact h1.symm
  have hdegge : ∀ p ∈ s, p.2 ≤ (F p).natDegree := by
    intro p hp
    obtain ⟨-, hl', hcop'⟩ := hs1 p hp
    obtain ⟨hFm, hFp, -, -, hFd⟩ := hs3 p hp
    exact Nat.le_of_dvd hFd (dvd_natDegree_of_isPure hπ hFm hl' hcop' hFp)
  have hginj : ∀ x ∈ (Finset.univ : Finset (Fin r)), ∀ y ∈ Finset.univ,
      (fun i : Fin r => (u i, ℓ i)) x = (fun i : Fin r => (u i, ℓ i)) y → x = y := by
    intro x _ y _ hxy
    by_contra hne
    simp only [Prod.mk.injEq] at hxy
    exact hdist x y hne (by rw [hxy.1, hxy.2])
  have hTsub : Finset.univ.image (fun i : Fin r => (u i, ℓ i)) ⊆ s :=
    Finset.image_subset_iff.mpr (fun i _ => hmem i)
  have hsumT : ∑ p ∈ Finset.univ.image (fun i : Fin r => (u i, ℓ i)), p.2
      = ∑ i, ℓ i := Finset.sum_image hginj
  have hl2T : ∀ p ∈ Finset.univ.image (fun i : Fin r => (u i, ℓ i)), 2 ≤ p.2 := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact hl i
  -- Claim 1: every input block is TIGHT (`deg = ℓᵢ`): excess in a `ℓ ≥ 2` block is `≥ ℓ ≥ 2`.
  have hTdeg : ∀ p ∈ Finset.univ.image (fun i : Fin r => (u i, ℓ i)),
      (F p).natDegree = p.2 := by
    intro p₀ hp₀
    by_contra hne
    -- the excess-multiple bound: `p.2 ∣ deg`, `deg ≠ p.2`, `deg > 0` force `deg ≥ 2·p.2`
    have hdvd : p₀.2 ∣ (F p₀).natDegree := by
      obtain ⟨-, hl', hcop'⟩ := hs1 p₀ (hTsub hp₀)
      exact dvd_natDegree_of_isPure hπ (hs3 p₀ (hTsub hp₀)).1 hl' hcop'
        (hs3 p₀ (hTsub hp₀)).2.1
    obtain ⟨t, ht⟩ := hdvd
    have hFd := (hs3 p₀ (hTsub hp₀)).2.2.2.2
    have h2t : 2 ≤ t := by
      rcases Nat.lt_or_ge t 2 with h | h
      · interval_cases t
        · omega
        · omega
      · exact h
    have hbig : p₀.2 * 2 ≤ (F p₀).natDegree := by
      rw [ht]
      exact Nat.mul_le_mul_left _ h2t
    -- total over the input slopes then exceeds `m`
    have hsplit := Finset.sum_erase_add
      (Finset.univ.image (fun i : Fin r => (u i, ℓ i))) (fun p => (F p).natDegree) hp₀
    have hsplit2 := Finset.sum_erase_add
      (Finset.univ.image (fun i : Fin r => (u i, ℓ i))) (fun p : ℕ × ℕ => p.2) hp₀
    have hge : ∑ p ∈ (Finset.univ.image (fun i : Fin r => (u i, ℓ i))).erase p₀, p.2
        ≤ ∑ p ∈ (Finset.univ.image (fun i : Fin r => (u i, ℓ i))).erase p₀,
            (F p).natDegree :=
      Finset.sum_le_sum (fun p hp => hdegge p (hTsub (Finset.mem_of_mem_erase hp)))
    have hTtot : ∑ p ∈ Finset.univ.image (fun i : Fin r => (u i, ℓ i)),
        (F p).natDegree ≤ ∑ p ∈ s, (F p).natDegree :=
      Finset.sum_le_sum_of_subset hTsub
    have hp2 := hl2T p₀ hp₀
    omega
  -- Claim 2: the complement is exactly ONE monic linear block.
  have hsdiff := Finset.sum_sdiff (f := fun p => (F p).natDegree) hTsub
  have hTsum : ∑ p ∈ Finset.univ.image (fun i : Fin r => (u i, ℓ i)),
      (F p).natDegree = ∑ i, ℓ i := by
    rw [Finset.sum_congr rfl hTdeg]
    exact hsumT
  have hextra : ∑ p ∈ s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i)),
      (F p).natDegree = 1 := by omega
  have hqex : (s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i))).Nonempty := by
    rcases Finset.eq_empty_or_nonempty
      (s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i))) with h0 | h
    · rw [h0, Finset.sum_empty] at hextra
      omega
    · exact h
  obtain ⟨q, hq⟩ := hqex
  have hqs : q ∈ s := (Finset.mem_sdiff.mp hq).1
  have hqdeg : (F q).natDegree = 1 := by
    have h1 := Finset.sum_erase_add
      (s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i)))
      (fun p => (F p).natDegree) hq
    have h3 := (hs3 q hqs).2.2.2.2
    rcases Finset.eq_empty_or_nonempty
      ((s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i))).erase q) with hemp | hne
    · rw [hemp, Finset.sum_empty] at h1
      omega
    · obtain ⟨p', hp'⟩ := hne
      have h4 := Finset.single_le_sum
        (f := fun p => (F p).natDegree)
        (fun p _ => Nat.zero_le ((F p).natDegree)) hp'
      have h5 := (hs3 p'
        (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hp')).1).2.2.2.2
      omega
  have hsdiffq : s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i)) = {q} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hq, ?_⟩
    intro p hp
    by_contra hpq
    have h1 := Finset.sum_erase_add
      (s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i)))
      (fun p => (F p).natDegree) hq
    have h4 := Finset.single_le_sum
      (f := fun p => (F p).natDegree)
      (fun p _ => Nat.zero_le ((F p).natDegree))
      (Finset.mem_erase.mpr ⟨hpq, hp⟩)
    have h5 := (hs3 p (Finset.mem_sdiff.mp hp).1).2.2.2.2
    have h3 := (hs3 q hqs).2.2.2.2
    omega
  -- STEP 6': decide the blocks and assemble the type.
  have hFdec : ∀ p ∈ Finset.univ.image (fun i : Fin r => (u i, ℓ i)),
      Irreducible (F p) ∧ efPair (F p) = (p.2, 1) := by
    intro p hp
    obtain ⟨-, hl', hcop'⟩ := hs1 p (hTsub hp)
    obtain ⟨hFm, hFp, -, -, -⟩ := hs3 p (hTsub hp)
    exact irreducible_of_isPure_natDegree_eq hπ hFm hl' hcop' hFp (hTdeg p hp)
  have hqirr : Irreducible (F q) :=
    Uniformity.Density.IFCG26.irreducible_of_monic_natDegree_one (hmon q hqs) hqdeg
  have hqef : efPair (F q) = (1, 1) := efPair_of_natDegree_one (hmon q hqs) hqdeg
  have hfactors : monicFactors (monicPoly a)
      = ∑ p ∈ s, ({F p} : Multiset (Polynomial O)) := by
    rw [hprod, monicFactors_prod s F hmon]
    refine Finset.sum_congr rfl fun p hp => ?_
    refine monicFactors_of_irreducible (hmon p hp) ?_
    by_cases hpT : p ∈ Finset.univ.image (fun i : Fin r => (u i, ℓ i))
    · exact (hFdec p hpT).1
    · have hpq : p ∈ s \ Finset.univ.image (fun i : Fin r => (u i, ℓ i)) :=
        Finset.mem_sdiff.mpr ⟨hp, hpT⟩
      rw [hsdiffq, Finset.mem_singleton] at hpq
      rw [hpq]
      exact hqirr
  have hdata : (typeOf (monicPoly a)).data
      = Finset.univ.val.map (fun i : Fin r => ((ℓ i : ℕ), (1 : ℕ))) + {(1, 1)} := by
    rw [typeOf_data, hfactors, map_sum_singleton s F efPair]
    have hsplit := Finset.sum_sdiff
      (f := fun p => ({efPair (F p)} : Multiset (ℕ × ℕ))) hTsub
    rw [← hsplit, hsdiffq, Finset.sum_singleton, hqef]
    have hTpart : ∑ p ∈ Finset.univ.image (fun i : Fin r => (u i, ℓ i)),
        ({efPair (F p)} : Multiset (ℕ × ℕ))
        = Finset.univ.val.map (fun i : Fin r => ((ℓ i : ℕ), (1 : ℕ))) := by
      rw [Finset.sum_congr rfl (fun p hp => by rw [(hFdec p hp).2]),
        Finset.sum_image hginj]
      exact sum_singleton_eq_map Finset.univ (fun i : Fin r => ((ℓ i : ℕ), (1 : ℕ)))
    rw [hTpart]
    exact add_comm _ _
  exact FactorizationType.ext hdata

end Pigeonhole

/-! ## §2 — the staircase sector: totally split, counted, and DEEP -/

section Staircase

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The totally split type at mass `m`: `m` copies of `(1, 1)`. -/
def totallySplitType (m : ℕ) : FactorizationType := ⟨Multiset.replicate m (1, 1)⟩

/-- The strict-convexity heights are strictly decreasing (downward induction from the
monic point). -/
theorem npHeight_strict_anti_of_staircase {m K : ℕ} {c : Coeff O m K}
    (hconv : ∀ i, i + 2 ≤ m → 2 * npHeight c (i + 1) < npHeight c i + npHeight c (i + 2))
    (hlast : 1 ≤ npHeight c (m - 1)) :
    ∀ i, i + 1 ≤ m → npHeight c (i + 1) < npHeight c i := by
  have hSm : npHeight c m = 0 := by
    unfold Uniformity.Density.IFCG22.npHeight
    rw [dif_neg (lt_irrefl m)]
  have key : ∀ d i, i + d + 1 = m → npHeight c (i + 1) < npHeight c i := by
    intro d
    induction d with
    | zero =>
        intro i hi
        have h1 : i + 1 = m := by omega
        have h2 : m - 1 = i := by omega
        rw [h1, hSm]
        rw [h2] at hlast
        omega
    | succ d ih =>
        intro i hi
        have h3 : npHeight c (i + 2) < npHeight c (i + 1) := ih (i + 1) (by omega)
        have h4 := hconv i (by omega)
        omega
  intro i hi
  exact key (m - i - 1) i (by omega)

/-- ★ **The staircase decision** (the charge's literal target, the `ℓ ≡ 1` instance of
§1): a class whose heights are strictly convex with all-integer slopes — every abscissa
a polygon vertex — and visible corner is DECIDED TOTALLY SPLIT. -/
theorem decidedAt_staircase [IsAdicComplete (maximalIdeal O) O] {m K : ℕ} (hm : 0 < m)
    {c : Coeff O m K} (hvis : npHeight c 0 < K)
    (hconv : ∀ i, i + 2 ≤ m → 2 * npHeight c (i + 1) < npHeight c i + npHeight c (i + 2))
    (hlast : 1 ≤ npHeight c (m - 1)) :
    DecidedAt O m (totallySplitType m) K c := by
  have hdec := npHeight_strict_anti_of_staircase hconv hlast
  -- STEP 1: the integer slopes strictly decrease along the polygon.
  have hUdec : ∀ t, t + 2 ≤ m →
      npHeight c (t + 1) - npHeight c (t + 2) < npHeight c t - npHeight c (t + 1) := by
    intro t ht
    have h1 := hdec t (by omega)
    have h2 : npHeight c (t + 2) < npHeight c (t + 1) := hdec (t + 1) (by omega)
    have h3 := hconv t ht
    omega
  have hUmono : ∀ j i, j < i → i + 1 ≤ m →
      npHeight c i - npHeight c (i + 1) < npHeight c j - npHeight c (j + 1) := by
    intro j i
    induction i with
    | zero => intro h1 h2; omega
    | succ i' ih =>
        intro hji h1m
        rcases Nat.lt_or_ge j i' with hj | hj
        · have h1 : npHeight c (i' + 1) - npHeight c (i' + 1 + 1)
              < npHeight c i' - npHeight c (i' + 1) := hUdec i' (by omega)
          have h2 := ih hj (by omega)
          omega
        · obtain rfl : j = i' := by omega
          have h1 : npHeight c (j + 1) - npHeight c (j + 1 + 1)
              < npHeight c j - npHeight c (j + 1) := hUdec j (by omega)
          exact h1
  -- STEP 2: the two-sided attainment bounds for each slope.
  have claimD : ∀ i, i + 1 ≤ m → ∀ d j, j + d = i →
      npHeight c i + (npHeight c i - npHeight c (i + 1)) * i
        ≤ npHeight c j + (npHeight c i - npHeight c (i + 1)) * j := by
    intro i him d
    induction d with
    | zero =>
        intro j hj
        obtain rfl : j = i := by omega
        exact le_rfl
    | succ d ih =>
        intro j hj
        have hstep := ih (j + 1) (by omega)
        have hUj : npHeight c i - npHeight c (i + 1)
            < npHeight c j - npHeight c (j + 1) := hUmono j i (by omega) him
        have hdj : npHeight c (j + 1) < npHeight c j := hdec j (by omega)
        have hmul : (npHeight c i - npHeight c (i + 1)) * (j + 1)
            = (npHeight c i - npHeight c (i + 1)) * j
              + (npHeight c i - npHeight c (i + 1)) := Nat.mul_succ _ _
        omega
  have claimU : ∀ i, i + 1 ≤ m → ∀ j, i + 1 ≤ j → j ≤ m →
      npHeight c (i + 1) + (npHeight c i - npHeight c (i + 1)) * (i + 1)
        ≤ npHeight c j + (npHeight c i - npHeight c (i + 1)) * j := by
    intro i him j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ j hij ih =>
        intro hjm
        have hstep := ih (by omega)
        have hUj : npHeight c j - npHeight c (j + 1)
            < npHeight c i - npHeight c (i + 1) := hUmono i j (by omega) hjm
        have hdj : npHeight c (j + 1) < npHeight c j := hdec j (by omega)
        have hmul : (npHeight c i - npHeight c (i + 1)) * (j + 1)
            = (npHeight c i - npHeight c (i + 1)) * j
              + (npHeight c i - npHeight c (i + 1)) := Nat.mul_succ _ _
        omega
  -- STEP 3: the support value and the two attained abscissae per slope.
  have hsup : ∀ i, i + 1 ≤ m →
      classNPSupport c (npHeight c i - npHeight c (i + 1)) 1
        = npHeight c i + (npHeight c i - npHeight c (i + 1)) * i := by
    intro i him
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h1 := classNPSupport_le_apply c (npHeight c i - npHeight c (i + 1)) 1
        (show i ≤ m by omega)
      omega
    · intro j hjm
      rcases Nat.lt_or_ge i j with hij | hji
      · have h2 := claimU i him j (by omega) hjm
        have h3 : npHeight c (i + 1) < npHeight c i := hdec i him
        have hmul : (npHeight c i - npHeight c (i + 1)) * (i + 1)
            = (npHeight c i - npHeight c (i + 1)) * i
              + (npHeight c i - npHeight c (i + 1)) := Nat.mul_succ _ _
        omega
      · have h2 := claimD i him (i - j) j (by omega)
        omega
  have hatt : ∀ i, i + 1 ≤ m →
      NPAttains c (npHeight c i - npHeight c (i + 1)) 1 i
        ∧ NPAttains c (npHeight c i - npHeight c (i + 1)) 1 (i + 1) := by
    intro i him
    have hs := hsup i him
    have h3 : npHeight c (i + 1) < npHeight c i := hdec i him
    have hmul : (npHeight c i - npHeight c (i + 1)) * (i + 1)
        = (npHeight c i - npHeight c (i + 1)) * i
          + (npHeight c i - npHeight c (i + 1)) := Nat.mul_succ _ _
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  have hvisall : ∀ i, i + 1 ≤ m →
      NPVisibleAt c (npHeight c i - npHeight c (i + 1)) 1 := by
    intro i him
    show classNPSupport c (npHeight c i - npHeight c (i + 1)) 1 < 1 * K
    have h1 := classNPSupport_le_apply c (npHeight c i - npHeight c (i + 1)) 1
      (Nat.zero_le m)
    omega
  -- STEP 4: assemble the pigeonhole inputs at `ℓ ≡ 1`.
  have hu' : ∀ i : Fin m, 0 < npHeight c ↑i - npHeight c (↑i + 1) := by
    intro i
    have := hdec ↑i (by have := i.isLt; omega)
    omega
  have hdist' : ∀ i j : Fin m, i ≠ j →
      (npHeight c ↑i - npHeight c (↑i + 1)) * 1
        ≠ (npHeight c ↑j - npHeight c (↑j + 1)) * 1 := by
    intro i j hne
    have hij : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_ge ↑i ↑j with h | h
    · have := hUmono ↑i ↑j h (by have := j.isLt; omega)
      omega
    · have := hUmono ↑j ↑i (by omega) (by have := i.isLt; omega)
      omega
  have hsum' : ∑ _i : Fin m, (1 : ℕ) = m := by simp
  have hstr' : ∀ i : Fin m, 1 ≤ classCoeffVal c i := by
    intro i
    have h5 : npHeight c (i : ℕ) = resOrd (c i) := npHeight_coe c i
    have h6 := hdec ↑i (by have := i.isLt; omega)
    show 1 ≤ resOrd (c i)
    omega
  have h0vis' : classCoeffVal c ⟨0, hm⟩ < K := by
    have h5 : npHeight c ((⟨0, hm⟩ : Fin m) : ℕ) = resOrd (c ⟨0, hm⟩) :=
      npHeight_coe c ⟨0, hm⟩
    show resOrd (c ⟨0, hm⟩) < K
    rw [← h5]
    exact hvis
  have hface' : ∀ i : Fin m, ∃ j j', j < j' ∧
      NPAttains c (npHeight c ↑i - npHeight c (↑i + 1)) 1 j ∧
      NPAttains c (npHeight c ↑i - npHeight c (↑i + 1)) 1 j' := by
    intro i
    obtain ⟨h1, h2⟩ := hatt ↑i (by have := i.isLt; omega)
    exact ⟨↑i, ↑i + 1, by omega, h1, h2⟩
  have hvis' : ∀ i : Fin m, NPVisibleAt c (npHeight c ↑i - npHeight c (↑i + 1)) 1 :=
    fun i => hvisall ↑i (by have := i.isLt; omega)
  have hgen := decidedAt_of_two_point_sides (r := m) hm
    (u := fun i : Fin m => npHeight c ↑i - npHeight c (↑i + 1))
    (ℓ := fun _ : Fin m => 1)
    hu' (fun _ => Nat.one_pos) (fun _ => Nat.coprime_one_right _)
    hdist' hsum' hstr' h0vis' hface' hvis'
  -- STEP 5: the type is totally split.
  have hty : (⟨Finset.univ.val.map (fun _ : Fin m => ((1 : ℕ), (1 : ℕ)))⟩
      : FactorizationType) = totallySplitType m := by
    unfold totallySplitType
    congr 1
    rw [Multiset.map_const']
    congr 1
    simp
  rwa [hty] at hgen

/-- The exact-height coefficient box: every coordinate at its pinned windowed
valuation. -/
def exactBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m K : ℕ) (v : Fin m → ℕ) : Set (Coeff O m K) :=
  {c | ∀ i : Fin m, c i ∈ {x : Res O K | resOrd x = v i}}

theorem mem_exactBox_iff {m K : ℕ} (v : Fin m → ℕ) (c : Coeff O m K) :
    c ∈ exactBox O m K v ↔ ∀ i, resOrd (c i) = v i := Iff.rfl

/-- ★ **The staircase-cell count** (the CN4 monomial genre, every finite level, uniform
in `q, m, v`): each exact-height box has `(q−1)^m · q^(Σᵢ (K−vᵢ−1))` classes. -/
theorem card_exactBox {m K : ℕ} {v : Fin m → ℕ} (hv : ∀ i, v i < K) :
    Nat.card (exactBox O m K v : Set (Coeff O m K))
      = (residueCard O - 1) ^ m * residueCard O ^ (∑ i, (K - v i - 1)) := by
  classical
  unfold exactBox
  rw [card_pi_set]
  rw [Finset.prod_congr rfl (fun (i : Fin m) _ => card_setOf_resOrd_eq (hv i))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum]

/-- ★ **THE HONEST SCOPING THEOREM**: strict convexity of all-integer slopes FORCES the
Eisenstein-deep heights `m − i ≤ vᵢ` — every staircase class lies in the DEEP box. -/
theorem mem_deepBox_of_staircase {m K : ℕ} {c : Coeff O m K}
    (hconv : ∀ i, i + 2 ≤ m → 2 * npHeight c (i + 1) < npHeight c i + npHeight c (i + 2))
    (hlast : 1 ≤ npHeight c (m - 1)) :
    c ∈ deepBox O m K := by
  have hSm : npHeight c m = 0 := by
    unfold Uniformity.Density.IFCG22.npHeight
    rw [dif_neg (lt_irrefl m)]
  -- the slope floor: at distance `d + 1` from the monic point the drop is `≥ d + 1`
  have key : ∀ d i, i + d + 1 = m → npHeight c (i + 1) + d + 1 ≤ npHeight c i := by
    intro d
    induction d with
    | zero =>
        intro i hi
        have h1 : i + 1 = m := by omega
        have h2 : m - 1 = i := by omega
        rw [h1, hSm]
        rw [h2] at hlast
        omega
    | succ d ih =>
        intro i hi
        have h3 : npHeight c (i + 2) + d + 1 ≤ npHeight c (i + 1) := ih (i + 1) (by omega)
        have h4 := hconv i (by omega)
        omega
  show ∀ i : Fin m, m - (i : ℕ) ≤ resOrd (c i)
  intro i
  have h5 : npHeight c (i : ℕ) = resOrd (c i) := npHeight_coe c i
  have h6 := key (m - (i : ℕ) - 1) (i : ℕ) (by have := i.isLt; omega)
  have := i.isLt
  omega

/-- The scoping corollary: NO staircase class is shallow — the totally-split staircase
sector belongs to the zero-centre recentring range (the recursion), never to the cone
remainder carrier. -/
theorem staircase_not_shallow {m K : ℕ} {c : Coeff O m K}
    (hconv : ∀ i, i + 2 ≤ m → 2 * npHeight c (i + 1) < npHeight c i + npHeight c (i + 2))
    (hlast : 1 ≤ npHeight c (m - 1)) :
    c ∉ shallowSet O m K := by
  intro hsh
  obtain ⟨i, hi⟩ := hsh
  have hd := mem_deepBox_of_staircase hconv hlast i
  omega

end Staircase

/-! ## §3 — CN1-FOR-RESIDUALS (Lean-core): the side residual polynomial is class data -/

section ClassResidual

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★ **The two-sided bridge**: below the frame floor, an abscissa is on-side for a lift
IFF it attains the class support.  (IFCG26 §1 is the `←` direction; `→` is new: a lift's
on-side height is finite below the floor, hence exact, hence the class height.) -/
theorem onSide_monicPoly_iff {π : O} (hπ : Irreducible π) {m K u ℓ : ℕ} (hl : 0 < ℓ)
    {c : Coeff O m K} (hvis : NPVisibleAt c u ℓ) {a : Fin m → O}
    (ha : proj O m K a = c) {j : ℕ} (hj : j ≤ m) :
    OnSide X (monicPoly a) u ℓ j ↔ NPAttains c u ℓ j := by
  constructor
  · intro hO
    obtain ⟨i₀, hA₀⟩ := exists_npAttains c u ℓ
    obtain ⟨-, hsupp⟩ := onSide_monicPoly_of_npAttains hπ hl hvis hA₀ ha
    have hO' : ℓ • npHgt X (monicPoly a) j + ((u * j : ℕ) : ℕ∞)
        = ((classNPSupport c u ℓ : ℕ) : ℕ∞) := by
      rw [← hsupp]
      exact hO
    have hfloor : classNPSupport c u ℓ < ℓ * K := hvis
    rcases eq_or_lt_of_le hj with rfl | hjlt
    · -- the monic point: heights vanish on both sides
      rw [npHgt_monicPoly_top, smul_zero, zero_add] at hO'
      have h2 : u * j = classNPSupport c u ℓ := Nat.cast_inj.mp hO'
      refine ⟨le_rfl, ?_⟩
      have h3 : npHeight c j = 0 := by
        unfold Uniformity.Density.IFCG22.npHeight
        rw [dif_neg (lt_irrefl j)]
      rw [h3]
      omega
    · -- interior: the lift's height is finite below the floor, hence the class height
      have hfin : npHgt X (monicPoly a) j ≠ ⊤ := by
        intro htop
        rw [htop, nsmul_eq_mul,
          ENat.mul_top (by exact_mod_cast hl.ne' : (ℓ : ℕ∞) ≠ 0), top_add] at hO'
        exact (ENat.coe_ne_top _) hO'.symm
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
      have hn' : ((n : ℕ) : ℕ∞) = npHgt X (monicPoly a) j := hn
      rw [← hn', nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add] at hO'
      have hO'' : ℓ * n + u * j = classNPSupport c u ℓ := Nat.cast_inj.mp hO'
      have hnK : n < K := by
        have h4 : ℓ * n < ℓ * K := by omega
        exact Nat.lt_of_mul_lt_mul_left h4
      have hle := le_npHgt_monicPoly hπ ha hjlt
      rw [← hn'] at hle
      have hcle : classCoeffVal c ⟨j, hjlt⟩ ≤ n := Nat.cast_le.mp hle
      have hcvK : classCoeffVal c ⟨j, hjlt⟩ < K := lt_of_le_of_lt hcle hnK
      have heq := npHgt_monicPoly_eq hπ ha hjlt hcvK
      rw [← hn'] at heq
      have hneq : n = classCoeffVal c ⟨j, hjlt⟩ := Nat.cast_inj.mp heq
      refine ⟨hj, ?_⟩
      have h5 : npHeight c j = classCoeffVal c ⟨j, hjlt⟩ := by
        unfold Uniformity.Density.IFCG22.npHeight
        rw [dif_pos hjlt]
      rw [h5, ← hneq]
      exact hO''
  · intro hA
    exact (onSide_monicPoly_of_npAttains hπ hl hvis hA ha).1

/-- The class attainment set, as a `Finset` over the marked abscissae `0, …, m`. -/
def classSideSet {m K : ℕ} (c : Coeff O m K) (u ℓ : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (m + 1)).filter (NPAttains c u ℓ)

/-- ★ **CN1-for-residuals, the side set**: below the floor, EVERY lift's side set is the
class attainment set. -/
theorem sideSet_monicPoly_eq {π : O} (hπ : Irreducible π) {m K u ℓ : ℕ} (hl : 0 < ℓ)
    {c : Coeff O m K} (hvis : NPVisibleAt c u ℓ) {a : Fin m → O}
    (ha : proj O m K a = c) :
    sideSet X (monicPoly a) u ℓ = classSideSet c u ℓ := by
  ext j
  simp only [sideSet, classSideSet, Finset.mem_filter, Finset.mem_range,
    monicPoly_natDegree]
  constructor
  · rintro ⟨hj, hO⟩
    exact ⟨hj, (onSide_monicPoly_iff hπ hl hvis ha (by omega)).1 hO⟩
  · rintro ⟨hj, hA⟩
    exact ⟨hj, (onSide_monicPoly_iff hπ hl hvis ha (by omega)).2 hA⟩

/-- The left endpoint is class data. -/
theorem sideMin_monicPoly_eq {π : O} (hπ : Irreducible π) {m K u ℓ : ℕ} (hl : 0 < ℓ)
    {c : Coeff O m K} (hvis : NPVisibleAt c u ℓ) {a : Fin m → O}
    (ha : proj O m K a = c) (hne : (sideSet X (monicPoly a) u ℓ).Nonempty)
    (hcne : (classSideSet c u ℓ).Nonempty) :
    sideMin X (monicPoly a) u ℓ hne = (classSideSet c u ℓ).min' hcne :=
  min'_congr (sideSet_monicPoly_eq hπ hl hvis ha) hne hcne

/-- The right endpoint is class data. -/
theorem sideMax_monicPoly_eq {π : O} (hπ : Irreducible π) {m K u ℓ : ℕ} (hl : 0 < ℓ)
    {c : Coeff O m K} (hvis : NPVisibleAt c u ℓ) {a : Fin m → O}
    (ha : proj O m K a = c) (hne : (sideSet X (monicPoly a) u ℓ).Nonempty)
    (hcne : (classSideSet c u ℓ).Nonempty) :
    sideMax X (monicPoly a) u ℓ hne = (classSideSet c u ℓ).max' hcne :=
  max'_congr (sideSet_monicPoly_eq hπ hl hvis ha) hne hcne

private theorem digAt_congr {π : O} (hπ : Irreducible π) {N k : ℕ} (hk : k < N)
    {x y : O} (h : π ^ N ∣ x - y) : digAt π k x = digAt π k y := by
  classical
  have hsub : π ^ k ∣ x - y := (pow_dvd_pow π hk.le).trans h
  have hsub1 : π ^ (k + 1) ∣ x - y := (pow_dvd_pow π (Nat.succ_le_of_lt hk)).trans h
  by_cases hx : π ^ k ∣ x
  · have hneg : π ^ k ∣ -(x - y) := (dvd_neg).2 hsub
    have hz : digAt π k (-(x - y)) = 0 := (digAt_eq_zero_iff hπ hneg).2 ((dvd_neg).2 hsub1)
    have hyx : y = x + -(x - y) := by ring
    rw [hyx, digAt_add hπ hx hneg, hz, add_zero]
  · have hy : ¬ π ^ k ∣ y := by
      intro hy
      refine hx ?_
      have hxy : x = y + (x - y) := by ring
      rw [hxy]
      exact dvd_add hy hsub
    simp only [digAt, dif_neg hx, dif_neg hy]

private theorem digPoly_congr {π : O} (hπ : Irreducible π) {N k : ℕ} (hk : k < N)
    {a b : Polynomial O} (h : ∀ i, π ^ N ∣ (a - b).coeff i) :
    digPoly π k a = digPoly π k b := by
  refine Polynomial.ext fun i => ?_
  rw [digPoly_coeff hπ, digPoly_coeff hπ]
  refine digAt_congr hπ hk ?_
  simpa only [Polynomial.coeff_sub] using h i

private theorem resMk_congr {π : O} (hπ : Irreducible π) {N k : ℕ} (hk : k < N)
    {φ a b : Polynomial O} (h : ∀ i, π ^ N ∣ (a - b).coeff i) :
    resMk π φ k a = resMk π φ k b := by
  rw [resMk, resMk, digPoly_congr hπ hk h]

/-- Two lifts of one class have all coefficients congruent at level `K` — including the
monic top (`1 − 1 = 0`) and beyond. -/
theorem monicPoly_sub_coeff_dvd {π : O} (hπ : Irreducible π) {m K : ℕ}
    {c : Coeff O m K} {a a' : Fin m → O} (ha : proj O m K a = c)
    (ha' : proj O m K a' = c) (j : ℕ) :
    π ^ K ∣ (monicPoly a - monicPoly a').coeff j := by
  rw [Polynomial.coeff_sub]
  rcases Nat.lt_or_ge j m with hj | hj
  · rw [monicPoly_coeff_lt a hj, monicPoly_coeff_lt a' hj]
    have h1 : Ideal.Quotient.mk ((maximalIdeal O) ^ K) (a ⟨j, hj⟩)
        = Ideal.Quotient.mk ((maximalIdeal O) ^ K) (a' ⟨j, hj⟩) := by
      have h2 := congrFun ha ⟨j, hj⟩
      have h3 := congrFun ha' ⟨j, hj⟩
      rw [← h3] at h2
      exact h2
    have h4 := Ideal.Quotient.eq.mp h1
    exact (mem_maximalIdeal_pow_iff_dvd_of_irr hπ K _).1 h4
  · rcases eq_or_lt_of_le hj with rfl | hjm
    · have hc : (monicPoly a).coeff m = 1 := by
        have h5 := (monicPoly_monic a).coeff_natDegree
        rwa [monicPoly_natDegree] at h5
      have hc' : (monicPoly a').coeff m = 1 := by
        have h5 := (monicPoly_monic a').coeff_natDegree
        rwa [monicPoly_natDegree] at h5
      rw [hc, hc', sub_self]
      exact dvd_zero _
    · have hc : (monicPoly a).coeff j = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [monicPoly_natDegree]
        exact hjm
      have hc' : (monicPoly a').coeff j = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [monicPoly_natDegree]
        exact hjm
      rw [hc, hc', sub_self]
      exact dvd_zero _

/-- ★★ **CN1-FOR-RESIDUALS** — the side residual polynomial is a CLASS INVARIANT: below
the frame floor, any two lifts of `c` have the same left height and THE SAME residual
polynomial at the x-frame.  (The digits at the side's lattice points are read strictly
below the floor, where they are level-`K` data.)  This is the wide-face refinement's
required input: the residual's factorization type is class data. -/
theorem resPoly_monicPoly_eq {π : O} (hπ : Irreducible π) {m K u ℓ : ℕ}
    (hl : 0 < ℓ) {c : Coeff O m K} (hvis : NPVisibleAt c u ℓ)
    {a a' : Fin m → O} (ha : proj O m K a = c) (ha' : proj O m K a' = c)
    (hne : (sideSet X (monicPoly a) u ℓ).Nonempty)
    (hne' : (sideSet X (monicPoly a') u ℓ).Nonempty)
    {H₀ H₀' : ℕ}
    (hH : npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hne) = (H₀ : ℕ∞))
    (hH' : npHgt X (monicPoly a') (sideMin X (monicPoly a') u ℓ hne') = (H₀' : ℕ∞)) :
    H₀ = H₀' ∧
      resPoly π X (monicPoly a) u ℓ hne H₀ = resPoly π X (monicPoly a') u ℓ hne' H₀' := by
  -- STEP 1: the side data are class-pinned.
  have hs := sideSet_monicPoly_eq hπ hl hvis ha
  have hcne : (classSideSet c u ℓ).Nonempty := hs ▸ hne
  have hmin : sideMin X (monicPoly a) u ℓ hne = sideMin X (monicPoly a') u ℓ hne' := by
    rw [sideMin_monicPoly_eq hπ hl hvis ha hne hcne,
      sideMin_monicPoly_eq hπ hl hvis ha' hne' hcne]
  have hmax : sideMax X (monicPoly a) u ℓ hne = sideMax X (monicPoly a') u ℓ hne' := by
    rw [sideMax_monicPoly_eq hπ hl hvis ha hne hcne,
      sideMax_monicPoly_eq hπ hl hvis ha' hne' hcne]
  have hdeg : sideDeg X (monicPoly a) u ℓ hne = sideDeg X (monicPoly a') u ℓ hne' := by
    unfold Uniformity.Density.Leaf.sideDeg
    rw [hmin, hmax]
  -- STEP 2: both left heights are pinned by the shared support value.
  obtain ⟨i₀, hA₀⟩ := exists_npAttains c u ℓ
  obtain ⟨-, hsupp⟩ := onSide_monicPoly_of_npAttains hπ hl hvis hA₀ ha
  obtain ⟨-, hsupp'⟩ := onSide_monicPoly_of_npAttains hπ hl hvis hA₀ ha'
  have hnat : ℓ * H₀ + u * sideMin X (monicPoly a) u ℓ hne
      = classNPSupport c u ℓ := by
    have hO₀ : OnSide X (monicPoly a) u ℓ (sideMin X (monicPoly a) u ℓ hne) :=
      onSide_of_mem_sideSet (Finset.min'_mem _ _)
    have h7 : ℓ • npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hne)
        + ((u * sideMin X (monicPoly a) u ℓ hne : ℕ) : ℕ∞)
        = ((classNPSupport c u ℓ : ℕ) : ℕ∞) := by
      rw [← hsupp]
      exact hO₀
    rw [hH, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add] at h7
    exact Nat.cast_inj.mp h7
  have hnat' : ℓ * H₀' + u * sideMin X (monicPoly a') u ℓ hne'
      = classNPSupport c u ℓ := by
    have hO₀' : OnSide X (monicPoly a') u ℓ (sideMin X (monicPoly a') u ℓ hne') :=
      onSide_of_mem_sideSet (Finset.min'_mem _ _)
    have h7 : ℓ • npHgt X (monicPoly a') (sideMin X (monicPoly a') u ℓ hne')
        + ((u * sideMin X (monicPoly a') u ℓ hne' : ℕ) : ℕ∞)
        = ((classNPSupport c u ℓ : ℕ) : ℕ∞) := by
      rw [← hsupp']
      exact hO₀'
    rw [hH', nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add] at h7
    exact Nat.cast_inj.mp h7
  rw [← hmin] at hnat'
  have hH₀eq : H₀ = H₀' := Nat.eq_of_mul_eq_mul_left hl (by omega)
  have hfloor : classNPSupport c u ℓ < ℓ * K := hvis
  have hH₀K : H₀ < K := by
    have h11 : ℓ * H₀ < ℓ * K := by omega
    exact Nat.lt_of_mul_lt_mul_left h11
  -- STEP 3: the residual coefficients are the class digits, read below the floor.
  refine ⟨hH₀eq, ?_⟩
  unfold Uniformity.Density.Leaf.resPoly
  rw [hdeg]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hcoeff : resCoeff π X (monicPoly a) u ℓ hne H₀ k
      = resCoeff π X (monicPoly a') u ℓ hne' H₀' k := by
    unfold Uniformity.Density.Leaf.resCoeff
    rw [← hmin, ← hH₀eq]
    refine resMk_congr hπ (show H₀ - u * k < K by omega) fun i => ?_
    rw [dev_X, dev_X, ← Polynomial.C_sub]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [Polynomial.coeff_C_zero]
      have h12 := monicPoly_sub_coeff_dvd hπ ha ha'
        (sideMin X (monicPoly a) u ℓ hne + ℓ * k)
      rwa [Polynomial.coeff_sub] at h12
    · rw [Polynomial.coeff_C, if_neg (by omega)]
      exact dvd_zero _
  rw [hcoeff]

end ClassResidual

end Uniformity.Density.IFCG28

end

/-! ## AXCHECK FOOTER — §0/§2-counting/§2-scoping/§3 expect Lean core
`{propext, Classical.choice, Quot.sound}`; §1 and the §2 decision theorems expect Lean
core PLUS exactly the signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42).  The C.33 cites must NOT
occur. -/

#print axioms Uniformity.Density.IFCG28.monicFactors_prod
#print axioms Uniformity.Density.IFCG28.decidedAt_of_two_point_sides
#print axioms Uniformity.Density.IFCG28.decidedAt_of_two_point_sides_off_one
#print axioms Uniformity.Density.IFCG28.npHeight_strict_anti_of_staircase
#print axioms Uniformity.Density.IFCG28.decidedAt_staircase
#print axioms Uniformity.Density.IFCG28.card_exactBox
#print axioms Uniformity.Density.IFCG28.mem_deepBox_of_staircase
#print axioms Uniformity.Density.IFCG28.staircase_not_shallow
#print axioms Uniformity.Density.IFCG28.onSide_monicPoly_iff
#print axioms Uniformity.Density.IFCG28.sideSet_monicPoly_eq
#print axioms Uniformity.Density.IFCG28.sideMin_monicPoly_eq
#print axioms Uniformity.Density.IFCG28.sideMax_monicPoly_eq
#print axioms Uniformity.Density.IFCG28.monicPoly_sub_coeff_dvd
#print axioms Uniformity.Density.IFCG28.resPoly_monicPoly_eq
