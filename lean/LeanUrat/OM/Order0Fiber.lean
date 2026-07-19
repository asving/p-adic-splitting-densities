/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.Order0Root
import LeanUrat.OM.Order0Fact
import LeanUrat.OM.Order0Capstone

/-!
# Order0Fiber — γ6 (converse / stratum characterization)
(`notes/HNODE0_BLUEPRINT.md` §5, node γ6)

**The statement.** For `0 < N`, `0 < n`, `lam : Nat.Partition n` and `f : monicBox p N n`,
`B.classify p n N f = sepShape n lam` FORCES `f` to be generic-λ:

* `hunit` — the constant coefficient is a unit (`zmodValuation p N (f.coeff 0) = 0`);
* `Squarefree f̄` for the mod-`p` reduction `f̄ := (f.1).map (ZMod.castHom … (ZMod p))`;
* the factor-degree pattern `(normalizedFactors f̄).map natDegree = lam.parts`.

**Extraction chain** (each node a lemma below):
1. One-step unfold of the `classifyAux` budget recursion (`Nat.strongRecOn_eq`, local copy —
   `classifyAux_head_payload`): the emitted shape is
   `⟨(order, clusterSize, dr) :: children, M5.encodeCells (rootCtx …)⟩`.
2. The payload of `sepShape n lam` is NONEMPTY (`lam.parts ≠ 0` for `0 < n`), and every payload
   cell of the classifier carries `polygon = T.Nr`, so `T.Nr = flatFace n`. The no-side branch has
   `Nr.width = 0 ≠ n`, so a side `S` was selected, with `M7.toSideFace S = flatFace n`.
3. Face injectivity on the reachable sides (`latticePolygon_height0_eq` + the width slot):
   `S.length = n` and `S.v₀ = sideCeilHeight S 0 = sideCeilHeight (flatSide n) 0 = 0` — the
   column-`0` ceiling height genuinely separates the flat side from the slope-`(−1)` side
   `(0,n)–(n,0)` (same width, same `e = 1`). The side endpoints are hull vertices, hence SUPPORT
   dots (`npVertices_mem_support`), so `S.j₀ ≤ n` (`boxValSupport_fst_le`), forcing
   `S.i₀ = 0, S.j₀ = n`; the left endpoint `(0, 0) ∈ boxValSupport` reads exactly `hunit`.
4. With `hunit`, γ3 (`Order0Root.fRootCtx_Rr`) pins `T.Rr = f̄` with `natDegree = n`. Mapping the
   payload equality through the `dS` slot gives the factor-degree LIST equality
   (`encodeCells_map_dS`), hence the multiset equality `F.factors.val.map natDegree = lam.parts`.
   The degree budget `∑ mult·deg = n` (`ResidualFactorization.degree_budget`) against
   `∑ deg = ∑ lam.parts = n` forces every `mult = 1` (`Finset.sum_eq_sum_iff_of_le`), so
   `f̄ = ∏ ψ ∈ factors, ψ` is a product of DISTINCT monic irreducibles:
   `normalizedFactors f̄ = factors.val` (`normalizedFactors_prod_eq`), squarefreeness by
   `squarefree_iff_nodup_normalizedFactors`, and the pattern equality follows.

All sorry-free.
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.OM.Order0

open Polynomial
open scoped Classical

/-! ## 1. One-step unfold of the `classifyAux` budget recursion (local, race-free copy) -/

/-- **One-step unfold of `classifyAux`** (`Nat.strongRecOn_eq` + beta). The emitted shape has root
tuple `(order, clusterSize, dr)` followed by SOME child list, and payload `M5.encodeCells Tctx`.
(The child list is exposed only existentially — γ6 needs the head and the payload.) -/
theorem classifyAux_head_payload (p : ℕ) [Fact p.Prime] (N n budget : ℕ)
    (f : QuotientBox.monicBox p N n) (Tctx : M5.OMType)
    (hT : M5.clusterSize Tctx = budget) :
    ∃ rest, B.classifyAux p N n budget f Tctx hT
      = ⟨(Tctx.order, M5.clusterSize Tctx, Tctx.dr) :: rest, M5.encodeCells Tctx⟩ := by
  unfold B.classifyAux
  rw [Nat.strongRecOn_eq]
  exact ⟨_, rfl⟩

/-- **One-step unfold of `classify`** at `0 < N`: the root context is the f-DEPENDENT
`fRootCtx p N hN f` (`dif_pos`), and the emitted shape is its root tuple + payload. -/
theorem classify_head_payload (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (f : QuotientBox.monicBox p N n) :
    ∃ rest, B.classify p n N f
      = ⟨((B.fRootCtx p N hN f).order, M5.clusterSize (B.fRootCtx p N hN f),
          (B.fRootCtx p N hN f).dr) :: rest,
         M5.encodeCells (B.fRootCtx p N hN f)⟩ := by
  have hroot : B.rootCtx p N f = B.fRootCtx p N hN f := by
    unfold B.rootCtx
    exact dif_pos hN
  obtain ⟨rest, hu⟩ :=
    classifyAux_head_payload p N n n f (B.rootCtx p N f) (B.clusterSize_rootCtx p N f)
  have hu2 : B.classify p n N f
      = ⟨((B.rootCtx p N f).order, M5.clusterSize (B.rootCtx p N f), (B.rootCtx p N f).dr)
          :: rest, M5.encodeCells (B.rootCtx p N f)⟩ := hu
  rw [hroot] at hu2
  exact ⟨rest, hu2⟩

/-! ## 2. Hull-scan geometry: vertices are support dots; face heights are injective at column 0 -/

/-- **Every genuine Newton-polygon vertex is a SUPPORT dot**: `npVertices` entries are hull dots at
hull abscissae, which are the on-hull support dots themselves (`hullHeightAt_of_onHull`). -/
theorem npVertices_mem_support (Su : Finset (ℕ × ℕ)) (hSu : Su.Nonempty) {P : ℕ × ℕ}
    (hP : P ∈ NewtonPolygon.npVertices Su hSu) : P ∈ Su := by
  have hP' : P ∈ NewtonPolygon.npVerticesFull Su hSu :=
    (NewtonPolygon.dropCollinear_sublist _).subset hP
  unfold NewtonPolygon.npVerticesFull at hP'
  rw [List.mem_map] at hP'
  obtain ⟨i, hi, rfl⟩ := hP'
  rw [NewtonPolygon.mem_hullAbscissae_iff] at hi
  obtain ⟨v, hiv, hon⟩ := hi
  unfold NewtonPolygon.hullDotAt
  rw [NewtonPolygon.hullHeightAt_of_onHull Su hSu hiv hon]
  exact hiv

/-- Equal lattice polygons have equal column-`0` ceiling heights (the dependent-field extraction;
proof-irrelevant in the width witnesses). -/
theorem latticePolygon_height0_eq {P Q : L4.LatticePolygon} (h : P = Q)
    (hP : 0 < P.width) (hQ : 0 < Q.width) :
    P.ceilHeights ⟨0, hP⟩ = Q.ceilHeights ⟨0, hQ⟩ := by
  subst h
  rfl

/-! ## 3. The payload `dS` slot reads the factor-degree list -/

/-- **The payload's `dS` slots are the (degree-sorted) factor degrees** of `T.Rr`'s chosen
factorization: mapping `M5.encodeCells T` through `ShapeCell.dS` gives the mergeSort-by-degree of
the factor-degree list. -/
theorem encodeCells_map_dS (T : M5.OMType) :
    (M5.encodeCells T).map ShapeCell.dS
      = ((Classical.choice (M4.factorize_any T.Rr)).factors.attach.toList.mergeSort
          (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
        (fun x => x.1.natDegree) := by
  simp only [M5.encodeCells, M5.cells, List.map_map]
  exact List.map_congr_left (fun x _ => by rcases x with ⟨ψ, hψ⟩; rfl)

/-- **Multiset of a sorted attach-list image = image of the underlying multiset.** The mergeSort is
a permutation, the `toList` coe is `Finset.coe_toList`, and the attach/val transport is
`Multiset.attach_map_val'` (applied by `exact` — the subtype domains `{x // x ∈ s}` /
`{x // x ∈ s.val}` are definitionally equal but resist `rw`'s motive check). -/
theorem sorted_attach_map_coe {α β : Type*} (s : Finset α) (g : α → β)
    (cmp : {x // x ∈ s} → {x // x ∈ s} → Bool) :
    (((s.attach.toList.mergeSort cmp).map (fun x => g x.1) : List β) : Multiset β)
      = s.val.map g := by
  calc (((s.attach.toList.mergeSort cmp).map (fun x => g x.1) : List β) : Multiset β)
      = ((s.attach.toList.map (fun x => g x.1) : List β) : Multiset β) :=
        Multiset.coe_eq_coe.mpr ((List.mergeSort_perm _ _).map _)
    _ = s.val.map g := by
        rw [← Multiset.map_coe, Finset.coe_toList]
        exact Multiset.attach_map_val' s.val g

/-! ## 4. γ6 — the fiber characterization -/

/-- **γ6 (converse / stratum characterization)** (`HNODE0_BLUEPRINT` §5). If the genuine OM
classifier sends `f` to the separable leaf shape `sepShape n lam` (for `0 < N`, `0 < n`), then `f`
lies on the generic-λ stratum: unit constant coefficient, squarefree mod-`p` reduction
`f̄ := (f.1).map (ZMod.castHom …)`, and factor-degree pattern
`(normalizedFactors f̄).map natDegree = lam.parts`. -/
theorem classify_eq_sepShape_only_if (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N)
    (hn : 0 < n) (lam : Nat.Partition n) (f : QuotientBox.monicBox p N n)
    (h : B.classify p n N f = sepShape n lam) :
    PadicLift.zmodValuation p N ((f.1).coeff 0) = 0
      ∧ Squarefree ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)))
      ∧ (UniqueFactorizationMonoid.normalizedFactors
            ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)))).map
          Polynomial.natDegree = lam.parts := by
  -- ── Step 1: one-step unfold; the payload equality ──
  obtain ⟨rest, hu⟩ := classify_head_payload p n N hN f
  rw [h] at hu
  have hcells : M5.encodeCells (B.fRootCtx p N hN f)
      = (lam.parts.sort (· ≤ ·)).map (fun d => (⟨d, 1, flatFace n, []⟩ : ShapeCell)) := by
    have hc := congrArg ClusterShape.cells hu
    exact hc.symm
  -- ── the payload is nonempty (`lam.parts ≠ 0` since `0 < n`) ──
  have hparts_ne : lam.parts ≠ 0 := by
    intro h0
    have hsum := lam.parts_sum
    rw [h0, Multiset.sum_zero] at hsum
    omega
  have hsort_ne : lam.parts.sort (· ≤ ·) ≠ [] := by
    intro h0
    apply hparts_ne
    have hs := Multiset.sort_eq lam.parts (· ≤ ·)
    rw [h0] at hs
    exact hs.symm
  have hpayload_ne : M5.encodeCells (B.fRootCtx p N hN f) ≠ [] := by
    rw [hcells]
    intro hc
    exact hsort_ne (List.map_eq_nil_iff.mp hc)
  -- ── Step 2: every payload polygon slot is `T.Nr` on the left, `flatFace n` on the right ──
  have hNr : (B.fRootCtx p N hN f).Nr = flatFace n := by
    obtain ⟨sc, hsc⟩ := List.exists_mem_of_ne_nil _ hpayload_ne
    have h1 : sc.polygon = (B.fRootCtx p N hN f).Nr := by
      have hsc' := hsc
      simp only [M5.encodeCells, M5.cells, List.map_map, List.mem_map] at hsc'
      obtain ⟨⟨ψ, hψ⟩, _, rfl⟩ := hsc'
      rfl
    have h2 : sc.polygon = flatFace n := by
      rw [hcells] at hsc
      rw [List.mem_map] at hsc
      obtain ⟨d, _, rfl⟩ := hsc
      rfl
    rw [← h1, h2]
  -- ── a side was selected (the no-side face has width 0 ≠ n) ──
  have hNrFace : B.rootFace p N hN f = flatFace n := hNr
  obtain ⟨S, hS⟩ : ∃ S, B.rootSide p N hN f = some S := by
    cases hSc : B.rootSide p N hN f with
    | some S => exact ⟨S, rfl⟩
    | none =>
        exfalso
        have hface0 : B.rootFace p N hN f = ⟨0, fun _ => 0, fun _ => false⟩ := by
          unfold B.rootFace
          rw [hSc]
        rw [hface0] at hNrFace
        have hw := congrArg L4.LatticePolygon.width hNrFace
        simp only [flatFace, flatSide, M7.toSideFace, NewtonPolygon.Side.length] at hw
        omega
  have hfaceS : M7.toSideFace S = flatFace n := by
    have hrS : B.rootFace p N hN f = M7.toSideFace S := by
      unfold B.rootFace
      rw [hS]
    rw [← hrS]
    exact hNrFace
  -- ── Step 3a: width slot ⟹ `S.j₀ − S.i₀ = n` ──
  have hlen : S.j₀ - S.i₀ = n := by
    have hw := congrArg L4.LatticePolygon.width hfaceS
    simpa [M7.toSideFace, flatFace, flatSide, NewtonPolygon.Side.length] using hw
  -- ── Step 3b: column-0 ceiling height ⟹ `S.v₀ = 0` (kills the slope-(−1) side) ──
  have hposS : 0 < (M7.toSideFace S).width := by
    show 0 < S.length
    unfold NewtonPolygon.Side.length
    omega
  have hposF : 0 < (flatFace n).width := by
    show 0 < NewtonPolygon.Side.length ⟨0, n, 0, 0⟩
    rw [flatSide_length]
    exact hn
  have hv0 : S.v₀ = 0 := by
    have h0 := latticePolygon_height0_eq hfaceS hposS hposF
    have hl : (M7.toSideFace S).ceilHeights ⟨0, hposS⟩ = S.v₀ := M7.sideCeilHeight_zero S
    have hr : (flatFace n).ceilHeights ⟨0, hposF⟩ = 0 := M7.sideCeilHeight_zero (flatSide n)
    rw [hl, hr] at h0
    exact h0
  -- ── Step 3c: the side endpoints are support dots; `S.j₀ ≤ n` ⟹ `S.i₀ = 0` ⟹ `hunit` ──
  have hmemS : S ∈ NewtonPolygon.npSides (B.boxValSupport p N f)
      (B.boxValSupport_nonempty p N hN f) := by
    have hS' : (NewtonPolygon.npSides (B.boxValSupport p N f)
        (B.boxValSupport_nonempty p N hN f)).head? = some S := hS
    exact List.mem_of_mem_head? hS'
  unfold NewtonPolygon.npSides at hmemS
  rw [List.mem_map] at hmemS
  obtain ⟨⟨⟨i, v⟩, ⟨j, w⟩⟩, hpr, hprEq⟩ := hmemS
  obtain ⟨hPmem, hQmem⟩ := List.of_mem_zip hpr
  have hQmem' := List.mem_of_mem_tail hQmem
  have hi0 : S.i₀ = i := by rw [← hprEq]
  have hj0 : S.j₀ = j := by rw [← hprEq]
  have hv0' : S.v₀ = v := by rw [← hprEq]
  have hPsupp : ((i : ℕ), (v : ℕ)) ∈ B.boxValSupport p N f :=
    npVertices_mem_support _ _ hPmem
  have hQsupp : ((j : ℕ), (w : ℕ)) ∈ B.boxValSupport p N f :=
    npVertices_mem_support _ _ hQmem'
  have hj_le : j ≤ n := boxValSupport_fst_le p n N f (j, w) hQsupp
  have hi_eq : i = 0 := by
    rw [hi0, hj0] at hlen
    omega
  have hv_eq : v = 0 := by
    rw [← hv0']
    exact hv0
  have h00 : ((0 : ℕ), (0 : ℕ)) ∈ B.boxValSupport p N f := by
    have hmm := hPsupp
    rw [hi_eq, hv_eq] at hmm
    exact hmm
  have hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0 := by
    have hmem := h00
    unfold LeanUrat.OM.B.boxValSupport at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨k, hk, hkeq⟩ := hmem
    have hk0 : k = 0 := congrArg Prod.fst hkeq
    have hval : PadicLift.zmodValuation p N ((f.1).coeff k) = 0 := congrArg Prod.snd hkeq
    rw [hk0] at hval
    exact hval
  -- ── Step 4: γ3 applies; the payload degree-multiset pins squarefreeness and the pattern ──
  have hRr : (B.fRootCtx p N hN f).Rr
      = (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) :=
    fRootCtx_Rr p n N hN hn f hunit
  have hmon : ((B.fRootCtx p N hN f).Rr).Monic := by
    rw [hRr]
    exact f.2.1.map _
  have hR0 : (B.fRootCtx p N hN f).Rr ≠ 0 := hmon.ne_zero
  have hdegR : ((B.fRootCtx p N hN f).Rr).natDegree = n :=
    rootResidual_natDegree p n N hN hn f hunit
  -- the factor-degree LIST equality from the payload `dS` slots
  have hdegList :
      ((Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors.attach.toList.mergeSort
          (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
        (fun x => x.1.natDegree)
      = lam.parts.sort (· ≤ ·) := by
    have hmap := congrArg (List.map ShapeCell.dS) hcells
    rw [encodeCells_map_dS] at hmap
    refine hmap.trans ?_
    rw [List.map_map]
    exact (List.map_congr_left (fun d _ => rfl)).trans (List.map_id _)
  -- the factor-degree MULTISET equality
  have hdegM :
      (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors.val.map
        Polynomial.natDegree = lam.parts := by
    have hcoe : (((Classical.choice
          (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors.attach.toList.mergeSort
            (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
          (fun x => x.1.natDegree) : Multiset ℕ)
        = lam.parts := by
      rw [← Multiset.sort_eq lam.parts (· ≤ ·)]
      exact congrArg _ hdegList
    exact (sorted_attach_map_coe _ _ _).symm.trans hcoe
  -- sum bookkeeping: `∑ deg = n = ∑ mult·deg` forces every `mult = 1`
  have hsum1 : ∑ ψ ∈ (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors,
      ψ.natDegree = n := by
    have hs := congrArg Multiset.sum hdegM
    rw [lam.parts_sum] at hs
    rw [Finset.sum_eq_multiset_sum]
    exact hs
  have hbudget : ∑ ψ ∈ (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors,
      (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).mult ψ * ψ.natDegree
      = n := by
    have hb := (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).degree_budget
    rwa [hdegR] at hb
  have hmult1 : ∀ ψ ∈ (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors,
      (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).mult ψ = 1 := by
    have hle : ∀ ψ ∈ (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors,
        ψ.natDegree
          ≤ (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).mult ψ
              * ψ.natDegree := fun ψ hψ =>
      Nat.le_mul_of_pos_left _
        ((Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).mult_pos ψ hψ)
    have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (hsum1.trans hbudget.symm)
    intro ψ hψ
    have hdpos : 0 < ψ.natDegree :=
      ((Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors_irreducible
        ψ hψ).natDegree_pos
    have h2 : (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).mult ψ
        * ψ.natDegree = 1 * ψ.natDegree := by
      rw [one_mul]
      exact (heq ψ hψ).symm
    exact Nat.eq_of_mul_eq_mul_right hdpos h2
  -- `R = ∏ ψ ∈ factors, ψ`, a product of DISTINCT monic irreducibles
  have hprod : (B.fRootCtx p N hN f).Rr
      = ∏ ψ ∈ (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors, ψ := by
    have hpe := (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).prod_eq
    rw [hmon.leadingCoeff, Polynomial.C_1, one_mul] at hpe
    conv_lhs => rw [hpe]
    exact Finset.prod_congr rfl (fun ψ hψ => by rw [hmult1 ψ hψ, pow_one])
  -- transport to the mod-`p` reduction spelling (the goal's `(ZMod p)[X]` instance path —
  -- restating at the concrete type keeps `normalizedFactors`' `DecidableEq`-dependent
  -- `NormalizationMonoid` instance on the `ZMod.decidableEq` path of the goal)
  have hprodF : (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))
      = ∏ ψ ∈ (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors, ψ := by
    rw [← hRr]
    exact hprod
  have hR0F : (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) ≠ 0 := by
    rw [← hRr]
    exact hR0
  -- transport the factor multiset ONCE to a clean `(ZMod p)[X]`-typed variable `m`, so all
  -- remaining instance synthesis (in particular `normalizedFactors`' `NormalizationMonoid`)
  -- runs on the concrete `ZMod p` path
  obtain ⟨m, hm⟩ : ∃ (m : Multiset ((ZMod p)[X])),
      m = (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors.val :=
    ⟨_, rfl⟩
  have hmdeg : m.map Polynomial.natDegree = lam.parts := by
    rw [hm]
    exact hdegM
  have hmirr : ∀ ψ ∈ m, Irreducible ψ := by
    rw [hm]
    exact fun ψ hψ =>
      (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors_irreducible ψ hψ
  have hmmon : ∀ ψ ∈ m, Polynomial.Monic ψ := by
    rw [hm]
    exact fun ψ hψ =>
      (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors_monic ψ hψ
  have hmnodup : m.Nodup := by
    rw [hm]
    exact (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors.nodup
  have hprodm : (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) = m.prod := by
    refine hprodF.trans ?_
    rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    exact (congrArg Multiset.prod hm).symm
  have hnfm : UniqueFactorizationMonoid.normalizedFactors m.prod = m := by
    rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq m hmirr]
    exact (Multiset.map_congr rfl (fun ψ hψ => (hmmon ψ hψ).normalize_eq_self)).trans
      (Multiset.map_id _)
  have hnfF : UniqueFactorizationMonoid.normalizedFactors
        ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))) = m := by
    rw [hprodm]
    exact hnfm
  have hsqF : Squarefree ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))) := by
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hR0F, hnfF]
    exact hmnodup
  have hpatF : (UniqueFactorizationMonoid.normalizedFactors
        ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)))).map
      Polynomial.natDegree = lam.parts := by
    rw [hnfF]
    exact hmdeg
  -- ── assemble ──
  exact ⟨hunit, hsqF, hpatF⟩

end LeanUrat.OM.Order0
