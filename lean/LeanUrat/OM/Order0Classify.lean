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
# Order0Classify — γ5, the forward face equality (`HNODE0_BLUEPRINT` §5)

**The target.** On the generic separable stratum (`hunit` : the constant coefficient is a unit,
`hsq` : the mod-`p` reduction `f̄` is squarefree, `hpat` : the factor-degree multiset of `f̄` is
`lam.parts`), the genuine classifier emits EXACTLY the menu literal:
`B.classify p n N f = sepShape n lam` (`classify_eq_sepShape`).

The proof pieces, each banked separately:
* `classifyAux_unfold` — ONE-STEP unfold of the `Nat.strongRecOn` budget recursion
  (`Nat.strongRecOn_eq`, batteries), folding the recursive occurrences back into `classifyAux`.
* `classifyAux_congr_ctx` — context-congruence across the proof-carrying `hT` argument
  (dispatches `rootCtx = fRootCtx` through the `dif_pos hN` branch).
* `classifyAux_of_childless` — childless cells collapse the children `flatMap` to `[]`: the
  emitted shape is `⟨[(order, cs, dr)], encodeCells T⟩`.
* `factors_degreeList_eq_sort` — THE ℕ-list identity: the degree list of the A5
  degree-`mergeSort`ed factor list equals `lam.parts.sort (· ≤ ·)` (both ≤-sorted, same multiset
  via γ4's `degrees_multiset` + `hpat`; `List.Perm.eq_of_pairwise'` closes).
* `encodeCells_of_squarefree` — the payload equality: with all multiplicities 1 the emitted
  payload is one childless `⟨deg ψ, δ, Nr, []⟩` per sorted factor.
* `zmodValuation_zero_iff_castHom_ne_zero` — the α-package bridge: `hunit` at level `N` ⟺ the
  mod-`p` reduction of the constant coefficient is nonzero.

Everything here is on Lean core (no new axioms): the banked γ2/γ3 (`Order0Root`) and γ4
(`Order0Fact`) nodes supply the residual identification and the factorization facts.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.OM.Order0

open Polynomial

open scoped Classical

/-! ## 0. The α-package helper: `hunit` reads on the mod-`p` reduction -/

/-- **Level-`N` unit-ness ⟺ nonzero mod-`p` reduction** (the α-package bridge,
`HNODE0_BLUEPRINT` §5 "α"). For `0 < N` and `x : ZMod (p^N)`:
`zmodValuation p N x = 0 ↔ castHom x ≠ 0`. Forward: `x ≠ 0` (a zero has valuation `N > 0`), so
the guarded datum of `valuation_ite_eq_castHom` is the unit residue, nonzero
(`zmodUnitResidue_ne_zero`). Backward: valuation `≠ 0` puts `valuation_ite_eq_castHom` in its
`0` branch, i.e. `castHom x = 0`. -/
theorem zmodValuation_zero_iff_castHom_ne_zero (p : ℕ) [Fact p.Prime] (N : ℕ) (hN : 0 < N)
    (x : ZMod (p ^ N)) :
    PadicLift.zmodValuation p N x = 0
      ↔ ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p) x ≠ 0 := by
  have key := valuation_ite_eq_castHom p N hN x
  constructor
  · intro h0
    have hx : x ≠ 0 := by
      intro hx0
      rw [hx0, PadicLift.zmodValuation_zero] at h0
      omega
    rw [if_pos (by exact_mod_cast h0)] at key
    rw [← key]
    exact PadicLift.zmodUnitResidue_ne_zero p hx
  · intro hne
    by_contra h0
    rw [if_neg (by exact_mod_cast h0)] at key
    exact hne key.symm

/-! ## 1. One-step unfold of the budget recursion -/

/-- **One-step unfold of `classifyAux`** (`HNODE0_BLUEPRINT` §5 γ5, bullet 1). `classifyAux` IS
`Nat.strongRecOn budget ind Tctx hT`; `Nat.strongRecOn_eq` (batteries) exposes one step and the
recursive occurrences fold back into `classifyAux` definitionally. -/
theorem classifyAux_unfold (p : ℕ) [Fact p.Prime] (N n budget : ℕ)
    (f : QuotientBox.monicBox p N n) (T : M5.OMType) (hT : M5.clusterSize T = budget) :
    B.classifyAux p N n budget f T hT
      = ⟨(T.order, M5.clusterSize T, T.dr) ::
          (B.omStep p N n f T).flatMap (fun c =>
            c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
              (B.classifyAux p N n ch.childSize f
                (B.childCtxOfSize (T.order + 1) ch.childSize) rfl).tree)),
        M5.encodeCells T⟩ := by
  have h := Nat.strongRecOn_eq
    (motive := fun b => ∀ (T : M5.OMType), M5.clusterSize T = b → ClusterShape)
    (fun b ih => fun (T : M5.OMType) (hTb : M5.clusterSize T = b) =>
      (⟨(T.order, M5.clusterSize T, T.dr) ::
        (B.omStep p N n f T).flatMap (fun c =>
          c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
            have hlt : ch.childSize < b := hTb ▸ ch.hChildSizeLt
            (ih ch.childSize hlt (B.childCtxOfSize (T.order + 1) ch.childSize) rfl).tree)),
        M5.encodeCells T⟩ : ClusterShape))
    budget
  exact congrFun (congrFun h T) hT

/-- **Context congruence for `classifyAux`** across the proof-carrying budget argument: equal
contexts give equal shapes (the `hT` slots are proofs of the same Prop after `subst`). Dispatches
`rootCtx = fRootCtx` (`dif_pos`) into `classify` without a dependent-motive fight. -/
theorem classifyAux_congr_ctx (p : ℕ) [Fact p.Prime] (N n budget : ℕ)
    (f : QuotientBox.monicBox p N n) {T₁ T₂ : M5.OMType} (h : T₁ = T₂)
    (hT₁ : M5.clusterSize T₁ = budget) (hT₂ : M5.clusterSize T₂ = budget) :
    B.classifyAux p N n budget f T₁ hT₁ = B.classifyAux p N n budget f T₂ hT₂ := by
  subst h
  rfl

/-- **Childless collapse** (`HNODE0_BLUEPRINT` §5 γ5, bullet 3). When every cell of `T` is
childless, the children `flatMap` of the one-step unfold is `[]` and `classifyAux` emits exactly
`⟨[(order, clusterSize, dr)], encodeCells T⟩`. -/
theorem classifyAux_of_childless (p : ℕ) [Fact p.Prime] (N n budget : ℕ)
    (f : QuotientBox.monicBox p N n) (T : M5.OMType) (hT : M5.clusterSize T = budget)
    (hchild : ∀ c ∈ M5.cells T, c.children = []) :
    B.classifyAux p N n budget f T hT
      = ⟨[(T.order, M5.clusterSize T, T.dr)], M5.encodeCells T⟩ := by
  rw [classifyAux_unfold]
  have hnil : (B.omStep p N n f T).flatMap (fun c =>
      c.children.flatMap (fun (ch : M5.OMCell.Child T) =>
        (B.classifyAux p N n ch.childSize f
          (B.childCtxOfSize (T.order + 1) ch.childSize) rfl).tree)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro c hc
    rw [hchild c hc]
    rfl
  rw [hnil]

/-! ## 2. The payload: the sorted factor-degree list is the sorted partition -/

section Payload

variable {kS : Type*} [Field kS] [Finite kS]

/-- **The ℕ-list identity** (`HNODE0_BLUEPRINT` §5 γ5, bullet 5). The degree list of the A5
degree-`mergeSort`ed factor list of `R` with factor-degree multiset `lam.parts` is EXACTLY
`lam.parts.sort (· ≤ ·)`: both are `≤`-sorted (`List.pairwise_mergeSort` through the key /
`Multiset.pairwise_sort`) with the same multiset (`mergeSort_perm` + attach/toList plumbing +
`hfac` / `Multiset.sort_eq`), so `List.Perm.eq_of_pairwise'` closes. (Stated on the factor
`Finset` itself — no `normalizedFactors`, hence no `NormalizationMonoid` instance flavor to
match at the `ZMod p`/`T.Fr` boundary.) -/
theorem factors_degreeList_eq_sort {n : ℕ} (R : kS[X])
    (F : M4.ResidualFactorization R) (lam : Nat.Partition n)
    (hfac : F.factors.val.map Polynomial.natDegree = lam.parts) :
    ((F.factors.attach.toList.mergeSort
        (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map (fun a => a.1.natDegree))
      = lam.parts.sort (· ≤ ·) := by
  -- LHS is `≤`-sorted: `mergeSort` sortedness for the Bool key comparator, mapped through the key
  have hpairB := List.pairwise_mergeSort
    (le := fun a b : {x // x ∈ F.factors} => decide (a.1.natDegree ≤ b.1.natDegree))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      omega)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega)
    F.factors.attach.toList
  have hpair₁ : ((F.factors.attach.toList.mergeSort
      (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
        (fun a => a.1.natDegree)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hpairB.imp (fun h => of_decide_eq_true h)
  -- RHS is `≤`-sorted
  have hpair₂ : (lam.parts.sort (· ≤ ·)).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  -- same multiset
  have hcoe : (((F.factors.attach.toList.mergeSort
        (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
          (fun a => a.1.natDegree) : List ℕ) : Multiset ℕ)
      = ((lam.parts.sort (· ≤ ·) : List ℕ) : Multiset ℕ) := by
    rw [Multiset.sort_eq]
    calc (((F.factors.attach.toList.mergeSort
          (fun a b => decide (a.1.natDegree ≤ b.1.natDegree))).map
            (fun a => a.1.natDegree) : List ℕ) : Multiset ℕ)
        = ((F.factors.attach.toList.map (fun a => a.1.natDegree) : List ℕ) : Multiset ℕ) :=
          Multiset.coe_eq_coe.mpr ((List.mergeSort_perm F.factors.attach.toList _).map _)
      _ = Multiset.map (fun (a : {x // x ∈ F.factors}) => a.1.natDegree)
            ((F.factors.attach.toList : List {x // x ∈ F.factors}) : Multiset _) :=
          (Multiset.map_coe _ _).symm
      _ = Multiset.map (fun (a : {x // x ∈ F.factors}) => a.1.natDegree) F.factors.attach.val :=
          congrArg (Multiset.map (fun (a : {x // x ∈ F.factors}) => a.1.natDegree))
            (Finset.coe_toList _)
      _ = F.factors.val.map Polynomial.natDegree :=
          Multiset.attach_map_val' F.factors.val Polynomial.natDegree
      _ = lam.parts := hfac
  exact List.Perm.eq_of_pairwise' hpair₁ hpair₂ (Multiset.coe_eq_coe.mp hcoe)

end Payload

/-- **The payload equality** (`HNODE0_BLUEPRINT` §5 γ5, bullet 5 assembled). For squarefree monic
`T.Rr` with factor-degree pattern `lam`, the emitted per-node payload is one CHILDLESS cell
`⟨d, T.δ, T.Nr, []⟩` per sorted part `d` of `lam`: multiplicity 1 kills the descent `dite`
(`mult_eq_one_of_squarefree`), and the sorted factor-degree list is `lam.parts.sort (· ≤ ·)`
(`factors_degreeList_eq_sort`). -/
theorem encodeCells_of_squarefree {n : ℕ} (T : M5.OMType)
    (hsq : Squarefree T.Rr) (lam : Nat.Partition n)
    (hfac : (Classical.choice (M4.factorize_any T.Rr)).factors.val.map Polynomial.natDegree
      = lam.parts) :
    M5.encodeCells T
      = (lam.parts.sort (· ≤ ·)).map (fun d => (⟨d, T.δ, T.Nr, []⟩ : ShapeCell)) := by
  have hdeg := factors_degreeList_eq_sort T.Rr
    (Classical.choice (M4.factorize_any T.Rr)) lam hfac
  rw [M5.encodeCells, M5.cells, List.map_map, ← hdeg, List.map_map]
  apply List.map_congr_left
  rintro ⟨ψ, hψ⟩ hmem
  have h1 : (Classical.choice (M4.factorize_any T.Rr)).mult ψ = 1 :=
    mult_eq_one_of_squarefree T.Rr hsq _ ψ hψ
  simp only [Function.comp_apply, h1]
  rw [dif_neg (by omega : ¬(2 ≤ 1))]
  rfl

/-! ## 3. γ5 — the forward face equality -/

/-- **γ5 (forward): `classify_eq_sepShape`** (`HNODE0_BLUEPRINT` §5). On the generic separable
stratum — unit constant coefficient (`hunit`), squarefree reduction `f̄` (`hsq`) with
factor-degree pattern `lam` (`hpat`) — the genuine classifier emits EXACTLY the menu literal:
`B.classify p n N f = sepShape n lam`.

Chain: `classify` dispatches to `classifyAux` at `fRootCtx` (`dif_pos hN` via
`classifyAux_congr_ctx`); γ3 identifies `Rr = f̄`, so every cell is childless
(`cells_childless_of_squarefree`) and the one-step unfold collapses
(`classifyAux_of_childless`) to `⟨[(0, n, dr)], encodeCells⟩`; the tree head is `(0, n, n)`
(`fRootCtx_dr`) and the payload is the sorted one-cell-per-part list
(`encodeCells_of_squarefree` + `fRootCtx_Nr`, `δ = 1` definitionally). -/
theorem classify_eq_sepShape (p : ℕ) [Fact p.Prime] (n N : ℕ) (hN : 0 < N) (hn : 0 < n)
    (f : QuotientBox.monicBox p N n)
    (hunit : PadicLift.zmodValuation p N ((f.1).coeff 0) = 0)
    (hsq : Squarefree ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))))
    (lam : Nat.Partition n)
    (hpat : (UniqueFactorizationMonoid.normalizedFactors
        ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)))).map Polynomial.natDegree
      = lam.parts) :
    B.classify p n N f = sepShape n lam := by
  -- γ3 transports the stratum hypotheses onto the root context's residual
  have hRr : (B.fRootCtx p N hN f).Rr
      = (f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) :=
    fRootCtx_Rr p n N hN hn f hunit
  have hsqT : Squarefree (B.fRootCtx p N hN f).Rr := by
    rw [hRr]; exact hsq
  have hmonT : ((B.fRootCtx p N hN f).Rr).Monic := by
    rw [hRr]; exact (f.2.1).map _
  have hR0T : (B.fRootCtx p N hN f).Rr ≠ 0 := hmonT.ne_zero
  -- the ZMod-flavored factorization of f̄ and the factor-set bridge (the classifier's internal
  -- `Classical.choice (M4.factorize_any T.Rr)` carries `T.Fr`-flavored instances; the stratum
  -- hypothesis `hpat` carries `ZMod p`-flavored ones — `mem_factors_iff` characterizes both
  -- factor Finsets instance-independently, so `Finset.ext` bridges them)
  have hmonZ : ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))).Monic :=
    (f.2.1).map _
  have hR0Z : ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))) ≠ 0 := hmonZ.ne_zero
  set FZ := Classical.choice (M4.factorize_any (kS := ZMod p)
    ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)))) with hFZ
  have hbridge : (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors
      = FZ.factors := by
    apply Finset.ext
    intro ψ
    rw [mem_factors_iff ((B.fRootCtx p N hN f).Rr) hR0T
      (Classical.choice (M4.factorize_any (B.fRootCtx p N hN f).Rr)) ψ, hRr]
    exact (mem_factors_iff _ hR0Z FZ ψ).symm
  -- the two `DecidableEq (ZMod p)` flavors baked into `normalizedFactors` agree (subsingleton)
  have hDE : (fun a b => Classical.propDecidable (a = b) : DecidableEq (ZMod p))
      = ZMod.decidableEq p := by
    funext a b
    exact Subsingleton.elim _ _
  have hZ : FZ.factors.val.map Polynomial.natDegree = lam.parts := by
    refine (degrees_multiset ((f.1).map (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)))
      hmonZ hsq FZ).trans ?_
    -- `degrees_multiset` (compiled under `open scoped Classical` with no `DecidableEq kS` in
    -- scope) bakes `fun a b => Classical.propDecidable (a = b)` into its `normalizedFactors`;
    -- `hpat` (elaborated at `ZMod p`) carries `ZMod.decidableEq p`. The two are NOT defeq
    -- (`Classical.choice` is opaque), so align them with the subsingleton rewrite `hDE` first.
    rw [hDE]
    exact hpat
  have hfacT : (Classical.choice
      (M4.factorize_any (B.fRootCtx p N hN f).Rr)).factors.val.map Polynomial.natDegree
      = lam.parts := by
    rw [hbridge]
    exact hZ
  -- dispatch `classify` to `classifyAux` at the `fRootCtx` branch
  have hdisp : B.classify p n N f
      = B.classifyAux p N n n f (B.fRootCtx p N hN f) (B.clusterSize_fRootCtx p N hN f) :=
    classifyAux_congr_ctx p N n n f (dif_pos hN)
      (B.clusterSize_rootCtx p N f) (B.clusterSize_fRootCtx p N hN f)
  rw [hdisp, classifyAux_of_childless p N n n f (B.fRootCtx p N hN f)
      (B.clusterSize_fRootCtx p N hN f)
      (cells_childless_of_squarefree (B.fRootCtx p N hN f) hsqT hmonT.ne_zero)]
  -- tree head `(0, n, n)`
  have htree : [((B.fRootCtx p N hN f).order,
      M5.clusterSize (B.fRootCtx p N hN f), (B.fRootCtx p N hN f).dr)]
      = [((0 : ℕ), n, n)] := by
    rw [fRootCtx_dr p n N hN hn f hunit]
    rfl
  -- payload: one childless flat-face cell per sorted part
  have hNr : (B.fRootCtx p N hN f).Nr = flatFace n := fRootCtx_Nr p n N hN hn f hunit
  have hδ : (B.fRootCtx p N hN f).δ = 1 := rfl
  have hcells : M5.encodeCells (B.fRootCtx p N hN f)
      = (lam.parts.sort (· ≤ ·)).map (fun d => (⟨d, 1, flatFace n, []⟩ : ShapeCell)) := by
    rw [encodeCells_of_squarefree (B.fRootCtx p N hN f) hsqT lam hfacT, hNr, hδ]
  rw [htree, hcells]
  rfl

end LeanUrat.OM.Order0
