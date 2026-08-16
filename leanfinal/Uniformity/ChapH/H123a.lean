/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H105
import Uniformity.ChapH.H114
import Uniformity.ChapH.H119
import Uniformity.Density.TypeOfInvariance

/-!
# Uniformity.ChapH.H123a — the recentring injection (H.123's first mandated split)

**Chapter H, NODE H.123, SPLIT a** (`blueprint/CHAP-H_general_induction.md` §17.3 — the T-1
completion layer, dated extension 2026-08-16; the blueprint's mandated three-way split
H.123a / H.123b / H.123c, *"H.123a (the recentring injection), H.123b (bridge-a per leaf shape),
H.123c (the count)"*).

**This file lands H.123a AND H.123c.  It does NOT land NODE H.123**, whose statement
(`undecidedCount_le_uCluster`) stays OPEN; see "## ⚠ What is NOT proved here" below, and the
committed obstruction record `H123_ROUTE_BLOCKED.lean.txt` beside this file.

* `recentreVec a w` — the coefficient vector of `(monicPoly a)(X + w)`;
* `recentreClass O m N w` — the induced map on level-`N` coefficient CLASSES, an involution up
  to sign (`recentreClass_recentreClass`), hence injective;
* `undecidedAt_recentreClass_iff` — the SEMANTIC undecidedness predicate is recentring
  invariant (through the landed `typeOf_shift`, HYP.05);
* `mem_map_maximalIdeal_of_stratum` — a class of the full-cluster level-0 stratum at the centre
  `z̄` recentres, at the pinned lift `resSect O z̄`, to a CLUSTER STATE (H.106's carrier);
* `card_undecided_stratum_le_card_undecidedClusterState` (H.123a + H.123c, UNCONDITIONAL) —
  the semantic undecided count of the stratum is at most the number of cluster states whose
  class is semantically undecided;
* `undecidedCount_le_uCluster_of_bridge` — H.123's target inequality, **with bridge-a carried
  as an explicit hypothesis**.

## ⚠ What is NOT proved here: bridge-a (H.123b) is OPEN, and H.123 with it

The composed statement `undecidedCount_le_uCluster_of_bridge` carries

```lean
(hbridge : ∀ c : ClusterState O m N, UndecidedAt O m N c.1 → ClusterUndecided O π m N c)
```

as a HYPOTHESIS.  That hypothesis is exactly NODE H.123's bridge-a in contrapositive form
(*reader-decided ⟹ `DecidedAt`*), and it is **not discharged anywhere in this corpus**.  This
file therefore records a CONDITIONALITY EDGE, in the same honesty shape as H.124's carried
`FullClusterRateBound` and B.61's carried `hBOX`: `BP.H.123a → (bridge-a, open)`.  Nothing here
may be read as a statement about `uCluster` bounding `undecidedCount` unconditionally.

Two independent obstructions were found while attempting bridge-a; both are recorded in
`H123_ROUTE_BLOCKED.lean.txt` (machine-checked where checkable):

1. **`B-BOX-1`, at `m ≥ 4`.** H.123's signed signature carries only `2 ≤ m` — no `m ≤ 3`.  The
   DEC leg of bridge-a (a state with no drain, no CS event and no child is semantically
   DECIDED) routes through B.63 `typeOf_of_separable_residuals`, whose `hperim` hypothesis at
   the order-1 key `φ = X` reads `(ℓ = 1 ∧ φ.natDegree = 1) ∨ ψ.natDegree = 1 ∨ B-BOX-1`.  A
   DEC cluster state at `m = 4` can carry a side of slope `u/ℓ = 1/2` whose residual polynomial
   is an irreducible QUADRATIC (block `ℓ · deg ψ = 4 ≤ m`), where both cheap disjuncts fail —
   e.g. `X ^ 4 + 2 X ^ 2 + 4` over `ℤ₂`, residual `y ^ 2 + y + 1`, type `(e, f) = (2, 2)`.  So
   the third disjunct is forced, and `B-BOX-1` is an UNSIGNED carried hypothesis
   (`ChapB/BBox1CiteStatement.lean`).  §17.0's supplier-gate table prices this exactly:
   *`B-BOX-1` (`ℓ ≥ 2 ∧ d ≥ 2` leaves) → return `BLOCKED: B-BOX-1`*.
2. **The β assembly.** Even below that corner, the α/β legs need `typeOf` of a parent cluster
   polynomial to be assembled from its children.  α is reachable (`alphaChild_spec` +
   `typeOf_shift` + `typeOf_scale`).  β is NOT: `betaChild_spec` exhibits the recentred frame as
   `C (π ^ D) * (monicPoly b * H')` with the COFACTOR `H'` uncontrolled — no landed lemma reads
   `typeOf H'`, and supplying one is the B.42/B.48 slope-and-residual dissection re-run against
   H.116's extraction (a chapter-B-scale piece of new mathematics, not a leaf).

## Why the recentring map is defined through a pinned lift

`recentreClass` is `proj ∘ recentreVec ∘ classSect` — the A-H.5 pinned class section composed
with the vector-level recentring.  The alternative (quantify over lifts) needs the
class-independence anyway, and that is `proj_recentreVec_congr`, an instance of H.109's
`pow_dvd_coeff_comp_sub` at the recentring `q = X + C w`: two lifts of one class produce
recentred polynomials whose coefficients agree mod `π ^ N`.  With the pinned form,
`proj_recentreVec` says the SAME class comes out of every lift, which is what both the
involution and the `DecidedAt` transport consume.

Note that the shift is by the pinned lift `resSect O z̄` of the centre.  Unlike H.115's α
extraction — where a centre shift by `d ∈ 𝔪` genuinely moves the child (the A-H.5 refutation) —
here NO divided digit is read, so any lift of `z̄` would do; the pinned choice is for
definiteness only.

DEPENDS: H.100 (`levelZeroStratum`, `proj_surjective'`), H.102 (`ext_of_monic_of_coeff_lt`),
H.105 (the N-1 transport chain, for `undecidedSet`/`UndecidedAt`), H.106 (`ClusterState`),
H.107 (`mem_maximalIdeal_pow_iff_dvd_of_irr`), H.109 (`pow_dvd_coeff_comp_sub`), H.115
(`resSect`, `classSect`, `residue_resSect`, `proj_classSect`), H.118 (`ClusterUndecided`),
H.119 (`uCluster`) · landed `typeOf_shift` (HYP.05), `monicPoly`, `proj`, `DecidedAt`,
`UndecidedAt`, `undecidedSet`.

**ENVIRONMENT — ENV-H17** (blueprint §17.0), every binder INLINE, plus
`[Finite (ResidueField O)]` on the counting declarations and `[IsAdicComplete (maximalIdeal O) O]`
+ `{O : Type}` on the two `uCluster`-facing ones (H.119's `uCluster` is declared at `Type`).

## Status

Sorry-free.  **Axiom footprint: Lean core only** (`propext`, `Classical.choice`, `Quot.sound`) —
printed at the end of the file.  B.42's `exists_slope_factorization` does NOT appear, because the
leg that would consume it (bridge-a) is precisely the leg this file does not prove.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. The recentred coefficient vector -/

section Vec

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **H.123a (def, vector level).** The coefficient vector of `(monicPoly a)(X + w)`: the
recentring of the lift `a` at the centre `w`, read back as a degree-`m` monic development. -/
noncomputable def recentreVec {m : ℕ} (a : Fin m → O) (w : O) : Fin m → O :=
  fun j => ((monicPoly a).comp (X + Polynomial.C w)).coeff (j : ℕ)

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The Taylor shift preserves `natDegree` — the landed `shift_natDegree` in `comp` phrasing. -/
theorem natDegree_comp_X_add_C (f : Polynomial O) (w : O) :
    (f.comp (X + Polynomial.C w)).natDegree = f.natDegree := by
  rw [← shift_apply, shift_natDegree]

omit [IsDiscreteValuationRing O] in
/-- **The development of the recentred vector IS the recentred polynomial.** Both sides are
monic of degree `m` and agree below `m` by construction. -/
theorem monicPoly_recentreVec {m : ℕ} (a : Fin m → O) (w : O) :
    monicPoly (recentreVec a w) = (monicPoly a).comp (X + Polynomial.C w) := by
  refine ext_of_monic_of_coeff_lt (monicPoly_monic _) ((monicPoly_monic a).comp_X_add_C w)
    (monicPoly_natDegree _) ?_ ?_
  · rw [natDegree_comp_X_add_C, monicPoly_natDegree]
  · intro i hi
    rw [monicPoly_coeff_lt _ hi]
    rfl

omit [IsDiscreteValuationRing O] in
/-- **The recentring is an involution up to sign**, at the vector level. -/
theorem recentreVec_recentreVec {m : ℕ} (a : Fin m → O) (w : O) :
    recentreVec (recentreVec a w) (-w) = a := by
  have hcomp : ((X + Polynomial.C w).comp (X + Polynomial.C (-w)) : Polynomial O) = X := by
    simp only [add_comp, X_comp, C_comp, map_neg]
    ring
  have h : monicPoly (recentreVec (recentreVec a w) (-w)) = monicPoly a := by
    rw [monicPoly_recentreVec, monicPoly_recentreVec, comp_assoc, hcomp, comp_X]
  funext j
  have hj := congrArg (fun p => Polynomial.coeff p (j : ℕ)) h
  simpa only [monicPoly_coeff_lt _ j.isLt, Fin.eta] using hj

/-- **Class-independence of the recentring** — H.109's `pow_dvd_coeff_comp_sub` at `q = X + C w`:
two lifts of one level-`N` class recentre to vectors in one level-`N` class. -/
theorem proj_recentreVec_congr {π : O} (hπ : Irreducible π) {m N : ℕ} {a a' : Fin m → O}
    (h : proj O m N a = proj O m N a') (w : O) :
    proj O m N (recentreVec a w) = proj O m N (recentreVec a' w) := by
  funext j
  refine Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).2 ?_)
  have hd := pow_dvd_coeff_comp_sub hπ h (X + Polynomial.C w) (j : ℕ)
  rwa [coeff_sub] at hd

end Vec

/-! ## 2. The recentring on classes -/

section Class

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **H.123a (def, class level).** The recentring of a level-`N` coefficient class at the centre
`w`, computed at the A-H.5 pinned lift `classSect`. -/
noncomputable def recentreClass (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m N : ℕ) (w : O) (c : Coeff O m N) : Coeff O m N :=
  proj O m N (recentreVec (classSect O m N c) w)

/-- **The def is lift-independent**: EVERY lift of `c` recentres into `recentreClass O m N w c`. -/
theorem proj_recentreVec {π : O} (hπ : Irreducible π) {m N : ℕ} {a : Fin m → O}
    {c : Coeff O m N} (ha : proj O m N a = c) (w : O) :
    proj O m N (recentreVec a w) = recentreClass O m N w c :=
  proj_recentreVec_congr hπ (ha.trans (proj_classSect O m N c).symm) w

/-- **The class recentring is an involution up to sign.** -/
theorem recentreClass_recentreClass {π : O} (hπ : Irreducible π) {m N : ℕ} (w : O)
    (c : Coeff O m N) :
    recentreClass O m N (-w) (recentreClass O m N w c) = c := by
  have h1 : proj O m N (recentreVec (classSect O m N c) w) = recentreClass O m N w c := rfl
  have h2 := proj_recentreVec hπ h1 (-w)
  rw [recentreVec_recentreVec, proj_classSect] at h2
  exact h2.symm

/-- **Hence it is injective** (indeed bijective, with inverse the recentring at `−w`). -/
theorem recentreClass_injective {π : O} (hπ : Irreducible π) {m N : ℕ} (w : O) :
    Function.Injective (recentreClass O m N w) := by
  intro c c' h
  have := congrArg (recentreClass O m N (-w)) h
  rwa [recentreClass_recentreClass hπ, recentreClass_recentreClass hπ] at this

/-- **Every lift of the recentred class is a recentred lift** — the surjectivity leg the
`DecidedAt` transport consumes. -/
theorem exists_lift_of_proj_recentreClass {π : O} (hπ : Irreducible π) {m N : ℕ}
    {c : Coeff O m N} (w : O) {b : Fin m → O} (hb : proj O m N b = recentreClass O m N w c) :
    proj O m N (recentreVec b (-w)) = c ∧ recentreVec (recentreVec b (-w)) w = b := by
  refine ⟨?_, ?_⟩
  · have h := proj_recentreVec hπ hb (-w)
    rwa [recentreClass_recentreClass hπ] at h
  · have h := recentreVec_recentreVec b (-w)
    rwa [neg_neg] at h

end Class

/-! ## 3. The semantic verdict is recentring invariant (HYP.05 at the class level) -/

section Semantic

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

omit [Finite (ResidueField O)] in
/-- **`DecidedAt` transports along the recentring.** Every lift of the recentred class is the
recentring of a lift of the original (`exists_lift_of_proj_recentreClass`), and `typeOf` is shift
invariant (HYP.05, `typeOf_shift`). -/
theorem decidedAt_recentreClass {π : O} (hπ : Irreducible π) {m N : ℕ}
    {σ : FactorizationType} {c : Coeff O m N} (w : O)
    (h : DecidedAt O m σ N c) : DecidedAt O m σ N (recentreClass O m N w c) := by
  intro b hb
  obtain ⟨ha, hbv⟩ := exists_lift_of_proj_recentreClass hπ w hb
  have hσ := h _ ha
  calc typeOf (monicPoly b)
      = typeOf (monicPoly (recentreVec (recentreVec b (-w)) w)) := by rw [hbv]
    _ = typeOf ((monicPoly (recentreVec b (-w))).comp (X + Polynomial.C w)) := by
        rw [monicPoly_recentreVec]
    _ = typeOf (monicPoly (recentreVec b (-w))) := typeOf_shift (monicPoly_monic _) w
    _ = σ := hσ

omit [Finite (ResidueField O)] in
/-- **`UndecidedAt` is recentring invariant.** -/
theorem undecidedAt_recentreClass_iff {π : O} (hπ : Irreducible π) {m N : ℕ}
    {c : Coeff O m N} (w : O) :
    UndecidedAt O m N (recentreClass O m N w c) ↔ UndecidedAt O m N c := by
  constructor
  · intro h σ hσ
    exact h σ (decidedAt_recentreClass hπ w hσ)
  · intro h σ hσ
    refine h σ ?_
    have := decidedAt_recentreClass hπ (-w) hσ
    rwa [recentreClass_recentreClass hπ] at this

end Semantic

/-! ## 4. The full-cluster stratum recentres into the cluster-state carrier -/

section Stratum

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **H.123a (the carrier leg).** A class of the level-0 stratum of `(X − z̄) ^ m` recentres, at
the pinned lift `resSect O z̄` of the centre, into H.106's cluster-state carrier: every
coordinate of the recentred class lies in the image ideal `𝔪 / 𝔪 ^ N`.

Reason: the reduction of the recentred lift is `((X − z̄) ^ m)(X + z̄) = X ^ m`, whose
coefficients below `m` all vanish. -/
theorem mem_map_maximalIdeal_of_stratum {m N : ℕ} (zbar : ResidueField O)
    {c : Coeff O m N} (hc : c ∈ levelZeroStratum O m N ((X - Polynomial.C zbar) ^ m))
    (i : Fin m) :
    recentreClass O m N (resSect O zbar) c i
      ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
  set a : Fin m → O := classSect O m N c with ha
  have hres : (monicPoly a).map (residue O) = (X - Polynomial.C zbar) ^ m :=
    hc a (proj_classSect O m N c)
  have hmapw : (X + Polynomial.C (resSect O zbar) : Polynomial O).map (residue O)
      = X + Polynomial.C zbar := by
    rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, residue_resSect]
  have hlin : ((X - Polynomial.C zbar).comp (X + Polynomial.C zbar) :
      Polynomial (ResidueField O)) = X := by
    simp only [sub_comp, X_comp, C_comp]
    ring
  have hzero : residue O (recentreVec a (resSect O zbar) i) = 0 := by
    have h1 : residue O (((monicPoly a).comp (X + Polynomial.C (resSect O zbar))).coeff (i : ℕ))
        = (((monicPoly a).comp (X + Polynomial.C (resSect O zbar))).map (residue O)).coeff
            (i : ℕ) := (Polynomial.coeff_map _ _).symm
    rw [recentreVec, h1, Polynomial.map_comp, hres, hmapw, Polynomial.pow_comp, hlin]
    rw [Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt i.isLt)]
  exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 hzero)

end Stratum

/-! ## 5. H.123a + H.123c — the counting reduction -/

section Count

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **H.123a + H.123c (UNCONDITIONAL).** The semantic undecided count of the full-cluster level-0
stratum at the centre `z̄` is at most the number of CLUSTER STATES whose class is semantically
undecided.  The map is the recentring at the pinned centre `resSect O z̄`; it lands in the
carrier by `mem_map_maximalIdeal_of_stratum`, preserves `UndecidedAt` by
`undecidedAt_recentreClass_iff`, and is injective by `recentreClass_injective`.

**This is NOT NODE H.123**: the right-hand side counts SEMANTICALLY undecided cluster states, not
H.118's CONSERVATIVE `ClusterUndecided` ones.  The step between the two is bridge-a (H.123b),
which is open — see the module docstring. -/
theorem card_undecided_stratum_le_card_undecidedClusterState {π : O} (hπ : Irreducible π)
    {m : ℕ} (N : ℕ) (zbar : ResidueField O) :
    Nat.card
        ((undecidedSet O m N ∩
          levelZeroStratum O m N ((X - Polynomial.C zbar) ^ m) : Set (Coeff O m N)))
      ≤ Nat.card {c : ClusterState O m N // UndecidedAt O m N c.1} := by
  classical
  refine Nat.card_le_card_of_injective
    (fun c => (⟨⟨recentreClass O m N (resSect O zbar) c.1,
        fun i => mem_map_maximalIdeal_of_stratum zbar c.2.2 i⟩,
      (undecidedAt_recentreClass_iff hπ (resSect O zbar)).2 c.2.1⟩ :
        {d : ClusterState O m N // UndecidedAt O m N d.1})) ?_
  intro c c' h
  have h1 : recentreClass O m N (resSect O zbar) c.1
      = recentreClass O m N (resSect O zbar) c'.1 := congrArg (fun d => d.1.1) h
  exact Subtype.ext (recentreClass_injective hπ (resSect O zbar) h1)

end Count

/-! ## 6. The composed reduction — bridge-a CARRIED, never claimed -/

section Composed

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **The conservative comparison, given bridge-a.** `uCluster` counts the states H.118's
CONSERVATIVE reader leaves undecided; the semantically undecided states inject into them exactly
when bridge-a holds. -/
theorem card_undecidedClusterState_le_uCluster {π : O} {m N : ℕ}
    (hbridge : ∀ c : ClusterState O m N, UndecidedAt O m N c.1 → ClusterUndecided O π m N c) :
    Nat.card {c : ClusterState O m N // UndecidedAt O m N c.1} ≤ uCluster O π m N :=
  Nat.card_le_card_of_injective
    (fun c => (⟨c.1, hbridge c.1 c.2⟩ :
      {d : ClusterState O m N // ClusterUndecided O π m N d}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun d : {e : ClusterState O m N // ClusterUndecided O π m N e} => (d : ClusterState O m N))
      h))

set_option linter.unusedVariables false in
/-- **H.123's target inequality, WITH BRIDGE-A CARRIED.**

⚠ **This is NOT NODE H.123.** `hbridge` is H.123's bridge-a in contrapositive form and it is
UNPROVED in this corpus (obstructions: `B-BOX-1` at `m ≥ 4`, and the β cofactor — see the module
docstring and `H123_ROUTE_BLOCKED.lean.txt`).  The declaration records the conditionality edge
and pins the remaining obligation to a single statement; it must never be cited as the bridge. -/
theorem undecidedCount_le_uCluster_of_bridge {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm : 2 ≤ m) (N : ℕ) (hN : 1 ≤ N) (zbar : ResidueField O)
    (hbridge : ∀ c : ClusterState O m N, UndecidedAt O m N c.1 → ClusterUndecided O π m N c) :
    Nat.card
        ((undecidedSet O m N ∩
          levelZeroStratum O m N ((X - Polynomial.C zbar) ^ m) : Set (Coeff O m N)))
      ≤ uCluster O π m N :=
  le_trans (card_undecided_stratum_le_card_undecidedClusterState hπ N zbar)
    (card_undecidedClusterState_le_uCluster hbridge)

end Composed

end Uniformity.Density.Induction

/-! ## Axiom footprint

Lean core only.  In particular `Uniformity.Density.Leaf.exists_slope_factorization` (B.42) is
ABSENT: the leg that consumes it — bridge-a — is the leg this file leaves open.  A future H.123b
WILL show it, by design (§17.0's supplier-gate row for B.42). -/

section AxCheck
#print axioms Uniformity.Density.Induction.monicPoly_recentreVec
#print axioms Uniformity.Density.Induction.recentreClass_injective
#print axioms Uniformity.Density.Induction.undecidedAt_recentreClass_iff
#print axioms Uniformity.Density.Induction.mem_map_maximalIdeal_of_stratum
#print axioms Uniformity.Density.Induction.card_undecided_stratum_le_card_undecidedClusterState
#print axioms Uniformity.Density.Induction.undecidedCount_le_uCluster_of_bridge
end AxCheck
