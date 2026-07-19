# De-stub blueprint: making `classifyAux` genuinely read `f` below the root (P1)

**Target:** `/workspace-vast/asving/forum-sigma/lean_urat/LeanUrat/OM/Classifier.lean`
**Revert point:** `69ad97a` (builds #48–#56). `git checkout -- <file>` to undo.
**Discipline:** ADDITIVE first (build the genuine classifier alongside the stub, master stays GREEN);
the SWAP (rip out the stub, break CERTLEVEL, re-prove) is LAST and NOT done this run.

---

## 0. The stub, precisely

`classify N f := classifyAux p N n n f (rootCtx p N f) …` (Classifier.lean:621).

- **Root IS f-dependent** (DECISION 1, #already-landed): `rootCtx = fRootCtx` for `0 < N`, whose
  `Rr := rootResidual p N hN f` genuinely factors `f`'s order-0 Newton-polygon residual (:214).
- **Below the root it is f-BLIND** (the stub): `classifyAux` (:417) recurses through
  `childCtxOfSize (T.order + 1) ch.childSize` (:264), an `M5.OMType` with `Rr := 0`. Since
  `M5.cells` of an `Rr = 0` context is `[]` (empty factorization), every child instantly bottoms out
  as a childless leaf. So the classifier's descent structure is truncated at depth 1: it reads `f`'s
  order-0 residual, then serializes a shape whose child subtrees are constant (size-slot only, no
  further residual content).
- **`classifyAux_indep := rfl`** (:758–761): because `omStep p N n f T = M5.cells T` discards `_f`,
  and the recursion's child context `childCtxOfSize (T.order+1) ch.childSize` reads only the bound
  `T`, the ENTIRE output of `classifyAux` is a function of `(n, budget, Tctx)` alone — `(N, f)`
  independent, provable by `rfl`. This defeq is the load-bearing shortcut for the whole CERTLEVEL
  cylinder.

## 1. What `classifyAux_indep := rfl` buys, and exactly what breaks when the stub is removed

`classifyAux_indep` is consumed by:

- **`classifyAux_congr_ctx`** (:765) — `subst` the ctx equality, then `classifyAux_indep`. This is the
  bridge that lets one prove "equal contexts ⟹ equal classifications across different `(N,f)`".
- **`oneDigitCylinder_fkeyed`** (:1123) — the one-digit shape cylinder
  `classify (N+1) g = classify N (boxReduce g)` for `g` in the bulk. Its proof is:
  `unfold classify; exact classifyAux_congr_ctx … (rootCtx_reduce_stable_R …).symm …`.
  i.e. it reduces the WHOLE cylinder to **root-context stability** `rootCtx_reduce_stable_R` (:1109)
  PLUS the defeq `classifyAux_indep`. The genuine recursion below the root never needs a stability
  argument *because the stub makes it f-independent*.
- **`oneDigit_to_LE_fkeyed`** (:1253) — telescopes the one-digit cylinder to
  `ClassifyReductionStableFKeyed` by gap-induction (`disc_reduce_bulk_mono` carries the bulk condition
  down each level; `boxReduceLE_boxReduce` tower-commutes).
- **`certLevel_stabilizes` / `classify_reductionStable`** (:1433/:1440) — `:= oneDigit_to_LE_fkeyed`.

**The CERTLEVEL cylinder consumed downstream** (the Layer D–E product): `certLevel_stabilizes` /
`classify_reductionStable : ClassifyReductionStableFKeyed p n (classify p n)`, consumed by
CountingModel / LimitGlue / LevelNCount / RealInstance (via F1.L9 → `M8.constantFiber`'s `∃ r`, and
F4.L-TOP2 → `h_env`). Also `classify_singleValued` (:1402, a `rfl` placeholder), `treeSize_classify`
(:1339), `decode_classify_section` (:1348), `classify_separable_leaf` (:1464).

### So the SWAP breaks (in dependency order):

1. **`classifyAux_indep := rfl`** — FALSE the moment `classifyAux` reads `f` below the root
   (the child ctx becomes `fChildCtx … f …`, whose `Rr := childResidual … f …` genuinely depends on
   `f`). The `rfl` proof dies; the *statement itself* becomes false as written (two different `f, f'`
   at the same context can give different subtrees). It must be **replaced** by a genuine
   `(N,f)`-dependent reduction-stability lemma, NOT a re-proof of the same statement.
2. **`classifyAux_congr_ctx`** — its `classifyAux_indep` call dies. Equal *contexts* no longer suffice;
   one needs equal *contexts AND `boxReduce`-related `f`s* (the child residual channel must also be
   shown stable). Re-proof: strengthen to carry a per-level residual-stability hypothesis.
3. **`oneDigitCylinder_fkeyed`** — the `classifyAux_congr_ctx` shortcut dies. The cylinder can no
   longer be reduced to root-context stability alone: EVERY descent level now reads `f`, so each level
   needs its own reduce-stability. Re-proof: a genuine induction on the OM tree, threading
   `childResidual_reduce_stable` (#55, :344) at each descent level, in place of the single
   `rootCtx_reduce_stable_R + defeq` step.
4. **`oneDigit_to_LE_fkeyed`, `certLevel_stabilizes`, `classify_reductionStable`** — mechanically
   survive IF (3) is re-proved with the same *statement* (they only cite `oneDigitCylinder_fkeyed`).
   So the whole downstream CERTLEVEL contract is preserved **provided the one-digit cylinder is
   re-established** with a genuine per-level argument.
5. **`classify_separable_leaf`** (:1464) — currently proved via the `decode` degeneracy (`decode` sets
   `Rr := 0`, so `omStep (decode …) = []`). This is INDEPENDENT of the `classifyAux` stub (it routes
   through `decode`, not `classifyAux`), so the swap of `childCtxOfSize` does NOT break it — but the
   companion `decode` de-stub (a SEPARATE obligation) would; flagged, out of scope here.

### The genuine re-proof plan for the one-digit cylinder (post-swap)

- **Ingredient A (banked, #55):** `childResidual_reduce_stable` (:344) — the order-1 child residual is
  stable under one-digit `boxReduce` below the per-digit cutoff. This is the per-level analogue of
  `rootResidual_reduce_stable_R`. It is the reusable seed.
- **Ingredient B (to prove):** `fChildCtx_reduce_stable` — the child CONTEXT agrees across one-digit
  reduction (from Ingredient A + the `dr := Rr.natDegree` motive `simp only`, exactly as
  `fRootCtx_reduce_stable_R` at :1096).
- **Ingredient C (to prove):** a **genuine recursion-stability** lemma
  `classifyGenuine_reduce_stable` by well-founded induction on `budget`: at each node the cells agree
  (root/parent residual channel stable), and each descent child recurses on a strictly-smaller budget
  with a `boxReduce`-related `f` whose child context is stable by Ingredient B — so the emitted
  subtrees agree by the IH. The bulk/cutoff hypotheses accumulate per level (this is the genuinely new
  content the stub elided; the paper's finite-depth tame termination `B(n,p)` bounds the depth).
- **Ingredient D (statement-preserving glue):** `oneDigitCylinder_genuine` with the SAME signature as
  `oneDigitCylinder_fkeyed`, proved from C instead of `classifyAux_congr_ctx`. Then
  `oneDigit_to_LE_fkeyed` and everything above it are UNCHANGED (they cite the cylinder by name).

The residue-field obstruction (why this is hard and staged): `ch.P : T.Fr[X]`, and `OMType.Fr` is an
opaque `Type`. `ch.P` is liftable to `(ZMod p)[X]` only when `T.Fr = ZMod p`, which holds
**definitionally at every `fRootCtx`/`fChildCtx` context** (both set `Fr := ZMod p`) but NOT for a
generic `T` in the abstract `classifyAux` recursion. So the genuine multi-level classifier must
descend **exclusively through `Fr = ZMod p` contexts** (the tame/unramified `deg ψ = 1` tower); the
general residue-field-extension case (`deg ψ > 1`, `Fr` a genuine extension) is a residue-field
representation redesign deliberately deferred. This matches the tame stratum where P2 drainage lives.

---

## 2. Phasing

### ADDITIVE phases (master stays GREEN; build the genuine classifier BESIDE the stub)

- **A0 (banked #54/#55):** `childResidual` (:295), `fChildCtx` (:368), `classifyFirstDescent` (:635),
  `childResidual_reduce_stable` (:344), `cells_fChildCtx_ne_nil` (:652). The root is f-dependent; the
  FIRST descent reads `f`.
- **A1 (THIS RUN):** a genuine **multi-level** recursive classifier `classifyGenuine` that reads `f`
  at *every* level (not just the first), by well-founded recursion on `budget`, descending through
  `fChildCtx` contexts (all `Fr = ZMod p`). Prove its non-vacuity (produces genuine non-empty cells
  from `f`, contrasting the stub's always-`[]` children) and the tractable menu-correctness (its root
  tuple / size / cell payload). All additive: `classify`/`classifyAux` untouched → master GREEN.
- **A2 (next):** `fChildCtx_reduce_stable` (Ingredient B) + as much of `classifyGenuine_reduce_stable`
  (Ingredient C) as the tame single-slope tower allows, still additive.
- **A3 (next):** `oneDigitCylinder_genuine` (Ingredient D) — statement-identical to
  `oneDigitCylinder_fkeyed`, proved from C. Still additive: two cylinders coexist.

### SWAP phase (LAST — breaks CERTLEVEL — NOT this run)

- **S1:** point `classifyAux` (or a new `classify`) at `classifyGenuine`; delete `childCtxOfSize`.
- **S2:** delete `classifyAux_indep := rfl` (now false); repoint `oneDigitCylinder_fkeyed` at
  `oneDigitCylinder_genuine`. `certLevel_stabilizes` et al. survive by name.
- **S3:** re-verify CountingModel / LimitGlue / LevelNCount / RealInstance against the repointed
  `classify`; re-check `classify_separable_leaf` (its `decode` route is independent, should survive).
- Footprint guard the whole way: `⊆ [propext, Classical.choice, Quot.sound]`.

---

## 3. This-run increment (A1) — exact plan

Add, alongside the stub, a well-founded genuine classifier keyed on a **`Fr = ZMod p` context**:

```
classifyGenuineAux (budget) (f) (T : OMType) (hFr : T.Fr = ZMod p) (hT : clusterSize T = budget)
  = ⟨(T.order, clusterSize T, T.dr) ::
       (M5.cells T).flatMap (fun c => c.children.flatMap (fun ch =>
          -- ch.P : T.Fr[X] ≃ (ZMod p)[X] via hFr; lift + develop f to get the child residual
          (classifyGenuineAux ch.childSize f
             (fChildCtx p N f (T.order+1) ch.childSize (hFr ▸ ch.P) ch.μ) rfl (clusterSize_fChildCtx …)
          ).tree)),
     M5.encodeCells T⟩
```

recursing via `Nat.strongRecOn budget`, strict descent by `ch.hChildSizeLt : ch.childSize < clusterSize T = budget`.
`fChildCtx.Fr = ZMod p` by construction (:370), so `hFr := rfl` propagates down every level — the
recursion never leaves the tame `Fr = ZMod p` tower. `classifyGenuine N f := classifyGenuineAux n f
(fRootCtx …) rfl …` (root `Fr = ZMod p` too).

**Non-vacuity (machine-checked):** `cells_fChildCtx_ne_nil` (:652) already proves the child context
has non-empty cells when `childResidual` has positive degree ≤ budget. Lift it to: when the root has a
descent child whose developed residual has positive degree, `classifyGenuine`'s emitted subtree at
that child is NOT a bare size-tuple leaf — its `tree` carries the child's own cells' children. This is
the exact contrast with `classifyAux` (whose child subtree is always the constant `childCtxOfSize`
shell). Report the footprint of the non-vacuity witness.

**Menu-correctness (tractable slice):** `treeSize (classifyGenuine N f) = n` (root size slot), and the
root tuple / `encodeCells` payload match `classify`'s root (so the genuine and stub classifiers agree
at the ROOT, diverging only in the descent subtrees — the precise statement of "genuine below root").
