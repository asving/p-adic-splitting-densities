# UNIT UDR — VERDICT: THE CAPSTONE'S a2 FIELD REDUCED TO THE PRIMARY DEEP-COLLISION TAIL — `drainageAt_all_of_deepTailDrain : (∀ m ≥ 4, DeepTailDrainAt m) → ∀ n, DrainageAt n`, LEAN-CORE, with the tail machine-confined to the single-cluster (ψ^k, k ≥ 2) locus (2026-08-30)

**Status: DONE — honest conditional of maximal strength; `UndecidedDrainAt n` at n ≥ 4
did NOT close unconditionally (the surviving core is exactly the cluster locus, as the
frontier predicted); everything reachable by the landed engine is landed.**

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG46.lean` (~910 lines, ZERO sorries, zero
warnings; TEN AxCheck footer lines, ALL pure Lean core `{propext, Classical.choice,
Quot.sound}` — no cite is consumed anywhere in this file).  One-line aggregator import
added to `Uniformity/ChapI.lean` (between IFCG45 and IFCG47; neither touched otherwise).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG46.lean`
(final: zero diagnostics), targeted `lake build Uniformity.ChapI.IFCG46` green (8958
jobs), aggregator `lake env lean Uniformity/ChapI.lean` green.  NO git operations.

## ★★★ THE HEADLINE

    def  DeepTailDrainAt (n : ℕ) : Prop :=          -- the exact named remainder
      ∀ O [complete DVR, finite residue] (π) (hπ : Irreducible π),
        Tendsto (fun N => deepTailSeq π n N) atTop (𝓝 0)
    theorem drainageAt_all_of_deepTailDrain :        -- LEAN CORE
      (∀ m, 4 ≤ m → DeepTailDrainAt m) → ∀ n, DrainageAt n
    theorem deepTail_residue_primary :               -- LEAN CORE ★ the tail structure
      c ∈ deepTailSet π n N → (lift a of c) →
        ∃ ψ k, Irreducible ψ ∧ 2 ≤ k ∧ Associated ((monicPoly a).map (residue O)) (ψ ^ k)

`deepTailSet π n N` := the level-`N` classes that are UNDECIDED and admit NO **shallow
split** — no monic factorization of a lift into positive degrees at resultant depth `v`
with `2v + 1 ≤ N`.  Combined with DRN's lossless dissection (IFCG45), the capstone's
ENTIRE `a2` field (`∀ n, DrainageAt n`, feeding `drainage_of_capstoneHypotheses` /
`totalMassOne_of_drainage` / `UniformityStatement.ofDecided`) now rests on the single
σ-free, factorization-free Prop family `DeepTailDrainAt n` at `n ≥ 4` — and by the
structure theorem the tail is EXACTLY the single-cluster locus: residue reduction a
proper prime power ψ^k, k ≥ 2.  The whole reducible/multi-cluster world drains,
machine-checked, uniformly in q, n.

## THE MECHANISM (the direct route, executed)

Strong induction on the DEGREE through the IFCG41/42 resultant-depth engine:

1. **The master decomposition** (`undecidedSet_subset_master`): an undecided class either
   lies in the deep tail or in a bucket `bucketAt π n₁ n N v` — undecided classes
   witnessing a split at exact depth `v` (exactness extracted by `Nat.find` from any
   shallow witness), `n₁ ∈ [1, n)`, `2v + 1 ≤ N`.
2. **The q^v-to-one packing** (`card_bucketSet_mul_le`): for each bucket class choose a
   depth-`v` witness pair; its `pairNbhd` (IFCG42) has EXACTLY `q^v` members
   (`natCard_pairNbhd`), all with product = that class — so neighborhoods of distinct
   bucket classes are DISJOINT, and the Sigma-injection (IFCG45's own packing idiom)
   gives `#bucket · q^v ≤ #badPairs`.  Every neighborhood pair is bad: its resultant
   stays at depth `v` mod `π^{v+1}` (NEW congruence bridge `resultant_not_dvd_congr`,
   via `classRes_proj` at level `v+1` + `mk_pow_dvd_mk_iff`), so the landed decidedness
   transfer `decidedAt_mulClass_of_not_dvd_resultant` forces an UNDECIDED factor at the
   shifted level `N − v` (else the product class would be decided ⊥).
3. **The bad-pair count** (`card_badPairs_le`): the level-shift is the landed
   `coeffFactor`, whose preimages are EXACTLY `q^{n(N−M)}`-fold
   (`card_preimage_coeffFactor_eq`, resolved from the landed proportion identity) —
   giving `#bucket·q^v ≤ u_{n₁}(N−v)·q^{n₁v+n₂N} + u_{n₂}(N−v)·q^{n₁N+n₂v}`.
4. ★★ **THE MASTER INEQUALITY** (`undecidedSeq_le_master`), the ℕ-bound normalized
   (the RHS collapses to exactly `q^{nN}(s₁+s₂)` — no loss):

       undecidedSeq O n N ≤ deepTailSeq π n N
         + Σ_{n₁=1}^{n−1} Σ_{2v+1≤N} q^{−v}·(undecidedSeq O n₁ (N−v) + undecidedSeq O (n−n₁) (N−v))

5. **The geometric-convolution drain** (`tendsto_geomConv_zero`, pure real analysis,
   landed first-attempt): `0 ≤ g ≤ C`, `g → 0`, `r ≤ 1/2` ⟹ `Σ_{2v+1≤N} r^v g(N−v) → 0`
   (head/tail ε-split against the geometric series).
6. **Reduction + strong induction** (`tendsto_undecidedSeq_of_tail`,
   `undecidedDrainAt_all_pos_of_deepTail`): smaller degrees drain (bases 1,2,3 landed —
   IFCG45/`drainage_two`/`drainageAt_three`), the convolution drains, the tail drains by
   hypothesis ⟹ `UndecidedDrainAt n`; then DRN's iff fires the capstone feed.
7. ★ **The tail structure** (§6): `decidedAt_of_irreducible_residue` (CN-21 packaged
   class-level: irreducible residue reduction ⟹ decided ⟨{(1,n)}⟩ at every N ≥ 1, all
   lifts share the reduction) + `hasShallowSplit_of_coprime_residue_split` (a coprime
   monic residue split lifts to a depth-0 shallow split: coefficientwise monic lifts,
   `Polynomial.resultant_ne_zero` at coprimality over the residue field, the landed
   depth-0 Hensel leg `liftsFactor_of_not_dvd_resultant` at level 1, the congruence
   bridge to carry depth 0 to the produced factors) + IFCG35 §2c's primary classifier
   ⟹ `deepTail_residue_primary`.

## ROUTE DECISION (charge item 1 — the H.124 read)

The ChapH map showed `FullClusterRateBound` has ZERO producers; its gates (HYP.36/30/32/33,
+81/82; hbeta blocked behind GR-7/9/10, hbridge open) are live-blocked, and RIS's x-frame
B-BOX-1 feeds only the d ≥ 2 leaf genre there — it does NOT unblock the rate. So the unit
took the charge's DIRECT route. The result is STRICTLY EASIER to discharge than the H.124
frontier: `DeepTailDrainAt` is (a) Tendsto-form, not a K·M^B·q^{−M} rate species, and
(b) confined to primary classes only — the convolution machinery here replaces the
InductionPackage split arm without any HYP gate.

## THE EXACT SURVIVING OPEN SET

`∀ n, DrainageAt n` (the capstone's a2) now rests on precisely:

* **`DeepTailDrainAt n` for each n ≥ 4** — the measure of level-`N` classes that are
  undecided, admit no shallow split, and (by the landed structure theorem) have residue
  reduction ≅ ψ^k (k ≥ 2, ψ irreducible) tends to 0.  Discharge lanes for successors:
  the ψ-recentring/polygon machinery (ChapB frames + IFCG20/35 sectors) on the primary
  classes, or the H.124 cluster rate at the (d₀, m) shapes with m = k ≥ 2.  Note
  `deepTail_residue_primary` also yields the finite decomposition of the tail by
  (deg ψ, k), k·deg ψ = n, at every level.

## File map (`leanfinal/Uniformity/ChapI/IFCG46.lean`)

§0 `card_preimage_coeffFactor_eq` · §1 `castClass` (+ `castClass_rfl'`,
`undecidedAt_castClass_iff`, `card_castClass_preimage`) · §2 `bucketSet`,
★ `resultant_not_dvd_congr`, `badPairs`, ★ `pairNbhd_subset_badPairs`,
`card_badPairs_le`, ★★ `card_bucketSet_mul_le` · §3 `HasShallowSplit`, `deepTailSet`,
`deepTailSeq`, `bucketAt`, `depthWindow`, ★ `undecidedSet_subset_master`,
`ncard_le_of_subset_union`, `undecidedCount_le_master`, `card_bucketAt_eq`,
`undecidedCount_cast_eq`, `bucketAt_seq_le`, ★★ `undecidedSeq_le_master` ·
§4 ★ `tendsto_geomConv_zero` · §5 `undecidedSeq_le_one`,
★★ `tendsto_undecidedSeq_of_tail`, `DeepTailDrainAt`,
★★ `undecidedDrainAt_all_pos_of_deepTail`, ★★★ `drainageAt_all_of_deepTailDrain` ·
§6 `map_residue_eq_of_proj_eq`, ★ `decidedAt_of_irreducible_residue`,
★★ `hasShallowSplit_of_coprime_residue_split`, ★★★ `deepTail_residue_primary` ·
AxCheck footer (10 lines, ALL Lean core).
Imports: IFCG35 (primary classifier), IFCG42 (transfer + fiber law, carries IFCG41),
IFCG45 (the σ-free carrier + iff), Density.InertLeaf (CN-21).

## Honesty ledger

* `DrainageAt`, `UndecidedDrainAt`, `undecidedSeq`, `DecidedAt` consumed byte-unchanged;
  nothing weakened; the reduction is an implication INTO the capstone field, and the
  remainder Prop `DeepTailDrainAt` is named, uniform in q and n, per-uniformizer.
* The unconditional fire of `UndecidedDrainAt n` (n ≥ 4) was NOT achieved — the deep
  tail (primary cluster classes with all-deep factorization collisions) is genuinely the
  H.124-hard core; no claim otherwise.
* Axioms: Lean core only, machine-printed for all 10 public declarations; no owner cite
  touched or introduced.
* PROJECT_STATE folding suggestion: a2's remainder line should now read
  "`DeepTailDrainAt n`, n ≥ 4 (IFCG46) — primary-residue deep-collision tail".

## Repair log (7 error rounds, all mechanical; every theorem landed as designed)

1. omega fed `n*(N−M)` variable products (standing trap) — replaced by
   `← Nat.mul_add, Nat.sub_add_cancel` rewriting throughout.
2. Occurrence-mistargeting: `Nat.card_coe_set_eq` hit the wrong card — targeted `have`s
   for the univ-set cards.
3. Sigma-binder copy-paste (`w₁ x.1` inside its own binder type) — `w₁ c`.
4. `Finset.sum_const` leaves `Finset.univ.card` — needs `Finset.card_univ` before
   `Nat.card_eq_fintype_card`.
5. `Set.mem_biUnion` index not inferable — pin via a typed `have hmemI`.
6. `add_le_add_left` arg-order at pin ≠ expected — `add_le_add le_rfl`.
   `div_le_div_of_nonneg_right` wants `0 ≤ c` — pass `hq.le`.
   `inv_le_inv_of_le` gone at pin — `one_div_le_one_div_of_le`.
7. whnf timeout: higher-order unification inferring the convolution's `g` — pin
   `(g := ...) (C := 2) (r := ...)` explicitly.  RIS's motive trap (twice): rewriting
   `R₁ ← (monicPoly b₁).map residue` under degree pins / under `(i : Fin (n₁+n₂))` —
   forward-instantiate `resultant_map_map` with all five explicit args; prove coefficient
   identities at ℕ-indexed `coeff j` before touching Fin-indexed goals.  Implicit level
   `N` unified as `n` in an application with no pin — `(N := N)`.
