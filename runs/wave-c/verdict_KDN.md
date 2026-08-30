# UNIT KDN — VERDICT: `DiscNullAt n` DISCHARGED AT EVERY `n` (UNCONDITIONAL, Lean core); `KrasnerAt` REDUCED to the deep-wild irreducible Krasner core; the capstone's a2 field now rests on ONE classical residual (2026-08-30)

**Status: DONE — the counting residual of DTD's pair is PROVED outright; the
field-theory residual is reduced to its exact classical kernel (irreducible +
residue-power inputs only); all three fires landed.  The full unconditional
`KrasnerAt` was NOT achieved (the mathlib `IsKrasner` bridge for the irreducible core
is the surviving open set — honest named remainder per charge sanction).**

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG50.lean` (1273 lines, ZERO sorries,
zero warnings, no new axioms; EIGHTEEN AxCheck footer lines, ALL pure Lean core
`{propext, Classical.choice, Quot.sound}` — no cite consumed anywhere).  One-line
aggregator import added to `Uniformity/ChapI.lean` (after IFCG49; IFCG48 untouched).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG50.lean`
(final: zero diagnostics beyond the 18 expected prints); targeted
`lake build Uniformity.ChapI.IFCG50` GREEN (8960 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN.  NO git ops.

## ★★★ THE HEADLINES

    theorem discNullAt (n : ℕ) : DiscNullAt n                    -- ★★★ UNCONDITIONAL, EVERY n
    theorem krasnerAt_of_krasnerIrred :
      (∀ m, KrasnerIrredAt m) → KrasnerAt n                      -- ★★★ the reduction
    theorem krasnerIrredAt_of_deep :
      KrasnerDeepAt n → KrasnerIrredAt n                         -- ★★ residue-irreducible case gone
    theorem deepTailDrainAt_of_krasner : KrasnerAt n → DeepTailDrainAt n     -- half the fence falls
    theorem drainageAt_all_of_krasner :
      (∀ m, 4 ≤ m → KrasnerAt m) → ∀ n, DrainageAt n             -- ★★★ a2, disc side DISCHARGED
    theorem drainageAt_all_of_krasnerDeep :
      (∀ m, KrasnerDeepAt m) → ∀ n, DrainageAt n                 -- ★★★ THE SHARPEST FIRE

`KrasnerDeepAt m` (the ONLY remaining supply for the capstone's ENTIRE a2 field, and
only at `m ≥ 4`): *an IRREDUCIBLE separable monic over a complete DVR whose residue
reduction is NOT irreducible is decided at some finite level* — pointwise, ∃-level, no
rate.  Constants, linears, reducibles, and residue-irreducible inputs are all
machine-checked away (UFD factorization + the IFCG42 transfer + CN-21/IFCG46).

## The `DiscNullAt` engine (all new, all Lean core — §§0–3 of the file)

DTD's charge pointer warned the honest mechanism is a hypersurface point-count
(Igusa/Serre); the classical uniform-rate bounds need splitting fields.  The landed
route needs NEITHER — the per-`O` Tendsto form is exploited through DTD's own König
engine, used TWICE:

1. **One variable** (§1): for `g ∈ O[Y]` nonzero, if the null cylinders
   `{y : g(y) ≡ 0 mod π^D}` never empty, `exists_point_of_truncClosed` (IFCG49)
   produces a point null at EVERY level — an EXACT ROOT `r ∈ O` by adic Hausdorffness
   (`exists_root_of_forall_oneNull_nonempty`, the König root).  Factor `g = (Y−r)h`;
   the ultrametric split (`mem_pow_sub_of_mul_mem`: `v(ab) ≥ D ∧ v(a) < t ⟹
   v(b) ≥ D−t`) gives `s_{2t}(g) ≤ q^{−t} + s_t(h)`; induction on `natDegree`.
   No Newton polygons, no extensions, no rates.
2. **Many variables** (§2): induction on the number of coefficient coordinates via
   `MvPolynomial.finSuccEquiv`.  If the null proportion of `F` has infimum `ε > 0`,
   then at every level the tail classes with HEAVY fibers (fiber proportion ≥ ε/2)
   have proportion ≥ ε/2 (`exists_heavy_survivor`: fiberwise count decomposition
   `card_mvNullSet_eq_sum` via `Equiv.sigmaFiberEquiv` + `Nat.card_sigma`), while the
   classes violating a guarded level-`D₀` nonvanishing of the leading coefficient have
   proportion < ε/2 (induction hypothesis + IFCG46's exact fiber law).  The survivor
   family is truncation-closed; its KÖNIG POINT specialises `F` to a one-variable
   polynomial that is NONZERO (guard) yet has non-draining null proportion (heaviness
   + `fiberSet_proj_eq_oneNullSet`) — contradicting §1.  The compactness substitutes
   for the (false-in-general) uniformity of the fiberwise limits.
3. **The bridge** (§3): `genericDisc n := Res(𝔉, 𝔉′) ∈ MvPolynomial (Fin n) O` of the
   generic monic; mathlib's `resultant_map_map` is UNCONDITIONAL at pinned formal
   degrees, so `classDisc = eval ∘ genericDisc` at every level (`eval_map_genericDisc`)
   and the discriminant-null cylinders are the null cylinders of ONE fixed polynomial.
   Nonzero (`genericDisc_ne_zero`): at the coefficient vector of `∏ᵢ (X − π^{i+1})`
   (distinct — powers of a uniformizer never repeat, via the §0 unit-power dvd iff)
   the resultant is nonzero over `Frac O` by `separable_prod_X_sub_C_iff` +
   `resultant_ne_zero` + monic degree-padding (`resultant_add_right_deg`, padding
   coefficient `1`).

## The `KrasnerAt` reduction (§4)

* `isCoprime_of_separable_mul` (constructive Bezout regrouping), pinned-degree
  resultant nonvanishing from separability over `Frac O` (both the self-derivative and
  the pair forms, transported along `algebraMap O (Frac O)` — injectivity used exactly
  once, for the FORWARD direction of the hypothesis).
* `decidedAt_multiset_prod` — THE RECOMBINATION: multiset induction over
  `monicFactorization_exists` (TypeOf's UFD factorization); at each step the exact
  resultant depth `v` is extracted by Hausdorffness, levels are lifted by IFCG49's
  `decidedAt_of_coeffFactor`, and IFCG42's
  `decidedAt_mulClass_of_not_dvd_resultant` + `mulClass_proj` fire at
  `N := v + max (v+1) (max N₁ N₂)`.  The empty product is decided at `typeOf 1`.
* `KrasnerIrredAt` (irreducible core) and `KrasnerDeepAt` (irreducible + residue
  reduction not irreducible) are byte-parallel strengthenings of `KrasnerAt`'s
  hypothesis side; `krasnerIrredAt_zero`, `krasnerIrredAt_one` are proved
  (nonvacuity), and the residue-irreducible case is discharged by
  `IFCG46.decidedAt_of_irreducible_residue` (CN-21).

## THE EXACT SURVIVING OPEN SET (the a2 fence after KDN)

`∀ n, DrainageAt n` (the capstone's a2) now rests on ANY of:
* `KrasnerDeepAt m`, `m ≥ 4` — THE minimal residual: irreducible separable monic,
  residue reduction a proper power `φ^e` (`e ≥ 2`, or mixed non-irreducible shapes),
  eventually decided.  Discharge lanes: (a) mathlib `IsKrasner` +
  `IsKrasner.of_completeSpace` (`Mathlib/Analysis/Normed/Field/Krasner.lean`) — the
  work is bridging the corpus's algebraic DVR framing (AdjoinRoot norms, `efPair`) to
  the normed-field framing, plus factorization-type rigidity under Krasner-equality of
  extensions; (b) the OM/Montes tower termination (the project's own deep-wild
  program, ChapB/ChapC assets); (c) the faithful cite under owner gate (b) — DTD
  already recorded this Prop family as textbook content.
* `KrasnerIrredAt m` / `KrasnerAt m`, `m ≥ 4` (strictly stronger supplies, same fires).
* `DeepTailDrainAt m`, `m ≥ 4` (UDR's IFCG46 lane, unchanged).

`DiscNullAt` is GONE from every fence — no lane needs it any more.

## File map (`leanfinal/Uniformity/ChapI/IFCG50.lean`, 1273 lines)

§0 `mem_maximalIdeal_pow_iff_dvd`, `pow_dvd_unit_mul_pow_iff`, ★ `mem_pow_sub_of_mul_mem`
(the ultrametric split), `exists_notMem_maximalIdeal_pow` (Hausdorff extraction),
`boxProp` + calculus (nonneg/mono/le_one/union_le/`boxProp_preimage_eq`/
`boxProp_le_of_subset_preimage`), `proj_cons`, ℝ-helpers
(`tendsto_zero_of_antitone_of_subseq`, `exists_pos_forall_le_of_not_tendsto`,
`tendsto_inv_qpow_zero`) ·
§1 `oneNullSet/Prop`, `mem_oneNullSet_proj`, `truncClosed_oneNullSet`,
★ `exists_root_of_forall_oneNull_nonempty`, `oneNullSet_subset_split`,
`oneNullProp_le_split`, ★★ `tendsto_oneNullProp_zero` ·
§2 `finSuccEquiv_map`, family helpers (`antitone_boxProp_of_truncClosed`,
`tendsto_boxProp_zero_of_empty`), `mvNullSet/Prop`, `eval_proj_comp_map_mk`,
`mem_mvNullSet_proj`, `truncClosed_mvNullSet`, `fiberSet/Prop`,
★ `fiberSet_proj_eq_oneNullSet`, `fiberProp_le_trunc`, `sliceEquivOfMem`,
`card_mvNullSet_eq_sum`, ★★ `exists_heavy_survivor`, ★★★ `tendsto_mvNullProp_zero` ·
§3 `genericMonic`, `genericDisc`, `map_genericMonic`, `apply_genericDisc`,
`eval_genericDisc`, `eval_map_genericDisc`, `mvNullSet_genericDisc`,
`mvNullProp_genericDisc`, ★ `genericDisc_ne_zero`, ★★★ `discNullAt` ·
§4 `KrasnerIrredAt`, `isCoprime_of_separable_mul`,
`natDegree_ne_zero_of_monic_irreducible`, `resultant_deriv_pinned_ne_zero`,
`resultant_deriv_ne_zero_of_separable_map`, `resultant_pair_ne_zero_of_coprime_map`,
★★ `decidedAt_multiset_prod`, ★★★ `krasnerAt_of_krasnerIrred`, `krasnerIrredAt_zero`,
`krasnerIrredAt_one`, `KrasnerDeepAt`, ★★ `krasnerIrredAt_of_deep` ·
§5 ★★★ `deepTailDrainAt_of_krasner`, ★★★ `drainageAt_all_of_krasner`,
★★★ `drainageAt_all_of_krasnerIrred`, ★★★ `drainageAt_all_of_krasnerDeep` ·
AxCheck footer (18 lines, ALL Lean core).  Imports: IFCG49 only.

## Honesty ledger

* `KrasnerAt`, `DiscNullAt`, `DeepTailDrainAt`, `DrainageAt`, `DecidedAt` consumed
  byte-unchanged from IFCG49/IFCG46/corpus; nothing weakened; the fires are
  implications INTO the capstone field.
* `KrasnerIrredAt`/`KrasnerDeepAt` are `KrasnerAt` with ADDED hypotheses
  (`Irreducible (monicPoly a)`, resp. + `¬Irreducible` of the residue reduction) —
  hypothesis-side strengthenings only, `O : Type` universe convention preserved.
* All drains per-`O` Tendsto, uniform in `q` and `n` in the ∀-`O` Prop sense; no
  uniform rate claimed or needed (and the charge's deep-box constant-proportion
  refutation in DTD's verdict explains why none is available cheaply).
* Nonvacuity: `discNullAt` itself is a full proof; `krasnerIrredAt_zero/one` proved;
  conventions machine-checked, not eyeballed.
* Axioms: Lean core only, machine-printed for all 18 public declarations; B.42/C.33
  never occur; no owner cite touched.
* PROJECT_STATE folding suggestion: a2's remainder line should now read
  "`KrasnerDeepAt m`, m ≥ 4 (IFCG50; or KrasnerAt/KrasnerIrredAt, or IFCG46's
  `DeepTailDrainAt`) — deep-wild pointwise Krasner completeness; `DiscNullAt`
  DISCHARGED (IFCG50.discNullAt, unconditional)".

## Repair log (5 error rounds, all mechanical; every theorem landed as designed)

1. Renames: `Irreducible.not_isUnit` (not `not_unit`), root `Nat.card_coe_set_eq`,
   `le_or_lt` gone (→ `Nat.lt_or_ge`), `div_add_div_same` gone (→ `← add_div`),
   `div_le_div_of_nonneg_right` wants `0 ≤ c`; `Monic.natDegree_eq_zero` (not
   `natDegree_eq_zero_iff_eq_one`); `push_neg` deprecated (avoided).
2. `boxProp_preimage_eq`: comm-gymnastics → `div_eq_div_iff + push_cast + ring`.
3. THE TRAP OF THE DAY: `rw [← x.2]` where `x`'s TYPE mentions the rewritten variable
   (subtype over a `c`-dependent predicate) = motive failure, and in structure-field
   elaboration an `isDefEq` TIMEOUT with no useful message.  Fix: destructure the
   subtype (`obtain ⟨⟨z, hz⟩, hzc⟩ := x`) before rewriting.  Also: the
   `Set.toFinset`+`filter` counting route whnf-times-out under classical instances —
   `Equiv.sigmaFiberEquiv` + `Nat.card_sigma` + a hand-rolled non-dependent subtype
   equiv (`sliceEquivOfMem`) is light and first-attempt green.
4. `simp` rewrote `C (π^k)` to `(C π)^k` (map_pow), breaking `natDegree_X_sub_C` —
   use `simp only` + explicit `Finset.sum_const` chain.
5. `resultant_add_right_deg` needs ALL-named args (section-variable order trap);
   dependent `Fin.cons ... 0` in a `show` needs a type ascription;
   `rw [← hd]` (degree = n) under `monicPoly a : Fin n → O` = dependent-motive
   failure — rewrite the OTHER equation (`rw [hd] at h4`) instead.

## Suggested next decomposition (for the orchestrator)

The a2 fence is now one Prop family.  Two independent lanes worth separate units:
(i) `KrasnerDeepAt` via mathlib `IsKrasner` — first sub-node: `Frac O` as a complete
normed/valued field from `IsAdicComplete` (the instance bridge is the whole
difficulty; everything after is Krasner + finitely many invariants);
(ii) the faithful-cite lane under owner gate (b) with the Prop as stated (DTD already
flagged it as textbook content; the statement is now maximally weak AND
residue-power-restricted).
