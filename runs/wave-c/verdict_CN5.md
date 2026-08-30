# UNIT CN5 — VERDICT: THE LINEAR ARM PROVED (stage CN3 CLOSED), THE BASE CHANGE NAMED AND ITS CONSUMPTION PROVED, THE CENSUS FRONT RE-BASED ON TWO FAMILIES (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG25.lean` (713 lines, ZERO sorries; all
17 AxCheck footer lines exactly Lean core `{propext, Classical.choice, Quot.sound}`; the
C.33 cite does not occur — its only two textual mentions are the axiom-fence docstrings;
no landed file touched except the sanctioned one-line aggregator import in
`Uniformity/ChapI.lean`; `I10RungPacks.lean` untouched; no git ops).
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG25.lean`
(final run: zero errors, zero warnings), targeted `lake build Uniformity.ChapI.IFCG25`
green (8931 jobs), `lake env lean Uniformity/ChapI.lean` (aggregator) green.

## ★★★ THE RESULT — `PointConeLaw` reduced to TWO named open families; the front re-based

    theorem pointConeLaw_of_remainder_bridge
        (hR : ∀ e ≥ 2, (smaller value laws < e) →
              ∀ σ deg-e Witnessed, ConeRemainderLaw e σ)
        (hBr : ∀ δ e, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
        PointConeLaw
    theorem decidedSliceAt_all_of_remainder_bridge (hR) (hBr) :
        ∀ n, DecidedSliceAt n                                   -- ★★★ the whole front

The all-degree decided slice now rests on exactly: `ConeRemainderLaw e σ` at every
`e ≥ 3` (the `e = 2` member is CLOSED here — see the tooth; ⚠ NOTE the family is
STRICTLY LARGER than IFCG24's `m ≥ 4` wiring: `e = 3` is a new member, forced because
`PointConeLaw`'s clauses consume cones at every exponent `2 ≤ e < m`) and
`UnramifiedBlockBridge δ e` at every `δ, e ≥ 2`.  Both families carry only the
conditional supply the laws themselves carry; nothing was weakened.

## ★★ THE LINEAR ARM (δ = 1) — ECONE's stage CN3, PROVED (beyond the unit's naming charge)

    theorem stratDecCount_eq_cone_add_deep :        -- ★ the exact partition, EVERY centre
      stratDecCount O m σ (M+m) ((X+Cγ)^m)
        = coneCellCount O π m σ M γ + deepDecCount π m σ M γ
    theorem tendsto_deepDecCount :                  -- ★ the deep limit, centre-BLIND
      Tendsto (deepDecCount π m σ M γ / q^(m(M+m))) atTop
        (nhds (q^(−T_m) · decidedDensity O m σ))
    theorem linearPointClause :                     -- ★★ the δ = 1 clause body
      1 ≤ e → DecidedValueLaw e ⟨s⟩ → ZeroConeClause e ⟨s⟩ →
      PtURLim 1 (pointStratFamily 1 e s)
      -- pair: (n_c·(X^T_e·d_v) + d_c·n_v, d_c·(X^T_e·d_v)) — cone value + q^(−T_e)·decided value

Mechanism (all landed inputs, no drainage): the stratum of `(X+Cγ)^e` partitions
EXACTLY as cone + deep at every level — the centre-`γ` recentring range sits inside the
stratum (`fullLoopClassN_mem_stratum`) and is counted by the mixed boxes (injectivity);
the deep part is squeezed between `q^(−T_e)·decidedSeq(M)` and `q^(−T_e)·decidedSeq(M+e)`
(LOWER: IFCG3's `decidedAt_of_loopMapN` + `card_preimage_mtruncN_kappaLoop` — each
decided level-`M` class contributes its full `q^(κ_e)` box fibre, at every centre;
UPPER: IFCG20's `decided_of_mixedTruncN` + the new `card_ker_mixedTruncN = q^(T_e)`),
converging by the LANDED `decidedSeq_tendsto` alone.  Point-uniformity is DERIVED:
IFCG22's `coneCellCount_translation` (cone part) + the centre-blindness of the squeeze
(deep part).  The DecidedValueLaw input is available in EVERY `PointConeLaw` clause
because `e < m` always (δ = 1: the self-call fence; δ ≥ 2: mass).  Off-menu fences
(`ptURLim_pointStrat_of_degree_ne`, `ptURLim_pointStrat_of_unwitnessed`) close every
degree-mismatched or unwitnessed label at EVERY base degree δ.

## ★★ THE NONVACUITY TOOTH — the (δ, e) = (1, 2) clause, UNCONDITIONAL

    theorem pointConeClause_two (s) : PtURLim 1 (pointStratFamily 1 2 s)   -- NO hypotheses
    theorem coneRemainderLaw_two (σ) : ConeRemainderLaw 2 σ               -- e = 2 CLOSED
    theorem coneRemainderCount_two_eq_zero (σ M) : coneRemainderCount O 2 σ M = 0

The quadratic stratum census over EVERY linear point at EVERY complete DVR is one
uniform rational pair, with zero hypotheses: supply = the landed `DecidedSliceAt 2`
(I02/I03w) + IFCG24's unconditional `zeroConeClause_two`.  This is `PointConeLaw`'s
clause body verbatim at its smallest instance — better than the charge asked (the
premise-free form needed no smaller-laws supply at all).  The remainder family's `e = 2`
member is also proved outright (remainder EMPTY at every type, both ram and non-ram).

## ★ THE NAMED BASE CHANGE + ITS CONSUMPTION (base change IS interface-level — proved)

    def fScale (δ) : Multiset (ℕ×ℕ) → Multiset (ℕ×ℕ)   -- (eᵢ, fᵢ) ↦ (eᵢ, δ·fᵢ)
    def UnramifiedBlockBridge (δ e : ℕ) : Prop          -- THE named CN5 residue:
      -- per O: (∃ complete-DVR O' with q' = q^δ) ∧ ∀ point p of degree δ:
      -- ∃ O' (q' = q^δ), linear p' over O', with the level-exact correspondence
      --   stratDecCount O (δe) ⟨fScale δ s'⟩ N (p^e) = stratDecCount O' e ⟨s'⟩ N (p'^e)
      -- and vanishing off fScale's range
    theorem ptURLim_pointStrat_of_bridge :              -- ★ the consumption, PROVED
      UnramifiedBlockBridge δ e → (∀ s', PtURLim 1 (pointStratFamily 1 e s')) →
      ∀ s, PtURLim δ (pointStratFamily δ e s)
      -- pair: the linear pair COMPOSED with X^δ (q ↦ q^δ; eval_comp)

The `∀ O` quantifier of the linear pair instantiates at the extension `O'`, so the VALUE
side of base change costs nothing — ECONE's prediction is now a theorem, not a forecast.
The denominator obligation `d(q^δ) ≠ 0` is fed by the bridge's scalar-extension clause.

## SCOPE ANSWERS (charge item 1)

**Does the corpus carry the unramified extension? YES, most of it.**  The Quarry backport
`Uniformity/Quarry/AdjoinRootDVR.lean` (FLT provenance, Lean-core):
`AdjoinRoot.isDiscreteValuationRing_of_irreducible_map_residue` (monic lift φ of an
irreducible residual p ⇒ `AdjoinRoot φ` is a DVR, UNRAMIFIED: `𝔪·O'` maximal, local hom,
same uniformizer) + `AdjoinRoot.residueFieldEquiv` (residue field `≃ₐ 𝔽_q[X]/(p)`), and
B53b's `keyIsDomain` supplies the domain instance.  Mathlib at this pin appears to have
NO complete-DVR-with-prescribed-residue-field package and no PowerSeries-DVR instance
chain we could find cheaply; Witt vectors were not needed anywhere.

**The bridge's genuinely OPEN legs** (all localized in the ONE named Prop):
1. `IsAdicComplete` transport to `AdjoinRoot φ` (finite module over a complete DVR) —
   in neither corpus nor an obvious mathlib lemma at this pin;
2. the residue cardinality count `q' = q^δ` (power basis of `AdjoinRoot p`; easy);
3. THE HEART: the level-exact class correspondence — Hensel block decomposition of a
   stratum-of-`p^e` lift into δ Frobenius-conjugate blocks over O', Galois descent
   `F = ∏ Frobᵏ(B)`, and the type transport `fScale δ` (inertia degrees over the point
   are divisible by δ; per-block type is the base type with f-entries divided by δ).
   This is real new mathematics (B.54's `inertiaDegOf_dvd_key_mul_resDeg` is the
   corpus's closest landed fact); it needs its own unit(s).

## What CN5 did NOT close (exact fence)

1. `UnramifiedBlockBridge δ e` for `δ, e ≥ 2` — open (the three legs above).
2. `ConeRemainderLaw e σ` for `e ≥ 3` — open (CN4's fence, now including `e = 3`).
3. Nothing else: given 1 + 2, `∀ n, DecidedSliceAt n` fires through
   `decidedSliceAt_all_of_remainder_bridge` (this file) — the fractional-slope census
   front has no other open content.

## File map (`leanfinal/Uniformity/ChapI/IFCG25.lean`, 713 lines)

§1 `fScale`, `UnramifiedBlockBridge` · §2 `decidedSet_eq_empty_of_unwitnessed`,
`stratDecCount_eq_zero_of_unwitnessed`, `ptURLim_pointStrat_of_degree_ne`,
`ptURLim_pointStrat_of_unwitnessed` · §3 `deepDecCount`, `card_ker_mixedTruncN`,
★ `stratDecCount_eq_cone_add_deep`, `deepDecCount_lower`, `deepDecCount_upper`,
★ `tendsto_deepDecCount` · §4 ★★ `linearPointClause`, `linearPointClause_all` ·
§5 `coneRemainderCount_two_eq_zero`, ★ `coneRemainderLaw_two`, ★★ `pointConeClause_two` ·
§6 ★ `ptURLim_pointStrat_of_bridge` · §7 ★★★ `pointConeLaw_of_remainder_bridge`,
★★★ `decidedSliceAt_all_of_remainder_bridge` · AxCheck footer (17 lines, all Lean core).
Aggregator: one import line in `Uniformity/ChapI.lean`.  Consumed landed inputs:
IFCG3 (loop transport, κ/T arithmetic, mtruncN fibre), IFCG14 (value-law carrier,
Witnessed), IFCG17 (stratPoly/stratDecCount), IFCG20 (fullLoopClassN, mixedTruncN, lift
correspondence), IFCG21 (PtURLim calculus, pointStratFamily, coneCellCount), IFCG22
(translation symmetry), IFCG24 (ZcURLim, ZeroConeClause, remainder wiring, m=2 bank),
I02/I03w (`DecidedSliceAt 2`), GenuineDensity (`decidedSeq_tendsto`).

## Repair log (4 error rounds, all mechanical; every theorem landed as designed)

1. `field_simp` closes goals the plan left for `ring` — three dead `ring`s deleted
   (CN4's known trap, recurred).
2. A manual `rw [eval_mul, eval_mul, …]` chain consumes instances in match order and
   can leave a compound `eval (X^T * dv)` — use `simp only [eval_add, eval_mul,
   eval_pow, eval_X]` (fixpoint) before `field_simp`.
3. Final family-equality cast `((a : ℚ) : ℝ)/… = ↑(↑a/↑b)` needs `push_cast`
   (Rat.cast_div), not `norm_cast`.
4. ⚠ NEW TRAP (generic, affects every consumer of Witnessed-style ∃-instance
   telescopes): a long `obtain ⟨O', i1, …⟩` pattern FAILS TC synthesis (earlier pattern
   binders are not fed to the elaborator for later components), and incremental
   `obtain` + `haveI := i` ALSO fails (haveI's copy is opaque, so instance types
   referencing the ORIGINAL telescope fvars no longer unify).  The fix: incremental
   `obtain ⟨i, h⟩ := h` with **`letI := i`** (definition-transparent) after each
   instance component.  Recorded for the bridge-discharge units, which will consume
   this exact Prop shape.
