# UNIT E2L — VERDICT: THE E2 DEPTH-0 CLOSURE LANDED — the three `e2DecFam` limits
fire on the named dd-recursion terms ALONE, the `∀ σ` E2 front closes on THREE terms,
and the two mass-4 TAIL rows drop to one deep premise each (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG53.lean` (2877 lines, ZERO sorries,
zero errors, zero warnings; 36 AxCheck footer lines).  **Axiom fence, exactly as
designed:** the field-side trichotomy (§1b), the ENTIRE counting layer (`card_aBox`,
`card_bBox`, `card_bdBox_le`, `card_digTriples`, `card_cBox`, `mem_genre_cases`), the
limit machinery (`ZcURLim.sandwich`, `tendsto_geom_sum`), and — notably — the THREE
depth-0 limit VALUES (`zcURLim_e2Ram0Fam/Split0Fam/Inert0Fam`) are **pure Lean core**
`{propext, Classical.choice, Quot.sound}`.  The decisions, partition identities,
decided counts, the three E2 limits, the rows, and the front carry Lean core + EXACTLY
the owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42), inherited through IFCG26's two-point-side peel and IFCG34/36's landed counts —
never re-consumed.  **The C.33 cites do NOT occur** (verified on the full dump; zero
`sorryAx`).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG53.lean` (15 increments, each GREEN
before the next; final: zero diagnostics beyond the 36 expected prints); targeted
`lake build Uniformity.ChapI.IFCG53` GREEN (8947 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the IFCG53 line wired between IFCG52
and ID12.  IFCG52.lean untouched; no other landed file touched; no git ops.

## ★★★ THE HEADLINES

    theorem zcURLim_e2DecFam_ramPair :                       -- ★★★ ramPair E2 limit
      ZcURLim (e2DdDecFam ramPairType) → ZcURLim (e2DecFam ramPairType)
    theorem zcURLim_e2DecFam_splitTail :                     -- ★★★ splitTail E2 limit
      ZcURLim (e2DdDecFam splitTailType) → ZcURLim (e2DecFam splitTailType)
    theorem zcURLim_e2DecFam_inertTail :                     -- ★★★ inertTail E2 limit
      ZcURLim (e2DdDecFam inertTailType) → ZcURLim (e2DecFam inertTailType)
    theorem zcURLim_e2DecFam_of_shape :                      -- ★★ ALL OTHER σ: value 0,
      σ ≠ ramPair → σ ≠ splitTail → σ ≠ inertTail → ZcURLim (e2DecFam σ)  -- UNCONDITIONAL
    theorem zcURLim_e2DecFam_all :                           -- ★★★ THE FULL ∀σ CLOSURE
      3 × ZcURLim (e2DdDecFam ·) → ∀ σ, ZcURLim (e2DecFam σ)

plus the census rows re-fired (ASM scoreboard delta below) and the REWIRED front
`decidedSliceAt_all_of_dd_limits` (IFCG36's `hE2 : ∀ σ` premise discharged to the three
named terms).

## The three charge items, disposition

**(1) THE GENRE PARTITION + DIGIT COUNTS — done, exact at every level.**  On `e2Box`
(`v₀ ≥ 3, v₁ ≥ 2, v₂ = 1` pinned, `v₃ ≥ 1`) the corner `(v₀, v₁)` is UNBOUNDED (unlike
E1's pinned `v₀ = 2`), so the depth-0 census is an infinite geometric family, resummed:

* **(a) `aBox t`** (`v₀ = 2t` exact, `t ≥ 2`, `v₁ ≥ t+1`): fractional `[0,2]` face ⇒
  DECIDED `{(2,1),(2,1)}`.  Count `(q−1)²q^(4K−3t−5)`; value `(q−1)²q³/((q³−1)q¹¹)`.
* **(b) `bBox v`** (`v₁ = v` exact, `v ≥ 2`, `v₀ ≥ 2v`): broken polygon ⇒ DECIDED
  `{(1,1),(1,1),(2,1)}`.  Count `(q−1)²q^(4K−3v−4)`.  NO boundary (`2v₁ ≤ v₀ ≤ K` free).
* **(c) `cBox s P`** (`v₀ = 2s+1` exact, `s ≥ 1`, `v₁ ≥ s+1`): integral slope-`s`
  width-2 face; residual = the CLASS-DIGIT monic quadratic `Y² + (d₁/δ)Y + (d₀/δ)`
  (`δ, d₁, d₀` = `resDig` at `1, s+1, 2s+1`); trichotomy `splitPairs/irrPairs/ddPairs`
  (new `splitPairs` + `pair_trichotomy` + 3 disjointnesses, Lean-core).  Counts
  `#digTriples(P)·q^(4K−3s−7)` with `#digTriples(P) = (q−1)·#P` (the scaling
  bijection) — DBL's digit instrument replayed via a fresh fiber engine.
* **Boundary `bdBox`** (`v₀ = K` invisible): `≤ q^(3K)`, squeezed to `0` by the new
  `ZcURLim.sandwich` — NO undecidability proof needed.
* `mem_genre_cases`: the partition is EXHAUSTIVE (Lean-core), and the decided-set
  identities are EXACT ℕ-equations at every level (`card_decided_*`).

Split/inert value symmetry, certified: both depth-0 values are
`(q−1)²q⁴/(2(q³−1)q¹⁰) = (q−1)²/(2q⁶(q³−1))`; ramPair depth-0 is `(q−1)²/(q⁸(q³−1))`.
Measure sanity (ledger): (a)+(b)+(c-split)+(c-irr)+(dd) = `(q−1)q⁻⁸` = measure(e2Box) ✓.

**(2) THE DECISIONS — all-corner-depths-at-once, and the recursion-reach check.**
The mechanism avoids residual multiplicativity entirely: peel the `(1,2)`-pure `[2,4]`
block `F` (IFCG26 two-point-side, purity RETAINED — `e2_peel`; IFCG34's
`exists_ramQuad_factor_of_e2` discards it), then read the cofactor `R`'s polygon off
the four coefficient identities `a₀ = f₀r₀`, `a₁ = f₀r₁ + f₁r₀`, `a₂ = f₀ + f₁r₁ + r₀`,
`a₃ = f₁ + r₁` in digit currency:
* (a): `R` is `(2t−1,2)`-pure ⇒ `irreducible_of_isPure_natDegree_eq` ⇒ efPair `(2,1)`.
* (b): `v(r₁) = v₁−1` EXACT (ultrametric strict-min), second two-point-side ON `R` at
  `(v₁−1,1)` ⇒ two monic linears (`efPair_of_natDegree_one`).
* (c): `R` is `(s,1)`-pure ⇒ **B.44** `exists_scaleRoots_of_pure_integral` — its digit
  clause hands `Ḡ` coefficientwise; the unit is pinned by the `a₂` identity (`λ = δ`),
  so `Ḡ` IS the class-digit quadratic.  Then **CN-21** `typeOf_inert_of_irreducible_map`
  (= B.59/B.60's step 3) for THE UNCONDITIONAL ℓ=1 INERT LEAF (`decidedAt_cIrrBox`),
  and Hensel `exists_linear_factorization` + `typeOf_mul_linear` for the split leaf.
* `typeOf_e2_mem` (the shape pin): every lift's type is `{(2,1)}` + a quadratic shape ⇒
  only the three named σ have nonempty decided sets — the `∀ σ` engine
  (`decided_inter_e2_eq_empty_of_shape`, strengthening IFCG34's singleton exclusion).

**THE RECURSION-REACH CHECK (charge item 2's question) — ANSWERED, negative at
depth ≥ 1, two decorrelated reads:** IFCG20's linear recentring PROVABLY misses `e2Box`
(its range forces `resOrd (c 2) ≥ 2` against the pinned `v₂ = 1`; the E2 sector is
inside IFCG20's own declared-open `fracCellCount`), and IFCG43's `cellTransport`
reaches the counting/value layers of the mass-2 reduction but NO decidedness/typeOf
transport is landed (IFCG43's honest-scope items 1+3).  Per the charge's sanction, the
dd sector enters as ONE new named family per σ — `e2DdDecFam σ` (carrier `e2DdBox` =
the union of visible `cBox s ddPairs`), the exact analogue of ER4's `e1DdDecFam`.
The MATH of the dd tower: after the linear recentring `x ↦ x + zπ^s` the double-root
sub-problem is the MASS-2 ZERO CONE over the SAME `O` — and `zeroConeClause_two` (IFCG24)
is CLOSED for every σ.  The missing Lean is exactly a decidedness transport across the
two-block Hensel factorization (the F·R split's π-adic continuity) — a full unit of
IFCG51-W1/W2-scale, the natural successor.

**(3) THE SCOREBOARD DELTA (vs ASM's table, row by row).**

* **Row 7 — `ZcURLim (e2DecFam σ)`, σ ∈ {ramPair, splitTail, inertTail} — DISCHARGED
  TO DEPTH ≥ 1**: replaced by the three named `ZcURLim (e2DdDecFam σ)` terms.  All
  OTHER σ close at `0` UNCONDITIONALLY (row 7 was implicitly ∀σ via the front's `hE2`;
  that quantifier is now fully accounted).
* **The mass-4 tail rows collapse to ONE deep premise each**:
  `coneRemainderLaw_four_splitTail_of_dd : ZcURLim (e2DdDecFam splitTailType) →
  ConeRemainderLaw 4 {(1,1),(1,1),(2,1)}` and the mirror `inertTail` row — previously
  each rested on the full `e2DecFam` term.
* **The ramPair row**: `coneRemainderLaw_four_ramPair_of_dd` — TWO named recursion
  terms (`e1DdDecFam ramPairType` order-2 + `e2DdDecFam ramPairType`), via IFCG36's
  rewiring (e1Split closed there).
* **The census front**: `decidedSliceAt_all_of_dd_limits` — the all-degree decided
  slice now rests on {`E1IrrLeafDecision`, `∀σ ZcURLim (e1DdDecFam σ)`, the THREE
  `e2DdDecFam` terms, the `e ≥ 5` ramified laws, the block bridges}.  IFCG36's
  `hE2 : ∀ σ, ZcURLim (e2DecFam σ)` premise is GONE from the scoreboard, replaced by
  three σ-specific deep terms.
* Rows 1–6, 8 unchanged.

## New definitions (trust boundary — flag for review)

`splitPairs` (two distinct roots, nonzero constant) · `aBox`/`bBox`/`cPair`/`cBox`/
`bdBox` (the genre boxes, class-digit form) · `e2DdBox` + `e2DdDecFam` (THE new named
premise family — the only open carrier) · `e2BdDecFam`, `e2Ram0Fam`, `e2Split0Fam`,
`e2Inert0Fam` (bookkeeping families) · `digTriples` · `Ta`/`Vb`/`Sc` (index windows).
The consumed statements (`e2DecFam`, `ConeRemainderLaw`, IFCG36's front) are
byte-untouched; nothing was weakened.

## File map (`leanfinal/Uniformity/ChapI/IFCG53.lean`, 2877 lines)

§0 coefficient kit (CommRing quad replays, `coeff_mul_quadratics`) · §1 boxes +
`splitPairs` · §1b `pair_trichotomy` + 3 disjointnesses · §2 `e2_class_bank` replay +
★ `e2_peel` · §3 ★★ `decidedAt_aBox`, ★★ `decidedAt_bBox`, ★★ `e2_cGenre_bank`,
★★ `decidedAt_cIrrBox` (THE ℓ=1 INERT LEAF), ★★ `decidedAt_cSplitBox` ·
§4 ★ `typeOf_e2_mem`, `decided_inter_e2_eq_empty_of_shape` · §5 `mem_genre_cases`,
the three `decided_*_inter_e2Box` identities · §6 `ncard_biUnion_eq` replay,
★★ `card_decided_*` (3), `quad_box_card`, ★ `card_aBox`/`card_bBox`/`card_bdBox_le`,
`digTriples`, ★ `card_digTriples`, fiber-engine replays, ★★ `card_cBox` ·
§7 the five families, ★ `ZcURLim.sandwich`, ★ `tendsto_geom_sum`, window lemmas,
pair-count kit, ★★ the three `zcURLim_e2*0Fam` (LEAN-CORE values), boundary squeeze,
decompositions · §8 ★★★ the three main fires + `of_shape` + `_all` · §9 the three rows
+ ★★★ `decidedSliceAt_all_of_dd_limits` · AxCheck footer (36 lines).
Imports: Mathlib + IFCG36 + ChapB.B60 + Density.Gates (everything else transitive).
Aggregator: one import line in `Uniformity/ChapI.lean` (between IFCG52 and ID12).

## Repair log (12 error rounds over 15 increments; every statement landed as designed)

1. `isCoprime_self_iff` not at pin → `hcop.isUnit_of_dvd' dvd_rfl dvd_rfl`; `linarith`
   on a general field → `eq_neg_of_add_eq_zero_left`.
2. `obtain` CONSUMES the destructured hypothesis — rebuild `π^1 ∣ f₀` after `⟨w, hw⟩`.
3. `Irreducible.not_unit` → `not_isUnit` (ER4's logged rename, re-confirmed);
   `ENat.lt_one_iff_eq_zero` deprecated → `Order.lt_one_iff`.
4. THIS PIN'S `add_le_add_left/right` ADD ON THE OPPOSITE SIDE vs current mathlib
   naming — `add_le_add_right h c : c + a ≤ c + b`(!); use `gcongr` where possible.
5. ℕ-subtraction × `ring`: rewriting `2s = (2s−1)+1` in place self-rewrites inside
   `2s−1` — opaque the exponent FIRST (`obtain ⟨E, hE1, hE2⟩`, the IFCG36 idiom #9).
6. B.44 returns `G.natDegree = R.natDegree`, not `= 2` — convert before use.
7. Structure eta for `FactorizationType`: `typeOf f = ⟨d⟩` via
   `⟨(typeOf f).data⟩ = ⟨σ.data⟩` + `exact` (rw on `{data := d}.data` fails).
8. `Multiset` literals: `g ::ₘ g₂ ::ₘ 0 = {g, g₂}` needs `Multiset.cons_zero` + `rfl`;
   multiset data equalities close by `decide`, never `rfl` across `+`-reassociation.
9. ELABORATION SPLIT: `((∑ …) : ℝ)` as a DIRECT ascription pushes the cast PER-TERM,
   but `((A + B : ℝ))` keeps `↑(∑…)` casts OUTSIDE — the two family shapes need
   different cast lemmas (`Nat.cast_sum` only in the second case); force the outside
   form with an inner `(… : ℕ)` ascription when matching.
10. `push_cast` reorders `Finset` arguments (`Ta (M+4)` → `Ta (4+M)`) — never push_cast
    across an identity that must stay syntactic; use controlled `Nat.cast_*` +
    `← add_div` + `ring` instead.
11. `div_add_div_same` not at pin → `← add_div`; `Nat.le_self_pow` needs its exponent
    pinned via `show` when used inside `push_cast`'s lemma list.
12. `gcongr` self-discharges side goals from context (leaves `exact` dead) — trim.

Traps avoided by design (ER4/DBL/XHS/ASM logs consulted): `Monic.eq_X_add_C` always
DESTRUCTURED through ∃ (the XHS self-rewrite trap, 4th corpus contact); the `{O : Type}`
universe fence on all `ZcURLim` families; `fin_cases`-free membership via the
`by_cases (i:ℕ) = k` + `Fin.ext` pattern; `resDig_mk` transport via `← congrFun ha i`.

## Consumption notes (for the successor)

* **The dd-discharge unit** (the natural next): land the decidedness transport across
  the two-block factorization (`monicPoly a = F·R` with `R`'s class at level `~2(K−s)`
  after recentring by the residual double root), then each `e2DdDecFam σ` value is the
  mass-2 zero-cone resummation over `s` — `zeroConeClause_two` (CLOSED, IFCG24) supplies
  the per-`s` values; `tendsto_geom_sum` (this file, Lean-core, generic in `C`, `a`,
  `e`, window) supplies the resummation.  Predicted values: ramPair
  `(q−1)²/(q⁷(q³−1))·(1/(q²+q+1))`-shaped splits across σ (per the mass-2 cone
  `1/(q²+q+1)` fraction) — certify in-unit.
* `ZcURLim.sandwich` and `tendsto_geom_sum` are general-purpose: any future stratum-sum
  limit (e.g. the `e ≥ 5` sectors) can consume them.
* `zcURLim_e2DecFam_of_shape` holds for EVERY off-shape σ — future bookkeeping can
  consume the E2 sector at any type without the three-row restriction.
