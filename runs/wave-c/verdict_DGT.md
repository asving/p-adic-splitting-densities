# UNIT DGT — VERDICT: THE ENGINE'S NORM STEP AND THE FULL BINARY LOCALIZATION LAND —
`Res(F,P) = N_{R[X]/(F)}(P)` for monic `F` over ANY nontrivial commutative ring
(pinned sizes, every window — NOT in mathlib, proved here), the depth-`v` box census
at a coprime product frame is the CONVOLUTION of the factor censuses, the stratified
pair census at a coprime product residual convolves (Hensel bridge composed in), and
the diagonal census IS a sum over factor shapes; the exact named remainder is the
Weierstrass peel at PRIMARY shapes (`r^e`) plus the Euler/zeta assembly (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG63.lean` (1050 lines, ZERO sorries,
zero errors, zero warnings; 20 AxCheck footer rows).
**Axiom fence, machine-exact: ALL TWENTY rows PURE Lean core
`{propext, Classical.choice, Quot.sound}`** — no B.42, no C.33, no `AX_cellRecursion`,
anywhere in the file.  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG63.lean` (final run: exactly the 20
footprint infos, nothing else); targeted `lake build Uniformity.ChapI.IFCG63` GREEN
(8968 jobs); sanctioned aggregator import added after IFCG62's line, aggregator
`lake env lean Uniformity/ChapI.lean` GREEN (exit 0).  `IFCG61.lean`/`IFCG62.lean`
byte-untouched.  NO git operations.

## The charge (IGV route, `runs/wave-c/verdict_IGV.md`) and the milestone ladder

IGV reduced VCL's axis-1 value side to the diagonal reduced census
`#redDepthPairSet(n, N, v)` and derived the master law
`Z_m(t) = ∏_{j≤m}(1−s^jt^{j−1})/(1−s^jt^j)` by the route (a) norm → (b) Hensel
localization → (c) `r`-adic Weierstrass peel → (d) Euler assembly.  **Steps (a) and
(b) are now LEAN THEOREMS, in full**; (c) and (d) are the named remainder.  Per the
charge's ladder: "(a) alone is a strong unit result; (a)+(b) makes the diagonal census
a sum over factor shapes" — BOTH rungs fired, the second one literally
(`card_redDepthPairSet_eq_sum_strata` + `card_stratumDepthSet_mul`).

## ★★★ THE LEAN HEADLINES (`IFCG63.lean`, all pure Lean core, all uniform in `q`)

    theorem resultant_eq_norm :                    -- ★★ THE NORM STEP (route (a))
      Monic F → P.natDegree ≤ k →
      Res(F, P, F.natDegree, k) = Algebra.norm R (AdjoinRoot.mk F P)
                                                   -- ANY nontrivial CommRing R
    theorem redRes_eq_norm :                       -- ★ on IGV's reduced carrier
      redRes c b = N_{(Res O N)[X]/(monicPoly c)}(polyOf b)
    theorem redRes_norm_mul :                      -- ★ norm splits over frames,
      redRes (mulClass c₁ c₂) b = N_{/F₁}(polyOf b) · N_{/F₂}(polyOf b)  -- NO coprimality
    theorem redRes_mulClass :                      -- ★ THE LOCALIZATION IDENTITY
      redRes (mulClass c₁ c₂) b = redRes c₁ (remOf c₁ b) · redRes c₂ (remOf c₂ b)
    theorem resOrd_mul :                           -- depth additivity below the cap
      resOrd (x·y) = min N (resOrd x + resOrd y)
    theorem crtPair_bijective :                    -- the CRT box split (coprime frames)
      IsCoprime F₁ F₂ → Bijective (b ↦ (b mod F₁, b mod F₂))
    theorem card_frameDepthSet_mulClass :          -- ★★ THE BINARY LOCALIZATION CENSUS
      IsCoprime F₁ F₂ → v < N →
      #fd(v, c₁·c₂) = Σ_{a≤v} #fd(a, c₁) · #fd(v−a, c₂)
    theorem isCoprime_monicPoly_of_stratum :       -- residual coprimality descends
    theorem card_stratumDepthSet_mul :             -- ★★ THE STRATUM ASSEMBLY
      [complete DVR] coprime monic residuals g₁ g₂ →
      #sd(v, g₁·g₂) = Σ_{a≤v} #sd(a, g₁) · #sd(v−a, g₂)
    theorem card_redDepthPairSet_eq_sum_strata :   -- ★ THE SHAPE PARTITION
      #redDepthPairSet(n,N,v) = Σ_{r : Fin n → 𝔽} #stratumDepthSet(n,N,v, monicPoly r)

Supporting cast: `rootBasis_repr_mk` (power-basis coordinates of `mk F Q` ARE the
remainder coefficients — the missing repr lemma for `AdjoinRoot.powerBasis'`),
`sylBasis` (the adapted basis `{X^i} ⊔ {X^j·F}` of `R[X]_(deg F + k)`, with full
LI/span/repr kit), `resultant_modByMonic_right` (the size-drop at any window),
`polyOf_eq_self_of_degree_lt`, `monicPoly_mulClass`, `remOf`/`polyOf_remOf`,
`resOrd_mul_eq_iff`, `mem_redDepthPairSet_iff_frame` (the bridge to IFCG61's
carrier), `frameDepthSet`/`stratumDepthSet` (the new census objects, resOrd-form,
uniformizer-free), `card_stratumDepthSet_eq_sum`/`card_redDepthPairSet_eq_sum`
(fiber-sum connectors), `existsUnique_stratum_vec` (every frame class in exactly one
residual-shape stratum).

## Mechanism notes (what made each step cheap or hard)

* **(a) is IFCG32 §1's technique on a new carrier**: `norm_mk_mul`'s adapted-basis
  block-triangular determinant, run against mathlib's `sylvesterMap` +
  `toMatrix_sylvesterMap'`.  `det(Syl) = det(unitriangular basis change) ·
  det[[leftMul(P), 0],[quotients, 1]] = det leftMul(P) = norm`.  Sign-free by
  construction (verified against IFCG61's `redRes_one` instance shape).
* **(b) rides three landed pillars**: mathlib's `resultant_mul_left` (sign-free,
  coprimality-free — the modulus-split needs NO norm), H.102's `bijOn_mulClass`
  (the no-precision-loss Hensel frame bijection; `[IsAdicComplete]` enters ONLY
  here), and `Uniformity.Hensel.isCoprime_of_map_eq` (the residual Bézout lift,
  pushed through `mapRingHom (mk 𝔪^N)` — the H.102 idiom).
* **The census objects are `resOrd`-form and uniformizer-free** (`frameDepthSet`,
  `stratumDepthSet`); the π-dependent divisibility form of IFCG61's carrier connects
  through `mem_redDepthPairSet_iff_frame` (needs `hπ`, `v < N` only).
* **`resOrd_mul` is π-free**: the statement uses only the canonical windowed
  valuation; the proof draws an arbitrary irreducible and exact-valuation
  representatives (any representative of a class of resOrd `a < N` has exact
  `π`-valuation `a`).
* **Counting discipline**: all convolutions run through explicit
  bijection-plus-Finset-fiberwise decompositions (`Finset.card_eq_sum_card_fiberwise`,
  `Finset.sum_fiberwise_of_maps_to`, `Finset.sum_bij` along `bijOn_mulClass`,
  `Finset.sum_mul_sum`); the two `Fintype` instance arguments on the two sum-form
  statements are explicit binders (canonical up to `Subsingleton (Fintype _)`;
  instantiate with `Fintype.ofFinite`) — a deliberate choice after `Fintype.ofFinite`
  as a local instance produced non-defeq instance diamonds.

## Charge disposition

1. **(a) norm step: LANDED IN FULL** (`resultant_eq_norm` + the reduced-carrier and
   frame-split forms).  Strictly stronger than the charged `v(Res) = v(N)`: the
   RING-ELEMENT identity.
2. **(b) localization: LANDED IN FULL, binary form, both levels** (frame convolution
   + stratum assembly + shape partition).  The n-ary form over a full coprime
   factorization is an induction over the landed binary step (pure bookkeeping, no
   new mathematics) — left to the peel unit, which needs the primary factors anyway.
3. **(c) the Weierstrass peel: NOT attempted** (named remainder): the primary-stratum
   censuses `#stratumDepthSet(n, N, v, r^e)`, `r` irreducible residual of degree `δ`,
   `δe = n`.  IGV's `B_e` recursion at finite level.  The `e = 1` case is the
   unramified `(1,1)` law at scale `q^δ` — INS/IFCG32 §2's `addVal_norm_mk_eq` genre
   is the natural substrate for the norm-valuation scaling, now connected to the
   census by `redRes_eq_norm`.
4. **(d) the Euler/zeta assembly: NOT attempted** (named remainder): summing the shape
   partition to `[t^v]Z_m · q^{2nN}`.  Note this is a genuine assembly (the number of
   shapes grows with `q`), so it needs the zeta collapse, not a finite-sum transport.

## VCL AXIS-1 STATUS, RECOMPUTED (charge item 3)

**Value side**: after IGV (min-reduction to the diagonal) and DGT (norm step + binary
localization + shape partition), the entire axis-1 value question at every `(n₁,n₂)`
is now: **the primary-shape censuses** `#stratumDepthSet(n, N, v, r^e)` **plus the
zeta-collapse assembly** — exactly IGV route steps (c) and (d), nothing else.  The
`ZcURLim` premise of `zcURLim_depthDensity_of_reduced` at `n ≥ 2` fires from (c)+(d)
at each fixed `n` (the box values become the exact `[t^v]Z_n` polynomials in `q`,
which are `ZcURLim` by the IFCG24 packaging pattern).  `min = 1` remains COMPLETELY
closed (IGV).  **Consumer side** (which visible cells carry the clusters — B.42's
block-grouping genre) and **axes 2, 3**: untouched, as before.

## File map (`leanfinal/Uniformity/ChapI/IFCG63.lean`, 1050 lines)

§0 ★★ `resultant_eq_norm` + kit (`polyOf_eq_self_of_degree_lt`, `rootBasis_repr_mk`,
`adaptedPoly`/`adaptedPoly_mem`/`div_degree_lt`/`poly_decomp`/`adapted_expand`/
`adapted_linearIndependent`/`adapted_span`/`sylBasis`/`sylBasis_coe`/`sylBasis_repr`,
all private but the two theorems) · §1 ★ `redRes_eq_norm`, `monicPoly_mulClass`,
★ `redRes_norm_mul` · §2 `resultant_modByMonic_right`, `remOf`, `polyOf_remOf`,
★ `redRes_mulClass` · §3 `resOrd_mul`, `resOrd_mul_eq_iff` · §4 `crtPair`,
`crtPair_bijective` · §5 `frameDepthSet`, `mem_redDepthPairSet_iff_frame`,
★★ `card_frameDepthSet_mulClass` · §6 `isCoprime_monicPoly_of_stratum`,
`stratumDepthSet`, `card_stratumDepthSet_eq_sum`, `card_redDepthPairSet_eq_sum`,
★★ `card_stratumDepthSet_mul` · §7 `existsUnique_stratum_vec`,
★ `card_redDepthPairSet_eq_sum_strata` · AxCheck footer (20 rows).
Imports: Mathlib + IFCG61 + IFCG32 + IFCG16.  Consumed landed corpus: IFCG61's
`polyOf`/`redRes`/`redDepthPairSet` kit, IFCG32's `mk_sum`/`repr_basis_sum`/
`norm_mk_mul`/`norm_mk_one` + generic sum lemmas, H.100–H.102 (`levelZeroStratum`,
`proj_surjective'`, `map_monicPoly`, `mem_levelZeroStratum_iff`, `mulClass`,
`bijOn_mulClass`), `Uniformity.Hensel.isCoprime_of_map_eq`, H.107's `resOrd` kit,
`rootBasis` (TypeOfInvariance), mathlib's Resultant/DegreeLT/AdjoinRoot API.

## Repair log (6 compile rounds, all mechanical; every theorem landed as designed)

1. This pin's `modByMonic_add_div` takes two POLYNOMIAL args (no monic proof) —
   matched IFCG61's call shape; one `linear_combination` sign flip.
2. Name drift: `Module.Basis.repr_reindex_apply` (not `reindex_repr`),
   `modByMonic_eq_zero_iff_dvd` (not `dvd_iff_...`), `Fin.val_castAdd/natAdd`
   (deprecations), `Nat.lt_or_ge` (this pin lacks bare `le_or_lt`), `push Not`
   deprecation (→ `Nat.not_le`).
3. `resultant_eq_norm`'s implicit `P` must be passed explicitly at the
   `redRes_eq_norm` call site (elaboration unified it against the monic frame).
4. `set`-bound abbreviations (`φ`, `ψ`) vs `show`: beta-redexes after `rw [hφdef]`
   don't expose rewrite targets — replaced by `show`-at-defeq.
5. `Finset.card_eq_sum_card_fiberwise` obligations arrive Set-coerced
   (`Finset.coe_range` + `Set.mem_Iio` normalize them).
6. `Fintype.ofFinite` as a local instance created non-defeq diamonds
   (`Pi.instFintype`, `Set.fintypeUniv`) — replaced by explicit instance binders on
   the two sum-form statements + a univ-specialized private fiber lemma; binder ORDER
   matters (`[Fintype (Coeff O n N)]` must follow `{n N : ℕ}`).

## Cross-checks

* The norm step reproduces IFCG61's `redRes_one` shape: at `n = 1`,
  `N_{R[X]/(X+a)}(C b) = b` = `Res(X+a, C b, 1, 1)` — the two computations agree
  (sign-free), confirming the block determinant's orientation.
* `redRes_norm_mul` ∘ `redRes_eq_norm` against `redRes_mulClass` ∘ (per-factor
  `redRes_eq_norm` + `polyOf_remOf`): two independent routes to the same product —
  one through INS's `norm_mk_mul` (norm of the SAME box), one through mathlib's
  `resultant_mul_left` (resultants of the CRT residues); both landed, both Lean-core.
  (Their equality is the norm-invariance `N_{/F}(P) = N_{/F}(P mod F)` instance of
  `rootBasis_repr_mk`.)
* `card_frameDepthSet_mulClass` at `v = 0` degenerates to the single term
  `#fd(0,c₁)·#fd(0,c₂)` — the unit-resultant product count, consistent with the
  IFCG41/RDC unit-depth genre.
