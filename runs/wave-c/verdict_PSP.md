# UNIT PSP — VERDICT: THE PRIMARY-SHAPE WEIERSTRASS PEEL LANDS IN FULL —
the `e = 1` law fires exactly (the (1,1) law at scale `q^δ`), the peel recursion at
every exponent is a LEAN THEOREM (finite-level, no completeness, pure resultant
calculus), and the closed form makes every primary value an `N`-FREE FINITE
COMPUTATION (`primo`); DGT route step (c) is CLOSED; the exact named remainder for
(d) is now purely residue-field combinatorics (n-ary convolution bookkeeping +
factorization-type grouping with the Gauss irreducible counts) (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG65.lean` (~2130 lines, ZERO sorries,
zero errors, zero warnings; 26 AxCheck footer rows).
**Axiom fence, machine-exact: ALL TWENTY-SIX rows PURE Lean core
`{propext, Classical.choice, Quot.sound}`** — no B.42, no C.33, no `AX_cellRecursion`
anywhere in the file.  Notably the peel needs NO `IsAdicComplete`: the coprime-Hensel
factorization is landed by injectivity + counting at finite level.
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG65.lean`
(final run: exactly the 26 footprint infos, nothing else); sanctioned aggregator
import appended after IFCG64's line.  `IFCG64.lean` byte-untouched.  NO git
operations.

## THE CHARGE (DGT's remainder (c)) AND WHAT LANDED

DGT (IFCG63) made the diagonal reduced census a sum over residual factor shapes with
composite shapes splitting by the landed convolution; the remainder was the PRIMARY
values `#stratumDepthSet(n, N, v, r^e)`, `r` irreducible residual of degree `δ`,
`δe = n`.  ALL THREE charge items addressed; (1) and (2) CLOSED in Lean.

## ★★★ THE LEAN HEADLINES (all pure Lean core, all uniform in `q`, every level)

    theorem card_stratumDepthSet_irreducible :   -- ★★ THE e = 1 LAW, EXACT
      0 < δ → v < N → Irreducible r → r.Monic → r.natDegree = δ →
      #stratumDepthSet(δ, N, v, r)
        = if δ ∣ v then q^{δ(N−1)} · ((q^δ − 1) · q^{δ(N − v/δ − 1)}) else 0
        -- the (1,1) law at scale q^δ: depth lives on multiples of δ, geometric in v/δ

    theorem card_stratumDepthSet_pow_rec :       -- ★★ THE PEEL RECURSION (any e ≥ 1)
      q^{δe} · T_e(v) = (if δe ≤ v then T_e(v − δe) else 0)
        + Σ_{j<e} (q^{δ(e−j)} − q^{δ(e−j−1)}) · q^{δ(e−j)(2N−1)}
                    · (if δj ≤ v then T_j(v − δj) else 0)
        -- T_j(w) := #stratumDepthSet(δj, N, w, r^j); v < N; IGV's B_e recursion
        -- at finite level, cross-checked against the generating identity
        -- B_e(1−(st)^{δe}) = Σ_{c<e}(s^δ)^c(1−s^δ)(t^δ)^c B_c

    def primo (q δ : ℕ) : ℕ → ℕ → ℕ              -- the N-FREE normalized values
        -- computable ℕ-recursion (well-founded on (e,v) lex); primo(0,v) = [v=0]
    theorem card_stratumDepthSet_pow :           -- ★★★ THE CLOSED FORM
      T_e(v) · q^{v+δe} = primo q δ e v · q^{δe(2N−1)}     (v < N)
        -- every primary value is a finite computation; the normalized density
        -- T_e(v)/q^{δe(2N−1)} = primo/q^{v+δe} is N-free — exactly the
        -- eventual-constancy shape the ZcURLim packaging consumes
    theorem primo_one : primo q δ 1 v = if δ ∣ v then q^δ − 1 else 0
        -- internal two-route pin: the direct e=1 law and the recursion agree

## THE ENGINE (the supporting cast, all landed Lean-core)

* **§0 residue-reading kit**: `resMap` (`Res O N → 𝔽_q`), `resVec`, `map_polyOf`,
  `mem_levelZeroStratum_iff_monicPoly_resVec` (the stratum reader), `resOrd_mk_pow`,
  `resOrd_isUnit_mul`, `resMap_eq_zero_iff` (depth-≥1 ⟺ residual vanishing);
  `card_preimage_of_subset_range` (fibre counting over a subset of the range);
  `scaleBox` + `card_scaleBox_preimage` (the `q^n`-to-1 π-scaling census transport);
  `card_levelZeroStratum` (= `q^{n(N−1)}` at ANY monic degree-`n` residual).
* **§1 the peel legs**: `resOrd_redRes_eq_zero_of_coprime` (coprime residual ⟹
  depth 0 — `resultant_map_map` + `resultant_ne_zero`, window-bridged) and
  `redRes_scaleBox` (`redRes c (π•b) = π^n·redRes c b` — `resultant_C_mul_right`):
  the whole unit runs on PURE RESULTANT CALCULUS, no norm detour.
* **§3 the decomposition machinery**:
  - `isCoprime_of_isCoprime_resMap` — the Bézout lift through the nilpotent kernel
    (defect polynomial has nilpotent coefficients ⟹ lifted combination is a unit);
  - ★ `bijOn_prodVecAt` — the content-`j` boxes ARE (monic `r^j`-stratum) ×
    (`r`-coprime box), by InjOn (monic cancellation through the lifted coprimality)
    + CARD COUNT — finite-level coprime Hensel with NO completeness;
  - ★ `bijOn_divVecAt` — the frame division bijection: for `P` in the `s`-stratum,
    `F ↦ (F /ₘ P, F %ₘ P)` identifies the `s·t`-stratum with (monic `t`-stratum) ×
    (zero-residual remainders) — residual division uniqueness both ways, constructive
    inverse;
  - ★ `resOrd_redRes_prodVecAt` (THE SWAP–PEEL) — `resOrd(Res(F, P·U)) =
    resOrd(Res(P, F mod P))`: window drop, `resultant_mul_right` split, the
    `U`-factor a depth-0 unit, `resultant_comm` swap (sign killed by
    `resOrd_isUnit_mul`), monic size-drop (IFCG63's `resultant_modByMonic_right`);
  - `card_zeroRes_stratumDepth` — the zero-residual depth shift
    `q^m·#{zero-residual slice at v} = [m ≤ v]·#stratum census at v−m`;
  - `card_content_slice` — the per-`j` term assembled (fibre sum over frames,
    BijOn condition transport, Fubini, per-divisor split, the shift);
  - residual counts: `card_dvd_residual`, `card_content_residual`,
    `card_coprime_residual`, `card_box_residual_pred` (census transport through the
    residual reading).

## CHARGE DISPOSITION

1. **e = 1: FIRED EXACTLY** (`card_stratumDepthSet_irreducible` +
   `card_frameDepthSet_irreducible` per-frame).  The mechanism is the mini-peel: a
   nonzero box residual is coprime to the irreducible frame residual by DEGREES, so
   depth 0; the zero-residual boxes peel one `π` (depth shifts by exactly `δ`);
   strong induction on `v` stepping by `δ`.  Note: proved WITHOUT the unramified-
   extension structure theory — the residue reading + resultant calculus suffice.
2. **The peel recursion: PROVED** (`card_stratumDepthSet_pow_rec`), and SOLVED
   (`card_stratumDepthSet_pow` + `primo`): the closed form by lex strong induction.
   The per-frame census at `e ≥ 2` is genuinely frame-dependent (checked: `x²` vs
   `x²−p` at level 2 give different box censuses), so the stratum-level pairing is
   essential — the recursion couples frame and box through the division bijection.
3. **THE WIRE (does (d) fire per-n?): NOT OUTRIGHT — but the remainder changed
   KIND.**  With (c) closed, the diagonal value `#redDepthPairSet(n, N, v)` at fixed
   `n` is, through IFCG63's shape partition + convolution: a sum over the `q^n`
   residual shapes of convolutions of `primo`-values.  What is still missing for the
   per-`n` `ZcURLim` premise of IFCG61's `zcURLim_depthDensity_of_reduced`:
   (i) the n-ary convolution bookkeeping (induction over IFCG63's landed binary
   `card_stratumDepthSet_mul` along a full coprime factorization of a shape);
   (ii) THE TYPE GROUPING: the shape count grows with `q`, so the sum must be grouped
   by factorization type λ ⊢ n (finitely many per `n`), with the number of shapes of
   type λ a polynomial in `q` through the monic-irreducible counts
   `I_δ(q) = (1/δ)Σ_{d∣δ} μ(d)q^{δ/d}` (Gauss/necklace) — NOT yet in the corpus.
   Every remaining step is now FINITE-FIELD COMBINATORICS at level 1 — all
   valuation-theoretic content of VCL's axis-1 value side is Lean-core as of this
   unit.  At `n = 2` the grouping needs only `I_1 = q` and `I_2 = (q²−q)/2`
   (elementary double counting), so the first `ZcURLim` at `n = 2` is one focused
   unit away: (i) is not even needed at n = 2 (binary convolution suffices),
   so the remainder is: the three-type grouping (split/double/inert) + `I_2` +
   the `[t^v]Z_2` extraction against IGV's battery-verified values.
   **Recommended next unit: (d) per-n at n = 2 first, then the general type-grouping
   engine (I_δ + multiset counts).**

## Repair log (10 compile rounds, all mechanical; every theorem landed as designed)

1. Pin drift: `Nat.lt_or_ge` (no `Nat.le_or_lt`), `pow_dvd_pow_iff` (GroupWithZero
   form), `Set.ncard_sdiff` (deprecation), `Nat.dvd_sub` (no `dvd_sub'`),
   `push Not` (deprecation).
2. `card_preimage_of_surjective` needs `[AddCommGroup]` (not `AddGroup`) to match
   LocalData's statement.
3. This pin's `modByMonic_add_div` takes two POLYNOMIAL args (DGT's log note
   confirmed) — no monic proof.
4. Dependent-motive rewrites where `n` occurs in `Coeff`-types: rewrite in the
   LEMMA INSTANCE (safe direction), never abstract `n` in the goal; `δ*0`-indexed
   types need `show`-at-defeq normalization, not simp.
5. `div_modByMonic_unique` with an undetermined `f`: pin `(f := X)` explicitly.
6. Higher-order unification can't infer `P` in `card_box_residual_pred` from the
   eta-normal set — pass the predicate explicitly (defeq-`exact` bridges).
7. `rw [primo]` unfolds the FIRST occurrence (inside the dite) — `conv_rhs`.
8. Beta-redex atoms defeat `omega`/`rw` after `Finset.card_eq_sum_card_fiberwise`
   and `Set.BijOn` applications — `show`-at-defeq beta-reduces.
9. Nonlinear exponent identities: never `omega` on `δ*x` atoms — bridge with
   `Nat.mul_sub`/`Nat.add_mul` equations or `obtain ⟨M, rfl⟩ : ∃ M, N = M+1` then
   `ring`.
10. `induction e ... generalizing v hv` + inner `revert hv; induction v ...` for the
    lex strong induction; `IHe`'s `v` is implicit — pass `(v := ...)`.

## Cross-checks

* `primo_one` (from the recursion) vs `card_stratumDepthSet_irreducible` (direct
  induction): two INDEPENDENT Lean proofs of the e = 1 value — the closed form at
  `e = 1` gives `T·q^{v+δ} = [δ∣v](q^δ−1)·q^{δ(2N−1)}`, the direct law gives
  `T = [δ∣v](q^δ−1)q^{2δN−δ−v−...}` — exponents agree (`δ(N−1)+δ(N−v/δ−1)+v+δ
  = δ(2N−1)` when `δ ∣ v`).
* Hand-evaluation of `primo` against IGV's battery-verified `B_2` coefficients
  (δ=1, e=2, q=2): primo(2,0)=q²−q=2, primo(2,1)=(q−1)²=1, primo(2,2)=(q²−q)+(q−1)²=3,
  primo(2,3)=2 — all four match `[t^v]B_2 = [t^v](1−s)(1−s²t)/((1−st)(1−s²t²))`
  at s=1/2 exactly (1/2, 1/8, 3/16, 1/16 times q^{v+2}).
* The recursion at e=1 degenerates to the mini-peel: `q^δT_1(v) = [δ≤v]T_1(v−δ) +
  [v=0](q^δ−1)q^{δ(2N−1)}` — consistent with the direct law.

## File map (`leanfinal/Uniformity/ChapI/IFCG65.lean`)

§0a `resMap` kit · §0b `resVec`/`map_polyOf`/stratum reader · §0c `resOrd`
complements · §0d `card_preimage_of_subset_range` · §0e `scaleBox` kit · §0f stratum
& fibre counts · §1 peel legs · §2 ★★ e=1 (`card_frameDepthSet_irreducible`,
`card_stratumDepthSet_irreducible`) · §3a residual censuses · §3b Bézout lift +
★ `bijOn_prodVecAt` · §3c ★ `bijOn_divVecAt` · §3d counting helpers +
★ `card_zeroRes_stratumDepth` + `card_stratumDepthSet_zero` · §3e ★ the swap–peel ·
§3f ★ `card_content_slice` · §3g `contentOf` + ★★ `card_stratumDepthSet_pow_rec` ·
§4 `primo` + `primo_one` + ★★★ `card_stratumDepthSet_pow` · AxCheck footer (26 rows).
Imports: Mathlib + IFCG63 (which carries IFCG61/32/16).  Consumed landed corpus:
IFCG61's `polyOf`/`redRes` kit, IFCG63's census objects + `resultant_modByMonic_right`
+ `resOrd_mul` + `card_stratumDepthSet_eq_sum` + `polyOf_eq_self_of_degree_lt`,
H.100/H.107 (`levelZeroStratum`, `resOrd` kit), LocalData
(`card_preimage_of_surjective`, `card_res_ge_of_ge`, `card_coeff`, `residueCard`),
mathlib's Resultant API (`resultant_map_map`, `resultant_mul_right`,
`resultant_C_mul_right`, `resultant_comm`, `resultant_add_right_deg`,
`resultant_ne_zero`).
