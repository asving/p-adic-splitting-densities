# UNIT ASM — VERDICT: THE FULL-SPAN/dd ASSEMBLY LANDED — composite-mass
`PowerFullSpanLaw` fired on the correspondence family (LEAN-CORE), the `m = 4` law and
ALL of ER4's dd limits on `FactorCorrespondenceAt 2` ALONE, the `{(4,1)}` row down to
TWO premises, and the endgame scoreboard recomputed (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG51.lean` (2353 lines, ZERO sorries,
zero errors, zero warnings; 24 AxCheck footer lines).  **Axiom fence, better than
charged:** EVERY assembly declaration — W1/W2 reconstruction, the stratum limit, the
squeeze, the cells/faces/partition, `zcURLim_eisFace`, ★★★
`powerFullSpanLaw_of_correspondence`, the wrapper, ★★★ `powerFullSpanLaw_four`, ★★★
`zcURLim_e1DdDecFam` — is **pure Lean core** `{propext, Classical.choice, Quot.sound}`.
Only the three §7 ER4-ROW fires carry Lean core + exactly the owner-signed gate-(b)
cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42) — inherited from
IFCG34's counts, never re-consumed.  **The C.33 cites do NOT occur** (verified on the
full axiom dump).  Verification: per-increment
`timeout 580 lake env lean Uniformity/ChapI/IFCG51.lean` (14 increments, each GREEN
before the next; final: zero diagnostics beyond the 24 expected prints); targeted
`lake build Uniformity.ChapI.IFCG51` GREEN (8960 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the IFCG51 line wired between
IFCG50 and IFCG52.  No other landed file touched; no git ops.

## ★★★ THE THREE HEADLINES

    theorem powerFullSpanLaw_of_correspondence :             -- ★★★ COMPOSITE FIRE
      (∀ D, D ∣ m → 2 ≤ D → 2·D ≤ m → FactorCorrespondenceAt D) →
      (… → DecidedValueLaw D τ) → (… → ZeroConeClause D τ) →
      EisFullSpanRemainderLaw m σ → PowerFullSpanLaw m σ     -- LEAN CORE
    theorem powerFullSpanLaw_four :                          -- ★★★ THE m = 4 LAW
      FactorCorrespondenceAt 2 → ∀ σ, PowerFullSpanLaw 4 σ   -- ONE premise, LEAN CORE
    theorem zcURLim_e1DdDecFam :                             -- ★★★ ER4's dd LIMITS
      FactorCorrespondenceAt 2 → ∀ σ, ZcURLim (e1DdDecFam σ) -- EVERY σ, LEAN CORE

plus the wrapper `powerFullSpanLaw_of_prime_or_correspondence` (m prime — DTR's fire —
OR the family) and the three ER4 rows re-fired with the dd premise GONE:

    coneRemainderLaw_four_ramPair_of_correspondence : FC 2 → ZcURLim e1SplitFam
      → ZcURLim (e2DecFam ramPairType) → ConeRemainderLaw 4 ramPairType
    coneRemainderLaw_four_type22_of_correspondence  : E1IrrLeafDecision → FC 2
      → ZcURLim e1IrrFam → ConeRemainderLaw 4 type22
    coneRemainderLaw_four_type41_of_correspondence  : E1IrrLeafDecision → FC 2
      → ConeRemainderLaw 4 type41                    -- ★ the WILD row: 2 premises

## The three charge items, disposition

**(1) THE FULL-SPAN ASSEMBLY — done, with one honest structural finding.**  The
assembly needed TWO genuinely new proof layers beyond bookkeeping, both landed:

* **W1/W2 — the reconstruction** (`lattice_pins`, `coeff_lattice_of_dev_box`,
  `cell_of_box`): an `alphaBox` member's inverse transport HAS the minimal face, the
  residual degree `D`, and residual `(X−z̄)^D`.  The lift half is the φ-adic digit
  computation: `g = Σ dev_t·φ^t`, `eis_root_pow_dvd_mk_iff` reads
  `v((dev_t)_i) ≥ D−t+[i=0]`, the binomial of `φ^t = (x^{e'}+wπ)^t` lands every
  coefficient on the lattice, the top digit is EXACTLY `1` (degree < e' + mk = 1), so
  the corner is `(wπ)^D` + a `π^{D+1}`-divisible tail — EXACT.  With it the transport
  image is characterized BOTH ways (`cellTransport_image_eisCellDec` =
  `alphaBox ∩ decidedSet`, via IFCG47's iff at `σ = scaleType e' σ'`).
* **L2 — the mixed-window squeeze** (`tendsto_boxDec`): #(alphaBox ∩ decided-σ') at
  levels `e'(M+m)` is squeezed between `q^{D(K−P+1)}·stratDecCount(P) / q^{Σκ}` and
  its `Q`-window mirror (`P = e'(N−D)`, `Q = e'(N−1)`), both arms →
  `q^{−e'T_D}·V`, `T_D = Σ_{t<D}(D−t)`.  The four counting maps are ONLY same-window
  ring multiplications + landed truncations (`scaledHom`, `stratHom`; kernel/range
  counts by `card_preimage_of_subset_range`); decidedness transfers both ways by
  `typeOf_scaleRoots` at `α^{e'}` (T1/T2).  `V` is the mass-`D` STRATUM-census limit
  `tendsto_stratDecCount_of_laws : DecidedValueLaw D σ' → ZeroConeClause D σ' → …` —
  IFCG25's cone+deep partition consumed at the zero centre.

Then the bookkeeping as planned: cells ⊆ `powerSectorFull` (stratum/shallow/¬pureFace/
proper-power-residual all discharged; the pure-face exclusion by reconstructing the
`(h, m)` face from `faceBox` and contradicting `minFaceAt_unique`), centre sums
(`card_eisFace_eq_sum`, `(q−1)` centres), the divisor partition (`card_psf_partition`,
exact at every level), per-face values `(q−1)·q^{−e'T_D}·(n_{σ'}/d_{σ'})(q)` with the
off-range and off-degree σ handled by PROVED emptiness (the pointwise law types every
lift inside `scaleType e''s range).

**THE HONEST FINDING — the named remainder is FORCED at composite `m ≥ 6`:**
`EisFullSpanRemainderLaw m σ` := the ZcURLim of `powerSectorFull` MINUS the
Eisenstein-frame faces — the `h ≥ 2` slopes and the `deg ψ ≥ 2` residual root fields.
The charge's forecast ("conditional on the FC family" alone) is exactly right at
`m = 4` (the remainder is PROVED EMPTY: `4 = e'·k·deg ψ`, `e' ≥ 2`, `k ≥ 2` forces
`(e', k, deg ψ, h) = (2, 2, 1, 1)`) and at every prime `m`; at composite `m ≥ 6` the
non-Eisenstein faces are real (e.g. slope `2/3` at `m = 6`) and their cell reading is
exactly PSL4 §5's OWN recorded open set (the `(h,1)` ring transport, the `(1,d)`
compositum lattice, the mixed case).  The remainder Prop is their one consumption
point — a NEW named law, not a weakening; nothing else was weakened.

**(2) THE dd ASSEMBLY at `m = 4` — done, stronger than charged.**
`dec_e1DdBox_eq_eisFace`: ER4's σ-decided double-root box IS the σ-decided `(4,2,2)`
Eisenstein face — E1's lattice/corner reconstruct the face through W1, ER4's pinned
side residual is the class residual through `fullSpan_pins` (proof-irrelevant
`sideSet`-nonemptiness aligns the two `resPoly` pins), and the centre is nonzero by
`natDegree_resPoly`'s constant-coefficient clause.  Hence `ZcURLim (e1DdDecFam σ)` for
EVERY σ (not just the three charged rows) on `FactorCorrespondenceAt 2` alone, and the
three rows fire as displayed above.  The `{(4,1)}` law — the census's first genuinely
deep-wild row — now rests on exactly {`E1IrrLeafDecision`, `FactorCorrespondenceAt 2`}.

**(3) THE ENDGAME SCOREBOARD — the census's total surviving premise set.**

After ASM, the all-degree decided slice (through IFCG44's
`decidedSliceAt_all_of_defects` + IFCG34's §8 wire) rests on:

| # | Surviving premise | Kind | Consumers / notes |
|---|---|---|---|
| 1 | `FactorCorrespondenceAt D`, `D ≥ 2` | **THE STAGED CITE** (GMN/FGMN, owner gate; CTS's two-surface package) | every composite full-span mass (divisor depths `2 ≤ D ≤ m/2`); the whole `m = 4` full-span law; ER4's three dd rows.  `D = 2` unlocks the ENTIRE `m = 4` territory. |
| 2 | `EisFullSpanRemainderLaw m σ`, composite `m ≥ 6` | NEW named law (this unit) | the `h ≥ 2` faces + `deg ψ ≥ 2` residuals of the full-span sector; = PSL4 §5's open instrument set (`(h,1)` digit/ring transport, `(1,d)` compositum, mixed).  EMPTY (proved) at `m = 4`; CLOSED at prime `m`. |
| 3 | `SplitConvolutionDefectLaw e σ` + `PowerConvolutionDefectLaw e σ`, `e ≥ 5` ram. witnessed | open (one mechanism) | the finite-precision polygon-factorization-uniqueness converse — IFCG38's genre, two consumers. |
| 4 | `LeafSectorLaw e σ`, `e ≥ 5` ram. witnessed | open | the leaf cell count (residual-irreducible sector). |
| 5 | `E1IrrLeafDecision` | open (B-BOX-1 at `ℓ = 2, deg ψ = 2`) | ER4's type22/type41 rows — the `{(4,1)}`-exclusion on irreducible residuals. |
| 6 | `ZcURLim e1SplitFam`, `ZcURLim e1IrrFam` | open, CLOSED-FORM targets | E1 depth-0 digit counts (needs a per-coordinate digit-count instrument; values already predicted in ER4's verdict). |
| 7 | `ZcURLim (e2DecFam σ)`, σ ∈ {ramPair, splitTail, inertTail} | open | E2 depth-0 closure (ER4 §e2-genres: no B-BOX obstruction; natural next unit). |
| 8 | `UnramifiedBlockBridge δ e`, `δ, e ≥ 2` | open (IFCG25 §6) | the `q ↦ q^δ` Hensel-block base change. |

Descent-internal (NOT scoreboard items): the `DecidedValueLaw D τ` / `ZeroConeClause D τ`
supplies at divisor depths `D ≤ m/2` are the recursion's own smaller-mass products
(`ZeroConeClause` from `zeroConeClause_of_remainderLaw` + the mass-`D` front) — closed
at `D = 2` outright, well-founded at all depths.  **GONE from the list since DTR/CTS:**
`CellTypeScalingAt D` (reduced to row 1), "the face/centre assembly" and "the dd
assembly" (THIS UNIT — both were the last named bookkeeping blocks).

## File map (`leanfinal/Uniformity/ChapI/IFCG51.lean`, 2357 lines)

§0 kit (private replicas: `isKey_X`, `mem_sideSet_iff'`, `resPoly_rep`) ·
§1 ★ `lattice_pins` (W1) · §2 `eisKey_pow_coeff_dvd`, ★ `coeff_lattice_of_dev_box`,
★★ `cell_of_box` (W2) · §3 ★ `tendsto_stratDec_of_laws`,
`card_preimage_of_subset_range`, `scaledHom`/`stratHom` (+ range/kernel
characterizations and counts), ★ T1 `decided_scaled_of_strat`, ★ T2
`decided_strat_of_scaled`, ★ `card_boxDec_lower`/`card_boxDec_upper`,
★★★ `tendsto_boxDec` · §4 `ncard_biUnion_eq`, `eisCellDec`, `residual_pow_inj`,
`not_irreducible_linear_pow`, ★ `eisCellDec_subset_psf`,
★★ `cellTransport_image_eisCellDec`, ★★ `card_eisCellDec`,
★ `eisCellDec_eq_empty_of_not_range`, ★★★ `tendsto_eisCellDec`, `eisFace`,
`card_eisFace_eq_sum`, `eisFace_subset_psf`, `eisFace_disjoint`,
★ `card_psf_partition`, ★★★ `tendsto_eisFace` · §5 `EisFullSpanRemainderLaw` (THE
named remainder), ★★ `zcURLim_eisFace`, ★★★ `powerFullSpanLaw_of_correspondence`,
★★★ `powerFullSpanLaw_of_prime_or_correspondence` · §6 ★★ `psf_four_subset_eisFace`,
★★ `eisFullSpanRemainderLaw_four`, ★★★ `powerFullSpanLaw_four` ·
§7 ★★ `dec_e1DdBox_eq_eisFace`, ★★★ `zcURLim_e1DdDecFam`, the three
`coneRemainderLaw_four_*_of_correspondence` rows · AxCheck footer (24 lines).
Imports: `IFCG25` + `IFCG34` + `IFCG48` (transitively 47/44/43/39/38/35/33/31/24/…).
Aggregator: one import line in `Uniformity/ChapI.lean` (between IFCG50 and IFCG52).

## New definitions (trust boundary — flag for review)

`eisCellDec` (face + residual-power + decided), `eisFace` (∃-nonzero-centre form),
`EisFullSpanRemainderLaw` (the complement family) — all three are NEW statements; the
remainder law's carrier is DEFINED as `powerSectorFull \ ⋃(divisor faces)`, so the
partition identity is definitional-complete (no coverage claim is assumed anywhere).
`PowerFullSpanLaw`'s statement (IFCG44's) is consumed byte-untouched.

## Repair log (8 error rounds over 14 increments; every statement landed as designed)

1. `typeOf_scaleRoots` lives in root `Uniformity.Density`, not a TypeOfInvariance
   namespace; `Irreducible.not_unit` → `not_isUnit`; `Dvd.intro _ rfl` → `dvd_mul_left`.
2. dvd_trans through a metavariable exponent — name the intermediate `have` first.
3. omega atom mismatches on `%`/`*` terms — the generalize-set must cover EVERY
   hypothesis mentioning the atom (h7 AND h8), and products under dependent Fin types
   must be `set`-opaqued BEFORE generalizing (`B := e'·resOrd …` first, then `C := e'·D`).
4. `div_le_div_iff` → `div_le_div_iff₀` at this mathlib pin.
5. `Nat.mul_le_mul_left` needs the common factor OUTERMOST-LEFT — calc-reshape, don't
   rw-chain `pow_add`s.
6. `tendsto_atTop_mono` leaves an `id M` atom — `show` it away before omega;
   `tendsto_finset_sum` deprecated → `tendsto_finsetSum`.
7. THE XHS SELF-REWRITE TRAP (third corpus contact): `Monic.eq_X_add_C` must be
   destructured through `∃ a, ψ = X + C a` — rewriting in place rewrites `ψ.coeff 0`
   inside its own replacement.
8. `interval_cases` leaves `↑⟨k, h⟩` Fin coercions opaque to omega — `show` with the
   literal; `Set.diff_eq_empty` → `Set.sdiff_eq_empty`.

Traps avoided by design (DTR/PSL4/ER4/CTS logs consulted): every `{O : Type}` universe
fence honored (three consumer sections); `eis_recentring_stack`'s ∃-pack destructured
with ALL components named; `hne` proof-irrelevance used via `exact`-defeq, never `rw`;
`(D+1)*e'`-style products normalized by `ring` before omega throughout.

## Consumption notes

* **The owner gate is now maximally concentrated**: signing the CTS cite package
  (either surface) at `D = 2` alone yields — machine-checked, Lean-core —
  `PowerFullSpanLaw 4 σ` (all σ) and all three dd rows; at all `D ≥ 2` it clears
  row 1 entirely, leaving the full-span territory on row 2 only.
* Row 2's discharge unit should extend §4's frame per PSL4 §5: the `(h,1)` axis via
  `xres_eq_pow_iff_digits_h` (digit criterion — the ring-free content), the `(1,d)`
  axis via `zcURLim_compositum_value` + `compositum_recentring_stack`; the per-cell
  pipeline here (W1/W2/L2) is the template — only the box reading and the recentring
  ring change.
* `zcURLim_e1DdDecFam` holds for EVERY σ — future E1 bookkeeping (e.g. the full σ-sum
  gates) can consume it without the three-row restriction.
