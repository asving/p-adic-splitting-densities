# UNIT EFR — VERDICT: ROW 2 RE-BASED ONTO ITS EXACT PER-AXIS CONTENT — the
`(h, e', d)`-frame partition machine-checked, THE MIXED LATTICE over the compositum
LANDED (PSL3's recorded missing instrument), the general-target digit reading and the
composed `(1, d)` tower criterion landed, the off-degree axes fired UNCONDITIONALLY,
and the census master rewired (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG62.lean` (903 lines, ZERO sorries,
zero errors, zero warnings; 19 AxCheck footer lines).  **Axiom fence, exactly as
designed:** EVERY §1–§6 declaration — the frame index + its three kernel-decided
censuses, the carrier/subset/disjointness/tiling/count stack, ★★★ the reduction fire,
the off-degree fires, the `m = 4` re-derivation, ★★ THE MIXED LATTICE, ★★ the
general-target reading, ★★ the composed compositum criterion — is **pure Lean core**
`{propext, Classical.choice, Quot.sound}`.  Only §7's master wire carries Lean core +
the owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42) — inherited through IFCG60's spine, never re-consumed.  Verification:
per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG62.lean` (8 increments,
each GREEN before the next); targeted `lake build Uniformity.ChapI.IFCG62` GREEN
(9037 jobs); aggregator `lake env lean Uniformity/ChapI.lean` GREEN with the IFCG62
line wired between IFCG61 and I10RungLift3W.  I10CalcBridge.lean untouched; no git
ops.

## ★★★ THE HEADLINES

    theorem eisFullSpanRemainderLaw_of_mixedFaceLaws :        -- ★★★ ROW 2 REDUCED
      (∀ p ∈ mixedFrames m, MixedFaceLaw m p.1 p.2.1 p.2.2 σ) →
      EisFullSpanRemainderLaw m σ                             -- LEAN CORE
    theorem compositum_root_pow_dvd_mk_iff :                  -- ★★ THE MIXED LATTICE
      α₂^w ∣ mk P ↔ ∀ i < e', ∀ j < deg φ,
        π^((w + e' − 1 − i)/e') ∣ (B i)ⱼ                      -- LEAN CORE
    theorem xres_eq_iff_digits_target :                       -- ★★ THE (h,d) READING
      xres = R (ANY monic degree-D target) ↔ the D digit equations at heights h·(D−t)
    theorem compositum_transfer_digits_base :                 -- ★★ THE TOWER ROUTE
      base composed ceilings on the dev bi-coordinates ↔ the O₁ digit equations
    theorem decidedSliceAt_all_of_MASTER_MIXED :              -- ★★★ THE MASTER REWIRED
      {FC cite, PER-FRAME laws, hSD, hPD, hLeafSub} → ∀ n, DecidedSliceAt n

plus the UNCONDITIONAL axes: `mixedFaceLaw_of_off_degree` +
`eisFullSpanRemainderLaw_of_off_degree` (σ.degree ≠ m — row 2's law with NO premise),
and the sanity re-derivation `eisFullSpanRemainderLaw_four_via_frames` (IFCG51's
`m = 4` law re-proved through the empty frame census).

## The three charge items, disposition

**(1) THE MIXED LATTICE — LANDED, composition-first as forecast.**  The charge's
hunch ("the h > 1 non-DVR obstruction may only block the SINGLE-ring route, not the
tower route") is CONFIRMED for the composition mechanics: both stage lattices compose
formally.
* `unram_pow_dvd_mk_iff` (instance-free beyond domain): `(algebraMap π)^t ∣ mk φ B ⟺
  π^t ∣ every coefficient of B` — the unramified stage is a coefficient-wise read
  (canonical rep via `modByMonicHom`, `mk_eq_zero` + the monic degree bound force the
  representative identity `B = C(π^t)·Q`).
* ★★ `compositum_root_pow_dvd_mk_iff`: over `O₂ = AdjoinRoot (eisKey (algebraMap π)
  c₁ e')` on `O₁ = AdjoinRoot φ`, for `P` of degree `< e'` with bi-polynomial
  coordinate reps `B i` (degree `< deg φ`): `α₂^w ∣ mk P ⟺ the composed divisibility
  ceilings π^{⌈(w−i)/e'⌉} ∣ (B i)ⱼ` — `eis_root_pow_dvd_mk_iff` INSTANTIATED at `O₁`
  (uniformizer persistence by IFCG29, instance supply by IFCG27's cascade via haveI)
  composed with the unramified read.  Exactly PSL3's fence item 2 ("the RINGS are
  landed, their coordinate lattices are not") — now landed, Lean-core, uniform in
  `q, φ, c₁, e', w`.

**(2) THE (h, d) CRITERION — the reading landed at FULL generality; the tower
composition landed on the `(1, d)` axis.**
* ★★ `xres_eq_iff_digits_target`: at ANY slope `h/e'` under the side pins, `xres = R`
  for ANY monic degree-`D` target ⟺ the `D` lattice digits at heights `h·(D−t)` read
  `R`'s coefficients.  This SUBSUMES the landed `(h,1)` criterion
  (`R = (X − z̄)^D` = the binomial reading) and supplies every mixed frame via
  ★ `xres_eq_psi_pow_iff_digits` (`R = ψ^k`) — the discovery here is that PSL4's
  `(h,1)` digit criterion was secretly target-generic: the binomial content was the
  TARGET's coefficients, not the reading.
* ★★ `compositum_transfer_digits_base`: `eis_transfer_digits_iff` (C110's two-way
  box↔digits heart) instantiates VERBATIM at `O₁` — the landed criteria are
  DVR-uniform, so the unramified stage costs nothing — and the mixed lattice converts
  the deep `O₂`-box into base-ring composed ceilings on the dev bi-coordinates.  With
  PSL4's `zcURLim_compositum_value` (the value transport at `q ↦ q^{deg φ}`, already
  landed) this completes the `(1, d)`-axis instrument set: box reading + lattice +
  value transport.

**(3) THE FIRE — the honest sanctioned reduction, exact and machine-checked.**
`EisFullSpanRemainderLaw m σ` at composite `m ≥ 6`, `σ.degree = m` did NOT fire
unconditionally (see the surviving remainder below).  What fired:
* **The per-frame partition**: every remainder class carries canonical frame data
  `(h, e', d)` (slope numerator/denominator, residual root-field degree) with
  `1 ≤ h < e'` coprime, `e'·d ∣ m`, `k := m/(e'·d) ≥ 2`, `(h, d) ≠ (1, 1)`;
  `mixedFace` = {face + residual `ψ^k` (`ψ` monic irreducible, degree `d`, `ψ(0) ≠ 0`)
  + decided-σ}.  ★★ `remainder_eq_biUnion` (THE EXACT TILING — forward by
  `powerSector_data` + face uniqueness + the `(1,1)`-frame-would-be-an-`eisFace`
  contradiction; backward by the general-`(h,d)` sector inclusion
  `mixedFace_subset_psf` + prime-power rigidity `mixedFace_disjoint_eisFace`), and
  `card_remainder_partition` (exact at every level).  No coverage claim is assumed
  anywhere — the tiling is a proved identity against IFCG51's law carrier.
* ★★★ `eisFullSpanRemainderLaw_of_mixedFaceLaws` — row 2 from the finitely many
  per-frame laws (`ZcURLim_sum` + the partition count).
* **The frame censuses, kernel-decided**: `mixedFrames 4 = ∅` (re-deriving IFCG51's
  `m = 4` law through the reduction — sanity GREEN), `mixedFrames 6 = {(2,3,1)}`
  (ONE frame at `m = 6`: the slope-2/3 face — ASM's witness), `mixedFrames 8 =
  {(1,2,2), (3,4,1)}` (the first compositum frame `𝔽_{q²}` and the slope-3/4 frame).
* **The unconditional axes**: off the degree (`σ.degree ≠ m`) every frame carrier is
  empty and row 2's law holds with NO premise.
* ★★★ `decidedSliceAt_all_of_MASTER_MIXED`: IFCG60's census master with row 2
  replaced by the per-frame laws.

## ★★ THE CENSUS POSITION (exact)

The master (`decidedSliceAt_all_of_MASTER_MIXED`) now rests on:
{`FactorCorrespondenceAt D` (THE STAGED CITE, row 1) · **`MixedFaceLaw m h e' d σ`
at `(h, e', d) ∈ mixedFrames m`, composite `m ≥ 6`, `σ.degree = m`, witnessed
ramified, under the `< m` value laws** (row 2, THIS UNIT's re-base) ·
`SplitConvolutionDefectLaw`/`PowerConvolutionDefectLaw` multi-σ (rows 3–4; on
IFCG58/60's spine these re-base onto `VisCensusLaw`) · `LeafSubfaceLaw` multi-σ
(row 5)}.  Hence the charge's ★★ endpoint, stated exactly: **once the frame laws
close, the census master = {FC_D cite, VisCensusLaw multi-σ, LeafSubfaceLaw
multi-σ}** — row 2 contributes NOTHING else.

## THE EXACT SURVIVING REMAINDER (row 2's discharge fence, per axis)

`MixedFaceLaw m h e' d σ` at `(h, e', d) ∈ mixedFrames m`, `σ.degree = m`.  The
per-frame discharge pipeline, against IFCG51's landed template (W1/W2/L2), now needs
ONLY the face-side transports — the criteria and lattices are all landed:
1. **`(1, d ≥ 2)` frames** (e.g. `(1,2,2)` at `m = 8`): the recentring rings
   (IFCG43 LEG 4), the box criterion at `O₁` (`compositum_transfer_digits_base`),
   the coordinate lattice (`compositum_root_pow_dvd_mk_iff`), and the value
   transport (`zcURLim_compositum_value`) are ALL landed.  Missing: the compositum
   `cellTransport` (the dev-transform bijection `Coeff O (e'·k·d) N ≃ Coeff O₂ k
   (e'·N)` with its count transport — IFCG43 LEG 2's replay over the tower, noting
   `card_coeff` at `q^d`) and the decision transport (`transport_decidedAt_iff`'s
   analogue — the OM tower step at the compositum; CTS's cite-reduction pattern).
2. **`(h ≥ 2, 1)` frames** (e.g. `(2,3,1)` at `m = 6` — the ONLY `m = 6` frame): the
   box reading is landed ring-free (`xres_eq_iff_digits_target` ⊇ PSL4's
   `xres_eq_pow_iff_digits_h`).  Missing: the recentring route — either the digit-box
   COUNT at the base ring (no transport; count the digit-pinned lattice boxes
   directly against `stratDecCount`) or the Bézout Eisenstein ring
   (`γ^{e'} = z^s·π`, `s·h ≡ 1 mod e'` — the tower route around the non-DVR order),
   plus the decision transport at slope `h/e'`.
3. **`(h ≥ 2, d ≥ 2)` frames** (first at `m = 12`: `(2,3,2)`): the composition of
   1 + 2 — the general-target reading covers the box; the mixed recentring ring is
   LEG 4's compositum at the `xKey`; both missing legs above apply.

## File map (`leanfinal/Uniformity/ChapI/IFCG62.lean`, 903 lines, 28 declarations)

§0 kit (`ncard_biUnion_eq`, `isKey_X` replicas; `not_irreducible_monic_pow`;
`monic_irreducible_pow_eq` — prime-power rigidity) · §1 `mixedFace`, `MixedFaceLaw`,
`mixedFrames`, `mem_mixedFrames_iff`, ★ the three decided censuses (m = 4/6/8) ·
§2 ★ `mixedFace_subset_psf`, `mixedFace_disjoint`, `mixedFace_disjoint_eisFace`,
★★ `remainder_eq_biUnion`, ★★ `card_remainder_partition` ·
§3 ★★★ `eisFullSpanRemainderLaw_of_mixedFaceLaws`, ★ `mixedFaceLaw_of_off_degree`,
★ `eisFullSpanRemainderLaw_of_off_degree`, `eisFullSpanRemainderLaw_four_via_frames` ·
§4 ★ `unram_pow_dvd_mk_iff`, ★★ `compositum_root_pow_dvd_mk_iff` ·
§5 ★★ `xres_eq_iff_digits_target`, ★ `xres_eq_psi_pow_iff_digits` ·
§6 ★★ `compositum_transfer_digits_base` · §7 ★★★ `decidedSliceAt_all_of_MASTER_MIXED`
· AxCheck (19 lines).  Import: `IFCG60` (transitively the whole spine).  Aggregator:
one line between IFCG61 and I10RungLift3W.

## New definitions (trust boundary — flag for review)

`mixedFace` (frame carrier: face + `ψ^{m/(e'·d)}` residual + decided),
`MixedFaceLaw` (the per-frame `ZcURLim`), `mixedFrames` (the frame Finset) — all
three NEW statements.  The remainder's tiling by them is PROVED
(`remainder_eq_biUnion`), so the reduction consumes IFCG51's
`EisFullSpanRemainderLaw` byte-identically with no coverage assumption; nothing was
weakened.

## Repair log (5 error rounds over 8 increments; every statement landed as designed)

1. `mixedFrames` defined WITHOUT the file-wide `Classical.propDecidable` attribute
   (which would break kernel `decide`); `classical` per-proof instead.
2. THE SUBST-DIRECTION TRAP (corpus contact #3): `minFaceAt_unique hF₀ hF` +
   `subst` eliminates the RIGHT variable — swap to `minFaceAt_unique hF hF₀` so the
   data-carrying names survive.
3. Frame-triple projections `(h,e',d).2.2` are stuck atoms for omega/rw after
   `obtain` — `dsimp only at hp ⊢` after destructuring.
4. `eisFace` sits in IFCG51's `{O : Type}` universe fence — consumer section split
   (the Type* subset lemma stays general).
5. `degree_modByMonicHom_lt` is IFCG39-private — replicated;
   `AdjoinRoot.mk_C` lands in `of`-form — `AdjoinRoot.algebraMap_eq` bridges;
   `Polynomial.degree_C_mul_le` absent at this pin — `degree_smul_le` via
   `smul_eq_C_mul`; `irreducible_algebraMap_adjoinRoot` needs `O₁`'s
   completeness/finiteness — `adjoinRoot_isAdicComplete/finite_residueField` haveI
   (twice); `eisKey_monic`'s unconstrained `π, c` metavariables pinned
   (PSL3's logged trap #4, avoided on second contact).

## Consumption notes for the frame-discharge units

* The `(1, d)` frame unit should replay IFCG51's W1/W2/L2 with: `fullSpan_pins` (h
  general, landed) → `xres_eq_psi_pow_iff_digits`/`compositum_transfer_digits_base`
  (the reading) → the compositum cellTransport (TO BUILD — LEG 2's replay) →
  `zcURLim_compositum_value` at `n(q^d)/d(q^d)` (mind: the value pair enters at
  `q^{deg φ}`, so the frame sum needs the `d`-reindexed rational family).
* The `(h, 1)` frame's cheapest route may be COUNT-FIRST: the digit criterion pins
  `D` digits and the lattice floors everything else — a product box at the BASE ring
  whose count against `stratDecCount` needs no ring transport at all; only the
  decision transport is genuinely tower-shaped.
* `mixedFrames m` is kernel-decidable at any concrete `m` — per-mass fires can
  enumerate frames by `decide` exactly as `m = 4/6/8` here.
