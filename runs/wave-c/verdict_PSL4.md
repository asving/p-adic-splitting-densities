# UNIT PSL4 — VERDICT: `PowerSectorLaw` FIRED ON TWO NAMED LAWS — the full-span/proper partition discovered and machine-checked, the face-indexed assembly landed CITE-FREE at the Eisenstein frame, both general-(h,d) axis instruments landed, the recentred wiring landed, and the census front re-based with `PowerSectorLaw` GONE from the premise list (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG44.lean` (1344 lines, ZERO sorries,
zero errors, zero warnings; 27 AxCheck footer lines).  **Axiom fence exactly as
designed:** §1 (partition), §3 (pins/purity/reconstruction/corner), §4 (cell reading +
α-box transport + box count), §5 (both axis instruments), §6 (recentred wiring), the
two law DEFINITIONS, `zcURLim_powerInv`, and ★ **the fire `powerSectorLaw_of_rebase`
itself** are all pure Lean core `{propext, Classical.choice, Quot.sound}`; the B.42
cite (`Uniformity.Density.Leaf.exists_slope_factorization`, owner-signed gate-(b))
occurs ONLY in §2's proper refinement/majorant, `powerDefect_nonneg`,
`powerLaws_unramified` (through IFCG33's forcing), and the two census wrappers
(through IFCG35's front, which already carried it).  The C.33 cites do NOT occur.
One-line aggregator import added to `Uniformity/ChapI.lean` after IFCG43 (IFCG42/45
lines are other units'; their files untouched).  No git ops.
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG44.lean`
(10 increments, each GREEN before the next; final: zero diagnostics); targeted
`lake build Uniformity.ChapI.IFCG44` GREEN (8957 jobs); aggregator
`lake env lean Uniformity/ChapI.lean` GREEN with the line wired.

## ★★★ THE HEADLINE — the fire and the new census position

    theorem powerSectorLaw_of_rebase :        -- ★★ THE FIRE (Lean-core!)
      0 < m → ∀ σ, (< m decided value laws) →
        PowerConvolutionDefectLaw m σ → PowerFullSpanLaw m σ → PowerSectorLaw m σ
    theorem decidedSliceAt_all_of_rebased :   -- ★★★ the front, PowerSectorLaw GONE
      (split laws) → (power defect laws) → (power full-span laws) → (leaf laws) →
        (five e = 4 laws) → ∀ n, DecidedSliceAt n
    theorem decidedSliceAt_all_of_defects :   -- ★★★ + IFCG38's split re-base consumed
      (SPLIT defect laws) → (power defect laws) → (power full-span laws) →
        (leaf laws) → (five e = 4 laws) → ∀ n, DecidedSliceAt n

`PowerSectorLaw`'s statement is IFCG35's, byte-untouched.  All law-family premises are
in the front's own descent shape (each mass receives the `< e` value laws; e ≥ 5,
σ ramified, Witnessed).  **Census position (exact):** the all-degree decided slice now
rests on {`SplitConvolutionDefectLaw` (or `SplitSectorLaw`), `PowerConvolutionDefectLaw`,
`PowerFullSpanLaw`, `LeafSectorLaw` (its cell count), the five `e = 4` even-ram
remainder laws} — the charge's ideal set plus the two power residues in place of
`PowerSectorLaw`, exactly parallel to SSL's split re-base.

## ★★ THE STRUCTURAL DISCOVERY (what made item 1 land cite-free)

`pureFaceSet` removes only the `e' = m` spanning boxes, so the power sector's unique
minimal face `(h, e')` spans either ALL of `[0, m]` (`e'·deg(residual) = m` — the class
is PURE, `k ≥ 2`, and NO `O`-level mass drop exists: THE fractional-recentring
territory) or a proper top segment — where the face factor splits off and BOTH factors
drop mass, so the `O`-level convolution descent (IFCG38's own table `convCount`)
applies verbatim.  Machine-checked as `powerSector = powerSectorFull ⊔ powerSectorProper`
(`powerSector_eq_full_union_proper`, `full_proper_disjoint`,
★ `powerSectorCount_eq_partition` = full + properVis + properInv, exact at every level).
Consequence: **on the full-span part the lift IS the face factor** — no B.42, no corner
gate; the whole item-1 assembly there is Lean-core.

## The three charge items, disposition

**(1) THE FACE-INDEXED ASSEMBLY — LANDED, two halves.**
* Proper half (B.42 through XHS with the TRIVIAL coprime pair `(ψ^k, 1)` — `H = 1`
  makes `wideFace_refinement_of_stratum` extract the single pure face factor):
  ★ `powerSectorProper_refines` (every lift factors `g·R`, `g` monic `(h,e')`-pure of
  degree `e'·k·deg ψ` with residual EXACTLY `ψ^k`, pinned corner height), ★
  `powerSectorProper_refines_decided` (a `mulClass` of two DECIDED strictly-smaller
  masses at types summing to σ), ★ `card_powerSectorProperVis_le ≤ convCount`
  (IFCG38's table, shared!), `card_powerSectorProperInv_le ≤ q^((m−1)(M+m))`.
* Full-span half (Lean-core): ★ `fullSpan_pins` (`sideMin = 0`, `sideDeg = D`,
  `H₀ = h·D`, canonical residual = the lift's side residual — the PSL3-item-1 ℕ∞
  bookkeeping), ★ `fullSpan_raw_dvd` (`π^(⌈h(m−j)/e'⌉) ∣ coeff j` — exactly
  `resPoly_eq_pow_iff_box`'s purity hypothesis at `h = 1`), ★ `minFaceAt_of_lattice`
  (the RECONSTRUCTION: lattice + exact corner ⟹ `MinFaceAt` — the ⟸ of the cell
  description), `fullSpan_corner` (`resOrd(c₀) = h·D` exact).

**(2) THE GENERAL-(h,d) AXES — the two axes landed as instruments; the lattices'
mixed/compositum half honestly open.**
* ★★ `fullSpan_resPoly_iff_box` — THE CELL READING at the landed frame `(1,1)`:
  full-span class at face `(1, e')` has residual `(X − z̄)^D` ⟺ every lift's
  `eisKey`-transform lies in the deep recentred box over `O' = AdjoinRoot(eisKey π (−z) e')`
  (PSL3's transfer heart fired on the sector's own data);
  ★ `cellTransport_mem_alphaBox_iff` — the transported class lies in the new
  `alphaBox` (`e'(D−t)+1 ≤ resOrd(b_t)`) ⟺ the lift box (so with PSL3's
  `cellTransport_card_image` the piece's count transports to `O'` exactly);
  ★ `card_alphaBox = q^(Σ_t (e'N − e'(D−t) − 1))` — the box count is an exact
  `q`-power at the BASE `q` (the free-coordinate supply for the discharge).
* ★★ `xres_eq_pow_iff_digits_h` — THE `(h,1)` AXIS, ring-free: at general slope
  numerator `h` under the side pins, `xres = (X − z̄)^D` ⟺ the `D` lattice digits at
  heights `h·(D−t)` read the binomial expansion (recovers PSL3's `h = 1` instance).
* ★ `zcURLim_compositum_value` — THE `(1,d)` AXIS consumption: any uniform law
  instantiated at LEG 4's compositum ring keeps its rational pair, evaluated at
  `q^{deg φ}` (the `q ↦ q^d` reindex; Eisenstein stage leaves `q` fixed).
* **Genuine obstruction, stated exactly:** at `h > 1` the key ring
  `AdjoinRoot(X^{e'} − z·π^h)` is NOT a DVR (e.g. `x² − π³`: the maximal ideal
  `(π, α)` is not principal — the integral closure strictly contains the order), so
  the `(h,1)` O'-ring/box transport cannot replay `eis_root_pow_dvd_mk_iff` verbatim;
  the digit criterion above is the ring-free content that DOES replay.  The surviving
  general-(h,d) set: {the `(1,d)` coordinate lattice + box criterion over the
  compositum (`d ≥ 2`), the `(h,1)` ring-side transport (`h ≥ 2`), the mixed case}.

**(3) THE RECENTRED-MASS INDUCTION WIRING — the instruments landed; the one missing
leg named.**  ★ `recentred_decidedSeq_tendsto`: a `DecidedValueLaw k τ` yields ONE
rational pair with `decidedSeq O' k τ (φ M) → n(q)/d(q)` at every Eisenstein
recentring ring `O'` and every diverging level reindex `φ` (`q' = q` via
`eis_residueCard`); `tendsto_transport_level` supplies `φ = M ↦ e'·(M+m)`;
`ZcURLim_sum`/`zcURLim_eis_value` stand ready.  What blocks the UNCONDITIONAL
`PowerFullSpanLaw`: **the DECISION transport across the recentring** (`DecidedAt` over
`O` at a full-span pure class ⟺ `DecidedAt` over `O'` of the transported class at the
`e'`-rescaled type — the OM tower step; C136's territory).  Not in the corpus; now the
full-span law's precisely-supplied discharge target.

## The two named laws (both consumed, both nonvacuous)

    def PowerConvolutionDefectLaw m σ : Prop :=   -- ZcURLim((conv − #properVis)/q^{m(M+m)})
    def PowerFullSpanLaw m σ : Prop :=            -- ZcURLim(#full/q^{m(M+m)})

`powerDefect_nonneg` (a genuine overcount, never a signed fudge);
`powerLaws_unramified` (at unramified σ both parts are EMPTY by UZL's forcing — the
defect is the full convolution table, the full-span family is 0).  Discharge
territories: the defect = the image description of the proper refinement (the SAME
polygon-factorization-uniqueness converse as IFCG38's split defect — one mechanism,
two consumers); the full-span law = the decision transport above, against §4's
two-way cell reading + count transport + §6's instruments + `powerSector_mass_drop`
(recentred mass `≤ m/2`).

## File map (`leanfinal/Uniformity/ChapI/IFCG44.lean`, 1344 lines)

§0 kit (private replicas: `isKey_X`, `mem_sideSet_iff'`, `resPoly_rep`) ·
§1 `powerSectorFull/Proper(+Vis/Inv)`, ★ the partition (3 thms) ·
§2 ★ `powerSectorProper_refines(_decided)`, ★ the two majorants ·
§3 ★ `fullSpan_pins`, ★ `fullSpan_raw_dvd`, ★ `minFaceAt_of_lattice`, `fullSpan_corner` ·
§4 ★★ `fullSpan_resPoly_iff_box`, `alphaBox`, ★ `cellTransport_mem_alphaBox_iff`,
★ `card_alphaBox` · §5 ★★ `xres_eq_pow_iff_digits_h` (+ private general-`h` read),
★ `zcURLim_compositum_value` · §6 ★ `recentred_decidedSeq_tendsto`,
`tendsto_transport_level` · §7 the two law defs, `powerDefect_nonneg`,
`zcURLim_powerInv`, ★ `powerLaws_unramified`, ★★ `powerSectorLaw_of_rebase` ·
§8 ★★★ `decidedSliceAt_all_of_rebased`, ★★★ `decidedSliceAt_all_of_defects` ·
AxCheck footer (27 lines).  Imports: `IFCG38` + `IFCG43` (transitively IFCG35/37/39
etc.).

## Repair log (5 error rounds over 10 increments; every statement landed as designed)

1. `npHeight_coe` lives in IFCG24, not IFCG22 (open-list fix).
2. `Polynomial.natDegree_pow` over `resField X` needs the field instance — the
   established `letI := instFieldResField isKey_X` idiom.
3. THE DEPENDENT-REWRITE TRAP (PSL3's logged #5, avoided on second contact):
   `rw [← hfull] at h1` with `hfull : e'·D = m` hits the `Fin m` index of the
   coefficient vector — rewrite the ℕ exponent equality alone and `rw` THAT.
4. `simp only at h1` after a rewrite that already beta-reduced — "no progress"; drop.
5. `obtain ⟨-,…⟩` on `compositum_recentring_stack`'s ∃-instance pack: the later
   components' TYPES depend on the instance binders — name them (`⟨i1, i2, i3, i4, …⟩`),
   never discard.
   Plus lint: an unused `0 < D` hypothesis on `minFaceAt_of_lattice` was DROPPED
   (statement strengthened — `D = 0` contradicts `hm0` through `hfull`).

Traps avoided by design (IFCG39/43/35 logs consulted): every `e'·(…)` product kept
out of omega via `generalize` atom pins; the ℕ∞ extraction by the recorded
`nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_inj` chain; `sideMin/sideMax`
entered only through `mem_sideSet_iff'` + `min'_le/le_max'`; the ceiling division by
`Nat.div_lt_iff_lt_mul` + product-atom omega.

## Consumption notes for the discharge units

* The full-span law's discharge shape: partition `powerSectorFull` by `(e' ∣ m, e' ≥ 2)`
  (uniqueness by `minFaceAt_unique`) and centre; at `(h,d) = (1,1)` faces read cells
  through `fullSpan_resPoly_iff_box` → `cellTransport_mem_alphaBox_iff` →
  `cellTransport_card_image`; the decided intersection is the ONE missing transport;
  then `recentred_decidedSeq_tendsto` at `φ := tendsto_transport_level` + `ZcURLim_sum`
  over the divisor faces.  Mind the sign convention: criterion at `eisKey π (−z) e'`,
  residual root `z̄` (PSL3's note).
* The defect law's discharge is the SAME converse as `SplitConvolutionDefectLaw` —
  the polygon-block Hensel-uniqueness genre; one unit can plausibly close both.
* `minFaceAt_of_lattice` + `fullSpan_corner` + `minFaceAt_min` give the full-span
  piece as an EXACT coordinate-condition set — the honest starting point for any
  bijective count.
