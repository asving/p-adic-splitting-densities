# Verdict — unit DEC2 (DECOMPOSER: the af′ reverse triangular-digit blocker → node plan)

Date: 2026-08-25. Deliverables (the only repo files written by this unit):
`docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md` (the plan) and
`leanfinal/scratch/DEC2_check.lean` (the elaboration check). No git commit.

## Design decision: the pointwise `TriangularDigitRead` is SUPERSEDED — DERIVABLE route

The C.53-sized blocker of `verdict_C131ae.md` §C.131af′ dissolves against the post-landing
corpus. Three checked facts do it (all pinned by `rfl`/elaboration in `DEC2_check.lean`):

1. **`dv2Hgt (T.levelDatum hπ) = dvSupp F · T.u₂ T.e₂` and `dv2Pin = dv2Hgt ∘ dev` are
   `rfl`** — C.131w′'s two direction-agnostic ledgers (`towerLocus_entry_floor`,
   `dv2Hgt_dev_floor`), built for `shadow_floor` AFTER the C131ae verdict was written,
   already transport locus side data onto every two-key digit at cost `jE₂`. That is the
   reverse correspondence in FLOOR form; only a `+1` strictness increment is missing,
   and `budgetFloor` is arithmetically EXACTLY `⌈((μ₂−j)E₂ + 1 − w)/e₁e₂⌉` (checked).
2. **The `+1` needs no digit dictionary.** Set `g := f − Φ₂^{μ₂}`. Both `f` and the
   landed reference `Φ₂^{μ₂}` (C.131ac′, the cite's single entry point) are locus members
   with the SAME residual `towerLabel^μ₂`, hence equal ϖ-reads at every lattice point;
   `dev` is `O`-linear and reads are additive at a common floor
   (`C130rp2.twistRead_add_of_le`, generic), so every on-line read of `g` is `0`; C.26's
   public `natDegree_dvResPoly` (nonzero left-endpoint coefficient) then forbids `g`
   having any on-line abscissa: `dvSupp g ≥ μ₂E₂ + 1` STRICT. `dev_sub` + `dev_pow_self`
   + `dv2Hgt_dev_floor` push this to `(μ₂−j)E₂ + 1` per digit — which is ALSO C.54(c)'s
   node floor (strict form), unblocking C123's deferred node-floor rows as a corollary.
3. **Faithfulness:** the signed `towerLocus_iff_budget` (leanspec ChapC.lean:2030) is
   proved byte-identically, `←` = the frozen landed `mem_towerLocus_of_budget`; the old
   TriangularDigitRead's base-ψ₂-uniqueness content is absorbed into (reference residual
   from the declared C66b cite) + (C.26 endpoint nonvanishing); C.53b's measure transport
   is never used pointwise (per the v2 doc's prohibition).

## The node plan (in the plan doc, §3)

Five Sonnet units, 30–45 min each, three files: U-SIDE ∥ U-ARITH (locus side-data pins +
ceiling arithmetic; Lean-core), U-HEART (`towerLocus_read_eq`, ★`dvSupp_sub_composedKey_pow`,
★`towerLocus_dev_strict_floor`), U-ASSEMBLE (★`budget_of_mem_towerLocus` = NODE C.131af′,
★`towerLocus_iff_budget` = C.131ag′), U-FEED (`C123r2.lean`). Each brief carries named
landed inputs and a step-scripted proof; footprints Lean-core except the declared
`fgmn_dv_exact_mul` inheritance from `composedKey_pow_mem_towerLocus` (disclosed per node).

## Feeding C123R — one witness, one honest finding

* U-FEED constructs the missing non-drain witness: `f₀ = Φ₂³ + π⁶xΦ′ ∈ towerLocus s2Tower 3`
  via `mem_towerLocus_of_budget` (explicit `hbud`, sub-top digit at finite height 31 = Θ₀).
* **Finding:** af′'s strict floor equals `Θ_j` exactly when `margin = 1` — and BOTH landed
  towers have margin 1 — so `shadow_faithful_band`'s window `m < Θ_j` is PROVABLY empty on
  the locus there (`towerLocus_band_window_empty`, planned). The landed band statement
  (C131y.lean:559) requires locus membership, so the only live-band route is a NEW
  `margin ≥ 2` tower instantiation (e.g. `(e₂,f₂,u₂) = (2,1,7)`, margin 3) — booked as
  follow-on. C123R's gap was not a missing witness but a provable emptiness.

## Verification

`cd leanfinal && lake env lean scratch/DEC2_check.lean` — exit 0, zero errors, zero
warnings, no `sorry`, no `axiom` (both tokens appear only in comments). Part 1 pins 30+
consumed landed declarations at the plan's claimed types (including the five `rfl`
bridges and the C.26 coefficient-extraction two-liner PROVED outside C26.lean); Part 2
elaborates all 14 planned signatures (`SIG_AF1a`–`SIG_AF7c`). No leanspec/, Uniformity/,
or roll-up file touched.
