# Verdict — unit NV3: S2-source plan node NV-3 (CORE 2/4 of the level-two product law)

Date: 2026-08-24 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §4, §6 row NV-3.
File created (the ONLY file touched): `leanfinal/Uniformity/ChapC/C130nv3.lean` (18 public
declarations; not added to any roll-up, per the NV01/NV2 precedent).

## The charge, and how it was met

NV-2 left ONE owed input: `hup : dv(dev (g·z) (jg+jz)) ≤ Hg + Hz` — the unique lowest
convolution term SURVIVES residual cancellation.  Proved in two halves:

* **Generic half** (`stageHeight_dev_endpoint_le_of_surv`, any frame, strict admissibility
  `ℓ·dv(Φ′) < u`): double development of `g·z` (NV-2's convolution pattern), endpoint pair
  split off via `Finset.add_sum_erase` + `dvOnSide_endpoint_unique`; the endpoint term IS
  `(dev g jg · dev z jz) %ₘ Φ′` (`dev_mul_pow` at carry 0 + `dev_zero_pin`); every other
  term prices at `Sg+Sz+1` (`lt_line_dev_term`), so the remainder sum sits at height
  `≥ Hg+Hz+1` (`le_weight_stageHeight_sum` + `succ_le_of_weight_succ_le`); the
  equality-off-ties ultrametric (`suppVal_add_eq`) then reads the digit off the endpoint
  term — MODULO one hypothesis `hsurv`: survival of the endpoint term itself.

* **S2 survival core** (`s2_stageHeight_mul_modByMonic_le`): at the S2 frame
  (`Φ′ = x²−2`, `(e₁,h) = (2,1)`), `dv((a·b) %ₘ Φ′) ≤ dv(a) + dv(b)` for `a, b` of degree
  ≤ 1, universal (zero cases ride `⊤`).  This is FGMN's `ψ ∤ R(a)R(b)` collapsed to
  PARITY: `dv(a) = min(2v(a₀), 2v(a₁)+1)` has one even and one odd branch, so the
  attaining slot is unique; the explicit remainder
  `(a₀b₁+a₁b₀)·x + (a₀b₀ + 2a₁b₁)` (`s2_mul_modByMonic`, by `div_modByMonic_unique`)
  keeps the product value in each of the four parity cases — in the odd×odd case through
  the CARRY (`x² ≡ 2` transfers the value onto `2a₁b₁` exactly; this is the genuine
  cancellation threat, compensated).

## LANDED (18 declarations, all `#print axioms` = Lean core, machine-checked)

* `s2_endpoint_dev_le` — ★ NV-2's `hup`, unconditional at S2 (the row's charge).
* `s2_dvSupp_mul` — ★ **NV-4's row LANDED**: `dvSupp (g·z) 5 2 = dvSupp g 5 2 + dvSupp z 5 2`,
  no monic/pure/degree fences, all zero cases.  `s2Hgt₂_mul` — carrier form
  (`WithTop ℤ` table).  NV-4's unit should CHECK this row off and consume these.
* Assembly discharge of NV-2's whole conditional bank: `s2_dvOnSide_mul_endpoint` (the sum
  of chosen minimizers IS a product minimizer), `s2_dvSideMin_mul_le`.
* Infrastructure now public: `s2_stageHeight_linear` (two-slot parity read),
  `s2_mul_modByMonic`, parity extractors `coe_le_of_two_nsmul_le` /
  `coe_succ_le_of_two_nsmul_le`, ultrametric upper reads `addVal_add_le_left/right`,
  `dvSideMin_le_natDegree`.
* Teeth (all three parity genres through the NEW law, matching hand computation):
  `h₂(x·x) = 4` (odd×odd, carry transfer), `h₂(Φ′·Φ′) = 10` (even×even),
  `h₂(x·Φ′) = 7` (mixed; independently reproduces NV-2's regression value).

## Not claimed (honesty)

The GENERIC survival core is NOT proved — it enters the generic theorem only as `hsurv`.
It genuinely needs the frame's residual irreducibility (`hresirr`): with a reducible
residual (slope-1 side, key `x²+4`, residual `(y+1)²`, `a = b = x+2`) the endpoint term
cancels (`dv(4x) = 3 > 1+1`) — that configuration violates ONLY `hresirr`, so the
faithful generic route is B35c/B43's `resPoly_mul_*` + `hresirr` (future work, not S2's
need).  C131k (named row input) was inspected but not needed: NV-2's B39a-based
convolution pattern already carries the expansion.

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130nv3.lean` — CLEAN (exit 0, 0 errors,
0 warnings, 0 sorry); 18 `#print axioms` rows ALL `[propext, Classical.choice, Quot.sound]`
(machine-checked by script over the joined output).  `lake build Uniformity.ChapC.C130nv3`
— success (8738 jobs; olean available to successors).  No git commit (per brief); only
file touched is `C130nv3.lean` (+ this verdict).
