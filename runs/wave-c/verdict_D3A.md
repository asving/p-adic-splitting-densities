# UNIT D3A verdict — μ₄ operator stack base: D3-00 / D3-01 / D3-02

Date: 2026-08-28 · Blueprint: `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md` §6.2
rows D3-00/01/02 · File: `leanfinal/Uniformity/ChapC/C136d0.lean` (new, 52 declarations)

**Verify:** `lake env lean Uniformity/ChapC/C136d0.lean` — exit 0 in ~10 s, zero errors,
zero warnings, zero `sorry`.  AxCheck footer: all 52 declarations print
`[propext, Classical.choice, Quot.sound]` (Lean-core only; no cite, no new axiom).

## Per-row status

### D3-00 support shell — PROVED (parameter-free)

Defined the `g8`-development support layer one level above C.11, mirroring the
`dv2Hgt/dv2Pin/dv2Supp` shape: `dv3Hgt L Ψ₂ u₂ ℓ₂ A := dv2Supp L Ψ₂ A u₂ ℓ₂` (the inner
read IS the level-2 support — anti-drift pin `dv3Hgt_eq_dv2Supp`), `dv3Pin` (heights of
`dev Ψ₃` digits), `dv3Supp` (the cleared `inf`).  Laws, each the C132nv0 statement one
level up, proved by the same arguments with C132nv0's own `dv2Supp` bank as the inner
facts: `dv3Pin_top_of_gt`, `dv3Supp_zero_eq_top`, `dv3Supp_eq_inf_range`,
`dv3Supp_ne_top_of_ne_zero`, `min_dv3Supp_le_dv3Supp_add`, `dv3Supp_neg`,
`dv3Supp_add_eq_of_lt`, `dv3Supp_add_eq`, plus the four `dv3Hgt` shims (zero / ne-top /
ultrametric / equality-off-ties).  Generic over any `(L, Ψ₂, u₂, ℓ₂, Ψ₃, u₃, ℓ₃)`; no S2
numeral.  Because `LevelDatum` bundling stops at level 2, the inner hypotheses
(`hΨ₂ : Ψ₂.Monic`, `hΨ₂d`, `hℓ₂`) are threaded explicitly — documented in the header.

### D3-01 μ₄ value — PROVED (S2 numerals `(u,e) = (85,2)`)

`s2Hgt₄ g := toZ (dv3Supp L Φ₂ 21 2 g₈ g 85 2)` at the same level datum `s2Hgt₂/s2Hgt₃`
read.  Pins: `s2Hgt₄_eq_dv3Supp` (shape), `s2Hgt₄_zero`, `s2Hgt₄_ne_top`,
`s2Hgt₄_add_ge`, `s2Hgt₄_add_eq`, and the tower-height tooth **`s2Hgt₄_g8 :
s2Hgt₄ g₈ = 85`** (9-slot inf computation; inner reads from Part-1 `dv3Hgt_zero` and
M3-NV5's landed `s2Hgt₃_one_eq_zero`).  C136t consumed: `s2g8_eq_keyChain_three` ties the
development key to the T2 chain's `keyAt 3` (`s2DepthThreeKeyAt_three`), and
`s2Hgt₄_eq_keyChain_dev` / `s2Hgt₄_keyChain_three` restate table and tooth at the
`s2DepthThreeKeyChain` slot for the chain-level D3 consumers.  Fleet lesson heeded: no
bare `rfl` against composed-key internals — the key tie goes through C136t's landed
`if_pos` pin.

### D3-02 endpoint/minimizer — PROVED (one explicit hypothesis, `Dv3ResSurv`)

Full port of C132nv2 one level up: `Dv3OnSide`, `dv3SideSet`, `dv3SideMin`, membership /
leftmost / off-side lemmas, **`dv3OnSide_endpoint_unique`** (the unique lowest convolution
pair), support bounds (`dv3Supp_le_term`, `le_dv3Weight`, `lt_dv3Weight`), the term
estimates (`le_line_dev3_term`, `lt_line_dev3_term`), the universal `≥` product law
(`dv3Supp_add_le_dv3Supp_mul`), and the endpoint assembly
(`dv3Supp_mul_of_endpoint_le`, **`dv3OnSide_mul_endpoint`**, `dv3SideMin_mul_le`,
`dv3Supp_mul_eq_add_of_endpoint_le`).  `Dv3ResSurv` (μ₃-residual survival for `Ψ₃`-digit
products, the exact `Dv2ResSurv` shape one level up) is the ONE explicit premise —
honestly NOT discharged here: that is row D3-03's genuine new core, superseded by the
[DWR] §11.7 L2E shared engine.  No unconditional μ₄ product law is claimed.

## Deviations / notes

* **One file for three rows** (recorded per the unit brief): §5's naming discipline names
  declarations, not files; the three rows are one dependency chain and land as one unit,
  exactly as C132nv0/nv1/nv2 did one level down.
* New helper restatements (anti-drift, no new mathematics): `s2g8_monic`/`s2g8_natDegree`
  (M3-RP10's landed facts at the `g8` spelling — same pattern as C136t's key pins).
* Untouched: `C136l2e0.lean`/`C136l2e1.lean` (codex unit), all landed and leanspec files.
* Downstream consumers now unblocked: D3-03 (discharge `Dv3ResSurv` at `(g8, 85, 2)` via
  L2E), D3-04 (`s2Hgt4_mul` from `dv3Supp_mul_eq_add_of_endpoint_le` + survival), D3-05
  (valuation/grades over `s2Hgt₄`), T4's deferred μ₄ exact-grade supply (grade `170`).
