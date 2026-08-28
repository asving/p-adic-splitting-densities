# UNIT A24A verdict — A-C.24 adjudicated: NOT ENACTED as drafted; the amendment fork changes (2026-08-28)

**Charge:** adjudicate the F1.4/C.39 signed root factor per the L2E1/L2E2/L2E3 binding
correction; if the root power is unsuppliable, enact A-C.24 (re-sign C.39 to the clean
normalized `γg` scalar) and land the repaired F1.4 + F1.5 in `C136f14.lean`.

## STATUS FIRST

| charge item | status | result |
|---|---|---|
| 1. verify the root-power defect | **CONFIRMED, with a genre refinement** | the signed root power is genuinely unsuppliable on the implemented normalized read (L2E1's machine diagnostic stands; independently re-derived from the source chain EFF.HE6R1.13 → .35 → .39). The precise genre: the source's cocycle is CORRECT for the source's own PIN-ANCHORED read; the signed Lean carrier `dv2ResPoly`/`dv2Res` implements the per-slot OWN-HEIGHT (bare) read, on which products are cocycle-free (`C136l2e1.dv2Res_mul`, machine-checked). |
| 2. enact A-C.24 (re-sign to `γg` alone) | **NOT ENACTED — record-and-stop clause fired** | the drafted repair target is ALSO refutable-in-mechanism: `dv2ResPoly`'s off-side lattice coefficients are unguarded own-height reads (the level-2 crank dropped C.25/C.26's fixed-grade junk-0), so NO constant-scalar polynomial law can hold over the current carrier. Machine diagnostic landed (scalar-generic). leanspec is byte-untouched by this unit. |
| 3. land repaired F1.4 + fire F1.5 | **BLOCKED-BECAUSE** (both candidate forms) | normalized form: false at off-side slots (diagnostic below) and uncertified at on-side slots (the mod-`Ψ` reduction anchor-shift risk, §5); absolute/anchored form: the required product law is the RECORDED-UNPROVEN `C136l2e2.Dv2FullReadCarryLawStatement` (a `def`, no theorem inhabits it) and the anchored polynomial object does not exist in leanspec. `C136f14.lean` instead lands the machine diagnostics + witnesses, exit 0, Lean-core. |
| 4. gates | **PASS on everything touched** | new file `C136f14.lean` exit 0, all 7 declarations `[propext, Classical.choice, Quot.sound]` only (no `exists_dvDissection`). leanspec untouched; `Leanspec/ChapC.lean` re-elaborated as a health check (see footer). No landed file edited; no git op; `C136l2e*.lean` untouched. |

## 1. The root-power adjudication (charge item 1): (a), CONFIRMED

Machine evidence, independently verified in source:

* `C136l2e1.dv2Res_mul` (landed, Lean-core): `dv2Res L (A*B) = dv2Res L A * dv2Res L B`
  for nonzero factors — the normalized read's product law is CLEAN, no root factor
  (the `AdjoinRoot.mk` image of `C133mh3.dvResPoly_mul_gen`, whose C.22 twistRead carries
  the inverse twist that absorbs the anchor bookkeeping under MULTIPLICATION).
* `C136l2e1.root_cocycle_eq_one_of_twist_shape` (private, checked): the L2E-00 twist
  shape on the normalized read forces `AdjoinRoot.root L.r ^ L.cocycle ka kb = 1` — no
  supplier, false for a nontrivial cocycle. L2E3's F1.4 audit transposes the same
  cancellation to the signed complement scalar, leaving exactly
  `root ^ L.cocycle (pinHeight …) (complementConst …) = 1`.

Source chain (spec/EFF-HE6R1.md): `.13`'s CHAIN paragraph → `.35` (PE2 F-2) → `.39`
(PE3 F-1, TERMINAL). The TERMINAL derivation normalizes each side by
**`n₂(m₁)·Ψ(ξ)^{j₁}` — the pin-anchored absolute normalizer** — and the cocycle
`β^{c₁(m₁^{f_S}, c_g)}` arises from composing absolute normalizers:
`n₂(a)·n₂(b) = τ₂(a,b)·n₂(a+b)`. So **the source genuinely demands the root power — for
the source's own anchored read**. The Lean signer transcribed the source conclusion onto
the bare-read carrier, where the anchor carry is already cancelled: that is the defect,
and it is the charge's fence-error genre (a) at the carrier level. The machine already
knows the anchored/bare dichotomy: `C136l2e2.dv2Pin_dv2SideMin_mul_with_carry` proves
`L.ℓ * L.cocycle Mg Mz = L.shift Mg + L.shift Mz - L.shift (Mg + Mz)` — the cocycle IS
the non-additivity of the anchor base, and it belongs to the absolute read
(`dv2FullRead`), exactly as L2E2 recorded.

## 2. The fork-changing finding: the drafted repair is also refutable

`dv2ResPoly` (C.38a (g), leanspec `ChapC.lean:1695`) sums `dv2Res` reads over ALL
lattice slots `dv2SideMin + t·ℓ₂`, `t ≤ dv2SideDeg`. At level 1 the residual polynomial
is FIXED-GRADE: `dvResPoly`'s coefficient `t` is `twistRead (M₀ - t*u)` (C.25,
leanspec:837), and C.26 (`dvResPoly_coeff_eq_zero_iff`) pins coefficient `= 0` iff the
slot is off-side. The level-2 crank replaced `twistRead` by the own-height total read
`dv2Res` and **dropped the off-side junk-0 guard**: an off-side lattice slot (interior
slot of the side strictly above the line — nothing in the row's hypotheses excludes it)
contributes the digit's OWN nonzero residue instead of `0`.

Consequence, machine-checked in `leanfinal/Uniformity/ChapC/C136f14.lean` (exit 0,
Lean-core):

* ★ `dv2ResPoly_scalar_shape_digit_kill` — **scalar-generic**: IF
  `dv2ResPoly L Ψ f u₂ ℓ₂ hne = C c * dv2ResPoly L Ψ (blockFactor L f) u₂ ℓ₂ hne'` for
  ANY constant `c : AdjoinRoot L.r`, THEN at every in-range lattice slot where the
  block's `Ψ`-digit vanishes, `f`'s `Ψ`-digit is forced to vanish
  (`dev Ψ (blockFactor L f) (min' + t·ℓ₂) = 0 → dev Ψ f (min + t·ℓ₂) = 0`; the engine
  supplies `dv2Res 0 = 0` on the right and the degree-fence nonvanishing
  `C134p1d.not_residual_dvd_of_natDegree_lt` on the left). Instantiations landed for
  BOTH the drafted `γg` scalar and the signed `γg·root^cocycle` scalar — so the
  off-side channel refutes the SIGNED row too, independently of the root-power
  obstruction.
* `dev_witness_block_digit_zero` / `dev_witness_product_digit_one` — the forced transfer
  is absurd as a mechanism: for any monic `Ψ` with `0 < deg Ψ`, the block-shaped
  `b := Ψ² + X^(deg Ψ − 1)` has `dev Ψ b 1 = 0` while `dev Ψ (b·X) 1 = 1`.
  (Caveat, stated honestly: a fully in-frame refutation instance additionally needs a
  `BlockContext`/test-key instantiation with this digit shape — not constructed here.
  The unprovability case does not need it: no hypothesis of the row constrains the
  off-side digits, and the diagnostic shows every proof would have to.)

## 3. The consumer check (charge 2 sub-item)

* Repo-wide (`rg dv2ResPoly_scalar` / `C.39`): **no landed proof consumes the axiom**;
  all leanfinal hits are BLOCKED-record comments (C134cfs/C134frt/C134f12c/C38a docs).
  `C136l2e3.dv2ResPoly_radical_eq_of_scalar` takes the scalar identity as a PREMISE.
* Blueprint dependents: C.68 consumes only the side-geometry half (per C38a's split).
  C.77's SIGNED Lean conclusion (monic `C_M` + block degree) does not mention the
  residual scalar — the γ_g clause is prose routed through C.38/C.39.
  **C.79 is the binding consumer**: the μ₂* = 2 decision table's `inertQuadratic`/`split`
  rows test roots/irreducibility of the (γ-scaled) quadratic residual. With the
  UNGUARDED `dv2ResPoly`, the quadratic's middle coefficient at an off-side interior
  slot is junk (own-height read) instead of the classical `0` — the root test would be
  wrong. **The consumers need the CLASSICAL (guarded, anchored) object.**
* The absolute-read side: `dv2FullRead` (C136l2e0) is the anchored read
  (canonical base `L.shift k`), with additivity landed (`dv2FullRead_add_of_le`) but its
  cocycle product law only RECORDED (`Dv2FullReadCarryLawStatement` is a `def`; no
  theorem inhabits it).

## 4. What A-C.24 must become (the redesign draft, for the next unit)

The defect is one layer below C.39's conclusion: **the C.38a residual half
(`dv2Res`-based `dv2ResPoly`) is not the classical level-2 residual polynomial** — it
lacks (i) the off-side junk-0 guard (C.26's level-2 analogue) and (ii) the per-slot
line-anchor normalization (the level-2 analogue of C.25's fixed-grade `twistRead`).
Recommended A-C.24′ shape:

1. Introduce the CLASSICAL guarded/anchored level-2 residual polynomial (new def beside
   C.38a, leanspec + leanfinal; the landed `dv2FullRead`/`C134p1d.lineRes` technology is
   the right basis — `lineRes_eq_shift` already proves `lineRes = R(z)·X^δ`, i.e.
   anchored = bare × root-power, and `lineRes_add` + `line_read_eq_zero_of_not_onSide`
   give the additivity and the off-side 0 for free).
2. Re-sign C.38 and C.39 OVER the new object. Over the anchored object the SOURCE's own
   conclusion shape (γ_g times the `c₁` root power, PE3 F-1's pin-height exponent) is
   the faithful form — i.e. C.39's signed conclusion likely survives nearly
   byte-unchanged once the carrier is repaired; alternatively the normalized-carrier
   route needs an on-side-quantified per-slot law (see §5's open risk first).
3. `dv2ResPoly` (bare) stays as-is — landed C136l2e3 lemmas keep compiling; no landed
   file edit is needed; C.104's `repoRead := dv2Res` is untouched (it consumes `dv2Res`,
   not the polynomial).
4. The F1.4 landing then needs the anchored product law at the complement
   specialization — the honest supplier chain: the exact digit split
   `dev Ψ (b·g) j = Σ_{i≤j} dev Ψ (dev Ψ b i · g) (j−i)` (additivity of `dev` +
   `dev_mul_pow`), strict off-pair pricing (landed L2E-05/07 banks +
   `dv2SideSet_eq_singleton_zero_of_not_muDvd`), the perturbation law
   `C133mh0.dv_resPoly_add_of_lt` (general, landed), and the mod-`Ψ` reduction read
   (§5).

## 5. The on-side risk record (identified mechanism, NOT machine-certified)

Even on-side, the per-slot comparison runs through the slot-0 reduction
`dev Ψ (b_j·g) 0 = (b_j·g) %ₘ Ψ`. At a μ₁-value TIE (`dvSupp(Ψ·q) = dvSupp(b_j·g)`,
allowed by the landed sharp bound), the subtraction of the `L.r`-divisible line vector
(`lineRes(Ψq) = L.r·R(q)·X^k` via `dvResPoly_mul_gen` + `C131aa.dvResPoly_testKey`) can
in principle cancel the digit's own level-1 side-min read, shifting the digit's OWN
anchor — and bare reads at shifted anchors differ by a root power
(`C134p1d.lineRes_eq_shift` makes this exact). Classically this is invisible (the
anchored read is reduction-stable: `mk L.r` kills the whole `L.r`-multiple, no anchor
bookkeeping); for the BARE read it is an open per-slot obstruction. Either the shift is
excluded for `short × complement` products (then the on-side normalized γg law is
provable), or it is realizable (then only the anchored form survives). The
`C134p1d.lineRes` private bank (`lineRes_add`, `lineRes_eq_shift`,
`residual_dvd_left_of_tie`) is the exact toolkit for deciding this; per the
examples-first directive, a small numeric battery at the S2 tower would decide it
fastest.

## 6. Landed artifact + verification

`leanfinal/Uniformity/ChapC/C136f14.lean` — 7 public declarations:
`dv2Res_zero`, `dv2Res_ne_zero_of_ne_zero_of_natDegree_lt` (public re-derivation of
C136l2e1's private nonvanishing, generalized to bare `A ≠ 0`),
★ `dv2ResPoly_scalar_shape_digit_kill`, `digit_kill_of_normalized_scalar_shape`,
`digit_kill_of_signed_scalar_shape`, `dev_witness_block_digit_zero`,
`dev_witness_product_digit_one`.

Verification (first attempt, zero repairs):

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136f14.lean
EXIT: 0
```

AxCheck: all seven `[propext, Classical.choice, Quot.sound]` — Lean core only; the
dissection axiom does not appear. No landed or leanspec file edited; no `C136l2e*.lean`
touched; no git operation; REVIEW_QUEUE untouched (nothing was enacted — the Tier-2 row
belongs to the A-C.24′ enacting unit).

Health check: `leanspec/Leanspec/ChapC.lean` re-elaborated at the current tree
(untouched by this unit) — see `/tmp/a24a_leanspec_gate.log`; exit status recorded there.
