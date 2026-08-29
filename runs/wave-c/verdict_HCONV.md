# UNIT HCONV verdict — the digit-split convolution supplier LANDS; the F1.4/F1.5 family CLOSES (2026-08-29)

## HCONV STATUS FIRST

| target | status | exact result |
|---|---|---|
| **`hconv` — the digit-split convolution supplier** (F14C §2.1, the last open F1.4/F1.5 leg) | **GREEN — PROVED, Lean-core, frame-generic** | `C136f14f.dv2FullRead_dev_mul_conv_split`: for every in-range lattice slot `t` of the product side, `dv2FullRead L (Mgz − t·u₂) (dev Ψ (g·z) (min₂(g·z) + t·ℓ₂))` equals the guarded weighted antidiagonal `Σ_{t₁≤t} [guards] root^{c₁(Mg−t₁u₂, Mz−(t−t₁)u₂)} · RAnch(g)[t₁] · RAnch(z)[t−t₁]` — byte-shaped as the premise of `C136f14c.dv2ResPolyAnch_eq_weightedConv_of_coeff_convolution` (machine-verified: both consumers accept it directly). Footprint exactly `[propext, Classical.choice, Quot.sound]` — the brief's "expect NOT the dissection cite" expectation is met. |

## FIRED SIGNED ROWS — STATUS SECOND

| signed row | status | exact result |
|---|---|---|
| **C.39 / F1.4 `dv2ResPolyTw_scalar`** | **GREEN — LANDED as a theorem, byte-as-is modulo the recorded `hh` delta** | `C136f14f.dv2ResPolyTw_scalar`: hypothesis block and conclusion machine-diffed against the leanspec post-A-C.24″ axiom — the ONLY deltas are `axiom → theorem` and the single inserted binder `hh : 0 < F.h` (the standing recorded F1.1/F1.2/F1.3/F1.8 convention, per the `C134cfs`/`C134f12c`/`C134f13a` headers). Every previously carried leg is DERIVED (see §2). Footprint: Lean core + `Uniformity.Density.Tower.exists_dvDissection` (the C.33 dissection cite) — inherited through the landed F1.1 block chain `C134cfs.blockFactor_spec`, i.e. the standing footprint of the whole F1 family. |
| **C.38 / F1.5 `dv2ResPolyTw_radical_eq`** | **GREEN — LANDED as a theorem, same convention** | `C136f14f.dv2ResPolyTw_radical_eq`: equal `natDegree` + identical monic irreducible divisors across the block projection, from the signed C.39 scalar via A24C's adapter `C136f14d.dv2ResPolyTw_radical_eq_of_scalar`. The scalar's nonvanishing is PROVED: `γ̂_g ≠ 0` from F1.2's residual clause (`C134f12c.quotient_residual_notdvd`) through the shift identity `dv2FullReadPoly_eq_shift` (neither the level residual nor `X^δ` is divisible by `L.r`), and `root ≠ 0` in the stage tower. Same footprint (Lean core + the dissection cite). |

**The F1 family (F1.1–F1.8) is COMPLETE**: every signed F1 row is now a landed theorem
on the standing footprint.

## 1. The supplier's proof (the level-2 transcription of MH9M's level-1 pattern)

File: `leanfinal/Uniformity/ChapC/C136f14f.lean` (NEW, 1014 lines, [HCONV 2026-08-29]).

1. **Expansion.** `g·z = Σ_{(j,i) ∈ range N ×ˢ range N} dev Ψ g j · dev Ψ z i · Ψ^{j+i}`
   (`sum_dev_eq`, the `C136l2e2.dv2Line_succ_le_of_no_pair` pattern), and `dev` of the
   sum splits termwise (`dev_finsetSum`).
2. **Additivity at the line.** New private `dv2FullRead_finsetSum` (finite-sum
   additivity of the anchored read at a common height floor, by cons-induction over
   `dv2FullRead_add_of_le` + the ultrametric `min_dv2Hgt_le_dv2Hgt_add`). The floor for
   EVERY term is `le_line_dev2_term`: each convolution term prices at or above
   `Sg + Sz = ℓ₂·(Mgz − t·u₂) + u₂·J` (the value-line identity uses the local
   `lattice_line_floor` twin `t·u₂ ≤ Mgz` and side-min/pin additivity
   `dv2SideMin_mul`/`dv2Pin_dv2SideMin_mul`).
3. **The strict kill.** Every term that is NOT an exact-slot on-side pair — off-line
   main terms AND the whole carry diagonal at once — prices at `Sg + Sz + 1`
   (`lt_line_dev2_term`), hence its read dies (`dv2FullRead_eq_zero_of_lt`). No
   separate carry-diagonal case is needed: the two-diagonal split of
   `dev_mul_conv_split_monic` is subsumed by pricing the full convolution square.
4. **The good set = the on-side lattice antidiagonal.** On-side abscissae are
   `≡ min (mod ℓ₂)` within `[min, max]` (local `dv2OnSide_modEq'`/`dv2SideSpan_eq'`
   twins), so the surviving pairs biject with `{t₁ ≤ t : both lattice slots on-side}`
   (`Finset.image` + `sum_image`).
5. **The good-pair evaluation** (`good_pair_read`): `dev_mul_pow` reduces the term to
   the slot-`0` reduced digit product; the §5-risk absorber
   (`C136f14b.dv2FullRead_dev_zero`, floors from inner `dvSupp_mul` + `Dv2ResSurv` +
   ultrametricity) removes the reduction; the landed absolute carry law
   (`C136f14c.dv2FullReadCarryLaw`) prices it as `root^{c₁(ka,kb)}·read(A)·read(B)`
   with the exact shift identity `s(ka) + s(kb) = s(ka+kb) + ℓ·c₁(ka,kb)` (new private
   `shift_add_exact`, from `L.cocycle_mem` + the shift-spec twins). The grades are the
   anchored ones: `ka = Mg − t₁·u₂` exactly (`dv2Pin_lattice_of_onSide`).
6. **The guard match.** Off-side lattice slots vanish on BOTH sides: strict pricing on
   the left, `dv2ResPolyAnch_coeff_eq_zero_of_not_onSide` on the right
   (`Finset.sum_subset` extension). The A24A/L2E4 caution is respected: no unweighted
   law anywhere; every slot carries its own explicit cocycle weight.

## 2. How the signed rows fire (all carried legs discharged)

Generic intermediates (both Lean-core):

* `dv2ResPolyAnch_mul_eq_weightedConv` — F14C's assembler fired frame-generically:
  `RAnch(g·z) = dv2ResPolyAnchWeightedConv(g, z)` (uses `dv2SideDeg_mul` for `hdeg`).
* `dv2ResPolyTw_scalar_of_split_geometry` — A24F's conditional with `hconv` DISCHARGED
  and the derivable legs (`hngz`, `hpgz`, `hM`, `hdeg`, `hfS`) derived; remaining
  premises exactly the complement-geometry legs.

The signed `dv2ResPolyTw_scalar` then derives those legs from its own hypothesis block:

* `hΨd : 0 < Ψ.natDegree` — from `IsTestKey`'s degree clause + frame positivity.
* `hSurv : Dv2ResSurv` — `C134p1d.isMuKey_of_isTestKey` + `C134f13a.dvSupp_testKey`
  (key grade `= L.ℓ·L.seam`) + `dv2ResSurv_of_muKey`; the signed `hseam` IS the fence.
* `hsplit` — `C134cfs.blockFactor_dvd` + monic block (`hasLabel_blockFactor`) +
  `modByMonic_eq_zero_iff_dvd`.
* the complement point side — P2 (`C134p1.block_complement_not_muDvd`) through the
  abscissa-0 collapse: new private `onSide_eq_zero_of_not_muDvd` (every level-2 on-side
  abscissa of a not-μ-divisible polynomial is `0`: the strict outer fence beats the
  digit floor `dvSupp_le_dev_add` at every positive abscissa), giving `hmin0`, `hzdeg`
  (side degree `0`), and `hpz` (`dvSupp_modByKey_eq_of_not_muDvd` at slot `0`,
  `complementConst` by `ENat.coe_toNat`).
* `hγ` — new private `read_dev_zero_of_not_muDvd`: the complement instance of the
  absorber, with `dvSupp_modByKey_eq_of_not_muDvd` supplying the remainder floor.

`dv2ResPolyTw_radical_eq` adds `γgAnch_ne_zero` (new private; §"FIRED" table above) and
a local `root_ne_zero` twin, then fires `dv2ResPolyTw_radical_eq_of_scalar`.

## 3. Findings for the record

* **The `hh` binder delta is forced, not optional**: `0 < F.h` is not a `KeyFrame`
  field (the degenerate `h = 0` frame is admitted by design), `BlockContext` does not
  package it, and the entire landed level-2 multiplicative engine consumes it. The
  F1.1/F1.2/F1.3/F1.8 rows already landed with the same recorded delta; C.39/C.38 now
  follow that precedent. If the owner wants the leanspec rows byte-exact with no
  delta, the engine would need an `h = 0` degenerate-frame derivation — currently
  unproven and (per the corpus notes) out of the live frame anyway.
* The dissection cite (`exists_dvDissection`, C.33) enters ONLY through the landed
  F1.1 block-selector chain (`blockFactor_spec` → `C133mh15.blockFrontier_of_context`);
  the supplier itself and both generic product laws are Lean-core.
* The two-diagonal split (`dev_mul_conv_split_monic`) named in the F14C route was NOT
  needed: pricing the full convolution square with `lt_line_dev2_term` kills the carry
  diagonal and the off-line terms uniformly — a strictly shorter route than the
  level-1 MH9M proof's case split.

## 4. Verification and trust footprint

Required scoped command:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136f14f.lean
```

Result: **EXIT 0**, zero errors, zero warnings, zero `sorry`. AxCheck prints:

* `dv2FullRead_dev_mul_conv_split` — `[propext, Classical.choice, Quot.sound]`
* `dv2ResPolyAnch_mul_eq_weightedConv` — `[propext, Classical.choice, Quot.sound]`
* `dv2ResPolyTw_scalar_of_split_geometry` — `[propext, Classical.choice, Quot.sound]`
* `dv2ResPolyTw_scalar` — Lean core + `Uniformity.Density.Tower.exists_dvDissection`
* `dv2ResPolyTw_radical_eq` — Lean core + `Uniformity.Density.Tower.exists_dvDissection`

Byte-fidelity: `diff` of the two signed statements against the leanspec axioms shows
exactly three deltas each — `axiom → theorem`, the `{F} {H₀ hpin}` binders factored
into the file's `variable` block, and the inserted `(hh : 0 < F.h)`.

## 5. Footprint

* `leanfinal/Uniformity/ChapC/C136f14f.lean` — CREATED (1014 lines; the supplier, the
  two generic product laws, the two SIGNED rows, private local twins only).
* `leanfinal/Uniformity/ChapC.lean` — one import line added (`C136f14f`, the standing
  sibling registration step; no other change).
* `runs/wave-c/verdict_HCONV.md` — CREATED.
* No landed theorem file or leanspec file edited. No git operation run.
