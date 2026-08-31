# UNIT MFL — VERDICT: THE `(h,1)` AXIS'S COUNT LAYER CLOSED AT THE BASE RING (no
transport), ★ THE COMPOSITUM CELL TRANSPORT LANDED (EFR's named missing instrument
#1), the unramified tower scale calculus landed — and the HONEST FINDING that NO live
frame law can fire without a new cite-genre step (2026-08-31)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG64.lean` (1205 lines, ZERO sorries,
zero errors, zero warnings; 19 AxCheck footer lines).  **Axiom fence, better than
charged:** EVERY declaration — the `(h,1)` cells/box/counts, the unramified scale
calculus, the unramified and compositum cell transports, the count identities — is
**pure Lean core `{propext, Classical.choice, Quot.sound}`**.  No cite occurs anywhere
in the file's footprint (not B.42, not C.33): this unit adds ZERO conditionality.
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG64.lean`
(4 increments, each GREEN before the next); targeted `lake build
Uniformity.ChapI.IFCG64` GREEN (9038 jobs); aggregator `lake env lean
Uniformity/ChapI.lean` GREEN with the IFCG64 line wired between IFCG63 and
I10RungLift3W.  IFCG63.lean untouched; no landed file touched except the sanctioned
one-line aggregator import; no git ops.

## ★★★ THE HEADLINES

    theorem slopeCellDec_eq_box_inter :          -- ★★ THE (h,1) BOX CHARACTERIZATION
      slopeCellDec π (e'*k) h e' k N (ζ̄ y) σ
        = slopeBox π h e' k N y ∩ decidedSet O (e'*k) σ N          -- LEAN CORE
    theorem card_slopeBox :                      -- ★★ THE EXACT (h,1) BOX COUNT
      Nat.card (slopeBox π h e' k N y)
        = q ^ (e'*k*N − ((Σ_{j<e'k} ⌈h(e'k−j)/e'⌉) + k))          -- LEAN CORE
    theorem card_mixedFace_one_eq_box_sum :      -- ★★★ THE (h,1) COUNT ENDPOINT
      Nat.card (mixedFace π (e'*k) h e' 1 N σ)
        = Σ_{y ≠ 0} Nat.card (slopeBox π h e' k N y ∩ decidedSet …) -- LEAN CORE
    noncomputable def compCellTransport :        -- ★★★ EFR's MISSING INSTRUMENT #1
      Coeff O ((deg φ)*(e'*k)) N ≃ Coeff O₂ k (e'*N)               -- LEAN CORE
    theorem card_coeff_compositum :              -- ★★ THE NORMALIZATION IDENTITY
      Nat.card (Coeff O₂ k (e'*N)) = Nat.card (Coeff O ((deg φ)*(e'*k)) N)

plus the unramified stage in full (`unramCellTransport` : `Coeff O ((deg φ)*k) N ≃
Coeff O₁ k N` with `_apply`/`_symm_apply`) and the tower type calculus
(`unramScaleType`, `towerScaleType`, degrees, injectivity, the commutation of the two
stages).

## ★★★ THE HONEST FINDING (the charge's two checks, both answered NEGATIVE)

**(1) CN2 does NOT close `(3,4,1)`.**  `decidedAt_of_eisenstein_face` (IFCG23) is
uniform in `h` but stated at denominator **`e' = m` ONLY** (`Nat.Coprime h m`,
attainment at `0` and `m`, conclusion `DecidedAt O m ⟨{(m,1)}⟩ N c`).  The `(3,4,1)`
frame at `m = 8` is slope `3/4` with `e' = 4 < 8 = m` and residual `(X − ζ)²` — this
is CN2's OWN named remainder item 2 (pure faces with `e' < m`: `e' ∣ ramIndexOf` is
PROVED on every factor, the TYPE is not pinned; the residual `ψ^k` dissects further).
So the charge's hoped-for outright fire does not exist in the landed corpus.

**(2) `FactorCorrespondenceAt` does NOT cover the compositum.**  It is
Eisenstein-key-shaped over an ARBITRARY complete DVR, so it instantiates at
`O₁ = AdjoinRoot φ` and covers the RAMIFIED leg of the mixed tower — but the
UNRAMIFIED leg (`typeOf` over `O` vs. over `O₁`, `(e,f) ↦ (e, d·f)`) is covered by NO
landed instrument.  Hence a `(1,d)` frame law is NOT expressible under the master's
existing `FC_D` premise alone: it needs `FC` at the compositum PLUS one new pointwise
unramified/tower step.  **I did not invent that Prop**: its hypothesis vector is a
literature question (the OM/Montes induction step at a residual key of degree `d`),
and a guessed hypothesis set is exactly the failure mode the axiom policy exists to
prevent.  What IS now true: the Prop is fully EXPRESSIBLE in landed vocabulary — the
box side by IFCG62's `compositum_transfer_digits_base` + `compositum_root_pow_dvd_mk_iff`,
the type side by this unit's `towerScaleType` (+ `towerScaleType_injective`, the lever
that turns ONE pointwise law into BOTH transport directions, exactly as
`scaleType_injective` does in DTR).

**Consequence, stated exactly: NO `MixedFaceLaw` fires at a live frame in this unit,
and the census master is UNCHANGED** (IFCG62's `decidedSliceAt_all_of_MASTER_MIXED`
stands as the current master).  Row 2 does NOT leave the master yet.  Claiming
otherwise would have required either weakening a statement or inventing a cite — both
refused.

## What DID close, per axis

**`(h,1)` AXIS — the COUNT leg is CLOSED, transport-free** (EFR's recorded
"count-first" route, confirmed as the right one):
* `slopeCellDec` (the general-`h` replay of IFCG51's `eisCellDec`) +
  `mixedFace_one_eq_biUnion` / `card_mixedFace_one_eq_sum`: the `d = 1` frame carrier
  is EXACTLY the disjoint union of the `q − 1` nonzero-centre slope cells (linear
  monic irreducible with `ψ(0) ≠ 0` ⟺ `X − ζ`, `ζ ≠ 0`), counted exactly at every
  level.
* ★ `slope_lattice_pins` — IFCG51's `lattice_pins` at EVERY coprime slope `h/e'`: the
  raw lattice `h(m−j) ≤ e'·v_j` with EXACT corner `v₀ = h·D` reconstructs the minimal
  face AND pins the residual degree.
* ★★ `slopeCellDec_eq_box_inter`: the σ-decided cell IS `slopeBox ∩ decidedSet` at the
  BASE ring, where `slopeBox` is a pure valuation/digit condition (lattice + the `k`
  class digits at heights `h(k−t)` on the `e'`-divisible slots reading `(X−y)^k`'s
  coefficients).  Forward: `fullSpan_pins` + `resPoly_x_frame` + IFCG62's
  `xres_eq_iff_digits_target`; backward: `slope_lattice_pins` with the exact corner
  recovered from the NONZERO pinned digit (`resOrd_eq_iff_resDig`, DBL's engine) —
  the `(−y)^k ≠ 0` step is where `ζ ≠ 0` pays.
* ★★ `card_slopeBox`: the box is an EXACT `q`-monomial
  `q^(mN − (Σ_j ⌈h(m−j)/e'⌉ + k))` — per-coordinate product of `card_setOf_le_resOrd`
  (free coordinates above the ceiling floor) and `card_setOf_resDig` (each digit pin
  costs one `q`-power); the `e'`-divisible slots' ceilings are computed exactly
  (`b(e'·t) = h(k−t)`).
* ★★★ `card_mixedFace_one_eq_box_sum`: the endpoint — carrier count = Σ over the
  `q − 1` centres of the decided box counts.  **What remains for this axis is exactly
  the decision leg, never the count.**

**`(1,d)` AXIS — the TRANSPORT is CLOSED** (EFR's named missing instrument #1):
* ★★ `unramCellTransport : Coeff O ((deg φ)·k) N ≃ Coeff O₁ k N` — the `φ`-adic
  dev-transform bijection at the UNRAMIFIED stage.  **Level UNCHANGED** (`e(K'/K)=1`,
  against IFCG43's `N ↦ e'·N` at the Eisenstein stage).  New mechanism landed for it:
  `smul_divByMonic` (mathlib has only the `%ₘ` half), `dev_smul` (the development is
  `O`-linear in scalars), ★ `dvd_dev_coeff` (the development PRESERVES coefficient
  divisibility) — with these, outbound level exactness is IFCG62's
  `unram_pow_dvd_mk_iff` on `dev` of the difference (via `dev_add_of_monic`), and
  inbound exactness is `smul_modByMonic` on the canonical representatives.  Round
  trips: IFCG39's `reassT_devT`/`devT_reassT`.
* ★★★ `compCellTransport : Coeff O ((deg φ)·(e'·k)) N ≃ Coeff O₂ k (e'·N)` — the
  composition with IFCG43's Eisenstein transport at `O₁`, over the full mixed tower
  `O → O₁ → O₂`; plus `compCellTransport_card_image` (count transport) and ★
  `card_coeff_compositum` (the normalization identity `q^{d·k·e'·N}` = the base box
  `q^{(d·e'·k)·N}`: **the mixed transport creates and loses NO `q`-power** — the
  bookkeeping the `(1,d)` frame sum consumes, with `q ↦ q^d` inertia against `N ↦ e'N`
  ramification exactly cancelling).
* Tower type calculus: `unramScaleType` (`(e,f) ↦ (e,d·f)`), degree `= d·σ.degree`,
  injective at `d > 0`, COMMUTES with `scaleType`; `towerScaleType e' d = scaleType e'
  ∘ unramScaleType d` (`(e,f) ↦ (e'·e, d·f)`), degree, injectivity.

**`(h,d)` AXIS**: the composition of the two — the count layer is the `(h,1)` box at
the compositum key, the transport is `compCellTransport` at the `xKey`; both legs'
missing pieces are the two decision steps below.

## THE EXACT SURVIVING REMAINDER (row 2's fence, after this unit)

1. **`(h ≥ 2, 1)` frames** (`(2,3,1)` at `m = 6`, `(3,4,1)` at `m = 8`): ONLY the
   decision leg — a pointwise OM tower step at slope `h/e'` (the Bézout Eisenstein
   ring `γ^{e'} = z^s·π`, `s·h ≡ 1 mod e'`, is the recorded route around the non-DVR
   single-ring obstruction).  Then the squeeze is IFCG51 §3's verbatim (the box is a
   `q`-monomial here, so the squeeze may even be replaced by a direct limit).
2. **`(1, d ≥ 2)` frames** (`(1,2,2)` at `m = 8`): the unramified pointwise tower step
   (expressible as above, hypothesis vector to be settled against FGMN), then the
   `ZcURLim` assembly = IFCG51 §3's squeeze replayed at the compositum with
   `zcURLim_compositum_value`'s `d`-reindexed rational family.
3. **`(h ≥ 2, d ≥ 2)`** (first at `m = 12`: `(2,3,2)`): 1 + 2 composed.

## File map (`leanfinal/Uniformity/ChapI/IFCG64.lean`, 1205 lines, 19 declarations)

§0 kit (`isKey_X`, `residual_pow_inj`, `ncard_biUnion_eq` replicas) · §1
`slopeCellDec`, ★ `mixedFace_one_eq_biUnion`, `slopeCellDec_disjoint`, ★
`card_mixedFace_one_eq_sum` · §2 `mem_sideSet_iff'`/`resPoly_rep` replicas, ★
`slope_lattice_pins`, `slopeBox`, ★★ `slopeCellDec_eq_box_inter`, ★★ `card_slopeBox`,
★★★ `card_mixedFace_one_eq_box_sum` · §3 `unramScaleType` (+ data/degree/one/injective),
`scaleType_unramScaleType_comm`, `towerScaleType` (+ degree/one/injective) · §4
`res_mk_eq_iff`/`pow_dvd_monicPoly_sub_coeff`/`monicPoly_coeff_self` replicas (all
ring-generic — they are applied at `O₁` too), `smul_divByMonic`, `dev_smul`, ★
`dvd_dev_coeff`, `unramDevVec`/`unramReassVec` + congruences + round trips, ★★
`unramCellTransport` (+ `_apply`, `_symm_apply`), ★★★ `compCellTransport`, ★
`compCellTransport_card_image`, ★ `card_coeff_compositum` · AxCheck (19 lines).
Imports: `IFCG36` (DBL's digit engine — NOT in IFCG62's closure) + `IFCG62`.
Aggregator: one line between IFCG63 and I10RungLift3W.

## New definitions (trust boundary — flag for review)

`slopeCellDec` (the `h`-general decided cell; `h = 1` recovers IFCG51's `eisCellDec`
verbatim in shape), `slopeBox` (the digit-pinned lattice box — pure valuation/digit
data, no face language), `unramScaleType`/`towerScaleType` (the tower `(e,f)`
bookkeeping; `towerScaleType 1 1 = id` is machine-checked as a convention pin, and
`towerScaleType_degree` pins the degree arithmetic), `unramDevVec`/`unramReassVec`,
`unramCellTransport`, `compCellTransport`.  NO new Prop and NO new axiom was
introduced; nothing was weakened; `mixedFace`/`MixedFaceLaw`/`mixedFrames` are
consumed byte-identically.

## Repair log (6 error rounds; every statement landed as designed)

1. The `Finset.filter (· ≠ 0)` census needs decidability — file-wide
   `Classical.propDecidable` local instance (safe here: NO kernel `decide` in this
   file, unlike IFCG62 whose frame censuses are decided upstream).
2. `onSide_monicPoly_of_npAttains` lives in IFCG26 (not IFCG35/44) — open added.
3. `resPoly_x_frame`'s `resFieldXEquiv` coercion is `AdjoinRoot.of (map (residue O) X)`
   by `rfl`, so `rw` on the coerced map form fails inside the goal: state the mapped
   equation as a `have` and close by `Polynomial.map_injective`.
4. `Nat.mul_lt_mul_of_lt_of_le` wants a STRICT first argument — `e'·t < e'·k` via
   `Nat.mul_le_mul` + `omega` on `e'(t+1) = e't + e'`.
5. `generalize … at` must list EVERY hypothesis mentioning the atom (a `%`-bound left
   behind on a stale atom killed one omega); and `subst hl` for `hl : l = n` eliminates
   the SECTION variable `n` (corpus trap: use `rw [hl]` and speak in `l`).
6. Instance plumbing (the session's main cost): `irreducible_algebraMap_adjoinRoot`
   needs `O₁`'s completeness + finiteness (haveI from IFCG27's cascade), `proj`/`proj_
   surjective` at `O₁` need `Finite (ResidueField O₁)` (section binder), and the three
   private replicas had to be made RING-GENERIC (`{R}`) because they are applied at
   `O₁` as well as `O` — a `{O}`-section replica silently demands the base section's
   completeness instances at `O₁`.  Also: `modByMonic_add_div` takes BOTH polynomials
   explicitly at this pin (no monicity argument), and mathlib has `smul_modByMonic`
   but NOT the `divByMonic` half (proved here by cancelling `q` in the domain).

## Consumption notes for the successor frame units

* The `(h,1)` law unit needs ONLY: the pointwise slope-`h/e'` tower step, then
  `card_mixedFace_one_eq_box_sum` + `card_slopeBox` + a limit of the DECIDED box
  fraction.  Because the box is a `q`-monomial with the decided set as the only
  non-monomial factor, the squeeze may reduce to a single `stratDecCount` ratio — check
  before replaying IFCG51 §3's two-arm squeeze.
* The `(1,d)` law unit: `compCellTransport` + `card_coeff_compositum` +
  `compositum_transfer_digits_base` (the box↔digits reading) +
  `zcURLim_compositum_value` (the value at `q^d`) are ALL landed; the ONLY missing
  piece is the pointwise unramified tower step, whose type side must be
  `towerScaleType e' d` (this unit) — state it with the box hypotheses phrased in
  IFCG62's landed vocabulary, and get the hypothesis vector checked against FGMN
  before landing it as a cite.
* Do NOT try to route the `(h,1)` decision through CN2's
  `decidedAt_of_eisenstein_face`: it is `e' = m` only (see THE HONEST FINDING).
