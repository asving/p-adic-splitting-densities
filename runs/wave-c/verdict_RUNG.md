# UNIT RUNG verdict — per-rung carrier packs: the rung-2 pack LANDS and the iteration CLOSES up to the named key-lift (2026-08-30)

**Status: COMPLETE.** `leanfinal/Uniformity/ChapI/I10RungPacks.lean` (NEW, 966 lines,
namespace `Uniformity.Density.Tower.I10rung`) — 0 errors, 0 warnings, 0 `sorry`; all
**11** printed footprints exactly `[propext, Classical.choice, Quot.sound]`.  Verified
per-file (`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10RungPacks.lean`,
exit 0), per-target (`lake build Uniformity.ChapI.I10RungPacks` — Build completed
successfully, 8853 jobs), and the chapter aggregator `Uniformity/ChapI.lean` re-verified
exit 0 after the one standing import-line edit.  Cite ledger: **empty** — everything is
Lean-core; no numeral, no `residueCard`, no S2 datum anywhere in the file.

## STATUS FIRST

| charge | status | exact result |
|---|---|---|
| 1. the level-2 pack | **GREEN — ★ LANDED, Lean-core, uniform in `q` and the frame** | `rung2Carrier : WeightedCarrier O (AdjoinRoot L.r)` + `rung2Key : CarrierKey … u₂ ℓ₂` at ANY `LevelDatum` and ANY test key; `rung2Key_nonempty` (inhabited at every level datum over a finite residue field, via `exists_testKey` — no S2 pin needed); ★ `rung2_wcoeff_mul` = WCC's `wcoeff_mul` FIRING at rung 2 of a general tower — the level-2→3 weighted convolution, the general-tower counterpart one level down of the S2-pinned `s2Mu4Coeff_mul` |
| 2. the iteration shape | **GREEN up to the named per-rung obligation, exactly as the charge's else-branch sanctioned** | UNCONDITIONAL: `nextCarrier : WeightedCarrier O (Polynomial K)` from any `RungPack` (including `lineFloor_mul` and BOTH halves of `nextSupp_mul` — the two pieces WCC left open); ★ FINDING `carrierKey_nextCarrier_isEmpty` (the pass to a quotient ring is FORCED, provably); adjudication: the root relation is NOT a field of the realization's chain data (C130fg evidence below) ⇒ CONDITIONAL step `RungLift`/`RungLift.pack` + induction wrapper `towerPacks` + `towerPacks_wcoeff_mul` (the convolution at every rung from base + step) |
| 3. wire into `LevelSiteBank` | **obligation map updated — §4 below** | key-lifting row DISCHARGED at rung 2 and pinned (`RungLift`) at rungs ≥ 3; B-1 at rung 2 reduced to one slope inequality; exact remainder named |

## 1. Charge 1 — the rung-2 pack (all landed content + one new mechanism)

### 1.1 The one new mechanism: the normalizer exponent (the coboundary repair)

The landed absolute carry law (`C136f14c.dv2FullReadCarryLaw`) is WEIGHTED —
`FR(ka+kb)(A·B) = root^{c₁(ka,kb)}·FR(ka)A·FR(kb)B`, `c₁ = L.cocycle` (C28) — while
`WeightedCarrier.read_mul` demands exact multiplicativity.  The repair: `c₁` is a
COBOUNDARY over ℕ.  With `s := L.shift`, `d := (L.ℓ−1)·s(1)`:

    normExp L m := (s(m) + d·m) / L.ℓ        -- exact division (normExp_dvd)
    normExp a + normExp b = normExp (a+b) + c₁(a,b)   -- (normExp_add)

Divisibility is by induction on `m` from the exact cocycle identity
`s(a)+s(b) = s(a+b)+ℓ·c₁(a,b)` alone (no coprimality argument beyond what C28 encodes —
`d + s(1) = ℓ·s(1)` is the only extra fact).  The carrier read is then

    rung2Read L m f := AdjoinRoot.root L.r ^ normExp L m * dv2FullRead L m f

and the twist absorbs the carry exactly.  This is the generic form of WCC §1.2's
observation that S2's `eval 1` erases the letter powers: here they are KEPT and
re-normalized.  (Relation to the landed anchored objects: the twist is an explicit
per-grade unit `root^{normExp}`, so nonvanishing and multiplicativity statements
transport; the slot dictionary to `dv2ResPolyAnch` remains f14b's
`dv2ResPolyAnch_coeff_of_onSide` root-power form.)

### 1.2 Field-by-field suppliers (every field a landed lemma)

carrier (`rung2Carrier L hπ hh`, `supp := dv2Hgt L`, `read := rung2Read L`):
`C132nv2.dv2Hgt_zero` · `C133mh3.dvSupp_mul` (Theorem M; floor = `L.hκ` via
`mul_assoc`) · `min_dv2Hgt_le_dv2Hgt_add` · `dv2FullRead_eq_zero_of_lt` (both
`read_zero` at `⊤` and `read_above`) · `dv2FullRead_add_of_le` ·
`dv2FullReadCarryLaw` + `normExp_add` (`read_mul`).

key (`rung2Key … hΨ hℓ₂ hstrict`, `key := Ψ`, `kgrade := L.ℓ * L.seam`): `hΨ.1` ·
`C134p1d.natDegree_pos_of_isTestKey` · `dv2Hgt_testKey` (`supp_key`) · **key lifting at
rung 2 = the LANDED `C136l2e0.dv2FullRead_testKey`** (`read_key`; twist-stable) ·
`hstrict : ℓ₂·(L.ℓ·L.seam) < u₂` (the engine-honest RE-SIGNED B-1 floor, a hypothesis —
the next level's slope datum) · `C134dv2g.dvSupp_mul_modByKey_eq` /
`dvSupp_add_le_key_quot_add` through `C134p1d.isMuKey_of_isTestKey` (P1)
(`supp_mod`/`supp_quot`).

pack extras (`rung2Pack`): `exact_ne` = `C136f14b.dv2FullRead_ne_zero_of_exact` (fence
`< L.keyDeg₂ = Ψ.natDegree` — exactly the `RungPack` fence) + local `root_ne_zero` twin
+ `AdjoinRoot.instField` under `Fact (Irreducible L.r)`.

### 1.3 The ★ headline

`rung2_wcoeff_mul` : at every `LevelDatum L` (`hπ`, `hh : 0 < F.h`), every test key,
every outer pair `(u₂, ℓ₂)` with `0 < ℓ₂` and `ℓ₂·(L.ℓ·L.seam) < u₂`, under pointwise
line floors:
`wcoeff (β+β') (g·z) J = Σ_{j≤J} wcoeff β g j · wcoeff β' z (J−j)` — the first
general-tower rung pack beyond the base, Lean-core.

## 2. Charge 2 — the iteration

### 2.1 Unconditional: the iterated carrier EXISTS at the polynomial ring

`RungPack O K u ℓ` := carrier + key + `exact_ne` (exact-grade read nonvanishing under
the key-degree fence — FGMN Thm 4.1/Cor 4.9(1) genre; the fence is what makes it true
AND what the iteration needs, since it only ever reads development coefficients).
From any pack over a `NoZeroDivisors` ring:

* `nextSupp f := ⨅ j, ℓ·supp(dev key f j) + u·j` (`LineFloor β f ↔ β ≤ nextSupp f`,
  by `le_iInf_iff` — WCC's hypothesis is exactly the coordinate form);
* `nextRead m f := Σ_j C (wcoeff m f j)·X^j` — the generating polynomial of the wcoeff
  family (`nextRead_coeff`: the range truncation is invisible since `0 < u`);
* ★ `lineFloor_mul` — WCC's anticipated supermultiplicativity: main terms priced by
  `supp_mod`, carry terms by `supp_quot` + `ℓ·kgrade ≤ u` (only the NON-strict floor is
  needed here; the strictness is consumed only by `wcoeff_mul`'s read kill);
* `nextSupp_mul` BOTH halves: `≥` from `lineFloor_mul` (with an `ℕ∞` lift through nat
  floors handling `⊤`), `≤` from `nextRead_mul` + `nextRead_ne_zero_of_exact` (the
  finite-infimum attainment is FREE in `ℕ∞`: exact value forces an exact on-lattice
  slot; the slot's read is nonzero by the pack's `exact_ne`, fence automatic);
* `nextRead_mul` at exact grades IS `wcoeff_mul` coefficientwise — **the convolution
  law is literally polynomial multiplication of the generating reads**
  (`Polynomial.coeff_mul` + antidiagonal↔range);
* ★★ `nextCarrier : WeightedCarrier O (Polynomial K)` assembles all nine laws.

### 2.2 ★ FINDING — the quotient is FORCED (Lean form of "blocked by content")

`carrierKey_nextCarrier_isEmpty : IsEmpty (CarrierKey (nextCarrier R) u' ℓ')` — any key
pack at the bare polynomial ring would have `supp_key` (exact grade) and `read_key = 0`
simultaneously, contradicting `nextRead_ne_zero_of_exact`.  So key lifting MUST pass to
a proper quotient of `Polynomial K` (the next letter's ring `K[X]/(r')`) — WCC's
"blocked on key lifting by content" is now a theorem, not a remark.

### 2.3 The adjudication and the conditional step

**Is the root relation a field of the realization's chain data?  NO.**  `ChainRealization`
(C130fg, post-PK/U15) carries `receiver`/`keys`/`normalizer`/`node`; the FGMN records
(`FGMNSourceData`/`FGMNSourceLaws`) carry letters, residuals, `carried_key_residual`
(`R_(r+1)(φ_(r+1)) = 1` — the CARRIED key, a different statement), and `graded_mul`
only under the `PrevGrade` fence (the carry-free slice).  No field asserts the NEXT
key's residual-root relation, and `KeyChain`/`DeepTower` carry keys without read laws
(C92_VACUITY stands).  Hence the else-branch: the step is CONDITIONAL on the named
per-rung datum, and the wrapper is proved.

* `pushCarrier` — any carrier pushes along any ring hom (unconditional).
* `RungLift R K' u' ℓ'` — THE named per-rung obligation, the `Rres_exists` genre with
  its pinned Lean shape: `φ : Polynomial K →+* K'` (the pass to the next letter's ring,
  forced by §2.2) + `CarrierKey (pushCarrier (nextCarrier R) φ) u' ℓ'` (whose
  `read_key = 0` IS "the next letter is a root of the key's residual polynomial") + the
  pushed `exact_ne` (FGMN's `graded_scalar_nonzero` clause at the new rung).
* ★ `RungLift.pack` — the step: pack + lift = pack one rung up.
* ★ `towerPacks : PackAt O → (∀ Q, LiftAt O Q) → ℕ → PackAt O` — the induction
  wrapper (packs at all rungs from base + step; `PackAt`/`LiftAt` bundle ring +
  `NoZeroDivisors` + slopes as instance fields), with `towerPacks_zero/succ` pins and
  ★ `towerPacks_wcoeff_mul` — the convolution law fires at EVERY rung of the stream.

At rung 2 the lift data is landed (§1); at rungs ≥ 3 supplying `RungLift` is exactly
the remaining key-lifting research, now with a machine-checked interface.

## 3. Honesty

* Uniform in `q` and the frame: zero numerals, zero `residueCard`, zero S2 data (the
  only grep hits are the header's own uniformity note).
* Nothing weakened: WCC's `WeightedCarrier`/`CarrierKey`/`wcoeff`/`LineFloor` and
  `wcoeff_mul` consumed verbatim; no landed file edited (aggregator import only).
* Honest hypotheses: `hπ`, `hh : 0 < F.h` (the standing f14-family convention),
  `IsTestKey` (constructible: `exists_testKey`), the B-1 slope floor
  `ℓ₂·(L.ℓ·L.seam) < u₂` (genuinely the next level's datum, not derivable), and
  `RungLift` per rung ≥ 3 (adjudicated genuinely new — §2.3).
* `RungPack.exact_ne` carries the FGMN degree fence — NOT weakened away; it is both what
  rung 2 supplies and what the iteration consumes.
* Local twins (3rd repetition in the corpus, flagged for dedup): `shift_spec`,
  `shift_unique`, `shift_add_exact`, `isKey_X`, `localFieldStageField`, `root_ne_zero`;
  plus local copies of WCC's private `wcoeff` guard/degree/floor helpers.

## 4. Charge 3 — the `LevelSiteBank` obligation map after this unit

`LevelSiteBank` (SCS) demands an `FGMNCalculus` at a `DeepTower`; the packs live at a
`LevelDatum`.  This unit does not bridge the spines (that is D3-03).  The SCS/WCC
remainder table updates to:

| leg | before this unit | after this unit |
|---|---|---|
| convolution | closed once-and-for-all (WCC) | unchanged; now INSTANTIATED at rung 2 and at every rung of any pack stream |
| key lifting (`Rres_exists`) | open at all rungs, shape pinned | **DISCHARGED AT RUNG 2** (`dv2FullRead_testKey` consumed as `read_key`); at rungs ≥ 3 = supply `RungLift` (quotient ring + root relation + `graded_scalar_nonzero`), with the polynomial-ring alternative PROVABLY closed |
| depth adapter (D3-03) | open | open (a `WeightedCarrier` per rung now constructs from `towerPacks` GIVEN lifts; the LevelDatum-per-truncation-from-`DeepTower` spine identification remains the research leg) |
| B-1 grades | open per rung | at rung 2: reduced to the single slope inequality `ℓ₂·(L.ℓ·L.seam) < u₂` (+ landed grade/D3AD content); at rungs ≥ 3: the `CarrierKey` numeric fields inside `RungLift` |
| `PrevGrade` at `f' ≥ 2` | open | untouched |

## 5. New statements flagged for the standing review

`normExp`, `rung2Read`, `rung2Carrier`, `rung2Key`, `RungPack`, `nextSupp`, `nextRead`,
`pushCarrier`, `RungLift`, `PackAt`, `LiftAt`, `towerPacks` (supplier-side interface
shapes below the signed surface; no leanspec name touched).

## 6. Verification, repair log, footprint

* Per-increment command run throughout; FINAL: exit 0, 0 errors, 0 warnings, 0 `sorry`;
  AxCheck 11/11 Lean-core (`rung2Carrier`, `rung2Key`, `rung2Key_nonempty`,
  `rung2_wcoeff_mul`, `rung2Pack`, `lineFloor_mul`, `nextCarrier`,
  `carrierKey_nextCarrier_isEmpty`, `RungLift.pack`, `towerPacks`,
  `towerPacks_wcoeff_mul`).  `lake build Uniformity.ChapI.I10RungPacks` — success
  (8853 jobs).  Aggregator re-verified exit 0.
* Repair log (all mechanical, no mathematical repair): (1) `localFieldStageField` is a
  per-file private twin, not importable — copied with `isKey_X`; (2) this mathlib:
  `Nat.dvd_sub'` → `Nat.dvd_sub`, `Polynomial.finset_sum_coeff` → `finsetSum_coeff`,
  `mul_le_mul_left'`/`add_le_add_left` deprecated or convention-flipped → used
  `mul_le_mul' le_rfl`/`add_le_add le_rfl` forms, `push_neg` → `push Not`;
  (3) `WithTop.mul_top` on `ℕ∞` only unifies via an ascribed `have`, never by direct
  `rw` (ENat vs WithTop syntactic mismatch — same trick as C118a); (4) `include P in`
  needed for section-variable inclusion (and it must precede any docstring);
  (5) one declaration-order swap (`nextSupp_mul` after `nextRead_mul`); (6) `PackAt`
  universe ascription dropped (inferred `max (u_O+1) (v+1)`), `LiftAt.next`/
  `RungLift.pack` marked noncomputable.  The §1 coboundary lemmas, all §5 pricing
  lemmas, and the §6 assembly compiled with no mathematical rework.
* Footprint: `leanfinal/Uniformity/ChapI/I10RungPacks.lean` CREATED (966 lines);
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  No landed theorem
  file edited; no git operation; IFCG24 untouched.
