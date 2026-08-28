# UNIT A24B verdict — the A-C.24′ carrier repair: battery DECIDES §5, the guarded/anchored R₂ LANDS (2026-08-28)

**Charge:** (1) the S2 numeric battery deciding A24A §5's anchor-shift risk; (2) the
guarded/anchored classical R₂ in Lean with its basic bank + the clean product/scalar law
as far as the landed engine supports; (3) the A-C.24′ enactment draft (leanspec diff for
the orchestrator; leanspec byte-untouched by this unit).

## STATUS FIRST

| charge item | status | result |
|---|---|---|
| 1. the battery | **DONE, DECISIVE** | `verification/a24b_anchor_battery.py`, 12/12 oracle pins green. §5's risk is **REAL and realized in the exact F1.4 territory**: anchor shifts occur at EVERY observed μ-value tie (120 generic + 15 in the block-digit × complement sweep, would-be root exponent δ = 1 in all 135); the anchored read absorbs every one (0 violations). Only the anchored form survives — §4's expectation confirmed, with one genre surprise (§1.3). |
| 2. the carrier | **LANDED, sorry-free, Lean-core** | `leanfinal/Uniformity/ChapC/C136f14b.lean`: 15 public declarations, exit 0, ALL `[propext, Classical.choice, Quot.sound]`. The carrier `dv2ResPolyAnch`, THE off-side junk-0 guard, anchor well-definedness, additivity, the public shift identity (`lineRes_eq_shift`'s level-2 twin), the mod-Ψ kill, **the §5-risk absorber `dv2FullRead_modByMonic` (unconditional)**, anchored nonvanishing, and the on-side root-power dictionary. |
| 3. enactment draft | **DELIVERED (§4 below)** | exact C.38a′ insertion + C.38/C.39 re-signed rows over the repaired carrier; both bare axioms have ZERO landed consumers (re-verified), so the replacement is machine-ripple-free. leanspec untouched by this unit. |
| 4. gates | **PASS** | `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136f14b.lean` → EXIT 0; AxCheck footer: 15/15 Lean-core (no `exists_dvDissection`, no cite, no sorryAx). No landed or leanspec file edited; no git op; `C136d1.lean` untouched. |

## 1. THE BATTERY (results first, per charge)

`verification/a24b_anchor_battery.py` — integer-exact model of the landed S2 stack
(O = ℤ₂ as ℤ with exact v₂; frame (e₁,f₁,h) = (2,1,1), Φ′ = X²−2, H₀ = 1;
datum (u,ℓ,r) = (5,2,X−1), K₂ = 𝔽₂ with root β = 1; Ψ = Φ₂ = X⁴−4X²−4X+4;
outer (u₂,ℓ₂) = (21,2); g8 = Φ₂²−16Φ′). Every read definition transcribed from its
Lean source (file map in the script header). Deterministic (seed 24), single run.

**Oracle validation — 12/12 green** (a red would void the run): Φ₂ shape + degree 4;
`dev Φ′ Φ₂ = [−4X, 0, 1]` with height 5 and twistRead 5 = 1 (C130np5/IsTestKey);
dv2Hgt Ψ = 10 (`dv2Hgt_testKey`); dv2Supp g8 = 42, side {0,2} (`s2Hgt₃_g8`/RP-10);
dvSupp corr = 21 (`s2Hgt₂_corr`); `dv2FullRead(10, Ψ) = 0` (`dv2FullRead_testKey`);
cocycle grid exact & {0,1} (C28); `dv2Res_mul` and level-1 supp multiplicativity on
400 random pairs each. Junk counters (Lean junk branches hit inside used reads): 0.

**Part A — slot-0 mod-Ψ reduction over 8128 digit pairs (127 curated digits, deg ≤ 3):**

| observable | count |
|---|---|
| reduction-active pairs (deg ≥ 4) | 4692 |
| μ-value ties (dvSupp(Ψq) = dvSupp(ab)) | 120 |
| strict-below (remainder line under the key line) | 4572 |
| strict-above | 0 (forced by survival — consistency check) |
| survival failures (supp(dev₀) ≠ ka + kb) | 0 |
| **anchor shifts at ties** (jmin of reduced digit ≠ jmin of product) | **120 — EVERY tie** |
| anchor shifts at non-ties | 0 |
| δ histogram (would-be root exponent, `lineRes_eq_shift`-exact) | {1: 120} |
| bare `dv2Res` VALUE changes under reduction | 0 (β = 1 collapse — see below) |
| **anchored `dv2FullRead` changes under reduction** | **0** |

**Part A′ — the exact F1.4 territory** (block digit b₀ = −16Φ′ of g8 × the complement
sweep): 84 reduction-active products, **15 ties, ALL 15 with anchor shifts**, anchored
read stable in all, survival clean. **So the shift is NOT excluded for
short × complement products** — §5's fork resolves: *the on-side normalized-γg law over
the bare carrier is dead; only the anchored form survives.*

**Part B — the C.39 shape on f = g8·b (127 complements):** endpoint/deg additivity clean
(127/127); both the bare and the guarded law hold coefficientwise at S2 — expected,
because 𝔽₂ collapses all scalars to 1 AND g8's side {0,2} has no interior lattice slot
(sideDeg 1). **Part B′ — the wider block×block hunt** found the off-side channel LIVE in
genuine product territory: 3 off-side interior lattice slots among 45 products, with
**bare read = 1 (junk) vs anchored read = 0** in 2 of them (e.g. g8·g8 at lattice slot
j = 2, digit degree 2) — a numeric in-frame-shaped instance of A24A's off-side
refutation channel, which A24A had only as an abstract witness pair.

**Part C — the recorded-unproven carry law at S2:** `Dv2FullReadCarryLawStatement`'s
equality content (β = 1 makes root^δ = 1) holds **8128/8128**; the slot-0 anchored
product law and the slot-0 bare product law hold 0-failure; all 8128 reads nonzero
(consistent with the deg < keyDeg₂ nonvanishing theorem — a further model check).

### 1.3 Findings, honestly bounded

1. **Q1 (the §5 decision): the anchor shift is REALIZABLE — trivially reachable, and
   reachable in the F1.4 territory itself.** Simplest instance: a = b = Φ′;
   Φ′² has level-1 side {2} (jmin 2), `dev Ψ (Φ′²) 0 = 4X` has side {0} (jmin 0) — at a
   perfect tie (both supports 10 = dvSupp Ψ).
2. **Genre surprise (a finding, not a defect):** every observed shift is **injection,
   not cancellation** — the subtracted key line Ψ·q contributes a *lower* surviving slot
   (jmin drops), rather than killing the digit's leading read. δ = +1 uniformly in the
   swept family. Mechanism identical in consequence: the bare read of the reduced digit
   is `root^δ ×` the bare read of the product (exact by `lineRes_eq_shift`; now also by
   the landed `dv2FullReadPoly_eq_shift` + `dv2FullRead_modByMonic`).
3. **The β = 1 collapse, stated plainly:** at S2, K₂ = 𝔽₂, so the root-power VALUES are
   invisible (`bare_change = 0` is the collapse, not safety); the battery's decisive
   observable is the anchor itself (an integer slot index), which does not collapse.
   Likewise Part C certifies the carry law's equality content at S2 only; the δ-exponent
   bookkeeping is exact in Lean (`cocycle_mem`, `dv2Pin_dv2SideMin_mul_with_carry`).
4. **Scope:** the tie census is existence-decisive, not exhaustive (curated 127-digit
   family, fixed seed). Nothing hangs on exhaustiveness: one realized shift kills the
   bare-carrier law, and the absorber is now a THEOREM (§2), not a sampled claim.

## 2. THE CARRIER (leanfinal/Uniformity/ChapC/C136f14b.lean — landed, Lean-core)

15 public declarations, frame-generic (no S2 numeral), all
`[propext, Classical.choice, Quot.sound]`:

* `dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂` — **the guarded/anchored classical R₂**:
  coefficient t = `dv2FullRead L (M₂ − t·u₂) (dev Ψ f (min₂ + t·ℓ₂))` — C.25's
  fixed-grade `twistRead (M₀ − t·u)` one level up, with the anchored absolute read as
  the instrument. GC-1 pin binders `(M₂, hp₂)` exactly as C.25 carries `(M₀, hpin₂)`.
* coefficient bank: `dv2ResPolyAnch_coeff_of_le` / `_coeff_of_gt` /
  `natDegree_dv2ResPolyAnch_le` / `dv2ResPolyAnch_coeff_zero` (anchor well-definedness:
  coeff 0 = the side-min digit's exact-pin read).
* ★ `dv2ResPolyAnch_coeff_eq_zero_of_not_onSide` — **THE GUARD** (needs
  `Nat.Coprime u₂ ℓ₂`, engine-honest: the span exactness that keeps the line at
  nonnegative heights through the side degree). This is the clause whose absence powers
  A24A's `dv2ResPoly_scalar_shape_digit_kill` and the battery's Part B′ junk.
* `dv2Pin_lattice_of_onSide` — on-side lattice slots have exactly the line pin
  `M₂ − t·u₂` (and `t·u₂ ≤ M₂`).
* `dv2FullRead_dev_add` + `dv2ResPolyAnch_add` — additivity (coefficientwise at a
  support-line floor; polynomial-level at matched side data — the tie configuration).
* ★ `dv2FullReadPoly_eq_shift` — the PUBLIC level-2 twin of C134p1d's private
  `lineRes_eq_shift`, at the canonical anchor base:
  `dv2FullReadPoly L k z = dvResPoly(z) · X^((jmin − L.shift k)/L.ℓ)` at exact height.
  (New proof, transplanted; local re-derivations of C28's private `shift_spec`/
  `shift_unique` through H.51's public `class_sep`/`class_sep_bij`.)
* ★★ `dv2FullRead_mul_testKey` — the mod-Ψ kill: `dv2FullRead L k (Ψ·q) = 0` for every
  `k ≤ dv2Hgt(Ψ·q)` (below: landed vanishing; at: the shift identity +
  `C133mh3.dvResPoly_mul_gen` + `dvResPoly_testKey`, and `mk L.r` kills `L.r`).
* ★★ `dv2FullRead_modByMonic` / `dv2FullRead_dev_zero` — **the §5-risk absorber,
  UNCONDITIONAL**: `dv2FullRead L k (dev Ψ f 0) = dv2FullRead L k f` at any common
  height floor. §4 item 4's "mod-Ψ reduction read" supplier leg is CLOSED — the anchored
  carrier looks through the reduction that shifts the bare anchor.
* `dv2FullRead_ne_zero_of_exact` — anchored nonvanishing below the recipe degree.
* ★ `dv2ResPolyAnch_coeff_of_onSide` — **the on-side dictionary**:
  `coeff t = root^δₜ · dv2Res(digit)` with `δₜ = (jmin(digit) − shift(M₂ − t·u₂))/ℓ`
  SLOT-DEPENDENT — the machine form of why no constant scalar can relate the bare
  carrier across a product, and the shape in which PE3 F-1's root powers re-enter the
  anchored C.39′ faithfully.

**What the landed engine could NOT yet give (honest fence):** the full C.39′ scalar law
itself. Its supplier inventory after this unit: LANDED — the guard, additivity, the
shift identity, the kill, reduction stability, endpoint/deg/pin addition
(`C136l2e2.dv2SideMin_mul`/`dv2SideDeg_mul`/`dv2Pin_dv2SideMin_mul_with_carry`),
survival (`C132nv4`), the on-side dictionary. REMAINING — (i) the digit-split
convolution assembly `dev Ψ (g·z) J = Σ_{i+j=J} …` with the strict off-pair pricing
(L2E-05/07 banks exist), and (ii) the carry law (`Dv2FullReadCarryLawStatement`, still a
recorded `def`; battery-certified 8128/8128 at S2). These two are exactly §4 item 4's
first two legs; the third (the mod-Ψ read) closed here.

Verification (per increment; final):

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136f14b.lean
EXIT: 0    — 15/15 #print axioms: [propext, Classical.choice, Quot.sound]
```

Battery: `python3 verification/a24b_anchor_battery.py` → 12/12 oracles, counts as §1.

## 3. Flagged for human review (trust boundary — new statements)

`dv2ResPolyAnch` (the carrier definition), `dv2FullReadPoly_eq_shift`,
`dv2FullRead_modByMonic` (statement shapes; proofs are Lean-core and machine-checked).

## 4. THE A-C.24′ ENACTMENT DRAFT (for the orchestrator; leanspec NOT edited here)

Pre-verified: `dv2ResPoly_radical_eq` (C.38) and `dv2ResPoly_scalar` (C.39) have **zero
landed consumers** (repo-wide grep re-run this unit; only leanspec's own declarations +
docstring mentions + premise-carrying `C136l2e3.dv2ResPoly_radical_eq_of_scalar`, which
keeps compiling unchanged). The bare `dv2ResPoly` def and C.104's `repoRead := dv2Res`
stay byte-untouched.

### 4.1 INSERT after the C.38a cluster (leanspec/Leanspec/ChapC.lean, after the
`dv2ResPoly` def ending ≈ line 1700, before the C.38 header):

```lean
/-! ### NODE C.38a′ [def, A-C.24′ helper extension] — the anchored absolute read and
the GUARDED/ANCHORED classical level-2 residual polynomial [signed: A-C.24′].
The bare C.38a cluster above is untouched; C.38/C.39 are re-signed over THIS carrier. -/

/-- the fence-free absolute residual read at inner height `k`, based at the canonical
anchor slot `L.shift k` (the landed `C136l2e0.dv2FullReadPoly`, transcribed). -/
noncomputable def dv2FullReadPoly {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (k : ℕ) (P : Polynomial O) : Polynomial (F.stageField H₀ hpin) :=
  open Classical in
  ((Finset.range (k + 1)).filter
      (fun t => (L.shift k + L.ℓ * t) * L.u ≤ k)).sum fun t =>
    Polynomial.C
        (F.twistRead H₀ hpin ((k - (L.shift k + L.ℓ * t) * L.u) / L.ℓ)
          (dev F.key P (L.shift k + L.ℓ * t)))
      * Polynomial.X ^ t

/-- the anchored absolute coefficient read over `K₂`. -/
noncomputable def dv2FullRead {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (k : ℕ) (P : Polynomial O) : AdjoinRoot L.r :=
  AdjoinRoot.mk L.r (dv2FullReadPoly L k P)

/-- the GUARDED/ANCHORED classical level-2 residual polynomial (C.25 one level up):
coefficient `t` is the anchored read of the lattice digit at the side LINE height
`M₂ − t·u₂` — off-side slots contribute `0` and the reads are reduction-stable
(machine record: `leanfinal/Uniformity/ChapC/C136f14b.lean`, Lean-core). -/
noncomputable def dv2ResPolyAnch {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) (M₂ : ℕ)
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) :
    Polynomial (AdjoinRoot L.r) :=
  (Finset.range (dv2SideDeg L Ψ f u₂ ℓ₂ hne + 1)).sum fun t =>
    Polynomial.C (dv2FullRead L (M₂ - t * u₂)
        (dev Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne + t * ℓ₂)))
      * Polynomial.X ^ t
```

(If leanspec prefers not to duplicate `dv2FullReadPoly`'s body, the alternative is a
spec-side `axiom`-free import fence; the transcription above is the byte-faithful
default, matching how C.38a itself mirrors the leanfinal cluster.)

### 4.2 REPLACE the C.38 row (leanspec ≈ 1702–1717) — same conclusion shape, repaired
carrier, pin binders added, `hcop` added (engine-honest: the guarded carrier's junk-0
clause needs span exactness):

```lean
/-! ### NODE C.38 [lemma] — same degree, same radical (as same-prime-divisors)
[signed: A-C.1; RE-SIGNED: A-C.24′ over the guarded/anchored carrier] -/

-- [RE-SIGNED: A-C.24′, 2026-08-28 — record at C.39 below; conclusion shape unchanged,
-- carrier repaired `dv2ResPoly ↦ dv2ResPolyAnch`, GC-1 pin binders added, `hcop` added.]
axiom dv2ResPolyAnch_radical_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hseam : ℓ₂ * (L.ℓ * L.seam) < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    {M₂ M₂' : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))
    (hp₂' : dv2Pin L Ψ (blockFactor L f)
        (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne') = (M₂' : ℕ∞)) :
    (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).natDegree
        = (dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂').natDegree ∧
    ∀ q : Polynomial (AdjoinRoot L.r), q.Monic → Irreducible q →
      (q ∣ dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂
        ↔ q ∣ dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂')
```

### 4.3 REPLACE the C.39 row (leanspec ≈ 1719–1744) — the SOURCE-FAITHFUL conclusion
over the repaired carrier (§4 item 2's "near-byte-unchanged": scalar shape
`γ̂g · root^{c₁(pinHeight, c_g)}` verbatim from the signed row, with the complement read
anchored):

```lean
/-! ### NODE C.39 [lemma] — the per-side scalar, pin-height TERMINAL form
[signed: A-C.1; RE-SIGNED: A-C.24′ over the guarded/anchored carrier] -/

/-- `γ̂_g` — the complement's ANCHORED absolute read at its own level grade
(the pin-anchored normalization of PE3 F-1's `γ_g`; over `K₂` it is
`root^δ · γg` by the landed on-side dictionary `C136f14b.dv2ResPolyAnch_coeff_of_onSide`
mechanism — the bare `γg` def above is retained as the record). -/
noncomputable def γgAnch {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : AdjoinRoot L.r :=
  dv2FullRead L (complementConst L f) (f /ₘ blockFactor L f)

-- [RE-SIGNED: A-C.24′, 2026-08-28 — the A24A/A24B carrier repair.  THE RECORD:
-- the A-C.1 row `dv2ResPoly_scalar` (and the drafted A-C.24 `γg`-only repair) are BOTH
-- refuted over the bare carrier by two independent machine channels:
-- (1) the root-power channel (L2E1/L2E3): on the normalized own-height read the product
--     law is CLEAN (`C136l2e1.dv2Res_mul`), so the signed root factor forces
--     `root^cocycle = 1` — unsuppliable (A24A §1);
-- (2) the off-side junk channel (A24A §2, `C136f14.dv2ResPoly_scalar_shape_digit_kill`):
--     the bare carrier's lattice coefficients are unguarded own-height reads, so ANY
--     constant-scalar law forces a false digit-vanishing transfer; live product
--     instances: A24B battery Part B′ (block×block off-side slots, bare 1 vs anchored 0).
-- The A24B battery further REALIZED §5's on-side risk: at every observed μ-value tie
-- (120 generic + 15 in the F1.4 block-digit × complement territory) the mod-Ψ reduction
-- SHIFTS the digit's level-1 anchor (would-be root exponent δ = 1 throughout, injection
-- genre), so no per-slot normalized-γg law survives on the bare carrier; the anchored
-- read absorbs every event — now the THEOREM `C136f14b.dv2FullRead_modByMonic`
-- (Lean-core, unconditional).  Over the anchored carrier the SOURCE's own conclusion
-- shape (PE3 F-1: γ_g times the `c₁` pin-height root power) is the faithful form —
-- scalar byte-unchanged except the complement read anchored (`γg ↦ γgAnch`).
-- Proof-target inventory (A24B §2): landed — guard, additivity, shift identity, mod-Ψ
-- kill, reduction stability, endpoint/deg/pin addition, survival, on-side dictionary;
-- remaining — the digit-split convolution assembly + the carry law
-- (`C136l2e2.Dv2FullReadCarryLawStatement`, battery-certified 8128/8128 at S2).]
axiom dv2ResPolyAnch_scalar {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hnd : ¬ Ψ ∣ blockFactor L f)
    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hcop : Nat.Coprime u₂ ℓ₂)
    (hseam : ℓ₂ * (L.ℓ * L.seam) < u₂)
    (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty)
    (hne' : (dv2SideSet L Ψ (blockFactor L f) u₂ ℓ₂).Nonempty)
    {M₂ M₂' : ℕ}
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞))
    (hp₂' : dv2Pin L Ψ (blockFactor L f)
        (dv2SideMin L Ψ (blockFactor L f) u₂ ℓ₂ hne') = (M₂' : ℕ∞)) :
    dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂
      = Polynomial.C (γgAnch L f * (AdjoinRoot.root L.r)
            ^ (L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne')
                (complementConst L f)))
          * dv2ResPolyAnch L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂'
```

The old `dv2ResPoly_scalar` and `dv2ResPoly_radical_eq` axiom declarations are REMOVED
(zero consumers); the `γg`/`pinHeight` defs stay (γg is the record + the dictionary's
right-hand side; pinHeight is consumed by the new row).

### 4.4 Enactment checklist for the orchestrator

1. Apply 4.1–4.3; re-elaborate `leanspec/Leanspec/ChapC.lean` (the only file changed).
2. Re-run the repo-wide consumer grep for the two removed names (expected: comment hits
   only) and the standard leanfinal builds (this unit's file:
   `lake env lean Uniformity/ChapC/C136f14b.lean`, exit 0 as recorded).
3. REVIEW_QUEUE Tier-2 row: A-C.24′ enacted — cite-free (no new axiom SOURCE: the two
   new axiom rows are re-signings of the same EFF.HE6R1.39 source conclusion over the
   repaired carrier; the faithfulness argument is A24A §1's source-chain reading:
   the source's normalizers ARE pin-anchored).
4. Down-blueprint note: C.79 (the binding consumer, μ₂* = 2 decision table) now reads
   the CLASSICAL object as its root/irreducibility tests assume; C.68's side-geometry
   half is carrier-independent; C.77 unaffected (its Lean conclusion never mentioned the
   residual scalar).

## 5. File inventory

* `verification/a24b_anchor_battery.py` — NEW (the battery; §1).
* `leanfinal/Uniformity/ChapC/C136f14b.lean` — NEW (the carrier + bank; §2; exit 0,
  Lean-core ×15).
* `runs/wave-c/verdict_A24B.md` — this record.
* Nothing else touched: no leanspec edit, no landed-file edit, no git op,
  `C136d1.lean` untouched.
