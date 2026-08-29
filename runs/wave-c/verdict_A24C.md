# UNIT A24C verdict — the C.39 scalar's THIRD round: the SOURCE is vindicated, the TRANSCRIPTION dropped the carrier's twist (2026-08-28)

**Charge:** (1) source archaeology on EFF.HE6R1.39 (the chain .13 → .35 → .39): constant
scalar or slot-indexed family? a dropped stationarity hypothesis? the exact slot
quantifiers; (2) the battery angle (does the source's setting have the β = 1 collapse
built in?) — extend `verification/a24b_anchor_battery.py` with a weighted-vs-constant
discriminator at a non-collapsing frame; (3) the A-C.24″ draft + consumer check;
(4) land the corrected form if provable from F14C's assembler + carry law.

## THE SOURCE-READING ANSWER FIRST

**(a) .39 asserts a CONSTANT per-side scalar — and it is HONEST — but between the
source's OWN residual polynomials, which are TWIST-CARRYING objects.** The transcription
(both the A-C.1 row and the enacted A-C.24′ row) equated the source's `R_{λ₂}` with an
UNTWISTED per-slot carrier; over that carrier the same content is exactly F14C's
slot-indexed family. The defect of the enacted row is a **missing per-slot twist in the
carrier definition**, not a missing stationarity hypothesis.

**(b) The source carries NO stationarity hypothesis, and NEEDS NONE.** The stationarity
F14C demanded (§2.2) is supplied identically by the twist bookkeeping: the exponent
identity

```
c₁(M, c) + ε_t(M) = c₁(M − t·u₂, c) + ε_t(M + c)        (ID1, exact, all t·u₂ ≤ M)
```

holds as pure cocycle arithmetic (from ℓ·c₁(a,b) = s(a) + s(b) − s(a+b) alone), where
ε_t are the source's own twist exponents (see (d)). ID1 converts F14C's slot-varying
family over the anchored carrier into the constant pin-height scalar over the twisted
carrier — no divisibility `ℓ ∣ u₂`, no matched-slot reading, no new premise.

**(c) The source's quantifiers:** the identity is **per side λ₂** (clause (b) of
LEMMA HE6R1-2 quantifies "for **every** rational κ₂ > T₂"; clause (c) "At every such
side"). The scalar is per-side constant with the exponent "**free to differ side by
side**" (.35, verbatim). **There is no quantifier over slots t anywhere in the chain**
— t is bound inside the definition of `R_{λ₂}` (the source's residual polynomial), which
is where the per-slot bookkeeping lives.

### (d) The exact spec quotes (the evidence chain)

**EFF.HE6R1.13 (LEMMA HE6R1-2, the transcribed lemma), CHAIN paragraph (spec line 390):**
> "CHAIN on clause (c)'s scalar (rule 25 — three layers). [r1′] identifies the per-side
> scalar as γ_g → PE2 F-2 (.35) adds the cocycle unit: R^f_{λ₂} = γ_g ·
> β^{c₁(h_{F₂,f_S}(λ₂), c_g)} · R^{f_S}_{λ₂} → PE3 F-1 (.39) corrects the exponent's
> argument to the pin height: R^f_{λ₂} = γ_g · β^{c₁(m₁^{f_S}, c_g)} · R^{f_S}_{λ₂}.
> TERMINAL: PE3 F-1. At ℓ = 1 — the branch this note decides and its battery runs —
> s(·) ≡ 0, c₁ ≡ 0, and the scalar is γ_g alone."

**EFF.HE6R1.35 (PE2 F-2), the per-side constancy claim (verbatim):**
> "the corrected identification per side λ₂ is R^f_{λ₂} = γ_g · β^{c₁(h_{F₂,f_S}(λ₂),
> c_g)} · R^{f_S}_{λ₂}, **a fixed nonzero element of K₂^× per side, with the exponent c₁
> free to differ side by side**."

**EFF.HE6R1.39 (PE3 F-1), the TERMINAL derivation mechanism (verbatim):**
> "normalize each side by n₂(m₁)·Ψ(ξ)^{j₁} — the normalization HE7-7′(b)'s own proof
> uses — where m₁ := dv₂(A^{(2)}_{j₁}) is the PIN height at the side's starting index
> j₁, an integer; … the cocycle composition then runs entirely over ℤ, and the corrected
> per-side identification is R^f_{λ₂} = γ_g · β^{c₁(m₁^{f_S}, c_g)} · R^{f_S}_{λ₂}"

The derivation is POINTWISE (a single normalizer per side, at the pin), "converted to a
polynomial identity by the same generic-letter degree argument" (.35). The pointwise
route composes ONE cocycle per side — the polynomial identity it yields is between the
polynomials for which the pointwise evaluation display holds, and those are the
twist-carrying ones:

**EFF.HE7.08 (the level-2 twist CONVENTION, verbatim):**
> "At level 2 the normalizers ϖ^m Φ′^s genuinely mix two generators, and
> n₂(k)·n₂(k′)/n₂(k+k′) = (Φ′^ℓ/ϖ^u)^c, c := (s(k)+s(k′)−s(k+k′))/ℓ ∈ ℤ … Consequently
> **every level-2 residual polynomial is defined only relative to a FIXED choice of n₂,
> and changing the choice multiplies its coefficients by explicit powers of β**. Every
> statement used below is twist-invariant … The battery's reader carries the twist
> explicitly, and tooth **HE7-T-BADTWIST** shows that dropping it mispredicts σ — so
> this is not a bookkeeping remark."

**EFF.HE7.30 (LEMMA HE7-7 Step 2, the residual assembly, verbatim) — the per-slot twist
in the source's own evaluation:**
> "dividing by n₂(d₂u₂)(ξ) and collecting, term t becomes
> [C_t(ξ)/n₂((d₂−t)u₂)(ξ)]·[Ψ(ξ)^{ℓ₂}/n₂(u₂)(ξ)]^t·**τ_t with res(τ_t) = β_ξ^{c_t} the
> explicit twist of §S1**"

**EFF.HE7.27 (DEFINITION HE7-3), the source's OWN CLOSED FORM for the twist exponents
(verbatim):**
> "let **c_t := (s(d₂u₂ − tu₂) + t·s(u₂) − s(d₂u₂))/ℓ** be the twist exponents of §S1
> at m₁ := d₂u₂"

(headline: "the level-2 test family; **the residues carry the INVERSE TWIST**"; and
EFF.HE7.34/HE7-7′'s proof: "the twist of §S1 carried through the residual assembly
exactly as in Step 2 above".) So the source's residual polynomial at a side with pin
`m₁` carries, at slot `t`, the twist exponent

```
ε_t(m₁) = (s(m₁ − t·u₂) + t·s(u₂) − s(m₁)) / ℓ
        = c₁(m₁ − t·u₂, t·u₂) + Σ_{i<t} c₁(u₂, i·u₂)      (cocycle-sum form, exact)
```

— DEFINITION HE7-3's display evaluated at the generic pin. The level-1 comparison locks
this reading: HE6's §S1 residual (spec/EFF-HE6.md line 400) is
`R_λ(Z) := Σ_t res(A_{j₁+tℓ}(θ)/ϖ(θ)^{m₁−tu}) Z^t` — per-slot normalizers at the LINE
heights — and at level 1 the ϖ-power normalizers compose exactly (no cocycle), which is
why HE6 carries no twist ("At level 1 HE6 could take all normalizers to be powers of the
single element ϖ, killing the cocycle", HE7.08). At level 2 the same per-slot definition
forces the τ_t twist, and the source carries it in the object (machine-load-bearing:
tooth HE7-T-BADTWIST, "21 (p, s, member) reads change when the twist is dropped; twisted
read == PARI 480/480").

### (e) The reconciliation identity (all three rounds agree)

With `s = L.shift`, `c₁ = L.cocycle` (C.28; ℓ·c₁(a,b) = s(a)+s(b)−s(a+b) is
`LevelDatum.cocycle_mem`), and pins `m₁^f = m₁^{f_S} + c_g`:

* F14C's honest family over the UNTWISTED anchored carrier (`dv2ResPolyAnch`):
  `coeff_t(f) = β^{c₁(M₂′ − t·u₂, c_g)} · γ̂_g · coeff_t(f_S)` — slot-varying.
* The twisted carriers `R̃_t := β^{ε_t(pin)}·coeff_t` then satisfy
  `R̃_t(f) = γ_g-hat · β^{c₁(M₂′, c_g)} · R̃_t(f_S)` — CONSTANT, pin-height exponent,
  **exactly the .39 display** — because of ID1 (§(b)), which is itself an instance of
  the 2-cocycle identity for c₁. Both machine-checked: numerically (battery Part D
  oracles, grids exact) and in Lean (`C136f14d.twistExp_cocycle_transfer`, Lean-core).

So: round 1's refutation (bare carrier), round 2's carrier repair (anchored), round 3's
family (slot weights) and THIS round's source reading are ONE consistent picture; the
only defective artifact is the enacted A-C.24′ row's CONSTANT scalar over the UNTWISTED
anchored carrier, which is refuted at any frame with β ≠ 1 and a parity-varying slot
line (battery Part D below) — S2 (β = 1) and the source's decided branch (ℓ = 1, c₁ ≡ 0)
are both degenerate for this question, which is why two rounds of battery could not see
it.

## THE BATTERY ANGLE (charge 2)

**Yes — the source's setting has the collapse built in, twice over:** the source's
decided branch is ℓ = 1, where "s(·) ≡ 0, c₁ ≡ 0, and the scalar is γ_g alone" (.13/.35/
.39 all state it) — the twist exponents ε_t ≡ 0 AND the cocycle ≡ 0, so constant-vs-
family is invisible; the battery HE6R1 ran is at ℓ = 1 (n = 8). The general-ℓ statement
is .13's proof-only configuration (HE6R1-BOX-2: "μ ≥ 5 … proof-only"). At the landed S2
site ℓ = 2 but K₂ = 𝔽₂ (β = 1) — value-collapse (A24B's finding). The scalar display at
general ℓ was never machine-tested in a discriminating regime; its honesty rests on the
twisted-carrier reading of §(d), NOT on a degenerate regime.

**The extension** (`verification/a24b_anchor_battery.py`, Part D — appended; every
pre-existing function, oracle and output byte-untouched): the NON-COLLAPSING synthetic
frame keeps the S2 inner tower (Φ′ = X²−2, u = 5, ℓ = 2 — shift/cocycle unchanged) and
replaces the datum residual by r = Z²+Z+1, so K₂ = 𝔽₄ and root β has order 3 (β ≠ 1).
Oracles at the new frame are the LANDED FRAME-GENERIC THEOREMS (they must hold at any
`LevelDatum`): the carry law `dv2FullRead_mul_of_eq` and `dv2Res_mul` (both Ψ-free) —
564 random pairs each, 0 failures — plus exact grids for the HE7-3 closed form and the
two exponent identities ID1/ID2. All green (a red voids the run).

**Honest scope fence, recorded in the script:** the frame is synthetic — Ψ = Φ₂ is the
composed key of the d_r = 1 datum, NOT of the 𝔽₄ datum (whose key has degree 8). So
`IsTestKey L Ψ` FAILS at this frame, hence the mod-Ψ kill (`dv2FullRead_mul_testKey`)
and its consequence `dv2FullRead_modByMonic` do not apply: dvResPoly(Φ₂) = 1 + Z has
mk_{Z−1} image 0 (the S2 pin) but mk_{Z²+Z+1} image 1 + β = β² ≠ 0. The battery
LOCALIZES this: exactly 15 of 127 complements hit a mod-Ψ tie-overflow with a nonzero
kill-leak, every leak is additivity-accounted (0 accounting failures: read(dev₀) +
read(Ψq) = read(product) in 𝔽₄, e.g. 1 + β² = β), and the contaminated set coincides
with the odd-c_z set (15 = 15; at deg Ψ = 4 the parity arithmetic forces every odd-c_z
complement into overflow — so carrier-level exponent variation and contamination
coincide STRUCTURALLY at this frame; a fully clean carrier-level discrimination needs
the genuine degree-8 𝔽₄ key, recorded as out of scope).

**The discriminator therefore runs at the UNREDUCED slot level** — pure carry-law
territory, kill-free, faithful at this frame — which is the level the landed
`dv2FullRead_modByMonic` THEOREM (whose IsTestKey premise holds at genuine C.39 frames)
equates to the anchored coefficients. Results (127 complements z on the g8 territory,
side-additive 127/127):

| test (slot reads r_t = read((Mg−t·u₂)+c_z, digit_t(g8)·z)) | result |
|---|---|
| **FAMILY** r_t = β^{c₁(Mg−t·u₂, c_z)}·γ̂·anch(g8)_t (F14C's form) | **127/127 hold** |
| **ENACTED constant** r_t = β^{c₁(Mg, c_z)}·γ̂·anch(g8)_t (A-C.24′ byte-shape) | **15 FAILURES**/112 — fails at exactly the odd-c_z complements |
| **SOURCE law over the TWISTED reads** β^{ε_t(Mf)}·r_t = [β^{c₁(Mg,c_z)}·γ̂]·β^{ε_t(Mg)}·anch(g8)_t (the .39 display) | **127/127 hold** |

Exhibit (z = X²+2X−2, c_z = 5, γ̂ = 1): slot reads [β, 1] = β^{[1,0]}·anch(g8) — the
family with varying exponents; the enacted row pins exponent 1 at both slots — false at
slot 1. RADICAL exhibit at the same z: the family-weighted linear residual has root β·(anch(g8)'s
root) — same-radical FAILS over the untwisted carrier (C.38-over-anch is threatened by
the same mechanism); the twisted carriers' constant law restores it. Kill-clean
carrier-level subset (112, all even c_z): family = enacted = twisted, 112/112 each
(degenerate there, as predicted). The twisted PRODUCT law
tw(gz) = β^{c₁(Mg,Mz)}·tw(g)·tw(z) holds on 22/28 additive block pairs with ALL 6
failures kill-contaminated (uncontaminated failures = 0).

## THE LANDING (charge 4): `leanfinal/Uniformity/ChapC/C136f14d.lean`

**LANDED, sorry-free, Lean-core ×12** (exit 0; every declaration
`[propext, Classical.choice, Quot.sound]` — no cite, no `exists_dvDissection`, no
sorryAx). Verified per increment (3 increments, `lake env lean` each; never bare
`lake build`):

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136f14d.lean
EXIT: 0    — 12/12 #print axioms: [propext, Classical.choice, Quot.sound]
```

* `twistExp L u₂ M₂ t` — DEFINITION HE7-3's twist exponents at the generic pin, in the
  cocycle-sum form `c₁(M₂−t·u₂, t·u₂) + Σ_{i<t} c₁(u₂, i·u₂)` (grid-identical to the
  source's closed form — battery Part D oracle); `twistExp_zero` (`ε_0 = 0`: the anchor
  clause survives the twist verbatim).
* ★ `twistExp_cocycle_transfer` (**ID1**) and ★ `twistExp_cocycle_mul` (**ID2**) — the
  two exponent identities, proved from `LevelDatum.cocycle_mem` + shift subadditivity
  (a new private `shift_add_le`, C.28's `hsum` step exposed — needed to kill the
  truncated-subtraction branch omega cannot exclude) by pure ℕ arithmetic.
* `dv2ResPolyTw` — **the SOURCE-faithful twisted carrier**: coefficient `t` is
  `root^{ε_t} ·` the anchored coefficient. `dv2ResPolyTw_coeff` (unconditional
  extraction), `dv2ResPolyTw_coeff_zero` (the exact-pin anchor clause).
* ★★ `dv2ResPolyTw_scalar_of_anch_family` — **THE A-C.24″ MECHANISM**: from F14C's
  honest slot-indexed family over `dv2ResPolyAnch` (+ pin addition `M₂ = M₂′ + c`, the
  side-degree match, and the line floor), the source display —
  `R̃(f) = C(root^{c₁(M₂′,c)}·γ̂) · R̃(f_S)`, ONE constant per side, PIN-HEIGHT
  exponent. ID1 is the whole proof; **no stationarity premise exists in the statement**.
* ★★ `dv2ResPolyTw_mul_of_weightedConv` — the classical theorem-of-the-product shape:
  from F14C's weighted-convolution conclusion (`dv2ResPolyAnch(gz) =
  dv2ResPolyAnchWeightedConv …`), `R̃(g·z) = C(root^{c₁(Mg,Mz)}) · R̃(g) · R̃(z)`.
  ID2 absorbs every antidiagonal slot weight. (The twisted carrier is THE
  multiplicative object — battery D5: 22/28 additive block pairs, all 6 failures
  kill-contaminated, 0 uncontaminated.)
* Bridge + adapter: `root_ne_zero` (private; from the datum's `r(0) ≠ 0`),
  `dv2ResPolyTw_coeff_eq_zero_iff` (the GUARD transfers verbatim),
  `natDegree_dv2ResPolyTw_eq` (the twist is degree-invariant),
  `dv2ResPolyTw_radical_eq_of_scalar` (the F1.5 adapter over the twisted carrier).

**What remains open (unchanged from F14C):** the digit-split convolution supplier
(F14C §2.1 — the premise of the weighted assembler; battery-certified at S2 8128/8128
and now shape-certified at the 𝔽₄ frame through the unreduced level). The A-C.24″
signed row stays an axiom until that supplier lands; everything from the family to the
source display is now THEOREM.

**Conditionality of the star theorems, stated honestly:** both are CONDITIONAL
transfers (the family/weighted-conv premises are hypotheses, matching F14C's honest
remainder); their content is that the source's constant-scalar and product displays are
EXACTLY equivalent to those premises — the two "missing stationarity" and
"slot-varying weight" obstructions of F14C are discharged by twist bookkeeping alone.

## THE A-C.24″ ENACTMENT DRAFT (leanspec NOT edited by this unit)

Pre-verified: `dv2ResPolyAnch_scalar` and `dv2ResPolyAnch_radical_eq` have **zero
landed proof consumers** (repo grep this unit: the only leanfinal hit is C136f14c's
boundary COMMENT); BP.C.79/BP.C.38/BP.C.39 are blueprint-OPEN. The re-sign is
machine-ripple-free.

### Draft 1 — INSERT after the C.38a′ cluster (after the `dv2ResPolyAnch` def):

```lean
/-- DEFINITION HE7-3's twist exponents at the generic pin (SOURCE: spec/EFF-HE7.md
.27, verbatim closed form `c_t := (s(m₁−tu₂) + t·s(u₂) − s(m₁))/ℓ`; exact cocycle-sum
form; machine record: leanfinal/Uniformity/ChapC/C136f14d.lean, Lean-core). -/
def twistExp {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (u₂ M₂ t : ℕ) : ℕ :=
  L.cocycle (M₂ - t * u₂) (t * u₂) + ∑ i ∈ Finset.range t, L.cocycle u₂ (i * u₂)

/-- the SOURCE-faithful TWISTED level-2 residual polynomial — the classical object:
EFF.HE7.08's convention ("changing the choice multiplies its coefficients by explicit
powers of β") with EFF.HE7.30 Step 2's assembly twist carried IN the carrier.
EFF.HE6R1.39's per-side constant scalar is a claim about THIS carrier. -/
noncomputable def dv2ResPolyTw {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (Ψ f : Polynomial O) (u₂ ℓ₂ : ℕ) (hne : (dv2SideSet L Ψ f u₂ ℓ₂).Nonempty) (M₂ : ℕ)
    (hp₂ : dv2Pin L Ψ f (dv2SideMin L Ψ f u₂ ℓ₂ hne) = (M₂ : ℕ∞)) :
    Polynomial (AdjoinRoot L.r) :=
  (Finset.range (dv2SideDeg L Ψ f u₂ ℓ₂ hne + 1)).sum fun t =>
    Polynomial.C (AdjoinRoot.root L.r ^ twistExp L u₂ M₂ t
        * (dv2ResPolyAnch L Ψ f u₂ ℓ₂ hne M₂ hp₂).coeff t)
      * Polynomial.X ^ t
```

(`dv2ResPolyAnch` and its whole C136f14b/c bank stay byte-untouched — the twisted
carrier is DEFINED over it, and the guard/anchor/reduction-stability clauses transfer
by `dv2ResPolyTw_coeff_eq_zero_iff`/`twistExp_zero`.)

### Draft 2 — RE-SIGN the C.39 row: `dv2ResPolyAnch_scalar ↦ dv2ResPolyTw_scalar`

Hypothesis block byte-identical to the enacted A-C.24′ row; conclusion with the SAME
scalar (γgAnch · root^{c₁(pinHeight, complementConst)} — the .39 display, byte-kept)
over the twisted carrier:

```lean
-- [RE-SIGNED: A-C.24″, 2026-08-29 — the A24C source-archaeology round.  THE RECORD:
-- EFF.HE6R1.39's constant per-side scalar is asserted between the source's OWN
-- residual polynomials, which CARRY DEFINITION HE7-3's per-slot twist exponents
-- (EFF.HE7.08 / EFF.HE7.30 Step 2 / tooth HE7-T-BADTWIST); the A-C.24′ row
-- transcribed that conclusion onto the UNTWISTED anchored carrier, over which the
-- honest law is F14C's slot-indexed family root^{c₁(M₂′−t·u₂, c_g)} — REFUTED as a
-- constant law at any β ≠ 1 frame with a parity-varying slot line (battery Part D:
-- 15/127 explicit failures at the 𝔽₄ frame, exactly the odd-c_z complements; S2's
-- β = 1 and the source's decided ℓ = 1 branch are both degenerate for this).  No
-- stationarity hypothesis was dropped: the twist-transfer identity ID1
-- (C136f14d.twistExp_cocycle_transfer, Lean-core) converts the family into THIS
-- row's constant law exactly — the machine bridge is
-- C136f14d.dv2ResPolyTw_scalar_of_anch_family.  Remaining supplier unchanged from
-- F14C: the digit-split convolution (§2.1).]
axiom dv2ResPolyTw_scalar {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
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
    dv2ResPolyTw L Ψ f u₂ ℓ₂ hne M₂ hp₂
      = Polynomial.C (γgAnch L f * (AdjoinRoot.root L.r)
            ^ (L.cocycle (pinHeight L Ψ (blockFactor L f) u₂ ℓ₂ hne')
                (complementConst L f)))
          * dv2ResPolyTw L Ψ (blockFactor L f) u₂ ℓ₂ hne' M₂' hp₂'
```

### Draft 3 — RE-SIGN the C.38 row over the SAME carrier

`dv2ResPolyAnch_radical_eq ↦ dv2ResPolyTw_radical_eq`, conclusion shape unchanged
(equal `natDegree` + same monic irreducible divisors), carrier `dv2ResPolyTw`. The
DEGREE half is carrier-indifferent (`natDegree_dv2ResPolyTw_eq`), but the RADICAL half
is NOT twist-invariant slot-wise (battery radical exhibit: the family-weighted linear
residual's root differs from the block's by a β-power) — the radical row MUST live on
the twisted carrier.

### Draft 4 — the fate of the A-C.24′ rows and the faithfulness note

* `dv2ResPolyAnch_scalar`: **REMOVED** (refuted-in-mechanism: battery D0's 15 explicit
  failures transport to the anch coefficients at any genuine frame through the LANDED
  `dv2FullRead_modByMonic` theorem, whose IsTestKey premise holds there). Zero
  consumers; C136f14c's boundary comment already records the obstruction.
* `dv2ResPolyAnch_radical_eq`: **REMOVED** for the same reason (radical not slot-twist
  invariant); the C.38 conclusion re-signed per Draft 3.
* `γgAnch`, `pinHeight`, the C.38a′ defs: all stay (consumed by the new rows).
* Faithfulness: cite-free — the re-sign is the SAME EFF.HE6R1.39 source conclusion,
  now over the carrier the source itself defines (the twist prescription is
  DEFINITION HE7-3 + EFF.HE7.08, quoted above); the faithfulness argument is this
  verdict's §(d), strictly tighter than A24B's (which read only the normalizer
  mechanism, not the residual assembly's per-slot twist).

## THE CONSUMER CHECK (C.79, per A24A's charge)

**C.79 needs the TWISTED (classical) object — the constant, not the family, and on the
right carrier:**

* C.79 (the μ₂* = 2 decision table) tests roots/irreducibility of the (γ-scaled)
  quadratic residual. The source object whose factorization the OM label theory reads
  is `R_{λ₂}` with the twist carried: COROLLARY HE7-7″ defines the level-2 label by
  `ι(R_{λ₂})(β₂) = 0`, "well defined because R_{λ₂} is a fixed element of K₂[Z] once
  the n₂ convention is fixed" — and the evaluation display behind it (HE7-7′(b)) holds
  for the twist-carrying assembly (EFF.HE7.30 Step 2). Root/irreducibility structure
  is NOT preserved between the twisted and untwisted carriers (the per-slot β-powers
  are non-geometric; battery radical exhibit) — so a C.79 built over `dv2ResPolyAnch`
  would test the WRONG polynomial exactly at β ≠ 1 frames.
* EFF.HE7.08's twist-invariance fence ("vanishing/non-vanishing at a residue, degree,
  and the multiset of irreducible factors up to K₂^×-scaling") is an invariance under
  CHANGE OF THE n₂ CHOICE — i.e., between twisted carriers at different conventions —
  not between twisted and untwisted. Degree-only consumers (C.68's side-geometry half)
  are carrier-indifferent (`natDegree_dv2ResPolyTw_eq`).
* BP.C.79 depends on BP.C.38/BP.C.39 (DAG rows 528–529) and is OPEN — it inherits the
  re-signed carrier automatically at transcription time.

## FILE INVENTORY + GATES

* `runs/wave-c/verdict_A24C.md` — this record.
* `leanfinal/Uniformity/ChapC/C136f14d.lean` — NEW (12 declarations, exit 0, Lean-core
  ×12; three increments, each verified by scoped `lake env lean`).
* `verification/a24b_anchor_battery.py` — EXTENDED (Part D appended, charge-authorized;
  every pre-existing function and oracle byte-untouched; the S2 sections reproduce
  A24B's recorded outputs exactly, same seed).
* No leanspec edit; no landed-file edit; no git operation. Flagged for human review
  (trust boundary — new statement shapes): `twistExp`, `dv2ResPolyTw`,
  `dv2ResPolyTw_scalar_of_anch_family`'s premise shape (the family form), and the
  Draft 2 axiom text (the A-C.24″ re-sign itself, which is the orchestrator's call).
