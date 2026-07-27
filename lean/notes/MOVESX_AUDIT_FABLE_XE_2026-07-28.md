# MOVESX XE.2/XE.3 RESTATED — fresh-Fable audit (2026-07-28)

**Charge.** Fresh-instance audit of the RESTATED units XE.2 (`envelopeExp`) and XE.3
(`envelopeSqrt`) + the §7 REFUTATION RECORD of
`lean/notes/MOVESX_LEAN_BLUEPRINT_2026-07-28.md`, and the Lean files
`lean/LeanUrat/MovesX/XE2.lean`, `XE3.lean`. Ground truth read in full:
`lean/notes/MOVES_2026-07-24.md` lines 11170–11470 (the (X2-*) kernels, the envelope
display with the (N−1−c_cap) numerator, the CONDITIONALITY SUMMARY at ~11448–11451).
Auditor did NOT fix anything; quote-and-classify only.

**VERDICT: ACCEPT — 0 critical / 0 gaps.** The restated ∃N₀-before-∀p forms are
(a) tag-complete against the CONDITIONALITY SUMMARY with only disclosed, conservative
extras, (b) escaped by the certified countermodel exactly as the §7 walk claims,
(c) NOT refutable — a dedicated new-countermodel search failed against a pinch argument
that the tags force (details below; no `max(0,·)` clamp is needed), and (d) byte-faithful
to the blueprint §3 specs.

---

## 1. Tag lists vs the CONDITIONALITY SUMMARY (MOVES ~11448–11451)

Summary line, exponential: "exponential GIVEN
(X.2)+X.1b+(ALIGN-inc)+(X2-TAILS)+(X2-BRIDGE)+(X2-CAP)".

XE.2 hypotheses: `PR : X2ProgressP` = (X.2) ✓ · `WC : WeightChargeFullP` = X.1b(full)
✓ (the full-burden form is the one the note pairs with (ALIGN-inc) — rev-2 finding 11
display at 11170–11180) · `AL : X1aAlignP n X ⟨true, false⟩` = (ALIGN-inc) only
(`AlignState.inc = true, recn = false`; checked against `certified` in Defs) ✓ ·
`TL : X2TailsP` = (X2-TAILS) ✓ · `BR : X2BridgeP` = (X2-BRIDGE) ✓ · `CP : X2CapP` =
(X2-CAP) ✓. **None of the summary's six tags dropped.**

Summary line, √N: "(X2-HYP)+(X2-AFF)+(X2-CAP)+X.1b+(ALIGN-inc)+(X2-TAILS)+(X2-BRIDGE)".
XE.3 hypotheses: AF, CP, WC, AL⟨true,false⟩, TL, BR — six of seven present by name;
(X2-HYP) is NOT a hypothesis but is legitimately REPLACED by its derivation: the note
itself types (X2-HYP) as "DERIVED given (X2-AFF) ∧ (X2-CAP)" (11248–11254), and unit
XD.4 `x2hypAssembled` (blueprint lines 434–443) is exactly that derivation from
`AF ∧ CP` over the context, imported by XE3.lean. Replacing a DERIVED tag by its named
inputs + the deriving unit is fidelity-preserving (strictly: it discharges the tag
in-corpus instead of assuming it). **None dropped.**

**Additions (all disclosed in the blueprint's TAG CHECK, all conservative):**
- `AF` in XE.2: not in the summary's exponential line, but the note's own envelope block
  opens "Given (X2-BRIDGE) + (X2-CAP) + (X2-AFF)" (11324) and traces the exponential
  constants to "c₀ ((X2-AFF))" (11341–11342). The summary line under-lists relative to
  the note's own display; the blueprint takes the superset — the honest side (extra
  hypotheses weaken the theorem; under-conditioning would be the sin, over-conditioning
  is safe).
- `NS : NsNullP` (both units): the (ns-null) tag, per the (NS-c) rule "the tag remains
  displayed at every consumption" (11369–11372) and the bridge decomposition's "the
  first three of mass 0 (… (ns-null), closed …)" (11303).
- `R : X3aRouteP` (both units): X.3(a)'s route tags, consumed by the bridge's
  first-three-pieces mass (InfTree ⊆ discZero needs X.3(a); 11303–11304).
  OBSERVATION (no action): `R` is formally REDUNDANT — `AL ∧ WC` already inhabit its
  second disjunct (`Or.inr ⟨AL, WC⟩ : X3aRouteP`, as the refutation witness's own `Rce`
  demonstrates). Harmless; keeps the note's tag name visible in the signature.

## 2. The countermodel's escape, re-run

Countermodel (both certificates, read in full: `XE2_refutation_witness.lean`,
`XE3_REFUTATION_2026-07-27.lean`): n = 2, every f gets the root-only tree
(Branch = Unit/PUnit, hist = []), threshold 1, capDetectable with detCap 1 (so
threshold + capHB = 2), `DetectedAt _ N := 2 ≤ N`, `Undec N` = univ for N < 2 and ∅
for N ≥ 2, Dirac content at f₀ = X² + X (disc = 1, a unit at every p). All nine/eight
tags verified to hold in the artifact. The OLD refutation lived at the FIXED N = 1:
frac(Undec 1) = 1 for every p, killing `∃ c3 c4, … ∀ p N` as p → ∞.

Against the RESTATED form: pick N₀ = 2, c3 = c4 = 1. For every p and every N ≥ 2,
Undec N = ∅, frac ∅ = 0 (f₀ ∉ ∅), and 0 ≤ 1·p^(−N) since the RHS is positive.
N ∈ {0, 1} are outside the claim. **Escape confirmed.** The blueprint's aside is also
right: this K has c_cap = 1, so the INTENDED N₀ formula (N > 1 + c_cap, d\*(N) = N−1 >
⌊log₂ 2⌋ = 1, h\*(N) ≥ 1) gives N₀ = 3 — also fine under ∃N₀. The retained
transcription-check `example` (`XE2_refutation_transcription_check.lean` line 22–28)
now no longer typechecks against the restated declaration (old ∀N closure vs new ∃N₀
Pi-type), which is exactly the negative-control semantics §7 assigns it.

## 3. New-countermodel search against the restated form: FAILED (statement stands)

The adversary must produce (n, X, K) satisfying all tags such that for EVERY
(N₀, c3, c4) — (n,K)-only, bound before p — some p, N ≥ N₀ violates
frac(Undec N) ≤ c3·p^(−c4·N) (resp. ·√N). The tags pinch this off:

**The pinch.** For any model, any p, N:
frac(Undec N) ≤ frac(Undec N ∩ ¬Wit N) + frac(Wit N) = 0 + frac(Wit N), by BR's SECOND
clause (the no-witness piece is frac-null BY HYPOTHESIS) + `frac_union_le`/`frac_mono`.
Wit N = {f | ∃ b leaf ∧ ns-free ∧ N < threshold b + capHB b}; the witness b satisfies
`FourthPieceB` via its first disjunct, so PR (resp. XD.4 from AF ∧ CP) applies:
- **Tall leg:** maxH(hist b) ≥ ch·N − ch' puts f ∈ TallEvent(⌈ch·N − ch'⌉₊) (maxH ≥ 1
  forces a nonempty history attaining it); TL caps this at CT·p^(−cT·(ch·N − ch')).
  For N ≥ 2·ch'/ch the exponent is ≥ (cT·ch/2)·N — p-free constants (ch' < 0 only
  helps).
- **Deep leg:** dTotal(hist b) ≥ cd·N − cd'. For f ∉ discZero, gmnLink puts f in the
  stratum of hist b; then AL + GMN `p2` give countPop incT12 = dCert⟨true,false⟩ ≤
  vdisc/2 (dCert = incT12-count checked against `certified`/`popOf?`: continuing T2
  is forced increment by `t2inc`); WC gives recT1 + t4 ≤ s·vdisc; `HistWF.degProd` +
  `t3inc` + e ≥ 2 give #t3 ≤ log₂ n. So vdisc ≥ (cd·N − cd' − log₂ n)/(s + 1/2) =: D(N),
  linear in N. f then lies in {vdisc ≥ ⌈D(N)⌉ ∨ discZero} — an event that contains the
  f ∈ discZero case FOR FREE (the `vdisc_le_tail` event includes discZero by
  construction, so the valuation junk-value channel is closed). `vdisc_le_tail` caps its
  frac by the CONCRETE `tailCount(p,n,D)/p^(nD)` — a model-independent number the
  adversary cannot game — and (3b) bounds that by (n−1)·p^(−⌈(D − n·v_p(n))/(n−1)⌉)
  ≤ (n−1)·n^(n/(n−1))·p^(−D/(n−1)) via p^(v_p(n)) ≤ n — p-free constants, exponent
  linear in N. ((3b) numerically confirmed this audit on 13 brute-forced cases —
  p ∈ {2,3,5}, n ∈ {2,3}, D ≤ 4 — tight at n = 2, p odd.)

Finite subadditivity sums the legs; N₀ absorbs every offset (n,K)-only. Same chain for
XE.3 with XD.4's √-shape (dTotal+1 or maxH ≳ √((N−1−ccap)/(c0+ccap))).

**Attacks tried and blocked:**
1. *p-indexed detection delay* (Undec N = univ for N < p via threshold = p on shallow
   branches): PR at N = p−1 forces those branches deep (≳ cd·p) or tall (≳ ch·p).
   All-tall dies on TL at hstar = 1: frac(TallEvent 1) = 1 ≤ CT·p^(−cT) fails for
   large p, since CT, cT sit in the ONE K fixed before p. All-deep dies on the concrete
   tailCount cap: frac{vdisc ≥ ~cd·p/(s+½)} is forced exponentially small in p. Mixed
   populations die by subadditivity. This is precisely the family class the charge
   flagged ("Undec N stays large for all N") — the tags do NOT permit it.
2. *discZero junk-valuation channel:* closed (event includes discZero; frac(discZero)=0
   forced by vdisc_le_tail at D → ∞ for n ≥ 2).
3. *Degenerate K in XE.3* (c0 = ccap = 0): AF forces threshold ≤ 1, CP forces
   detCap = 0, so Wit N = ∅ for N ≥ 1 — statement trivially true; no divide-by-zero
   reaches the statement level (XD.4's conclusion handles it as displayed).
4. *Sign/offset games* (ch' , cd' arbitrary ℚ; p^(cT·ch'), p^(n·v_p(n)/(n−1)) pseudo-
   p-dependence): all absorbed p-freely (halved slopes for N ≥ N₀; p^(v_p(n)) ≤ n).
5. *Content pathologies:* the pinch uses only frac_mono/frac_union_le/BR₂ — no
   countable subadditivity is assumed anywhere, so the finitely-additive-only frac
   offers no wiggle room.

**Consequence for the charge's `max(0,·)` question:** the ∃N₀ device fully replaces the
note's literal (N−1−c_cap)-may-go-negative clamp; since no model of the tags violates
the restated forms, the exponent form does NOT need `max(0,·)`. The restatement is the
correct weakening, not still-too-strong.

*(Scope note: this establishes non-refutability at derivation level — the restated
statements are TRUE in every model of their hypothesis Props, with the one external
load-bearing arithmetic fact being (3b)/XF.7 (accepted Lemma 3.3, proof on record,
spot-checked above). Whether the fleet can FORMALIZE the pinch is XE.2/XE.3's HARD
proof duty, not an audit finding.)*

## 4. Byte-faithfulness, Lean files vs blueprint §3

- `XE2.lean` lines 46–51 vs blueprint lines 455–460: **byte-identical** (diffed
  programmatically; sole difference the trailing ` := by`). Imports = the spec's dep
  list (Defs, XC3, XE1a–h, XF7, XG2b–d). Body `sorry` as required.
- `XE3.lean` lines 35–40 vs blueprint line 479–481: signature is XE.2's MINUS `PR`
  verbatim ✓; the inline conclusion is **token-identical** after whitespace
  normalization (the file wraps the blueprint's one-line span across two lines —
  formatting only). Extra import `XD4` matches "deps: XD.4 in place of PR" ✓.
- MANIFEST: both entries status `restated-post-refutation`, restatement note + new
  statement hashes present, dep lists match the files ✓.
- §7 record cross-checked against all three artifacts: the countermodel description,
  the "all nine/eight tags hold" claim (proof terms present per tag in both witness
  files), the `example : XE3Statement := envelopeSqrt` statement-match device, and the
  negative-control retention claim are all accurate as written.

## Observations (no action required)

1. NOTE-INTERNAL: the CONDITIONALITY SUMMARY's exponential line omits (X2-AFF) while
   the same envelope block both opens with it and traces c₃, c₄ to "c₀ ((X2-AFF))" —
   the summary under-lists its own display. The blueprint's superset hypothesis list is
   the honest resolution; if the note gets a rev 9, the summary line should add
   (X2-AFF).
2. `R : X3aRouteP` is derivable from `AL ∧ WC` (second disjunct) — redundant in both
   signatures, kept for tag-name visibility. Fine.
3. The §7 "SIDE EVENT" (XF.6 ballCover timeout) was noted but is outside this audit's
   scope; nothing in it touches XE.2/XE.3.

— Fable (fresh instance), 2026-07-28 charge, executed 2026-07-27.
