# HC-2 blueprint — fresh-instance semantic audit (Fable, 2026-07-28)

ARTIFACT: `lean/notes/HC2_LEAN_BLUEPRINT_2026-07-28.md` (rev 1, 947 lines, 45 units), read in full.
CHARGE: `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` (CORPUS = HC2; NOTE = §C rev 14 + §B2-DEF +
§D4-R of `MOVES_2026-07-24.md`, read at the cited displays) + the orchestrator's special duties
(axiom proposals P-1/P-2/P-3; PresentSeed vs MovesC's deferred fields; W4-1 seam consistency;
POL-PIN and §2.1 deviations; order-0 gates vs `docs/PROJECT_STATE.md`; tripwire ordering; doctrine
sweep). Ground truths actually read: `MovesC/Defs.lean` (round 6, 979 lines) + `MANIFEST.json`
(36 units), `Moves/Defs.lean`, `Moves/DefsCore.lean`, `Moves/DefsL.lean` (StageCoreL /
TransitionCoreL / LandingCylinderL 247–259), `Moves/DefsT.lean` (TransitionData),
`L3_liftExists.lean`, note §B2-DEF D.5/D.7/D.8/D.10, §C C.0/C.1.5/C.2, §D4-R D4-R.0 (policy, L1,
L2, F1 record), `MOVESD_LEAN_BLUEPRINT_2026-07-28.md` (§2 rows, PresentNorm/PrefSet/PrefIdx/
Presented/Threshold displays, W4-1/W4-4), `GMN_citations.md` (full), `docs/PROJECT_STATE.md`
(realF2 gates, kernel (a)+(b) discharge), `OM/RealInstanceV2Gates.lean`,
`LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §4, `MovesC/C6_thmC_b.lean` (statement line).
I fix nothing. Findings quoted and classified CRITICAL / GAP, then the two mandated rulings,
then counts and the verdict line.

---

## CRITICAL findings

### CRIT-1 — P-1's carve-out list is incomplete; the faithfulness-entry draft's SAYS-NO-MORE is false as written

Blueprint §3 P-1, SAYS NO MORE: *"conclusion is one ∃ over `Stage p F` records whose every field
is a GMN-§2/§3 object [MINUS (S6) if the carve-out fires]"* — and the CARVE-OUT WARNING names
ONLY the (S6a)/(S6b) exactness fields.

But P-1's conclusion packages `TransitionCoreL σ σ' … ∧ StageCoreL σ'`, and `StageCoreL`
(`Moves/DefsL.lean` 186–189) = `StageCore` + `TvecUnitLaw` + `CoeffLocLaw`, where `StageCore`
(`Moves/DefsCore.lean` 196–208) additionally carries `w_strict`/`w_jump`/`R_neg` (the D.1(b) tie
laws), `tvec : TvecLaw`, `prevIaug`, `slot : SlotDecomp`, `coeff : CoeffFieldLawCore`, and the
`Stage` fields themselves include `hRΦ` (D.3(b)'s `R Φ = z^s` pinning), `he1t` (P2), `hS5`, the
`reps`/`Tvec` bookkeeping. These are the §B2-DEF D.0(P2)/D.1(e)/D.2(S4) graded-localization
ledger — content `Moves/DefsL.lean`'s own header calls *"the single remaining boundary — the
identification of `(σ.R, σ.w)` with the residual calculus of a genuine graded tower (the round-1
D2 fiat + D.1(e))"*, i.e. OURS, with a dedicated unfinished graded-ring campaign. None of it
appears in P-1's citation map (which covers key existence, valuation/polygon, the five residual
laws, residue tower); even the residual laws it does map are EXACT-equality forms where GMN's
Thm 2.26/Thm 3.7 (per `GMN_citations.md` §2, "∼" throughout) state normalized up-to-unit
multiplicativity of residual POLYNOMIALS, not a graded residual map with `hRadd`/`hRlt`.

Consequence: declared per the current draft, our-math leaks into the axiom — exactly the failure
mode the special duty names, on the campaign's highest-stakes surface. The §3 fence (proposal-only,
guardian-gated) mitigates, but the draft AFFIRMATIVELY claims the opposite of the truth, so the
gate is primed to pass a false SAYS-NO-MORE. Repair (for the designer, not me): extend the
carve-out to the full `StageCore(L)` ledger — i.e. restate P-1's conclusion as Stage-minus-ledger
(TransitionData-level: key/valuation/polygon/residual-polynomial/residue-tower conjuncts only),
with `StageCoreL σ'` supplied by HC-1's D.7 induction or by `StageTransHyp`; or declare nothing
(the already-recorded downgrade). Classification: **CRITICAL** (the proposal text as displayed
mis-states what the citation covers; the mutation probes do not exercise the ledger conjuncts).

---

## GAP findings

### GAP-1 — P-1's `hlift` keying: stage pair vs node pair, no owned bridge (the F10 trap)

P-1 hypothesizes `hlift : IsStandardLift σ ψ g Φhat` — stride `σ.e`, parent-scale weights
`σ.wPrev (t_k) = σ.h·(g−k)` (`Moves/Defs.lean` 214–224, matching D.5's display at the STAGE's
pair, as `L3_liftExists` consumes it). Its declared consumers — *"U-layer history construction
(U19, U17a)"* — work at `HistoryCoherent`'s read legs, whose recorded lift law is `IsNodeLift ν`
(`MovesC/Defs.lean` 535–543): stride `ν.e`, CURRENT-valuation weights `σ.w(t_k) = ν.h·(g−k)` —
the round-3 F10 adjudication (*"the D.5 lift positions … use the READ's own pair, while
Stage.(e,h,s,t) records the frame-CREATING read's"*). The two predicates are genuinely
differently keyed; a consumer holding node data cannot discharge `hlift` without a reindexing
bridge, and no unit owns one. The blueprint KNOWS the cousin issue — U1's sketch: *"if L3's unit
is stage-keyed only, add helper `nodeLift_exists` … the MovesC F10 lesson says DO NOT
conflate"* — but P-1's spec and U17a/U19 carry no analogous clause. Risk: a P-phase repair
silently re-keys the axiom's hypothesis (a meaning change) without a fresh guardian pass.
Demand: P-1's spec must state WHICH pair keys `hlift` relative to a `History` consumer and name
the bridge unit (or fold the reindexing into `StageTransHyp`'s signature). **GAP**
(underspecified Defs dependency, inconsistently handled across units).

### GAP-2 — P-2: after its own carve-outs, no honest axiom content remains; supplier claim not literal

(a) The blueprint's own expected outcome (*"P-2 survives only in reduced form or not at all"*) is
correct, and the audit confirms it is the ONLY sound outcome: with carve-out (i) (Theta_uni →
proved from Fact A) and (ii) (digit-flattening → SEED-EXIST) fired, the surviving
polynomial-level φ-development existence/uniqueness is already PROVED corpus content
(`L0_FactA_exists`/`L0_FactB_unique`, iterated down the recorded keys) — a P-2 declaration in
reduced form would axiomatize provable material, and in displayed form would import R4.5 our-math
(`pres_zero`'s baseDigit chart, the ≺-sort, `pres_block`'s block convention ride as ∃-CONCLUSION
conjuncts — conclusion-side conventions are imports, not selections; the draft's SAYS-NO-LESS
itself concedes this pends the guardian). Recommendation on record: strike P-2 to
hypothesis-only; the default (SEED-EXIST) already stands.
(b) *"P-2 and SEED-EXIST are interchangeable suppliers of D5's spine fields"* is not literal:
P-2's conjunct is `∀ i, i < H.nodes.length → IsUnitriangular (Theta i)` (BOUNDED) while
`PresentSeed.Theta_uni` (and `JetSetup.Theta_uni`, `MovesC/Defs.lean` 833) is UNBOUNDED `∀ i` —
P-2's output needs junk-index patching (`Theta i := id` beyond `len`) before it seeds D5.
(c) P-2's carve-out (i) references unit "U12′" — no U12 exists in the 45-unit census; the phantom
unit is uncounted. **GAP**.

### GAP-3 — P-3 cannot discharge its declared consumers as typed; citation direction questionable

U18 = MovesD's `PresentNorm` clause (ii) (MOVESD blueprint 675–681): `∀ H H' ∈ PrefSet …,
EtaGalEq (etaData H) (etaData H') → etaData H = etaData H'` — histories carry NO polynomial; the
two members are in general runs of DIFFERENT `f`'s. P-3 hypothesizes `ReadsOf p F n f H` and
`ReadsOf p F n f H'` at the SAME `f` plus equal `branchChoicesOf` — hypotheses unavailable in
U18's (and U26's) context. The recorded "fallback" is therefore illusory as typed: if U18 fails
as a proof, P-3 as displayed does not rescue it, and the axiom that WOULD is essentially U18
itself (undeclarable). Citation plausibility: (P4b) (`GMN_citations.md`, verified verbatim) says
the data `(λ, ψ)` *"depend on this choice"* — GMN asserts choice-DEPENDENCE with per-choice
factorization validity + intrinsic `(e,f)` (Cor 1.20); the η-data EQUALITY under our canonical
normalization is OUR normalization theorem, not the cited invariance. "HN" unpinned — honestly
flagged by the blueprint itself. POSITIVE: the mandatory `hbr`-drop mutation probe IS well-formed
and fires — §D4-R L2's rev-6 F1 record (*"two same-shape factors are simultaneously eligible"*)
supplies same-f, same-shape, distinct-branch histories with distinct η-data, refuting the
mutated statement; the probe meets the F1-precedent standard. PROOF-FIRST stands as the only
real route. **GAP**.

### GAP-4 — `ReadsOf` has no non-vacuity anchor among the 45 units

D4's `SideReads` body is elided (its exact inequality forms an E-phase transcription duty), and
NO unit instantiates `ReadsOf p F n f H` on concrete data: U27/U28 construct histories + seeds
directly, U30 witnesses one node spec. If the E-phase transcription over-strengthens SideReads,
`ReadsOf` is empty, U19–U24 become vacuously true, and the W4-1 `eligible` seam (MovesT re-keys
to THIS predicate) dies silently — the pre-rebase trap the charge's item 2 exists for. Demand:
add an order-0 gate (e.g. `gate_readsOf_inert2`: a concrete monic quadratic `f` at U27's `H₀`
with `ReadsOf 2 f H₀` proved), axiom- and seed-free, run with U27/U30 in the first block. **GAP**
(blocking-adjacent; cheap to add).

### GAP-5 — `PresentSeed` is not "exactly the deferred fields … and NOTHING else"; SEED-EXIST's two displays differ

MovesC's honest boundary (`MovesC/Defs.lean` 195–202 + the `htH` flag at 597–604) defers: the
presentation spine, the TYP piece maps, and the two `htH` identifications. D5's seed carries
these (pres/Theta/laws → spine ✓; `typObj` with full alphabet → piece maps + D.3(e)(ii) ✓;
`zcSeed` → LST(i) ✓ — the coverage map is faithful) — but ALSO `coordOf`(+sorted/lt) (constructed
by D1 `boxChart`, which I checked against C.0's display: level-major, base-descending, correct
with the recorded `n = 0` junk-guard), `keys`/`keys_mid`/`landing` (PROVED to exist by the
blueprint's own U1 from coherence), and `hm`/`hN`. Hypothesis-side over-strength is sound
(SEED-EXIST becomes nominally harder, the theorems honestly weaker), but the docstring's
minimality claim is false, and HC-1's obligation is inflated by provable fields. Also §2 Wall B
displays SEED-EXIST as `∀ H ∈ PrefSet …` while U15 consumes `∀ i : PrefIdx …` at `reprOf i` —
record which quantifier is HC-1's actual deliverable (the weaker reprOf-form suffices for
`Presented.jet`). **GAP** (doc/spec drift; no soundness leak).

### GAP-6 — POL-PIN nominal mismatch with MovesD's ledger row (condition attached to the D2 ratification below)

MovesD §2's POL-PIN row reads *"the instance `pol := the (S6b) offset-P policy`"* by name;
HC-2 delivers `polOM` = the choice-selected realizer of the same spec. Ratified below on the
math; the ledger row (and the wave-4 reconciliation) must be re-worded to "an instance satisfying
the realizer laws (`RecenterLiftSpec` per node + blindness + totality)" or a sign-off recorded,
else the seam registry will flag a nominal drift. Also U18/U17a's `hypothesis_fields` name
"P-3"/"P-1" directly while §7.3(v) demands consumption only via supplier hypotheses — phrase the
fields as the named-hypothesis signatures (`StageTransHyp`, `OmUniqHyp`) to keep
declaration/downgrade consumer-invisible. **GAP** (wording, two files).

### GAP-7 — minor spec defects (one line each)

(i) U13's moves_ref says `JetSetup` has "all 25 fields" — the round-6 structure has 29.
(ii) §7.1's "E-phase elaborates … U27/U30 FIRST" is correct only in the elaborate/typecheck
sense — U27's PROOF needs U13 ← U9/U10; the text's own "fails to typecheck" wording carries the
right reading, but a prover-phase scheduler must not interpret it as prove-first.
(iii) `ZCSeedLaws` line-by-line check (charge addition (ii)) is NOT dischargeable now — the
bundle is declared TO-BE-FIXED-AT-E-PHASE; the fence is properly worded (only C.1.5/rev-9-display
or D.3(e) content pre-authorized, anything else a statement-fence event) and matches C.1.5's
actual graded-content markers; the check is a STANDING OBLIGATION for the E-phase audit round.
**GAP** (bookkeeping).

---

## The two mandated rulings

### RULING 1 — §2.1 `mkStratum := fresh`: **RATIFIED**

`JetSetup.recursion`/`inh_implied` (`MovesC/Defs.lean` 872–877) evaluate `stratum` only in
conjunction with `Sigma i`-membership, and `SHZ` reads `fresh` only; the note's C.1(i) (*"E_inh
is implied"*, C.1.5's proof line) makes `Σ_{i−1} ∩ E(ν) = Σ_{i−1} ∩ E_fresh(ν)` — the instance
installs a STRONGER-than-note `inh_implied` (holds off-cylinder too), which is sound for an
interface consumed as a hypothesis bundle. The semantic residue (constructed Sigma = the
classifier's per-prefix locus) is genuinely carried where the blueprint says: U9/U10 pin the
(ZC) geometry per C.1.5, U27/U28 pin the numbers. Falsifiability check passes: a wrong `mkFresh`
still fails U6 (`mstar_eq`), U9/U10. No inherited carrier demanded; U8 stays `Iff.rfl`-easy.

### RULING 2 — D2 `polOM` (choice-realizer) vs the offset-P formula: **RATIFIED, with GAP-6's condition**

Spec-identity verified: `RecenterLiftSpec` is verbatim `LandingKey`'s recentering conjuncts
(`MovesC/Defs.lean` 552–557) = D.10's admissible-lift clause (*"take ANY t ∈ C_Φ̂ with
v(t) = v(Φ̂) and dig(t) = c̃"*, MOVES 2593–2594). D.10's dual-accepted lift-independence
(*"Everything below depends on t only through (v(t), dig(t))"*, with the honest below-the-line
scope, which no HC-2 consumer crosses) makes every spec-realizer policy — offset-P included —
produce identical graded data, η's, and masses at read heights; MovesD is ∀-pol and `etaData`
excludes lifts (its display, MOVESD 707–711), so all counts and gates tie. `polOM` is
deterministic (a fixed choice function; `blind := rfl` is plausible under structure eta —
`RecenterLiftSpec` reads only `σ`/`center`). U25's totality-of-the-∃ is WEAKER than the
formula's totality and its math-level support checks out (PROJECT_STATE:360 *"kernel parts
(a)+(b) DISCHARGED"*). The U25 eligibility narrowing and the U30 tripwire are the right
insurance for the D.10 scale risk. Condition: GAP-6's ledger-row rewording/sign-off.

---

## Special-duty confirmations (checked, clean)

* Order-0 gates vs the realF2 record: U27's `1/4` at n = 2 inert = `gate_v2_countingDensity_inert2`
  ✓ (PROJECT_STATE:57–58; `RealInstanceV2Gates.lean` 22–24); U28's split `1/9` ≠ inert `1/3` at
  q′ = 3 ✓ (gates G2, lines 119–143); U29's NP(P̂*) = 1 + 4 = 5 ✓ (MOVESD 118, 244–248). U27's
  count form matches `C6_thmC_b`'s literal statement (`Nat.card (J.SHZ Z) * p ^ totalPins J Z =
  boxMass p m`) ✓.
* Tripwire ordering: U30 genuinely first (§7.1 + the DAG's "(U30 tripwire first)") — the day-one
  falsifier for U25's scale arithmetic ✓; with GAP-7(ii)'s reading note.
* SEED-EXIST discipline: hypothesis, never axiom ✓ (§2 Wall B, U15's `hseed` field); `hnorm`,
  `hbox`, `vOf`, `StageTransHyp` all carried as hypothesis_fields ✓; campaign §4's
  hypothesis-never-axiom list honored ✓; no silently dropped kernel found in the 45-unit sweep.
* W4-1 seam: D4's `ReadsOf`/`SideReads` is consistent with §D4-R L2's display (side/digit-tuple/
  ψ/canonical-lift, sides read off f's polygon in the frame) and with MovesD's W4-1 row —
  ownership (HC-2 defines, MovesT re-keys) consistently registered on both sides; the
  `Box p m`-point vs `Polynomial` typing is mediated by `pres` (implicit but unambiguous).
* Faithfulness spot-checks: U11 = `JetSetup.root_height` byte-consistent; U20/U22 match
  `TransitionAdmissible`'s (NA)/(SAE) conjuncts; U21's vertex unit `T(μ·m̂ − a)` matches
  `LandingCylinderL` (DefsL 247–259) literally; U14's cutoff sentence matches C.2's
  `N(H,Z) := 1 + largest BASE level` (incl. the no-equations `N := 1` ↔ MovesD's piecewise NP);
  U18 = PresentNorm(ii) verbatim; census arithmetic (45; hard 16; easy 11 / medium 18) checks.

---

## Counts and verdict

CRITICAL: 1 (CRIT-1). GAP: 7 (GAP-1 … GAP-7).

**REJECT (1 crit / 7 gap).** Perimeter of the rejection: the §3 axiom-proposal surface (P-1's
carve-out/faithfulness draft; P-2's supplier claim; P-3's fallback typing) plus the four
spec-hygiene gaps. The architecture itself — the three walls, D1–D7, the U-layer decomposition,
both displayed deviations (ratified), the gate block, and the seam registry — survives this
audit; a targeted rev 2 fixing CRIT-1 and GAP-1…7 (no structural rebuild) is the expected
disposition before E-phase.

— Fable, fresh instance, 2026-07-28. I fixed nothing.
