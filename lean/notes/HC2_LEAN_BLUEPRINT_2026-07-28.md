# HC-2 LEAN BLUEPRINT — the JetSetup-existence bridge (2026-07-28, REV 2)

STATUS: BLUEPRINT (phase B of the campaign gate chain B → A → E → P → V).
NOTHING in this file is declared code. In particular §3's axiom statements are
**PROPOSALS ONLY** — none may be declared without (i) a published-source citation
confirmed against the PDF, (ii) a faithfulness entry in `docs/AXIOM_FAITHFULNESS.md`,
(iii) a semantic-guardian audit pass (the process that has caught two false axioms).

REV 2 (2026-07-28), per the fresh-instance audit `HC2_AUDIT_FABLE_2026-07-28.md`
(verdict: REJECT, 1 critical / 7 gaps; the architecture itself ratified — "a
targeted rev 2 fixing CRIT-1 and GAP-1…7 (no structural rebuild) is the expected
disposition"). What changed: CRIT-1 → §3's P-1 rebuilt STAGE-MINUS-LEDGER with
DEFAULT = NO DECLARATION (consumers carry the named hypothesis `StageTransHyp`);
GAP-2/GAP-3 → P-2 and P-3 STRUCK to hypothesis-only (tombstones kept in §3);
GAP-1 → the stage↔node lift keying gets an owned bridge (D8 `IsReadLift` + U1b
`nodeLift_exists`); GAP-4 → new order-0 gate U31 anchors `ReadsOf` non-vacuity;
GAP-5 → D5 `PresentSeed` pruned to the genuinely deferred fields and SEED-EXIST
restated once, in U15's reprOf form; GAP-6 → the POL-PIN naming reconciled (polOM
= the offset-P policy, spec-realized; sign-off inline at D2); GAP-7 → count/
reading/obligation fixes. Both displayed deviations RATIFIED — records inline at
§2.1 and D2. Census 45 → 48. Full disposition table: §8. This file returns to a
fresh verifier for the acceptance pass (perimeter: §3 + the seven gap sites + the
two inline ratification records).

## 0. Charge and ground truth

HC-2 = the second hard core of `lean/notes/LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`
(§1/§5 wave 5): instantiate MovesC's PROVED interface — Theorem C over `JetSetup`
(`lean/LeanUrat/MovesC/Defs.lean`, 36/36 units proved-clean, MANIFEST.json) — from the
real classifier side, and thereby discharge the MovesD rev-9 open surface
(`lean/notes/MOVESD_LEAN_BLUEPRINT_2026-07-28.md` §2): **PRESENT-EXIST**,
**PresentNorm**, **POL-PIN** (+ the W4-1 `eligible` seam definition).

Ground truth for every statement: the frozen dual-accepted text in
`lean/notes/MOVES_2026-07-24.md` — §C rev 14 (C.0–C.3, esp. C.2's presentability
"N(H,Z) := 1 + the largest BASE level occurring among the coordinates of T(H,Z)'s
equations" and C.3's realizability sentence: "the classifier reads actual hull sides,
so all three [(NA)+(HV)+(SAE)] hold on its output"), §B2-DEF (D.0–D.12, esp. D.5's
standard lift, D.7's (S6b′) offset-P-lift, D.10's recentering), §D4-R (D4-R.0's
canonical policy + L1/L2). The Lean ground truth: `MovesC/Defs.lean` (round 6),
`Moves/Defs*.lean` (Stage/TransitionCoreL/LandingCylinderL — 54/61 unit ledger),
`OM/RealInstanceV2.lean` (realF2 — the M9-rebase MODEL for this bridge).

MEMORY-RULES CARRIED: subagent staged-write discipline in every prover prompt;
plan-level adversarial pass (this file goes to a fresh verifier BEFORE E-phase);
wave-3 doctrine — "a faithful interface must be FALSE for instances the note would
reject; obligations may be open, but their TYPES must pin their content."

## 1. The discharge ledger (what HC-2 delivers, to whom)

| consumer object (owner file) | HC-2 deliverable | unit(s) |
|---|---|---|
| `MovesC.JetSetup H n N m` existence (MovesC honest boundary, Defs header "The honest boundary") | `jetSetup_of_seed` : `PresentSeed` → coherent → realizable → JetSetup | U13 (+U1/U1b–U11) |
| **PRESENT-EXIST** (MovesD §2: `∀ N ≥ P.NP pol, Nonempty (Presented p F n N (n*N) pol P)`) | reduced to SEED-EXIST (the named HC-1 graded hypothesis, §2 Wall B) + proved assembly | U14, U15, U16 |
| **PresentNorm** (MovesD §3.2, the typed two-sided dictionary) | totality (lift-swap + Galois re-rooting) + uniqueness (embedding rigidity) | U17a–c, U18 |
| **POL-PIN** (MovesD §2: the canonical-policy instance + realizer laws) | `polOM : CanonPolicy p F` — the (S6b′) offset-P policy, spec-realized (RATIFIED; sign-off at D2) + blindness + totality-on-eligible-nodes (L1 kernel-(a)) | D2, U24, U25 |
| W4-1 `TreeModel.eligible` seam (MovesD §2.5) | the f-explicit run predicate `ReadsOf` (the negotiating definition MovesT re-keys) | D4, U19–U23 |
| `ClassFiberWelldef` (MovesD §3.4; D15's `hwd`) | conditional unit, proof-first; on failure its consumers carry `OmUniqHyp` (P-3 STRUCK, §3); DEFERRABLE (its consumer already carries it as a hypothesis) | U26 |
| order-0 non-vacuity (the realF2 lesson) | gates: inert-n=2 value tie, σ-separation, NP(P̂*)=5, polOM instance, ReadsOf instance (rev 2, GAP-4) | U27–U31 |

NOT HC-2's to deliver (recorded so nobody silently widens scope): the graded ring
itself and the two R4.5 identifications (HC-1; here the `PresentSeed` fields, §2
Wall B); `D4R_CYL` and the MovesT tree corpus (wave 4); `hExhaust`/drainage;
anything palindromy/htameFE (out of scope by standing directive).

## 2. Architecture — three walls, and where each is handled

The M9-rebase lesson (PROJECT_STATE §2, the model this blueprint copies): bridge an
abstract interface to the real engine by (i) keeping the interface fixed (statement
fence), (ii) building the instance bottom-up with the ORDER-0 case first, (iii)
machine-checked value gates against independently recorded numbers (realF2's 1/4 at
n=2 inert; split ≠ inert at q′=3) before any generality. HC-2 repeats this pattern
one level up: `JetSetup` is to Theorem C what `DensityFoundation` was to
`goal_theorem_montes`, and U27/U28 are the analogues of the V2 gates.

**Wall A — engine → History translation.** MovesC's `Node`/`History` are keyed to
`Moves.Stage` (the §B2-DEF ledger), NOT to the OM/ engine's `M5.OMType`/
`ClusterShape` (which erase the run data: the emitted shape has no lines, no digit
tuples, no lifts). The honest translation object is therefore a RUN PREDICATE
`ReadsOf f H` — "H's recorded reads are the polygon-side data f actually produces,
frame by frame" — stated in Moves vocabulary (`IsDevelopment`, slot weights via
`σ.w`/K1, `σ.R` digits, `LandingKey`), not a function of the engine's internals.
This is deliberately the SAME semantic surface as MovesD's W4-1 `eligible` (L2's
"ALL next-node data ν = (side s, its digit tuple, ψ, canonical lift)"): HC-2 owns
the definition; MovesT re-keys `eligible` to it in wave 4. The engine's own
`classify` (OM/Classifier.lean) is tied in ONLY at the order-0 gates (U27/U28),
where its numbers are independently recorded — full engine-run ↔ ReadsOf
faithfulness at all orders is NOT an HC-2 obligation (it is the existing
order-≥2 classifier-faithfulness program, PROJECT_STATE §4).

**Wall B — the graded presentation seed (OUR math ⇒ hypothesis, NEVER axiom).**
MovesC's declared honest boundary (Defs header): the existence of the presentation
spine (`pres`, `Theta`, `Theta_uni`, `pres_total`, `pres_block`), the TYP piece
maps, and the two `History.htH` identifications are "the unbuilt graded ring
(§B2-DEF gap R4.5 items 1&3)". These are §B2-DEF/§C content — dual-accepted but
OURS and unpublished — so by the campaign axiom policy (§4) they CANNOT be axioms.
HC-2 packages exactly these fields — and, after the rev-2 pruning (audit GAP-5),
literally NOTHING else — as the structure `PresentSeed` (D5), and proves
EVERYTHING ELSE of `JetSetup` from it (U1–U13). The named hypothesis, in its
rev-2 form (stated ONCE, aligned with U15's consumption; the `reprOf` quantifier
— one representative per class — is the weaker form and IS HC-1's actual
deliverable, per audit GAP-5):

  (SEED-EXIST)  ∀ (i : PrefIdx n (polOM p F) P) (N : ℕ), P.NP (polOM p F) ≤ N →
                  ∃ keys, KeysLawful (reprOf i) keys ∧
                    Nonempty (PresentSeed p F (reprOf i) n N keys)

is HC-1's deliverable (its graded carriers are precisely the CStatements/
GradedCarrier raw material of the parked MovesR re-architecture). `KeysLawful`
(D5) names U1's key-tower laws; the ∃-keys form is the WEAKEST form sufficient
for U15 (U13 accepts any lawful tower), keeping HC-1's obligation minimal — the
point of the GAP-5 pruning. [Rev 1 displayed a `∀ H ∈ PrefSet` form here and a
`PrefIdx` form at U15; the audit required recording which quantifier is the
deliverable: THIS one.] PRESENT-EXIST = SEED-EXIST + U15; the reduction is the
deliverable, the seed is the honest residue. The former "budget-saver" proposal
P-2 is STRUCK (audit GAP-2; tombstone in §3): its post-carve-out residue was
already-proved Fact A content, so there was no budget to save — SEED-EXIST is
the sole supplier of D5 values.

**Wall C — published Montes content (the fenced axiom surface, post-audit).**
Rev 1 proposed three axioms here; the audit round (CRIT-1, GAP-2, GAP-3) resolved
the surface to:
  P-1 stage-transition existence — SURVIVES only in STAGE-MINUS-LEDGER form, and
      even that is NOT declared by default: the reduced form cannot populate a
      `Stage`-carrying consumer by itself (§3's consumer analysis), so consumers
      carry the named hypothesis `StageTransHyp`; P-1-reduced is recorded as a
      CONTINGENT declaration for one precisely named future state (§3);
  P-2 higher-order φ-adic coordinates — STRUCK (tombstone, §3): after its own
      carve-outs, the residue is already-proved Fact A content; SEED-EXIST stands
      as the sole seed supplier;
  P-3 OM-invariant choice-independence — STRUCK (tombstone, §3): it cannot
      discharge U18/U26 as typed, and the retyped version would be OUR
      normalization theorem (undeclarable); consumers carry `OmUniqHyp` if the
      proof-first route fails.
The standing policy is unchanged — prove > cite > hypothesize; an axiom is
declared only where the guardian confirms the citation says NEITHER MORE NOR
LESS. The audit round APPLIED it, and "hypothesize" won on all three counts
(with P-1's "cite" kept alive as the one recorded contingency).

### 2.1 The one pre-declared DESIGN DEVIATION (displayed for the audit round)

`mkStratum i := (mkFresh i).sat` — the constructed stratum is the FRESH clause
content only, so `JetSetup.inh_implied` holds by `Iff.rfl`. The note's C.1(i)
("on the state cylinder, the inherited content is implied — the stratum reduces to
exactly its fresh clauses") is thereby INSTALLED rather than re-proved: the
inherited-clause content of `E(ν_i)` has no self-contained Lean carrier short of
transporting the entire previous-frame clause vocabulary, and every MovesC consumer
reaches the stratum only through `recursion` + `inh_implied`. The semantic residue
— that the constructed `Sigma` chain equals the classifier's actual per-prefix
locus — is carried by (a) the zc/fresh laws U9–U10 (which pin Sigma's geometry to
the recorded node data exactly) and (b) the value gates U27/U28. The audit round
must either RATIFY this deviation or demand the inherited carrier; if the latter,
U8 re-opens as a full C.1(i) unit (add ~1 hard unit). [Wave-3 doctrine check: with
stratum := fresh, a WRONG fresh construction still fails U9/U10/U6 — the interface
stays falsifiable; no degenerate instance slips through.]

**AUDIT RULING 1 (2026-07-28): RATIFIED.** The auditor confirmed:
`JetSetup.recursion`/`inh_implied` (MovesC/Defs.lean 872–877) evaluate `stratum`
only in conjunction with `Sigma i`-membership, and `SHZ` reads `fresh` only, so
with the note's C.1(i) ("E_inh is implied", C.1.5's proof line) the installed
`inh_implied` is a STRONGER-than-note law (it holds off-cylinder too) — sound for
an interface consumed as a hypothesis bundle. The semantic residue (constructed
`Sigma` = the classifier's per-prefix locus) is carried exactly where displayed:
U9/U10 pin the (ZC) geometry per C.1.5, U27/U28 pin the numbers. Falsifiability
holds: a wrong `mkFresh` still fails U6 (`mstar_eq`)/U9/U10. No inherited carrier
demanded; U8 stays `Iff.rfl`-easy.

## 3. THE AXIOM PROPOSALS — FENCED; PROPOSALS ONLY, NOTHING DECLARED

Common citation base (already pinned verbatim in `lean/notes/GMN_citations.md`):
J. Guàrdia, J. Montes, E. Nart, *Newton polygons of higher order in algebraic
number theory*, Trans. Amer. Math. Soc. 364 (2012) 361–416 (arXiv:0807.2620v2 —
theorem numbers below are the arXiv ones; the standing pagination caveat of
GMN_citations.md applies: confirm against the TAMS PDF before declaration).
The campaign charge names "GMN/HN papers": **"HN" is NOT yet pinned in this repo**
— candidate second sources for the uniqueness leg are J. Guàrdia, J. Montes,
E. Nart, *Okutsu invariants and Newton polygons* (Acta Arith. 145 (2010) 83–108)
and J. Guàrdia, E. Nart, *Genetics of polynomials over local fields* (Contemp.
Math. 637 (2015)); with P-3 STRUCK (below), the pinning duty now attaches only to
a FUTURE uniqueness declaration — none is proposed — and lapses until one is.
GMN's scope fence (GMN_citations.md §0): base field a
finite extension of ℚ_p, per-fixed-p; our `ℤ_[p]` sits inside it; NO uniformity/
rationality/p-independence content may ride in any of these axioms — those are
derived, never imported.

### P-1 `AX_stage_trans_gmn` — order-r stage existence, STAGE-MINUS-LEDGER (rev 2 per CRIT-1); DEFAULT: NOT DECLARED

**Why rev 1's form was UNDECLARABLE (CRIT-1, the axiom-discipline event).** Rev 1
concluded `∃ σ' : Stage p F, … ∧ TransitionCoreL σ σ' … ∧ StageCoreL σ'`, and its
SAYS-NO-MORE claimed every conclusion field is a GMN-§2/§3 object. FALSE:
`Stage p F` is a Lean structure whose FIELDS already carry the graded-localization
ledger — `hRadd`/`hRlt` (a graded residual MAP with exact additivity/domination
laws, where GMN's Thm 2.26/Thm 3.7 state "∼"-form normalized up-to-unit
multiplicativity of residual POLYNOMIALS, per `GMN_citations.md` §2), `hRΦ`
(D.3(b)'s `R Φ = z^s` pinning), `he1t` (D.0(P2)), `hS5` (the forced-position digit
law), `hStretch`, the `reps`/`Tvec` bookkeeping, the (S6a)/(S6b) realizer
exactness — and `StageCoreL` adds the D.1(b) tie laws (`w_strict`/`w_jump`/
`R_neg`), `TvecLaw`/`TvecUnitLaw`, `CoeffLocLaw`, `prevIaug`, `SlotDecomp`. That
is the §B2-DEF D.0(P2)/D.1(e)/D.2(S4) ledger — OURS (the `Moves/DefsL.lean`
header's "single remaining boundary — the identification of `(σ.R, σ.w)` with the
residual calculus of a genuine graded tower", with a dedicated unfinished
graded-ring campaign), stated in no GMN theorem. The same holds one level down:
`TransitionData` is itself parameterized over a child `Stage p F`, so ANY
conclusion that so much as MENTIONS a `Stage` value smuggles the ledger. There is
no carve-out patch; the conclusion TYPE must change.

**The only faithful shape — the reduced conclusion.** A MovesJ-owned, ledger-free
skeleton: exactly the four GMN conjunct groups, each at GMN's own strength
(∼-forms), reusing existing Moves vocabulary (`IsSlotMinWeight`, `K1At`) only
where it is ledger-free:

```lean
/-- PROPOSAL P-1-REDUCED (NOT DECLARED; contingency only — see DISPOSITION).
GMN order-r apparatus, stage-minus-ledger: an eligible increment read on a lawful
stage produces the order-(r+1) GMN SKELETON — key, valuation + polygon, residual
operator at ∼-strength, residue tower — and NOTHING of our Stage/StageCoreL
ledger. -/
axiom AX_stage_trans_gmn {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hψm : ψ.Monic) (hψd : ψ.natDegree = g)
    (hψirr : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (hg : 1 ≤ g)
    (zbar : Fˣ) (hroot : Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0)
    (e' h' : ℕ) (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g e' h' Φhat)  -- D8; GAP-1
    (hiaug : IAug σ Φhat e' h') :
    ∃ (w' : Polynomial ℤ_[p] → ℤ) (K' : Subfield F)
      (R' : Polynomial ℤ_[p] → Polynomial ↥K'),
      -- (key)  Thm 2.11: Φ̂ is a key polynomial of the augmented type
      (Φhat.Monic ∧ Φhat.natDegree = e' * g * σ.Φ.natDegree) ∧
      -- (valuation + polygon)  §2.2 (v_{r+1}) + Thm 2.9/Thm 3.1: w' a valuation,
      -- slot-minimum over (σ.w, e', h') at Φ̂, K1 at Φ̂
      ((∀ f g', f ≠ 0 → g' ≠ 0 → w' (f * g') = w' f + w' g') ∧
       (∀ f g', f ≠ 0 → g' ≠ 0 → f + g' ≠ 0 → min (w' f) (w' g') ≤ w' (f + g')) ∧
       IsSlotMinWeight w' Φhat e' h' σ.w ∧ K1At w' Φhat (w' Φhat)) ∧
      -- (residual, ∼-form ONLY)  Def 2.20–2.21 + Thm 2.26 + Thm 3.7/Cor 3.8: a
      -- residual-POLYNOMIAL operator, multiplicative UP TO nonzero K'-scalars;
      -- NO graded map, NO exact hRadd/hRlt, NO position/monomial pinning
      ((∀ f, f ≠ 0 → R' f ≠ 0) ∧
       (∀ f g', f ≠ 0 → g' ≠ 0 →
          ∃ c : (↥K')ˣ, R' (f * g') = (c : ↥K') • (R' f * R' g'))) ∧
      -- (residue tower)  §2.1: F_{r+1} = F_r[y]/(ψ) via the chosen root
      K' = σ.nextField zbar
```

The exact conjunct list is transcribed against the TAMS PDF AT DECLARATION TIME
(if the contingency ever fires); the four GROUPS above are normative, and nothing
outside them may be added without a fresh guardian pass. Note what fell out of
the hypotheses too: rev 1's `(s' t' : ℤ)`, `hbez`, `hwin` (the canonical Bézout
window) are GONE — they were our convention riding on the axiom; they now live
only in `StageTransHyp` below, which is the faithful place for a selection.

**`hlift` keying (audit GAP-1, resolved).** Rev 1 keyed `hlift` by
`IsStandardLift σ ψ g Φhat` — stride `σ.e`, parent-scale weights
`σ.wPrev (t_k) = σ.h·(g−k)`: the frame-CREATING read's pair. History consumers
hold `IsNodeLift ν` — stride `ν.e`, CURRENT-valuation weights
`ν.σ.w (t_k) = ν.h·(ν.g−k)`: the READ's own pair (the F10 adjudication; MovesC
round 3 replaced `IsStandardLift ν.σ` inside `HistoryCoherent` for exactly this).
The two are GENUINELY differently keyed; conflating them was the F10 trap. Rev-2
resolution, both halves of the audit's demand: (a) the reindexing is FOLDED INTO
the signature — `IsReadLift` (D8) is the `IsNodeLift` formula abstracted off
`Node` (`isNodeLift_iff : IsNodeLift ν Φhat ↔ IsReadLift ν.σ ν.ψ ν.g ν.e ν.h
Φhat`, definitional), and BOTH `StageTransHyp` and P-1-reduced key `hlift` by it;
(b) the OWNED BRIDGE UNIT is U1b `nodeLift_exists` (read-pair lift existence from
stage data — L3's proof shape at the node's pair), which is how consumers
DISCHARGE the hypothesis. Any re-keying of `hlift` in a P-phase repair is a
MEANING CHANGE requiring a fresh guardian pass — recorded here so it cannot
happen silently.

**Consumer analysis — the "too weak?" question, answered.** The declared
consumers (U17a's chain rebuild; history construction generally) must BUILD
`Node` values, and a `Node` carries a full `Stage p F`; they must further supply
`TransitionCoreL`/`StageCoreL` for `HistoryCoherent`'s legs. The reduced
conclusion contains no `Stage` — it CANNOT populate a `Node`. So P-1-reduced
alone discharges NO consumer obligation as typed: the stage-minus-ledger form IS
too weak for the consumers, and the honest default is NO DECLARATION. The
consumer-facing surface is the FULL-STRENGTH named hypothesis (ours;
hypothesis-never-axiom):

```lean
/-- The stage-transition supplier hypothesis (HC-1's TRANS; rev-1 P-1's statement
with the lift keyed at the READ pair per GAP-1). NEVER an axiom. -/
def StageTransHyp (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop :=
  ∀ (σ : Stage p F), StageCoreL σ →
    ∀ (ψ : Polynomial ↥σ.K) (g : ℕ), ψ.Monic → ψ.natDegree = g → Irreducible ψ →
      ψ ≠ Polynomial.X → 1 ≤ g →
    ∀ (zbar : Fˣ), Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0 →
    ∀ (e' h' : ℕ) (s' t' : ℤ), 1 ≤ e' → 1 ≤ h' → Nat.gcd e' h' = 1 →
      (e' : ℤ) * s' + (h' : ℤ) * t' = 1 → 0 ≤ t' ∧ t' < (e' : ℤ) →
    ∀ (Φhat : Polynomial ℤ_[p]), IsReadLift σ ψ g e' h' Φhat →
      IAug σ Φhat e' h' →
    ∃ σ' : Stage p F, σ'.Φ = Φhat ∧ σ'.e = e' ∧ σ'.h = h' ∧ σ'.s = s' ∧ σ'.t = t' ∧
      TransitionCoreL σ σ' Φhat e' h' zbar ∧ StageCoreL σ'
```

The factored discharge — the ONLY configuration in which declaring P-1-reduced
ever pays — is

  StageTransHyp  ⇐  P-1-reduced  +  StageLedgerHyp,

where `StageLedgerHyp` (HC-1's; named here so the factoring is on record)
upgrades any reduced skeleton to a lawful stage: given skeleton data
`(w', K', R'∼)` for an eligible read on a lawful stage, there is `σ' : Stage p F`
with the tie fields, `σ'.w = w'`, `σ'.K = K'`, the EXACTIFIED residual map, and
`TransitionCoreL ∧ StageCoreL` — precisely the D.0(P2)/D.1(e)/D.2(S4)
exactification-plus-ties: the D.7-induction / graded-ring content.

**DISPOSITION (the honest answer to CRIT-1's downgrade question): DEFAULT = NO
DECLARATION.** If HC-1's D.7 induction lands, it proves `StageTransHyp` outright
(the induction constructs the stage — skeleton and ledger together) and P-1 is
never declared. The ONE state in which declaring P-1-reduced pays: HC-1 proves
`StageLedgerHyp` (the ledger upgrade, conditional on a skeleton) but stalls on
skeleton EXISTENCE — the genuinely published-hard content (Thm 2.11 / Thm 3.1 /
Thm 2.26 / Thm 3.7). ONLY in that state does the §7.4 gate chain run for
P-1-reduced (PDF re-extraction, faithfulness entry from the draft below,
guardian, compiled probes). Until then every consumer carries `StageTransHyp`
verbatim — zero re-statement cost, the campaign's standard open-kernel pattern.

* citation map (per conjunct GROUP of the reduced conclusion): key — Thm 2.11
  (key polynomial of a type, "effectively construct"); valuation/polygon — §2.2
  (`v_{r+1}`) + Thm 2.9/Thm 3.1 (Theorem of the polygon); residual ∼-laws —
  Def 2.20–2.21 + Thm 2.26 (product theorem) + Thm 3.7/Cor 3.8 (Theorem of the
  residual polynomial); residue tower — §2.1 (types of order r+1).
* the rev-1 (S6) CARVE-OUT WARNING is DISSOLVED (audit charge (iv)): no (S6)
  field — indeed no `Stage` field of any kind — appears in the reduced
  conclusion; (S6) attainability now sits inside `StageLedgerHyp`, ours to prove,
  not the guardian's to check against GMN §2.4.
* non-vacuity probe (retargeted at the skeleton): instantiate at the base stage
  (`L1.baseStage_exists`, Moves corpus, PROVED) with the n=2 Eisenstein read
  (e=2, h=1, ψ = z+1, g=1) — the Wave-1 wild gate data; the ∃ must produce the
  SKELETON of the stage the W1 chain built by hand (its `w'`/`K'` checked against
  the W1 data). Mutation probes: drop `hiaug` → must break (the F-EMPTY family);
  mutate the slot-min/K1 conjunct's `h'` to `h' + 1` → must break the K1 gate
  arithmetic.
* faithfulness-entry DRAFT (rev 2 — the SAYS clauses now truthful):
  - VERIFIED CORE: GMN §§2–3 construct, for each type of order r and each side/
    residual-factor choice, the order-(r+1) data: key (Thm 2.11), valuation and
    polygon (§2.2, Thm 3.1), residual polynomial with UP-TO-UNIT
    multiplicativity (Def 2.21, Thm 2.26, Thm 3.7), residue tower (§2.1).
    Existence-only; per fixed p.
  - SAYS NO MORE: no uniformity, no rationality, no measure/density term, no
    p-independence; the conclusion is one ∃ over a LEDGER-FREE skeleton —
    residual laws at ∼-strength (up-to-unit, polynomial-level) ONLY; NO `Stage`/
    `StageCoreL` content: no exact `hRadd`/`hRlt`, no `hRΦ` pinning, no `he1t`
    (P2), no `hS5` position law, no `hStretch`, no tie laws
    (`w_strict`/`w_jump`/`R_neg`), no `TvecUnitLaw`/`CoeffLocLaw`/`SlotDecomp`/
    `prevIaug`, no `reps`/`Tvec` bookkeeping, no (S6a)/(S6b) exactness — all of
    that is §B2-DEF D.0(P2)/D.1(e)/D.2(S4) content, carried as
    `StageLedgerHyp`/`StageTransHyp` (named HC-1 hypotheses) at the consumption
    sites.
  - SAYS NO LESS: the eligibility hypotheses (`hσ : StageCoreL σ`,
    `hlift : IsReadLift …`, `hiaug`) are OUR selections riding hypothesis-side
    (stronger hypotheses only weaken an axiom); the Bézout window is GONE from
    the statement (never GMN content; it lives in `StageTransHyp`).
  - CONSUMED BY: nothing directly — only via the factored discharge of
    `StageTransHyp` (whose consumers are U17a and history construction; never a
    density/counting capstone).

### P-2 `AX_om_present` — STRUCK to hypothesis-only (audit GAP-2); tombstone

Rev 1 proposed GMN §2's admissible φ-developments (iterated down a recorded key
tower) as the optional "budget-saver" supplying the seed's pres/Theta half. The
audit confirmed rev 1's own expected outcome ("P-2 survives only in reduced form
or not at all") at its strong end — NOTHING declarable remains:
* carve-out (i) fires: `IsUnitriangular (Theta i)` is Fact A's ≺-triangular
  DIVISION ACCOUNTING — PROVED corpus content (Moves `L0_FactA_exists`/
  `L0_FactB_unique`), ours; GMN does not state it in this coordinate form.
* carve-out (ii) fires: the DIGIT-level chart (coefficients → `ZMod p` tuples
  through the block convention, `pres` itself as a base-p digit statement) rides
  on the K1-height reading — R4.5 item 1, OURS, not GMN-citable.
* the post-carve-out residue — polynomial-level φ-development existence/
  uniqueness iterated down the recorded keys — is ALREADY PROVED (Fact A/B,
  iterated): declaring it would AXIOMATIZE PROVABLE MATERIAL.
* the un-reduced form would import our-math as ∃-CONCLUSION conjuncts
  (`pres_zero`'s baseDigit chart, the ≺-sort, `pres_block`'s block convention) —
  conclusion-side conventions are IMPORTS, not selections.
Also on record from the audit: (a) rev 1's "P-2 and SEED-EXIST are
interchangeable suppliers" was NOT literal — P-2's unitriangularity conjunct was
BOUNDED (`∀ i, i < H.nodes.length`) where `PresentSeed.Theta_uni`/`JetSetup` need
UNBOUNDED `∀ i` (junk-index patching `Theta i := id` beyond `len` would have been
required); (b) rev 1's carve-out (i) referenced a unit "U12′" that exists nowhere
in the census — the PHANTOM UNIT is DELETED with this tombstone.
DISPOSITION: no axiom, and no new named hypothesis either — SEED-EXIST (Wall B)
is the sole supplier of D5 values, and the would-be P-2 content is either proved
(Fact A/B) or already inside SEED-EXIST. The campaign plan's "budget-saver" line
is answered: the saving was illusory. No downstream unit ever referenced P-2 by
name (they consume `PresentSeed` values only), so the striking is
consumer-invisible.

### P-3 `AX_om_uniq` — STRUCK to hypothesis-only (audit GAP-3); tombstone + standing probe

Rev 1 proposed choice-independence of η-data (same f, same shape, same recorded
branch choices, normalized presentations ⇒ equal η-data) as the U18/U26 fallback.
The audit found the fallback ILLUSORY AS TYPED, and the citation direction wrong:
* TYPE MISMATCH: U18 (= MovesD's `PresentNorm` clause (ii)) and U26 quantify over
  `H, H' ∈ PrefSet` — histories carry NO polynomial, and two members are in
  general runs of DIFFERENT `f`'s. P-3 hypothesized `ReadsOf … f H` and
  `ReadsOf … f H'` at the SAME `f` plus `branchChoicesOf H = branchChoicesOf H'`
  — hypotheses simply UNAVAILABLE in the consumers' context. If U18 fails as a
  proof, P-3 as displayed rescues nothing; the axiom that WOULD rescue it is
  essentially U18 itself.
* CITATION DIRECTION: (P4b) (verified verbatim in `GMN_citations.md`) asserts the
  data `(λ, ψ)` "depend on this choice" — GMN states choice-DEPENDENCE with
  per-choice factorization validity plus intrinsic `(e,f)` (Cor 1.20). The η-data
  EQUALITY under our canonical normalization is OUR normalization theorem, not
  the cited invariance — so retyping P-3 to match U18's quantification would make
  the axiom BE our theorem: UNDECLARABLE. ("HN" was never pinned; that duty
  lapses with this striking — §3 header.)
DISPOSITION: U18 stays PROOF-FIRST (unchanged — the only real route; sketch at
U18). If the proof fails, its consumers carry the named hypothesis

```lean
/-- The uniqueness supplier hypothesis — typed VERBATIM as U18's statement
(MovesD `PresentNorm` clause (ii)). NEVER an axiom. -/
def OmUniqHyp {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Prop :=
  ∀ H H', H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
    EtaGalEq (etaData H) (etaData H') → etaData H = etaData H'
```

(consumed by U15/U16 through `hnorm`'s uniqueness clause, and by U26) — a
recorded non-discharge, never a declaration.
RETAINED — THE STANDING PROBE (audit-confirmed well-formed and FIRING): the
`hbr`-drop mutation probe. §D4-R L2's rev-6 F1 record ("two same-shape factors
are simultaneously eligible") supplies same-f, same-shape, DISTINCT-BRANCH
histories with DISTINCT η-data — refuting any uniqueness statement lacking a
branch-identity hypothesis. This probe rides in the guardian charge PERMANENTLY:
any FUTURE uniqueness declaration, at any type, must survive it (it is the dual
of the F1 critical that punctured §D4-R).

## 4. Defs skeleton — `lean/LeanUrat/MovesJ/Defs.lean` (definitions only)

Imports: `Mathlib`, `LeanUrat.MovesC.Defs`, `LeanUrat.Moves.Defs{,Core,L,T}`,
`LeanUrat.MovesD.Defs` (the E-phase core — needed for `CanonPolicy`, `Shape`,
`PrefSet`, `PresentNorm`, `Presented`, `Threshold`; HC-2 runs AFTER MovesD's core
lands, per the wave plan). Namespace `LeanUrat.MovesJ`,
`open LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD`.

DECLARATION ORDER (normative, the MovesD §3.0 discipline): D1 → D3 → D2 → D8 →
D4 → D5 → D6 → D7 (D8 added at rev 2, audit GAP-1). NO axiom declarations in this file, ever (proposals live in §3 of
this note until their gate chain completes; if declared, they go in a dedicated
`MovesJ/Axioms.lean` behind the guardian gate, mirroring `OM/OmLeafFaithful.lean`).

### D1 `boxChart` — the ≺-sorted chart of the n×N box  [easy]

```lean
/-- The canonical ≺-sorted enumeration of the n·N coordinate box: level-major
(ℓ ascending), base-index DESCENDING within a level (CoordPrec, §C C.0). -/
def boxChart (n N : ℕ) : Fin (n * N) → Coord :=
  fun j => ((j : ℕ) / n, n - 1 - (j : ℕ) % n)
```
lemmas (same file, proved at E-phase): `boxChart_sorted : ∀ j j', j < j' ↔
CoordPrec (boxChart n N j) (boxChart n N j')` (consumes MovesC's
`C0.coordPrec_trichotomy`; arithmetic on div/mod) and `boxChart_lt : ∀ j,
(boxChart n N j).1 < N ∧ (boxChart n N j).2 < n` (needs `0 < n`; junk-guard the
`n = 0` case by `Fin (0*N)` emptiness). moves_ref: §C C.0 "(ℓ,i) ≺ (ℓ′,i′) iff
ℓ < ℓ′, or ℓ = ℓ′ and i > i′".

### D3 `RecenterLiftSpec` — the lift specification (before D2, which chooses from it)

```lean
/-- The EXACT specification of a recentering lift at node ν — verbatim the
recentering clause of MovesC's `LandingKey` (D.10's center realizer). -/
def RecenterLiftSpec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (tL : Polynomial ℤ_[p]) : Prop :=
  inC ν.σ.Φ tL ∧ tL ≠ 0 ∧ ν.σ.w tL = ν.σ.w ν.σ.Φ ∧
    ν.σ.R tL = LaurentPolynomial.C ν.center * LaurentPolynomial.T 0
```
moves_ref: MovesC `LandingKey` first conjunct; §B2-DEF D.10 "Φ′ = Φ − t,
w(t) = w(Φ), dig(t) = c̃ (position 0)".

### D2 `polOM` — the canonical policy instance (POL-PIN's carrier)  [easy]

```lean
/-- THE canonical policy — nominally the note's (S6b′) OFFSET-P policy (MovesD
§2's POL-PIN row names it so; naming per the rev-2 GAP-6 reconciliation),
delivered as the choice-selected realizer of that policy's specification: at
every node, the classically chosen realizer of `RecenterLiftSpec` when one
exists, else 0. Deterministic; reads only (σ, center) — never the lift field —
so `blind` holds. -/
noncomputable def polOM (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] :
    CanonPolicy p F where
  liftOf ν := if h : ∃ tL, RecenterLiftSpec ν tL then h.choose else 0
  blind := by
    intro ν t
    -- `{ν with lift := t}` leaves σ and center untouched; the ∃ and its choice
    -- are literally the same proposition/term.
    rfl
```
**DISPLAYED CANONICITY DEVIATION — RATIFIED (audit 2026-07-28, RULING 2; record
below):** the note's
canonical policy is the (S6b′) OFFSET-P FORMULA (§B2-DEF MOVES 2446–2449: anchor
slot j₀ forced by the congruence, summands t_k·Φ^{j₀+e·k}, prescribed digits);
`polOM` is instead THE choice-selected realizer of the SAME spec
(`RecenterLiftSpec` = D.10's clauses). Soundness of the substitution: every MovesD
theorem is ∀-pol; the counts are η-class-level and `etaData` EXCLUDES lifts (MovesD
§3.2 "lifts are policy-determined, so classes ↔ η's"); PresentNorm (U17/U18) is
what makes the count policy-independent — exactly the note's own dictionary
argument (MovesD reconciliation (6)). The offset-P FORMULA's Lean form (the j₀-sum
as a construction) remains HC-1 property and can later replace `h.choose` with
zero consumer changes (same spec). If the audit rejects the substitution, U25
re-keys to the formula and inherits HC-1's D.7 dependency — recorded as the
downgrade path.

**AUDIT RULING 2 (2026-07-28): RATIFIED, with the GAP-6 naming condition —
discharged here.** The auditor verified SPEC-IDENTITY: `RecenterLiftSpec` is
verbatim `LandingKey`'s recentering conjuncts (MovesC/Defs.lean 552–557) = D.10's
admissible-lift clause ("take ANY t ∈ C_Φ̂ with v(t) = v(Φ̂) and dig(t) = c̃",
MOVES 2593–2594); D.10's dual-accepted lift-independence ("everything below
depends on t only through (v(t), dig(t))", whose honest below-the-line scope no
HC-2 consumer crosses) + ∀-pol MovesD theorems + lift-free `etaData` (MOVESD
707–711) ⇒ every spec-realizer — the offset-P formula included — produces
identical graded data, η's, masses, counts, gates. `polOM` is deterministic;
`blind := rfl` plausible under structure eta. CONDITION DISCHARGE (GAP-6): rev 2
therefore NAMES `polOM` under the offset-P policy (docstring above) — MovesD §2's
row "pol := the (S6b) offset-P policy" is satisfied by `polOM` AS the
spec-realized instance of that policy; THIS PARAGRAPH IS THE SIGN-OFF the audit
demanded, and the wave-4 reconciliation copies it into MovesD's ledger row (seam
registry, §7.6) so no nominal drift is flagged. U25's totality-of-the-∃ (weaker
than the formula's totality; math support: PROJECT_STATE "kernel (a)+(b)
DISCHARGED") and the U30 tripwire remain the D.10 scale-risk insurance.

### D4 `ReadsOf` — the f-explicit run predicate (Wall A; the W4-1 seam)  [def-only]

```lean
/-- "History H is a classifier run on f": per read i, f's development in frame i's
key realizes the recorded side/digit data, and the recorded landing produces the
recorded next key. THE NEGOTIATING DEFINITION for MovesD's W4-1 `eligible` seam —
MovesT re-keys `TreeModel.eligible` to per-read clauses of THIS predicate. -/
def ReadsOf (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] (n : ℕ)
    (f : Polynomial ℤ_[p]) (H : History p F) : Prop :=
  f.Monic ∧ f.natDegree = n ∧
  ∀ (i : ℕ) (hi : i < H.nodes.length),
    ∃ (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ),
      IsDevelopment (H.nodes[i]'hi).σ.Φ f B Nd ∧
      SideReads (H.nodes[i]'hi) B Nd
```
with the ONE per-read clause bundle (kept a separate def so U20–U22 can consume
its conjuncts by name):
```lean
/-- The recorded read data are the ACTUAL window data of the development `B`:
(i) SIDE — the recorded span slots minimize the slot weights `w(B_j) + j·w(Φ)`
    along the recorded line, all other window slots lie strictly above it
    (D.3(a)/(c): the side is a genuine lower-hull edge over the window);
(ii) DIGITS — at every span lattice slot `j = s0 + e·k`, the recorded pattern
    digit is f's actual side digit: `σ.R (B j)` is the monomial-unit with scalar
    `pat k` at the forced position (S5);
(iii) ANCHOR/ORDER — the recorded (a, Ranch, ψ, μ) tie to `R(f)` in frame i:
    HasAnchorK (frame residual of f) a Ranch ∧ OrdPsiPoly ψ Ranch μ, at the node's
    recorded fields (Node's own hRanch/hOrd make Ranch/μ pattern-determined —
    this clause ties the PATTERN to f);
(iv) DESCENT WITNESS — `ψ (zbar) = 0` selected root (already Node.hzbarRoot) and
    the landing key is realized: `LandingKey (H.nodes[i]) (nextKeyOf H i)`
    where `nextKeyOf H i` := the recorded child frame key (i+1 < len) or the
    designated final key;
(v) LIFTS — recentering nodes carry the polOM lift: `ν.lift = (polOM p F).liftOf ν`.
def SideReads {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ) : Prop := …
```
E-phase duty: (i)–(iv)'s exact inequality forms are transcribed from §B2-DEF
D.3(a)/(c)+D.8's `LandingCylinderL` (Moves/DefsL.lean 247–259 ALREADY carries the
box/vertex/transport shape — reuse it verbatim for the μ-side reading rather than
re-deriving). moves_ref: §D4-R L2 "ALL next-node data ν = (side s, its digit
tuple, ψ, canonical lift) where s is an eligible side of the polygon f produces
in η's frame"; §C C.3 "the classifier reads actual hull sides".
NON-VACUITY ANCHOR (rev 2, audit GAP-4): U31 `gate_readsOf_inert2` instantiates
`ReadsOf` on concrete order-0 data in the FIRST E-phase block — if the E-phase
transcription of `SideReads` over-strengthens, `ReadsOf` goes EMPTY, U19–U24 turn
vacuously true, and the W4-1 `eligible` seam dies silently (the pre-rebase trap);
U31 converts that failure mode into a day-one gate. See Layer E.

### D5 `PresentSeed` — the graded seed (Wall B; the HC-1 interface)  [def-only]

REV 2 (audit GAP-5): PRUNED to the genuinely deferred fields. Moved OUT (they
were provable or constructible, inflating HC-1's obligation and falsifying the
docstring's minimality claim): `coordOf`/`coordOf_sorted`/`coordOf_lt` — the
chart is D1's `boxChart` (audit-checked against C.0's display: level-major,
base-descending, with the recorded `n = 0` junk-guard), hardwired below;
`keys`/`keys_mid`/`landing` — U1 PROVES a lawful tower exists from coherence;
`keys` becomes a structure PARAMETER with U1's laws named `KeysLawful`;
`hm`/`hN` — hypotheses at the consuming units (the tuple type is `Fin (n * N)`
directly; the parameter `m` is eliminated).

```lean
/-- U1's key-tower laws, named (rev 2): interior keys are the recorded child
keys, and EVERY read (incl. the final one) lands on `keys i`. -/
def KeysLawful {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (keys : ℕ → Polynomial ℤ_[p]) : Prop :=
  (∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i))

/-- The graded-presentation SEED: exactly the fields of `JetSetup` that MovesC's
honest boundary defers to the unbuilt graded ring (§B2-DEF R4.5 items 1&3), and
— after the rev-2 pruning — literally NOTHING else. HC-1 supplies values
(SEED-EXIST, Wall B); U13 proves `JetSetup` from a seed. Field statements are
byte-identical to `JetSetup`'s at `coordOf := boxChart n N` and these `keys`. -/
structure PresentSeed (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (H : History p F) (n N : ℕ) (keys : ℕ → Polynomial ℤ_[p]) where
  pres : ℕ → (Fin (n * N) → ZMod p) → Polynomial ℤ_[p] → Prop
  pres_zero : ∀ x f, pres 0 x f ↔
      ∀ j, x j = baseDigit p (boxChart n N j).1 (f.coeff (boxChart n N j).2)
  pres_total : ∀ i, i ≤ H.nodes.length → ∀ f : Polynomial ℤ_[p],
      f.Monic → f.natDegree = n → ∃ x, pres i x f
  Theta : ℕ → ((Fin (n * N) → ZMod p) → (Fin (n * N) → ZMod p))
  Theta_uni : ∀ i, IsUnitriangular (Theta i)
  pres_theta : ∀ i, i < H.nodes.length → ∀ x f, pres (i+1) x f → pres i (Theta i x) f
  pres_block : (verbatim JetSetup.pres_block, at these keys and boxChart)
  /-- R4.5 item 1: the graded piece map of each recorded value support — a
  TypObject with FULL alphabet (Fin S.card → ZMod p): D.3(e)(i)'s additive span +
  D.3(e)(ii)'s attainable accounting, jointly (surjectivity onto the full p^{|S|}
  alphabet IS the two identifications' consumer form). -/
  typObj : ∀ (i : ℕ) (hi : i < H.nodes.length) (S : Finset (Fin (n * N))),
      IsValueSupport H (boxChart n N) i (H.nodes[i]'hi) S →
      TypObject p (n * N) S (Fin S.card → ZMod p)
  /-- the height law consumer form (LST(i), R4.5 item 3): the DEFINED `History.htH`
  is the presentation's own height reading — carried as the ZC-seed law the U10
  induction consumes; exact clause list fixed at E-phase against C.1.5's proof
  (the per-step exactness needs: fresh clauses cut freshly = their supports are
  UNPINNED on the prior state, and the move maps carry pin status — the first is
  a fresh-band/floor consequence (U-layer), the second is C0.pinTransport;
  whatever residue of C.1.5's step is NOT derivable from the above lands HERE as
  named seed laws, never silently). -/
  zcSeed : ZCSeedLaws H (boxChart n N) pres Theta keys
```
Coverage map (audit-verified faithful, now also MINIMAL): pres/Theta + laws →
the presentation spine; typObj → the TYP piece maps + D.3(e)(ii); zcSeed →
LST(i)/the two `htH` identifications. Nothing else.
FENCE: `ZCSeedLaws` is a TO-BE-FIXED-AT-E-PHASE Prop bundle; the blueprint
pre-authorizes ONLY laws that are (a) stated in §C C.1.5/rev-9's display or
(b) §B2-DEF D.3(e) content — anything else added there is a statement-fence event
requiring sign-off. STANDING OBLIGATION (rev 2, audit GAP-7(iii)): the E-PHASE
audit round checks `ZCSeedLaws`'s final field list line-by-line against C.1.5's
proof — every field a quoted note display; the check is NOT dischargeable before
the list exists and is carried forward explicitly. [This remains the blueprint's
declared seam-of-least-knowledge: the exact split of the C.1.5 induction between
provable (U10) and seed (zcSeed) is the one genuinely open design point — the
stuck-rule's expected firing site.]

### D6 `mkFresh` — the fresh-data constructor  [def-only]

```lean
/-- Read i's fresh clauses, constructed from node geometry: one STRIP clause
`x c = 0` per band coordinate that is NOT a value position; one VALUE clause per
recorded span slot with nonempty exact-valuation level set, with support that
level set, codim = |support|, and constraint `typObj.φ x = vOf i j` (the emitted
value at the node's read digit — the R4.B.2 provenance boundary). -/
noncomputable def mkFresh {p F …} (H) (n N) {keys} (S : PresentSeed p F H n N keys)
    (vOf : ℕ → ℕ → …) (i : ℕ) (hi : i < H.nodes.length) : FreshData p (n * N) := …
```
Consumes MovesC's `C1.stripClause` (strip `LevelClause` constructor) and
`C1.TYP_toClause` (TypObject → LevelClause) — both PROVED units. The emitted
values `vOf` are a parameter at this layer (their provenance from the node's
pattern digits is the declared graded boundary, MovesC round-5 header "only the
emitted value v stays existential — R4.B.2"); U27/U28's gates fix them concretely
at order 0. Value supports: `levelSet i j := {c | fineSlot = j ∧ htH = slotVal j}`
as a Finset via `Fintype (Fin m)` + decidability-by-ℚ-equality (noncomputable
classical Finset is fine — counting is by `Nat.card`).

### D7 `mkSigma` / `mkStratum` — the state chain  [def-only]

```lean
noncomputable def mkStratum … (i : ℕ) : (Fin m → ZMod p) → Prop :=
  fun y => (mkFresh … i …).sat y   -- THE §2.1 DISPLAYED DEVIATION
noncomputable def mkSigma … : ℕ → Locus p m
  | 0     => fullBox        -- all pinned = false
  | i + 1 => pinTransportSystem (mkSigma i) (S.Theta i) (mkFresh … i)
```
`pinTransportSystem` = the digit-system re-presentation of
`(mkSigma i).pullback (Theta i) ∩ (fresh locus)` with pins = the transported pins
plus the fresh clauses' cut coordinates — built on MovesC's `C0.pinTransport`
(PROVED: pullback by a unitriangular move is a digit system with the SAME pinned
coordinates) + a strip/value pin-attachment constructor. The (ZC)-relevant
geometry (WHICH coordinates the value clauses pin) is settled by U9/U10, not by
this definition; the definition only fixes the digit-system CARRIER.

### D8 `IsReadLift` — the read-pair lift predicate (rev 2, the GAP-1 keying)  [easy]

```lean
/-- The `IsNodeLift` formula abstracted off `Node` (rev 2, audit GAP-1): stride
`e'`, CURRENT-valuation weights `σ.w (t_k) = h'·(g−k)`, digit scalars the literal
ψ-coefficients at the frame's forced (S5) positions — the READ's own pair (the
F10 adjudication), NOT the frame-creating pair of `IsStandardLift`. -/
def IsReadLift {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g e' h' : ℕ)
    (Φhat : Polynomial ℤ_[p]) : Prop :=
  ∃ tt : ℕ → Polynomial ℤ_[p],
    (∀ k, ψ.coeff k = 0 → tt k = 0) ∧
    (∀ k, k < g → ψ.coeff k ≠ 0 →
        tt k ≠ 0 ∧ inC σ.Φ (tt k) ∧
          σ.w (tt k) = (h' : ℤ) * ((g : ℤ) - (k : ℤ)) ∧
          σ.R (tt k) = LaurentPolynomial.C (ψ.coeff k) *
            LaurentPolynomial.T (- σ.t * σ.wPrev (tt k))) ∧
    Φhat = σ.Φ ^ (e' * g) + ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (e' * k)
```
definitional lemma (same file): `isNodeLift_iff : IsNodeLift ν Φhat ↔
IsReadLift ν.σ ν.ψ ν.g ν.e ν.h Φhat` — both sides are the same formula at
`(ψ, g, e', h') := (ν.ψ, ν.g, ν.e, ν.h)` (unfold). Consumers: `StageTransHyp` and
P-1-reduced key `hlift` by THIS predicate (§3); U1/U1b discharge it; U17a's
rebuilds route through it. moves_ref: MovesC `IsNodeLift` (Defs.lean 535–543) +
the round-3 F10 record ("the D.5 lift positions use the READ's own pair, while
Stage.(e,h,s,t) records the frame-CREATING read's").


## 5. Unit specs (campaign §2 format; every unit ≤ ~40 expected proof lines or pre-split)

Binder conventions for all units: `variable {p : ℕ} [Fact p.Prime] {F : Type*}
[Field F] [Finite F] {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}`;
`S : PresentSeed p F H n N keys`;
`hcoh : HistoryCoherent H`; `hreal : Realizable H`; `len := H.nodes.length`.
REV 2 NOTE (audit GAP-5): `m` reads `n * N` throughout (D5's pruning eliminated
the `m` parameter and its `hm`/`hN` fields; units needing `1 ≤ N` carry it
explicitly), and the chart is D1's `boxChart n N` wherever rev 1 wrote a seed
chart field.
`hypothesis_fields` lists the OPEN objects a statement carries — never silently
strengthened or dropped (campaign rule).

### Layer A — seed-independent facts

**U1 `keys_exist`** · file `MovesJ/U1_keysExist.lean` · statement:
```lean
theorem keys_exist (hcoh : HistoryCoherent H) :
    ∃ keys : ℕ → Polynomial ℤ_[p],
      (∀ (i : ℕ) (hi : i + 1 < H.nodes.length), keys i = (H.nodes[i+1]'hi).σ.Φ) ∧
      (∀ (i : ℕ) (hi : i < H.nodes.length), LandingKey (H.nodes[i]'hi) (keys i))
```
moves_ref: MovesC `JetSetup.keys_mid`/`landing` docstrings ("ALL reads incl. the
FINAL one obey the recorded-data landing law"). deps: Moves `L3_liftExists`
(standard lift exists, PROVED), `IsRecenteringCore` (final-read recentering:
`Φ' = Φ − lift` is explicit). sketch: interior keys are recorded (coherence's
`IsNodeLift`/`IsRecenteringCore` clauses ARE the landing law there — extract);
the FINAL key: recentering → `σ.Φ − lift` literally; else U1b `nodeLift_exists`
(rev 2: the owned stage↔node bridge, PROMOTED from this sketch's inline "check"
per audit GAP-1) gives the `IsNodeLift` witness via D8's `isNodeLift_iff` —
L3's lift is at the STAGE pair and must NEVER be conflated with the node pair
(the MovesC F10 lesson). difficulty: medium. hypothesis_fields: none.

**U1b `nodeLift_exists`** · `MovesJ/U1b_nodeLift.lean` · THE OWNED STAGE↔NODE
BRIDGE (rev 2, audit GAP-1 — the F10 trap gets a named unit instead of an inline
check). statement:
```lean
theorem nodeLift_exists (σ : Stage p F) (hσ : StageCoreL σ)
    (ψ : Polynomial ↥σ.K) (g e' h' : ℕ) (hψm : ψ.Monic) (hψd : ψ.natDegree = g)
    (hg : 1 ≤ g) (hh' : 1 ≤ h') …(the read's D.5 side conditions)… :
    ∃ Φhat, IsReadLift σ ψ g e' h' Φhat
```
moves_ref: §B2-DEF D.5 (the lift at the READ's own pair, per the F10
adjudication); MovesC `IsNodeLift` docstring. deps: D8, Moves `L3_liftExists`
(the stage-pair sibling — its proof SHAPE only, never its statement),
`Stage.hS6b`. sketch: L3's proof shape with the (S6b) realizers taken at the
node's h (current scale). NAMED RISK: the stride/stretch arithmetic — `hStretch`
puts C-weights in `e·ℤ` while the read pair wants `σ.w (t_k) = h'·(g−k)`; if some
read pairs are unreachable from (S6b)'s parent-scale realizers, the D.5 side
conditions enter as named hypotheses (statement-fence: hypothesis narrowing,
sign-off + note-line citation — the U25 pattern). Consumers: U1 (final-read
landing), U17a (rebuilt chains discharge `StageTransHyp`'s lift hypothesis), the
P-1-reduced contingency (§3). difficulty: medium. hypothesis_fields: none
(target), or the named D.5 side conditions (fallback).

**U2 `mkFresh_disj`** · `MovesJ/U2_freshDisj.lean` ·
`(mkFresh … i hi).clauses.Pairwise (Disjoint ·.support ·.support)`.
moves_ref: §C C.1.5′ "pairwise disjoint: the factors multiply". deps: D6. sketch:
strips are singletons at non-value coords; value supports are level sets of
distinct span slots (distinct fine blocks → disjoint) and exclude non-value
coords by definition; list construction indexes clauses by disjoint coordinate
sets. difficulty: easy-medium. hypothesis_fields: none.

**U3 `mkFresh_band`** · `MovesJ/U3_freshBand.lean` ·
`∀ cl ∈ (mkFresh … i hi).clauses, ∀ c ∈ cl.support, inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c`.
moves_ref: MovesC `JetSetup.fresh_band` docstring. deps: D6. sketch: strip
supports are chosen from the band; value level-set members have height = slotVal
(the band's upper edge) — membership needs `floorH < slotVal ≤ slotVal` and
`< prevRim`: the former is the band's own selection (value slots past the (γ)
crossing have empty level sets IN THE BAND — D6 constructs value clauses only at
slots with `floorH < slotVal`), the latter from D6's slot range. difficulty:
medium. hypothesis_fields: none.

**U4 `mkFresh_cover`** · `MovesJ/U4_freshCover.lean` ·
`inFreshBand … c → ∃ cl ∈ (mkFresh … i hi).clauses, c ∈ cl.support`.
moves_ref: `fresh_cover` docstring ("every band coordinate lies in SOME clause's
support — EXACTLY one, by disj"). deps: D6, U2. sketch: dichotomy on
`IsValueCoord c`: value → c is in its slot's level set = that value clause's
support; non-value → its strip clause exists by D6's strip roster (indexed by
exactly the non-value band coords). difficulty: easy-medium. hypothesis_fields:
none.

**U5 `mkFresh_assembled`** · `MovesJ/U5_freshAssembled.lean` · the
`fresh_assembled` disjunction for `mkFresh`, verbatim MovesC's field type.
moves_ref: MovesC round-5 header "exact geometric fresh-clause identification".
deps: D6, `C1.TYP_toClause` (PROVED), `IsValueSupport`. sketch: by construction —
strips carry the ¬IsValueCoord tag from their roster; value clauses carry
`IsValueSupport` (their support IS a slot level set, both directions of the iff
from D6's set-builder), `codim = card` by `C1.TYP_toClause`'s clause shape, and
the TypObject/`v` witnesses are D6's own data. difficulty: medium (iff
bookkeeping). hypothesis_fields: the emitted values `vOf` (R4.B.2 boundary —
free parameters here).

**U6 `mkFresh_mstar`** · `MovesJ/U6_mstarEq.lean` ·
`(mkFresh … i hi).mstar = Nat.card {c : Fin m // inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c}`.
moves_ref: `mstar_eq` docstring ("the presented fresh codimension sum equals the
FRESH-BAND count computed from node data"). deps: U2–U5. sketch: mstar = Σ codim
= Σ strips 1 + Σ value |support| = |non-value band| + |value band| (U3 supports ⊆
band, U4 cover, U2 disjoint ⇒ the supports PARTITION the band; strips contribute
1 = |{c}|, value clauses |support|); finish by `Finset.card_biUnion`.
difficulty: medium. hypothesis_fields: none.

**U7 `mkSigma_init_rec`** · `MovesJ/U7_sigmaRec.lean` · two lemmas:
`(mkSigma … 0).pinned c = false` and the `recursion` law
`(mkSigma … (i+1)).IsSolution x ↔ ((mkSigma … i).IsSolution (S.Theta i x) ∧ mkStratum … i (S.Theta i x))`.
moves_ref: `JetSetup.init`/`recursion` field types. deps: D7, `C0.pinTransport`
(PROVED), S.Theta_uni. sketch: init is definitional; recursion = pinTransport's
solution-set law + the fresh-cut attachment's solution-set law. difficulty:
medium. hypothesis_fields: none.

**U8 `mkStratum_inh`** · `MovesJ/U8_inhImplied.lean` ·
`(mkSigma … i).IsSolution y → (mkStratum … i y ↔ (mkFresh … i hi).sat y)` — by
`Iff.rfl` under D7's definition. **CARRIES THE §2.1 DEVIATION DISPLAY in its
docstring; the audit round rules.** difficulty: easy (or re-opens as hard if the
ruling demands the inherited carrier). hypothesis_fields: none.

**U11 `root_height_of_inBox`** · `MovesJ/U11_rootHeight.lean` ·
```lean
theorem root_height_of_inBox (hcoh : HistoryCoherent H) (hbox : InBox n H) :
    ∀ (hj : 0 < H.nodes.length) (b : ℕ),
      b < (H.nodes[0]'hj).μ * (H.nodes[0]'hj).childWidth → 1 ≤ (H.nodes[0]'hj).line.at b
```
moves_ref: MovesC `JetSetup.root_height` docstring ("D.4's ROOT case: every side
slope ≥ 1; the cluster zeros pin level 0, floor height 1"). deps: MovesD `InBox`
(E-phase core). sketch: InBox gives the root side inside the degree-n box —
intercept/slope bounds; the line at interior b ≥ its value at the right interior
edge ≥ 1 (descending line, endpoint arithmetic). RISK: if MovesD's `InBox` turns
out weaker than the height bound, this unit's hypothesis must be upgraded to the
D.4 root clause — statement-fence event, sign-off required (never prove from
junk). difficulty: medium. hypothesis_fields: `hbox`.

### Layer B — the (ZC) induction (the hard core of the hard core)

**U9 `zc_root`** · `MovesJ/U9_zcRoot.lean` ·
`ZCData (mkSigma … 1) (boxChart n N) (H.htH 1) (H.floorH 1) ((H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth)`
(the i = 0 instance of `JetSetup.zc`). moves_ref: §C C.2 proof "initialized at
the root (C.1.5's base = D.8 + D.11 at ν₀)". deps: U7, D6/D7, S.zcSeed, U11.
sketch: after the root read, pins = root fresh cuts; downset-exactness: a level-0
interior coordinate has htH = ℓ ≤ floor iff it is a cluster-zero strip (U3/U4's
partition + root_height puts the floor at ≥ 1); interior zeros: strips solve to
0 by construction; value pins sit at the rim by the root band's shape.
difficulty: hard (pre-split: U9a downset ⊆, U9b ⊇, U9c interior_zero).
hypothesis_fields: S.zcSeed.

**U10 `zc_step`** · `MovesJ/U10_zcStep.lean` · the inductive step: given
`ZCData (mkSigma … (i+1)) … (rim i)`, prove
`ZCData (mkSigma … (i+2)) (boxChart n N) (H.htH (i+2)) (H.floorH (i+2)) (rim (i+1))`.
moves_ref: §C C.1.5 (per-step conditional exactness): "(1) multiplies the mass by
exactly vol_nom(E_fresh(ν_{i+1})); (2) re-establishes (ZC)". deps: U3–U7, S
(zcSeed, Theta_uni, pres_block), `C0.pinTransport`, MovesC `C2.freshFree`,
`C3.lineDom` (PROVED consumers of the same geometry), `hreal` (the per-step
`TransitionAdmissible` via `JetSetup.realizable`'s definitional unfold — rev 14's
DOM hypothesis). sketch (C.1.5's proof, note-accepted): the move Θ_i carries pin
status (pinTransport); the new floor is the old max'd with ν_{i+1}'s staircase
(floorH_succ, PROVED); fresh cuts land strictly above the old floor and inside
the region (U3), so the downset grows by exactly the strip zeros + the sub-line
levels; (SAE)/(NA)/DOM order the lines so no old pin resurfaces above the new
floor; rim leads = the value clauses at the new rim. PRE-SPLIT (mandatory):
U10a floor-monotone downset transport; U10b fresh-cut downset exactness; U10c
interior zeros; U10d rim-lead placement. difficulty: HARD ×4 — the pre-declared
escalation-risk center. Whatever step resists derivation is a candidate zcSeed
law (D5's fence) — via the stuck rule, NEVER a silent axiom. hypothesis_fields:
S.zcSeed, hreal.

**U13 `jetSetup_of_seed`** · `MovesJ/U13_assembly.lean` ·
```lean
theorem jetSetup_of_seed {keys : ℕ → Polynomial ℤ_[p]} (hkeys : KeysLawful H keys)
    (S : PresentSeed p F H n N keys) (hN : 1 ≤ N)
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H)
    (vOf : …) : Nonempty (JetSetup H n N (n * N))
```
moves_ref: MovesC `JetSetup` structure (all 29 fields — rev 2, audit GAP-7(i):
the round-6 structure has 29, not the 25 rev 1 claimed). deps: D1 (`boxChart` +
its two lemmas supply the chart fields), U1 (discharges `hkeys` at call sites),
U2–U11 (+U9/U10 for `zc`), D5–D7. sketch: field-by-field packaging;
`coordOf := boxChart n N` with D1's lemmas, `keys := keys` with `hkeys`'s two
laws, `coherent := hcoh`, `realizable := hreal`, seed fields verbatim,
constructed fields with their U-layer laws. difficulty: medium (assembly only).
hypothesis_fields: S (SEED-EXIST's payload), hkeys (U1-dischargeable), hN, hbox,
vOf.

### Layer C — MovesD discharge

**U14 `NP_fits`** · `MovesJ/U14_npFits.lean` · statement (against MovesD §3.3's
shape replica): for `P : Shape n`, `H ∈ PrefSet n pol P`, `N ≥ (P : ShapePrefix).NPband n`:
every coordinate of every `mkFresh` support and every `Z = ⊤` pin has base level
`< N` — i.e. the constructed system fits the box (C.2's "N ≥ N(H,Z)" largeness,
at the shape bound). moves_ref: §C C.2 "N(H,Z) := 1 + the largest BASE level
occurring among the coordinates of T(H,Z)'s equations"; MovesD W4-4 (NP-ID) —
THIS UNIT IS NP-ID's ⊆ direction; its moves_ref must carry the W4-4 pointer.
deps: U3 (supports ⊆ band), MovesD `bandS`/`NPband` (shape-level band replica,
E-phase core). sketch: band coordinates' levels are bounded by the shape's band
levels (htH arithmetic vs the line data, which are shape-pinned by MatchesHist);
NPband is 1 + their max. difficulty: medium-hard (the htH ↔ bandS arithmetic).
hypothesis_fields: none beyond PrefSet membership.

**U15 `present_exist_of_seeds`** · `MovesJ/U15_presentExist.lean` ·
```lean
theorem present_exist_of_seeds {P : Shape n}
    (hseed : ∀ (i : PrefIdx n (polOM p F) P) (N : ℕ), P.NP (polOM p F) ≤ N →
       ∃ keys, KeysLawful (reprOf i) keys ∧
         Nonempty (PresentSeed p F (reprOf i) n N keys))
    (hnorm : PresentNorm n (polOM p F) P) :
    ∀ N : ℕ, P.NP (polOM p F) ≤ N → Nonempty (Presented p F n N (n * N) (polOM p F) P)
```
moves_ref: MovesD §2 PRESENT-EXIST row ("∀ N ≥ P.NP pol, Nonempty (Presented …) —
presentability at every level of L12's exact range (§C C.2)"). deps: U13, U14
(reprOf i ∈ PrefSet gives hcoh/hreal/hbox), U17/U18 (hnorm — or carried).
sketch: obtain `⟨keys, hkeys, ⟨S⟩⟩ := hseed i N hN`; `jet i := jetSetup_of_seed
hkeys S …`; `hnorm := hnorm`. `hseed` is SEED-EXIST VERBATIM (Wall B's rev-2
display — the single, reprOf-form statement recorded as HC-1's deliverable per
audit GAP-5; rev 1's two divergent displays are gone). difficulty: easy-medium.
hypothesis_fields: **hseed = SEED-EXIST (HC-1)**; hnorm (dischargeable by
U17/U18, else carried).

**U16 `threshold_of_seeds`** · `MovesJ/U16_threshold.lean` ·
`… → Nonempty (Threshold p F n (polOM p F) P)` via MovesD's `TW_threshold_witness`
+ U15. moves_ref: MovesD §2 Threshold/TW row. deps: U15, MovesD TW unit.
difficulty: easy. hypothesis_fields: hseed, hnorm.

**U17a `lift_swap`** · `MovesJ/U17a_liftSwap.lean` · statement: for
`H ∈ PrefSetAny n P` there is `H'` with the SAME shape, side digits, and
ψ-coefficients per read (i.e. `etaData … H' = etaData … H`), all recentering
lifts = `polOM.liftOf`, `HistoryCoherent H'`, `Realizable H'`, `InBox n H'`.
moves_ref: MovesD §3.2 PresentNorm docstring clause (i) totality "= L1's
kernel-(a) totality + the L6-corollary + conjugation equivariance"; §B2-DEF D.10
"lift independence". deps: U25 (polOM total on eligible nodes), U1b (read-pair
lift discharge), Moves `L5_recLiftIndep_R4` (PROVED — D.10's lift-independence
core), `StageTransHyp` (swapping a lift changes the child key `Φ′ = Φ − t′`, so
the DOWNSTREAM stages must be rebuilt — stage existence enters HERE, ONLY through
the named hypothesis: rev 2 per audit GAP-6/§7.3(v), no unit names P-1). sketch:
induct along the chain; at each recentering replace lift and rebuild the child
stage by `IsRecenteringCore` (explicit construction, Moves DefsCore 242 — check
whether the recentered stage is CONSTRUCTED by a proved Moves unit or only
specified; if specified-only, this is `StageTransHyp`'s recentering sibling —
extend `StageTransHyp`'s signature, a designer-round event, or consume HC-1);
transport the remaining reads (their data are development-side, unchanged by the
D.10 independence lemma). difficulty: HARD — escalation risk; the one unit
consuming stage RECONSTRUCTION. hypothesis_fields: `StageTransHyp` (§3 —
discharge: HC-1's D.7 induction, or the recorded P-1-reduced contingency;
consumer-invisible either way).

**U17b `galois_normalize`** · `MovesJ/U17b_galois.lean` · statement: for coherent
realizable H there is `φ : F ≃+* F` and `H'` with `zbar`'s = `canonRoot` at every
read, `EtaGalEq (etaData … H) (etaData … H')`, coherence/realizability preserved.
moves_ref: MovesD `EtaGalEq`/`canonRoot` defs; §0.6 root-normalization gate.
deps: mathlib finite-field Galois (`ZMod.algHom_ext`-family, Frobenius closure),
MovesD `fieldEnum`. sketch: per read, the recorded `zbar` and `canonRoot ν` are
roots of the same irreducible `ψImage`; a power of Frobenius over the frame
subfield maps one to the other; compose down the tower (finite chain; the
automorphism group of a finite field is cyclic, generated by Frobenius —
extension over the recorded subfield tower is elementary Galois theory of finite
fields); transport all node data along φ (a ring-iso commutes with every clause
in Node's Prop fields — mechanical but long). difficulty: hard (pre-split:
U17b-1 single-read root swap; U17b-2 tower composition; U17b-3 data transport).
hypothesis_fields: none.

**U17c `presentNorm_total`** · `MovesJ/U17c_total.lean` · the totality clause of
`PresentNorm n (polOM p F) P` from U17a + U17b + membership bookkeeping
(`H' ∈ PrefSet` → its class is a `PrefIdx` member). difficulty: medium.
hypothesis_fields: inherits U17a's stage supplier.

**U18 `presentNorm_unique`** · `MovesJ/U18_unique.lean` · the uniqueness clause:
`H, H' ∈ PrefSet, EtaGalEq (etaData H) (etaData H') → etaData H = etaData H'`.
moves_ref: MovesD §3.2 clause (ii) "UNIQUENESS (embedding rigidity)". deps:
MovesD canonRoot/fieldEnum; mathlib. sketch: both normalized ⇒ each read's
residue root is the fieldEnum-LEAST root of its ψ-image; the EtaGalEq
automorphism φ maps ψ-coefficients to ψ′-coefficients and roots to roots; by
induction up the tower φ fixes the generated subfield (least-root pinning:
φ permutes the root set of the SAME polynomial once coefficients are fixed, and
order-preservation of the FIXED enumeration forces the least root to the least
root — φ fixes it; then the frame subfield of the next read is generated by
fixed elements). PROOF-FIRST — and rev 2 REMOVES the illusory axiom fallback
(P-3 STRUCK, audit GAP-3: it could not discharge this statement as typed). If
the proof fails, the consumers carry `OmUniqHyp` (§3), typed verbatim as this
statement — a recorded non-discharge, never a declaration. difficulty: hard.
hypothesis_fields: none (or `OmUniqHyp` if it fails).

### Layer D — the run predicate and realizability (Wall A)

**U19 `readsOf_coherent`** · `MovesJ/U19_runCoherent.lean` ·
`ReadsOf p F n f H → HistoryCoherent H`. moves_ref: MovesC `HistoryCoherent`
docstring ("the recorded frames are linked by the ACCEPTED §B2-DEF transitions AT
THE RECORDED NODE DATA"). deps: D4; Moves L4_TRANS* (PROVED transition items).
sketch: SideReads(iv)'s landing + the recorded child stages give the
IsNodeLift/IsRecenteringCore legs; slope/γ/width ties are SideReads(i)'s line
arithmetic. NOTE: if D4 (by design) RECORDS coherence-adjacent data rather than
re-deriving it, parts collapse to projections — the E-phase decides which
clauses of HistoryCoherent are D4-recorded vs derived; the unit's statement is
fixed either way. difficulty: medium. hypothesis_fields: none.

**U20 `readsOf_NA`** · `MovesJ/U20_NA.lean` · for consecutive reads of a run
with `s0' + wSide' < μ` (non-adjacent): the (NA) strict inequality of
`TransitionAdmissible`. moves_ref: §C C.0 (NA) display; C.3 "the classifier
reads actual hull sides". deps: D4 (SideReads(i)), hull convexity (Moves
L2_widthBound/L2_strideRule + line arithmetic). sketch: the new side is a lower
hull edge of the CHILD development whose window ends strictly left of the
standing vertex; the standing vertex's value is the old line's; strict
convexity of the hull at the vertex + the side's minimality give the strict
gap at base index μ·D. difficulty: hard-ish (medium-hard). hypothesis_fields:
none.

**U21 `readsOf_HV`** · `MovesJ/U21_HV.lean` · adjacent reads: the pattern lead
equals `vtx(νp)` in F. moves_ref: §C C.0 (HV) "the data IDENTITY pattern lead of
ν_{i+1} = vtx(ν_i) with the FULL transported vertex value". deps: D4, Moves
`L5_landVertexDigit{,_repair}` + `L5_landTransport_R4` + `LandingCylinderL`
(PROVED — D.8's two-sided landing with the vertex unit). sketch: the adjacent
read's hinge digit is the transported vertex digit by D.8's (VERTEX) clause of
the landing cylinder; unfold `Node.vtx`'s scalar bookkeeping (`z̄^{a−μm̂}` — the
anchor/normalization exponents match `LandingCylinderL`'s `T(μ·m̂ − a)` unit
literally). difficulty: HARD (exponent bookkeeping across two conventions —
the MovesC F10 index lesson applies; escalation risk). hypothesis_fields: none.

**U22 `readsOf_SAE`** · `MovesJ/U22_SAE.lean` · the span-entry inequalities:
`new(j) > old(j)` at span slots `j < μ`, equality at the adjacent vertex.
moves_ref: §C rev 12 (SAE) display (MovesC `TransitionAdmissible` conjuncts
3–4). deps: D4, the parent's (ZC)-zeroed strips (the stratum's interior zeros
raise actual valuations strictly above the old line), K1 slot reading. sketch:
on the descend stratum the sub-line digits are zero, so each span coefficient's
actual weight exceeds the old line at its slot; the new line reads ACTUAL
weights (SideReads(i)), giving strictness below the vertex; at the vertex the
side passes through the standing vertex (adjacent case) — equality. difficulty:
HARD (escalation risk; this is the clause whose ABSENCE the F-EMPTY refutation
exposed — the unit's docstring must cite the F-EMPTY record). hypothesis_fields:
none.

**U23 `readsOf_realizable`** · `MovesJ/U23_runRealizable.lean` ·
`ReadsOf p F n f H → Realizable H` — assembly of U20–U22 over the per-step
dichotomy (`s0+w < μ` | `= μ`; the `> μ` case excluded by coherence's window
containment). difficulty: easy given U20–U22. hypothesis_fields: none.

**U24 `readsOf_canonical`** · `MovesJ/U24_runCanon.lean` ·
`ReadsOf p F n f H → (polOM p F).IsCanonPres H` given SideReads(v) + the
canonRoot clause added to D4 (or stated with the root-normalization hypothesis).
E-phase decision: bake `zbar = canonRoot` into SideReads(v) (making runs
normalized by definition — matches §D4-R's "the classifier is run with ONE lift
rule" + rev-6 canonRoot pinning) — then this unit is a projection. difficulty:
easy. hypothesis_fields: none.

**U25 `polOM_total`** · `MovesJ/U25_polTotal.lean` · statement: at every
recentering node ν of a coherent realizable history (i.e. every node with
`ν.species = recentering` reachable in `PrefSetAny`), `∃ tL, RecenterLiftSpec ν tL`
— hence `polOM.liftOf ν` satisfies `RecenterLiftSpec`. moves_ref: §D4-R L1
(canonical-choice totality, kernel (a) — DUAL-VERIFIED at the math level:
PROJECT_STATE "kernel parts (a)+(b) DISCHARGED"); §B2-DEF (S6b′) consumers item
(ii) "the recentering lift (D.10): W = λ″ > w(Φ̂) — (I-aug) is literally the
hypothesis". deps: `Stage.hS6b` + coherence's (I-aug) chain. sketch: the spec
demands `w tL = w Φ` with digit = center at position 0; realize via hS6b one
scale down per the (S6b′) two-line recursion. **NAMED RISK (resolve FIRST at
E-phase, before any prover runs):** the scale bookkeeping — `RecenterLiftSpec`
wants `σ.w tL = σ.w σ.Φ` while `hStretch` puts C-weights in `e·ℤ`; the note's
D.10 resolves this with the eligibility side conditions (e_read = 1 reads;
which frames admit recenterings) — the unit owner must first transcribe D.10's
eligibility EXACTLY (MOVES 2583–2671) and, if the Lean node vocabulary admits
ineligible recentering nodes that the note excludes, U25's hypothesis must name
the eligibility predicate rather than all-recenterings (statement-fence: this
is a hypothesis NARROWING, needs sign-off + a note-line citation). difficulty:
HARD (escalation risk #1 for arithmetic). hypothesis_fields: none (target), or
the named eligibility predicate (fallback).

**U26 `class_fiber_welldef`** · `MovesJ/U26_fiberWelldef.lean` ·
`ClassFiberWelldef p F n N m pol P` (MovesD §3.4's Prop) — one η-class, one
classifier locus. PROOF-FIRST route: two PrefSet representatives of one class
have equal `etaData` (U18), and `SHZ ⊤` is a function of (shape, etaData,
policy-determined lifts, seed) — the seed-dependence is the honest catch:
DIFFERENT seeds may present differently; the Prop (check MovesD's final typing
at E-phase) should be consumed at FIXED presentation data. If the Prop
quantifies over jets, prove locus-equality via Theorem C(a) (both loci = the
same transported T(H,⊤) system). DEFERRABLE: D15 carries it as `hwd`; deferral
is a recorded non-discharge, not a failure. difficulty: hard. fallback:
`OmUniqHyp` (§3; P-3 STRUCK — rev 2). hypothesis_fields: possibly `OmUniqHyp`.

### Layer E — the order-0 gates (the realF2 lesson; run FIRST at E-phase)

**U27 `gate_order0_inert`** · `MovesJ/U27_gateInert.lean` · the root-only n = 2
inert history at p = 2: construct `H₀` (one root read; the inert shape's side +
residual data), the U1 key tower, a CONCRETE `PresentSeed` at it (rev 2: the
chart is D1's `boxChart`, no longer a seed field; the seed supplies `pres` — the
literal `baseDigit` chart at the root-only history — Theta trivial since len = 1
uses only Θ₀, plus concrete typObj/zcSeed), fire `jetSetup_of_seed`, then check
via MovesC `C6.thmC_b`:
`Nat.card (S(H₀,⊤) ∩ box) * 2^(totalPins) = 2^(2N)` with totalPins = the inert
shape's m* — and tie the resulting stratum mass to the independently recorded
engine value (realM2's decided count for the inert shape at n = 2; the 1/4
density anchor of `gate_v2_countingDensity_inert2`). Numeric form: an `example`
with `decide`/`Nat.card` computation at N = 2 or 3 (small!); if kernel-decide
is too heavy, the recorded-count comparison goes to `verification/` Python with
the number pinned in the docstring (census stop-the-line discipline).
difficulty: medium. hypothesis_fields: none — THIS UNIT MUST BE AXIOM- AND
SEED-HYPOTHESIS-FREE (the seed is constructed concretely; that is the point).

**U28 `gate_order0_sep`** · `MovesJ/U28_gateSep.lean` · same at q′ = 3: the split
and inert root histories yield DIFFERENT masses (σ-separation through the
bridge; the V2 gate's mirror: split 1/9 ≠ inert 1/3 at the tame prime 3 — here
as the corresponding stratum-count inequality at a fixed small N). difficulty:
medium. hypothesis_fields: none.

**U29 `gate_NP`** · `MovesJ/U29_gateNP.lean` · the MovesD gate instance: for the
worked shape P̂* (MovesD §3.3's gate row), the CONSTRUCTED system's largest
equation level + 1 = 5 = `Shape.NP` — U14's arithmetic at one census-pinned
instance (`NP(P̂*) = 1 + 4 = 5, the note's own derivation`). difficulty: easy-
medium. hypothesis_fields: none.

**U30 `gate_polOM`** · `MovesJ/U30_gatePol.lean` · a concrete recentering node
(the Case-L gate's recentering read data at p = 2, transcribed) on which
`∃ tL, RecenterLiftSpec ν tL` is PROVED by explicit witness — polOM's totality
instantiated once, axiom-free (U25's non-vacuity anchor, and the D.10-arithmetic
risk's early tripwire: if even the witness instance fails to typecheck against
`RecenterLiftSpec`, the scale-bookkeeping risk fires at day one, not at
escalation). difficulty: medium. hypothesis_fields: none.

**U31 `gate_readsOf_inert2`** · `MovesJ/U31_gateReadsOf.lean` · the `ReadsOf`
non-vacuity anchor (rev 2, audit GAP-4): at U27's root-only inert history `H₀`
(p = 2, n = 2), a CONCRETE monic quadratic `f` (the inert gate's polynomial —
the E-phase pins the exact instance from the W1/realF2 gate data) with
`ReadsOf 2 F 2 f H₀` PROVED by an explicit development witness — axiom- and
seed-free. Purpose: D4's `SideReads` body is an E-phase transcription duty; if
the transcription over-strengthens, `ReadsOf` is EMPTY, U19–U24 become vacuously
true, and the W4-1 `eligible` seam (MovesT re-keys to THIS predicate) dies
silently — the pre-rebase trap the charge's item 2 exists for. U31 converts that
silent death into a day-one gate failure; it runs in the FIRST E-phase block
with U27/U30. difficulty: medium. hypothesis_fields: none.

## 6. The DAG, difficulty census, escalation-risk set

```
D1 D3 D2 D8 D4 D5 D6 D7                  (Defs; D5's zcSeed list = E-phase design duty)
 │        │  │  │  │
 ├─ U1 ← U1b(D8) ──┼──┤    U19 ← D4      U25 ← D2,D3   (U30+U31 tripwires first)
 ├─ U2 U3 U4 U5 U6 ← D6    U20 U21 U22 ← D4,Moves-L5
 ├─ U7 U8 ← D7             U23 ← U20–22
 ├─ U11 ← MovesD.InBox     U24 ← D4     U31 ← D4 (concrete f at U27's H₀)
 ├─ U9 ← U7,U11,zcSeed
 ├─ U10a–d ← U9,U3–U7,zcSeed,hreal
 └─ U13 ← D1,U1,U2–U11
U14 ← U3,MovesD.bandS      U27 U28 ← U13(concrete seed), MovesC.thmC_b   U29 ← U14
U15 ← U13,U14,(SEED-EXIST),(hnorm)       U16 ← U15,MovesD.TW
U17a ← U25,U1b,Moves.L5_recLiftIndep,(StageTransHyp)   U17b   U17c ← U17a,U17b
U18 (proof-first; OmUniqHyp if it fails)  U26 ← U18,thmC_a (deferrable)
```

Census, flat prover-unit granularity (pre-splits counted): D1–D8 (8) +
U1, U1b, U2–U8 (9) + U9a–c (3) + U10a–d (4) + U11, U13, U14, U15, U16 (5) +
U17a, U17b-1..3, U17c (5) + U18 (1) + U19–U26 (8, incl. U26 deferrable) +
U27–U31 (5) = **48 units** (rev 1: 45; rev 2 adds D8 + U1b per audit GAP-1 and
U31 per GAP-4; nothing removed — the phantom "U12′" was never counted).
Difficulty: easy 12 (D1–D8, U8, U16, U23, U24) · medium 20 (U1, U1b, U2–U7,
U11, U13, U14, U15, U17c, U19, U20, U27–U31) · **HARD 16** (U9a–c, U10a–d,
U17a, U17b-1..3, U18, U21, U22, U25, U26) — of which the PRE-DECLARED
ESCALATION-RISK SET is unchanged: **U10 (the C.1.5 step, ×4), U25 (D.10 scale
arithmetic), U21 (D.8 exponent bookkeeping), U22 (SAE strictness), U17a (stage
reconstruction)**. Expected stuck-rule firings: U10 (→ zcSeed law extraction,
the D5 fence) and U25 (→ eligibility-predicate narrowing, statement-fence).

## 7. Process notes (binding on E/P phases)

1. **Order of battle.** E-phase ELABORATES D1–D8 + U27/U30/U31 FIRST (the realF2
   lesson: the concrete order-0 seed, the polOM witness instance, and the ReadsOf
   instance are the cheapest falsifiers of the whole design — if any fails to
   TYPECHECK, the Defs are wrong, not the provers). REV-2 READING NOTE (audit
   GAP-7(ii)): "first" means elaborate/typecheck-first, NOT prove-first — U27's
   PROOF needs U13 ← U9/U10; the prover-phase scheduler orders PROOFS by the §6
   DAG. Then layer A, then B, then C/D in parallel. Gates U27–U29 + U31 gate the
   corpus's acceptance exactly as RealInstanceV2Gates gated the V2 capstone.
2. **Statement fence.** MovesC/Defs.lean, MovesD's accepted Defs, and Moves/Defs*
   are FROZEN inputs — HC-2 adds files, never edits them. Any needed change is a
   designer-round event with sign-off. The two displayed deviations (§2.1
   stratum-as-fresh; D2 polOM-as-choice) were RATIFIED at the audit round
   (records inline; D2's carried the GAP-6 naming condition, discharged there).
   The remaining authorized flex points are the two pre-declared possible
   hypothesis adjustments (U11 InBox strength; U25 eligibility) plus U1b's D.5
   side-condition fallback (rev 2) — each a statement-fence event needing
   sign-off.
3. **Audit charge additions — REV-2 DISPOSITIONS:** (i) DONE — both deviations
   RATIFIED (records at §2.1 and D2). (ii) STANDING OBLIGATION, carried to the
   E-PHASE audit round (audit GAP-7(iii)): check D5's final `ZCSeedLaws` field
   list line-by-line against §C C.1.5's proof — every field a quoted note
   display; not dischargeable before the list exists. (iii) DONE — the
   `hbr`-drop probe fired and refutes (the §D4-R F1 instance); it survives P-3's
   striking as the STANDING PROBE for any future uniqueness declaration (§3).
   (iv) DISSOLVED — the stage-minus-ledger restatement removes every `Stage`
   field from P-1's conclusion; (S6) attainability sits in `StageLedgerHyp`
   (ours), no longer a citation question. (v) ENFORCED at rev 2 — every
   hypothesis_field names supplier hypotheses only (`StageTransHyp`,
   `OmUniqHyp`); no unit names P-1/P-2/P-3.
4. **Axiom gate.** Applies to the ONE surviving contingent proposal,
   P-1-reduced (§3; P-2/P-3 struck) — and only if its named contingency state
   fires. Then: re-extract the GMN PDF lines for each cited theorem into
   `GMN_citations.md` (§P5+ entries), write the faithfulness entry from §3's
   rev-2 draft, run the guardian, and add the mutation probes as compiled
   `example`-refutation blocks next to the axiom (the `OM/QpTypeChain.lean`
   Block-7b pattern). ("HN" pinning is moot — §3 header.) Footprint census:
   `AxChk_baseline` gains a MovesJ section; the
   MovesC 36/36 and every density capstone must remain Lean-core-only — any
   declared HC-2 axiom may appear ONLY in MovesJ/MovesD-discharge footprints.
5. **Codex budget.** Per the campaign ledger (90%+ used, reset Sun Aug 02):
   this blueprint's audit round runs on fresh-Fable legs now; the Codex leg is
   the FINAL confirmation, batched post-reset with the MovesS/MovesD
   ratifications.
6. **Seam registry (who unblocks whom).** HC-1 → SEED-EXIST (the rev-2 form:
   the reprOf + `KeysLawful` display, Wall B — the ONLY display) and
   `StageTransHyp`'s discharge (U17a); the P-1-reduced contingency (§3) fires
   ONLY in the named StageLedgerHyp-without-skeleton state. MovesT (wave 4) →
   re-keys W4-1 `eligible` to D4's SideReads clauses (non-vacuity anchored by
   U31) and consumes U14 as NP-ID's ⊆ direction. MovesD E-phase core →
   `CanonPolicy`/`Shape`/`PrefSet`/`PresentNorm`/`Presented`/`Threshold` binders
   used verbatim here; if its audited types drift during its Codex ratification,
   U14–U18 re-elaborate (statements re-generated from this blueprint's semantic
   specs — the specs, not the transcribed binders, are normative). REGISTERED
   (rev 2, audit GAP-6): the POL-PIN naming reconciliation — D2's sign-off
   (polOM = the (S6b′) offset-P policy, spec-realized) is copied into MovesD
   §2's POL-PIN row at the wave-4 reconciliation, so the seam registry never
   flags nominal drift between the two ledgers.

## 8. Audit record (rev 1 → rev 2) — the findings table

Rev-1 verdict (fresh-instance audit, `HC2_AUDIT_FABLE_2026-07-28.md`): **REJECT,
1 critical / 7 gaps**; perimeter = the §3 axiom-proposal surface plus four
spec-hygiene gaps; the architecture (three walls, D1–D7, U-layer, both displayed
deviations, gate block, seam registry) RATIFIED. Rev-2 dispositions:

| finding | class | rev-2 disposition | where |
|---|---|---|---|
| CRIT-1: P-1's conclusion smuggled the graded-localization ledger (`Stage`/`StageCoreL` fields are OUR D.0(P2)/D.1(e)/D.2(S4) content; even the mapped residual laws exceed GMN's ∼-forms); the SAYS-NO-MORE draft was false | CRITICAL | P-1 rebuilt STAGE-MINUS-LEDGER (ledger-free skeleton conclusion, ∼-strength residual laws; Bézout window dropped from the statement); consumer analysis shows the reduced form alone discharges nothing → DEFAULT = NO DECLARATION; consumers carry `StageTransHyp`; the factored contingency (P-1-reduced + `StageLedgerHyp`) recorded; SAYS clauses redrafted truthfully | §3 P-1 |
| GAP-1: `IsStandardLift` (stage pair) vs `IsNodeLift` (read pair) conflation; no owned bridge (the F10 trap) | GAP | new D8 `IsReadLift` (keying folded into the signatures; `isNodeLift_iff`) + owned bridge unit U1b `nodeLift_exists`; `StageTransHyp`/P-1-reduced key `hlift` at the READ pair; any re-keying = fresh guardian pass | §3 P-1, D8, U1b |
| GAP-2: P-2's post-carve-out residue already proved (Fact A/B); "interchangeable suppliers" not literal; phantom U12′ | GAP | P-2 STRUCK to tombstone (no axiom, no new hypothesis — SEED-EXIST sole supplier); both defects recorded; the phantom unit deleted | §3 P-2 |
| GAP-3: P-3 cannot discharge U18/U26 as typed (same-f/`hbr` hypotheses unavailable); (P4b) cites choice-DEPENDENCE, not the equality | GAP | P-3 STRUCK to tombstone; `OmUniqHyp` (typed verbatim as U18) carried on proof failure; the `hbr`-drop probe RETAINED as the permanent standing falsifier | §3 P-3, U18/U26 |
| GAP-4: `ReadsOf` had no non-vacuity anchor among the units (the W4-1 seam could die silently) | GAP | new gate unit U31 `gate_readsOf_inert2` — concrete order-0 instantiation, axiom- and seed-free, first E-phase block | U31, D4, §7.1 |
| GAP-5: `PresentSeed` not minimal (provable fields inflated HC-1's obligation); SEED-EXIST's two displays differed | GAP | D5 pruned to the genuinely deferred fields (chart → D1's boxChart; keys → parameter + `KeysLawful` proved by U1; hm/hN → unit hypotheses); SEED-EXIST stated ONCE, in U15's reprOf form | D5, §2 Wall B, U13/U15 |
| GAP-6: POL-PIN nominal drift vs MovesD's row; units named P-1/P-3 in hypothesis_fields | GAP | polOM named under the offset-P policy (spec-realized; sign-off inline at D2 — the ratification's condition discharged; wave-4 copy registered at §7.6); hypothesis_fields renamed to `StageTransHyp`/`OmUniqHyp` | D2, §7.6, U17a/U18/U26 |
| GAP-7: U13 claimed 25 `JetSetup` fields (round 6 has 29); §7.1's "first" readable as prove-first; `ZCSeedLaws` line-check not yet dischargeable | GAP | 29 corrected; elaborate-not-prove-first reading note added; the line-check recorded as a STANDING E-phase obligation | U13, §7.1, D5/§7.3 |
| RULING 1: §2.1 `mkStratum := fresh` | RATIFIED | recorded inline; U8 stays `Iff.rfl`-easy; no inherited carrier demanded | §2.1 |
| RULING 2: D2 `polOM` (choice-realizer of the offset-P spec) | RATIFIED (condition: GAP-6) | recorded inline; condition discharged by the D2 sign-off + the §7.6 registration | D2 |

Census: 45 (rev 1) → **48** (rev 2): +D8 (easy), +U1b (medium), +U31 (medium).

— end of blueprint (REV 2). Next: the acceptance pass — a fresh verifier on this
file (perimeter: §3 + the seven gap sites + the two inline ratification
records), then the A-round; the Codex leg batched post-reset per §7.5.
