-- ⚠ THIS FILE DELIBERATELY DOES **NOT** `import Uniformity` — see defect I-D1 in the header.
-- The list below is `leanfinal/Uniformity.lean`'s own import list MINUS `Uniformity.ChapD`
-- (the roll-up), PLUS the two chapter-E modules chapter I's Display-A `ladder` field consumes.
-- Importing the roll-up and the E-side deep-twist branch TOGETHER is a hard Lean error at HEAD.
import Uniformity.Basic
import Uniformity.HenselFactorization
import Uniformity.MultiHensel
import Uniformity.StrongHensel
import Uniformity.Quarry
import Uniformity.Density.LocalData
import Uniformity.Density.CensusGen
import Uniformity.Density.Transport
import Uniformity.Density.TypeOf
import Uniformity.Density.TypePositivity
import Uniformity.Density.InertLeaf
import Uniformity.Density.TypeOfAlgebra
import Uniformity.Density.TypeOfInvariance
import Uniformity.Density.ScaleExtraction
import Uniformity.Density.NormLeaves
import Uniformity.Density.GenuineDensity
import Uniformity.Density.CoveringMenus
import Uniformity.Density.QuadCert
import Uniformity.Density.AnisotropicForms
import Uniformity.Density.Statement
import Uniformity.Density.Gates
import Uniformity.Density.Drainage
import Uniformity.Density.DensityAPI
import Uniformity.Density.TypeOfFaithful
import Uniformity.Density.TypeOfFaithfulInert
import Uniformity.ChapG
import Uniformity.ChapG.G78
import Uniformity.ChapH
import Uniformity.ChapB
import Uniformity.ChapB.B86
import Uniformity.ChapE
import Uniformity.ChapE.E24
import Uniformity.ChapE.E63
import Uniformity.ChapI.I10FreezeV2 -- [A-I.2] F3's typed freeze-v2 carriers (DeepTwistConjunctLive)
import Uniformity.ChapI.I10LadderLive -- [A-I.6] the live-range ladder record (the `ladder` field's rebind target)
import Uniformity.ChapI.I10RecenterLive -- [A-I.7] the recenter-step export surface + the live-MP1 record (the `ladder` field's rebind target)
import Uniformity.ChapC
import Uniformity.ChapC.C130sg -- [A-I.3] the SG-1 socket-application instances (the §4 gate's non-vacuity teeth)
import Uniformity.ChapF

/-!
# Chapter I — CAPSTONE AND CONDITIONALITY: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-I_capstone_conditionality.md` (25 nodes I.01–I.25 — the
Display-A hypothesis block, the conditionality ledger, and the assembly toward
`UniformityStatement`), landed in the isolated `leanspec` environment **before** the chapter-I
fleet fires, in the blueprint's node order.

**STATE (2026-08-16, after AMENDMENT A-I.1): OPEN, AND THE CAPSTONE HYPOTHESIS BLOCK IS
CONTRADICTORY UNTIL CHAPTER C TYPES TWO SOCKETS (defect I-D13, machine-shown in the §4 gate).**
The 0e gate signed I.10 with Display-A carrier fields quantified over ALL configurations; the
A-E.2/A-D.2 carriers are certified FALSE at concrete legal instances, so
`CapstoneHypotheses n` is UNINHABITED and I.15–I.18 fire from a contradiction. A-I.1 re-signs
the two ladder fields at the ARISING configurations (NODES I.10a/I.10b — sockets whose bodies
are owed at chapter C's freeze), which is the shape that becomes honest the moment those bodies
land; it does NOT repair the contradiction today, and says so with a machine witness. I.10
remains an ELABORATION GATE, not a signature (defect I-D7's verdict, upheld): **no fleet agent
may fire on I.10.**

**STATE UPDATE (2026-08-26, AMENDMENT A-I.3): CHAPTER C HAS TYPED THE TWO SOCKETS, AND THE
I-D13 CONTRADICTION IS LIFTED.** The packaging enactment (`runs/wave-b/verdict_PK12.md`;
`docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` §4.4) landed the intended I.10a/I.10b bodies
as chapter-C data-carriers — `Uniformity.Density.Tower.C130s18.CanonicalLadderConfigData` /
`.CanonicalDeepTwistConfigData` (the `∃ (E : Type uE) (fE : Field E) … ChainRealization …
(fieldE := fE)` shapes over the PK-1-retyped split-node carrier, with the CC-12 view pins) —
and this amendment re-signs the two socket BODIES at exactly those carriers (ONLY the two
bodies change; `CapstoneHypotheses`' field list, `UniformityStatement`, and I.15–I.18's
statements are byte-unchanged). Consequences, machine-run in the §4 gate: the old item (10)
(`¬ CapstoneHypotheses n` from one certified-false `(C, B)` through a `trivial` socket
certificate) NO LONGER ELABORATES and is struck with its text preserved — the block is no
longer provably empty by the I-D13 route; the old item (11) equivalence (guarded = unguarded)
is retired to its surviving weakening direction — **the owner-gate-(a) narrowing event A-I.1
flagged in advance has now HAPPENED** (the fields are demanded at the arising configurations
only); and the sockets are certified NON-VACUOUSLY INHABITABLE at the S2 instance (new teeth
(16)/(17): `C130sg.s2Frontier_ladder_socket`/`s2Frontier_deepTwist_socket`, conditional on
exactly `w : S2LevelOneThreshold` + `IsAdicComplete`). The block is NOT thereby inhabited —
`a0`/`a1` stay open at `n ≥ 3`, the guarded fields still demand supply at the arising
configurations, and the `jd0`/`genhnBox2`/`w1` debts and five I-D12 placeholders are untouched.

**STATE UPDATE (2026-08-27, AMENDMENT A-I.4): I.01'S SIGNED BODY IS RECONCILED WITH THE
LANDED A-C.6 REDRAFT.** C.94 has declared the allowlisted cite
`Uniformity.Density.Tower.agnprw_termination : NS7TerminationStatementR`, and landed I.01 has
already consumed it through `ns7Termination_of_cite`. This amendment replaces ONLY
`NS7Termination`'s literal `True` matrix by the byte-shaped redrafted descent assertion; the
name, bundle quantifier, and `Prop` kind are unchanged, and every other signed declaration is
byte-unchanged. Gate item (14) now pins the body definitionally to
`Tower.NS7TerminationStatementR` and re-elaborates the `CapstoneHypotheses.ns7` projection.

**STATE UPDATE (2026-08-27, AMENDMENT A-I.5): THE GC-13 WIRING LAW IS SIGNED (NEW NODES
I.10c/I.10d), AND THE DT0 GentowW DEMAND IS AMENDED TO THE WIRED SITEWISE FORM.**  Per
`docs/in-progress/GC13_WIRING_2026-08-27.md`'s `[GCW-0]` decision record (print-read
`runs/wave-b/verdict_GCW0.md`) and the orchestrator's F2=P2 adjudication, this amendment ADDS
two declarations and changes NO existing statement: `GC13Wiring` (I.10c — the sitewise
read/normalizer dictionary at the abstract D.44 surface, GCW-0's record verbatim) and
`WiredGentowDemand` (I.10d — the per-level `deepTwist`-route demand: the law AND D.44's
`GentowW` at the same read; a STRENGTHENING of the flat per-level conclusion).  The signed
socket `CanonicalDeepTwistConfig` and `CapstoneHypotheses`' field list are BYTE-UNCHANGED
(the guard-extension fork was REJECTED: it would couple the law into chapter C's signed
socket).  Basis: the wiring is a missing source-faithful LAW, not a missing proof — FGCW's
underdetermination certificates (`IFC2.s2_hread_refuted_at_landed_exports`, the landed
witness's own zero read refutes the identification; `IFC2.s2_gentowW_of_read_one`, ⚠ the
D-D12-FENCED freedom half, NOT SUPPLY).  Leanfinal twins + the μ₃ consumption route:
`Uniformity/ChapI/IFC3.lean` (byte-identical binder blocks).  The UNIVERSAL wired supplier is
deliberately NOT signed — BLOCKED-BECAUSE: no landed per-level calculus/receiver exporter
(the `WleCleared` truncation exporter); every site-quantified form is defective today, anchored
on the `f' = 0` vacuity fence (see NODE I.10c's gate examples).  Parallel VAUD finding
(`runs/wave-b/verdict_VAUD.md`): E.24's `vartheta` range needs live-index restriction bound to
the same witness — PROPOSED, owner-gated, NOT enacted here; `IFC0.lean` untouched by both units.

**STATE UPDATE (2026-08-28, LVT ENACTMENT RECORD — comment-level only: NO signed statement,
declaration, gate, or count changes):** THE VAUD LIVE-RANGE LADDER SHAPES ARE LANDED AS
SUPERSESSION TWINS in `leanfinal` (`Uniformity/ChapI/IFC5.lean`: `CanonicalLadderLiveAt`,
`LadderVarthetaSupplierLive`, `LadderSupplyLive`, `LadderFieldLive`,
`ladderFieldLive_iff_suppliers`, `ladderFieldLive_of_suppliers`, plus two supersession-direction
pins showing the old targets imply the new — the amendment only RESTRICTS the demanded range).
Basis, machine-certified (`leanfinal/scratch/VAUD_probe.lean`, all Lean-core, exit 0):
`gauge_view_offRange_kernel_replacement` (the I.10a socket's `GaugeFamilyViewEq` is invariant
under arbitrary dependent `(v, ρ)` and `q` replacement at every non-`GaugeLive` index),
`vartheta_sitewise_negative` (a concrete FALSE sitewise `HVarthetaRes`), and
`s2_three_not_gaugeLive` (the landed depth-2 S2 socket's first demanded index `3` is already off
range) — so E.24's unbounded `vartheta` range (`∀ i ≥ 3`), which the signed I.10 `ladder` field
consumes through `LadderSupply`, is NOT derivable from the I.10a guard; an HVR-shaped guard
premise stays FORBIDDEN (the D.62 trap fence).  Per the A-I.5 coordination rule, `IFC0.lean` and
every signed declaration HERE are BYTE-UNCHANGED: the unbounded form stays as the tension record
(the GCW-6 pattern; retired as a campaign target), and the live-restricted `IFC5.LadderFieldLive`
is the campaign target.  Rebinding `CapstoneHypotheses.ladder` to `LadderSupplyLive` (or moving
the live record into E.24) remains OWNER-GATED and would be a numbered amendment (A-I.6) — NOT
enacted.

**STATE UPDATE (2026-08-28, AMENDMENT A-I.6): THE `ladder` FIELD IS REBOUND TO THE LIVE-RANGE
RECORD — A STATEMENT CHANGE, MACHINE-FORCED.**  The rider route the LVT record above held open
is CLOSED BY REFUTATION: `leanfinal/scratch/AI6_probe.lean` (Lean-core, exit 0, orchestrator
re-verified; adjudication `runs/wave-c/verdict_AI6.md`) proves

* `AI6Probe.ladderField_four_refuted : ¬ IFC0.LadderField 4`
* `AI6Probe.capstoneHypotheses_four_refuted : ¬ CapstoneHypotheses 4`

— VAUD's teeth assemble INSIDE the field's own quantification at the landed degree-4 S2 socket
(the off-range index `3` replaced by junk data whose ambient residue `X⁻¹` is no `K2`-unit
image), so the signed block's bytes were machine-EMPTY at degree 4 and an interpretive rider is
IMPOSSIBLE — the A-I.5 rider precedent requires the signed field to remain inhabitable in
principle.  The pre-rebind refutation (stated against the then-live structure) is archived at
commit `ce301df1`; after this amendment the probe's `capstoneHypotheses_four_refuted` is pinned
to a local RETIRED-RECORD verbatim copy (`AI6Probe.CapstoneHypothesesUnbounded`) and
`ladderField_four_refuted` still compiles against byte-frozen `IFC0.LadderField`.

THE EXACT REBINDING: the `ladder` field's result record
`Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q` is replaced by
`Uniformity.Density.IFC5.LadderSupplyLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n` — the first
three record fields (`package`/`lb1`/`mp1`) are byte-identical to E.24's; ONLY the `vartheta`
leg gains the `CanonicalLadderLiveAt` premise (demanded only at indices live in a realization
witnessing the SAME socket data).  To keep the import order acyclic the two live declarations
(`CanonicalLadderLiveAt`, `LadderSupplyLive`) are MOVED byte-for-byte from
`Uniformity/ChapI/IFC5.lean` to the new `Uniformity/ChapI/I10LadderLive.lean` (namespace
`Uniformity.Density.IFC5` unchanged), which I.10 now imports here and in `leanfinal`.  This
weakens a hypothesis and therefore STRENGTHENS the conditional capstone; the field list and
I.15–I.18's statements are BYTE-UNCHANGED.  `IFC0.LadderField`/`LadderVarthetaSupplier` and
their exact split stay byte-frozen as the refuted tension record.  Gate change: item (4) ALONE
(the sitewise-ϑ consumption now costs the live-index certificate); items (2)/(3) are unchanged
because the first three fields are byte-identical.  Review: `docs/REVIEW_QUEUE_2026-08-26.md`,
Tier 1 row A-I.6 (capstone-surface amendment).

**STATE UPDATE (2026-08-28, AMENDMENT A-I.7): THE `ladder` FIELD'S `mp1` LEG IS REBOUND TO THE
SAME-REALIZATION LIVE CARRIER — A STATEMENT CHANGE, MACHINE-FORCED.**  A-I.6's record was
refuted through its remaining unrestricted leg: `leanfinal/scratch/REX_probe.lean` (Lean-core,
exit 0, orchestrator re-verified pre-enactment; adjudication `runs/wave-c/verdict_REX.md`)
proves

* `REXProbe.s2_unrestricted_mp1_false : ¬ Ladder.MP1Carrier C2 B2`
* `REXProbe.s2_ladderSupplyLive_false : ¬ IFC5.LadderSupplyLive C2 B2 … 4`
* `REXProbe.capstoneHypotheses_four_refuted_via_mp1 : ¬ CapstoneHypotheses 4`

— `IFC5.LadderSupplyLive.mp1` still demanded the UNRESTRICTED `Ladder.MP1Carrier`, and the
landed degree-4 S2 producer's own data (`B2.μ = 1`, `B2.F = B2.Φ + 1`) admit `Λ = −1` with the
legal successor `B2'.Φ = B2.F`, whose demanded `MidPeelEmission` quotient is degree-impossible
at the length-one parent (`hmass` forces `deg quot.F + D = D` against `D > 0`).  So the signed
block's bytes were machine-EMPTY at degree 4 AGAIN and an interpretive rider is IMPOSSIBLE (the
A-I.5/A-I.6 precedent).  The pre-rebind refutation (stated against the then-live structure) is
archived at commit `05f067b7`; after this amendment the probe's
`capstoneHypotheses_four_refuted_via_mp1` is pinned to a local RETIRED-RECORD verbatim copy
(`REXProbe.CapstoneHypothesesUnrestrictedMP1`) and `s2_ladderSupplyLive_false` still compiles
against byte-frozen `IFC5.LadderSupplyLive`.

THE EXACT REBINDING: the `ladder` field's result record
`Uniformity.Density.IFC5.LadderSupplyLive.{uW, uG, uKt, uL} C B G Kt L N v ρ q n` is replaced
by `Uniformity.Density.IFC5.LadderSupplyLive₂.{uW, uG, uKt, uL} C B G Kt L N v ρ q n`
(NEW `leanfinal/Uniformity/ChapI/I10RecenterLive.lean`, namespace `Uniformity.Density.IFC5`,
imported here and in `leanfinal`; acyclic: `I10_I15_I18 → I10RecenterLive → I10LadderLive`) —
the `package`/`lb1` fields byte-identical to E.24's, the `vartheta` field byte-identical to
A-I.6's live field; ONLY the `mp1` leg is replaced by the same-realization
`IFC5.MP1CarrierLive`: the `Nonempty (MidPeelEmission B B')` conclusion is demanded only at
successors `B'` exported by an `IFC5.RecenterStep` — ONE existential witness carrying the SAME
slot/block/gauge-family views as the socket, the GN15-Thm-2.3 payload (`IFC5.GNCitePayload`, a
STATEMENT CARRIER one-to-one with the source's exact hypothesis list, residual multiplicity
one spelled `residual = psi * residualQuot` + `¬ psi ∣ residualQuot`; NO cite consumed) for
the exact key `B'.Φ`, and the peel core (`IFC5.MP1StepCore` = `MidPeelEmission` items 2–4,
neither `hirr` nor `hef`).  The four export-surface declarations are PROMOTED byte-for-byte
from `scratch/REX_probe.lean` (machine byte-diff: `runs/wave-c/verdict_AI7E.md`); supersession
pins `mp1CarrierLive_of_mp1` / `ladderSupplyLive₂_of_live` prove OLD ⟹ NEW (restriction only
— the converse is exactly what REX refuted).  This weakens a hypothesis and therefore
STRENGTHENS the conditional capstone; the field list and I.15–I.18's statements are
BYTE-UNCHANGED.  `LadderSupplyLive` stays byte-frozen in `I10LadderLive.lean` as the refuted
tension record; E.40's `MP1Carrier` byte-frozen likewise.  Gate change: item (3) ALONE (the
MP1 consumption now costs the recenter-step export `hstep`); items (2)/(4) are unchanged.
The S2-instance export construction is landed as far as the producer data allows
(`I10RecenterLiveS2.lean`: `S2LandedPrefix` + `s2LandedPrefix_tangentClass_impossible`); the
remaining GAP rows of REX's cite mapping table are the NAMED OPEN `S2-RECENTER-EXPORT`
(`docs/in-progress/LADDER_SUPPLY_2026-08-27.md`, [AI7E] entry).  Review:
`docs/REVIEW_QUEUE_2026-08-26.md`, Tier 1 row A-I.7 (capstone-surface amendment).

Since 2026-08-20 the definitional layer I.01–I.03/I.05–I.07/I.21 IS landed in `leanfinal`
(`Uniformity/ChapI/I01.lean` … `I21.lean`, byte-frozen transcriptions), and A-I.3's Stage-2
companion lands I.10a/I.10b + I.10 + I.15–I.18 there (`Uniformity/ChapI/I10_I15_I18.lean`) at
the amended bodies; the 2026-08-16 "nothing landed" paragraph below is the historical record.

Chapter I has landed nothing in `leanfinal` (`grep` for `CapstoneHypotheses` /
`DecidedSliceAt` / `MenuLawAt` / `TypeOfFaithful` as a `Prop`-carrier over `leanfinal/Uniformity/`:
zero hits), so nothing here is in the retirement state of `Leanspec.lean`'s stub lifecycle.

**Wrapper choice, declared per GC-6.6:** wrapper `namespace LeanspecI`, which the blueprint's §11
instructs directly ("stubs wrap in `namespace LeanspecI`, one file `leanspec/Leanspec/ChapI.lean`
… whichever the stub agent picks, say so in the file header"). Consequently the blueprint's
`namespace Uniformity.Density` headers in the SIGNATURE blocks are DROPPED here and every
declaration is flat inside `LeanspecI`; the landed-side namespace assignment (GC-6.2 gives
chapter I **no** sub-namespace — every I declaration lands in `Uniformity.Density` directly) is
what the fleet must land.

**This file is never imported by `leanfinal` or `leancheck`.** It is an interface contract, not
mathematics. `sorry` and `native_decide` appear nowhere; the file elaborates with
`autoImplicit`/`relaxedAutoImplicit` **off**.

## HONESTY, CARRIED FROM THE BLUEPRINT'S §1 (read before consuming anything here)

* **I-1.** Nothing in this chapter proves the capstone. `uniformity_of_capstoneHypotheses`
  (I.17) is bookkeeping: it says `UniformityStatement` follows from the frozen Display-A block
  and nothing else. The honest headline stays *"proved unconditionally at `n = 1` and `n = 2`;
  at every `n ≥ 3` stated with its complete named conditionality."*
* **I-2 (the GENIND.B fence).** No node here composes `InductionPackage n` at `n ≥ 4`.
* **I-4.** `TotalMassOne` is the drainage leg in disguise — I.18 derives it from the `a2` fields
  through landed `totalMassOne_of_drainage`; it gets no field of its own.
* **I-7.** The WELD-ZERO arc licenses nothing: `HYP.148` stays CARRY and `HYP.139` stays MATH at
  full strength.
* **OM-9's `w1` note, carried (the charge's standing instruction).** F.12's landed `W1Transport`
  is the transport's **SIGNATURE**: `w1Transport_iff_zero_iff` (F12w) proves the carrier is
  equivalent to equality of vanishing loci, and `w1Transport_of_ne_zero` makes any instantiation
  at nonvanishing families FORMALLY TRIVIAL. **A typed `w1` field discharges NOTHING of HYP.139**
  (whose MATH content is TR-3′-GEN's compatible dictionary at general order). See defect I-D8:
  in I.10's signed field list there is no `w1` field for the note to ride on.

## THE `LB1 ∧ MP1` AND `(H-VARTHETA-RES) ∧ 𝒲` CONSUMPTION RULES (I.10's dated note, binding)

Two Display-A carriers were machine-refuted VACUOUS as committed and re-signed; this file
consumes the re-signed forms ONLY, against the LANDED declarations:

1. **`LB1 ∧ MP1`** at the **A-E.2 forms** — landed `Uniformity.Density.Ladder.LB1Carrier`
   (`ChapE/E39.lean`, concluding `Nonempty (BlockSuite I)` at E.39a's full S1.7A record) and
   `…MP1Carrier` (`ChapE/E40.lean`, concluding `Nonempty (MidPeelEmission B B')`), reached
   through E.24's `LadderSupply` and consumed **universe-polymorphically in `uW`** (honesty
   E-12: `uW` is the `(SEC-RANK)` rank carrier's universe, which occurs only inside the `Prop`).
   `CapstoneHypotheses` below is therefore universe-polymorphic — `CapstoneHypotheses.{uW, uG,
   uKt, uL}` — which is the only reading Lean admits (a `Prop` cannot quantify over universes).
   The voided shadows `OM4Shadow.LB1CarrierVoided`/`MP1CarrierVoided`/`LadderObligationsVoided`
   (`verification/om4_shadow_vacuity.lean`) are FENCED: nothing here cites them.
2. **`(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}`** at the **A-D.2 form** — chapter D's SITEWISE
   `Uniformity.Density.Gauge.HVarthetaRes G K L N (v i) (ρ i) (q i)` against the level's GIVEN
   ambient residue datum, reached through E.61's typed socket `Ladder.VarthetaRes` inside E.24's
   `vartheta` field. The voided existential `HVarthetaResVoided` is FENCED. **[A-I.1, defect
   I-D4 CURED] the `𝒲` half now has its own field**: `deepTwist`, consuming landed E.63's
   `Ladder.DeepTwistConjunct` — BOTH halves at the typed E.61/E.62 sockets, one use-height
   family `q` serving both (E.63's own fence against splitting them). The ϑ-half is consequently
   carried twice, at the same level data; the redundancy is harmless and the field-level source
   of truth for the `∀ i ≥ 3` conjunct is `deepTwist`.
3. **[A-I.1, defects I-D3/I-D13] BOTH ladder fields are consumed only AT AN ARISING
   CONFIGURATION** — `CanonicalLadderConfig` (I.10a) / `CanonicalDeepTwistConfig` (I.10b), the
   sockets that pin the block `(C, B)` to chapter C's OM ladder and `ρ` to its canonical
   node-point residue read. Consuming either field therefore costs a configuration certificate,
   which is the honest price: without it the field is refutable, not merely open.

## THE SIGN-OFF COROLLARY (CONVENTIONS Part V, carried)

Two owner gates only: (a) the main Lean statement; (b) every literature cite, signed per cite.
**Every hypothesis on the capstone path must terminate as a DISCHARGE NODE or a gate-(b)
LITERATURE CITE — no third category.** Gate-(b) state at composition, transcribed:

| cite | statement artifact | state |
|---|---|---|
| B.42 `[cite:GN15 Thm 2.3 + FGMN Thm 6.6]` | `LeanspecB.exists_slope_factorization` | **landed-signed** |
| C.66 `[cite:FGMN]` | `LeanspecC.FgmnResidualMulStatement` | **REDRAFTED (A-C.6, commit `958cc39b`), awaiting owner signature** |
| C.94 `[cite:AGNPRW Thm 5.6]` | `LeanspecC.NS7TerminationStatementR` over `DescentStepR` | **REDRAFTED (A-C.6), awaiting owner signature**; the A-C.1 draft is MACHINE-REFUTED (defect I-D6) |
| C.92 `[cite:FGMN-chain]` | — | **axiom RETIRED to hypothesis-form (A-C.6 DECISION option (1)); C.92 EXITS the gate-(b) queue** |

Consequences carried into this file: I.01's `ns7` field is **cite-conditional on the C.94
REDRAFT**, not on the struck A-C.1 draft (I-D6); and no I.10 field, and no I.24/I.25 registry
row, consumes C.92's withdrawn `fgmn_calculus_exists` (defect I-D11 records what that costs).

## Census (mechanical, over this file)

| kind | count | note |
|---|---:|---|
| `def` of blueprint declarations (real bodies, stage-0e rule 1) | **9** | `NS7Termination` (I.01), `DecidedSliceAt` (I.02), `MenuLawAt` (I.03, RE-SIGNED at A-I.1), `WindowPinningAt` (I.05), `GenhnHEAt` (I.06), `GenhnTow1At` (I.07), `TypeOfFaithful` (I.21), **+ A-I.1's two sockets** `CanonicalLadderConfig` (I.10a), `CanonicalDeepTwistConfig` (I.10b) **[A-I.5, 2026-08-27: +1 — `WiredGentowDemand` (I.10d), count now 10]** |
| `def` NAMED-AND-VOIDED (refutation record, cite-forbidden) | **1** | `MenuLawAtVoided` — I.03's pre-A-I.1 form, kept so its vacuity proof survives verbatim |
| `structure` (real body) | **1** | `CapstoneHypotheses` (I.10) — ⚠ an ELABORATION GATE, not a signature (defects I-D7, I-D13) **[A-I.5, 2026-08-27: +1 — `GC13Wiring` (I.10c), count now 2]** |
| `theorem` landed REAL (blueprint §11: "I.15–I.18 … land REAL, not axiom") | **4** | I.15–I.18 ⚠ ~~conditionally VACUOUS today: their hypothesis is uninhabited until the I.10a/I.10b sockets are typed (defect I-D13)~~ **[A-I.3, 2026-08-26: the sockets ARE typed and the I-D13 refutation route is closed — the hypothesis is no longer provably empty; it is OPEN (not claimed inhabited: `a0`/`a1` open at `n ≥ 3`, supply at arising configurations open)]** |
| `axiom` stubs | **0** | chapter I signs no theorem it cannot prove at stub time; the file's ONE `axiom` is I.25's fenced, `private`, `True`-valued positive control for the AXCHK guard, consumed by nothing |
| gate `example`s / `#check`, ALL EXECUTED | **33 `example` + 8 `#check`** [A-I.3: item (10) struck (−1), item (11) retired to its surviving direction (±0), items (15)–(17) added (+4)] [A-I.5: items (18)–(20) added at NODE I.10c/I.10d (+3, examples now 36)] | §4 gate (14 checks at A-I.1, five of them A-I.1's certifications; A-I.3 strikes (10), retires (11), adds the two `Iff.rfl` body pins (15) and the two S2 non-vacuity teeth (16)/(17)) · §6 gate (the `Iff.rfl` slice pin + the I.19 package-route `#check`s) · I.23 (the `q = 2`/`q = 3` anchors, the `e·f = 2` non-applicability proof, the two `n = 2` non-vacuity witnesses — `MenuLawAt 2` now at a REAL three-cell family) |
| gate-local `private def` (not a blueprint declaration) | **1** | `a1LabelCell` — the σ-labelled `A1Cell 0` used by the re-signed `MenuLawAt 2` witness |
| `[note]` nodes with no Lean file (blueprint §0.2) | **8** | I.04, I.11, I.12, I.13, I.14, I.19, I.20, I.22 — transcribed as docstring sections, nothing declared |
| ENFORCED AXCHK guards (`#axiom_core`, I.24/I.25) | **70** [A-I.5: +2 (`GC13Wiring`, `WiredGentowDemand`), now 72] | each one FAILS THE BUILD on a non-core footprint; two `elab` commands (`#axiom_core`, `#axiom_reg`) implement them |

**14 signed blueprint declarations** (9 `def` + 1 `structure` + 4 `theorem`) — the blueprint's
own file list (I01–I03, I05–I07, I10, I15–I18, I21, I23–I25 = 15 files; I.23–I.25 are gate files
carrying no declaration) **plus AMENDMENT A-I.1's two new socket nodes I.10a/I.10b**.

## Gate order (GC-6.6(c)) as actually run

(a) the fragile signatures first — I.10's `ladder` field (the six-universe E.24 application),
I.03's `A1Family` membership, I.02's literal-slice body, I.16's `exact`-closes-the-slice proof;
(b) the `def` bodies, real; (c) the §8 numeric gates EXECUTED at `q = 2` AND `q = 3`; (d) the
`axiom` stubs — none.

## THE DEFECT LIST (stage-0e gate, 2026-08-16) — WITH AMENDMENT A-I.1's DISPOSITIONS

Recorded here and in the 0e report; the blueprint-side ones are now ADJUDICATED AND SIGNED by
**AMENDMENT A-I.1** (`blueprint/CHAP-I_capstone_conditionality.md`, dated block at the end),
which is the versioned dated append CHAP-H §15 rule 5 asks for; this file then carries the
signed forms. Every stub-side adjustment is listed; nothing was adjusted silently.

| defect | A-I.1 disposition |
|---|---|
| I-D1, I-D2 | out of scope here — `leanfinal`-side (duplicate declarations, roll-up gaps), cured separately |
| **I-D3** | **RE-SIGNED**: repaired E.24 application + the arising-configuration binding (sockets I.10a/I.10b) |
| **I-D4** | **CURED**: new `deepTwist` field at E.63's `DeepTwistConjunct` (both halves); §12 rider-(iii) and I.20's S3 row struck-and-corrected in the blueprint |
| **I-D5** | **SIGNED**: the `@id (List (A1Cell r))` spelling is the blueprint form (reverts if H.93 lands an `abbrev`/instance) |
| **I-D6** | **RE-POINTED**: the A-C.1 instruction struck at both blueprint sites; the live target is the A-C.6 REDRAFT `LeanspecC.NS7TerminationStatementR`, owner gate-(b) pending |
| **I-D7, I-D8** | **RULED, not signed**: the weld carriers' `∀`-over-all-sites shapes are REFUTABLE (gate item (13)), so the placeholders stay and L-1/L-2's trigger is re-pointed at a weld site-supply socket; the missing `w1` field is a NAMED DEBT |
| **I-D9** | **RE-SIGNED**: the two-directional σ-label enumeration, with the old form voided and its refutation preserved |
| I-D10, I-D11, I-D12 | unchanged (recorded; not this amendment's scope) |
| **I-D13 (NEW)** | the finding A-I.1 was written around: the Display-A carrier fields as signed are **REFUTABLE**, so the block is contradictory — see the entry below |

* **I-D1 — STOP-THE-LINE, a `leanfinal` DUPLICATE-DECLARATION defect: `Uniformity.Density.Gauge.Wle`
  and `…VarthetaWConjunct` are each declared by TWO modules, which therefore cannot be imported
  together.** `Uniformity/ChapD/D55.lean:103` (`Wle`) + `D63.lean:144` (`VarthetaWConjunct`)
  versus `Uniformity/ChapD/D62w.lean:369` + `:412` — D62w re-declares both "byte-matching the
  leanspec carrier" in its own module rather than importing them. `Uniformity/ChapD.lean` (the
  roll-up, hence `Uniformity`) carries **D62w**; every chapter-E deep-twist module (E.61, E.62,
  E.63, and E.24 through E.61) imports **D63 → D55**. So
  `import Uniformity` + `import Uniformity.ChapE.E24` is a hard error:
  `import Uniformity.ChapD.D55 failed, environment already contains 'Uniformity.Density.Gauge.Wle'
  from Uniformity.ChapD.D62w`. *Class: duplicate landed declaration (a `leanfinal` defect, not a
  blueprint one) — footprint-visible and stop-the-line under the repo's axiom/interface policy.*
  **Stub-side workaround (the import block at the top of this file):** `Uniformity.lean`'s list
  MINUS `Uniformity.ChapD`, PLUS `Uniformity.ChapE.E24`/`E63`. The fleet CANNOT land chapter I in
  `leanfinal` until this is cured (a `leanfinal` I-node importing `Uniformity` and the E-side
  carriers is impossible at HEAD). Cure: delete D62w's two duplicate `def`s and have it import
  D55/D63 — mechanical, but it is an owner-visible `leanfinal` edit.
* **I-D2 — the chapter-E and chapter-F roll-ups do not carry the Display-A carrier modules.**
  `Uniformity/ChapE.lean` omits **E24, E39, E39a, E40, E44, E61, E62, E63** — every module the
  `ladder` field consumes; `Uniformity/ChapF.lean` stops at F13, omitting **F14–F28** (so F.28's
  `Weld.WeldObligations`, the weld layer's own handoff record to chapter I, is unreachable).
  Machine-checked from `import Uniformity`: `Ladder.LadderSupply`, `LB1Carrier`, `MP1Carrier`,
  `BlockSuite`, `MidPeelEmission`, `VarthetaRes`, `WFrame`, `DeepTwistConjunct` and
  `Weld.WeldObligations` are all `unknownIdentifier`. *Class: roll-up gap (same class as CHAP-F's
  recorded `ladderSigma_degree` note, but load-bearing here).* Note the ChapE half **cannot be
  cured before I-D1 is**: adding E24 to the roll-up would import D55 into `Uniformity` and break
  the package.
* **I-D3 — I.10's `ladder` field is UNDERAPPLIED BY EIGHT ARGUMENTS (hard error).** The blueprint
  signs `Ladder.LadderSupply C B`; landed E.24 is
  `LadderSupply (C) (B) (G) [CommGroup G] (Kt) [Field Kt] (L) [Field L] [Algebra Kt L]
  (N : NormSection G) (v) (ρ) (q)`. Verbatim, Lean reports `type expected, got
  (Ladder.LadderSupply C B : (G : Type ?u) → …)`. *Class: signature/landed-declaration arity
  mismatch.* **Stub-side repair:** the level data `(G, Kt, L, N, v, ρ, q)` is universally
  quantified inside the field, and the six universes are spelled
  `LadderSupply.{0, 0, uW, uG, uKt, uL}` (E-12). **The repair is honest but the resulting field
  is UNDISCHARGEABLE, and that is a second, mathematical finding:** OM-8's ρ-defeat (machine-shown
  at real tower exponents, `verification/om8_vartheta_deep.py` LEG D2) says *"typing E.61's socket
  at anything but chapter C's canonical residue data leaves the conjunct undischargeable"* — and
  a `∀ (ρ : ∀ j, ker (v j) →* Lˣ)` binder is exactly "arbitrary `ρ`". The blueprint's own ⚠
  QUANTIFIER DISCLOSURE chose the strongest uniform reading without the level data in view. The
  honest cure is an owner-gate-(a) field-list change binding the level data to chapter C's
  canonical instantiation; recorded, not taken.
  **[A-I.1 DISPOSITION: BOTH HALVES SIGNED.]** The repaired application is now the blueprint's
  own; the binding is NODE I.10a's socket (`CanonicalLadderConfig`), guarding the field. And the
  "undischargeable" reading was too kind — see I-D13: the field is FALSE. E.24's three recorded
  options are inherited (quantify = refutable; bundle existentially, equivalently thread as
  structure parameters and supply at I.17 = fabricable D-D12; bind = signed).
* **I-D4 — the `𝒲_{≤i}` half of Display A's `∀ i ≥ 3` conjunct (HYP.63) HAS NO FIELD.** I.10's
  STATEMENT says the `ladder` field packages "E.24's `LadderSupply`, which packages … the
  `∀ i ≥ 3` deep-twist carriers E.61/E.62". The LANDED E.24 packages **E.61 only**, and says so
  in its own docstring: *"E.62's `𝒲` leg is conjoined at chapter I, not here."* So as signed,
  chapter I carries `(H-VARTHETA-RES)_i` and silently DROPS `𝒲_{≤i}` — a Display-A conjunct with
  no carrier, which §12's rider-(iii) check ("nothing else on the frozen display lacks a
  carrier ✓") therefore mis-reports. *Class: missing field for a frozen conjunct.* No stub-side
  repair (field list frozen); the §4 gate elaborates landed `Ladder.DeepTwistConjunct` (E.63),
  which is the declaration that carries both halves at the typed sockets, so the fleet has the
  exact object to re-sign against.
  **[A-I.1 DISPOSITION: CURED.]** The `deepTwist` field is signed at exactly that object, guarded
  by I.10b; §12's rider-(iii) and NODE I.20's S3 row are struck-and-corrected in the blueprint
  (both were FALSE as written, and the S3 row carried a second falsity: it called I.17 an
  EQUIVALENCE, which it never was).
* **I-D5 — I.03's `∀ C ∈ F` does not elaborate: `A1Family` is a plain `def`, not an `abbrev`.**
  H.93 lands `def A1Family (r : ℕ) : Type := List (A1Cell r)`; instance search does not unfold
  plain `def`s, so `failed to synthesize Membership ?m (Induction.A1Family r)`, cascading into
  `Invalid field notation … cannot resolve field 'σ'`. A `(F : List (Induction.A1Cell r))`
  ascription does **not** cure it (ascription is transparent; `inferType F` still returns
  `A1Family r`). *Class: missing instance / wrong reducibility on a landed declaration.*
  **Stub-side repair:** `∀ C ∈ @id (List (Induction.A1Cell r)) F, …` — type-identical, since the
  two types are definitionally equal. Root-cause cure for the fleet: make H.93's `A1Family` an
  `abbrev`, or land a `Membership (A1Cell r) (A1Family r)` instance.
  **[A-I.1 DISPOSITION: SIGNED.]** The `@id` spelling is now the blueprint's own form for I.03
  (type-identical, so this is an elaboration repair and not a strength event); it reverts to the
  plain `∀ C ∈ F` verbatim if the root cure lands at H.93.
* **I-D6 — I.01's resolution instruction (the 2026-08-16 A-C.1 addendum) is STALE AND UNSAFE.**
  The addendum states *"the typed body is exactly `Uniformity.Density.Tower.NS7TerminationStatement`'s
  matrix … the orchestrator's stub-resolution pass may now type I.01's body — either
  `NS7Termination := NS7TerminationStatement` … "*. That draft was **MACHINE-REFUTED** at A-C.6:
  `leanfinal/Uniformity/ChapC/C94_REFUTATION.lean.txt` proves `NS7TerminationStatement → False`
  absolutely over `ℤ_[2]`, Lean-core and sorry-free. It is struck; the live artifact is
  `LeanspecC.NS7TerminationStatementR` over `DescentStepR` (commit `958cc39b`), still awaiting
  owner gate-(b) signature. Secondary: the name `Uniformity.Density.Tower.NS7TerminationStatement`
  **does not exist in `leanfinal` at HEAD** (only inside the `.lean.txt` refutation record and the
  `LeanspecC` draft), so the instruction is unexecutable as written as well as unsafe. *Class:
  stale blueprint instruction pointing at a refuted statement.* I.01 is landed here at its SIGNED
  `True` body, unresolved; **any fleet agent that follows the addendum lands `False`.**
  **[A-I.1 DISPOSITION: RE-POINTED.]** Both blueprint sites (NODE I.01's A-C.1 rider and the
  A-C.1 addendum's "I.01 UNBLOCKED" paragraph) are STRUCK with their text kept verbatim, and the
  signed instruction names the A-C.6 REDRAFT `LeanspecC.NS7TerminationStatementR` over
  `DescentStepR`, **cite-conditional on the owner's gate-(b) signature**: no pass may type I.01
  before that signature; on it, the registry entry is `agnprw_termination` at gate I.25.
* **I-D7 — I.10 is signed in a state its own blueprint FORBIDS, and the prohibition is now stale
  too.** §11's blocked table reads *"a signed I.10 stub with `True` fields is a false
  conditionality claim; forbidden"*, while I.10's own SIGNATURE block signs `jd0 : True` and
  `genhnBox2 : 6 ≤ n → True`. Since OM-9 (2026-08-16) the L-1/L-2 binding targets are LANDED —
  `Uniformity.Density.Weld.JD0Box2` (F.04), `.GenhnBox2` (F.11), `.W1Transport` (F.12) — so the
  placeholders are stale, not merely blocked. *Class: self-contradictory node state.*
  **This file lands the structure at the signed types as an ELABORATION GATE ONLY**, with the ⚠
  carried verbatim at the declaration and a gate-local `example` proving the L-1/L-2 typed shape
  elaborates against the landed carriers. **The stub is not a signature: no fleet agent may fire
  on I.10 until the owner re-signs the field list.**
  **[A-I.1 DISPOSITION: RULED — the prohibition STANDS, its blocker is RE-POINTED.]** The 0e
  reasoning ("the placeholders are stale, the targets are landed") does not survive: the
  consumption shapes gate item (6) exhibits quantify over ALL sites, and at least one of them is
  REFUTABLE (item (13): `¬ ∀ (K ι) (Rh RG), W1Transport Rh RG`, at `Fin 1`/`ZMod 3`), so binding
  the fields there would make the block contradictory a second time. L-1/L-2 must bind through a
  weld site-supply socket (the I.10a pattern); until then `jd0`/`genhnBox2` stay `True`.
* **I-D8 — the OM-9 `w1` honesty note has no field to attach to.** OM-9's instruction is that the
  `w1` conjunct field "should carry this note when bound". I.10's signed field list has **no `w1`
  field at all**: the W-1 sub-residue (HYP.139, MATH at full strength) rides inside the
  `genhnBox2 : 6 ≤ n → True` placeholder. F.28's landed `WeldObligations` carries three fields
  (`jd0box2`, `genhnBox2`, `w1`); I.10 carries one and a half. *Class: missing field for a carried
  ledger row.* The note is carried in this file's honesty block instead; no stub-side repair.
  **[A-I.1 DISPOSITION: REGISTERED AS A NAMED DEBT.]** The field is owed at L-2's re-pointed
  trigger (three fields, not two), and the OM-9 note travels with it verbatim. A-I.1 does not add
  it now for the reason in I-D7: the only shape available today is the refutable one.
* **I-D9 — I.03's `(A1)`-admissibility clause is VACUOUS as signed (machine-checked here).**
  `MenuLawAt n` existentially quantifies `(r, F, S)` and constrains `F` by `∀ C ∈ F, C.σ ∈ S`
  ONLY — one-directional, so `r = 0, F = []` satisfies it for **every** `S`. The §4 gate proves
  the equivalence outright: `MenuLawAt n ↔ ∃ S, (∀ σ ∈ S, σ.degree = n) ∧ ∀ O, CoveringMenu O n S`
  — i.e. the `A1Family` existential adds no strength whatsoever, and the carrier is the bare menu
  clause. This is the OM-4 FINDING-0 genre (a trivially satisfiable conjunct tracks no
  conditionality) and it is NOT what I.03's own ⚠ SIGNATURE NOTE discloses — that note discloses
  only the missing WEIGHT-correctness tie. *Class: vacuous carrier.* **No stub-side repair**
  (statements frozen). The evident re-sign is the reverse inclusion (`∀ σ ∈ S, ∃ C ∈ F, C.σ = σ`)
  plus H.94's closure predicate; that is an owner-gate-(a) event.
  **[A-I.1 DISPOSITION: RE-SIGNED at the enumeration — the clause is CONTENTFUL, not redundant.]**
  Adjudicated from the source: NODE I.03's STATEMENT says the cells' σ-labels *"enumerate `S`"*
  (two-directional), and ledger HYP.26 wants a family carrying the menu's labels — the ⊇ half was
  LOST, not absent by design. It is signed. H.94 turns out to supply a cell CALCULUS
  (`A1Cell.prod`, `A1Cell.deltaSubst`), not a closure predicate, so nothing further is bound.
  Certified per the A-E.2 standard in the gates: the old form's refutation preserved verbatim
  against `MenuLawAtVoided`; the empty family PROVED not to satisfy the new clause at a nonempty
  menu; `MenuLawAt 2` re-PROVED with a real three-cell labelled family; re-signed ⟹ voided.
  ⚠ The re-sign kills the VACUITY, not the disclosed gap: the WEIGHT-correctness tie stays open.
* **I-D10 — `a0` is over-demanded at `n = 0`.** `UniformityStatementDecided` guards its body with
  `0 < n`; `CapstoneHypotheses n`'s `a0 : DecidedSliceAt n` does not, so `∀ n, CapstoneHypotheses n`
  demands the decided-value law at degree 0, which the target never asks for. (`a2`'s `DrainageAt 0`
  IS genuinely required — landed `ofDecided` takes `∀ n, DrainageAt n`.) The `Iff.rfl` pin in §6's
  gate makes the exact relationship machine-visible: `UniformityStatementDecided ↔ ∀ n, 0 < n →
  DecidedSliceAt n`. *Class: hypothesis-side over-demand (harmless to soundness, dishonest to the
  open surface — it makes the block look one law bigger than Display A).* No stub-side repair.
* **I-D11 — I.25's expected registry is out of date by one entry, in the safe direction.** The
  node's SOURCE names "C.66/C.92's FGMN axiom group (one or two entries per the orchestrator's
  subsumption choice, §9.3 O-4)". A-C.6 DECISION option (1) **retired C.92's axiom outright**
  (`fgmn_calculus_exists` withdrawn; the class kept as a hypothesis carrier; "C.92 EXITS the
  gate-(b) queue"), so orchestrator item **O-4 is moot** and the expected registry is
  {C.94's `agnprw_termination` (at the REDRAFT `NS7TerminationStatementR`), C.66's FGMN axiom (at
  the REDRAFT `FgmnResidualMulStatement`), B.42's `[GN15]+[FGMN]` axiom}, with the OM-4/OM-5
  candidates (`recentered_key_emission`, `bBox1_cite`) queued. Also unlisted at I.25: the axiom
  `Uniformity.Density.Ladder`-side has none, but the C.92 route now depends on INSTANCE SUPPLY,
  which `#print axioms` cannot see — the gate's clause (ii) ("the conditionality is IN the axiom
  dependency") does not reach hypothesis-form cites. *Class: stale gate registry + a gate blind
  spot, both recorded.*
* **I-D12 — six SIGNED bodies are the literal placeholder `True`.** I.01, I.05, I.06, I.07, I.21
  and (as fields) I.10's `jd0`/`genhnBox2`. Every one is the blueprint's own
  BLOCKED-UNTIL-RESOLUTION state, and all six are landed here verbatim so the NAME, INDEX and
  `Prop` KIND are gated — but a reader must not mistake the elaboration for content. Blocker
  status at HEAD, re-checked at this gate: I.01 **unblocked-but-unsafe** (I-D6); I.05 **narrowed**
  (OM-6 landed `ChapH/H89w.lean`, 17 declarations, but `hwin` itself is undischarged); I.06
  **owner-assigned** (OM-7 landed `ChapH/H73w.lean`, so I.06's docstring line "transcription owner
  UNASSIGNED (orchestrator O-1)" is stale and is carried here corrected-by-annotation, not
  edited); I.07 **partially typed** (C.93's clause (i) `Tower.tower_first_live` is landed and
  reachable — `#check`ed in the §4 gate); I.21 **still blocked** (the maximal-order carrier does
  not exist in the tree). *Class: signed placeholders — an accounting fact, not an elaboration
  failure.*
* **I-D13 — NEW AT AMENDMENT A-I.1, STOP-THE-LINE: the Display-A carrier fields, read over ALL
  configurations, are REFUTABLE — so the capstone hypothesis block is CONTRADICTORY and I.15–I.18
  fire from `False`.** I-D3 called the `∀ ρ` reading *undischargeable*; it is worse than that.
  The A-E.2/A-D.2 re-signed carriers are machine-certified FALSE at concrete LEGAL instances —
  `lb1_resigned_not_trivial : ¬ LB1Carrier C₁ B₁` over a real `SlotCarrier ℤ ℚ` with
  `B₁.F = X² + X + 1`, `mp1_resigned_not_trivial : ¬ MP1Carrier C₂ B₂`,
  `hvarthetaRes_resigned_not_trivial` (all in `verification/om4_resign_nontriviality.lean`,
  RE-RUN at A-I.1: exit 0, Lean-core; its `LB1Carrier`/`BlockSuite` byte-identical to the landed
  ones modulo namespace, `RungInterface` differing only in universe-variable spelling) — and the
  field's binders range over exactly those instances.
  The §4 gate transports it: items (9)/(10) prove `¬ (the 0e ladder field type)` and
  `¬ CapstoneHypotheses n` from one certified-false `(C, B)`. *Class: contradictory hypothesis
  block (the OM-4 FINDING-0 genre with the sign flipped — FINDING 0 was a conjunct too weak to
  say anything, this is one too strong to be true).* **Cure (A-I.1's ruling): the fields are
  re-signed at the ARISING configurations (sockets I.10a/I.10b), and the contradiction lifts
  exactly when chapter C types those sockets — no edit in this file can do it.** Until then:
  no report may make a positive conditional claim from I.17, and no fleet agent may fire on I.10.

## What is real and what is a stub

Per stage-0e rule 1 the definitional layer lands as REAL BODIES (7 `def`s + 1 `structure`), and
per blueprint §11 the four assembly theorems I.15–I.18 land REAL as well — their proofs are
projections and one term application, all provable at stub time. **There is not one `axiom` STUB
in this file**, which is the chapter's design point: every open input to `UniformityStatement` is
a HYPOTHESIS of I.17, never an axiom, so I.17's own footprint is Lean-core — *enforced*, not
merely printed, at I.24. (The single `private axiom axchkSelfTestAxiom : True` at I.25 is the
AXCHK guard's positive control: `True`-valued, so it cannot weaken anything, and consumed by
nothing outside its own two commented self-test lines.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace LeanspecI

open Uniformity Uniformity.Density Polynomial IsLocalRing

/-! E.12's three universes plus E.61's threaded tower universes, bound explicitly (A-E.1/E-D6,
honesty E-12): `uW` occurs only inside the `ladder` field's `Prop`, so `CapstoneHypotheses` must
name it. This IS the "consume the carrier universe-polymorphically" instruction of E.39/E.24 in
the only form Lean admits — a `Prop` cannot quantify over universes, so the structure carries
them as parameters and every consumer records its choice. -/
universe uW uG uKt uL

/-! ## §4 — THE DISPLAY-A CARRIERS AND THE CAPSTONE HYPOTHESIS STRUCTURE (I.01–I.10)

Section contract, transcribed: one field per Display-A conjunct, at exactly ledger strength,
degree-indexed where the display is (`if n ≥ 6`, `if n ≥ 8`). Under Part V gate (a) the field
list of I.10 is capstone-conditionality state: **any field change (add, remove, restate) is
owner-gated**, including the removal WELD-ZERO would license (I-7). Carrier `def`s are `Prop`s;
none is proved; non-vacuity is this file's elaboration check plus the `n ≤ 2` conclusion gates
(I.23), never a claimed instance — a `Prop` structure's instantiability IS the open mathematics.
-/

/-! ### NODE I.01 [def] — `NS7(O)`, the termination hypothesis at exactly HYP.15's strength.
Lands `Uniformity.Density.NS7Termination`. ENV-I1.

~~⚠ **BLOCKED-UNTIL-RESOLUTION, and the published resolution route is REFUTED (defect I-D6).**
The signed body is the literal `True` placeholder; FROZEN are the name, the bundle quantifier
and the `Prop` kind. The live target is `LeanspecC.NS7TerminationStatementR`, awaiting the
owner's gate-(b) signature.~~

⛔ **RESOLVED AT AMENDMENT A-I.4 (2026-08-27): the BODY is TYPED at the landed A-C.6 redraft.**
C.94's allowlisted `agnprw_termination : Tower.NS7TerminationStatementR` is declared and
consumed by landed I.01. The refuted A-C.1 `NS7TerminationStatement` remains untouched. ONLY
this body's `True` matrix changes; the frozen name, bundle quantifier, and `Prop` kind are
byte-preserved. The §4 gate pins the replacement by `Iff.rfl`. -/

/-- `NS7(O)` (Display A line 1; ledger HYP.15, CARRY-as-CITE): OM descent terminates over every
complete DVR with finite residue field. Discharged by chapter C's gate-(b) cite C.94 ([AGNPRW]
**Thm 5.6**, published — the repo's "Thm 5.2" is the arXiv-v1 number, A-3 audit §3) once signed;
carried as a named `Prop` until then.

~~⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over chapter C's
descent-history type and asserts finiteness. FROZEN HERE: the name, the bundle quantifier, the
`Prop` kind.~~

**[A-I.4, 2026-08-27]** The body below is definitionally the A-C.6 redraft
`Tower.NS7TerminationStatementR` (and not the refuted `NS7TerminationStatement`). -/
def NS7Termination : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (π : O), Irreducible π →
    ∀ f : Polynomial O, f.Monic → Squarefree f →
    ∀ hist : ℕ → Uniformity.Density.Tower.DescentState O,
      (∀ n, (hist n).block ∣ f) →
      (∀ n, Uniformity.Density.Tower.DescentStepR π (hist n) (hist (n + 1))) → False

/-! ### NODE I.02 [def] — `A0_n`, the decided-value law at degree `n` (HYP.25's Lean-facing
slice). Lands `Uniformity.Density.DecidedSliceAt`. ENV-I1.

The body is the LITERAL slice of the landed `UniformityStatementDecided` (copied, not re-typed),
which is what makes I.16's one-line `exact` proof close. The `Iff.rfl` pin in §6's gate is the
standing machine check on that copy: it fails the build if either body drifts. -/

/-- `A0_n` (Display A; ledger HYP.25): the degree-`n` decided-value law — the degree-`n` slice of
`UniformityStatementDecided`. FAITHFULNESS (honesty I-6): the corpus states `(A0)` on the
`disc ≠ 0` locus; `decidedDensity` counts the every-lift decided classes (GC-9, the strictly
stronger read) — divergence recorded, not silently strengthened. -/
def DecidedSliceAt (n : ℕ) : Prop :=
  ∀ σ : FactorizationType, σ.degree = n →
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          decidedDensity O n σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

/-! ### NODE I.03 [def] — `A1_n`, the exact-core-menu law at degree `n` (HYP.26, at ledger
strength; COND:A1_n's resolution, I.13). Lands `Uniformity.Density.MenuLawAt`. ENV-I1.

**RE-SIGNED AT AMENDMENT A-I.1 (2026-08-16)** — defects I-D5 (the `@id` membership repair, now
the signed spelling) and I-D9 (the one-directional shape clause was PROVABLY VACUOUS; the
signed clause is the two-directional ENUMERATION the node's own STATEMENT always said —
*"whose cells' σ-labels enumerate `S`"*). The pre-A-I.1 form and its vacuity proof are
preserved verbatim below as `MenuLawAtVoided` (named-and-voided: no consumer may cite it). -/

/-- `A1_n` (Display A; ledger HYP.26; COND:A1_n's resolution — I.13): a q-independent
`(A1)`-admissible family list whose σ-labels ENUMERATE a covering menu at degree `n`. The shape
clause uses chapter H's landed `A1Family`/`A1Cell` (H.93, with W-12 r4's σ-label field).

⚠ SIGNATURE NOTE (blueprint's own, UNCHANGED by A-I.1): the exact-weights clause of HYP.26 is
carried by the `A1Cell.coeff` field plus the count laws (C.114/H §7) — this carrier states menu
+ shape + labels, and the WEIGHT-correctness tie stays OPEN-MATH (§3 rows HYP.23/32/35).
⚠ A-I.1 (I-D9): the second conjunct (`∀ σ ∈ S, ∃ C ∈ F, C.σ = σ`) is the half that was missing.
Without it `r = 0, F = []` satisfies the shape clause for EVERY `S` and the `A1Family`
existential is vacuous — proved in the gate below against `MenuLawAtVoided`, and the empty
family is proved NOT to satisfy the re-signed clause at a nonempty menu.
⚠ A-I.1 (I-D5): `∀ C ∈ F` is spelled `∀ C ∈ @id (List (Induction.A1Cell r)) F` because
`Induction.A1Family` is a plain `def` and instance search will not unfold it. Type-identical;
reverts to the plain spelling if H.93 lands an `abbrev` or a `Membership` instance. -/
def MenuLawAt (n : ℕ) : Prop :=
  ∃ (r : ℕ) (F : Induction.A1Family r) (S : Finset FactorizationType),
    (∀ C ∈ @id (List (Induction.A1Cell r)) F, C.σ ∈ S) ∧
    (∀ σ ∈ S, ∃ C ∈ @id (List (Induction.A1Cell r)) F, C.σ = σ) ∧
    (∀ σ ∈ S, σ.degree = n) ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      CoveringMenu O n S

/-- **NAMED-AND-VOIDED (A-I.1, defect I-D9): I.03's pre-amendment form**, kept so its machine
refutation survives verbatim (the `OM4Shadow.*` pattern). The shape clause here is the
one-directional one; the gate below proves this `Prop` is EQUAL to its bare menu clause, i.e.
the `A1Family` existential carries nothing. **No consumer, gate or census row may cite this
name**; it exists to be refuted. -/
def MenuLawAtVoided (n : ℕ) : Prop :=
  ∃ (r : ℕ) (F : Induction.A1Family r) (S : Finset FactorizationType),
    (∀ C ∈ @id (List (Induction.A1Cell r)) F, C.σ ∈ S) ∧ (∀ σ ∈ S, σ.degree = n) ∧
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
      CoveringMenu O n S

/-! ### NODE I.04 [note] — `A2_n` IS LANDED `DrainageAt n` (NO LEAN FILE)

`A2_n`'s formal carrier exists and is landed: `Uniformity.Density.DrainageAt`
(`Density/Statement.lean:118`), PROVED at `n = 1` (`drainage_one`) and `n = 2` (`drainage_two`),
open at `n ≥ 3`. Chapter I declares **no** parallel drainage `Prop` — that would double-count the
leg (honesty I-4). I.10's `a2` field binds the landed name directly; the `#check` is in the §4
gate. DAG rows only. -/

/-! ### NODE I.05 [def] — `(H-e)-window-pinning`, the pinning carrier (HYP.24's pinning half; the
third COND orphan, resolved at I.14). Lands `Uniformity.Density.WindowPinningAt`. ENV-I1.

⚠ BLOCKED-UNTIL-RESOLUTION (defect I-D12). Status NARROWED at HEAD, not discharged: OM-6 landed
`leanfinal/Uniformity/ChapH/H89w.lean` (CHAP-H amendment A-H.3, 17 declarations, sorry-free,
Lean-core) — `EFF.GENHN.29`'s (b)/(c) clauses at general `e₁`, (a)'s rider-corrected interior
criterion, the `[r2]`/CAP-GEN band census, and (d)'s update-map descent. That narrows the
SUPPLIER gap (honesty I-11(ii)); it does **not** discharge `hwin` (HYP.36, GC-5) and does not
formalize `GENHN-CAP-GEN`'s reader rule. I.05's body gains concrete clauses to bind to at the
resolution pass; it is not bound here. -/

-- The signed body is the bare `True` placeholder; the binder `n` is part of the FROZEN
-- signature (the degree index), so the linter is silenced rather than the contract respelled.
set_option linter.unusedVariables false in
/-- `(H-e)-window-pinning` (Display A; ledger HYP.24's pinning half; COND resolution I.14).
Supplier re-sourcing per v4: `LEMMA GENHN-3` + GENIND-2's consulted-height bound — NOT the
off-route `(H-a)`/`(H-b)` leg. Discharged at `e₁ = 2` by H.89; general case = per-genre
`StageInterface.hwin`.

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over the degree-`n` stage
data (H.09's `StageInterface` instances) and asserts the `hwin` clause at every stage of every
genre of degree `n`. FROZEN HERE: name, degree index, `Prop` kind. -/
def WindowPinningAt (n : ℕ) : Prop :=
  True

/-! ### NODE I.06 [def] — `[GENHN-HE(μ ≥ 3)]`, the deep-leaf σ-decision carrier (HYP.81),
degree-indexed `n ≥ 6`. Lands `Uniformity.Density.GenhnHEAt`. ENV-I1.

⚠ BLOCKED-UNTIL-RESOLUTION (defect I-D12). **The docstring's signed line "transcription owner
UNASSIGNED (orchestrator O-1)" is STALE at HEAD** and is corrected by annotation here, not
edited: OM-7 (2026-08-16) booked the owner — `leanfinal/Uniformity/ChapH/H73w.lean`, CHAP-H
amendment A-H.4 (the HE3.A transport with its degree law, the five-type `μ = 3` dictionary with
degree conservation, five-type exhaustiveness, the `μ = 2` consistency theorem, HE3.B's
unconditionality arithmetic). The conjunct is UNCHANGED and stays on the open surface: `μ ≥ 4`
still rides HYP.143, and consumers still return `BLOCKED: HYP.81`. -/

-- The signed body is the bare `True` placeholder; the binder `n` is part of the FROZEN
-- signature (the degree index), so the linter is silenced rather than the contract respelled.
set_option linter.unusedVariables false in
/-- `[GENHN-HE(μ ≥ 3)]` (Display A, `if n ≥ 6`; ledger HYP.81). `μ = 3` slice: THEOREM HE3.A,
unconditional in the corpus, transcription owner **H73w (OM-7, 2026-08-16)** — the signed
docstring's "UNASSIGNED (orchestrator O-1)" predates that unit. `μ ≥ 4`: open (HE3-BOX-6,
HYP.143). Consumers return `BLOCKED: HYP.81`, never assume.

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): quantifies over degree-`n` stage leaves with
`μ ≥ 3` (H's `StageLeaf`/`GenreDatum` layer) asserting the σ-decision clause. -/
def GenhnHEAt (n : ℕ) : Prop :=
  True

/-! ### NODE I.07 [def] — `[GENHN-TOW-1]`, the deep-tower supplier carrier (HYP.82),
degree-indexed `n ≥ 8`. Lands `Uniformity.Density.GenhnTow1At`. ENV-I1.

⚠ BLOCKED-UNTIL-RESOLUTION (defect I-D12), PARTIALLY TYPEABLE at HEAD: C.93's clause (i) — the
threshold `n = D_r·μ_r ≥ 2^{r+1}` the whole HYP.82 census rests on — is LANDED and reachable as
`Uniformity.Density.Tower.tower_first_live` (`ChapC/C93.lean`), `#check`ed in the §4 gate. The
remaining census items are the `#check`-suite the resolution pass binds. -/

-- The signed body is the bare `True` placeholder; the binder `n` is part of the FROZEN
-- signature (the degree index), so the linter is silenced rather than the contract respelled.
set_option linter.unusedVariables false in
/-- `[GENHN-TOW-1]` (Display A, `if n ≥ 8`; ledger HYP.82). Keyed to chapter C's census C.93: the
boxed remainder is the `n ≥ 8` open family (HYP.67–71/78–80/142/143/144-BOX-2).

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the census conjunction, typed against C.93's
`#check`-suite names at the resolution pass. -/
def GenhnTow1At (n : ℕ) : Prop :=
  True

/-! ### NODES I.08 / I.09 [def] [late-binding: chapter F] — NO LEAN FILE, AND THE TARGETS NOW EXIST

I.08 (`JD0-BOX-2`, HYP.74) and I.09 (`GENHN-BOX-2` + the W-1 sub-residue, HYP.148/HYP.139) are
signed as GC-13(c) placeholders that "type directly into I.10's fields at the F freeze", with no
file of their own. **At HEAD their binding targets are LANDED** (OM-9, 2026-08-16, CHAP-F
amendment A-W.2): `Uniformity.Density.Weld.JD0Box2` (F.04) with the strike ledger
`JD0SiteStrike` and the proved fold half `JD0SiteStrike.jd0Box2`; `Weld.GenhnBox2` (F.11, clause
(iv) structurally absent, the `μ ≥ 3` guard inside the `Prop`); `Weld.W1Transport` (F.12). The §4
gate below elaborates all three at chapter I's consumption shape — so §9's items ~~**L-1 and L-2
are executable now**, which is exactly what makes I.10's `True` fields a defect (I-D7) rather
than a wait~~.

⛔ **STRUCK BY A-I.1 (I-D7/I-D8): L-1 and L-2 are NOT executable.** "Elaborates" is not
"bindable": the shapes gate item (6) exhibits quantify over ALL sites, and gate item (13) PROVES
one of them FALSE (`¬ ∀ (K ι) (Rh RG), W1Transport Rh RG`, at `Fin 1`/`ZMod 3`). A field at that
shape would make the hypothesis block contradictory a second time, so the placeholders STAY and
L-1/L-2's trigger is re-pointed at a weld site-supply socket (the I.10a pattern). The missing
`w1` field is registered as a NAMED DEBT, to be bound with the other two.

The conjuncts themselves are UNCHANGED: CARRY, and the OM-9 `w1` note (a typed instantiation
discharges NOTHING of HYP.139) travels with them. -/

/-! ### NODES I.10a / I.10b [def] [NEW at AMENDMENT A-I.1] — THE ARISING-CONFIGURATION SOCKETS

The two GC-13(c) sockets the re-signed Display-A carrier fields are guarded by. **They exist
because both other readings of the configuration quantifier are closed by machine evidence**
(A-I.1 §I-D13): quantifying over ALL configurations is REFUTABLE (the A-E.2/A-D.2 carriers are
certified FALSE at concrete legal instances — `verification/om4_resign_nontriviality.lean` — so
the block would be contradictory and I.17 would fire from `False`), and bundling the data
existentially (equivalently: threading it as parameters of `CapstoneHypotheses` and supplying it
at I.17) is the FABRICABLE shape defect D-D12 refuted and E.24 explicitly rejected. What is
left, and what the corpus actually claims, is the supply **at the configurations that arise**,
with `ρ` pinned to chapter C's canonical node-point residue read (OM-8 §3.1: YES at every
DEF GENTOW5-1 instantiation with the canonical read, NO at arbitrary `ρ`).

~~⚠ **BLOCKED-UNTIL-RESOLUTION, and the block is on chapter C, not on this chapter.** Both bodies
are the literal `True` placeholder; the typed bodies are owed at chapter C's tower-instantiation
freeze (the same GC-13/GC-14 pass that typed E.61/E.62). **Consequence, disclosed and
machine-shown in the §4 gate: while the sockets read `True` the guarded fields are EQUIVALENT to
the unguarded ones, so A-I.1 weakens nothing today AND the block stays contradictory until the
sockets are typed.** No fleet agent may fire on I.10 (unchanged from the 0e gate).~~

⛔ **RESOLVED AT AMENDMENT A-I.3 (2026-08-26): both bodies are TYPED at chapter C's enacted
carriers.** The tower-instantiation freeze happened as the packaging enactment
(`runs/wave-b/verdict_PK12.md`; `docs/in-progress/PACKAGING_ROUTE_2026-08-25.md` §4.4): the
intended bodies are `leanfinal/Uniformity/ChapC/C130s18.lean`'s `CanonicalLadderConfigData` /
`CanonicalDeepTwistConfigData`, which were composed AT THESE EXACT BINDER BLOCKS for this
re-sign ("re-signing them at these bodies is a later recorded amendment gated on this file" —
C130s18 §1) and amended by PK-2/U15 to the split-carrier existential shape
`∃ (E : Type uE) (fE : Field E) (core : ArisingCore …) (Aℛ : ChainRealization … (fieldE := fE)
core.T Kt E L) (X : RealizedInput core Aℛ) …` with the CC-12 view pins. The bodies below ARE
those carriers (I.10a definitionally; I.10b keeps its frozen refinement shape, definitionally
equal to the C130s18 conjunction — `Iff.rfl` pins at gate item (15)).

⚠ **UNIVERSE PIN, disclosed (A-I.3).** C130s18's carriers are universe-polymorphic in the
existential ambient (`∃ (E : Type uE')`); a `Prop` cannot quantify over universes, and giving
the sockets a NEW universe parameter would leave it an unconstrained metavariable at
`CapstoneHypotheses`' byte-frozen field sites (the fields apply the sockets with no universe
annotation), un-elaborating the frozen structure. The ambient universe is therefore PINNED to
`0` — the universe of every arising instance (the ambient is constructed from `O : Type`;
at S2, `E := FractionRing (Polynomial O)`), and exactly the level C130sg's socket applications
use (`.{0, uG, 0, uL}`). A wider ambient is representable on the leanfinal side
(`CanonicalLadderConfigData.{uE', …}`) if ever needed; re-widening the leanspec socket would be
a further recorded amendment.

⚠ **THE NON-SWALLOWING FENCE, CHECKED AT THE RESOLUTION (A-I.3).** The typed bodies constrain
the CONFIGURATION only — an arising witness (`ChainRealization` + `RealizedInput`) exporting
exactly the socket data through the CC-12 views — and pin no relation between the canonical
residue read `ρ` and the arena read. This is machine-audited, not prose: C130s18's §5 audit
proves that NO derivation uniform in the supplied context can produce either landed trap's
hypothesis (`arenaAgreement_not_uniform` defeats `Gauge.hvarthetaRes_of_arena_agree`'s
agreement clause; `embeddedValue_not_uniform` defeats the `Gauge.hvarthetaRes_of_tau_letters`
genre), because a χ-twist of the canonical read is again a full carrier supplying identical
socket data. Unpacking a socket leaves exactly the OM-8 L3 descent/agreement goal — reachable,
NOT supplied.

⚠ **THE NON-SWALLOWING FENCE (A-I.1, binding on the resolution pass).** The socket may NOT be
typed at any condition that already implies its own carrier. Two landed traps, both of which
would silently discharge a CARRY conjunct by hypothesis-shuffling rather than by mathematics:
`Gauge.hvarthetaRes_of_arena_agree` (a `ρ` agreeing with an arena's residue read discharges
`HVarthetaRes` outright) and `Gauge.hvarthetaRes_of_tau_letters` (the τ-letter law does the
same). The socket must constrain the CONFIGURATION (that it is the one chapter C's tower
produces), never the residue law itself. -/

set_option linter.unusedVariables false in
/-- **NODE I.10a** [A-I.1] — *the arising ladder configuration at chapter C's canonical residue
read.* The block `(C, B)` is the one chapter C's OM ladder produces for a degree-`n` input over
`O`, and `(G, K_t, L, N, v, ρ, q)` is that tower's level data with `ρ` the CANONICAL node-point
residue datum (OM-8's pinning; an unpinned `ρ` leaves the ϑ-conjunct undischargeable, and the
`∀ ρ` reading makes it outright false).

[A-I.2(a), 2026-08-24 — interpretive rider, no statement change.] The frozen single `K_t` is
the terminal common receiver: every arising witness carries `T.fld r ≃+* K_t` and compatible
live maps `T.fld i →+* K_t` (freeze v2's `TerminalReceiver`). Thus the conclusion is the
common-receiver recast in `K_r`, not the source's literal per-level `K_i` statement.

~~⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): typed at chapter C's tower-instantiation freeze.
FROZEN HERE: the name, the configuration argument block, the degree index, the `Prop` kind.~~
⛔ **TYPED AT AMENDMENT A-I.3 (2026-08-26)**: the body is chapter C's enacted I.10a
data-carrier `Uniformity.Density.Tower.C130s18.CanonicalLadderConfigData` (freeze v2 §8 at the
landed CC-12 views, PK-2/U15-amended split-carrier shape — `runs/wave-b/verdict_PK12.md`,
`PACKAGING_ROUTE_2026-08-25.md` §4.4), ambient universe pinned to `0` (see the section
disclosure). The frozen name/argument block/degree index/`Prop` kind are byte-unchanged. -/
def CanonicalLadderConfig {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) : Prop :=
  -- [A-I.3, 2026-08-26] the typed body (was the `True` placeholder): some arising occurrence,
  -- realized by the PK-1 split-node chain carrier, exports exactly `(C, B, G, N, v, ρ, q)` at
  -- degree `n` through the CC-12 views. Cites: verdict_PK12.md + PACKAGING_ROUTE §4.4.
  Uniformity.Density.Tower.C130s18.CanonicalLadderConfigData.{0, uG, uKt, uL}
    C B G Kt L N v ρ q n

set_option linter.unusedVariables false in
/-- **NODE I.10b** [A-I.1] — *the arising deep-twist configuration*: I.10a's configuration
TOGETHER with the level-indexed gauge-arena family `(A, R, w)` chapter D's `𝒲` leg reads
(`EFF.T3.21`'s `θ_j`, `w_j`). The conjunction spelling is deliberate: the second component is
the arena half's own socket, so when both are typed the refinement
`CanonicalDeepTwistConfig → CanonicalLadderConfig` holds BY CONSTRUCTION (machine-checked in
the §4 gate), and no pass can type the deep-twist half against a configuration the ladder half
would reject.

~~⚠ STUB-STAGE BODY: the `True` conjunct is the arena half's placeholder, owed at the same
freeze. FROZEN HERE: the name, the argument block, the refinement shape, the `Prop` kind.~~
⛔ **TYPED AT AMENDMENT A-I.3 (2026-08-26)**: the arena-half conjunct is chapter C's enacted
joint-witness carrier `Uniformity.Density.Tower.C130s18.DeepTwistRealizationData` (behind the
same `IsDomain`/`IsDiscreteValuationRing` existential the ladder half carries), so the whole
body is definitionally C130s18's `CanonicalDeepTwistConfigData` (`Iff.rfl`, gate item (15)).
The frozen refinement shape is byte-preserved: the first conjunct is still literally
`CanonicalLadderConfig …`, so I.10b → I.10a stays `And.left` by construction. -/
def CanonicalDeepTwistConfig {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ)
    (r n : ℕ) : Prop :=
  -- [A-I.2(b)] `r` is the tower depth the deep-twist conjunct is read at; the final real body
  -- must pin it to the same joint arising witness the arena export uses (never a free numeral).
  -- [A-I.3, 2026-08-26] the pin is now REAL: the joint witness carries `core.r = r` inside
  -- `DeepTwistRealizationData` (A-I.2(b)'s "never a free numeral" rule, discharged).
  CanonicalLadderConfig C B G Kt L N v ρ q n ∧
    ∃ (dom : IsDomain O) (dvr : IsDiscreteValuationRing O),
      Uniformity.Density.Tower.C130s18.DeepTwistRealizationData.{0, uG, uKt, uL}
        (dom := dom) (dvr := dvr) C B G Kt L N v ρ q A R w r n

/-! ### NODES I.10c / I.10d [structure/def] [NEW at AMENDMENT A-I.5, 2026-08-27] — THE GC-13
WIRING LAW AND THE WIRED PER-LEVEL `deepTwist` DEMAND

**[A-I.5, unit GCW1]** — the GCW-1 signing round of `docs/in-progress/GC13_WIRING_2026-08-27.md`
(its `[GCW-0]` decision record + the orchestrator's F2=P2 adjudication; print-read
`runs/wave-b/verdict_GCW0.md`).  Decisions enacted, all three forks:

* **F1** — the law is the RELATIONAL SCALAR-READ bridge at the abstract D.44 surface: no
  lattice-equals-polynomial equality; D.44's `(N, q, R)` binders retained (the arising-witness
  views `C130vw.GaugeFamilyViewEq`/`ArenaFamilyViewEq` already pin them to a witness's exports);
  grade `e' * (s * u')` = OPEN-DICT-2's full-current clearing (NOT `s * u'`); normalizer
  `chainNormBelow r` = the decided below-current `n̂_i` (NOT the current key).
* **F2 = P2** — a standalone `Prop` record demanded by the chapter-I suppliers at arising
  witnesses.  The signed socket I.10b (`CanonicalDeepTwistConfig`) and I.10's field list are
  BYTE-UNCHANGED; the guard-extension fork is REJECTED (gate-(a) statement change of the signed
  socket + chapter-C coupling, the P1 genre P2 was adopted against).
* **F3** — the SOURCE DEFINES the read (`EFF.T3.21`: "Define `w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1}))`";
  `GENTOW2_PROOF_2026-08-09.md` S5.1 `u(β) := R_{3,β}(n̂₂(β̂))`, S5.2 `w := u(κ̄)`); Lean's
  `towerRead` is a FREE node field (NP-8), so the definition is signed HERE as a law.  The P3
  definitional route is licensed ONLY at witness-construction sites AFTER this signing (GCW-3).

**The underdetermination basis (why a LAW, not a proof)** — FGCW's certificates, both landed
Lean-core in `leanfinal/Uniformity/ChapI/IFC2.lean`: `s2_hread_refuted_at_landed_exports` (the
landed S2 witness's OWN exported read `≡ 0` refutes the identification at every level, receiver,
lattice point) and `s2_gentowW_of_read_one` — ⚠ the D-D12-FENCED freedom half (the equally
admissible read `≡ 1` satisfies FULL `GentowW`): **NOT SUPPLY, never citable as teeth**; cited
here only as the freedom half of the both-truth-values adjudication.

**The amended DT0 demand (I.10d).**  The `deepTwist`-route per-level GentowW demand gains the
wiring leg SITEWISE: at one consumed live level `j` of an arising witness, instantiate at the
guard's own exports `(N, q j, R j, A j, w j)` and the supplied level calculus/receiver.  The
UNIVERSAL wired supplier is deliberately NOT signed — BLOCKED-BECAUSE: the per-level
calculus/receiver correspondence has no landed exporter (the `WleCleared` truncation exporter,
GC13_WIRING §4 / FIELDLIST §8 — the DT0 analogue of W0's missing weld-site exporter), and every
site-quantified form is defective today: a guard-side or `∃`-bound site collapses to the
refutable unwired demand through an `f' = 0` junk site (gate example (19) below is the anchor);
an `∀`-bound site is false at wrong calculi; a def-parameter site family cannot see the witness
hidden in the guard's existential.  Leanfinal twins + the μ₃ consumption route (the `hread`
binder of IFC1/IFC2 superseded by the law's projection; the law-forced S2 read normalization;
the anti-cook refutation at the landed zero-read witness): `Uniformity/ChapI/IFC3.lean`,
byte-identical binder blocks.  IFC0's flat `DeepGentowSupplier` is RETIRED AS A CAMPAIGN TARGET
(byte-untouched there — it stays GCW-6's tension record: any depth-`≥ 4` witness with a zero
read refutes it; stop-the-line for the deep-witness campaign). -/

section GC13WiringLaw

open Uniformity.Density.Gauge Uniformity.Density.Tower

universe uT

/-- **NODE I.10c** [A-I.5] — *GC-13's read/normalizer dictionary at one D.44 site*: the exported
tower read at the `s`-th ladder point IS the receiver image of the FGMN normalizer read at the
cleared full-current grade.  GCW-0's decision-record statement, signed VERBATIM.  A chapter-I
supplier must demand an instance at each consumed live level using the arising witness's OWN
exported `(N, q j, R j)` and the corresponding calculus/receiver (the D-D12 anti-cook guard).
NEW STATEMENT (review row: `docs/REVIEW_QUEUE_2026-08-26.md`, A-I.5). -/
structure GC13Wiring {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    (N : NormSection G) (q : ℤ) (R : G → Kt)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (φ : W.fld r →+* Kt) : Prop where
  read_norm : ∀ s : ℕ, 1 ≤ s → s ≤ f' →
    R (N.n (s * q)) =
      φ (I.Rgr (e' * (s * u')) (I.chainNormBelow r (s * u')))

/-- **NODE I.10d** [A-I.5] — *the wired per-level DT0 demand*: at one D.44 site, the signed
GC-13 law AND D.44's `[GENTOW5-W(j)]` identity `GentowW`, at the same read.  STRENGTHENS the
flat per-level conclusion (gate example (20)); supersedes it as the campaign target.
NEW STATEMENT (review row: `docs/REVIEW_QUEUE_2026-08-26.md`, A-I.5). -/
def WiredGentowDemand {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} (A : GaugeArena G Kt N) (q : ℤ) (R : G → Kt) (w : Ktˣ)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    (I : FGMNCalculus W e' f' u') (φ : W.fld r →+* Kt) : Prop :=
  GC13Wiring N q R I φ ∧ GentowW A q R w

-- (18) [A-I.5] the record's projection is BYTE-EXACTLY the `hread` shape IFC1 displayed
-- (`IFC1.gentowWWindow_of_gentow5wCleared`'s binder) — the consumer-shape pin, generic form.
example {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} {q : ℤ} {R : G → Kt}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    {I : FGMNCalculus W e' f' u'} {φ : W.fld r →+* Kt}
    (hwire : GC13Wiring N q R I φ) :
    ∀ s, 1 ≤ s → s ≤ f' → R (N.n (s * q)) =
      φ (I.Rgr (e' * (s * u')) (I.chainNormBelow r (s * u'))) := hwire.read_norm

-- (19) [A-I.5] THE FABRICABILITY FENCE, EXECUTED: at `f' = 0` the law is VACUOUS at any read —
-- why no landed statement may quantify the level site existentially or hypothesis-side, and
-- why the universal wired supplier is BLOCKED on the per-level exporter.
example {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} {q : ℤ} {R : G → Kt}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' u' : ℕ}
    (I : FGMNCalculus W e' 0 u') (φ : W.fld r →+* Kt) :
    GC13Wiring N q R I φ :=
  ⟨fun _ hs1 hs0 => absurd (hs1.trans hs0) (by omega)⟩

-- (20) [A-I.5] the wired demand STRENGTHENS the flat per-level conclusion (nothing weakened):
-- both legs are projections.
example {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : NormSection G} {A : GaugeArena G Kt N} {q : ℤ} {R : G → Kt} {w : Ktˣ}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ}
    {I : FGMNCalculus W e' f' u'} {φ : W.fld r →+* Kt}
    (h : WiredGentowDemand A q R w I φ) :
    GC13Wiring N q R I φ ∧ GentowW A q R w := ⟨h.1, h.2⟩

end GC13WiringLaw

/-! ### NODE I.10 [structure] — **THE CAPSTONE HYPOTHESIS STRUCTURE** (Display A, made formal).
Lands `Uniformity.Density.CapstoneHypotheses`. ENV-I1.

⚠⚠ **THIS DECLARATION IS AN ELABORATION GATE, NOT A SIGNATURE — defect I-D7.** The blueprint's
§11 blocked table says, verbatim, *"a signed I.10 stub with `True` fields is a false
conditionality claim; forbidden"*, and I.10's own SIGNATURE block nevertheless signs
`jd0 : True` and `genhnBox2 : 6 ≤ n → True`. The structure is landed here at the SIGNED types so
that the eight non-placeholder fields are type-checked against the landed corpus (which is what
found I-D3, I-D4, I-D5 and I-D9); **no fleet agent may fire on I.10 until the owner re-signs the
field list.** ~~Since OM-9 the two `True` fields have real binding targets (F.04/F.11/F.12) — the
gate below elaborates them — so the placeholders are STALE, not merely blocked.~~ ⛔ **A-I.1
corrects this**: the targets are landed but not BINDABLE at the exhibited shapes (gate item (13)
refutes one of them), so the placeholders are blocked after all — on the weld site-supply socket,
not on chapter F. And the defect that now dominates I.10 is I-D13, not I-D7: the eight
NON-placeholder fields are the ones that make the block contradictory.

⛔ **[A-I.3, 2026-08-26] I-D13 IS LIFTED: the I.10a/I.10b sockets are TYPED** (bodies =
chapter C's enacted `C130s18` carriers; see the socket nodes above and the STATE UPDATE in the
header). The field list below is BYTE-UNCHANGED by A-I.3; the gate's refutation of the block
(old item (10)) no longer elaborates and is struck with its text preserved. The block's honest
state is OPEN — not provably empty, not claimed inhabited. The `jd0`/`genhnBox2` placeholders,
the `w1` debt, and I-D10 are untouched and still owed exactly as A-I.1 ruled. The Stage-2
companion lands the byte-frozen transcription (sockets + structure + I.15–I.18, statements
only, nothing discharged) at `leanfinal/Uniformity/ChapI/I10_I15_I18.lean`.

⚠ **THE `ladder` FIELD, RE-SIGNED AT AMENDMENT A-I.1 (defects I-D3 and I-D13).** Two halves:
(i) the MECHANICAL half — the 0e gate found the signed `Ladder.LadderSupply C B` underapplied by
eight arguments against landed E.24, and the repaired application (level data
`(G, Kt, L, N, v, ρ, q)` bound in the field, six universes spelled `LadderSupply.{0, 0, uW, uG,
uKt, uL}`, E-12) is now the SIGNED application; (ii) the MATHEMATICAL half — the `∀`-over-all-
configurations reading is not merely undischargeable (OM-8's ρ-defeat), it is **REFUTABLE**
(A-I.1 §I-D13: `¬ LB1Carrier C₁ B₁` at a legal `SlotCarrier ℤ ℚ`,
`verification/om4_resign_nontriviality.lean`), so the field is guarded by I.10a's
`CanonicalLadderConfig` — the supply is demanded at the ARISING configurations, at chapter C's
canonical residue read, which is what the corpus claims and the only reading that can ever be
discharged.

⚠ **THE `deepTwist` FIELD IS NEW AT A-I.1 (defect I-D4).** Display A's `∀ i ≥ 3` conjunct is
`(H-VARTHETA-RES)_i ∧ 𝒲_{≤i}`; E.24's `LadderSupply` packages the ϑ-half ONLY (its own
docstring: *"E.62's `𝒲` leg is conjoined at chapter I, not here"*), so as signed chapter I
carried half a conjunct. The field consumes E.63's `Ladder.DeepTwistConjunct`, which packages
BOTH halves at the typed E.61/E.62 sockets and threads ONE use-height family `q` through both
(E.63's own fence). The ϑ-half is now carried twice (here and inside `ladder`'s `vartheta`
projection) at the SAME level data: harmless redundancy, and the field-level source of truth for
the `∀ i ≥ 3` conjunct is `deepTwist`.

⚠ **QUANTIFIER DISCLOSURE, transcribed and AMENDED (A-I.1).** Display A assumes the ladder suite
"uniformly in `O`"; E's carriers are instance-level. The 0e reading quantified over ALL
instantiations — "the strongest uniform reading", chosen without the level data in view — and
§I-D13 shows that reading is FALSE, not strong. The signed reading is the blueprint's own
alternative ("the instantiations arising from degree-`n` inputs"), sharpened by OM-8 to the
canonical residue read and named as the I.10a/I.10b sockets. It weakens a hypothesis, hence
STRENGTHENS the theorem; it is an owner gate-(a) event and is flagged as such in A-I.1.

⚠ **KIND NOTE [F7], transcribed.** H.95's `InductionPackage` is a `def`-Prop existential; this
carrier is a `structure` and does NOT claim to mirror H.95's kind. -/

/-- **Display A** (`spec/HYPOTHESIS_LEDGER.md`, FROZEN v5), one field per conjunct, at ledger
strength, degree-indexed where the display is. Field-list changes are owner gate-(a) events
(CONVENTIONS Part V).

Consumption rules in force (I.10's 2026-08-16 dated note): `ladder`'s `.lb1`/`.mp1` projections
are the **A-E.2** forms (`Nonempty (BlockSuite I)` / `Nonempty (MidPeelEmission B B')`), consumed
universe-polymorphically in `uW`; `.vartheta` is E.61's typed socket at chapter D's **A-D.2**
sitewise `HVarthetaRes`. The voided shadows (`OM4Shadow.*`, `HVarthetaResVoided`) are FENCED.

⚠ The `AllOInterfaces` conjunct is NOT a field — §4.3's signed reconciliation (honesty I-10).
⚠ `jd0`/`genhnBox2` are the FORBIDDEN-TO-SIGN placeholders (defect I-D7); `w1` has no field at
all (defect I-D8). A-I.1 RULES both open rather than typing them — the naive consumption shapes
the 0e gate exhibited are REFUTABLE (see the §4 gate's item (13)), so binding them unguarded
would add a second contradiction to the block. -/
structure CapstoneHypotheses (n : ℕ) : Prop where
  ns7 : NS7Termination
  -- [A-I.1] the repaired E.24 application, guarded by I.10a's arising-configuration socket.
  -- [A-I.6, 2026-08-28 — STATEMENT CHANGE (rebind)] the result record is the live-range
  -- `IFC5.LadderSupplyLive` (the vartheta leg demanded only at indices live in a realization
  -- witnessing the SAME socket data): the old unbounded `Ladder.LadderSupply` conclusion is
  -- machine-REFUTED at the landed degree-4 S2 occurrence (`scratch/AI6_probe.lean`, Lean-core,
  -- archived pre-rebind at commit ce301df1; adjudication `runs/wave-c/verdict_AI6.md`) — a
  -- forced weakening of a hypothesis, hence a STRENGTHENING of the conditional capstone.
  -- [A-I.7, 2026-08-28 — STATEMENT CHANGE (rebind)] the result record is the A-I.7 record
  -- `IFC5.LadderSupplyLive₂` (ONLY the `mp1` leg replaced by the same-realization
  -- `MP1CarrierLive`: the MidPeelEmission conclusion is demanded only at successors exported
  -- by a `RecenterStep` of the SAME realization witnessing the socket): the A-I.6 record's
  -- unrestricted `mp1` is machine-REFUTED at the landed degree-4 S2 occurrence
  -- (`scratch/REX_probe.lean`, Lean-core, archived pre-rebind at commit 05f067b7;
  -- adjudication `runs/wave-c/verdict_REX.md`) — again a forced weakening of a hypothesis,
  -- hence a STRENGTHENING of the conditional capstone.
  ladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Uniformity.Density.IFC5.LadderSupplyLive₂.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n
  -- [A-I.1, defect I-D4] Display A's `∀ i ≥ 3` conjunct, BOTH halves, at E.63's packaging.
  -- [A-I.2(b), 2026-08-24] re-signed at the freeze-v2 LIVE RANGE: the conjunct is read at the
  -- arising tower depth `r` through `DeepTwistConjunctLive` (unbounded form undischargeable).
  -- [A-I.5, 2026-08-27 — interpretive rider, no statement change.] The GC-13 wiring law
  -- (NODE I.10c) is signed; per GCW-0 + P2 the per-level GentowW half of this field's supply
  -- route is superseded as a campaign target by the WIRED sitewise demand (NODE I.10d) — a
  -- STRENGTHENING at each site.  This field is BYTE-UNCHANGED; suppliers demanding its
  -- conclusion at arising witnesses must demand `GC13Wiring` per consumed live level at the
  -- guard's own `(N, q j, R j)` exports (GCW-6 stop-the-line: no depth-`≥ 4` witness may land
  -- with a read violating the law — a zero-read deep witness refutes the flat supplier).
  deepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w
  a0 : DecidedSliceAt n
  a1 : MenuLawAt n
  a2 : DrainageAt n
  jd0 : True                            -- ⚠ LATE-BINDING F (I.08); defect I-D7
  genhnBox2 : 6 ≤ n → True              -- ⚠ LATE-BINDING F (I.09); defects I-D7, I-D8
  windowPinning : WindowPinningAt n
  genhnHE : 6 ≤ n → GenhnHEAt n
  genhnTow1 : 8 ≤ n → GenhnTow1At n

/-! ## §4 GATE (executed; not blueprint declarations)

Nine checks. Each is something this section could get wrong silently, and three of them are the
machine evidence behind defects I-D4, I-D7 and I-D9. -/

section GateFour

-- (1) I.04: `A2_n`'s carrier is the LANDED `DrainageAt`, and I.10's `a2` field binds that name.
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n) : DrainageAt n := h.a2

-- (2) the A-E.2 `(LB1)` consumption pattern, universe-polymorphic in `uW`: from the `ladder`
-- field AT AN ARISING CONFIGURATION (A-I.1's I.10a guard) and a triggering interface, the FULL
-- S1.7A block suite. Had `lb1` been left at the machine-refuted shadow (product identity +
-- degree sum only), this would not typecheck.
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n)
    (K : Type) [Field K] (C : Ladder.SlotCarrier ℤ K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (hcfg : CanonicalLadderConfig C B G Kt L N v ρ q n)
    (I : Ladder.RungInterface.{0, 0, uW} C B) (hmulti : 1 < I.sides.card) :
    Nonempty (Ladder.BlockSuite I) :=
  (h.ladder ℤ K C B G Kt L N v ρ q hcfg).lb1 I (Or.inl hmulti)

-- (3) the A-E.2 `(MP1)` consumption pattern: at a legal recentering, the FULL items-2–5 record.
-- [A-I.7, 2026-08-28] the consumption now additionally costs the recenter-step export
-- `hstep` (the rebound `mp1` leg's premise) — the honest price REX established: without it
-- the unrestricted demand is refutable at the landed degree-4 S2 socket, not merely open.
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n)
    (K : Type) [Field K] (C : Ladder.SlotCarrier ℤ K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (hcfg : CanonicalLadderConfig C B G Kt L N v ρ q n)
    (Λ : Polynomial ℤ) (hΛ : Λ ≠ 0) (hdeg : Λ.natDegree < C.D) (B' : Ladder.BlockData C)
    (hB' : B'.Φ = B.Φ - Λ) (hdvd : B'.Φ ∣ B.F)
    (hstep : Uniformity.Density.IFC5.RecenterStep.{uW, uG, uKt, uL}
      C B B' G Kt L N v ρ q n Λ) :
    Nonempty (Ladder.MidPeelEmission.{0, 0, uW} B B') :=
  (h.ladder ℤ K C B G Kt L N v ρ q hcfg).mp1 Λ hΛ hdeg B' hB' hdvd hstep

-- (4) the A-D.2 `(H-VARTHETA-RES)_i` consumption pattern: chapter D's SITEWISE carrier at the
-- level-`i` data. Typing this against the voided existential would fail.
-- [A-I.6, 2026-08-28] the consumption now additionally costs the live-index certificate
-- `hLive` (the rebound `vartheta` leg's premise) — the honest price VAUD/AI6 established:
-- without it the unbounded demand is refutable, not merely open.
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n)
    (K : Type) [Field K] (C : Ladder.SlotCarrier ℤ K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (hcfg : CanonicalLadderConfig C B G Kt L N v ρ q n) (i : ℕ) (hi : 3 ≤ i)
    (hLive : Uniformity.Density.IFC5.CanonicalLadderLiveAt
      C B G Kt L N v ρ q n i) :
    Gauge.HVarthetaRes G Kt L N (v i) (ρ i) (q i) :=
  ((h.ladder ℤ K C B G Kt L N v ρ q hcfg).vartheta i hi hLive).supplied

-- (5) **DEFECT I-D4, CURED AT A-I.1 and machine-exhibited at the new field.** Display A's
-- `∀ i ≥ 3` conjunct has BOTH halves at the typed sockets, delivered by E.63's
-- `DeepTwistConjunct` through the `deepTwist` field: the sitewise `(H-VARTHETA-RES)_i` AND the
-- cumulative `𝒲_{≤i}` w-frame, at one use-height family `q`. Before A-I.1 the `𝒲` half had no
-- carrier anywhere in the structure.
#check @Uniformity.Density.Ladder.DeepTwistConjunctLive
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n)
    (K : Type) [Field K] (C : Ladder.SlotCarrier ℤ K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r i : ℕ)
    (hcfg : CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n)
    (hi : Tower.DeepLive r i) :
    Gauge.HVarthetaRes G Kt L N (v i) (ρ i) (q i) ∧ Ladder.WFrame A q R w i :=
  ⟨(h.deepTwist ℤ K C B G Kt L N v ρ q A R w r hcfg i hi).1.supplied,
   (h.deepTwist ℤ K C B G Kt L N v ρ q A R w r hcfg i hi).2⟩

-- (5a) the I.10b refinement, by construction: a deep-twist configuration IS a ladder
-- configuration, so the two guarded fields can never drift onto different data.
example {K : Type} [Field K] {C : Ladder.SlotCarrier ℤ K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ}
    {A : ℕ → Gauge.GaugeArena G Kt N} {R : ℕ → G → Kt} {w : ℕ → Ktˣ} {n : ℕ}
    {r : ℕ} (hcfg : CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n) :
    CanonicalLadderConfig C B G Kt L N v ρ q n := hcfg.1

-- (6) **DEFECT I-D7 / items L-1 and L-2, machine-exhibited.** The `True` fields' binding targets
-- are landed and type at chapter I's consumption shape RIGHT NOW.
example : Prop :=
  ∀ (Γ K : Type) [AddCommGroup Γ] [Field K] (site : Weld.ValueDictSite Γ K), Weld.JD0Box2 site
example : Prop := ∀ (K : Type) [Field K] (s : Weld.CarrySite K), Weld.GenhnBox2 s
example : Prop := ∀ (K ι : Type) [Field K] (Rh RG : ι → K), Weld.W1Transport Rh RG

-- (7) **DEFECT I-D9, machine-PROVED, PRESERVED VERBATIM AGAINST THE VOIDED NAME.** The
-- pre-A-I.1 shape clause is one-directional, so `r = 0, F = []` satisfies it for every `S`, and
-- `MenuLawAtVoided` is EQUAL to its bare menu clause. This is the OM-4 FINDING-0 genre and is
-- NOT what I.03's ⚠ SIGNATURE NOTE disclosed. (Statement and proof are the 0e gate's, with the
-- carrier name re-pointed at the voided copy — that is the whole diff.)
example (n : ℕ) : MenuLawAtVoided n ↔
    ∃ S : Finset FactorizationType, (∀ σ ∈ S, σ.degree = n) ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)],
        CoveringMenu O n S := by
  constructor
  · rintro ⟨_, _, S, _, hdeg, hmenu⟩
    exact ⟨S, hdeg, hmenu⟩
  · rintro ⟨S, hdeg, hmenu⟩
    exact ⟨0, ([] : List (Induction.A1Cell 0)), S, by intro C hC; simp at hC, hdeg, hmenu⟩

-- (7a) **A-I.1's CERTIFICATION of the I-D9 re-sign (the A-E.2 standard: the witness that killed
-- the old form must FAIL against the new one).** The empty family does not satisfy the
-- re-signed enumeration clause at any nonempty menu — so the vacuity witness genre is dead.
example (σ₀ : FactorizationType) :
    ¬ (∀ σ ∈ ({σ₀} : Finset FactorizationType),
        ∃ C ∈ @id (List (Induction.A1Cell 0)) ([] : Induction.A1Family 0), C.σ = σ) := by
  intro h
  obtain ⟨C, hC, _⟩ := h σ₀ (Finset.mem_singleton_self σ₀)
  simp at hC

-- (7b) the re-signed carrier still IMPLIES the old one (nothing was traded away): A-I.1
-- STRENGTHENED I.03, it did not respell it.
example (n : ℕ) (h : MenuLawAt n) : MenuLawAtVoided n := by
  obtain ⟨r, F, S, hsub, _, hdeg, hmenu⟩ := h
  exact ⟨r, F, S, hsub, hdeg, hmenu⟩

-- (8) I.07's partially-typed census leg: C.93 clause (i), the `n = D_r·μ_r ≥ 2^{r+1}` threshold
-- the whole HYP.82 census rests on, is LANDED and reachable.
#check @Uniformity.Density.Tower.tower_first_live

-- (9) **DEFECT I-D13 (A-I.1's NEW finding), machine-TRANSPORTED: the 0e `ladder` field is not
-- undischargeable, it is FALSE.** One legal `(C, B)` at which the A-E.2 carrier fails refutes
-- the whole ∀-over-all-configurations reading. The antecedent is certified, not assumed:
-- `verification/om4_resign_nontriviality.lean` proves `lb1_resigned_not_trivial :
-- ¬ LB1Carrier C₁ B₁` over a REAL `SlotCarrier ℤ ℚ` with `B₁.F = X² + X + 1`. RE-RUN at this
-- amendment (`lake env lean ../verification/om4_resign_nontriviality.lean`, exit 0, Lean-core),
-- and its carriers diffed against the landed ones: `LB1Carrier`/`BlockSuite` byte-identical
-- modulo namespace, `RungInterface` differing only in universe-variable spelling.
example {C : Ladder.SlotCarrier ℤ ℚ} {B : Ladder.BlockData C}
    (hlb1 : ¬ Ladder.LB1Carrier.{0, 0, uW} C B)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) :
    ¬ (∀ (O : Type) [CommRing O] (K : Type) [Field K]
        (C' : Ladder.SlotCarrier O K) (B' : Ladder.BlockData C')
        (G' : Type uG) [CommGroup G'] (Kt' : Type uKt) [Field Kt'] (L' : Type uL) [Field L']
        [Algebra Kt' L'] (N' : Gauge.NormSection G') (v' : ℕ → (G' →* Multiplicative ℤ))
        (ρ' : ∀ j : ℕ, MonoidHom.ker (v' j) →* L'ˣ) (q' : ℕ → ℤ),
        Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C' B' G' Kt' L' N' v' ρ' q') :=
  fun hall => hlb1 (hall ℤ ℚ C B G Kt L N v ρ q).lb1

-- (10) ~~…and, WHILE THE I.10a SOCKET READS `True`, the same refutation reaches the re-signed
-- structure: `CapstoneHypotheses n` is UNINHABITED, hence `∀ n, CapstoneHypotheses n` is FALSE
-- and I.15–I.18 fire from a contradiction. **This is the disclosure A-I.1 exists to make.** It
-- is repaired by TYPING I.10a (chapter C's freeze), not by any edit here: a typed socket
-- excludes exactly the adversarial `(C, B)`/`ρ` configurations that carry the refutation.~~
-- ⛔ **STRUCK BY A-I.3 (2026-08-26): the socket is TYPED and this refutation route is CLOSED —
-- defect I-D13's contradiction is LIFTED.** The item's proof fed the certified-false `(C, B)`
-- through the socket with `trivial`; with the body the C130s18 carrier, the adversarial
-- configuration would need an arising witness (a `ChainRealization`/`RealizedInput` pair
-- exporting exactly that `(C, B)` and `ρ` through the CC-12 views) — exactly what the socket
-- was installed to demand. NOT thereby claimed: inhabitation of `CapstoneHypotheses n`
-- (`a0`/`a1` stay open at `n ≥ 3`; the guarded fields still demand supply at the arising
-- configurations; the weld debts are untouched). The struck term, preserved verbatim (it no
-- longer elaborates — `trivial` no longer certifies an arising configuration, which is the
-- amendment's whole content):
--   example {C : Ladder.SlotCarrier ℤ ℚ} {B : Ladder.BlockData C}
--       (hlb1 : ¬ Ladder.LB1Carrier.{0, 0, uW} C B)
--       (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
--       [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
--       (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) :
--       ¬ CapstoneHypotheses.{uW, uG, uKt, uL} n :=
--     fun h => hlb1 (h.ladder ℤ ℚ C B G Kt L N v ρ q trivial).lb1

-- (11) ~~**A-I.1 WEAKENS NOTHING TODAY (the "never weaken" check, machine-run).** While I.10a's
-- body is the placeholder, the guarded `ladder` field type is EQUIVALENT to the 0e unguarded
-- one — so the amendment installs the binding site without moving the strength; the narrowing
-- to arising configurations happens exactly at the moment the socket is typed, and is the
-- gate-(a) event flagged to the owner.~~ ⛔ **RETIRED BY A-I.3 (2026-08-26): THE FLAGGED
-- NARROWING HAS HAPPENED.** With the socket typed, the 0e equivalence's forward direction
-- (guarded ⟹ unguarded, proved by `trivial`) is GONE — deliberately: that direction was the
-- contradiction (items (9)/(10)). What survives, machine-run below, is the weakening direction
-- (unguarded ⟹ guarded): the guarded field is IMPLIED by the 0e one, so A-I.3 weakens a
-- hypothesis and thereby STRENGTHENS I.15–I.18 — the owner-gate-(a) event A-I.1 flagged in
-- advance, now enacted and re-flagged (REVIEW_QUEUE_2026-08-26 amendment row A-I.3).
example (n : ℕ) :
    (∀ (O : Type) [CommRing O] (K : Type) [Field K]
        (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
        (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
        [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
        (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
        Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q)
      →
    (∀ (O : Type) [CommRing O] (K : Type) [Field K]
        (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
        (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
        [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
        (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
        CanonicalLadderConfig C B G Kt L N v ρ q n →
        Ladder.LadderSupply.{0, 0, uW, uG, uKt, uL} C B G Kt L N v ρ q) := by
  intro h O _ K _ C B G _ Kt _ L _ _ N v ρ q _
  exact h O K C B G Kt L N v ρ q

-- (12) the NON-SWALLOWING fence, with its landed trap named as a term: this, used as the I.10a
-- socket's body, would discharge the ϑ-conjunct outright — a CARRY row retired by
-- hypothesis-shuffling rather than by mathematics. The resolution pass must constrain the
-- CONFIGURATION, never the residue law. (The second trap, `hvarthetaRes_of_tau_letters` in
-- `ChapD/D62w.lean`, is the τ-letter law and is the same hazard; it cannot be `#check`ed from
-- this file because D62w is the module defect I-D1 makes un-importable alongside D55/D63.)
#check @Uniformity.Density.Gauge.hvarthetaRes_of_arena_agree

-- (13) **DEFECT I-D7/I-D8's honest reason, machine-shown (A-I.1's ruling).** The 0e gate's item
-- (6) exhibited the weld carriers' `∀`-over-all-sites consumption shapes as if they were ready
-- to bind. They are not: at least one of them is REFUTABLE, so a field at that shape would make
-- the block contradictory in a second, independent way. `W1Transport` is equivalent to equality
-- of vanishing loci (F.12w), and mismatched loci refuse every transport — so the `∀ Rh RG`
-- reading is FALSE, exhibited here at `ι = Fin 1`, `K = ZMod 3`.
example : ¬ (∀ (K ι : Type) [Field K] (Rh RG : ι → K), Weld.W1Transport Rh RG) := by
  intro h
  have := (Weld.w1Transport_iff_zero_iff (K := ZMod 3) (ι := Fin 1)
    (fun _ => (1 : ZMod 3)) (fun _ => (0 : ZMod 3))).mp (h (ZMod 3) (Fin 1) _ _)
  exact one_ne_zero ((this 0).mpr rfl)

-- (14) ~~the FENCE: `NS7Termination`'s signed body is the placeholder, witnessed by the old
-- gate below.~~ ⛔ **RESOLVED BY A-I.4 (2026-08-27):** the old gate is struck with its text
-- preserved, and the replacement pins the new body to the landed A-C.6 redraft on the nose.
-- The second example is the explicit consumer audit: I.10's `ns7` field still projects at the
-- re-signed type, with the field list byte-unchanged.
--
-- STRUCK PRE-A-I.4 GATE (no longer elaborates, which is the point):
-- example : NS7Termination := fun _ => trivial
example : NS7Termination ↔ Uniformity.Density.Tower.NS7TerminationStatementR := Iff.rfl
example (n : ℕ) (h : CapstoneHypotheses.{uW, uG, uKt, uL} n) : NS7Termination := h.ns7

-- (15) **[A-I.3] anti-drift pins: the socket bodies ARE chapter C's enacted I.10a/I.10b
-- data-carriers, DEFINITIONALLY** (`Iff.rfl` — fails the build the moment either side drifts;
-- the A-I.2 `deepTwistConjunctLive_iff` pattern). The deep-twist pin also certifies that the
-- frozen refinement shape (first conjunct literally `CanonicalLadderConfig`) reassembles
-- C130s18's `CanonicalDeepTwistConfigData` on the nose.
example {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ) (n : ℕ) :
    CanonicalLadderConfig C B G Kt L N v ρ q n ↔
      Uniformity.Density.Tower.C130s18.CanonicalLadderConfigData.{0, uG, uKt, uL}
        C B G Kt L N v ρ q n := Iff.rfl
example {O : Type} [CommRing O] {K : Type} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
    (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r n : ℕ) :
    CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n ↔
      Uniformity.Density.Tower.C130s18.CanonicalDeepTwistConfigData.{0, uG, uKt, uL}
        C B G Kt L N v ρ q A R w r n := Iff.rfl

section AThreeTeeth
open Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s17 Uniformity.Density.Tower.C130sg

-- (16) **[A-I.3] NON-VACUITY of the typed I.10a socket at the arising S2 instance** (the
-- A-E.2 certification standard: a re-sign ships a witness genre). The landed SG-1 stage-4a
-- application (`C130sg.s2Frontier_ladder_socket`, `ev`/`lf`-FREE per PK-2/U15) inhabits the
-- re-signed socket at the concrete `keyAt 2 + 1` occurrence, degree 4, conditional on exactly
-- `w : S2LevelOneThreshold` (the one open faithfulness datum) + `IsAdicComplete` — no
-- provably-empty premise anywhere on the path.
example {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (L : Type uL) [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (w : S2LevelOneThreshold) :
    CanonicalLadderConfig
      ((s2Frontier h2 hq L w).s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      ((s2Frontier h2 hq L w).s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      ((s2Frontier h2 hq L w).toCarrier.normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (canonicalResFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (useHeightFamily (s2Frontier h2 hq L w).s2RealizedInput) 4 :=
  s2Frontier_ladder_socket h2 hq L w

-- (17) **[A-I.3] NON-VACUITY of the typed I.10b socket at the same instance**, depth binder
-- pinned to the witness's own `r = 2` (the A-I.2(b) rule, machine-real via the joint witness's
-- `core.r = r` conjunct) — `C130sg.s2Frontier_deepTwist_socket`, same exact conditionality.
example {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)]
    (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)
    (L : Type uL) [Field L] [Algebra ((S2DepthTwo h2 hq).fld 2) L]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (w : S2LevelOneThreshold) :
    CanonicalDeepTwistConfig
      ((s2Frontier h2 hq L w).s2RealizedInput.stageCarrierTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      ((s2Frontier h2 hq L w).s2RealizedInput.inputBlockTransport
        (RingEquiv.refl ((S2DepthTwo h2 hq).fld 2)))
      (GaugeLattice.{uG} 2) ((S2DepthTwo h2 hq).fld 2) L
      ((s2Frontier h2 hq L w).toCarrier.normalizer.arenaNormSection0.transport
        (gaugeLatticeEquiv 2).symm)
      (gaugeHeightFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (canonicalResFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (useHeightFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (arenaFamily (s2Frontier h2 hq L w).s2RealizedInput Nat.one_lt_two)
      (towerReadFamily (s2Frontier h2 hq L w).s2RealizedInput)
      (s2Frontier h2 hq L w).toCarrier.node.peelUnitFamily 2 4 :=
  s2Frontier_deepTwist_socket h2 hq L w

end AThreeTeeth

end GateFour

/-! ## §4.3 — NODE I.11 [note] — THE `AllOInterfaces` RECONCILIATION (NO LEAN FILE)

Honesty I-10: in Lean, all-`O` generality is not an assumption but the statement form itself, so
Display A's final conjunct is a **signed structural disposition**, not a field — "the informal
corpus's uses are characteristic-general" is not a statable `Prop`. The 14 names terminate as:
GENIND-1 (HYP.121) ∀`O`-free by form, H.93/H.94; RMG (122), GRB (124), ITER-LAW (125) out of cut
(`EXT:` notes, no import to generalize); ILN (123) consumers out of cone, residual rides
HYP.148's ∀`O` carrier; W/J (126), DU (127), W-10 (128) consumers out of cone / pricing-only;
J-D0 (129) the ∀`O` binder of F's carrier statement — **now landed and checkable**, see §4 gate
check (6); L2core (130), HUMAN_PROOF (131), local-integrals (132) quarry-side / Q7 route
exclusion; CONV (133) `leanfinal` is monic-native; GENHN-count (134) H §7's ∀`O` statements at
`μ = 2`. GC-8's rider-(iii) sanity check passes for these 14 — and the §12 summary sentence ("nothing
else on the frozen display lacks a carrier ✓"), which was FALSE at this gate because `𝒲_{≤i}`
lacked a carrier (defect I-D4), is struck-and-corrected in the blueprint by A-I.1: with the
`deepTwist` field signed, the Display-A content without a typed field is `AllOInterfaces`
(signed non-applicability) plus the two weld placeholders and the `w1` debt (A-I.1 §I-D7/§I-D8)
— named exceptions, which is the honest form of the row.

## §5 — THE COND RESOLUTIONS (I.12–I.14, all [note], NO LEAN FILES)

* **I.12 — `COND:A2_n` RESOLVED.** `A2_n` IS ledger row HYP.27's content and its carrier is
  LANDED: `Uniformity.Density.DrainageAt n`. `n = 1, 2` PROVED (`drainage_one`, `drainage_two`);
  `n = 3` open (HYP.08/09 frontier); `n ≥ 4` open via H.98 ⇐ `InductionPackage`. The 0c matcher
  missed it on a name-form technicality ("`A2` drainage", no `_n`).
* **I.13 — `COND:A1_n` RESOLVED.** `A1_n` IS HYP.26's content; its carrier is I.03 (`MenuLawAt`),
  typed against H.93's landed `A1Cell`/`A1Family`. ⚠ This resolution is weaker than it reads:
  defect I-D9 shows the `A1Family` leg of `MenuLawAt` is vacuous, so what I.13 actually resolves
  today is the MENU clause, not the `(A1)`-admissible SHAPE.
* **I.14 — `COND:H-e)-window-pinning` RESOLVED.** The conjunct IS HYP.24's pinning half (the v4
  SUPPLIER RE-SOURCED block is the authority: `LEMMA GENHN-3` + GENIND-2's consulted-height
  bound, NOT the off-route `(H-a)`/`(H-b)` leg). Carriers: I.05 + H.89 (`e₁ = 2`) +
  `StageInterface.hwin` (carried, per-genre). Supplier gap narrowed by OM-6's landed `H89w.lean`
  and NOT closed (`hwin` undischarged) — orchestrator item O-2 is DISCHARGED as an orchestration
  item, the mathematics is not.

## §6 — THE ASSEMBLY (I.15–I.20)

Section contract, transcribed: everything here is bookkeeping (honesty I-1) — projections of
I.10 and applications of landed `UniformityStatement.ofDecided` / `totalMassOne_of_drainage` and
committed `uniformity_of_package` (H.98). **No theorem in this section makes the capstone less
conditional; each makes the conditionality machine-readable.** Per blueprint §11 these four land
REAL, not as `axiom`s — their proofs are projections and one term application. -/

/-- **I.15** — the drainage projection. -/
theorem drainage_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : ∀ n, DrainageAt n :=
  fun n => (h n).a2

/-- **I.16** — the decided-target projection. The content: the `a0` fields ARE the degree-slices
of the decided target, so re-indexing is the whole proof. This is where the count layer's
openness is made visible — nobody can supply `∀ n, CapstoneHypotheses n` today precisely because
`a0`/`a1` are open at `n ≥ 3`.

The one-line `exact` closes because I.02's body was COPIED from the landed target's body rather
than re-typed; the `Iff.rfl` pin in the §6 gate is the standing regression on that copy. -/
theorem decided_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : UniformityStatementDecided := by
  intro n _hn σ hσ
  exact (h n).a0 σ hσ

/-- **I.17 — THE HONEST CAPSTONE ASSEMBLY.** `UniformityStatement` follows from the ledger's
frozen hypothesis block and nothing else. What remains open is exactly the block's fields: see
the chapter-I disposition table (§3, 36 OPEN-MATH rows + the gate-(b) cites).

**This proves no mathematics** (honesty I-1). Its value is the footprint: every open input is a
HYPOTHESIS, never an axiom, so this declaration's `#print axioms` is Lean-core — printed at
gate I.24. -/
theorem uniformity_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : UniformityStatement :=
  UniformityStatement.ofDecided (drainage_of_capstoneHypotheses h)
    (decided_of_capstoneHypotheses h)

/-- **I.18** — `TotalMassOne`, not double-counted: from the same structure, via the `a2` fields
and landed `totalMassOne_of_drainage` ONLY (honesty I-4 — the mass law is the drainage leg
wearing a different hat and gets no field of its own). -/
theorem totalMassOne_of_capstoneHypotheses
    (h : ∀ n, CapstoneHypotheses.{uW, uG, uKt, uL} n) : TotalMassOne :=
  totalMassOne_of_drainage (drainage_of_capstoneHypotheses h)

/-! ### §6 GATE (executed) -/

section GateSix

-- (1) **THE LITERAL-SLICE PIN (I.02 ⟷ the landed target).** `UniformityStatementDecided` IS
-- `∀ n, 0 < n → DecidedSliceAt n`, on the nose. This `Iff.rfl` fails the build the moment either
-- body drifts by so much as an instance order — the standing regression behind I.16's `exact`.
example : UniformityStatementDecided ↔ ∀ n : ℕ, 0 < n → DecidedSliceAt n := Iff.rfl

-- (2) **DEFECT I-D10, machine-visible in the same pin.** The landed target guards its body with
-- `0 < n`; `CapstoneHypotheses n`'s `a0` does not, so `∀ n, CapstoneHypotheses n` demands
-- `DecidedSliceAt 0` — a law the capstone never asks for. (`a2`'s `DrainageAt 0` IS required:
-- landed `ofDecided` takes `∀ n, DrainageAt n`, as the `#check` records.)
#check @Uniformity.Density.UniformityStatement.ofDecided

-- (3) **NODE I.19 [note] — THE PACKAGE ROUTE, consumed by name and NOT re-exported.** CHAP-H's
-- committed pair is landed; the one-public-declaration discipline forbids a verbatim re-export
-- (that adds a name, not content), so the note is a `#check`. `package_two` is UNCONDITIONAL
-- (H.96, a chapter-G payoff); `package_three_of_rate` is H.97's ADOPTED form —
-- `package_three_of_drainage` is DECLARED UNPROVABLE by H.97's own ⚠ and must not be assigned.
-- ⚠ THE GENIND.B FENCE APPLIES IN FULL (honesty I-2): no node here or anywhere composes
-- `InductionPackage n` for `n ≥ 4`.
#check @Uniformity.Density.drainage_of_package
#check @Uniformity.Density.uniformity_of_package
#check @Uniformity.Density.package_two
#check @Uniformity.Density.package_three_of_rate

end GateSix

/-! ### NODE I.20 [note] — THE STAGE DISPLAY (NO LEAN FILE)

The honest "capstone modulo …" statement at each stage, for the record and for §12's teeth.

| stage | fires | modulo (named) |
|---|---|---|
| **S0 — today, landed** | `n = 1` drainage + total mass; `n = 2` drainage, total mass, the exact densities, THE CAPSTONE SLICE; the `q = 2, 3` instances | nothing — unconditional, Lean-core |
| **S1 — chapters B–H land** | leaf layer, schema, rate calculus, `package_two`, the σ-μ2 chain, order-1 count laws | the gate-(b) cites where consumed (B.42 signed; C.66/C.94 REDRAFTED, unsigned; C.92 RETIRED) |
| **S2 — the `n = 3` frontier closes** | `DrainageAt 3` (H.97 + H.98), cubic total mass unconditionally | `hrate₃` (HYP.08) + the cubic value layer (HYP.11/28/29) |
| **S3 — the open surface** | `UniformityStatement` via I.17 | **exactly the A-I.1 field list** — §3's 36 OPEN-MATH rows + the CITEs, **plus chapter I's own two untyped sockets** (I.10a/I.10b) |

**No stage claims more than its row.** ⚠ The S3 row was doubly wrong as composed and is
struck-and-corrected in the blueprint by A-I.1: (i) "exactly the §4 field list" was SHORT of
Display A by one conjunct (`𝒲_{≤i}`, defect I-D4 — now carried by `deepTwist`); (ii) the
report sentence called I.17 an EQUIVALENCE, which it never was (one direction only). And while
the I.10a/I.10b sockets read `True`, the block is contradictory (I-D13), so **no positive
conditional claim may be made from I.17 at all** — the honest S3 sentence is A-I.1's, quoted in
the blueprint at NODE I.20.

## §7 — THE `typeOf` FAITHFULNESS BRIDGE AND THE CORE-SET AUDIT LEDGER (I.21–I.22)

### NODE I.21 [def] — `TypeOfFaithful`, the trust-boundary bridge statement.
Lands `Uniformity.Density.TypeOfFaithful`. ENV-I1.

⚠ BLOCKED-UNTIL-RESOLUTION (defect I-D12), and STILL BLOCKED at HEAD: typing the body needs the
factor-field valuation-ring carrier — the object B.56's OPTIONAL repair route would build — and
it does not exist in the tree. OM-5 §3.1 sharpens why: at every `d ≥ 2` leaf the order
`AdjoinRoot g` has residue field of degree `m < m·d`, hence is never a DVR, so that region lies
entirely OFF the monogenic-maximal locus the landed `Density/TypeOfFaithful.lean` reaches. -/

-- The signed body is the bare `True` placeholder (the node is BLOCKED-UNTIL-RESOLUTION);
-- nothing about the two APIs is asserted, which is the point of GC-3's KEPT-APART rule.
/-- **THE TRUST BOUNDARY, NAMED** (ledger HYP.01 [CORE-SET] + HYP.105; GC-3's kept-apart rule):
`typeOf`'s gcd multiset (over the ORDER `AdjoinRoot g`) agrees on the `disc ≠ 0` locus with the
ideal-theoretic `(e, f)` multiset (over the maximal order/DVR), in the primed rank-form
generation. **NO chapter may silently identify the two APIs** (GC-3); a node needing the
identification hypothesizes THIS name or returns `BLOCKED: HYP.01`.

⚠ STUB-STAGE BODY (BLOCKED-UNTIL-RESOLUTION): the real body quantifies over the bundle and monic
`f` with `disc f ≠ 0`, and equates `(typeOf f).data` with the maximal-order multiset via
`Ideal.ramificationIdx'`/`inertiaDeg'`. FROZEN HERE: name, locus, both APIs by name. -/
def TypeOfFaithful : Prop :=
  True

/-! ### NODE I.22 [note] — THE CORE-SET AUDIT LEDGER A-1 … A-7 (NO LEAN FILE)

Under Part V item 2, cite/def-faithfulness rows stay gate-(b)-adjacent HUMAN reads; the rest are
absorbed into the standing fresh-eyes cadence. **No audit row is a fleet node.**

| id | row(s) | object | class | when |
|---|---|---|---|---|
| A-1 | HYP.01, HYP.105 | `typeOf` faithfulness — review I.21's statement against the classical `(e,f)` multiset | gate-(b)-adjacent, human | before any node hypothesizes `TypeOfFaithful` |
| A-2 | HYP.12 | `(e,f)` ordering/multiset normalization vs the classical convention | rides A-4 | with A-4 |
| A-3 | HYP.17 | [AGNPRW]/[GN15]/[FGMN]/Kuhlmann publisher numbering | gate-(b)-adjacent (cite) | **DONE for all three C-side cites** (A-C.1/A-C.6); residual print-reads are the owner's closing checks |
| A-4 | HYP.98 | the core set: the types, `UniformityStatement`, the two densities, the cites, changed-definition faithfulness paragraphs | RECURRING fresh-eyes | at chapter milestones; **next at this gate's findings** |
| A-5 | HYP.111 (def half) | what `decidedDensity` counts | rides A-4 | with A-4 |
| A-6 | (I.10) | the field list of `CapstoneHypotheses` vs frozen Display A — one-to-one, nothing added, nothing dropped | fresh-eyes, decorrelated arm | **FIRED at the 0e gate — NOT one-to-one: I-D4 (`𝒲` dropped), I-D7/I-D8 (`jd0`/`genhnBox2` placeholders, no `w1`), I-D9 (`a1` vacuous), I-D10 (`a0` over-demanded at n = 0). A-I.1 CLOSES I-D4 (field added) and I-D9 (clause re-signed), RULES I-D7/I-D8 (named debt at the weld socket), leaves I-D10 open, and ADDS I-D13 (the fields are refutable). Re-fire after the I.10a/I.10b sockets are typed.** |
| A-7 | HYP.91 | OB-a…OB-d representation vs CHAP-H's committed text | bounded, one pass | at the H stub stage |
-/

/-! ## §8 — THE GATES (I.23–I.25), EXECUTED

**Arena note.** Chapter I owns no mathematics, so its gates are the teeth (GC-8's own
battery-inheritance row: "I: no batteries — its teeth are the gate nodes"). Three of them: the
unconditional `n ≤ 2` re-fire (I.23), the maintained AXCHK census (I.24), and the cite-footprint
gate (I.25). GC-11 compliance for I.23: **two primes ✓** (`q = 2` and `q = 3`); the
`e > 1 ∧ f > 1` witness clause is **signed non-applicable at `n = 2`** and the reason is
executed below rather than asserted (a degree-2 type has `e·f = 2`).

**The AXCHK guard is EXECUTED, not eyeballed.** `#print axioms` prints a line a human must read;
this file installs `#axiom_core`, which *fails the build* when a constant's footprint leaves
`{propext, Classical.choice, Quot.sound}`. That turns REVISION 2's "maintained, diffable census"
into a maintained, self-enforcing one: a footprint regression anywhere on the capstone-facing
surface is a red build here, which is what the repo's stop-the-line rule wants. -/

section Gates

open Lean Elab Command in
/-- **The AXCHK primitive (I.24/I.25).** `#axiom_core foo` fails the build unless `foo`'s axiom
footprint is EXACTLY Lean core `{propext, Classical.choice, Quot.sound}`. With the gate-(b)
registry currently EMPTY (no cite axiom is landed in `leanfinal`; B.42 is signed but unlanded,
C.66/C.94 are REDRAFTED and unsigned, C.92's axiom is RETIRED), "Lean core exactly" IS I.25's
clause (i) AND its clause (iii) forbidden-list check — `AX_cellRecursion`, `Lean.ofReduceBool`
and every unsigned axiom are excluded by the same test. When a cite lands, its consumers move to
`#axiom_reg` below. -/
elab "#axiom_core " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let ax ← liftCoreM <| collectAxioms n
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AXCHK FAIL (I.25 clause (i)/(iii)): {n} depends on non-core axioms {bad.toList}"

open Lean Elab Command in
/-- **I.25 clause (ii), the cite-conditional form.** `#axiom_reg foo [a, b]` fails the build
unless `foo`'s footprint is Lean core PLUS a subset of the named registry — the honest carrier
the ledger wants ("the conditionality is IN the axiom dependency", C.67's pattern). The registry
at composition time is **empty**, so no declaration uses this form yet; expected first entries
are C.94's `agnprw_termination` (at the A-C.6 REDRAFT `NS7TerminationStatementR`) and C.66's FGMN
axiom (at the REDRAFT `FgmnResidualMulStatement`), plus B.42's `[GN15]+[FGMN]` axiom on landing.
⚠ Defect I-D11: this gate is BLIND to C.92's route, which A-C.6 converted from an axiom to
hypothesis-form — an unsupplied `[FGMNCalculus …]` instance is invisible to `collectAxioms`. -/
elab "#axiom_reg " id:ident " [" reg:ident,* "] " : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let ax ← liftCoreM <| collectAxioms n
  let mut allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for r in reg.getElems do
    allowed := allowed.push (← liftCoreM <| realizeGlobalConstNoOverload r)
  let bad := ax.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "AXCHK FAIL (I.25 clause (ii)): {n} depends on unregistered axioms {bad.toList}"

/-! ### NODE I.23 [gate] — THE UNCONDITIONAL-SLICE GATE (`q = 2` AND `q = 3`)

(i) footprints of the landed unconditional set; (ii) chapter G's landed `n = 2` values re-fired
as regression anchors, with the expected numbers EXECUTED rather than commented; (iii)
non-vacuity witnesses for I.02's and I.03's `n = 2` instances. -/

-- (i) the landed unconditional set: every one Lean-core, enforced.
#axiom_core Uniformity.Density.drainage_one
#axiom_core Uniformity.Density.totalMass_one
#axiom_core Uniformity.Density.drainage_two
#axiom_core Uniformity.Density.totalMass_two
#axiom_core Uniformity.Density.coveringMenu_two
#axiom_core Uniformity.Density.coveringMenu_three
#axiom_core Uniformity.Density.genuineDensity_two_exact
#axiom_core Uniformity.Density.uniformityStatement_two
#axiom_core Uniformity.Density.gate_two_padic_two_exact
#axiom_core Uniformity.Density.gate_two_padic_three_exact

-- (ii) the `q = 2` anchor triple `(1/3, 1/3, 1/3)`.
example : genuineDensity ℤ_[2] 2 splitType = 1 / 3 := gate_two_padic_two_exact.1
example : genuineDensity ℤ_[2] 2 inertType = 1 / 3 := gate_two_padic_two_exact.2.1
example : genuineDensity ℤ_[2] 2 ramType = 1 / 3 := gate_two_padic_two_exact.2.2
-- the `q = 3` anchor triple `(3/8, 3/8, 1/4)` — a NON-uniform triple, so the two primes really
-- separate (had the gate run at `q = 2` alone, a "all types equally likely" bug would survive).
example : genuineDensity ℤ_[3] 2 splitType = 3 / 8 := gate_two_padic_three_exact.1
example : genuineDensity ℤ_[3] 2 inertType = 3 / 8 := gate_two_padic_three_exact.2.1
example : genuineDensity ℤ_[3] 2 ramType = 1 / 4 := gate_two_padic_three_exact.2.2
-- the exact `n = 2` drainage law `undecidedCount O 2 N = q^N` (G.36), at both primes and at the
-- blueprint's three spot values `(q, N) = (2,1) ↦ 2`, `(2,3) ↦ 8`, `(3,2) ↦ 9`.
example : undecidedCount ℤ_[2] 2 1 = 2 := by rw [undecidedCount_two_eq]; simp [residueCard_padicInt]
example : undecidedCount ℤ_[2] 2 3 = 8 := by rw [undecidedCount_two_eq]; simp [residueCard_padicInt]
example : undecidedCount ℤ_[3] 2 2 = 9 := by rw [undecidedCount_two_eq]; simp [residueCard_padicInt]

-- GC-11's `e > 1 ∧ f > 1` witness clause: SIGNED NON-APPLICABLE at `n = 2`, and the reason is
-- executed rather than asserted. The meaningful witnesses live in B/C/E's gates (e.g. B.85),
-- whose footprints I.24 re-prints on landing.
example : ∀ e f : ℕ, e * f = 2 → ¬ (1 < e ∧ 1 < f) := by
  rintro e f hef ⟨he, hf⟩
  have h4 : 2 * 2 ≤ e * f := Nat.mul_le_mul he hf
  rw [hef] at h4
  omega

-- (iii) NON-VACUITY of the `a0` field at `n = 2`: `DecidedSliceAt 2` is PROVED outright, from
-- chapter G's landed `uniformityStatement_two` through the landed `n = 2` drainage tie
-- `genuineDensity_eq_decidedDensity_two`. This is the field's witness that it says something.
example : DecidedSliceAt 2 := by
  intro σ hσ
  obtain ⟨num, den, hden, hlaw⟩ := uniformityStatement_two σ hσ
  refine ⟨num, den, hden, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨h1, h2⟩ := hlaw O
  exact ⟨h1, by rw [← genuineDensity_eq_decidedDensity_two]; exact h2⟩

-- NON-VACUITY of the `a1` field at `n = 2`: `MenuLawAt 2` is PROVED from `coveringMenu_two`,
-- **at A-I.1's re-signed (enumerating) carrier** — so the witness now has to EXHIBIT a family
-- whose σ-labels run over the whole menu, which the 0e gate's empty-list witness could not.
-- ⚠ WHAT THIS DOES AND DOES NOT CERTIFY: the three cells carry the σ-labels and nothing else
-- (r = 0, so the locus/exponent/coefficient data is trivial). The label ENUMERATION is
-- certified; the WEIGHT-correctness tie (I.03's ⚠ SIGNATURE NOTE, §3 rows HYP.23/32/35) is
-- still not in the carrier and is not certified by anything here.
private def a1LabelCell (σ : FactorizationType) : Induction.A1Cell 0 where
  offset := fun i => i.elim0
  stride := fun i => i.elim0
  stride_pos := fun i => i.elim0
  expCoeff := fun i => i.elim0
  expCoeff_pos := fun i => i.elim0
  expConst := 0
  visCoeff := fun i => i.elim0
  visConst := 0
  coeff := 1
  σ := σ

example : MenuLawAt 2 := by
  refine ⟨0, [a1LabelCell splitType, a1LabelCell inertType, a1LabelCell ramType],
    {splitType, inertType, ramType}, ?_, ?_, ?_, ?_⟩
  · intro C hC
    simp only [id_eq, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with h | h | h <;> subst h <;> simp [a1LabelCell]
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h <;> subst h
    · exact ⟨a1LabelCell splitType, by simp, rfl⟩
    · exact ⟨a1LabelCell inertType, by simp, rfl⟩
    · exact ⟨a1LabelCell ramType, by simp, rfl⟩
  · intro σ hσ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
    rcases hσ with h | h | h <;> subst h
    exacts [splitType_degree, inertType_degree, ramType_degree]
  · intro O _ _ _ _ _
    exact coveringMenu_two

/-! ### NODE I.24 [gate] — **AXCHK: THE MAINTAINED INTERFACE CENSUS**

REVISION 2's planned artifact, composed here as an ENFORCED census: every exported
capstone-facing interface of `leanfinal`, guarded Lean-core.

**Location decision, recorded and CHANGED at this gate.** The blueprint proposes
`leanfinal/AXCHK.lean` with a pointer at `spec/`. That is not composable at HEAD: defect I-D1
means a `leanfinal` module cannot import both `Uniformity` and the chapter-E Display-A carriers,
so a `leanfinal`-side census cannot cover the `ladder` field's supply. The census therefore
lives HERE (in `leanspec`, which is allowed to pick its import set) until I-D1 is cured; the
committed diffable OUTPUT still belongs under `spec/` and remains the orchestrator's to emit.

**Maintenance rule (unchanged).** Every chapter's stub-gate agent APPENDS its chapter's terminal
names on landing — this block is the one place the whole trusted surface is greppable. -/

-- the `Statement.lean` API: both CAP targets and every cross-implication
#axiom_core Uniformity.Density.UniformityStatement
#axiom_core Uniformity.Density.UniformityStatementDecided
#axiom_core Uniformity.Density.UniformityStatementPadic
#axiom_core Uniformity.Density.UniformityStatement.ofDecided
#axiom_core Uniformity.Density.UniformityStatement.toDecided
#axiom_core Uniformity.Density.UniformityStatement.toPadic
#axiom_core Uniformity.Density.DrainageAt
#axiom_core Uniformity.Density.TotalMassOne
#axiom_core Uniformity.Density.totalMassOne_of_drainage
-- the density / drainage layer
#axiom_core Uniformity.Density.genuineDensity
#axiom_core Uniformity.Density.decidedDensity
#axiom_core Uniformity.Density.CoveringMenu
#axiom_core Uniformity.Density.genuineDensity_eq_of_drainage
#axiom_core Uniformity.Density.sum_genuineDensity_eq_one_of_drainage
#axiom_core Uniformity.Density.one_le_sum_genuineDensity
#axiom_core Uniformity.Density.typeOf
-- chapter G's terminal supplies (the rest are re-fired at I.23)
#axiom_core Uniformity.Density.undecidedCount_two_eq
#axiom_core Uniformity.Density.undecidedSeq_two_eq
#axiom_core Uniformity.Density.totalMass_three_of_drainage
#axiom_core Uniformity.Density.one_le_sum_three
#axiom_core Uniformity.Density.card_le_undecidedCount_three
-- chapter H's terminal supplies (the assembly spine + the `(A1)` schema)
#axiom_core Uniformity.Density.InductionPackage
#axiom_core Uniformity.Density.package_two
#axiom_core Uniformity.Density.package_three_of_rate
#axiom_core Uniformity.Density.drainage_of_package
#axiom_core Uniformity.Density.uniformity_of_package
#axiom_core Uniformity.Density.Induction.A1Cell
#axiom_core Uniformity.Density.Induction.A1Family
-- chapter E's Display-A carriers (the `ladder` field's supply, at the A-E.2/A-D.2 forms)
#axiom_core Uniformity.Density.Ladder.LadderSupply
#axiom_core Uniformity.Density.Ladder.LB1Carrier
#axiom_core Uniformity.Density.Ladder.MP1Carrier
#axiom_core Uniformity.Density.Ladder.VarthetaRes
#axiom_core Uniformity.Density.Ladder.WFrame
#axiom_core Uniformity.Density.Ladder.DeepTwistConjunctLive
#axiom_core Uniformity.Density.Gauge.HVarthetaRes
-- chapter F's Display-A carriers (I.08/I.09's L-1/L-2 targets)
#axiom_core Uniformity.Density.Weld.JD0Box2
#axiom_core Uniformity.Density.Weld.GenhnBox2
#axiom_core Uniformity.Density.Weld.W1Transport
-- chapter C's landed census leg
#axiom_core Uniformity.Density.Tower.tower_first_live
-- the landed discharge set named in the §3 disposition table
#axiom_core Uniformity.Hensel.strongHensel
#axiom_core Uniformity.Hensel.exists_monic_factorization_finset
#axiom_core Uniformity.Density.typeOf_shift
#axiom_core Uniformity.Density.typeOf_scaleRoots
#axiom_core Uniformity.Density.typeOf_scale
#axiom_core Uniformity.Density.exists_anisotropic
-- **THIS CHAPTER'S OWN TERMINAL SUPPLIES (I.15–I.18).** I.17's Lean-core footprint IS the design
-- point (I.17's TEETH row): every open input is a HYPOTHESIS, never an axiom, so the capstone
-- assembly adds nothing to the trusted base.
#axiom_core LeanspecI.drainage_of_capstoneHypotheses
#axiom_core LeanspecI.decided_of_capstoneHypotheses
#axiom_core LeanspecI.uniformity_of_capstoneHypotheses
#axiom_core LeanspecI.totalMassOne_of_capstoneHypotheses
-- and this chapter's carriers, so a later resolution pass cannot smuggle an axiom into a `Prop`
#axiom_core LeanspecI.NS7Termination
#axiom_core LeanspecI.DecidedSliceAt
#axiom_core LeanspecI.MenuLawAt
-- A-I.1's three additions: the voided I.03 copy (kept for its refutation) and the two
-- arising-configuration sockets. A socket typed with an axiom would be a silent trusted-base
-- change; these three lines fail the build if that ever happens.
#axiom_core LeanspecI.MenuLawAtVoided
#axiom_core LeanspecI.CanonicalLadderConfig
#axiom_core LeanspecI.CanonicalDeepTwistConfig
-- A-I.5's two additions: the signed GC-13 wiring law and the wired per-level demand.
#axiom_core LeanspecI.GC13Wiring
#axiom_core LeanspecI.WiredGentowDemand
#axiom_core LeanspecI.WindowPinningAt
#axiom_core LeanspecI.GenhnHEAt
#axiom_core LeanspecI.GenhnTow1At
#axiom_core LeanspecI.CapstoneHypotheses
#axiom_core LeanspecI.TypeOfFaithful

/-! ### NODE I.25 [gate] — THE CITE-FOOTPRINT GATE

Axiom hygiene under Part V: Lean core plus exactly the signed cites, nowhere else.

* **clause (i)** — every declaration NOT downstream of a gate-(b) import prints exactly Lean
  core. Enforced: that is what all 67 `#axiom_core` lines above assert, and the guard THROWS
  rather than prints.
* **clause (ii)** — every cite-conditional declaration prints Lean core plus exactly its signed
  cite axioms. The `#axiom_reg` form above is the enforcement shape; **the signed registry at
  composition time is EMPTY**, so it has no call sites yet. Expected first entries: C.94's
  `agnprw_termination` at the A-C.6 REDRAFT, C.66's FGMN axiom at the A-C.6 REDRAFT, B.42's
  `[GN15 Thm 2.3 + FGMN Thm 6.6]` axiom. ⚠ **Defect I-D11**: C.92's route left the axiom world
  at A-C.6 (option (1): `fgmn_calculus_exists` RETIRED, the class kept as a hypothesis carrier,
  "C.92 EXITS the gate-(b) queue"), so orchestrator item **O-4 is MOOT** — and the sixteen
  `[FGMNCalculus …]`-conditional §10 theorems are now conditional in a way `collectAxioms`
  cannot see. A hypothesis-form cite is invisible to this gate BY CONSTRUCTION; the honest
  compensating control is the instance-supply census, not the axiom census.
* **clause (iii)** — the FORBIDDEN list (`AX_cellRecursion`-family, quarry-quarantined under Q7;
  `Lean.ofReduceBool`, i.e. `native_decide`, stop-the-line per H.99's precedent; and any axiom
  not in the signed registry) is enforced by the SAME test, since with an empty registry
  "Lean core exactly" excludes all of them. The self-test below shows the guard has teeth. -/

-- The guard's own self-test: a deliberately non-core constant must be REJECTED. It is declared
-- and immediately fenced — nothing in this file or any other consumes it, and it is the only
-- `axiom` chapter I writes anywhere.
private axiom axchkSelfTestAxiom : True
private theorem axchkSelfTestConsumer : True := axchkSelfTestAxiom
-- If `#axiom_core LeanspecI.axchkSelfTestConsumer` is uncommented the build FAILS with
-- "AXCHK FAIL (I.25 clause (i)/(iii)): … depends on non-core axioms [axchkSelfTestAxiom]".
-- That is the gate's positive control, verified at composition (2026-08-16) and left commented
-- so the file stays green:
-- #axiom_core LeanspecI.axchkSelfTestConsumer
-- The registry form's behaviour on the same constant, also verified and left commented:
-- #axiom_reg LeanspecI.axchkSelfTestConsumer [axchkSelfTestAxiom]   -- PASSES (registered)
-- #axiom_reg LeanspecI.axchkSelfTestConsumer []                     -- FAILS  (unregistered)

end Gates

end LeanspecI

/-!
## RESUME

**LSPEC-I stage 0e COMPLETE (2026-08-16), THEN AMENDED BY A-I.1 (2026-08-16, same day).** All 25
blueprint nodes plus A-I.1's two new socket nodes are landed here: **14 signed declarations**
(9 `def` + 1 `structure` real bodies + 4 `theorem`s landed REAL per §11), one NAMED-AND-VOIDED
`def` (`MenuLawAtVoided`, kept for its refutation), **zero `axiom` stubs** (the one `axiom` in
the file is I.25's fenced positive control), zero `sorry`, zero `native_decide`, `autoImplicit`
off, the §8 gates EXECUTED at `q = 2` AND `q = 3` (the `(1/3, 1/3, 1/3)` and `(3/8, 3/8, 1/4)`
triples, the three `undecidedCount` spot values, the `e > 1 ∧ f > 1` non-applicability proof,
and the two `n = 2` non-vacuity witnesses `DecidedSliceAt 2` / `MenuLawAt 2` PROVED — the latter
now at a REAL three-cell labelled family), plus an **enforced** AXCHK census of 70
capstone-facing constants, all Lean-core. Build: `lake build Leanspec.ChapI` (green).

**What A-I.1 changed here** (blueprint side: `blueprint/CHAP-I_capstone_conditionality.md`,
AMENDMENT A-I.1 block):

1. **I.10's field list** — the `ladder` field re-signed (E.24's repaired application, guarded by
   the new I.10a socket `CanonicalLadderConfig`), and a NEW `deepTwist` field consuming E.63's
   `DeepTwistConjunct` (both halves of Display A's `∀ i ≥ 3` conjunct, guarded by I.10b). Owner
   gate-(a) event, flagged.
2. **I.03 re-signed** at the two-directional σ-label enumeration (I-D9), with the vacuous form
   kept as `MenuLawAtVoided` and its refutation preserved verbatim; the `@id` membership
   spelling signed (I-D5).
3. **I.01's resolution instruction re-pointed** at the A-C.6 REDRAFT
   `LeanspecC.NS7TerminationStatementR`, owner gate-(b) pending; the refuted A-C.1 route struck
   at both blueprint sites, text kept (I-D6).
4. **I-D7/I-D8 ruled**, not signed: the weld carriers' `∀`-over-all-sites shapes are refutable,
   so the placeholders stay and the missing `w1` field becomes a named debt at a weld
   site-supply socket.

**THE ONE THING A READER MUST TAKE AWAY (defect I-D13).** The capstone hypothesis block is
**contradictory today**: the Display-A carrier fields quantify over all configurations, and the
carriers are certified false at concrete legal ones, so `CapstoneHypotheses n` is uninhabited
and I.15–I.18 fire from `False`. A-I.1 installs the binding site (the two sockets) and proves
that installing it weakens nothing today; **the contradiction lifts only when chapter C types
the sockets.** Until then: I.10 is an elaboration gate, not a signature; no fleet agent fires on
it; and no report makes a positive conditional claim from I.17.

**Remaining external actions:** (i) `import Leanspec.ChapI` is wired into
`leanspec/Leanspec.lean` **as a COMMENTED line with its reason** — wiring it live breaks
`lake build Leanspec` outright, because the root imports `Uniformity` (the D62w branch) and this
file must reach the E-side carriers (the D63 → D55 branch); machine-checked at the 0e gate. One
uncommenting restores the standing gate the moment I-D1 is cured; (ii) I-D1's `leanfinal` cure,
then the ChapE/ChapF roll-up repairs of I-D2, then this file's import block reverts to the
one-line `import Uniformity` every other chapter uses; (iii) ~~**chapter C types I.10a/I.10b**
(the GC-13/GC-14 pass that typed E.61/E.62), under A-I.1's NON-SWALLOWING fence — this is the
item that repairs I-D13~~ **DONE AT AMENDMENT A-I.3 (2026-08-26)**: chapter C's packaging
enactment (PK-1..6, `runs/wave-b/verdict_PK12.md`) landed the bodies as
`C130s18.CanonicalLadderConfigData`/`CanonicalDeepTwistConfigData`, and A-I.3 re-signs the two
socket bodies at exactly those carriers (ambient universe pinned to `0`; fence checked against
C130s18's mechanized non-swallowing audit; gate items (10)/(11) struck/retired, (15)–(17)
added; the I-D13 refutation route is CLOSED — the block is OPEN, not claimed inhabited; the
narrowing is the gate-(a) event A-I.1 pre-flagged, re-flagged in
`docs/REVIEW_QUEUE_2026-08-26.md`'s amendment table); (iv) the weld site-supply socket, then L-1/L-2 bind `jd0`,
`genhnBox2` and `w1`; (v) the gate-(b) signatures for the C.66/C.94 REDRAFTS, after which their
consumers move from `#axiom_core` to `#axiom_reg`; (vi) the owner's read of A-I.1's field-list
change (gate (a)); (vii) as chapter I lands in `leanfinal`, retire each stub to the
`example : <type> := <name>` diff form per `Leanspec.lean`'s stub lifecycle. Defect I-D10
(`a0` over-demanded at `n = 0`) and I-D11 (I.25's stale registry) are recorded and still open.
-/
