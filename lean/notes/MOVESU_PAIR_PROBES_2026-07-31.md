# MOVESU-PAIR PROBES (2026-07-31) — BridgeD19 n2 probe + SlotsG11c falsifier check

Unit movesu-pair, per REMAINING_CENSUS_2026-08-01.md §4.2 item 8 (the two MovesU
probes). Outcomes: probe 1 CLOSED (compiled countermodel, row refuted as typed);
probe 2 still BLOCKED (no cheap CutRealization-Presented supplier yet) — record
updated below with the exact shrunken missing-piece list.

## Probe 1 — `decCovers_typeOf5_n2` (BridgeD19_omAgree.lean:90): REFUTED AS TYPED

**New leaf: `lean/LeanUrat/MovesU/BridgeD19_omAgreeNeg.lean` (compiles green,
all theorems Lean-core `[propext, Classical.choice, Quot.sound]`).**

The round-3 SUSPECT flag (stall stratum: typeOf5 → typeOf4 → none) is CONFIRMED
by compilation, at EVERY prime:

* Witness: the stall point `g = X²` at level `N = 1` (`stallBox p`) — all lower
  coefficients vanish, the level-1 undecided cluster point.
* `boxValSupport` is the single dot `(2, 0)` → the Newton polygon has no sides
  (`npSides_of_card_le_one`, via `npVertices_length_le`) → `rootSide = none` →
  `rootResidual = 0` → `dr = 0`, and `M5.cells` is empty at a degree-0 residual
  (`cells_eq_nil_of_natDegree_zero`, the free-context form of
  `cells_childCtxOfSize`). With `ClassifierBridgeChildful.classify_eq_shapeOf`,
  `(OM.B.classify p 2 1 stallBox).tree = [(0, 2, 0)]` (`classify_stallBox_tree`).
* The decoder falls through exactly as flagged: `headOrd = 0 ≠ 2` (not a chain
  head) `≠ 1` (not multi-slope), and `typeOfW` rejects `[(0,2,0)]` (neither the
  separable head `[(0,2,2)]` nor a self-loop head with `0 < dr < 2`) → `none`
  (`typeOf5_stallBox`).
* Hence `¬ DecCoversClassify 2 p (typeOf5 2)` for every prime p
  (`decCovers_typeOf5_n2_false`), and the census row's ∀-statement is false
  already at p = 2 (`decCovers_typeOf5_n2_refuted`).

DISPOSITION: the sorry at BridgeD19_omAgree.lean:90 STANDS byte-unchanged
(countermodel-not-force discipline; its deletion/repair is a fence event for
Asvin). The row is CLOSED as an enrichment probe: the Architecture-B covering
hypothesis is genuinely FALSE on the stall strata, so IB-F7's `hcov` discharge
must carry a DECIDED-LOCUS guard (covering off the stall strata) — e.g. restrict
`DecCoversClassify`'s ∀ to shapes in the decided menu (`omMenu5`'s range, where
`typeOf5_of_mem_omMenu5` already gives `some`), or to polynomials whose level-N
polygon has a side. No consumer is affected: `decCovers_typeOf5_n2` has zero
consumers at HEAD (optional enrichment, off the default path).

M1 COEXISTENCE (recorded in the leaf header): the leaf imports the sorried
module only for the named Prop `DecCoversClassify`; nothing consumes the sorried
universal, and the leaf's own footprint is Lean-core.

## Probe 2 — `slot_m4bConst_falsifiable` (SlotsG11c_seamAudit.lean:76): STILL BLOCKED

CHARGE: check whether TV_A5b_forge / HK23 carriers / G19e wrongValuedData now
supply the compiled CutRealization-Presented instance the 2026-07-30 blocked
record wanted ("a minimal `Presented` with one realized prefix class"); prove if
yes, update the record if no.

VERDICT: **NO — not cheaply.** None of the three named suppliers touches the
MovesD `Presented`/`PrefSet`/η-class layer:

* `TV_A5b_forge` (MovesT): compiled realizable ROOT HISTORIES over (2, ZMod 2)
  — `realizableA/B` prove `HistoryCoherent ∧ Realizable ∧ IsCanonPres` at
  length 1. These are PrefSet-membership INGREDIENTS (the canonical-presentation
  half), but no Shape tie, no JetSetup, no η-class packaging.
* HK23/HK25 (HC2 gates): 2-node coherent histories under the NEW (S-a) keying —
  same situation (no Presented-layer content).
* `SlotsG19e.wrongValuedData`: a D-SC `RelSite`/`RelData` pack (sited-slot
  falsifier layer) — entirely disjoint from the CutRealization seam.

Corpus grep 2026-07-31: `Presented` and `CutRealization` still occur ONLY as
binders; zero compiled instances.

WHAT DID CHANGE since the 2026-07-30 record (the gap has SHRUNK):

1. TWO compiled JetSetup artifacts now exist (none existed then):
   `HC2/U27_gateInert.gateJ : JetSetup U31.H₀ 2 1 (2·1)` — CONCRETE, sorry-free,
   at the root-only inert history `U31.H₀` over `F = F4`, with its fiber
   COMPUTED (`gateJ_SHZ`: `SHZ ⊤` = the all-zero cylinder, card 1) — exactly the
   `Presented.fiber`/`encode_fiber` raw material; and `HC2/U28_gateSep`'s
   hypothesis-driven root-stage builder (free `H`, binders hcoh/hband/hvalsupp/
   hzc).
2. The Shape-side packaging exists: `MovesT/V8_shapeOf.shapeOfH_matches` gives
   `MatchesHist + ShapeWF` from `HistLawful` — i.e. `Shape.ofHist`-style PrefSet
   membership is now assemblable for a concrete lawful history.
3. The assembly reduction exists: `HC2/U15.present_exist_of_seeds` builds
   `Nonempty (Presented …)` from (hseed SEED-EXIST, hnorm PresentNorm, hd4,
   hunp) at `polOM` — all still HYPOTHESIS binders.

WHAT IS STILL MISSING (the honest residue, in dependency order):

(a) ONE history carrying BOTH halves: `gateJ`'s `U31.H₀` (has the JetSetup +
    computed fiber, over F4) lacks `IsCanonPres`/shape packaging; the forge's
    canonical realizable histories (over ZMod 2) lack JetSetups. The pieces
    live at different histories/fields.
(b) THE η-CLASS EXHAUSTION KERNEL: `Presented.jet` quantifies over `PrefIdx`
    with the OPAQUE representative `reprOf i` (`Classical.choice`), so a
    concrete JetSetup transports only through `PrefSet P = {H₀}` (or JetSetups
    for ALL members) — a classification of every coherent realizable canonical
    matching history at the chosen shape. No such exhaustion exists for ANY
    concrete shape. This is an instance-classification kernel (IFK-adjacent).
(c) `PresentNorm` at the concrete shape: totality over `PrefSetAny` + Galois
    uniqueness — same classification kernel; the only in-corpus supplier is
    U17c's `presentNorm_polOM`, itself conditional on the re-keyed
    `StageTransHyp` + `OmUniqHyp` (and U17a's `lift_swap` sorry is one of its
    legs — census HC2 row).
(d) Even with (a)-(c): the falsifier still owes the surrounding degenerate
    `CtsMeasured` chassis (the ~30-field carrier with `ent_card`/`ent_sel`/
    `evt_*` laws tying the height-reading census to genuine box events at
    `entLvl`), which was the ORIGINAL sketch burden — now ON TOP of the
    ent_cut supply.

DISPOSITION: `slot_m4bConst_falsifiable`'s sorry STANDS as the blocked record
says; the falsifier remains an HC-2-scale helper away. RECOMMENDED next
mechanism (not attempted here, per bounded scope): a "PrefSet-singleton gate"
unit at the U27 inert history — prove `HistLawful` + `IsCanonPres` for `U31.H₀`
at a policy over F4, fire `shapeOfH_matches`, and attempt the η-exhaustion at
that ONE root-only shape (the smallest instance of kernel (b)); if (b) closes
there, `gateJ` + `gateJ_SHZ` supply `jet`/`encode_fiber` directly and only (c)
+ (d) remain. Wave-D's n = 2 carrier duty subsumes (d).
