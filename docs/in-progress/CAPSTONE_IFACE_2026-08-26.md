# Capstone interface nodes L0 / DT0 / W0 / WIN0 — unit CIFACE, 2026-08-26/27

Charge: author the four interface nodes named by `CAPSTONE_SUPPLY_MAP_2026-08-26.md`
(rows CHFD-L0 / CHFD-DT0 / CHFD-W0 / CHFD-WIN0).  Lean carriers land in
`leanfinal/Uniformity/ChapI/IFC0.lean` (namespace `Uniformity.Density.IFC0`), probed
against the landed corpus.  **Every declaration in that file is a NEW statement —
trust-boundary items, all flagged for the standing review.**  No leanspec edit is made
or implied; where a node's endpoint is a future leanspec re-sign, that re-sign is a
LATER RECORDED AMENDMENT and is marked so below.

Status legend per node: INTERFACE (the Lean carrier), SUPPLIER (who proves it, sized),
CONSUMER (how the capstone field follows — probed where cheap), AUDIT (the
non-swallowing / fabricability note, C130s18-§5 style).

---

## NODE LADDER-SUPPLY-L0 — the four-way split of the `ladder` field

### Interface

The capstone field (`I10_I15_I18.lean:154-160`) is one universal function

    ∀ (O K C B G Kt L N v ρ q), CanonicalLadderConfig C B G Kt L N v ρ q n →
      Ladder.LadderSupply.{0,0,uW,uG,uKt,uL} C B G Kt L N v ρ q

whose target is a four-field record (`E24.lean:147-155`).  L0 splits it into four
supplier `Prop`s, each with the field's EXACT binder block and guard, each concluding
in exactly ONE `LadderSupply` field:

| supplier (IFC0 name) | conclusion after the guard | landed conclusion carrier |
|---|---|---|
| `LadderPackageSupplier n` | `Ladder.HE7APackage.{0,0,uW} C B` (= `Nonempty (RungInterface C B)`) | E.24/E.12 |
| `LadderLB1Supplier n` | `Ladder.LB1Carrier.{0,0,uW} C B` | E.39 (A-E.2 form) |
| `LadderMP1Supplier n` | `Ladder.MP1Carrier.{0,0,uW} C B` | E.40 (A-E.2 form) |
| `LadderVarthetaSupplier n` | `∀ i ≥ 3, Ladder.VarthetaRes G Kt L N v ρ q i` | E.61 (A-D.2 sitewise `HVarthetaRes`) |

Universe discipline (A-E.1/E-D6): the first three bind `uW` explicitly (the `(SEC-RANK)`
rank carrier's universe, not inferable from `(C, B)`); `O, K` are pinned at `Type 0`
exactly as the capstone field pins them, so the `HE7APackage`/`LB1Carrier`/`MP1Carrier`
applications are at `.{0, 0, uW}`.  The ϑ-supplier needs no `uW`.

### Exit gate (consumer derivation — PROBED, landed in IFC0)

`ladderField_of_suppliers` : the four suppliers imply the capstone `ladder` field
verbatim (proof: the `LadderSupply` record constructor — one anonymous constructor
application per configuration).  Conversely (the forward direction of
`ladderField_iff_suppliers`): each supplier is a PROJECTION of the field.  The field's
type is named `LadderField n`, with an anti-drift `example` pinning it definitionally to
`CapstoneHypotheses.ladder`.  So machine-checked in IFC0:

    (all four suppliers at n)  ↔  (the capstone ladder field at n)

The split therefore neither strengthens nor weakens the obligation — it is an exact
decomposition, which is the whole design: four independently-campaignable targets whose
join is the field, with no residual assembly debt beyond the landed record constructor.

### Supplier campaigns (sized per the supply map row `ladder`)

* HE7A/RungInterface leg: multi-node; `BLOCKERS_PLAN_2026-08-26.md` F1/F2 (BlockFrontier,
  exact slot reads) are prerequisite candidates for the C-to-E block accounting.
* LB1 leg: multi-node (block-suite existence at multi-side / nonseparable triggers).
* MP1 leg: multi-node; exposes the queued gate-(b) cite candidate
  `recentered_key_emission` (`E40.lean:145-148`) — owner cite gate applies there, not here.
* ϑ leg: research-open (E.61's TEETH row: no machine teeth at the level-3 family).
  Sub-decomposition of these four is the campaign's own first node, not L0's.

### Audit (non-swallowing, C130s18-§5 discipline)

* Each supplier consumes the guard `CanonicalLadderConfig` AS A WHOLE — the same
  already-audited socket (leanspec A-I.3 fence check).  No supplier weakens the guard
  (dropping a CC-12 view) or adds a residue-law hypothesis: an added clause of either
  trap genre (`hvarthetaRes_of_arena_agree` agreement, τ-letter embedded values) is
  refuted UNIFORMLY by the landed `arenaAgreement_not_uniform` /
  `embeddedValue_not_uniform`, which apply verbatim since the context is identical.
* The suppliers do not supply each other and do not supply the guard: none of the four
  conclusions mentions `ChainRealization`/`RealizedInput`, so no supplier can be used to
  fabricate a socket witness.
* Honest vacuity note: at `n = 2` no landed witness inhabits the guard (the S2 teeth sit
  at degree 4 — supply-map stop-the-line finding 3).  A degree-2 supplier proved by
  REFUTING the guard would typecheck; the supplier campaign's exit gate must therefore
  re-fire a non-vacuity tooth (an inhabited degree-2 socket instance) before any
  positive-conditionality claim.  Same note verbatim for DT0.

### Review flags (trust boundary)

NEW statements: the four supplier `def`s.  The two assembly/projection theorems are
proofs, not commitments.  Nothing here is signed; binding any supplier name into
leanspec is a later recorded amendment.

---

## NODE DEEP-TWIST-DT0 — the per-live-level split of the `deepTwist` field

### Interface

The capstone field (`I10_I15_I18.lean:164-171`) demands, per configuration `(… A R w r)`,

    CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w

where `DeepTwistConjunctLive r … = ∀ i, DeepLive r i → VarthetaRes … i ∧ WFrame A q R w i`
(`I10FreezeV2.lean:45-50`), `DeepLive r i = 3 ≤ i ∧ i < r` (`C130a.lean:40`), and
`WFrame … i` unfolds to `∀ j, 3 ≤ j → j ≤ i → GentowW (A j) (q j) (R j) (w j)`
(`E62.lean:127-137`, `D55.lean:103`).  Key simplification, machine-checked in IFC0: the
cumulative `WFrame` legs over ALL live `i` are jointly equivalent to the flat per-level
family `∀ j, 3 ≤ j → j < r → GentowW (A j) (q j) (R j) (w j)` — because `j ≤ i < r` and
each live `j` is its own live witness.  So DT0 splits the field into exactly TWO
suppliers, each at the field's binder block and guard:

| supplier (IFC0 name) | conclusion after the guard |
|---|---|
| `DeepVarthetaSupplier n` | `∀ i, DeepLive r i → Ladder.VarthetaRes G Kt L N v ρ q i` |
| `DeepGentowSupplier n`   | `∀ j, 3 ≤ j → j < r → Gauge.GentowW (A j) (q j) (R j) (w j)` |

The second is stated at D.44's raw `GentowW` — the exact `[GENTOW5-W(j)]` identity
`R j (N.n (s * q j)) = theta (q j) s * (w j)^s` — so the μ₃ campaign's per-level
endpoints (e.g. a depth-2 `gentow5w_two`, once OPEN-RP1-TRANSPORT clears) plug in at
single levels without repackaging through `WFrame`.

### Exit gate (consumer derivation — PROBED, landed in IFC0)

`deepTwistField_of_suppliers`: the two suppliers imply the capstone `deepTwist` field
(proof: pair the ϑ leg with the `WFrame` rebuilt from the flat `GentowW` family — a
three-line term).  Converse projections are the forward direction of
`deepTwistField_iff_suppliers` (the `GentowW` leg reads level `j` off the conjunct at
the live index `i := j` with `j ≤ j`); the field's type is named `DeepTwistField n`
with its own anti-drift pin.  Machine-checked equivalence:

    (both suppliers at n)  ↔  (the capstone deepTwist field at n)

Plus the per-live-index projections ON the conjunct itself (the map row's ask):
`DeepTwistConjunctLive.vartheta_at` and `DeepTwistConjunctLive.gentowW_at` extract the
sitewise `VarthetaRes i` and the level-`j` `GentowW` from any conjunct proof.

### Supplier campaigns

* ϑ leg: shares the `HVarthetaRes` subproblem with L0's fourth supplier (the DAG's
  explicit join point) — research-open, E.61 has no teeth.
* `GentowW` leg: per live level; the μ₃ campaign is a depth-2 TOOTH, not the universal
  supplier (`MU3_CAMPAIGN_2026-08-26.md`); blocked there on OPEN-RP1-TRANSPORT plus the
  concurrent `hprev`/`chainNormBelow` amendments.  General levels research-open.
* At `r ≤ 3` the live range `3 ≤ i < r` is empty and both suppliers are vacuously
  dischargeable (the `CHFD_probe.lean` depth-2 observation) — honest scope note: DT0's
  content begins at witnesses of depth `r ≥ 4`.

### Audit

* Both suppliers consume the joint-witness guard whole (arena family pinned to the SAME
  realized input, `core.r = r` — A-I.2(b)); neither exposes the arena or the read
  separately, so the C130s18 §5 twist audit transports: a χ-twisted context is again a
  full guard witness, refuting any uniform derivation of the D.62 trap hypotheses.
* The `GentowW` supplier's conclusion relates `R`, `A`, `w` — NOT `ρ` — so it cannot
  swallow the ϑ conjunct; the ϑ supplier's conclusion is the already-fenced sitewise
  carrier.  No new relation between the canonical read and the arena read is stated
  anywhere in DT0.
* Same degree-2 vacuity note as L0's audit (no landed degree-2 socket witness).

### Review flags

NEW statements: the two supplier `def`s.  Assembly/projection theorems are proofs.
Later recorded amendment if leanspec ever binds these names.

---

## NODE WELD-SITE-W0 — the guarded weld-site supply socket (design node)

### The A-I.1 constraints this design answers

1. The all-sites shapes are MACHINE-REFUTED (`Leanspec/ChapI.lean:310-324`, gate item
   (13); landed negative `F12w.lean:106-116`: `¬ W1Transport (fun _ : Fin 1 => 1) 0`
   over `ZMod 3`), so no field may quantify over all sites unguarded.
2. The three legs must bind TOGETHER (I-D8: `w1` is a named debt owed at the same
   trigger as `jd0box2`/`genhnBox2`; F.28's actual bundle has all three).
3. The I.10a pattern is the sanctioned cure: guard by "the sites that ARISE".

### Interface (landed in IFC0 §3)

    structure ArisingWeldSiteSupply (vsite csite Rh RG) (AV AC AF) : Prop where
      jd0box2   : ∀ s, AV s → Weld.JD0Box2 (vsite s)
      genhnBox2 : ∀ s, AC s → Weld.GenhnBox2 (csite s)
      w1        : Weld.W1Transport (fun l : {l // AF l} => Rh l.1) (fun l => RG l.1)

with `AV/AC/AF` the per-index arising predicates and the `w1` leg restricted to the
arising line subtype.  Cheap theorems landed alongside:

* `arisingWeldSiteSupply_total_iff` — at the TOTAL guards (`fun _ => True`) the socket is
  exactly F.28's `WeldObligations` (the refuted all-sites bundle): the degenerate guard
  recovers the old shape, machine-pinned.
* the F12w-transported TOOTH — at the `Fin 1`/`ZMod 3` instance the total-guard socket is
  REFUTED (`¬ ArisingWeldSiteSupply … (fun _ => True) …`), so the guard is load-bearing:
  A-I.1's refutation argument transports to this socket verbatim.
* `ArisingWeldSiteSupply.of_strikes` — the fold half at guarded sites: per-arising-site
  `JD0SiteStrike`s with site/ledger pins + the other two legs assemble the socket (the
  F04w `JD0SiteStrike.jd0Box2` route, composed).
* the fabricability DISCLOSURE — at the EMPTY guards the socket is trivially inhabited
  (machine-shown `example`), which is exactly why the guards are NOT free for a
  capstone-field binding (see the blocked item).

### Consumer derivation — BLOCKED-BECAUSE, with the missing mechanism named

The capstone fields `jd0 : True` / `genhnBox2 : 6 ≤ n → True` stay `True` per A-I.1;
re-signing them at this socket (plus adding the owed `w1` field) is an owner gate-(a)
amendment.  That amendment CANNOT be enacted yet, and W0 does not pretend otherwise:

**BLOCKED-BECAUSE: no landed declaration exports weld sites from arising data.**  The
guards must be pinned to a canonical producer the way I.10a pins `ρ` to the canonical
node-point read — but `rg` over the tree shows `ValueDictSite`/`CarrySite` occur ONLY in
`ChapF/F04|F05|F11|F28` (carriers), never constructed from chapter-C/H stage objects
(GC-13: "no F node constructs one").  The missing mechanism is a SITE EXPORT — the weld
analogue of CC-12's views: from a realized stage/chain object, the induced
`ValueDictSite` (slot/ledger action pair), `CarrySite` (carry table at multiplicity μ),
and the `(Rh, RG)` residual-operator line families, with degree/site indexing.  That is
WELD-SITE-SUPPLY node 1 (statement/design review first, per the map); until it lands,
`AV/AC/AF` remain explicit parameters and the socket is a campaign target shape, NOT a
capstone-field candidate.  Any attempt to bind it with free guards would be the D-D12
fabricable-shape defect — the disclosure example is the standing regression against
forgetting this.

### Audit

* The socket only DEMANDS the three ledger-strength legs at guarded indices; it supplies
  none of them, states no relation between the legs, and cannot discharge itself: the
  total-guard tooth shows it is falsifiable, the empty-guard example shows the guard
  parameters carry all the content — both directions machine-pinned.
* No conclusion of the socket mentions the guard predicates, so a supplier cannot
  weaken its obligation by strengthening the guard silently (the guard sits only in
  hypothesis position, exactly like `CanonicalLadderConfig`).

### Review flags

NEW statements: `ArisingWeldSiteSupply` (structure).  The degeneration/tooth/fold
theorems are proofs over landed F-vocabulary.  The future field re-sign (three fields
bound together, `w1` debt paid) is a later recorded owner amendment — NOT enacted here.

---

## NODE WINDOW-PINNING-WIN0 — the real `WindowPinningAt` body, typed not asserted

### The trap the typing must avoid

I.05's signed docstring: the real body "quantifies over the degree-`n` stage data
(H.09's `StageInterface` instances) and asserts the `hwin` clause".  Read literally over
INSTANCES that is vacuous — `hwin` is a FIELD of `StageInterface` (`H09.lean:93`), so
every instance satisfies it by projection.  The contentful reading: a stage presents its
window/loss numbers BEFORE the interface exists (the consulted-height reader's output),
and window-pinning is the claim that those numbers satisfy `(CS-1Q.a)`.  So the body
needs a PRE-`hwin` datum carrier — and, as with W0, quantifying it over ALL data is
refutable (window = loss = 0), so an arising guard is again mandatory.

### Interface (landed in IFC0 §4)

    structure StageWindowData (G : GenreDatum) (N H S : ℕ) where
      stageWindow : ℕ
      stageLoss   : ℕ

    def StageWindowData.Pinned (d) : Prop :=            -- (CS-1Q.a), the hwin statement
      G.e₁ * (N - 1 - H) ≤ d.stageWindow + d.stageLoss

    def WindowPinningBody
        (Arises : ℕ → ∀ ⦃G N H S⦄, StageWindowData G N H S → Prop) (n : ℕ) : Prop :=
      ∀ G N H S (d : StageWindowData G N H S), Arises n d → d.Pinned

with the byte-tie to H.09 machine-pinned in both directions:
`StageInterface.windowData` projects an interface to its datum and
`windowData_pinned : st.windowData.Pinned := st.hwin` (so `Pinned` IS the `hwin` clause,
consumed by projection, asserted nowhere); and an extension lemma shows a pinned datum
is exactly what completes a window-free interface skeleton.  The degree index `n` and
the degree tie live INSIDE the arising guard — WIN0 deliberately does not invent a
numeric degree formula on `GenreDatum` (that would be a new mathematical commitment
beyond the signed docstring; the reader rule knows which stages a degree-`n` input
generates).

Teeth landed alongside: at the TOTAL guard the body is REFUTED (a concrete
`GenreDatum` with `e₁·(N−1−H) = 1 > 0` and the zero datum), so the guard is
load-bearing; at the EMPTY guard the body is trivially inhabited (fabricability
disclosure, same fence note as W0).

### Consumer derivation — the exit gate, and what stays open

`WindowPinningAt n` is the signed `True` placeholder (I-D12); its re-sign at
`WindowPinningBody ⟨canonical guard⟩ n` is a later recorded owner amendment.  The
canonical guard is OPEN: H.89w supplies the consulted-height LEMMAS at the restricted
`e₁ = 2` regime but "does not formalize GENHN-CAP-GEN's reader rule" (I.05's own
disposition), so no landed declaration produces the arising stage data.  The supplier
campaign (map row: H.89w + GENHN-3/GENIND-2 consulted-height supply) must (1) land the
reader-rule carrier = the canonical `Arises`, then (2) prove `WindowPinningBody n` at
it.  Until then the placeholder stays `True` — WIN0 changes nothing signed.

### Audit

* `Pinned` restates `hwin` byte-exactly (the `Iff.rfl` pin in IFC0 fails the build on
  drift); the body DEMANDS it under the guard and supplies nothing — no H.89w lemma is
  consumed, no window value is computed, no stage is claimed to arise.
* The guard is hypothesis-position only; total-guard refutation + empty-guard
  disclosure pin both failure modes (I-D13 genre and D-D12 genre respectively).

### Review flags

NEW statements: `StageWindowData`, `StageWindowData.Pinned`, `WindowPinningBody`.
The projection/extension/teeth are proofs.  Re-signing I.05 is a later owner amendment.
