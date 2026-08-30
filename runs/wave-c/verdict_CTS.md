# UNIT CTS — VERDICT (COMPLETE, 2026-08-30; finisher CTS2 over the hung CTS)

**Charge:** `CellTypeScalingAt D` at `D ≥ 2` — the deep-wild OM tower step isolated by
DTR (IFCG47 §1) as the ONE open pointwise Prop of the full-span/dd census territory.
Deliverable file: `leanfinal/Uniformity/ChapI/IFCG48.lean`.

**Session record:** the original CTS agent landed §0–§2 (M1/M2) and hung starting M3;
CTS2 recovered the state from disk, landed M3 first-try, and completed the unit.

## VERDICT: HONEST PARTIAL with the exact named remainder MINIMIZED + the
signed-ready two-surface cite package. No axiom declared. Whole file Lean-core.

`CellTypeScalingAt D` at `D ≥ 2` is NOT proved outright — as DTR predicted, it is the
Montes/Okutsu induction step proper (C136's deep-wild territory). What this unit did:
reduce it, by machine-checked Lean-core theorems, to the STRICTLY SMALLER statement
`FactorCorrespondenceAt D` (the bare OM factor matching, with ALL `(e, f)`/type/degree
bookkeeping discharged), and stage the cite at BOTH surfaces so the owner signs
whichever reads faithfully.

## The landed layer (all Lean-core, per-file exit 0, 17/17 `#print axioms` clean)

- **§0** `cellTypeScalingAt_zero` — the `D = 0` witness (completes the depth interval).
- **§1** `DeepWildTypeScalingStatement` (RAW cite surface, stated NOT asserted) +
  `cellTypeScaling_of_cite` (signed cite ⟹ the COMPLETE pointwise law, all `D`).
- **§2** the Eisenstein valuation bridge: `eis_addVal_algebraMap` (M1: `addVal` scales
  by exactly `e'` along the structure map), `eis_addVal_norm` (M2: `f(K'/K) = 1` in
  `addVal ∘ norm` form), **`eis_addVal_norm_tower` (M3, the step the predecessor died
  on): the TOWER MASTER IDENTITY `addVal_O ∘ norm_O = addVal_{O'} ∘ norm_{O'}` on ANY
  free `O'`-algebra** — mathlib's `Algebra.norm_norm` (first use in this corpus)
  composed with M2. No completeness/domain/finiteness on the tower top.
- **§3** the tower `(e, f)` reads: `normValues_eq_of_algEquiv` +
  `inertiaDegOf_eq_of_algEquiv` (the f-leg is invariant through an order iso — the
  master identity in action), `natDegree_eq_of_algEquiv` (the e-leg: pure finrank
  tower law, no Eisenstein data), `efPair_eq_scale` + `efPair_scaled_of_algEquiv`
  (the per-factor `(e, f) ↦ (e'·e, f)` — exactly `scaleType`'s member map).
- **§4** `typeOf_eq_scaleType_of_rel` — THE MULTISET REDUCTION: a factor
  correspondence carrying (equal inertia gcd, `e'`-scaled degree) per matched pair
  fires `typeOf g = scaleType e' (typeOf G)` for ANY monic `g`, `G`. The named Prop's
  lattice/box hypotheses play NO role at this layer (they are consumed only in proving
  the correspondence — i.e. they live entirely inside the remaining cite).
- **§5** `FactorCorrespondenceAt D` (the named remainder in correspondence currency,
  mirroring the named Prop's hypotheses exactly) +
  `cellTypeScalingAt_of_factorCorrespondence` (fires the named Prop at EVERY depth) +
  `deepWildTypeScaling_of_correspondence` (the smaller surface fires §1's).
- **§6** consumer sockets: `transport_decidedAt_iff_of_cite` /
  `_of_correspondence` — DTR's decision-transport iff at every depth with the
  `CellTypeScalingAt` premise replaced by either cite surface (THE entry point for the
  face/centre assembly on composite-mass `PowerFullSpanLaw`); `cellTypeScalingAt_two_of_cite`
  / `_of_correspondence` — the exact `D = 2` supplies for ER4's dd terms.

**Design choice (flagged, trust boundary):** the correspondence Rel is in the corpus's
gcd currency (`inertiaDegOf h = inertiaDegOf H ∧ deg h = e'·deg H`), deliberately NOT
`Nonempty (AdjoinRoot h ≃ₐ[O] AdjoinRoot H)` — OM matches FIELDS, and the orders need
not be isomorphic; an order-iso form could be unrealizable. §3's iso lemmas are the
machine-checked special case, kept as the transport instrument.

## The cite package (fallback executed; NO axiom declared)

- Both surfaces staged and TYPED against the landed layer (elaboration machine-checks
  the shapes); faithfulness entry DRAFT in IFCG48's module docstring: sources
  (GMN Trans. AMS 364 (2012), numbering to pin at print-read; FGMN J. Algebra 427
  (2015) as the standing dictionary), the corpus↔source dictionary, and THREE scope
  caveats. **Caveat 2 is load-bearing**: the multiplicity/inseparability fringe (devT
  is not multiplicative; classical sources assume separable/squarefree) applies to
  BOTH surfaces — the signing read may need to add a separability hypothesis, a
  statement-shape decision at the owner gate.
- REVIEW_QUEUE Tier-1 row 9 added (`docs/REVIEW_QUEUE_2026-08-26.md`), status STAGED.

## The surviving set (honest remainder)

1. `FactorCorrespondenceAt D` at `D ≥ 2` (⟸ suffices for everything below) — the cite.
2. `PowerFullSpanLaw m σ` at COMPOSITE `m`: needs (1) + the face/centre partition
   assembly + `recentred_decidedSeq_tendsto` summation — a separate unit (PSL4's
   consumption plan); primes remain CLOSED unconditionally (DTR §3).
3. ER4's `ZcURLim (e1DdDecFam σ)` limits: need (1)'s `D = 2` instance (supplied here
   conditionally) + the same assembly.

## Verification record

- Per-file: `lake env lean Uniformity/ChapI/IFCG48.lean` exit 0 after EVERY increment
  (I1 M3; I2/I3 §3; I4 §4; I5 §5 after the Finite-instance fence fix; I6 §6+AxCheck;
  final docstring pass).
- AxCheck: 17/17 declarations = `{propext, Classical.choice, Quot.sound}` exactly.
- Aggregator import added (`Uniformity/ChapI.lean`: IFCG48 between 47 and 49);
  chapter roll-up `lake build Uniformity.ChapI.IFCG48 Uniformity.ChapI` run at close.
- Instance-fence note: §3/§4 deliberately carry NO `Finite (ResidueField ·)` section
  variables (Lean's mention-based auto-inclusion would otherwise make the reduction
  unsynthesizable from `CellTypeScalingAt`'s binders); the three §3 lemmas that
  consume the master identity take them explicitly.
- Probe file `leanfinal/scratch/cts2_probe.lean` (kept): the four mechanical joints
  (AdjoinRoot tower instances, `norm_norm` unification, `norm_eq_of_algEquiv`,
  finrank tower law) verified against plain mathlib before landing.
