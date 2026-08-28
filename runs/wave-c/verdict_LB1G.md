# Verdict LB1G — the LB1 guard-link

**Date:** 2026-08-28  
**Unit:** LB1G  
**Verdict:** **RESTRICT-ANYWAY.** The unrestricted carrier is not refuted at the landed S2
pair; it is PROVED there only vacuously because the exported block has mass one and no legal
`RungInterface` can trigger LB1. The arbitrary-interface demand remains unsupported and unused
by landed mathematical consumers. Supersede it with an export-restricted twin after the missing
C-to-E interface-export relation is typed.

## Malicious-interface attempt

The landed antecedent remains `VAUDProbe.s2_degree_four_socket`
(`leanfinal/scratch/VAUD_probe.lean:39-59`), using
`C130sg.s2Frontier_ladder_socket` (`leanfinal/Uniformity/ChapC/C130sg.lean:522-535`). The
attempted two-side construction cannot inhabit its block:

- **PROVED** `LB1GProbe.s2_exported_block_mu_one`
  (`leanfinal/scratch/LB1G_probe.lean:44-47`): the exported S2 block has `μ = 1`.
- **PROVED** `LB1GProbe.rungInterface_card_eq_one_of_mu_eq_one` (`:56-71`): positive side
  lengths summing to one force `I.sides.card = 1`.
- **PROVED** `LB1GProbe.rungInterface_sep_of_mu_eq_one` (`:83-248`): `hresdeg`, `hforce`,
  `hnonempty`, and `hexhaust` force every residual multiplicity on that side to be one.
- **PROVED** `LB1GProbe.not_lb1_trigger_of_mu_eq_one` (`:251-258`): both LB1 trigger
  disjuncts are false.
- **PROVED** `LB1GProbe.s2_unrestricted_lb1_vacuous` (`:279-286`): the unrestricted
  `LB1Carrier` holds at the exact landed S2 pair, vacuously, for every `uW`.

Therefore there is no concrete malicious `I` on this landed pair. This is stronger than a
failed search: such an `I` is impossible from the landed `RungInterface` laws. It does not
validate the arbitrary quantifier at arising blocks with `μ ≥ 2`; the known abstract
counterexample `OM4ResignCert.lb1_resigned_not_trivial`
(`verification/om4_resign_nontriviality.lean:144-220`) lives at `μ = 2`.

## Exact restricted statement

**PROVED/ELABORATED** `LB1GProbe.LB1CarrierLive`
(`leanfinal/scratch/LB1G_probe.lean:296-301`):

```lean
def LB1CarrierLive {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (Exported : Ladder.RungInterface.{uO, uK, uW} C B → Prop) : Prop :=
  ∀ I : Ladder.RungInterface.{uO, uK, uW} C B, Exported I →
    (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
    Nonempty (Ladder.BlockSuite I)
```

`Exported I` is intentionally explicit. Its production instantiation must mirror
`IFC5.CanonicalLadderLiveAt` (`IFC5.lean:105-123`): the same realization witness and the same
slot/block views, plus a contentful `RealizedRungInterfaceExport X eK I` relation. Merely
bundling an arbitrary `I` or taking `Exported := True` would recover the defect.

- **PROVED** `LB1GProbe.lb1CarrierLive_of_unrestricted` (`:304-310`): OLD implies NEW.
- **PROVED** `LB1GProbe.lb1CarrierLive_of_exported_partitionLegs` (`:314-322`): the landed
  E.57 funnel only needs `PartitionLeg I` for exported triggering interfaces.
- **GAP:** no `RealizedInput → RungInterface` exporter or export relation exists. The current
  realization views end at `SlotViewEq`, `BlockViewEq`, and `GaugeFamilyViewEq`
  (`C130s18.lean:149-175`).
- **BLOCKED-BECAUSE:** production supersession must retype E.24's `LadderSupply.lb1` and
  ultimately the signed `CapstoneHypotheses.ladder`; that is an owner amendment, not licensed
  by this audit.

## Consumer table

| Consumer | Instantiated interface | Export status |
|---|---|---|
| E.39 gate (`E39.lean:140-143`) | arbitrary caller `I` | not exported; test only |
| E.24 gate (`E24.lean:193-200`) | arbitrary caller `I` | not exported; test only |
| E.24 `LadderSupply.lb1` (`E24.lean:147-155`) | none | record field only |
| E.44 `LadderObligations` (`E44.lean:111-168`) | none | packaging/projection only |
| I.10 `CapstoneHypotheses.ladder` (`I10_I15_I18.lean:151-160`) | none | returns E.24 record |
| IFC0 LB1 supplier/join (`IFC0.lean:85-92`, `:120-147`) | none | bookkeeping only |
| IFC5 live record/join (`IFC5.lean:146-157`, `:179-234`) | none | retains old LB1 field |
| E.57 `PartitionLeg.toBlockSuite` (`E57p.lean:188-246`) | its parametric `I` | export unspecified; works restricted |
| E57i `split_blockSuite` (`E57i.lean:201-205`) | synthetic `mixIface` | not arising-exported |
| E57ih `hi_blockSuite` (`E57ih.lean:180-183`) | synthetic `hiIface` | not arising-exported |
| LDEC probe (`LDEC_probe.lean:59-66`) | every arbitrary `I` | scratch only |
| VAUD tooth (`VAUD_probe.lean:70-86`) | arbitrary caller `I` | diagnostic only |

The proposed assertion that the landed E.24 funnel already instantiates LB1 only at exported
interfaces is **false literally**: its sole application gate accepts an arbitrary `I`. But no
landed mathematical theorem depends on that strength. `PartitionLeg.toBlockSuite` is the actual
construction and the restricted probe wrapper uses it unchanged.

## Recommendation

**RESTRICT-ANYWAY**, not KEEP-UNRESTRICTED:

1. unrestricted LB1 is false on legal abstract E data;
2. S2 cannot distinguish the readings because `μ = 1` makes the trigger empty;
3. no genuine uniform proof strategy for arbitrary interfaces was found—the missing theorem
   would have to realize every legal numerical interface on an arising polynomial, far beyond
   the planned canonical C-to-E exporter and HE7.96; and
4. the consumer table plus the restricted E.57 wrapper show no mathematical downstream loss.

LS-G0 remains a stop on the old supplier. Its next legitimate work is the export relation and
an owner-approved supersession twin, not an unrestricted LB1 proof fleet.

## Verification

Executed exactly:

```bash
cd leanfinal
timeout 580 ~/.elan/bin/lake env lean scratch/LB1G_probe.lean
```

Exit 0; zero `sorry`; all ten `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]`. No landed `.lean`, leanspec, or existing scratch file
was edited; no commit was made.
