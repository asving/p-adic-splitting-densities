# verdict_LRS — UNIT LRS: row C2's residue dissected — the derivable fields of the D.44 ladder-read law + its carrier normal form (2026-08-30)

**Status: COMPLETE (dissection + derivable fields landed; the supply does NOT close —
adjudicated, not merely unattempted; the residue now has a carrier-shaped normal form
matched to RUNG's `read_mul` genre).**
`leanfinal/Uniformity/ChapI/I10LadderRead.lean` (NEW, namespace
`Uniformity.Density.DeepExport`) — 0 errors, 0 warnings, 0 `sorry`; all **13** printed
footprints exactly `[propext, Classical.choice, Quot.sound]`.  Verified per-file
(`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10LadderRead.lean`, clean),
per-target (`lake build Uniformity.ChapI.I10LadderRead` — Build completed successfully,
8970 jobs), and the chapter aggregator `Uniformity/ChapI.lean` re-verified exit 0 after
the one standing import-line edit.  Cite ledger: **empty**.  Repo footprint: the new
module + the aggregator line + this verdict, nothing else.  Every proof landed
first-attempt — zero repair rounds.

## Charge 1 — the per-clause dissection at a general arising realization (settled)

`LadderReadSupply X` (WSS §2) = per deep-live level, `LadderReadLaw X hr j`: (i) `head`
`R(n̂(0)) = θ(q,0)`, (ii) `law` `R(n̂(s·q)) = θ(q,s)·R(n̂(q))^s` for all `s ≥ 1`,
(iii) `tie` `(peelUnit : Kt) = R(n̂(q))` — on the realization's OWN exports.  The exports
unfold (C130vw/C130ar) to RAW node data: `towerReadFamily` reads the
`SplitNodePointSource.towerRead` field ("an arbitrary function `R : G → K`" — D.44
faithfulness item 2, quoted in C130ar §4), `peelUnitFamily` IS the `peelUnit` field
verbatim (`rfl`-pinned), and `θ(q,s)` is the arena read of the section element
`thetaEl q s = n̂(s·q)·(n̂(q)^s)⁻¹` (D.04/D.08), i.e. the `arenaRead` field.  Verdict per
clause:

| clause | needs beyond exports + landed machinery | verdict |
|---|---|---|
| `law` at `s = 1` | **nothing** — `θ(q,1) = res(n̂(q)·n̂(q)⁻¹) = res(1) = 1` (landed `IFC2.theta_one`) and both sides are the base read | **DERIVABLE OUTRIGHT — PROVED** (`ladderRead_law_one`, unconditional, uniform in `q`) |
| `head` | `θ(q,0) = 1` and `n̂(0) = 1` are generic (`IFC2.theta_zero`, `NormSection.n_zero`), so the clause is EXACTLY the read normalization `R(1) = 1` | **simplified — PROVED as an iff** (`ladderReadLaw_head_iff_read_one`); the residue `R(1) = 1` is a law on the free `towerRead` field, not closable |
| `law` at `s ≥ 2` | the section identity `n̂(s·q) = thetaEl(q,s)·n̂(q)^s` is generic (proved inline, pure `CommGroup`); what remains is kernel-equivariant power multiplicativity of the read over the arena read | **carrier-derivable** — the normal form's single field `read_ker_pow` forces the WHOLE family (including head); not closable from exports |
| `tie` | relates the third free field `peelUnit` to the read | **genuinely independent** — demanded verbatim by the normal form |

**Why the whole Prop cannot close generically** (the adjudication, RUNG-§2.3 genre):
`arenaRead`/`towerRead`/`peelUnit` are FREE source fields of `SplitNodePointSource`
(C130k2 lines 167–171) with no structure law relating them; CC-11's separateness audit
is mechanized (`gaugeArenaAt_res` etc. are `rfl`-pins and C130ar's fence says "NO B-law
instance is claimed at any level — that is the instantiating supplier's obligation");
and the bank side cannot help — `IFC3.GC13Wiring` has the SINGLE clause `read_norm`,
pinning `R` only at window ladder points `1 ≤ s ≤ f'` and never mentioning `theta` or
the peel unit.  A generic proof would inhabit a law on free data (C92-vacuity genre).
So **the site half's residue does NOT shrink to the bank alone — that outcome is
refuted for this route**, and `LadderReadSupply` remains row C2's minimal named
per-realization residue.

## Charge 2 — what landed

* **§1 the derivable fields**: `ladderRead_law_one` (★ the `s = 1` rung of the ladder
  law as an unconditional THEOREM at every arising realization) +
  `ladderReadLaw_head_iff_read_one` (the head clause ⟺ `R(1) = 1` — the exact
  per-realization content of the `s = 0` clause, nothing else hides in it).
* **§2 the carrier normal form** (NEW STATEMENTS, review):
  - `CarrierReadLaw X hr j` — (i) `read_ker_pow`: `R(k·n̂(q)^s) = res(k)·R(n̂(q))^s` for
    every height-kernel element `k` and every `s` (the exported read is equivariant over
    the exported arena read along the kernel and power-multiplicative on the ladder
    base); (ii) the peel `tie` verbatim.  This is the shape the landed carrier machinery
    produces: RUNG's `rung2Read` satisfies `WeightedCarrier.read_mul` — exactly a
    ladder-type multiplicativity.  Strictly STRONGER per level than `LadderReadLaw`
    (sufficient-only; the ladder law is its trace on the ladder points).
  - `CarrierReadSupply X` (per deep-live level) + shallow vacuity tooth.
* **§2 ★ the generic derivation**: `ladderReadLaw_of_carrierRead` —
  `CarrierReadLaw ⟹ LadderReadLaw`: head is the instance `k = 1, s = 0`; the `s`-rung
  is the instance `k = thetaEl(q,s)` through the section identity; tie verbatim.
  Uniform in `q`: no cardinality, no S2 datum, no numeral, no calculus.  Plus
  `carrierReadLaw_of_mult_agree` (the coarse supplier shape: fully multiplicative read
  + kernel agreement + tie) and the supply-level ★
  `ladderReadSupply_of_carrierReadSupply` and ★ `wiredSiteSupply_of_bank_carrierRead`.
* **§3 universal form + capstone composition**: `UniversalCarrierReadSupply n` (NEW
  STATEMENT), ★ `universalLadderReadSupply_of_carrierRead`, ★
  `deepTwistField_of_carrier_supplies` — the capstone `deepTwist` field from tau supply
  + bank supply + CARRIER supply, through WSS's `deepTwistField_of_bank_supplies`.
* **§4 keystone nonvacuity**: `s2Four_carrierReadSupply` at EVERY depth-4 keystone
  witness (full parametric payload; conditionality exactly the keystone's: `w₁ w₂ w₃ w₄`
  + `IsAdicComplete` + R8r payload), plus the coherence pin — the normal form re-derives
  WSS's `s2Four_ladderReadSupply` result through the new generic derivation.

## Charge 3 — the deepTwist boundary after LRS, exactly

Per the landed iff (`deepTwistField_iff_universalPerWitness`) the boundary is unchanged
in strength; the SUFFICIENT surface is now (all sufficient-only, constructive normal
forms):

    deepTwist  ⟸  UniversalTauWordDescentSupply           (USUP; unchanged)
                ∧ UniversalSiteCalculusSupply             (rows C0/C1 — bank ⊗ wiring; L2E program)
                ∧ UniversalLadderReadSupply               (row C2 residue; UNCHANGED as the minimal named remainder)
                       ⟸ UniversalCarrierReadSupply      (NEW normal form: read_ker_pow + tie)

Within the row-C2 residue the per-level demanded content is now exactly:
`R(1) = 1` (head, simplified) ∧ the `s ≥ 2` rungs (the `s = 1` rung is PROVED) ∧ the
peel tie — all three fired at once by `CarrierReadLaw`.  Strict progress vs the
pre-LRS boundary: the supplier target for the L2E/D3-spine carrier program is now the
same `read_mul` shape RUNG already produces at rung 2; the remaining research for row
C2 is the D3-03 spine adapter (carrier ⇒ node W-leg exports) + the peel tie, not a new
law genre.

## Honesty

* Uniform in `q`: §§1–3 contain zero numerals, zero `residueCard`, zero S2 data; the
  card-2 collapses appear only in §4's keystone instance, as in WSS §5.
* Nothing weakened: `LadderReadLaw`/`LadderReadSupply`/`WiredSiteSupply` consumed
  verbatim on the conclusion side; every new `Prop` is hypothesis-side of a proved
  reduction; no landed file edited (aggregator import only); IFCG39 untouched.
* `CarrierReadSupply` is NOT claimed necessary: it is strictly stronger per level than
  `LadderReadSupply` (no converse); the minimal named remainder is still
  `LadderReadSupply`, and the honest reading of this unit is "derivable slice proved +
  the residue re-expressed in the shape the carrier program produces."
* The non-closability adjudication is by inspection of the landed structures (free
  fields + fences), recorded above; a machine REFUTATION (a realization violating the
  law) is not constructible from the landed corpus — the only landed realization genre
  is the S2 keystone, whose terminal field has trivial unit group, so it cannot violate
  any of the three clauses.  Flagged honestly rather than overclaimed.

## New statements flagged for the standing review

`CarrierReadLaw`, `CarrierReadSupply`, `UniversalCarrierReadSupply` (supplier-side
interface `Prop`s below the signed surface; no leanspec name touched).

## Verification, repair log, footprint

* Per-increment command run throughout; FINAL: exit 0, 0 errors, 0 warnings, 0 `sorry`;
  AxCheck 13/13 Lean-core (`ladderRead_law_one`, `ladderReadLaw_head_iff_read_one`,
  `CarrierReadLaw`, `CarrierReadSupply`, `carrierReadSupply_of_shallow`,
  `ladderReadLaw_of_carrierRead`, `carrierReadLaw_of_mult_agree`,
  `ladderReadSupply_of_carrierReadSupply`, `wiredSiteSupply_of_bank_carrierRead`,
  `UniversalCarrierReadSupply`, `universalLadderReadSupply_of_carrierRead`,
  `deepTwistField_of_carrier_supplies`, `s2Four_carrierReadSupply`).
  `lake build Uniformity.ChapI.I10LadderRead` — success (8970 jobs); aggregator exit 0.
* Repair log: EMPTY — every proof compiled on the first attempt (the WSS §5 keystone
  pattern and the D04/D08/IFC2 generic layer supplied everything; no cross-boundary
  defeq issue arose since no calculus term enters this unit).
* Universe note: follows WSS's convention (`{uG, uKt, uL}`, `E` at universe 0); the
  keystone instance pinned `.{0, 0, uL}`.
* Footprint: `leanfinal/Uniformity/ChapI/I10LadderRead.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  No git operation.
