# MovesT E-phase Lean blueprint — Codex semantic audit (rev 3, 2026-07-28)

CORPUS: `lean/LeanUrat/MovesT/` per `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md`
**REV 3** (§T-ASSEMBLY, full 2963-line blueprint). NOTE: `lean/notes/MOVES_2026-07-24.md`
§T-ASSEMBLY, rev 7, body lines 6970–7761 (dual-accepted 2026-07-27, unchanged since
rev 1's and rev 2's audits). This is the THIRD round on this blueprint. Round 1
(fresh sweep of the from-scratch draft) found 35 crit / 10 gap
(`MOVEST_AUDIT_CODEX_2026-07-28.md`) + Fable 5 crit / 8 gap
(`MOVEST_AUDIT_FABLE_2026-07-28.md`) and DUAL-REJECTED. Round 2 (fresh sweep of
rev 2, which claimed to repair the round-1 union) found 21 crit / 4 gap
(`MOVEST_AUDIT_CODEX2_2026-07-28.md`) + Fable 3 crit / 4 gap
(`MOVEST_AUDIT_FABLE2_2026-07-28.md`) and DUAL-REJECTED AGAIN. Rev 3, submitted
this round, claims to repair the UNION of both round-2 verdicts via a §7 "REV-3
DISPOSITION TABLE" dispositioning all 32 round-2 findings one by one (F = fixed,
R = redesigned, PB = pushed back — 21 F / 11 R / 0 PB claimed), plus a rebuilt §5
SEAM ACCOUNTING whose headline DISCHARGED/REDUCED/SUPPLIED/NOT-OURS tally (1/4/
12/2 over 19 seam entries) it claims is now row-faithful (round 2's own tally had
contradicted its own table — round-2 finding #25/G-1). The named pushback from
round 2 (finding #20: the S-3 `W3_recursion` NOT-OURS tag ruled NOT JUSTIFIED
against the MovesS contract's own preamble) is claimed REVERSED this round: S-3
is re-tagged SUPPLIED, with a new `hxrbStmt`/`w3Rekeyed` pair in the blueprint's
§2.10 stated over the imported, already-built `MovesS.RS1Meas.βmeas`.

SEAM CONTRACTS cross-checked against, pasted verbatim into the prompt (all three
line ranges verified unchanged since round 2's audit): MovesD blueprint §2.5 (the
§W4-SYNC contract, `MOVESD_LEAN_BLUEPRINT_2026-07-28.md` lines 318–379), MovesS
blueprint's §W4-SYNC seam contract + both ratification addenda (S-1..S-11 + 2
addenda, `MOVESS_LEAN_BLUEPRINT_2026-07-28.md` lines 1104–1349 — this is the
range containing the S-3 contract sentences the blueprint's §5 row quotes: "the
contract MovesT/MovesV re-key when their vocabulary exists" and S-3's prescribed
re-keyed premise shape), HC-2's Wall A/B/C architecture notes
(`HC2_LEAN_BLUEPRINT_2026-07-28.md` lines 66–139).

Charge: `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`, instantiated for
CORPUS = MovesT / NOTE = §T-ASSEMBLY, with an APPENDING paragraph (this round's
addition) directing the auditor to: (a) verify each of the round-2 Codex pass's
15 recurrent base-layer findings one by one against the disposition table's
claimed repair, checking specifically for the "name for a future value, not the
value" pattern under new vocabulary, and likewise spot-check the seam-map
findings 16–25 and the ported Fable-2 rows; (b) adjudicate the S-3 pushback
reversal directly against the pasted MovesS contract text — does `hxrbStmt`
actually state the contract's prescribed equality over the right object with the
right quantifiers, and does `w3Rekeyed`'s conclusion match the contract's actual
`W3_recursion` obligation (a wrong reversal counts as a fresh CRITICAL, exactly
as a wrongly-sustained pushback would have); (c) recount §5's seam-map tally from
its own rows and re-check every DISCHARGED/SUPPLIED row (especially S-9, Wall A,
and any row whose status moved this round) against the pasted contracts; (d)
sweep the entire rewrite fresh for new defects, including the two units new at
rev 3 (T-V9, T-D15) with no round-2 antecedent to check against.

Run: `codex exec --skip-git-repo-check -` (stdin; the assembled prompt was
290,784 bytes, over the 128KB argv-safe threshold, so stdin was mandatory).
Sandbox: `workspace-write` (the harness's default; the shell inside was in fact
unavailable to Codex per its own report at GAP-19 below — it could not
independently open the repo to confirm the blueprint's "MovesS is BUILT"
claim, so it correctly downgraded that specific check to a GAP rather than
either trusting or silently dropping it). The entire corpus (note excerpt + all
three seam contracts + the full rev-3 blueprint) was pasted inline into the
prompt, not read from the repo, per the paste-context rule. First attempt
succeeded, no retry needed. Model `gpt-5.6-sol`, session
`019faa58-cd59-7dc2-bbd3-794cafd81950`, 125,583 tokens. Full transcript:
`/tmp/leanaudit_t3/codex.log`; prompt assembly: `/tmp/leanaudit_t3/prompt.txt`
(four parts — the instantiated charge + appending paragraph, the frozen
6970–7761 note excerpt, the three seam-contract sources, the full rev-3
blueprint).

## Verdict

**REJECT (18 crit / 5 gap)**. An improvement in raw count over round 2's 21
crit / 4 gap, but the pattern round 2 diagnosed — a repair supplying a NAME for
a future value rather than the value the contract or the note actually demands —
recurs throughout rev 3's own supposedly-repaired rows (findings 3, 8, 10, 13, 14,
18 below), and several round-2 base-layer findings recur in only-cosmetically-
different form (findings 1, 2, 5, 6, 7, 9, 11, 12, 15, 16, 17). Codex judged the
§5 arithmetic tally itself correct this time (1 DISCHARGED / 4 REDUCED / 12
SUPPLIED-PARTIAL / 2 NOT-OURS over 19 rows checks out), but held that the
numerical correction does not validate the rows' semantic *statuses* — four of
the specific rows it names (W4-1, S-2/S-9, S-3, S-6) fail on inspection for the
reasons in the findings below.

## Named pushback ruling (S-3 reversal, this round's central adjudication)

**PARTIALLY JUSTIFIED, BUT THE REPAIR IS INCOMPLETE — counted as fresh CRITICAL
finding 18.** Codex confirmed `hxrbStmt` gets the reversed ruling's substance
right: it is stated with the correct `B₀ : MovesS.RS1Meas T' M`, the correct
pool quantifier, the two height variables, and the βmeas equality the contract's
S-3 entry prescribes — so the round-2 ruling that "βmeas is not stateable in this
corpus" was indeed false, as round 2 held, and rev 3's `hxrbStmt` is genuine
evidence for that. But the contract's `W3_recursion` itself is premised on the
real typed `LedgerIV T' M` object (§W4-SYNC's displayed form, pasted into the
prompt), and rev 3's `w3Rekeyed` instead premises an arbitrary `ledger_iv : Prop`
in its place — supplying only a slot name for that future value, not the value,
which is exactly the failure pattern round 2 named. T-D15 was found to merely
prove this weakened definition unfolds to itself. So: the REVERSAL direction was
correctly decided (S-3 is not NOT-OURS), but the SUPPLIED-tagged object built on
top of it does not yet state the contract's actual obligation.

## CRITICAL findings (18)

1. `IrrHalts` still misencodes τ-irr: the note defines τ-irr by a nonempty read
   history whose accumulated invariants saturate the cluster degree (lawfulness
   is standing perimeter, not part of the halting rule's own definition); rev 3
   silently strengthens τ by folding `NodeDataLawful` into `IrrHalts` while
   `IrrHalts` itself still never states `accE H * accF H = d(cluster)` — T-V9 is
   a separate conditional theorem, not a repair of the definition's semantics.
2. The rev-3 `VTree.fiberAt` degree-conservation clause
   (`(Tr.typemult.map fun ef => ef.1 * ef.2).sum = n`) smuggles a theorem into the
   fiber *definition* and still doesn't express per-track completeness: the note
   defines the fiber by `T_can^τ(f) = T`, with degree conservation a consequence
   of every halted cluster verdict having its own cluster degree; the new global
   degree equation can accept compensating errors between leaves and rejects
   models by fiat rather than expressing the all-and-only tree graph.
3. `KBTot`'s repair (`slot0`/`ns_lumps`) fixes the childless degeneracy only via
   an impossible fixed-level hypothesis: a fixed `JetSetup H n N m` and finite
   `Box p m` cannot supply arbitrarily many independent fresh coordinates as
   `M → ∞`; the note's ladder is profinite/all-cap and needs a compatible tower
   at finite level, so `KBTot` has no stated inhabitation story at a realized
   fixed-level state — T-V6/`vModelOf` can still be vacuous, and the claimed
   childless-model falsifier improperly invokes later pricing theorems `KBTot`
   itself doesn't contain.
4. T-V8/T-V9 remain stronger than their premise: `HistLawful` lacks at least the
   initial `Dwidth = 1` datum the telescope to `childWidth` needs, and its
   p-power cardinality clauses don't supply the cross-level `wchain` relation —
   the blueprint's own prose defers the missing piece to a future SW1b, but the
   present theorems universally assert the conclusion from the weaker displayed
   predicate today.
5. `CapIrrLaw`/`tbcap_irr_family`'s cross-level cap is incorrectly typed: it
   holds `m` fixed while quantifying over `N'`, but the canonical finite boxes
   change with the level (`m = n * N'` elsewhere in the same blueprint), so this
   is not one cap across the family of level-`N'` cylinders TREE-N actually
   consumes; `capIrrOf J₀` also stays a supplied reference-jet choice rather than
   an independently-defined function of the realized halting class.
6. T-C7's repair (`JetTower`/`hMgrow`/`hne`) omits the hypothesis its own proof
   needs: no `ZCPack (Jat N' h)` or equivalent admissibility premise is present,
   while T-C5's admissible-`Z_M` construction explicitly requires `hzc : ZCPack J`
   — `NsLumpFamily.vanish`/`slot0` alone don't imply the equations are free on the
   state or priced by Theorem C(b), so the stated limit permits families outside
   the accepted `(ZC)` mechanism.
7. The root-conditioned-entrance repair (`child_cell_red`) states only one
   implication of all-and-only child keying: at a reduction-cell entrance the
   note's branch set is ALL eligible branches of the selected track, but
   `SibCount` quantifies over `branchSetOf c`, so a `CellAssign` may omit actual
   siblings and get a weaker product law — the missing converse is promised for a
   future canonical instance and is absent from every E-layer hypothesis.
8. The `SideSplit` redesign (`clausesOf`/`hpartition`/`sideExp`) still erases
   `(JC-multi)`'s open content: nothing ties `clausesOf j` to side `j`'s actual
   literal equation system, to `sideOf`, or to the note's shared-hinge
   consistency — any arbitrary partition of `fd.clauses` qualifies, so the
   exponent sum is definitionally the total fresh-clause count and `JCmultiAt`
   silently decides the open multi-side theorem rather than stating it.
9. T-E7/T-E8 have no equality tying the split charge to the ledger charge: no
   field asserts `splitFrame.jointExp = L.siteExp H`, yet T-E7 uses the former
   while TREE-EXP's conclusion sums the latter, and neither `hframe` nor
   `splitAt` supplies the missing bridge — the induction sketch cannot produce
   T-E8's displayed exponent as stated.
10. `fiber_root_split`'s root decomposition (`RootSplitData Tr g`) is still extra
    future data, not a consequence of realizability: TREE-EXP's root clause is
    asserted by the note for every realizable tree, but rev 3 proves only a
    conditional identity after being HANDED a root partition, head enumeration,
    child-root proofs, and root-cell containment — no theorem/hypothesis states
    that every `hreal : Realizes T χ Tr` actually supplies these values, the same
    "name for a future value" pattern.
11. `TreeScaffold`'s `hdecomp` field for T-E8 assumes the central AND-over-nodes
    first-split fiber identification as a HYPOTHESIS rather than deriving it —
    that identification is part of TREE-EXP's proof content in the note, not an
    owner-supplied premise; `subtree_part` is also too weak, its existential
    subtree specs sitting inside the event without identifying the fixed
    `ContFiber` witness from `SplitSiteData.hS`. T-E8 is both weaker than the
    note and unsupported by its own sketch.
12. T-E10's per-shape law (`hfin`/`hA`) is vacuously satisfiable and
    over-conditioned: with no premise `NsFree Tr₀ ∧ Realizes T χ Tr₀`,
    `shapeClass Tr₀ T χ` may be empty, making the theorem `0 = 0` for an
    arbitrary representative; the note derives finiteness and exponent constancy
    from the realized shape/site theory, while rev 3 simply assumes both as new
    hypotheses.
13. S-2/S-9's re-key of `(ns-null)` (`ns_null := NsAmendedPair pol`, "FINITE FACE
    ONLY") is a weaker statement than the contract demands: the note's
    `(ns-null)` conclusion is the actual conditional measure-zero claim, and the
    MovesS registry needs that real owner statement, not a truncated-ratio
    theorem plus a rider asking another corpus to supply the missing bridge —
    still a name for a weaker future value.
14. The W4-1 non-vacuity repair does not make the contracted interface false on
    the prohibited instance: a childless `TreeModel` with constant `CellAssign`
    still satisfies `eligibleT_iff_child` definitionally; the separate
    `rootOnly_childless_rejected` fiber theorem rejects one VTree via the added
    global degree clause (finding 2) but does not falsify the W4-1 semantic
    layer itself on that instance — the exact contract non-vacuity demand is
    still unmet.
15. T-D10/T-D11's `fibOf`/`nsLeaf` rule ("the looked-up verdict is a
    replicate — nsVerdict-shaped") misclassifies data: every irreducible
    singleton verdict is also `Multiset.replicate 1 (E,F)`, so ordinary τ-irr
    leaves get classified as τ-ns leaves; `ClassTree` also imposes no
    uniqueness/maximal-address condition on its association list — `fibOf`
    cannot establish `hleaf`, `hns_leaf`, or the canonical-tree fiber key S-7
    demands.
16. T-D14's chain-charge telescope (`hparent`, `chain_charge`) lacks
    immediate-parent connectivity: `hparent` permits a read to use ANY earlier
    prefix, not the immediately preceding read in `chainReads`, so iterating T-E6
    can skip or duplicate intermediate conditioning states while the exponent
    still sums every read; `state_cell` does not repair this, and the displayed
    telescope is false for such ledgers.
17. T-D14 also violates the note's own `(BDY)` indexing convention: `L :=
    (chainReads Tr H).length` while `charge r` indexes by list position and
    `(BDY)` sums through `Finset.Icc 0 L` — for a length-`k` list the valid read
    indices are `0,…,k−1`, so setting `L = k` creates a phantom terminal read of
    zero charge and admits `fe = k`; the contract's inclusive `0…L` convention
    treats `L` as the last read index, not the count of reads.
18. The S-3 reversal gets `hxrbStmt` right (see the pushback ruling above) but
    `w3Rekeyed` still does not state the full contracted W3 object: the
    contract's `W3_recursion` is premised on the real typed `LedgerIV T' M`, and
    rev 3 substitutes an arbitrary `ledger_iv : Prop` in its place — a slot name
    for that future value, not the value; T-D15 merely proves the weakened
    definition unfolds to itself.

## GAP findings (5, #19–23)

19 (the claimed MovesS dependency is internally inconsistent and could not be
externally confirmed: the Defs import roster lists only `Mathlib`,
`LeanUrat.MovesD.Defs`, `LeanUrat.MovesSp.Defs`, while §2.10 uses
`MovesS.TableShape`/`MovesS.RS1Meas`/`MovesS.evalRe`, and the blueprint's later
claim of an `Interfaces` import is not reflected in the normative import list;
Codex's shell was unavailable this run, so the claimed built/sorry-free MovesS
source files could not be independently opened and confirmed — flagged as an
evidentiary gap rather than assumed either way); 20 (`PCI` still depends on the
undisplayed `SubtreeTransport TsubAt es es' ν → ...`, which decides whether two
subtree events represent the same child CTS state — precisely PCI's semantic
content — and is deferred to E-phase); 21 (T-D10/T-D11 remain schematic: the
displayed `ClassTree` has no root-payload component for `henV`, and
`fibOf_fiber_disjoint`/`fibOf_partition` retain ellipses in their statements —
load-bearing S-7 deliverables, not harmless plumbing); 22 (`ClusterFactorOf`/
`UnramifiedOfDeg` remain pointer-only without displayed definitions, though they
encode the exact factor assignment and (E,F) conclusion of the frozen VP-SOUND
declarations); 23 (the non-vacuity gates `toyModel`/`toyCA`/`toy_e5_instance`
that are supposed to certify inhabitation of `CellAssign`/`VerdictModelT`/
fibers/SIB retain ellipses in both their defining data and several theorem
statements, so they cannot presently certify anything).

## Disposition

Rev 3 is again a genuine numeric improvement (18+5 vs. round 2's 21+4 — fewer
gaps, comparable overall count, and Codex now certifies the §5 arithmetic tally
itself is internally consistent, closing the specific defect named at round-2
#25/G-1). But eleven of the eighteen criticals (1, 2, 5, 6, 7, 9, 11, 12, 15, 16,
17) are round-2 base-layer or seam findings that recur in only superficially
different form under rev 3's new vocabulary, and six more (3, 8, 10, 13, 14, 18)
are new instances of exactly the failure mode round 2 diagnosed by name — a row
or theorem supplying a NAME/SLOT for the value a contract or the note's display
actually demands, rather than the value itself (`KBTot`'s fixed-level ladder,
`SideSplit`'s untied partition, `fiber_root_split`'s handed-in root data, the
finite-face `(ns-null)` re-key, the still-satisfiable W4-1 interface, and now
`w3Rekeyed`'s bare `ledger_iv : Prop` in place of the contract's real
`LedgerIV`). The S-3 pushback reversal itself is only half-vindicated: Codex
confirms the reversal's premise was correct (βmeas is indeed stateable here, and
`hxrbStmt` states it correctly against the pasted contract text), but the object
built on top of that correct premise (`w3Rekeyed`) does not yet state the
contract's actual `W3_recursion` obligation — so the reversal is directionally
right but its supplied repair is not yet complete, and is counted as finding 18
rather than validated outright. One evidentiary gap (#19) is procedural rather
than semantic: Codex's sandbox this run could not independently read the repo to
confirm the blueprint's claim that `LeanUrat.MovesS`/`LeanUrat.HC2` are built and
sorry-free, so that specific claim should be re-verified by a build check
(`lake build` / `#print axioms`) rather than re-argued in prose at rev 4.
