# MovesT E-phase Lean blueprint — Codex semantic audit (rev 5, 2026-07-28)

CORPUS: `lean/LeanUrat/MovesT/` per `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md`
**REV 5** (full 4023-line blueprint). NOTE: `lean/notes/MOVES_2026-07-24.md`
§T-ASSEMBLY, rev 7, body lines 6970–7761 (dual-accepted 2026-07-27, unchanged
since rounds 1–4's audits). This is the FIFTH round on this blueprint, and a
monotone-convergence sequence up to round 4: round 1 found 35 crit / 10 gap
(`MOVEST_AUDIT_CODEX_2026-07-28.md`) + Fable 5/8
(`MOVEST_AUDIT_FABLE_2026-07-28.md`), DUAL-REJECTED. Round 2 found 21 crit /
4 gap (`MOVEST_AUDIT_CODEX2_2026-07-28.md`) + Fable 3/4
(`MOVEST_AUDIT_FABLE2_2026-07-28.md`), DUAL-REJECTED AGAIN. Round 3 found 18
crit / 5 gap (`MOVEST_AUDIT_CODEX3_2026-07-28.md`) + Fable 2/4
(`MOVEST_AUDIT_FABLE3_2026-07-28.md`), DUAL-REJECTED AGAIN. Round 4 found 9
crit / 4 gap (`MOVEST_AUDIT_CODEX4_2026-07-28.md`) + Fable 1/1
(`MOVEST_AUDIT_FABLE4_2026-07-28.md`); the round-4 verdicts AGREED the entire
round-3 union was genuinely repaired, with Fable-4 walking both rev-4 headline
repairs at the built signatures and Codex-4 landing nine fresh rows led by
counter-models against the two rev-4 mechanisms themselves. Rev 5, submitted
this round, claims to disposition the UNION of both round-4 verdicts (Codex-4's
9/4 + Fable-4's 1/1 = 15 rows) via a §7 "REV-5 DISPOSITION TABLE" (12 F / 2 F*
/ 1 BDY claimed), with the one standing BDY row (W4-1) and one standing F* row
(S-2 / `ns_bridge`) carrying THIRD-ROUND comparisons (both round-4 verdicts +
the note/contract text quoted in place at §5), and five headline repair
mechanisms: `ScaleFaithful`/`KBTotTower`, the GAP-form `hMgrow`, derived
rigidity (`vtree_ext_eq`/`AofTr_shape_const`) replacing the deleted `hfin`/
`hA`, a fully displayed `ClusterFactorOf`, and two toy carriers (A/B) in T-G1.

SEAM CONTRACTS cross-checked against, pasted verbatim into the prompt (all
three line ranges verified unchanged since round 4's audit): MovesD blueprint
§2.5 (the §W4-SYNC contract, `MOVESD_LEAN_BLUEPRINT_2026-07-28.md` lines
318–379), MovesS blueprint's ratification addenda + §W4-SYNC seam contract
(S-1..S-11 + 2 addenda, `MOVESS_LEAN_BLUEPRINT_2026-07-28.md` lines
1104–1349), HC-2's Wall A/B/C architecture notes
(`HC2_LEAN_BLUEPRINT_2026-07-28.md` lines 66–139).

Charge: `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`, instantiated for
CORPUS = MovesT / NOTE = §T-ASSEMBLY, with an APPENDING paragraph (this
round's addition) directing the auditor to: (a) treat the round-3-and-earlier
union as RE-ARMED and independently confirmed DEAD by Fable-4 at the built
signatures (LedgerIV import, wchain/w-mult clause, capped ladder, §7 table
quote-faithfulness), so the burden on any recurrence claim is a fresh
COUNTER-COMPUTATION, never re-assertion; (b) verify the five rev-5 repair
mechanisms head-on (`ScaleFaithful`/`KBTotTower` against Codex-4 #1; the
GAP-form `hMgrow` against Codex-4 #2; the derived rigidity replacing
`hfin`/`hA` against Codex-4 #4; the displayed `ClusterFactorOf` against
Codex-4 #7; the two toy carriers against Codex-4 #13/Fable-4 G-1); (c) sweep
the entire rev-5 text fresh with the standard five-point checklist, including
§4's Q-fence and §5's seam accounting (claimed unchanged, 1/4/12/2 = 19); (d)
give an acceptance-or-exact-residue verdict, every finding a genuine
counter-computation quoted against the pasted rev-5 text.

Run: `codex exec --skip-git-repo-check --sandbox workspace-write -` (stdin;
the assembled prompt was 379,045 bytes, over the 128KB argv-safe threshold, so
stdin was mandatory). The entire corpus (instantiated charge + appending
paragraph + the frozen 6970–7761 note excerpt + all three seam-contract
sources + the full rev-5 blueprint) was pasted inline into the prompt, not
read from the repo, per the paste-context rule; the codex working directory
(`/tmp/leanaudit_t5`) does not contain the repo, so no shell-based cross-check
of the actual `.lean`/`.olean` tree was possible or attempted this round
(consistent with the charge telling the auditor to trust the build-check
record rather than re-verify it). Run detached via `nohup … &` with output
redirected to file, then polled to completion in the foreground; first attempt
succeeded, no retry needed. Session `019faaf0-f319-7c91-aefb-db85b888bd59`,
137,033 tokens, wall time ≈6 minutes. Full transcript: `/tmp/leanaudit_t5/codex.log`;
prompt assembly: `/tmp/leanaudit_t5/prompt.txt` (charge+appending, the frozen
note excerpt, the three seam-contract sources, the full rev-5 blueprint).

## Verdict

**REJECT (6 crit / 6 gap)**. A further numeric improvement over round 4's 9
crit / 4 gap on the critical count, though the gap count rose (4 → 6); no
zero-residue pass yet, and no monotone convergence to zero this round on
either axis when both are counted together (13 → 12 union findings). Four of
the six criticals (findings 1, 4, 5, 6 below) are direct fresh
counter-computations against four of the five flagged rev-5 repair
mechanisms — `KBTotTower` (a childless-tower model bypassing `ScaleFaithful`
entirely), the displayed `ClusterFactorOf` (a `trackOf := 0` witness making
`OmSat` vacuous), the `hdict` premise replacing `hfin`/`hA` (an unlicensed new
open hypothesis, structurally the same defect as the deleted ones), and the
two-toy-carrier T-G1 fix (a literal `Realizes ∧ ¬Realizes` contradiction on
carrier A). One (finding 2) is the THIRD-ROUND adjudication of the standing
W4-1 BDY row, arguing the boundary declaration does not cure the underlying
vacuity of `eligibleT_iff_child` itself. One (finding 3) is a fresh
structural finding on `SibCount`'s missing finiteness hypothesis, not
previously raised in this form. The six gaps concern the two undisplayed
values inside `ScaleFaithful` (`hScale`/`hRes`), the still-nominal `ns_bridge`
Prop (echoing the rev-5 table's own disclosed F* residual), a missing
`trackOf` parameter on `belowEnt`/`SubtreeFiber`, a representative-key
injectivity gap in T-D11's `fibOf`, T-G1's carriers still not fully
closed-form, and T-E10's bundling/undisplayed `shapeExp`. Codex recounts the
§5 seam tally (1+4+12+2 = 19) as correct and does not challenge it.

## CRITICAL findings (6)

1. **`KBTotTower` still admits a childless tower.** Against
   `scale_grow : ∀ (H : History p F), (∀ N' h, ∃ x, (Tat N' h).mem (some H) x) →
   ∃ Jat …`: take every `Tat N h` to be root-only, with `mem none x` true,
   every `mem (some H) x` false for nonempty `H`, and every child relation
   empty. Then `KBTot.dichotomy` and `KBTot.ns_lumps` are vacuous (no history
   is realized), and for every fixed nonempty `H` the antecedent of
   `scale_grow` is false, so `KBTotTower` holds without ever invoking
   `ScaleFaithful` or the growing ladder — contradicting the note's level-0
   covering clause ("At level 0, `m_i = 1` gives τ-hen and `m_i ≥ 2` opens the
   window — total"). The rev-5 mechanism addresses childlessness only below
   an already-realized history; it does not enforce the root-to-track
   existence part of `(c2)`.
2. **W4-1 remains vacuously satisfiable at its own semantic layer.** Against
   `theorem eligibleT_iff_child … : T.child o ν x ↔ eligibleT T CA o ν x` with
   `eligibleT … := ν ∈ CA.branchSetOf (CA.cellOf (embE o) x)`: constant-false
   `T.child`, `CA.Cell := Unit`, and every `branchSetOf` empty satisfies the
   theorem identically — exactly the instance the W4-1 contract text
   forbids ("NO `eligible := child` vacuity … the root-only childless tree
   must not satisfy the law for realizable inputs"). `rootOnly_childless_rejected`
   operates through `fiberAt`, and `KBTotTower` is a different ledger layer;
   neither falsifies the W4-1 semantic structure itself, so declaring the
   requirement a boundary does not make the proposed Lean interface
   faithful.
3. **`SibCount` is stronger than the displayed finite-subtree SIB kernel.**
   Against `(∃ hν Tsub leafSpec nsSpec, S ν = {x | ContFiber T … Tsub … x}) ∨
   S ν = Set.univ`: `Tsub : Set (History p F)` carries no finiteness
   hypothesis, so `SibCount` demands the product law for continuation events
   representing arbitrary, potentially infinite subtrees, where the note
   quantifies only over "a PRESCRIBED FINITE SUBTREE `T_j`" — the central
   open hypothesis has been silently strengthened, propagating to
   `SibCountShallow`, T-S1, and T-S3.
4. **`VPPinned.om_sat` remains vacuously satisfiable for a bad `trackOf`.**
   Against the displayed `ClusterFactorOf` (monic ∧ degree = cluster degree ∧
   reduction = own track's factor power ∧ divides a realized monic degree-n
   f) and `fη.map PadicInt.toZMod = trackOf (…) ^ (fη.natDegree /
   (trackOf …).natDegree)`: no irreducibility, monicity, or positive-degree
   law is imposed on `trackOf` itself. Choosing `trackOf ν := 0` makes the
   displayed right side `0` or `1` against a monic positive-degree `fη`, so
   `ClusterFactorOf` has no witnesses and `OmSat` holds vacuously — the
   declared OM-SAT citation ("the branch's cluster factor `f_η` … is
   IRREDUCIBLE…") is not pinned.
5. **T-E10 replaces the deleted `hA` with another unlicensed hypothesis.**
   Against `(hdict : ∀ Tr … ∀ H ∈ Tr.chains, (Lat Tr h).siteExp H = shapeExp
   (shapeOfH H n))`: the note derives site-volume shape dependence from
   `(JC-root)`, C.3/L3 for `(JC-single)`, and the side-product form for
   `(JC-multi)` — it does not name an additional open "dictionary law."
   `SiteLedger.siteExp` remains arbitrary enough that the displayed equality
   is not derivable from `ShapeEquiv`, `hjcm`, or the existing ledger fields,
   so `AofTr_shape_const` derives constancy only by assuming essentially the
   missing conclusion-content premise in pointwise form — structurally the
   same defect as the deleted `hfin`/`hA`.
6. **T-G1 contains mutually contradictory gate statements.** `toyTreeA` is
   defined with `henV = ∅`, yet the unit states both `toy_fiber_ne : ∃ x,
   toyTreeA.fiberAt toyModel toyχ x` (i.e. `Realizes toyTreeA`) and
   `toy_henflip_unrealizable : ¬ Realizes toyModel toyχ
   (toyTreeA.withHenV ∅)`. Since `toyTreeA.henV` is already `∅`, the record
   update `toyTreeA.withHenV ∅` is the same tree, so the two theorems assert
   `Realizes toyTreeA` and `¬ Realizes toyTreeA` simultaneously.

## GAP findings (6)

7. `ScaleFaithful` (`Mlev J N' = hScale H N' ∧ M₀ J = hRes H`) depends on two
   undisplayed future values (`hScale`, `hRes`); a bracketed "E-phase-bound"
   promise does not pin them, leaving the principal rev-5 non-vacuity
   mechanism underspecified.
8. `ns_bridge : Prop` inside `ns_null := NsAmendedPair pol ∧ ns_bridge` gives
   no typed finite-to-profinite assertion, measure space, or conclusion
   `μ((τ-ns) class │ Σ) = 0`, and can be instantiated with `True` — it does
   not yet represent the missing hypothesis-field the note's
   continuity-from-above step demands (this echoes the rev-5 table's own
   disclosed F* residual on this row rather than adding new information).
9. The rev-5 subtree-scope repair (`SubtreeFiber`, `belowEnt`) is supposed to
   inspect the shared `trackOf` accessor at `.red g ψ` per its own
   explanatory text, but neither `SubtreeFiber` nor the undisplayed
   `belowEnt` receives `trackOf` as a parameter, so the `.red` scope central
   to the T-E7/T-E8 repair is not actually pinned.
10. T-D11's `leafV := fun H => (the unique ct.leafV entry at H's address …)`
    is well-defined only given injectivity of `a ↦ reprOf a.2` on class
    addresses; `ClassTree.hkeys` gives uniqueness by class address, not
    representative-history uniqueness, and `fibOf` receives only
    `PrefixCoherentRepr`, not an explicit `ClassFiberWelldef`-style
    injectivity theorem — a different well-definedness gap from the
    round-4 list-permutation defect (Codex-4 #8, now fixed by the `Finset`
    re-carry).
11. T-G1's carriers still retain non-closed-form fields (`toyModel := { mem
    := toyMemA, child := toyChildA, … }`, "remaining Node fields are
    E-phase-bound junk") that feed `childWidth`, `IrrHalts`, `HistLawful`,
    and `fiberAt`, not merely proof arguments; combined with the many
    carriers and theorems packed into G1a/G1b this also reads as a hidden
    multi-lemma unit (largely a restatement of the rev-5 table's own
    disclosed boundary on this row, per its "day-one duty" framing).
12. T-E10 bundles three substantial prerequisites (`vtree_ext_eq`,
    `shapeClass_finite`, `AofTr_shape_const`) ahead of `perShape_law` inside
    one nominal unit, and its `shapeExp (shapeOfH H n)` has no displayed
    definition (only an "E-phase-bound" promise), preventing a check that
    `hdict` (finding 5) actually expresses the note's per-site exponent.

## Recounts (Codex's own, matching the blueprint's claimed tallies)

* §5 seam rows: "the §5 arithmetic itself recounts correctly: 19 seam entries
  with the advertised `1 + 4 + 12 + 2 = 19` status tally. The two Q-fence rows
  are correctly excluded from that count." No challenge to the tally.
* §7 disposition rows: not separately recounted by Codex in this pass (no
  arithmetic objection raised against the claimed 12 F / 2 F* / 1 BDY = 15).

## Disposition

Rev 5 continues the campaign's improvement on raw critical count (9 → 6) but
the combined critical+gap count is essentially flat (13 → 12), so this is not
yet the zero-residue pass. The charge's "fresh counter-computation, not
re-assertion" standard is met cleanly by four of the six criticals: findings
1, 4, 5, and 6 land squarely on four of the five repair mechanisms the charge
specifically asked to be checked (`ScaleFaithful`/`KBTotTower`, the displayed
`ClusterFactorOf`, the `hdict` replacement for `hfin`/`hA`, and the two-toy-
carrier T-G1 fix), each with an explicit countermodel, witness value, or a
direct logical contradiction (finding 6) rather than repeated prior prose.
Finding 2 is the requested third-round adjudication of the standing W4-1 BDY
row — Codex does not dispute the quoted texts (as both round-4 auditors
already certified them faithful) but argues the boundary declaration does not
cure the underlying vacuity, i.e. it presses the adjudication rather than
re-litigating the quotes. Finding 3 (`SibCount`) is a genuinely new
structural finding from the fresh sweep, with no round 1–4 antecedent found
in this file's own text or the prior four audit files. Of the six gaps, three
(9, 10, and the "different from round 4" half of 12) are fresh technical
points not raised before in this form; the other three (8, 11, and the
`shapeExp`-fence half of 12) substantially restate residuals the rev-5 table
itself already discloses as open (the `ns_bridge` value, the G1a proof-field/
Node-payload boundary, and E-phase-bound values generally) rather than
surfacing new information — a reader adjudicating this round should weigh
those three lower than 7, 9, 10, 1–6. The GAP-form `hMgrow` (repair mechanism
b) drew no fresh finding this round, consistent with it surviving unchallenged.
A rev 6 addressing the six criticals (priority on 1, 4, 5, 6, since these
are the four newest headline mechanisms) and the non-redundant gaps (7, 9, 10)
should be re-audited against this file plus the parallel Fable-5 pass.
