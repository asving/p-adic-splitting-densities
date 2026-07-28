# MovesT E-phase Lean blueprint — Codex semantic audit (rev 2, 2026-07-28)

CORPUS: `lean/LeanUrat/MovesT/` per `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md`
**REV 2** (§T-ASSEMBLY, full 2109-line blueprint). NOTE: `lean/notes/MOVES_2026-07-24.md`
§T-ASSEMBLY, rev 7, body lines 6970–7761 (dual-accepted 2026-07-27, unchanged since
rev 1's audit). This is the RE-AUDIT of rev 2, which rev 2's own header claims
repairs the union of the rev-1 dual-reject verdicts (Codex 35 crit / 10 gap,
`MOVEST_AUDIT_CODEX_2026-07-28.md`; Fable 5 crit / 8 gap,
`MOVEST_AUDIT_FABLE_2026-07-28.md`), via a rebuilt §5 SEAM ACCOUNTING (status
semantics DISCHARGED/REDUCED/SUPPLIED/NOT-OURS, headline tally 21 = 19 seam
entries + 2 fenced Q1/Q2 rows) and a new §7 REV-2 DISPOSITION TABLE (finding-by-
finding fixed/redesigned/pushed-back over the full union of both rev-1 verdicts).

SEAM CONTRACTS cross-checked against, pasted verbatim into the prompt (all three
line ranges verified unchanged since rev 1's audit): MovesD blueprint §2.5 (the
§W4-SYNC contract, `MOVESD_LEAN_BLUEPRINT_2026-07-28.md` lines 318–379), MovesS
blueprint's RATIFICATION ADDENDA + §W4-SYNC contract (S-1..S-11 + 2 addenda,
`MOVESS_LEAN_BLUEPRINT_2026-07-28.md` lines 1105–1346), HC-2's Wall A/B/C
architecture notes (`HC2_LEAN_BLUEPRINT_2026-07-28.md` lines 66–139).

Charge: `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`, instantiated for
CORPUS = MovesT, with an APPENDING paragraph (this re-audit's addition) directing
the auditor to: (a) verify the §5 seam-map tally and spot-check every DISCHARGED/
SUPPLIED row against the pushback trap named in rev 1 ("the contract demands X;
the unit supplies a name for X's future value, not X"); (b) spot-check a sample
of §7's disposition-table entries against the actual repaired unit; (c) explicitly
adjudicate the one named pushback, rev-1 Codex finding #29 (S-3 `W3_recursion`,
the deferred `hxrb` premise), against the quoted MovesS contract text, with a
wrong pushback counting as a fresh CRITICAL; (d) sweep the entire rewrite fresh
for new defects, not confined to the disposition table's own pointers.

Run: `codex exec --skip-git-repo-check -` (stdin; the assembled prompt was
223,434 bytes, over the 128KB argv-safe threshold, so stdin was mandatory).
Note: `--sandbox danger-full-access` was blocked by the local harness's auto-mode
classifier on this box; the default read-only sandbox was used instead — no
functional loss, since the charge requires the auditor to write nothing to disk
and the entire corpus (note + all three contracts + full blueprint) was pasted
inline into the prompt, not read from the repo. First attempt succeeded, no
retry needed. Model `gpt-5.6-sol`, session `019faa0c-531b-70a3-add3-46a3b0d20a49`,
87,255 tokens. Full transcript: `/tmp/leanaudit_t2/codex.log`; prompt assembly:
`/tmp/leanaudit_t2/prompt.txt` (four parts — instantiated charge + appending
paragraph, the frozen note excerpt, the three seam-contract sources, the full
rev-2 blueprint).

## Verdict

**REJECT (21 crit / 4 gap)**. An improvement over rev 1's 35 crit / 10 gap, but
still far from ACCEPT, and the pattern rev 1 diagnosed — seam rows claiming
DISCHARGED/SUPPLIED status while actually supplying only a name for a future
value — recurs throughout rev 2's own rebuilt §5 (findings 16–21 below). Several
rev-1 base-layer findings (vacuous `IrrHalts`/`BranchDichotomy`/T-V6, incomplete
`VTree`, T-C2's cap substitution, T-E5's missing decomposition) also recur in
close-to-original form despite rev 2's claimed restatements.

## Named pushback ruling (S-3, rev-1 Codex finding #29)

**NOT JUSTIFIED — counted as fresh CRITICAL finding 20.** Rev 2's §7 records
S-3 (`W3_recursion`'s required re-keyed `hxrb` premise) as NOT-OURS, arguing
`βmeas` is MovesS's object and not stateable in the MovesT corpus. Codex found
the MovesS contract's own preamble explicitly assigns this re-keying to
"MovesT/MovesV when their vocabulary exists," and S-3 explicitly prescribes the
re-keyed premise `(hxrb : ∀ …, B₀.βmeas … = B₀.βmeas …) → …`; referencing
`RS1Meas.βmeas` from the seam unit does not make it unstateable, since a seam
re-key necessarily imports the contract's own vocabulary. Rev 2 has neither
supplied the required conclusion equality nor reduced it to an equivalent typed
bridge.

## CRITICAL findings (21)

**Base-layer findings recurring from rev 1, in close-to-original form (1–15):**

1. `IrrHalts` doesn't encode saturation: it accepts any history ending in
   `ν.μ = 1` without `NodeDataLawful`, `accE * accF = d`, or a cluster-degree
   field, so `fiberAt`/`ContFiber`/`PreHalt`/the verdict model can halt histories
   the note would not halt.
2. `NsHalts`/`BranchDichotomy` still admit the forbidden childless degeneracy:
   the note's no-side case is the specific Theorem-B status J(f) = ∅, not
   arbitrary absence of children in an abstract model; a model with `mem`
   everywhere and `child` nowhere satisfies `BranchDichotomy` vacuously.
3. `VTree`/`fiberAt` still don't express a complete tree: `chains` may be
   empty and nothing relates non-Hensel root tracks to heads of `chains`, so a
   reduction with repeated factors can fiber an empty-chain tree that silently
   omits every unresolved track (no degree-conservation fact either).
4. T-V6 remains vacuous despite its claimed repair: the first disjunct is
   `... → True`, always true, so T-V6 proves no saturate-or-continue disposition
   at all — disposition-table entry Codex #1/#8 is not actually fixed.
5. T-C2 still doesn't state the note's cross-level uniform cap: it is locality
   for one fixed `Presented ... N ...` object; `capIrrOf` still depends on a
   jet whose type/data depend on N, and no compatible family across all
   presented N is quantified.
6. T-C5 is strengthened beyond the displayed (ns) setting: the note fixes a
   realized no-side track with window interior, rim separation, and nonempty
   slot-0 ladder; the theorem quantifies over every `JetSetup` with none of
   those hypotheses.
7. T-C7 is neither the note's nullity statement nor a coherent truncation
   theorem: the displayed term is ill-typed below N₀, there's no
   jet-compatibility across levels, `hM₀` permits a forever-frozen `Mlev = M₀`,
   the denominator may be empty, and the unit supplies only a truncated-ratio
   limit where the note needs a finite-to-profinite continuity-from-above
   bridge.
8. The site state vocabulary still cannot represent the root-conditioned
   entrance state: `parentSt = none` denotes the ambient root, not the
   selected `rootCell`, so there is no carrier for "root state conditioned on
   reduction cell g" — this invalidates the first window step and T-D14.
9. `SideSplit` makes (JC-multi) contradictory or meaningless: `sideExp` is
   unconstrained and untied to the cell's actual per-side systems, so the same
   cell can carry different `SideSplit` values with incompatible exponents,
   while `oneSide` in `FreshData` is untied to `SideSplit.k` and lets a real
   multi-side cell evade `hjcm` by mislabeling.
10. T-E5 still lacks the decomposition needed to apply root (SIB): nothing
    identifies the `Fin t` continuing tracks with `CA.branchSetOf c`, proves
    distinct eligible root-branch heads, or proves the fiber equals the
    intersection of `trackEvent`s; at t = 0 it permits an arbitrary proper
    subset of the root cell while concluding full root-cell cardinality.
11. T-E6 does not follow from `SiteLedger.presents`: `L.presents` never
    identifies the cell event with `stateEvent T (some H)`, nor does `hparent`
    say H is the child/read represented by `cellAt H` — the missing equality is
    precisely the semantic history-to-cell bridge.
12. T-E7 omits the joint-cell charge from its conclusion: `hcharge` is assumed
    but unused; the conclusion is only the SIB count identity after rewriting,
    not the first-split recursion with the `jvol` factor — weaker than the
    quoted TREE-EXP display.
13. T-E8 asserts TREE-EXP without the structural hypotheses its own sketch
    requires: no root-track decomposition, no first-split data per branching
    node, no `stateEvent`/joint-cell equality, no proof the ledger sites are
    exactly the tree's read sites, no child-subtree partition — combined with
    the incomplete `VTree`, the theorem is false on admitted degenerate trees.
14. T-E10 lacks the per-shape constancy hypotheses: nothing states
    `AofTr Tr (Lat Tr) = Ashape T̂`, that the ledger is canonical, or that
    `CofShape` is the cardinality of exactly the summation domain; the
    displayed unrestricted infinite sum also lacks a finiteness/summability
    premise.
15. T-F2 equates class indices with raw histories without a bijection:
    `chainCount` counts histories in `Tr.chains`, but the left side counts
    `PrefIdx` equivalence classes through one representative, and no cited
    lemma gives the needed bijection or proves `PreHalt` invariant across a
    class.

**Seam-map findings — rev 2's own rebuilt §5, the section the re-audit charge
asked to be hit hardest (16–21):**

16. T-D2 does not reject the W4-1 degeneracy: it only proves a model already
    known to have a child has an eligible child, saying nothing about the
    prohibited root-only childless model on a realizable input — effectively
    the forbidden `eligible := child` construction one layer down.
17. W4-2 is not genuinely reduced to completed typed inputs: `VdictCellData`,
    `CapIrrLaw`, and `capData` are undisplayed future packages, `BranchDichotomy`
    admits the childless degeneration (finding 2), and T-C2 does not supply the
    promised cross-level cap (finding 5) — the row's claim that structure,
    vdict values, `halt_iff`, both caps, and both locality laws are in-corpus
    is unverified.
18. T-D12 does not discharge S-9 or genuinely re-key the MovesS registries:
    `XRBPackage`/`RS1GivenPackage`/`Wsh17Package` are parallel MovesT
    declarations, not instances of the actual MovesS contract structures;
    several field values are prose placeholders or undefined Props; the
    blueprint itself says MovesS must later "re-point" the declarations — the
    exact "name for a future value, not the value" failure rev 1 diagnosed.
19. Wall A is labeled SUPPLIED but only a future bridge Prop is named:
    `WallAReconciled T CA ReadsOf` is parameterized by an arbitrary `ReadsOf`,
    supplying neither the real predicate nor an inhabited canonical
    `CellAssign` satisfying it — at most REDUCED, not SUPPLIED.
20. The S-3 pushback is not justified by the contract (see ruling above,
    promoted to a numbered CRITICAL finding).
21. S-6's claimed delivered side is only a conditional carrier: no
    `SiteLedger` instance is constructed from a tree (it is supplied as a
    hypothesis); its `sys`/`cellAt`/`parentSt`/presentation proofs are exactly
    the future semantic values the contract needs; `chain_charge` starts from
    `stateEvent none` (cannot represent the root reduction cell) and handles
    only all-one-side chains — not yet a real per-entered-path `ReadLedger`.

## GAP findings (4, #22–25)

22 (T-C1's finite-union face is prose, not a Lean statement — the displayed
theorem proves locality only, and the required finite union of level-1
cylinders is relegated to prose, contrary to the one-display/unit discipline);
23 (numerous load-bearing definitions remain undisplayed or contain `…`:
`CapIrrLaw`, `StageRealized`, `ClusterFactorOf`, `UnramifiedOfDeg`, `jointExpOf`,
`SubFiber`, `PartitionsDecided`, `TreeShapeOf`/`Ashape`/`CofShape`, `fibOf`,
"(T-E8's statement Prop)", `VPPinned`, `NsAmendedPair` — Defs soundness and
hypothesis fidelity cannot be audited until these are pinned); 24 (T-E13 does
not itself obtain the TGT partition from T-E9: disjointness is derived from
"one f, one tree" in the note, but is here assumed for raw `VTree` values, and
T-E9 yields equality only of an extensional tuple, not of structure values with
proof fields — the promised `VTreeExt`/quotient bridge is deferred to prose);
25 (§5's status tally and §7's disposition claims are not internally verified:
the 21-row headline arithmetic checks out (4+11+2+2+2=21, 19 seam rows + 2 queue
rows), but the stated 19-row status tally "2 DISCHARGED · 3 REDUCED ·
12 SUPPLIED/PARTIAL · 2 NOT-OURS" doesn't match the table itself, which tags
S-3, S-4, and Wall B as NOT-OURS — three, not two — giving eleven, not twelve,
SUPPLIED/PARTIAL; representative §7 claims that don't survive inspection
include Codex #1/#8 (`tau_total` remains vacuous), #5 (`SibCount` reconditioned
but TREE-EXP's site ties remain absent), #11 (E5 still lacks the root
decomposition), #20/#21 (verdict-model/cap repair remains packaged in future
Props), #29 (the pushback is contrary to the seam preamble), #31 (no actual
`SiteLedger` instance is supplied) — so "no finding is left unaddressed" is not
supported).

## Disposition

Rev 2 is a genuine improvement in scale (21+4 vs. rev 1's 35+10) and several
rev-1 findings are cleanly closed by name (T-V5's `∨ True`, T-E9's ns-fiber
ambiguity, T-F1's `∃!` failure, PreHaltPfx's box-dependence, T-F4's inequality-
vs-identity gap, and the JCmulti global-vs-per-site scope issue all do not
recur in Codex's fresh sweep). But the rewrite has NOT closed the two structural
problems rev 1 named as needing "a from-scratch restatement, not local
patches": (i) the VP/tree-model Defs layer (`IrrHalts`, `NsHalts`/
`BranchDichotomy`, `VTree`/`fiberAt`) still admits the same degenerate models
that made rev 1's tautologies possible — T-V6 in particular is verified
unchanged in its vacuous form; (ii) §5's SEAM ACCOUNTING, despite its new
status-semantics vocabulary, reproduces the exact "name for a future value"
failure mode on its own DISCHARGED/SUPPLIED rows (W4-1/W4-2 via T-D2/T-D12,
Wall A, S-6), and its own headline tally arithmetic (the 2/3/12/2 status
breakdown) doesn't check out against its own table, echoing rev 1's finding
#35 about the seam count. The S-3 pushback (rev-1 #29) is adjudicated NOT
JUSTIFIED against the quoted MovesS contract text. Recommend a rev 3 that: (a)
adds an explicit non-degeneracy/inhabitation hypothesis threaded through
`BranchDichotomy`/`NsHalts`/`IrrHalts` rather than patching individual
consumers; (b) for every §5 row currently tagged DISCHARGED or SUPPLIED,
either produces the actual named contract-typed object (not a parallel
MovesT-local structure) or re-tags the row REDUCED/NOT-OURS honestly; (c)
re-derives the T-E5/T-E6/T-E7/T-E8 first-split chain from an explicit root-
track-to-branch-set identification, since T-E8's falsity on admitted
degenerate trees is a direct corollary of the still-incomplete `VTree`
definition (finding 3) rather than an independent defect.
