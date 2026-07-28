# MovesS §S-RESUM — Codex ratification pass on the actual E-phase Lean (2026-07-28)

*Run metadata: OpenAI Codex v0.145.0, model gpt-5.6-sol, `--sandbox danger-full-access`,
session `019fa760-790d-7af0-8994-beb3ad817c02`, workdir = repo root, 202,502 tokens.
Prompt assembled at `/tmp/leanaudit_rats/s_prompt.txt` (158,705 bytes): (1) the
ratification charge (quote-and-classify DIFFERENT/WEAKER/STRONGER/VACUOUS/FAITHFUL,
ADJUDICATIONS A-1/A-2/A-3 binding and not to be re-litigated); (2) the note excerpt
`MOVES_2026-07-24.md` lines 11557–12577; (3) the blueprint's ADJUDICATIONS (lines 3–34)
+ §W4-SYNC seam contract (lines 1104–1334) from `MOVESS_LEAN_BLUEPRINT_2026-07-28.md`;
(4) `MovesS/Defs.lean`, `MovesS/Interfaces.lean`, and grepped theorem/lemma statements
(signature + 4 lines) from all 95 unit files. Full raw transcript at
`/tmp/leanaudit_rats/s_verdict.txt` (Codex used its own shell access inside the
sandbox to additionally read prior audit files and the live blueprint/note directly,
beyond what was pasted into the prompt — this is why some citations below carry line
numbers not in the excerpted ranges).*

## Codex's own summary line

> "Ratification result: the 95-unit core statements are faithful to §S-RESUM, except
> for one explicitly disclosed device-only vacuity in `n2_act`. The proposed §W4-SYNC
> seam design is not yet faithful: seven material defects remain in its shown typed
> forms. I did not revisit A-1, A-2, or A-3."

## Findings (Codex's numbering, verbatim classification)

**On the core (95 units + Defs/Interfaces) — one item:**

8. **VACUOUS — `n2_act`'s inactive-target clause has an impossible antecedent.**
   `N2Act.lean:14` proves `¬activeState → kstep = 0` for the n=2 internal-consistency
   device, but that device is all-active by construction (the file's own comment says
   so), so the hypothesis `¬activeState` is never met. Codex's own qualifier: *"This is
   disclosed and confined to the internal consistency instance; the general
   `LedgerIV.act_target` statement remains faithful."* — i.e. not a defect in the
   general statement, only in the toy n=2 witness's coverage of one branch nobody
   claimed it covered.

**On the §W4-SYNC seam contract (explicitly NOT built at E-phase — pinned pseudocode
in the blueprint, not Lean files) — seven items:**

1. **VACUOUS — `W1_RS1SH`/`W1e_equates` are circular projections.** Both seam
   obligations have conclusions syntactically identical to `Interfaces.lean`'s
   unconditional fields `rs1_equates`/`rsh_interp` (already in `RS4Chain` with no RS.1
   hypotheses attached) — so any instantiation can discharge the "theorem-under-
   hypotheses" pin by citing those existing unconditional fields directly and ignoring
   every premise in the RS.1-SH/RS1GivenPackage list. **Not flagged in S-1's own
   DEMANDS text** — a new finding.

2. **DIFFERENT — `W3_recursion` assumes the XRB *implication*, not XRB's *conclusion*.**
   Reproduces, in the currently-shown code block, exactly the defect the blueprint's
   own **S-3 entry already names as an open DEMAND** ("assume XRB's CONCLUSION … not
   the bare implication; re-keyed form: `(hxrb : ∀ …, …) → …`") — i.e. the shown pin
   has not yet incorporated the fix the seam list already prescribes for itself.

3. **WEAKER — `W7_cutWD`'s no-reclassification fence uses `¬isEntrance`, not "has a
   first-entrance ancestor."** Same pattern: **S-5's own DEMANDS text** already
   specifies the correct re-keyed clause (`∃ ν', isEntrance ν' ∧ onPath ν' ν`); the
   `def W7_cutWD` block shown immediately below it in the same document still has the
   old, weaker clause.

4. **VACUOUS — `W8_bdy`/`ReadLedger` isn't tied to any tree, path, or measured mass**
   (the all-zero ledger satisfies it). Matches **S-6's own DEMANDS** ("tie ReadLedger
   to the tree … charges = the tree's read masses") — already flagged as open.

5. **VACUOUS — `FiberIface`/`W10_convergence` permits an empty, tree-unrelated fiber
   type** (`Fib` empty + `βmeas = 0` satisfies both conjuncts vacuously). Matches
   **S-7's own DEMANDS** ("`Fib` must MAP to canonical-tree fibers … `βmeas = 0` must
   not trivialize") — already flagged as open.

6. **WEAKER — `Wsh17Package`/`W17ii` omit the `xhd_s` face and the nonempty-menu
   condition.** Matches **S-8's own DEMANDS** ("add the `xhd_s` face … exclude the
   empty menu") — already flagged as open.

7. **STRONGER — `W1m_marked` omits the nine-input ledger from its hypotheses**: unlike
   `W1_RS1SH`/`W3_recursion`, it carries no `LedgerIV`/chain premise, so it asserts the
   marked identification without the COMP/HMC/INIT support the note displays for it.
   **Not explicitly named in S-1's DEMANDS text** (which only discusses premising
   `RS1GivenPackage`, not the ledger) — a new finding.

**Orchestrator note on findings 2/3/4/5/6:** these five reconfirm — rather than newly
discover — open items the seam list already names as its own DEMANDS (S-3, S-5, S-6,
S-7, S-8 respectively). That is a successful cross-check (an independent pass agrees
the self-documented gaps are real and accurately described), not five new defects to
triage. Findings **1** (W1_RS1SH/W1e_equates circularity) and **7** (W1m_marked's
missing ledger) are the two seam items not already named in the S-list and are the
ones that should be folded into the seam contract text at the next blueprint revision.

## Explicit faithful checks (Codex's list)

Combinatorial routing/triangularity (`Member`, `Outcome`, `routeOf`, `dispatch_spec`,
`DegCons`, `ktri`, `kcol_agree`, `SCSData`, `scs_flank`, `scs_stage`, `scs`); boundary
arithmetic (`bdyEdgeOwner`, `bdyNodeOwner`, `bdy_edge`, `bdy_node_shadow`,
`bdy_mass_split`); the measured ledger (all fourteen `LedgerIV` fields, "respects
binding adjudication A-1"); rational presentations/branching (`PolyGeom`, `RatBurdens`,
`Kmat`, `bTerm`, `legFactor`, `bSplit`, `bSplit_def`, `routedMass`, `ksub_regroup`,
`ksub_eval`, `ksub`, `ksub_pool`, "the aggregate `J` design was not re-litigated under
A-3"); base change/solve (`powSubst*`, `pow_pool`, `consumedDeltas`, `nested_delta_mem`,
`RegP`, `solve_iff`, `solve_exists_unique`, `solve_cramer`, `blockSolve*`, `evalRe`,
`rexact_solve`, "the consumed-pool scope was accepted under A-2"); escape/read-off
(`EscapeE0`, `PoolHyp`, `Aℝ`, `AVAgree`, `e0_det_ne_zero`, `e0_inv_nonneg`,
`rs3_det_symbolic`, `active_solve_meas`, `interp_read_off`, `ReadOffBundle`); RS.1–RS.4
core (`shConv`, `Rsh`, `markedPairing`, `RS1Meas`, `recursion_meas`, `rexact`,
`rs2_unique_interp`, `rs4_rational_step`, `MuHat`); the n=2 device (carrier, row
masses, determinant, two nonzero solve values, denominator q²+q+1, checksum, XRB,
exactness, pools, read-off — "its lack of split outcomes is appropriately not
presented as evidence for the general split/J machinery").

## Disposition

**Core (the actual E-phase Lean corpus subject to this ratification): RATIFIED**, with
one disclosed, confined, non-load-bearing caveat (`n2_act`'s vacuous inactive-target
branch on the all-active n=2 device — does not touch the general `LedgerIV.act_target`
statement). ADJUDICATIONS A-1/A-2/A-3 were checked against and not re-litigated, per
Codex's own statement.

**Seam contract (§W4-SYNC, explicitly not built at E-phase): NOT ratified in its
currently-shown typed form** — 7 items, 5 of which reconfirm the seam list's own
already-open DEMANDS (S-3/S-5/S-6/S-7/S-8) and 2 of which (W1_RS1SH/W1e_equates
circularity; W1m_marked's missing ledger) are new and should be added to the seam
list's DEMANDS at the next blueprint revision, before any wave-4 re-keying begins.
