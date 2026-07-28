# MovesT E-phase Lean blueprint — Codex semantic audit (rev 1, 2026-07-28)

CORPUS: `lean/LeanUrat/MovesT/` per `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md`
(§T-ASSEMBLY, 51 units). NOTE: `lean/notes/MOVES_2026-07-24.md` §T-ASSEMBLY, rev 7,
body lines 6970–7761 (dual-accepted 2026-07-27). SEAM CONTRACTS cross-checked
against, pasted verbatim into the prompt: MovesD blueprint §2.5 (W4-1..W4-4,
`MOVESD_LEAN_BLUEPRINT_2026-07-28.md` lines 318–379), MovesS blueprint's
RATIFICATION ADDENDA + §W4-SYNC (S-1..S-11 + 2 addenda,
`MOVESS_LEAN_BLUEPRINT_2026-07-28.md` lines 1105–1346), HC-2's Wall A/B/C
architecture notes (`HC2_LEAN_BLUEPRINT_2026-07-28.md` lines 66–139), and (context
only) PROJECT_STATE's 28j Q1/Q2 queue (`docs/PROJECT_STATE.md` lines 897–911).
Charge: `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`, instantiated for
CORPUS = MovesT with an APPENDING paragraph directing the auditor to spend the
most scrutiny on the blueprint's §5 SEAM-DISCHARGE table (this corpus's central
claim: discharging 19 seam contract entries left open by MovesD/MovesS/HC-2) and
on the Q1/Q2 statement-fence (no unit may consume the fenced HistoryCoherent
re-key / RunVertexPin design as though already built).

Run: `codex exec --skip-git-repo-check --sandbox danger-full-access -` (stdin;
the assembled prompt was 172,669 bytes, over the 128KB argv-safe threshold, so
stdin was mandatory and the first attempt succeeded — no retry needed). Model
`gpt-5.6-sol`, session `019fa9cd-f9f4-7b31-bd10-fdf6fc8e2844`, 70,522 tokens.
Full transcript: `/tmp/leanaudit_t/verdict`; prompt assembly:
`/tmp/leanaudit_t/prompt.txt` (four parts — instantiated charge, the frozen
note excerpt, the three seam-contract sources, the full blueprint).

## Verdict

**REJECT (35 crit / 10 gap)** — the heaviest reject of the campaign's blueprint
audits to date. Findings below are Codex's numbering verbatim (findings 1–18
are base FAITHFULNESS/NON-VACUITY/HYPOTHESIS-FIDELITY findings against the
frozen note directly; 19–35 are seam-discharge findings, the section the charge
asked to be hit hardest; 36–45 are GAP-grade).

## CRITICAL findings (35)

**Verdict-pin / tree-model layer (1–9, 14–18) — against the frozen note directly:**

1. `NsHalts`/`BranchDichotomy` don't encode (τ-ns) or Theorem B's structural
   content: `BranchDichotomy` reduces to the classical tautology
   `∃ child ∨ ∀ ν, ¬ child` given `T.mem`, so a degenerate childless model
   satisfies it — none of KB-TOT's actual content is carried.
2. `PrunedMem`'s halt test omits `H'.nodes ≠ []`, so it applies to the empty
   prefix and an arbitrary `NsHalts` value there can prune every nonempty
   history — contradicts the blueprint's own "proper nonempty prefix" comment.
3. `VTree.fiberAt`'s (ns) disjunct never ties `Tr.leafV H` to `nsVerdict`, so two
   trees differing only in their ns-leaf verdict value can both fiber the same
   `x` — the note's `v = μ·{(E(Φ̂),F(Φ̂))}` pin is unstated.
4. `irrVerdictOf`'s `max(accE H, 1)`/`max(accF H, 1)` junk guards are asserted
   (not proved) inactive on realizable histories; the statement surface carries
   no coherence/degree fact that would let a consumer discharge this.
5. `SibCount` is strictly stronger than (SIB): it quantifies over an arbitrary
   `Σc`/`B` rather than the note's actual full joint digit cell and its whole
   branch set, so it demands independence after arbitrary further conditioning.
6. T-V3's stated equality omits the cluster degree and `μ` from
   "cluster degree = key degree · μ = E·F·μ"; `?g_of` is an undeclared datum.
7. T-V5 as displayed is `... ∨ True` — vacuously true for every instance,
   proving no mutual exclusivity at all.
8. T-V6 is the same tautology as finding 1 and drops (c2)'s no-orphan/
   exactly-one-verdict content.
9. T-V8 (`shapeOfH_matches`) takes `hcoh : HistoryCoherent H` unfenced — Q1
   records the current child key makes the intended steep two-node histories
   inconsistent, and the re-key isn't authorized; T-V8 isn't manifest-tagged
   `fenced-Q1`, so it can vacuously "prove" its steep face ahead of the gate.
   **(This is the Q1-fence violation the charge specifically asked to check for.)**
14. T-E9 is false under the proposed `fiberAt` (direct consequence of finding 3):
    two `VTree`s differing only in an ns verdict are simultaneous fibers.
15. T-F1 (ONE-F) therefore fails too — same ns counterexample produces distinct
    `VTreeExt` witnesses under the `∃!`.
16. T-E10 applies the exact per-shape exponent law to ns-leaf trees with no
    `hdet`/cap-detectable-leaf restriction, contradicting the note's explicit
    denial of the product law there (replaced by an asymptotic zero statement).
17. `PreHaltPfx` is box- (`x`-)dependent, contrary to the note's PRE-HALT being
    "a property of η's own cell data" computable before summing over `f`.
18. T-F4 proves only an inequality where the note displays an exact
    below-halt-decomposition identity — strictly weaker than its `moves_ref`.

**Per-clause / joint-cell layer (10–13):**

10. T-C2 substitutes `NPband` for TB-CAP(irr)'s actual cap `N(η′,⊤)` at the
    extended history η′ — that substitution IS W4-4/NP-ID, which the unit
    claims not to consume.
11. T-E5's division-free root formula is off by one factor of `|rootCell|`
    versus (SIB)'s required exponent (checked by direct substitution using
    T-E2's identity).
12–13. T-E7/T-E8/T-E11 require the global `JCmulti` hypothesis unconditionally,
    silently strengthening trees whose splits are all single-side (the note
    requires (JC-multi) only AT multi-side sites; (JC-single) is unconditional
    elsewhere).

**Seam-discharge findings (19–35) — the section audited hardest, per the charge:**

19. W4-1 not discharged: T-D1/T-D2 assume an arbitrary `CellAssign`, leaving the
    canonical HC-2 instance residual; the toy non-vacuity witness doesn't make
    the general interface reject root-only/childless models.
20. The claimed "ENTIRE" W4-2 discharge omits most of `VerdictModelT`'s required
    fields and `CellAssign` still admits the forbidden degenerate (singleton
    `Cell`, constant `cellOf`) models.
21. W4-2's cross-level uniform-cap demand (one cap per class across all N) is
    dropped; T-C2 is fixed-N and depends on the unproved NP-ID substitution.
22. T-D5 doesn't discharge D4R_CYL — `hkey` IS the deferred cylinder/tree
    identification, repackaged as an unnamed premise (violates the typed-
    package discipline the campaign doctrine demands).
23. T-D6 is circular on `ClassFiberWelldef` for the same reason.
24. T-D7 weakens NP-ID: it proves the equality only at the selected `S.jet i`,
    not the contract's `∀ (J : JetSetup (reprOf i))`.
25. T-D12's `rs1GivenOfMovesT`/`xrbOfMovesT` produce parallel "Values" carriers,
    not the actual named `RS1GivenPackage`/`XRBPackage`/`Wsh17Package` types.
26. S-1 (`W1_RS1SH`) remains undischarged — all three RS.1 conclusions are
    deferred to "MovesS wave 5," and the contract requires re-keying + re-audit
    before an entry counts as done.
27. The W1 circularity ratification addendum isn't repaired: exporting
    TREE-EXP/TREE-N/ONE-F as future-available inputs isn't the same as any unit
    actually deriving RS.1-SH.
28. The W1m nine-input-ledger addendum is still omitted from T-D12's statement
    or any typed package.
29. S-3 (`W3_recursion`)'s required re-keyed `hxrb` (XRB's conclusion equality)
    premise is not supplied; the bare implication form stands untouched.
30. S-5/S-11 claimed mapped, but the load-bearing clauses (first-entrance-
    ancestor fence for S-5; the full TreeIface gate instance + W7 check for
    S-11) are both absent — only a carrier core exists.
31. S-6's tree-tied `ReadLedger` (per-first-entrance-path assignment, charge
    equalities, the (BDY) split) isn't built.
32. S-7's non-vacuity demand (βmeas = 0 must not trivialize; fiber nonemptiness
    where βmeas > 0) is dropped from the claimed discharge.
33. S-8/S-10 only partially mapped: S-8's empty-menu exclusion and S-10's
    CUT-WD leg + device-instance replacement are tie-demands, not optional.
34. Wall A isn't reconciled with HC-2's typed `ReadsOf`: `CellAssign` has no
    field or theorem tying its branch set to HC-2's per-frame run predicate.
35. **The seam-discharge count itself is arithmetically false.** The blueprint's
    own §5 tally reads `4 (MovesD) + 11 + 2 addenda (MovesS) + 2 (HC-2 walls) +
    2 (Q1/Q2) = 19` — but `4+11+2+2+2 = 21`, not 19. (Verified independently:
    the arithmetic error is real and checkable directly from the blueprint's own
    displayed sum, not a matter of interpretation.) The actual 19-entry set is
    `4+11+2+2` (MovesD + MovesS + addenda + HC-2 walls); Q1/Q2 are fenced
    context, not discharge targets, and several of the 19 are themselves
    explicitly left to later owners in the same table.

## GAP findings (10, #36–45)

36 (T-V4 bundles extra unfrozen equivalences), 37 (multiple load-bearing Defs —
`VTree.typemult`, `ContFiber`, `SibStep`, `PCI`, `HenLift`, `OmSat`, `VTree.thr`,
`readOf`, `shapeOfH` — are only `…` ellipses, unauditable), 38 (T-C3's
`IsNsLumpFamily` may assume its own conclusion, definition not pinned), 39
(T-C7's principal hypothesis and level-threading unspecified), 40 (T-E1's stated
`∧` nests under the wrong side of the equality — a plausible typo, not a
plausible Lean statement as written), 41 (T-E3's promised site-cell bridge is
absent from the actual statement), 42 (T-E4's side-count⇒branch-count depends
entirely on the undefined `IsMultiSideSite`), 43 (T-E6 omits the locality/
level-separation premise its spectator-event conclusion needs), 44 (T-E12 is
not yet a complete auditable statement), 45 (Wall B's `SEED-EXIST` quantifier
structure — `∃ keys`, `KeysLawful`, `Nonempty PresentSeed` — isn't traced through
the generic `JetSetup`/`S.jet`/`hsites` riders MovesT actually consumes).

## Disposition

35 criticals is far above this campaign's usual pass/fail threshold; the corpus
is not close to ACCEPT. Two classes of finding are especially load-bearing for
next steps: (i) findings 1–9/14–18 show the VP/tree-model Defs layer (§2.4–2.5)
needs a from-scratch restatement, not local patches — `BranchDichotomy`,
`fiberAt`'s ns clause, and the (τ-irr) verdict value all need their actual
note content threaded through, and T-V8's Q1-fence violation needs an explicit
`fenced-Q1` manifest tag or a restatement that avoids `HistoryCoherent`
entirely at steep legs; (ii) findings 19–35 show §5's SEAM-DISCHARGE table is
mostly aspirational — of the 19 claimed-mapped entries, none survives the
audit as an actual re-keyed, typed-package discharge (W4-1/W4-2/W4-4, S-1/S-3/
S-5/S-6/S-7/S-8/S-10/S-11, both ratification addenda, and Wall A are all named
as CRITICAL failures to discharge), and the table's own headline arithmetic
(19 = 4+11+2+2+2, which sums to 21) doesn't check out. Recommend a full rev-2
pass rather than incremental repair, given the scale and the systematic pattern
(nearly every seam row repeats the same shape: "the contract demands X; the
unit supplies a name for X's future value, not X").
