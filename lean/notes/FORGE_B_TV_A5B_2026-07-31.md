# UNIT FORGE-B — realizable root nodes built; TV-A5b's countermodel existence DISCHARGED (2026-07-31)

## What this unit was

The instance-forge adjudication (`BRIDGE_ADJUDICATIONS_2026-07-30.md`, UNIFYING
AUTONOMOUS UNIT item (b)) had TV-A5b's stray-child countermodel blocked on ONE missing
artifact class: a compiled **realizable root node** — a `Node 2 (ZMod 2)` whose
singleton history passes `TreeModel.mem_realizable`'s triple
`HistoryCoherent ∧ Realizable ∧ pol.IsCanonPres` (at length 1: root Φ-degree 1, the
slope law `slope·(e·STR·Dwidth) = h`, the γ-tie, vacuous transitions/realizability,
policy-canonical lift, and `zbar = canonRoot`). This unit built TWO of them and
discharged the fenced existence statement `stray_countermodel_attempt`
(MovesT/TV_A5b.lean:73) **as-is** — no statement, signature, or hypothesis changed
anywhere.

## Deliverables (both landed, per-file gates green)

1. **NEW `lean/LeanUrat/MovesT/TV_A5b_forge.lean`** (~590 lines, 0 sorry):
   * `forgeNodeA` / `forgeNodeB` — root-species node literals over G1's
     `toyStage : Stage 2 (ZMod 2)` (Φ = X, degree 1; REUSED, not rebuilt — it IS the
     established from-scratch build, the compiled transport of HC2/U31's `bStage`;
     recorded as a provenance deviation from the charge's "from-scratch Stage" wording).
     Data: (e,h,s,t) = (1,1,1,0), (g,μ) = (1,1), ψ = X − C 1, pat ≡ 1, Ranch = 1 + X
     (ord_ψ = 1 exactly), lift = 0, zbar = 1; they differ ONLY at s0 (0 vs 1) with the
     induced (a, line, gam) = (0, ⟨1,1⟩, 1) vs (1, ⟨2,1⟩, 2).
   * `realizableA` / `realizableB` — the forged content: any history with nodes
     `[forgeNodeA]` (resp. B) satisfies the full `mem_realizable` triple, including the
     `canonRoot` computation (`canonRoot_of_psiImage`: roots of X − C 1 = {1}, the
     enum-least root is 1 = zbar). Instance friction note: `canonRoot`'s classical
     `DecidableEq` instances differ from `ZMod.decidableEq`, so the singleton-min
     computation is the instance-EXPLICIT helper `min_image_toFinset_singleton`
     (explicit binders keep the rw pattern's instances as unifiable metavariables).
   * `forgeTree : TreeModel 2 (ZMod 2) 2 1 2 forgePol` — children
     `forgeChild o ν x := ν = A ∨ ν = B` everywhere; `mem` = root everywhere + the two
     singleton histories; `mem_snoc` legs die on the species-root clash; `forgePol` =
     constant-0 lift policy.
   * `forgeCells : CellAssign 2 (ZMod 2) 2 1 2 forgePol forgeTree forgeχ forgeTrack` —
     TV-A5a's Unit-cell pattern with branch set {A, B};
     `forgeTrack ν := if ν.s0 = 0 then X else X + 1`. `child_cover` holds EXACTLY at
     n = 2 / p = 2: the g = (0,0) cell (X² = X·X) is covered by A on track X, the
     g = (1,0) cell (X² + 1 = (X+1)², char-2 identity `z2_sq`) by B on track X + 1;
     the two other reductions (X² + X, X² + X + 1) have derivative 1, hence are
     separable → squarefree → no repeated factor (`count_le_one_of_deriv_one`).
   * `stray_countermodel_witness` — the byte-identical ∃-statement of TV_A5b:73,
     proved. **The stray breaks (R)**: at g ≡ 0 (reduction X², normalizedFactors
     2 • {X}) the realized child `forgeNodeB` rides track X + 1 of multiplicity 0 —
     `TrackRepOn` fails, so ¬(TrackUniqOn ∧ TrackRepOn).
2. **TV_A5b.lean sorry DISCHARGED** (line 87): the only edits are the added
   `import LeanUrat.MovesT.TV_A5b_forge` and `sorry` → `exact stray_countermodel_witness`.
   Statement + docstrings byte-identical.

## What the result MEANS (the fence upgrade)

The sealed prediction (E5_rootSplit.lean:311-342, risk R4) is CONFIRMED-COMPILED: the
(U)∧(R) pair `TrackUniqOn`/`TrackRepOn` is **NOT derivable** from the displayed
`CellData`/`CellAssign` laws — there is a full compiled `CellAssign` carrier where the
pair fails. The pair's NECESSITY as named warranted hypotheses (the TV-A2/A3/A4 hoist
rows, owner HC-2/D4R0K) is now machine-certified. Note the countermodel shape
delivered is the (R)-breaking stray (a child on a multiplicity-0 track), a stronger
break than the docstring's minimal multiplicity-1 sketch; the (U)-conjunct is simply
discarded by the ¬∧.

Consistency cross-check: KB12/KB13 (which PROVE the pair from the named laws
`RootChildDataFn`/`RootChildRootSpecies`/`RootTrackMem`/`HenAtSimple`) are not
contradicted — this carrier violates `RootTrackMem` (B is a child at every point,
including cells whose reduction its track does not divide). So the countermodel also
certifies that KB13's `RootTrackMem` premise is not redundant.

## M1 coexistence check (clean)

The witness refutes NO sorried universal in any module TV_A5b (now) imports:
* TV_A1 — 0 sorries.
* TV_A5b_forge → G1_toyGate — 4 sorries, all carrier-specific to G1's OWN toy tables
  (`toyModel.mem_realizable` ×2 BLOCKED-FALSE at those tables; `twoNodeKcardH`,
  `toy_v8_wchain` type-blocked pins). None is a universal over carriers; the forge
  witness carrier is disjoint and proves nothing about them.
* E5's fenced internal `hD4R0K` sorry is NOT in the import cone (E5_rootSplit is not
  imported), and its trackOf is context-supplied there — no shared-environment
  refutation. No local copies were therefore needed; the forge module imports the
  vocabulary directly.

## Verification record

* `lake env lean LeanUrat/MovesT/TV_A5b_forge.lean` — clean (0 errors, 0 warnings).
* `lake env lean LeanUrat/MovesT/TV_A5b.lean` — clean.
* `lake build LeanUrat.MovesT.TV_A5b_forge LeanUrat.MovesT.TV_A5b` — green
  (8589 jobs; both modules replay warning-free).
* `#print axioms`: `stray_countermodel_witness`, `stray_countermodel_attempt`,
  `forgeTree`, `forgeCells` all `[propext, Classical.choice, Quot.sound]` — Lean-core,
  no sorryAx (G1's sorries are NOT inherited: `toyStage`'s cone is sorry-free).
* MovesT sorry census delta: −1 (TV_A5b:87 gone; forge adds 0). Remaining "sorry"
  matches in both files are docstring text only.

## Follow-ups for the orchestrator (NOT executed here — outside this unit's fence)

* TV_A5b's module docstring still says "E-PHASE SKELETON ... bodies sorry" — a
  prover-phase docstring refresh is due but is an edit beyond the sanctioned
  import+discharge surface, so it was left byte-identical per the unit charge.
* The TV-A1 docstrings' deliverable row ("recorded at the TV-A1 docstrings,
  prover-phase edit") and the E5:339-342 fence record now warrant the
  "countermodel COMPILED" upgrade — same fence-record duty class as TV-A5a's.
* MovesT/MANIFEST.json gains a FORGE-B row at the next manifest sweep.
