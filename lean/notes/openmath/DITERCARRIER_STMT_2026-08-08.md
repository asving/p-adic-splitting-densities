# DITERSUP P1 + JS1/JS2 LANDED — `Scaffold/HDischarge/H1/DIterCarrier.lean` (wave-18 U7, completed by the recovery unit 2026-08-03)

**What this unit is.** The 𝒟₂ carrier interface: the application-INDEPENDENT layer
of the DIterJunctionSupplier program — DITERSUP §S5 row P1 (`DIterCarrier`, `δ₂`,
`InnerIntegral`, `IterLaw`, `RowNPattern`, `CyclicPresentation`) plus the two
application-free sanity gates JS1/JS2 of §S4. Statement shapes transcribed from the
DITERSUP §S3/§S4 displays (`DITERSUP_STMT_2026-08-08.md`, themselves transcribing
DITER_RESTATE §S2/§S3). The J-gates (J1/J2/J3a/J3b) are NOT here (P0-gated; P0
landed separately at cecba9d — this file deliberately imports neither DefsPrime nor
any application module: the carrier layer stays application-free, exactly the P1
pricing row's "no application dependency").

## Recovery/audit record (idempotency)

The original U7 died mid-run on API 529s; its file was sweep-checkpointed AS-IS at
d0e2b74 (completeness UNVERIFIED). Recovery audit findings:

1. **Structurally complete but NEVER COMPILED.** The checkpointed file had all
   declarations, the census block, and the closing `end` — but the predecessor died
   before its first `lake env lean`, and the file did not elaborate (see 2–3).
   Nothing was double-applied; all repairs below were made in place.
2. **TRANSCRIPTION-REPAIR (structure fields; spelling only, zero semantic change).**
   The DITERSUP §S3 display writes shared-type field groups `e₀ e₁ : ℕ`,
   `z₁ zbar : K₂ˣ`, `s₁ s₂ : ℤ → ℕ`. On the pinned toolchain (Lean 4.31.0) this is
   NOT two-fields sugar inside `structure ... where`: it parses as ONE field with a
   BINDER (`s₁ (s₂ : _) : ℤ → ℕ`), so the second name never becomes a field
   (minimal repro: `structure D2 where x y : ℕ  hy : 0 < y` →
   "Failed to infer type of binder `y`"). Each group was split into per-line
   fields — same names, same types, same order; the display's own comments gloss
   both names as separate data, so intent is unambiguous. **FLAG for any future
   unit transcribing the DITERSUP/GRW2 displays verbatim: the display spelling is
   not valid Lean 4.31 structure syntax.**
3. **Proof-level repairs (fallout the predecessor never saw):** (i) JS1's closing
   `rw [mul_mul_mul_comm, mul_mul_mul_comm, ...]` self-undid (the second rewrite
   re-matched the equation LHS and flipped it back) — replaced by explicit
   `hzbar`/`hzone` pair-regrouping haves; (ii) six structure-field proofs
   `by dsimp only; omega` failed ("dsimp made no progress" — the elaborator already
   beta-reduces) — now `by omega`; (iii) two lint cleanups (a no-op `push_cast`,
   one unused simp arg). No statement changed by any of these.
4. **GRW2 interface-flag fold (docstrings only).** The gr(w₂) tie design note
   (`GRW2_TIE_DESIGN_2026-08-08.md` §S3.1, 3baf3cb) landed concurrently with the
   predecessor's draft and raised P1-FLAG-1 + J3B-FLAG-1, which bind this file.
   Folded in: header flag block + `IterLaw`/`iterCocycle`/witness/nonvacuity
   docstring fences. **Disposition of record = the note's recommendation (b):**
   `IterLaw` stays byte-stable with the DITERSUP §S3 display; ALL semantic
   consumption routes through the grTie/GRT-3 canonical-carrier bundle, never
   through bare (hcarrier, hIter). The structure is field-for-field the GRT-1a
   target shape (the design note keys its canonical-fields display to
   `DIterCarrier.hE₂` by name); the canonical derivation D(T) is GRT-1a's job,
   NOT built here.

## Declarations + census (all in namespace `LeanUrat.Scaffold.HDischarge.H1`)

Gate: `lake env lean LeanUrat/Scaffold/HDischarge/H1/DIterCarrier.lean` EXIT 0,
zero errors, zero warnings, ZERO sorryAx anywhere; in-file `#print axioms` census
(15 theorems) all Lean-core (subsets of {propext, Classical.choice, Quot.sound}).

| decl | kind | status |
|---|---|---|
| `DIterCarrier` | structure (12 fields + 7 laws) | DEF — DITERSUP §S3 display, field-split per repair 2; review-owed at E-phase vs harness conventions |
| `DIterCarrier.δ₂` | def | verbatim display |
| `DIterCarrier.InnerIntegral` | Prop def | HYPOTHESIS-STYLE (B1 clause; application-derived) |
| `IterLaw` | Prop def | HYPOTHESIS-STYLE + P1-FLAG-1 fence; verbatim display |
| `DIterCarrier.OuterTrackAdd` | Prop def | HYPOTHESIS-STYLE; NEW statement site (deviation record below) |
| `DIterCarrier.iterCocycle` | def | the cooked formula cocycle (P1-FLAG-1 made concrete) |
| `DIterCarrier.iterLaw_iterCocycle` | thm | PROVED (type-inhabitation only) |
| `carry_chain` (private), `DIterCarrier.δ₂_cocycle` | thm | PROVED — the outer-carry 2-cocycle identity FROM `OuterTrackAdd` (pure finite algebra) |
| `gateJS1_cocycle_assoc` | thm | PROVED = **GATE JS1**, with the honest added hypothesis `hTrack : D.OuterTrackAdd` |
| `gateJS2_dreal_degeneration` | thm | PROVED = **GATE JS2**, exactly as displayed (no added hypotheses) |
| `badTracksCarrier` (+ `_innerIntegral`), `gateJS1_freeTracks_false` | def/thm | PROVED countermodel: the JS1 display WITHOUT the track law is FALSE on the free-field interface |
| `witnessOuterDReal` (+ 4 legs incl. fired JS2) | def/thm | PROVED; P1-FLAG-1-fenced (below) |
| `witnessInnerE1` (+ 4 legs incl. fired JS1) | def/thm | PROVED; P1-FLAG-1-fenced |
| `carrier_interface_nonvacuous` | thm | PROVED — hypothesis-bundle CONSISTENCY only (P1-FLAG-1-fenced) |
| `RowNPattern`, `CyclicPresentation` | Prop defs | DESIGN-OWED statement sites for JS3 (no verbatim display exists); consumed by NOTHING here; review-owed vs the 22-table JSON record before any JS3 use |

## Proved vs hypothesis-style split

PROVED (pure finite algebra / compiled instances): the δ₂ carry-cocycle identity,
JS1 (with hTrack), JS2, the free-tracks countermodel, both witnesses with their
gate fires, the bundle-consistency theorem. HYPOTHESIS-STYLE (Props consumed as
named hypotheses, NEVER asserted — the DensityFoundation genre): `IterLaw`,
`InnerIntegral`, `OuterTrackAdd`. No sorries, no axioms, no application-dependent
leg asserted.

## Deviation record (statement-review flag)

The DITERSUP §S4 JS1 display takes only (hLaw, hInt). On this interface (free
s₁/s₂ fields, per the display's own E-phase flag) that statement is FALSE —
compiled countermodel `gateJS1_freeTracks_false` (e₀ = 1, e₁ = 2, s₂ ≡ 1 on evens:
c(0,0)·c(0,1) = z̄ ≠ 1 = c(0,1)·c(0,1)). The shipped JS1 carries the additional
honest hypothesis `hTrack : D.OuterTrackAdd` (the s₂ digit-additivity law, which
any eq12-derived instance satisfies definitionally — and which GRT-1a's canonical
D(T) will discharge). NEW-statement site, not an edit: the DITERSUP displays are
DISPLAY ONLY — NOT COMMITTED by that note's own banner. This countermodel is ALSO
independent compiled evidence for P1-FLAG-1: the bare interface genuinely cannot
tell a semantic track from a cooked one.

## Witness honesty status (P1-FLAG-1)

Both witnesses (`witnessOuterDReal` = the D-REAL e₀ = 1 degeneration leg,
ITER-LAW-FREE per the J3a pricing; `witnessInnerE1` = the e₁ = 1 leg) carry
explicit does/does-not-evidence docstrings: they evidence that the interface types
are inhabitable, that the degeneration shapes are expressible, and that JS1/JS2
fire on concrete instances with non-trivial cocycle values (c(1,1) ≠ 1) — and
evidence NOTHING about (H7), gr(w₂), or any actual tower, because their cocycles
are the cooked `iterCocycle`. `carrier_interface_nonvacuous` is relabeled bundled
interface INHABITATION (hypothesis-bundle consistency), not semantic non-vacuity.

## Conditionality (what this unit does NOT do)

Nothing here machine-checks (ITER-LAW) or touches the gr(w₂) tie. ITER-LAW
acceptance citation consumed by this unit, PASTED from the ledger block "ITER-LAW
ACCEPTED — 2026-08-03" (`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`): "Scope
as accepted: the harness tower class (superset of DITER_RESTATE §S2's E₂ > 1 pin;
on-the-nose coincidence restricted to E₂ > 1); residuals: (ITER-LAW-LIFT) open
exactly at g₀ = 1 ∧ δ₁ = 1; gr(w₂) wrapper rides the accepted GRB retarget;
orders ≥ 3 untouched." That acceptance is a numerics + math-level result about
the actual tower cocycle; the Lean `IterLaw` is the interface Prop it is consumed
through — accepting the law discharges NO hypothesis in this file. J3b's E-phase
statement should bundle grTie per J3B-FLAG-1 (rides to the J3b unit). JS3 is NOT
this unit (priced M; its two statement sites land here design-owed and unconsumed).
