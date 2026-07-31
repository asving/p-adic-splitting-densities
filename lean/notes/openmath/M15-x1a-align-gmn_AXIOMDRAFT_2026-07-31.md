# M15-x1a-align-gmn — AXIOM DRAFT executed (2026-07-31, agent: m15-axiom-draft)

AUTHORIZATION quoted for the record — Asvin, 2026-07-31, verbatim: "Sign-off granted
on all 21 items as preferred, execute the queue." + the /goal standing authority.
Unit: the GMN literature-axiom draft (M15 dual-LITERATURE). Sources consumed: the
Fable twin `M15-x1a-align-gmn_fable.md` (this directory) and the Codex twin
(`/tmp/openmath/M15-x1a-align-gmn_codex.jsonl`, agent_message text extracted;
VERDICT LITERATURE). Scope fence honored: docs + notes + ONE new Lean leaf;
MovesC/HC1/HC2/MovesD untouched; zero existing statements changed.

## (1) The Lean leaf — `LeanUrat/GMNIndex.lean` (NEW; NO axiom, NO sorry)

**The `axiom` keyword is WITHHELD — deliberately, and here is the doubt, stated:**
the drafted declaration (`AX_GMN_index_finsum`, text on record in the leaf header)
is about `gmnInd p f` (GMN Def 4.11 at O = ℤ_p) and `gmnOrderInd p f r` (Def 4.15's
ind_r(f) keyed to the engine's pinned representative family) — two definitions that
DO NOT EXIST YET. Declaring today would mean `opaque` stand-ins, and an axiom over
opaque constants is not a faithful minimal transcription: the leaf machine-checks
this by `face_zero_witness` (the shape holds for the all-zero functions — no content
until the definitions are real, and once they are, an early axiom would be an
UNAUDITED bridge from the bodies to the paper). So the leaf ships, per the unit
instruction's escape hatch:

* `GmnIndexFinsumFace` — the statement SHAPE as a `def`, parameterized over the
  not-yet-built definitions (the finite-sum face of Thm 4.18(1) + Def 4.15
  nonnegativity: `∀ p f ∉ discZero, ∀ R : Finset ℕ, ∑_{r ∈ R} ind_r(f) ≤ ind(f)`);
* the pending declaration displayed verbatim in the module doc with the
  NOT-YET-DECLARED marker and the three gates (definitions built → guardian audit →
  Asvin sign-off);
* `orderAccounting_of_face` + `x1aAlignInc_of_face` — the CONSUMPTION SEAM,
  machine-checked: face + `ind`-pin + the three placement duties inhabit the KE8
  carrier `GmnOrderAccounting`, and thence `X1aAlignP n X ⟨true, false⟩`
  (= `KT.cl15_align`'s row) via the proved `x1aAlignInc_of_orderAccounting`. This
  pins the both-twins over-scoping trap in Lean: the axiom face discharges
  `finsum_le` ALONE; `place`/`place_inj`/`place_charged` enter as hypotheses.

Checks run: `lake env lean LeanUrat/GMNIndex.lean` GREEN (0 errors, 0 warnings);
`lake build LeanUrat.GMNIndex` GREEN (8561 jobs); `#print axioms` on all three
theorems = `[propext, Classical.choice, Quot.sound]` (Lean-core only, as required —
the leaf declares nothing). `AxChk_baseline` NOT touched: no axiom exists, no
footprint to print.

## (2)+(3) The faithfulness entry — `docs/AXIOM_FAITHFULNESS.md` §AX-GMN-INDEX

Appended (94 lines), status **STATEMENT DRAFT ONLY / DRAFT 2026-07-31 — PENDING
guardian audit**, format matching AX-SERRE-DVR (statement / verified core / scope
caveats / residual / guardian audit). Contents beyond the citation
(GMN TAMS 364 (2012) 361–416, arXiv:0807.2620v2, **Thm 4.18(1) + Defs 4.11/4.12/4.15
+ Rmk 4.14**): the EXACT residual for `cl15_align`, with the two twins' analyses
reconciled item by item —

* Fable OL-1 (injective order placement) ↔ Codex L.1+L.4, WITH the route divergence
  resolved: axiom pinned to the TAMS-only per-ORDER charging; Codex's refined-index
  route (Bordeaux companion, numbering UNVERIFIED this session) recorded as fallback
  for the placement discharge, never as axiom content.
* Fable OL-2 (v_r-normalization crossing) ↔ Codex L.2+L.3, with the raw-frame half
  marked NOT residual (already machine-checked: `ind2Region`/XA9 + the 1548-case N1
  dictionary probe).
* Fable OL-3 (representative admissibility) kept EXPLICIT against Codex's folding
  into "valid flow" — it fixes the meaning of `gmnOrderInd` itself, so it gates the
  DECLARATION, not merely the placement proof.
* Fable OL-4 (`inStratum` pinned to genuine ledgers) ↔ Codex's HistWF/`inStratum`
  remark, converse of the carried `gmnLink`.
* Shared exclusions: `GMNIndex.p2` NOT covered (classical, separate disposition —
  Serre *Corps Locaux* III §6 / Neukirch III.2 class); the KE8-carrier-as-axiom trap
  named by both twins independently.

## (4) The gate — noted

The guardian audit runs SEPARATELY (orchestrator-run Codex audit of the entry + the
drafted statement, quote-and-classify). Nothing in this unit unblocks any consumer:
no prover may cite AX-GMN-INDEX, and the declaration itself waits on all three gates
in order. Next dedicated work when gates open: build `gmnInd`/`gmnOrderInd`
engine-side (OL-3 first — it is the declaration gate), then OL-1/OL-2/OL-4 feeding
`x1aAlignInc_of_face`.

Files this unit owns: `lean/LeanUrat/GMNIndex.lean` (new),
`docs/AXIOM_FAITHFULNESS.md` (append-only entry), this note.
