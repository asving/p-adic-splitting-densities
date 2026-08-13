# BLUEPRINT PHASE DESIGN — 2026-08-13

**Goal (Asvin, /goal, verbatim):** "once the math simplification is done, get codex to
write out EXTREMELY clear and precise mathematical blueprints, optimized for
parallelizability of formalization by breaking up the entire project into tiny pieces
with a clear dependancy graph uniting all of them. Once the blueprint is written, launch
lower tier agents to formalize in lean to the blueprint. The blueprint should be
detailed enough that the formalization is essentially trivial."

**Status:** DESIGN, pending codex plan-level adversarial review (standing rule) and the
gate. **Gate:** T2 acceptance (campaign 5/5; sol pass on r12 in flight).

---

## 1. Source of truth (what blueprints transcribe — never invent)

1. **The compressed corpus at HEAD**: the five accepted T-units (T1 gauge-cocycle, T2
   σ-ladder master [pending], T3 telescope, T4 certificate witness, T5 w-frame) + the
   accepted notes they organize (W11, W12, HMENU3, HEX3, GENIND, GENH4, GENHN,
   GENTOW1–6, HE3/HE6/HE7/HE6R1, HETOW, weld layer, JD0, SIGMALAW, LIFTCORNER).
   Byte-frozen; blueprints cite note + section/display per node (provenance).
2. **docs/CITE_SCOPE_RESOLUTION_2026-08-13.md**: the general-O bibliography. In Lean
   there are no citations — every cited leaf theorem becomes a blueprint node to PROVE
   (or quarry-copy); the resolution doc tells the blueprint AT WHAT GENERALITY.
3. **leanfinal's landed API** (the blueprint MUST target these, never parallel-define):
   `LocalData` bundle, `FactorizationType`, `typeOf` (gcd form), `genuineDensity` /
   `upperDensity` / drainage tie, `HenselFactorization.*`, `Res/proj/Coeff` levels.
4. **The quarry** (lean/LeanUrat, 1209 modules): nodes may be supplied by VERBATIM COPY
   after verification (provenance comment). The OM order-≤1 layer especially.
5. **leancheck's n≤3 experience**: the census-lemma pattern, certificate suites,
   what a real formalization unit consumes — calibration for node sizing.

## 2. Node format (the heart — one node = one Lean declaration)

Each node, in the chapter blueprint file:

```
### NODE <ID>  [def|lemma|theorem|instance|gate]  [fresh|quarry:<LeanUrat path>|landed:<name>]
STATEMENT (math): complete, self-contained modulo node references; every symbol
  defined here or cited as <ID>. No "as above", no "the usual".
SIGNATURE (Lean): the exact proposed declaration, typed against leanfinal's real
  names. This is the interface contract — formalizers may not alter it.
DEPENDS: [<ID>, <ID>, ...] + mathlib lemmas by exact name where known.
PROOF (steps): numbered; each step is one of: "by <ID>", "by mathlib <name>",
  "computation: <displayed>", "definitional". FORBIDDEN: "clearly", "standard",
  "similarly", "one checks". A step needing >3 Lean tactics is a split candidate.
SIZE: target ≤ 40 Lean lines; >10 proof steps ⇒ split the node.
SOURCE: <note>, <section/display>, at HEAD <commit>.
TEST: builds green; #print axioms = Lean core; signature matches blueprint
  byte-modulo-elaboration; node-specific numeric check if any.
```

## 3. DAG + parallelization mechanics

- **blueprint/DAG.md**: machine-readable edge list (`<ID> -> <ID>`), one line per edge,
  plus computed topological layers. Width of a layer = available parallelism.
- **Zero-sorry compatibility**: leanfinal never holds a sorry. Parallelism therefore
  comes from DAG width, not stubs: an agent may claim a node iff ALL its dependencies
  are LANDED. The blueprint's frozen signatures prevent interface drift while waiting.
- **Statement elaboration pre-check**: before the fleet fires on a chapter, one agent
  lands `leancheck/UniformityCheck/BlueprintStubs_<chap>.lean` containing each
  signature as a `Prop`-valued `def` (no sorries) — catching elaboration errors in the
  blueprint's signatures BEFORE formalization starts. Blueprint bugs go back to codex.
- **Status ledger**: blueprint/STATUS.md — per node: OPEN / CLAIMED(agent) / LANDED
  (commit) / BLOCKED(reason). ORCHESTRATOR-OWNED (agents never edit it; they return,
  the orchestrator books). Prevents write conflicts.
- **File layout**: one Lean file per node (parallel-safe), chapter roll-up imports
  (leanfinal/Uniformity/<Chap>/<ID>.lean; <Chap>.lean imports all).

## 4. Chapters (one codex blueprint run each, in DAG order)

- **A. FOUNDATIONS** — already landed (enumerate as `landed:` nodes; no work).
- **B. LEAF/ORDER-1 LAYER** — the polygon + residual factorization leaf theorem at
  general O (the corpus's Ore/GMN cite, per CITE_SCOPE at [GN15] scope): typeOf
  transport, Hensel certificates at level 1, the (e,f) read. Quarry-rich chapter.
- **C. DIGIT CALCULUS + MENUS** — W11/W-12.A: level-N boxes, digit laws, menu counts,
  the shape-generic count law. (Includes the level-exact count-law formulation the
  equal-char probe suggested.)
- **D. THE REDUCTION** — THEOREM W-12.D: menus + drainage ⟹ one R_τ ∈ ℚ(q). The spine.
- **E. THE INDUCTION** — GENIND/GENH4/GENHN: two-species induction, genre finiteness,
  stage laws.
- **F. THE σ-LADDER** — T2's master HE7.A + the five instance records (+ (LB1)/(MP1)
  as explicit blueprint hypotheses or discharge nodes — decision recorded per node).
- **G. GAUGE/LETTER LAYER** — T1/T3/T5 + the consumed weld faces (JD0 count-blindness
  as the count-side interface).
- **H. TOWERS** — T4 + GENTOW1–6 as consumed by the composite stages.
- **I. DRAINAGE/EXHAUSTIVENESS** — HE-chain/HEX3 exact laws; general drainage; the
  strong-Hensel infrastructure node (the named n≥3 blocker) lives here.
- **J. ASSEMBLY** — coefficient uniformity (D6 analogue), the capstone
  `UniformityStatement` discharge, gates.
- The three audit work-items become nodes: L5fix(b) depth weakening (chapter I),
  NS-6 corollary (B), typeOf shift/scale invariance (B).

## 5. Codex blueprint-run protocol

- One chapter per run; runner pattern with nohup+disown; the charge names the exact
  source files (sandbox now works — codex reads the repo) AND pins the format of §2
  verbatim; output = blueprint/CHAP-<X>_<name>.md + DAG.md edge additions.
- Each blueprint run is followed by (i) the stub elaboration check (§3) and (ii) an
  Opus consistency read (signatures vs leanfinal API; dependency completeness; no
  "clearly" violations) before the chapter's fleet fires. Blueprint defects → codex
  revision run, versioned in place.
- Budget: codex 7-day window at 61% (resets Tue 2026-08-18 10:23). Blueprint runs are
  the top-priority codex spend. Chapter order B, C, D first; heavy later chapters may
  ride the post-reset window.

## 6. Formalization fleet protocol (lower-tier)

- Default tier: **sonnet** agents, one node per run, charge = the node's blueprint
  block verbatim + landed-dependency names + leanfinal rules (zero sorries, Lean-core
  axioms, no statement edits — the SIGNATURE is a contract; if it cannot elaborate or
  cannot be proved as stated, return BLOCKED with the precise obstruction; never
  weaken).
- Escalation ladder per node: sonnet ×2 attempts → opus ×1 → back to codex as a
  blueprint defect. Books in STATUS.md.
- Concurrency: ≤3 agents at once (org token throttle; budget). Commit discipline:
  each agent commits only its own node file(s), prefix "BP:<ID>:"; orchestrator runs
  the chapter build + axiom check at each layer boundary and books STATUS.
- Verification cadence: full `lake build` + axiom sweep at every completed DAG layer;
  numeric gates where the blueprint names them.

## 7. Open decisions for the codex plan review to attack

1. Node-per-file vs section-files (conflict-safety vs import bloat at ~10² nodes).
2. Where (LB1)/(MP1) live: blueprint hypotheses (conditional chapter F) vs discharge
   nodes gated on their own small units.
3. Whether chapter B proves the leaf theorem fresh or quarry-copies LeanUrat's OM
   order-≤1 layer (the copies are large; verification cost vs re-prove cost).
4. The level-exact count-law formulation (probe's suggestion) as chapter C's primary
   object vs the density-limit formulation only.
5. Chapter sequencing vs the codex window reset (how much blueprint mass before Tue).
