# GLUEGEN-CONSTRUCT — residue-GENERIC glued groups: the PV-4 falsifier target, constructed

STATUS: SKELETON (commit 1 of the two-commit seal; S2/S3/S4 verdicts PENDING —
to be filled from runner artifacts only).  Unit of the 2026-08-08 campaign
(wallclock 2026-08-04), per the constructed-counterexamples directive:
derive → solve → realize → verify; no sweeping.

Target: the K2-CLOSE PV-4 MISS (ledger 00a3658; `K2CLOSE_2026-08-08.md` S6
GLUE-DEGEN): all 38 realized glued groups are residue-DEGENERATE — a single
in-vivo residue class each (the full-merge state), so the instance roster
probes ONLY the full-merge corner of the K2-L12 state space and is NO
evidence about generic glue ratios.  This unit constructs residue-GENERIC
glued groups in vivo and runs the K2-CLOSE verdict machinery on them — the
falsifier test for K2-THM-B's shape-level covers.

## S0. Authority, consumption, scope

Consumes read-only, at the SURVK2_PROOF/K2CLOSE header grades (everything
ATTEMPT-capped by the W arc): K2-L4 (residue monomial), K2-L6/L7, K2-L8
(ψ₀_0 ≠ 0 class-wide — the A = {1} corner is CLASS-EMPTY; the pin every
candidate is checked against FIRST), K2-L11 (⟨I₁, I₃⟩ closure), K2-L12
(patterns = closed partitions), K2-THM-B + the (R4⁺) corner covers, the
GLUE-DEGEN finding; machine legs `k2close_enum.py` (shape table 43+10,
GLUE-COVER 38/38) and `k2close_verdicts.py` (verdict column, corner safety,
committed `k2close_verdicts_results.json`); `survk2_instrument.py` (the
tracer + row selection, replicated verbatim); `engine_ext.py` per the
standing rule (import + install() + agreement_gate() re-run, counts
reported).  Machine leg of THIS unit: `verification/openmath/
gluegen_construct.py` (+ `gluegen_construct_results.json`,
`gluegen_table.md`).  Two-commit seal: this skeleton + the runner committed
BEFORE the sealed run; S2–S4 verdicts appended from artifacts only.

## S1. The derivation (charge 1): what makes a glued group residue-generic

**(D1) GLUE-DEGEN is forced by the residue field, not chosen by the glue.**
The 29 glued rows live on SDG2BF/SDG2BZ/SDW4G2F only — all p = 2, d₀ = 1
towers, so K₀ = F₂ and K₀* = {1}: EVERY nonzero residue is 1, every K2-L4
cell monomial evaluates to 1, and the coincidence pattern of every glued
group is the FULL MERGE, identically.  The realized degeneracy is a field-
size artifact.  Corollary: residue-genericity REQUIRES |K₀| = q ≥ 3.

**(D2) The genericity conditions.**  A glued shape with distinct cell
monomials μ₁..μ_n ∈ Z^{4+r} (K2-L4 coordinates x₀, x₁, ψ̄₀, ψ̄₁, ρ_1..ρ_r)
is GENERIC under an assignment φ: coords → K₀* iff φ(μ_i − μ_j) ≠ 1 for all
i < j — finitely many inequations in the cyclic group K₀* of order q − 1.
The class pin constrains ONLY the digit pair: ψ₀ = y² + ψ̄₁y + ψ̄₀ monic
irreducible over K₀ with ψ̄₀ ≠ 0 (K2-L8 — any solution demanding ψ̄₀ = 0,
i.e. the A = {1} corner, is DEAD ON ARRIVAL and excluded from the search
space outright) and, main table, ψ̄₁ ≠ 0 ((R2)); annex: ψ̄₁ = 0, forced odd
q (char 2 has no irreducible y² + c — K2-L8's Reading).  x₀, x₁, ρ_f are
free in K₀* (seed digits and interior dump-variant products).  WLOG x₀ = 1
and ρ_1 = 1 (each cell carries exactly one x and one ρ, so global scalings
preserve all coincidences).

**(D3) Small-field obstructions exist (hand-derived teeth).**  GS-02
(monomials x₀ρ₁ vs x₀ψ̄₁ρ₂) is generic iff ψ̄₁ρ₂/ρ₁ ≠ 1 — one inequation,
solvable at q = 3 (pair (ψ̄₀, ψ̄₁) = (2, 1), ρ₂ = 2).  GS-08 (fiber 1:
x₀ψ̄₀ρ₁, x₀ψ̄₁²ρ₁; fiber 2: x₀ψ̄₁ρ₂) needs ¬I₃ AND ρ₂/ρ₁ ∉ {ψ̄₀/ψ̄₁, ψ̄₁}:
over F₃ the two pin-legal pairs (2,1), (2,2) each exclude BOTH elements of
F₃* — GS-08 genericity is IMPOSSIBLE at q = 3 and first possible at q = 4
(pair (ω, 1) over F₄, ρ₂/ρ₁ = ω²).  The solver (S2) settles minimal q for
all 53 shapes.

**(D4) The realization route.**  Glue = dump-variant co-location.  The
realized glue reads are (3,1,2)@m=3 (SDG2B) and (3,1,2)@m=4 (SDW4); the
SAME reads at p = 5 (K2G2P5B) and p = 3 (K2W4G2Z) traced the SAME row keys
with ZERO glued groups — the dump-variant multiplicity rides the char-2
lift/carry structure, not the exponent arithmetic alone.  So the
construction keeps p = 2 (preserving the glue mechanism) and raises q
through the root inertia degree: d₀ = 2 → K₀ = F₄ (committed engine),
d₀ = 3 → K₀ = F₈ (`engine_ext` TowerExt through the (W2) wall).  A p = 3,
d₀ = 2 (K₀ = F₉) control tower probes the char-2 hypothesis (measured,
not predicted).

## S2. The solve (charge 1, machine) — PENDING commit 2

Per shape × field (F₃, F₄, F₅, F₇, F₈, F₉): exhaustive search over
pin-compliant assignments; outputs minimal generic q, witness assignment,
witness corner (I₁/I₃ truth), and the free-digit comparison (does the
irreducibility pin ever RAISE the threshold?).  Table: `gluegen_table.md`.

## S3. The realizations (charge 2, machine) — PENDING commit 2

Roster (sealed): GGB2AF/GGB2AZ (m=3, p=2, d₀=2, SDG2B reads, F₄);
GGW4AF (m=4, p=2, d₀=2, SDW4 reads, F₄); GGB3AF (m=3, p=2, d₀=3, F₈,
engine_ext); GGW3AF (m=3, p=2, d₀=2, SDW3 reads — control, no glue at
d₀=1); GGP3BF (m=3, p=3, d₀=2, F₉ — char-2-hypothesis control, measured).
Row selection = `run_fresh_tower` caps 12/6 replicated verbatim; per-tower
wall budget with disclosed-skip semantics (the K2-phase convention).

## S4. The verdict machinery on the realized groups (charge 3) — PENDING commit 2

Laws (LAW-KEYED; violation counts predicted 0 unless marked measured):
GG-PIN (ψ₀_0 ≠ 0 every tower — K2-L8 shadow); GG-FACT (K2-L4 monomial
readout cellwise on every glued bottom cell); GG-SHAPE (every realized
glued group normalizes into the committed 43+10 table; UNMATCHED/BREACH =
censused FINDING, the first beyond-perimeter realization, not a law
violation); GG-CLOSED (the in-vivo partition is a CLOSED state — K2-L12
shadow); GG-IDC (state H digit part ⊆ ⟨I₁, I₃⟩ — K2-L11 shadow);
GG-CORNER (state H contains no in-vivo-falsified identity); GG-STR
(string-class = keq-class agreement, harness); GG-THMB (**the falsifier**:
on every realized row whose β_min system covers its in-vivo corner c(φ),
some bottom group's in-vivo class vector is SD-L7 protected).

## S5. Sealed predictions (hand-derived BEFORE the sealed run)

  PG-A1  every one of the 53 shapes admits a pin-compliant fully generic
         assignment at some q ≤ 9; none at q = 2.
  PG-A2  minimal generic q: GS-02 = 3, GS-01 = 3, GS-08 = 4 (the D3
         derivation; the F₃ obstruction reproduced by the solver).
  PG-A3  the irreducibility pin never raises the threshold: minimal
         pin-compliant q == minimal free-digit q on all 53 shapes.
  PG-B1  GGB2AF and GGB2AZ each realize ≥ 1 glued β_min row; shapes match
         the committed table (GLUE-COVER extends to d₀ = 2).
  PG-B2  at q ≥ 4 some realized glued group attains ≥ 2 in-vivo residue
         classes — a non-full-merge state; PV-4's unprobed corner ENTERED
         (a MISS here = degeneracy is NOT a field-size artifact — finding).
  PG-B3  GG-PIN, GG-FACT, GG-CLOSED, GG-IDC, GG-CORNER, GG-STR: 0
         violations.
  PG-C1  GG-THMB: 0 violations — K2-THM-B's protection HOLDS on every
         corner-covered realized row (shape-level covers survive their
         first generic in-vivo probe).  A violation = counterexample to
         the covers' sufficiency — MAJOR FINDING, reported loud.
  PG-C2  GGP3BF (p = 3 control): MEASURED — glued rows expected 0 per the
         char-2 hypothesis; any glued row there is a finding (either way
         it decides the D4 attribution).

## S6. Verdict — PENDING commit 2 (from artifacts only)

## S7. Fences

(F-1) Everything ATTEMPT-capped by the consumed arcs; no hostile pass on
this note.  (F-2) The solver's genericity is the ABSTRACT K2-L4 model
(K2-L12 realizability discipline); engine faithfulness enters only through
GG-FACT on the realized cells.  (F-3) d₀ ≥ 2 towers sit OUTSIDE the d₀ = 1
perimeter of several consumed machine censuses (K2-JBOT's Y-freeness is
re-checked in vivo, not assumed).  (F-4) Realized-shape matching at d₀ ≥ 2
extends GLUE-COVER's domain; failures are boxed findings, not breaches.
