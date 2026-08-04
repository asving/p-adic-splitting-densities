# GLUEGEN-CONSTRUCT — residue-GENERIC glued groups: the PV-4 falsifier target, constructed

STATUS: COMPLETE (two-commit seal: skeleton+predictions 9888ea6, runner
e3922bb; verdict below from artifacts only — laws GREEN 0 violations,
predictions 6/8, the two misses substantive findings).  Unit of the
2026-08-08 campaign (wallclock 2026-08-04), per the constructed-
counterexamples directive: derive → solve → realize → verify; no sweeping.

**Verdict, stated first.**  (1) K2-THM-B **HELD** on all 30 corner-covered
realized rows — the shape-level covers survive their first generic in-vivo
probe (GG-THMB 0 violations).  (2) The PV-4 unprobed corner is ENTERED:
non-full-merge glued states realized at q ∈ {4, 8, 9}, including TEN fully
GENERIC GS-04 groups.  (3) The realized-shape census doubles (GS-04/15/29
new, all in-table), and GGB3AF (F₈, the first TWO-SEED glue tower —
I₁ determinate FALSE, corner c00) realizes **fourteen rows on which NO
bottom group is SD-L7 protected** — box (K2-RES-B)(i) is now NON-VACUOUS
in vivo, survival there carried by additive cancellation (SK2-BOT green).
(4) GS-02 stays FULL-MERGE at every q — the glue-pair coincidence is the
dump-swap pairing's residue-preservation law, NOT a field artifact.

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

## S2. The solve (charge 1, machine): every shape admits pin-compliant genericity

Fields F₂..F₁₆ (extended past the sealed F₃..F₉ by the shakedown-disclosed
COUNTING BOUND q − 1 ≥ n_monos — all monomial values must be distinct in
the cyclic K₀*; runner docstring repair (i)).  Results (`gluegen_table.md`,
53/53 rows):  **ALL 53 shapes admit a pin-compliant fully generic
assignment**; minimal q ranges 3 (GS-01/02/03/07, five annex shapes) to 13
(GS-43, 12 monomials — the bound tight given prime-power availability;
also tight: GS-38 8→9; GS-36/41/42 9 monomials → 11, the first prime
power past the floor 10).  **The irreducibility pin NEVER raises the
threshold: min-q(pin) = min-q(free-digit) on 53/53** — genericity is
constrained by the value-group size, never by ψ₀'s irreducibility, and no
candidate ever wanted ψ̄₀ = 0 (the A = {1} kill held by construction).
The D3 hand teeth confirmed exactly: GS-02 = 3, GS-01 = 3, GS-08 = 4.

## S3. The realizations (charge 2, machine): glue at q = 4, 8, 9

Roster as sealed (S0/S5); row selection caps 12/6 verbatim; engine_ext
gate re-run GREEN (0 new violations; agr_irr 158, agr_cert 1181, agr_pick
30, agr_tower 60, install 1).  Census (84 glued groups — GS-02 ×42,
GS-15 ×14, GS-08 ×13, GS-04 ×10, GS-29 ×4, GS-16 ×1 — GG-SHAPE 84/84
matched: GLUE-COVER extends to d₀ ≥ 2 and to THREE never-realized
shapes):

    GGB2AF/GGB2AZ (F₄, ¬I₃, I₁ undet): 14 glued rows, 18 groups EACH —
      14 GS-02 (1 class, FULL-MERGE, DEAD) + 4 GS-08 (2 classes, PROT);
      the d₀ = 1 shape census byte-reproduced one field size up.
    GGW4AF (F₄): the SDW4G2F row: GS-08 + GS-16, both 2-class, PROT.
    GGB3AF (F₈, d₀ = 3 through the (W2) wall; the FIRST two-seed glue
      tower — I₁ determinate FALSE, corner c00): 14 glued rows, 28
      groups, all NEW shapes: GS-04 ×10 (3/3 classes — FULLY GENERIC),
      GS-15 ×14 (4/5 classes), GS-29 ×4 (5/7 classes, one class of net
      +2 — the first in-vivo |net| ≥ 2 β_min class on a glued group).
    GGW3AF (F₄ control): 0 glued (matches d₀ = 1).
    GGP3BF (F₉, p = 3): 14 glued rows, 18 groups (14 GS-02 full-merge
      dead + 4 GS-08 2-class PROT) — the FIRST odd-characteristic glue.

Realized-shape census now {GS-02, GS-04, GS-08, GS-15, GS-16, GS-29}
(was 3 shapes).  PV-4's unprobed corner is ENTERED: 42 non-full-merge
glued groups in vivo (2/3/4/5-class states), 10 of them fully generic.

## S4. The verdict machinery on the realized groups (charge 3)

Laws (LAW-KEYED): GG-PIN (K2-L8 shadow) · GG-FACT (K2-L4 readout, every
glued bottom cell) · GG-SHAPE (66/66 matched) · GG-CLOSED (K2-L12 shadow:
every in-vivo partition CLOSED) · GG-IDC (K2-L11 shadow) · GG-CORNER (no
in-vivo-falsified identity in any state H) · GG-STR (string = keq classes,
validated on all 531 pinned grprec records first) · GG-PROT (model/vivo
protection agree) · GG-THMB (the falsifier) — **ALL GREEN, 0 violations**;
tracer harness (SK2-*) surfaced 0 on all six towers.

**GG-THMB, the falsifier verdict: K2-THM-B HELD.**  30 realized glued
rows cover their in-vivo corner under every completion of the
undetermined I₁ coordinate (repair (ii)) — the S-carrying rows, 10 each
on GGB2AF/GGB2AZ/GGP3BF; on every one some bottom group is SD-L7
protected in vivo — no counterexample.  Bonus instance fact: the 13
UNCOVERED-but-protected rows (4+4+4 [GS-02, GS-08] anchor rows at ¬I₃ on
those towers + the GGW4AF [GS-08, GS-16] row — the K2-CLOSE F-1 genre,
now probed at ¬I₃ with teeth) are all carried by the anchors' PARTIAL
2-class states: the ¬I₃ split leaves a protected remainder in vivo —
PC-2's anchors working OFF their safe corner, instance-grade only.

**The uncovered corner realized (box (K2-RES-B)(i) non-vacuous).**  All
14 GGB3AF glued rows sit at the determinate corner c00 (¬I₁ ∧ ¬I₃), cover
only {c10, c11} (their GS-04/GS-15 anchors are I₁-corner-safe shapes),
and on every one **NO bottom group — glued or single-book — carries an
SD-L7-protected vector** (in-vivo vectors e.g. GS-04 generic (−1,+1,+1),
GS-15 (−1,+1,0,+1), GS-29 (+2,−1,−1,−1,+1)).  The rows are LIVE and their
netted bottoms SURVIVE (SK2-BOT green): survival is carried by additive
mixed-sign arithmetic outside the multiplicative calculus — exactly the
mechanism (K2-RES-B)(i) names, now with 14 concrete instances.  (SURV-K2)
in the weak per-class sense still holds row-wide (SK2-MULT1 green); the
PROTECTED-vector existence fails on these rows — the first realized gap
between the two readings.

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

**S5 verdicts (from `gluegen_construct_results.json`, appended — the
sealed text above is byte-untouched):** PG-A2, PG-A3, PG-B1, PG-B2,
PG-B3, PG-C1 **GREEN**; PG-A1 **MISS** (GS-36/41/42 need q = 11, GS-43
needs q = 13 — the counting bound q − 1 ≥ n_monos, disclosed pre-seal at
repair (i), is the exact reason; "none at q = 2" held); PG-C2 **MISS,
measured** (GGP3BF realized 14 glued rows at p = 3).

## S6. Verdict, and two derivation corrections (dated, superseding-in-place)

**[GG-r1 correction to D1, 2026-08-08 campaign (wallclock 2026-08-04).]**
D1's field-size explanation of GLUE-DEGEN is only HALF right.  Right: at
q = 2 full merge is forced, and enlarging the field DOES split GS-08/15/16/29
states.  Wrong half: the GS-02 glue PAIR stays full-merge at q = 4, 8, 9
on all 42 realized pairs — the coincidence ψ̄₁ρ₂ = ρ₁ holds in vivo at
every field size.  Corrected attribution: the realized glue pair is the
instrument's DUMP-SWAP exchange (K2-L7 reading, cross-book), which is
RESIDUE-PRESERVING by the measured pairing law — the pair's two cells
coincide by mechanism, not by field accident.  Consequence: the K2-L12
states of GS-02 with ¬(glue identity) — the protected (+1, −1) pair —
appear UNREALIZABLE by this engine's dump mechanism; PC-1's dichotomy is
instance-resolved to the g-true branch on all 42 pairs.  The state-space
model stays sound (conservative superset); its generic GS-02 corner is
engine-dark, now knowingly so.

**[GG-r1 correction to D4.]**  The char-2 attribution is REFUTED by the
sealed control: GGP3BF (p = 3, d₀ = 2) realizes the full 14-row glue
census.  Corrected census: glue realized at {p = 2, d₀ ∈ {1,2,3}} and
{p = 3, d₀ = 2}; absent at {p = 5, d₀ = 1} and {p = 3, d₀ = 1} (the
committed K2G2P5B/K2W4G2Z reads).  The dump-variant multiplicity rides
the root-key lift-term structure (present at d₀ ≥ 2 for any p, and at
d₀ = 1 only via the char-2 carries) — boxed as a measured attribution,
not derived.

**What this unit adds to the K2-CLOSE ledger.**  (a) K2-THM-B's covers
survive their first residue-generic probe (30/30 covered rows protected)
— the falsifier found no counterexample; the covers' sufficiency stands
at instance grade beyond full-merge.  (b) Box (K2-RES-B)(i) is
NON-VACUOUS: 14 realized corner-uncovered rows with NO SD-L7-protected
group, netted bottoms surviving additively — the additive-arithmetic
residual is now the demonstrated, not hypothetical, frontier of the
involution program.  (c) The K2-L12 state space is in-vivo validated at
six distinct states (GG-CLOSED/IDC/CORNER green), incl. a fully generic
one.  (d) PV-4's disposition closes: the degenerate roster was field-size
artifact for the |T| ≥ 1 shapes and pairing-law NECESSITY for the glue
pairs.

## S7. Fences

(F-1) Everything ATTEMPT-capped by the consumed arcs; no hostile pass on
this note.  (F-2) The solver's genericity is the ABSTRACT K2-L4 model
(K2-L12 realizability discipline); engine faithfulness enters only through
GG-FACT on the realized cells.  (F-3) d₀ ≥ 2 towers sit OUTSIDE the d₀ = 1
perimeter of several consumed machine censuses (K2-JBOT's Y-freeness is
re-checked in vivo, not assumed).  (F-4) Realized-shape matching at d₀ ≥ 2
extends GLUE-COVER's domain; failures are boxed findings, not breaches.
(F-5) The corner-coverage test conservatively requires coverage under
EVERY completion of the I₁-undetermined coordinate (single-seed towers);
GGB3AF alone is corner-determinate.  (F-6) "GS-02 generic states are
engine-unrealizable" (GG-r1/D1) is an instance observation over 42 pairs
at three field sizes, not a proved impossibility.  (F-7) The 14
unprotected GGB3AF rows do NOT contradict K2-THM-A/B (their systems fail
(R4⁺): no S, and the anchors sit off their safe corner) nor (SURV-K2)'s
weak per-class reading (SK2-MULT1 green); they instantiate the open box
(i).  Residue class strings compared under the GG-STR validation (531/531
pinned + all new rows).
