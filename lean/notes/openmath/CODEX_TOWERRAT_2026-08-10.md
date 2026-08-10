# TOWER RATIFICATION — CODEX ADVERSARIAL BATCH (decorrelated model, post-acceptance) + ADJUDICATION

## S0. Charter and provenance

**Batch:** the ratification sweep's tower leg — three FROZEN accepted notes,
each attacked in its own fresh-context Codex run (decorrelated model
`gpt-5.6-sol`, reasoning effort HIGH, quote-and-classify / fix-nothing,
outcome vocabulary {RATIFIED, RATIFIED-WITH-ANNEX, CHALLENGE}); acceptances
are ANNOTATED by challenges, never revoked.

**Subjects (all ACCEPTED 2/2, frozen at their acceptance commits):**
1. **HETOW** (`HETOW_RECON_2026-08-09.md`) — the tower σ-closure as a
   literal instance of frozen HE7 (instantiation table + HETOW-1/2/3 +
   termination + n_min = 12). Arc: seal → PE1 NOT-CLEAN 1C+2G+2m → r1 →
   PE2 CLEAN 0C/0G/3m → PE3 CLEAN 0C/0G/1m = ACCEPTED.
2. **GENTOW1** (`GENTOW1_PROOF_2026-08-09.md`) — composed entry budgets
   E₂ = e₂f₂u₂ + inner refine transfer + composed window ledger +
   depth-3 floor. Arc: seal → PE1 1G+2m → r1 gauge annex → PE2 CLEAN →
   PE3 CLEAN = ACCEPTED.
3. **GENTOW2** (`GENTOW2_PROOF_2026-08-09.md`) — item 6α via the FGMN
   cite (Thm 6.3 + Cor 6.4) + LEMMA B″ u(β_t) = ϑ(t)·w^{f₃−t}. Arc:
   seal → PE1 → r1 → PE2 → r2 → PE3 CLEAN → PE4 NOT-CLEAN (B-2
   machine-refuted, counter reset) → r3 (B″ PROVED) → PE5 CLEAN →
   PE6 CLEAN = ACCEPTED.

**Decorrelation discipline:** the orchestrator's pre-verdict key for every
charged surface was written and committed BEFORE any Codex output existed
(`towerrat_scaffold_2026-08-10.md`, commit 3be19b4, same commit as the
three briefs).

**Briefs** (committed 3be19b4, each fully self-contained — pasted note
byte-verbatim + consumed-statement excerpts + acceptance-pass verdict
sections; Codex sandbox broken on this box, so nothing read from disk):
- `towerrat_hetow_brief_2026-08-10.txt` (63,971 chars; PASTE B = HE7's
  DEFINITION HE7-1 + twist CONVENTION + THEOREM HE7.A/C/D byte-verbatim)
- `towerrat_gentow1_brief_2026-08-10.txt` (55,014 chars)
- `towerrat_gentow2_brief_2026-08-10.txt` (97,455 chars)
None approached the 1,048,576-char input cap; stderr checked at each
launch, no trim warnings.

**Runs of record** (stdin `-` prompt mode, nohup + disown + per-run fresh
pidfiles, launched sequentially):
- HETOW: session TBD
- GENTOW1: session TBD
- GENTOW2: session TBD

## S1. VERDICT SUMMARY (orchestrator adjudication, not Codex self-grade)

TBD

## S2. HETOW — Codex findings + adjudication

**Run:** session `019fe985-2c4b-7fc0-9885-5e558447502d`, ~5 min, 33,202
tokens, log `/tmp/codex_towerrat_hetow_out.log` (raw output reproduced in
the appendix). **Codex outcome: CHALLENGE — 3 findings, all classified
JUSTIFICATION GAP by Codex, plus 11 CHECKED CLEAN lines** (the wrap
identity, the multi-wrap telescoping SUM = floor, HETOW-1(c)'s exponent
algebra, HETOW-2's w = 0 leg AND the conditional carry arithmetic, the
termination row μ₁ ≥ e₂f₂μ₂ / J ≤ log₂n − 2, the n_min = 12 arithmetic
with uniqueness at (2,2,3), the no-second-jump claim, HETOW-3(a), and
both μ₂ = 3 σ-menus' degree totals). The three charged surfaces named in
the task (literal instance / termination arithmetic / letter clause at
multi-wrap) came back: termination CLEAN, multi-wrap letter clause CLEAN,
literal instance CHALLENGED on its residual-identification leg.

### F-1 — Codex GAP on the S1 normalizer row — ADJUDICATED **REAL (CONFIRMED GAP)**

Codex quote target: the row "n₂(k) = ϖ^{m(k)}Φ′^{s(k)} ... vs GENHN's
ladder monomials n̂₂(m) = π^ax^iΦ′^b | unit-residue discrepancy in K₂^×
only; σ-content twist-invariant per HE7 §S1 CONVENTION (J-D0)". Codex's
mechanism: HE7's twist CONVENTION covers ITS OWN cocycle-compatible
family (change of n₂ choice ⟹ coefficients scaled by powers of β — the
grade-covariant pattern, factor structure preserved); an ARBITRARY
per-height unit family is not covered (over F₃, Z²+2Z+1 = (Z+1)² and
Z²+2Z+2 irreducible differ by one coefficient unit), and HE7.A(3)
consumes the actual K₂-rational letter s₂, so "letters related by
HETOW-1's unit" (a single-height translation) does not identify the
HIGHER residuals read in the two normalizer systems.

**Adjudication: REAL.** Re-derived independently: branch routing between
HE7.A(2) (separable) and HE7.A(3) (repeated; then K₂-rational-linear vs
level-3) is NOT invariant under arbitrary per-coefficient unit scaling,
and the n̂₂/n₂ per-height discrepancy has a wrap-cocycle
(non-multiplicative) part — the note's own frame X (naive (Z+1)² vs
corrected irreducible minpoly) exhibits exactly this danger one seam
over. The note asserts J-D0 coverage without displaying the formula.
Blast radius, stated exactly: HE7.A still APPLIES at the instantiated
datum (HETOW-1/2/3 establish the datum hypotheses; the pins/polygon rows
are valuation-only and clean), so HETOW.A(ii)'s dictionary AT HE7's own
n₂-read stands; what is gapped is the identification "GENHN's composed
residuals ARE HE7.A's P₂ data" (the last clause of HETOW.A(i)) — the
claim that the read in TOWER coordinates routes identically.
**Repair charge queued (TOWERRAT-R1):** prove a HETOW-4 bridge lemma —
the per-height ratio n̂₂(m)/n₂(m) has residue a grade-determined letter
monomial forming a cocycle of the J-D0-covered species (the exact
level-2 analogue of GENTOW2's LEMMA B″ γ-calculus, which is the proved
template one level up), and check the two routing predicates
(separability; repeated-factor letter rationality) transport under it.
Scaffold match: predicted as the residual risk on this exact row
("possible GAP grade"; I expected MINOR — Codex's severity is right, the
routing predicates are letter-sensitive).

### F-2 — Codex GAP on the tower-node locus / every-root claim — ADJUDICATED **REAL AS DISPLAY, SUBSTANCE LICENSED**

Codex quote target: the level-2-point row + HETOW-3(b)'s "every root of
f on the opening locus is a level-2 point ... so S_{κ₂,r̃} = roots(f)".
Codex's mechanism: HETOW-1(b) translates letters at points ALREADY on
the locus; nothing displayed forces every root of f onto the locus
((T1),(T2)), so f_S = f is not proved self-containedly. (Codex's
(x−π)(x−2π) instance itself is off-target — its residual has two
DISTINCT roots, while HETOW's side carries ψ₂^{μ₂}, one irreducible —
but the missing-transport point stands independently of the instance.)

**Adjudication: REAL as display, licensed in substance.** The all-roots
forcing is the consumed GENHN-T(b)′ setting's own content — the ACCEPTED
GENTOW1 note (Step 4) states and cites it exactly: "All roots x₀ of
f ∈ 𝒯 are tower-node points: the full inner side forces v(Φ′(x₀)) =
u₂/(e₁e₂) exactly with η₂(x₀) a ψ₂-root — T(b)′(iii)'s (T1′)/(T2′)
transport, consumed." HETOW consumes the same setting (S1 opens
"verbatim GENHN-T(b)′") but does not display the transport cite at
HETOW-3(b)'s use site. **Repair: one-line cite addition at HETOW-3(b)**
(annex-grade; no statement change).

### F-3 — Codex GAP on disc f ≠ 0 — ADJUDICATED **ARTIFACT IN SUBSTANCE (frame data), MINOR display annex**

Codex quote target: the frame row "f monic, disc f ≠ 0, Φ′ ∤ f | Φ′ ∤ f
automatic at a full side | HETOW-3(a) ✓" — the check column discharges
only Φ′ ∤ f; Codex supplies a char-p inseparable f = (Φ′−π)^p with full
side and A₀ ≠ 0.

**Adjudication: ARTIFACT in substance.** f monic with disc f ≠ 0 is the
standing frame of the consumed setting (the σ/density program is posed
over separable f; T(b)′'s genre carries the level-1 frame wholesale —
S1's header imports it "verbatim"), so no new obligation arises and the
inseparable instance is outside the setting. REAL only as display: the
row's ✓ reads as if HETOW-3(a) discharged all three entries. **Repair:
annotate the row "monic + disc ≠ 0 = T(b)′ frame data (inherited), only
Φ′ ∤ f needed proof"** (annex-grade).

**HETOW outcome: CHALLENGE (annotates, does not revoke, the 2/2
acceptance).** One confirmed gap with a queued repair charge (F-1 →
TOWERRAT-R1), two display-level annex items (F-2, F-3). The r1 wrap
repair, the termination arithmetic, and the letter clause at multi-wrap
— the three surfaces the acceptance arc had owned hardest — all survived
the decorrelated attack.

## S3. GENTOW1 — Codex findings + adjudication

**Run:** session `019fe98a-19ed-7400-8b02-46117f9dd15b`, ~5 min, 35,425
tokens, log `/tmp/codex_towerrat_gentow1_out.log` (raw output in the
appendix). **Codex outcome: CHALLENGE — 4 findings (2 Codex-CRITICAL +
1 GAP + 1 MINOR) and 16 CHECKED CLEAN lines** (among them: the event
slice DOES prescribe residues including zero prescriptions; the
triangular map's unit diagonal gives injectivity; (c)'s congruence bound
valid with literal w(a,b); (d) is no weight/height conflation — slot
weight IS the composed digit height; the first-band tower-basis argument
coherent at e₂ ≥ 2; the [pin] guard has no negative corner since
w(a,b) < E₂ ≤ (μ₂−j)E₂; Step 0's variable reuse is a harmless dummy;
the CRT ranges suffice; no clause visibly consumes the gauge-naive
lifts; GENTOW-5(e)'s unipotence genuine).

### F-1 — Codex CRITICAL: the free-count display omits clipping — ADJUDICATED **REAL (GAP with mechanical repair)**

Quoted site (GENTOW-1(b)): "per window N the free-O-digit count is
Sum_{j,a,b} (N − floor(j,a,b))". Codex instance, verified by me
in-scope (μ₂ = 2, e₁ = f₁ = e₂ = 1, f₂ = 2, h = 1, u₂ = 2 — node floor
2 > 1 ✓, gcd ✓; floors 9/7/5/3): at N = 1 the display gives −20 while
the true budget box mod π is the single all-zero string (0 free digits).
The display is false whenever N < max floor; true with the clip
Σ max(0, N − floor). **Adjudication: REAL.** The intended content is
transparent and the battery ran at windows above the floors, but a
stated lemma clause is false on part of its parameter range, and
GENTOW-5(e)'s "budget/count display of GENTOW-1(b) is exact per window"
inherits it. Codex's CRITICAL regraded to **GAP-with-mechanical-repair**
(no consumer at small N exists in the corpus today; the count is a
display, not a load-bearing step of GENTOW-2/5's proofs).
**Repair charge TOWERRAT-R2a:** clip the display in (b) and re-scope
(e)'s exactness sentence (either the clipped form or N ≥ max floor).

### F-2 — Codex GAP: the ONTO cardinality argument — ADJUDICATED **REAL (GAP; scaffold-predicted)**

Quoted site (GENTOW-2 layer 3): "onto by cardinality: slot strings are
key-independent ... the mu2 pinned digits are the event data and the
remaining slots biject". Codex: the two finite sets are never defined
(truncated strings with ragged K₂-components need clipped counts); on
infinite strings equal cardinality + injectivity does not give
surjectivity; on finite windows the only supplied count is F-1's false
display. Codex also reports NO counter-count exists at the charged
small case (both projected sets singletons) — the conclusion is
plausibly true; the argument is incomplete. **Adjudication: REAL as a
justification gap** — exactly the scaffold's predicted thinnest step
(predicted: "possible GAP grade... REAL only if a concrete count
mismatch is exhibited"; none was, so the lemma's conclusion stands
unrefuted, the proof text owes the count). **Repair charge
TOWERRAT-R2b:** restate layer 3 with per-window clipped counts (the
floors transform identically under the triangular map, so the slotwise
free-digit counts match — display it), or replace cardinality by direct
digit-by-digit surjection up the window (the unipotent triangular
system solves upward without any counting).

### F-3 — Codex CRITICAL: GENTOW-5(a)'s iff self-contradicts its first-band clause — ADJUDICATED **REAL (statement repair owed)**

Quoted site: "a computed dv2-value is LIFT-STABLE iff < e1e2*N"
against the same clause's "at the FIRST band height m = e1e2*N exactly:
... the VALUE is exact for every lift". Codex instance verified: at
f₁f₂ ≥ 2, a readable digit at exactly the cap height on a flavor
complementary to the unread ones is value-stable (tower-basis
independence — the note's own mechanism) yet not < e₁e₂N; also
"undercutting every computed value ≥ e₁e₂N" fails at equality (tie, not
undercut). **Adjudication: REAL** — the clause compresses the intended
trichotomy (below cap: stable; at cap with f₁f₂ ≥ 2: value stable,
K₂-residue undetermined; deeper: unstable — the level-1 band annex's
own shape) into a biconditional whose only-if direction is false at the
cap. The clause's consumers survive on the intended reading ((c)'s
readable-event consultation rides residue-determinacy, not bare value
stability), but the STATEMENT of (a) owes a repair.
**Repair charge TOWERRAT-R2c:** restate (a) as the three-band form; no
proof content changes (the note's own first-band paragraph already
carries it).

### F-4 — Codex MINOR: "constant term untouched" — ADJUDICATED **REAL MINOR**

GENTOW-2(i)'s wording: the note's own B-R2 example (lift(s;λ) = 16+4xΦ′)
changes the constant coefficient by −16; what is untouched is the
constant term's SIDE DIGIT (the change sits strictly above the side),
which is what the invariance argument needs. Wording annex.

**GENTOW1 outcome: CHALLENGE (annotates, does not revoke, the 2/2
acceptance).** Three REAL defects (one clipped display, one
under-specified ONTO argument, one self-contradictory iff) + one
wording MINOR; repair charges R2a/R2b/R2c queued; no conclusion of
GENTOW-1/2/5 was refuted (Codex exhibited no counter-instance to any
CONCLUSION — the failures are in displays and proof text).

## S4. GENTOW2 — Codex findings + adjudication

TBD

## S5. Scaffold match record

TBD
