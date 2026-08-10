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

**Runs of record** (stdin `-` prompt mode — `codex exec --skip-git-repo-check
-c model_reasoning_effort=high -` with the brief on stdin; nohup + disown +
per-run fresh pidfiles, launched sequentially; a first HETOW launch attempt
came up at effort NONE from config defaults and was killed pre-output by its
own pidfile, then relaunched with the effort pinned):
- HETOW: session `019fe985-2c4b-7fc0-9885-5e558447502d`, ~5 min, 33,202 tokens
- GENTOW1: session `019fe98a-19ed-7400-8b02-46117f9dd15b`, ~5 min, 35,425 tokens
- GENTOW2: session `019fe98f-1e70-7321-9422-de37059d2b46` (details in S4)

## S1. VERDICT SUMMARY (orchestrator adjudication, not Codex self-grade)

| note | Codex outcome | findings (Codex grade) | adjudication | repair queue |
|---|---|---|---|---|
| HETOW | **CHALLENGE** | 3 GAP | 1 REAL GAP (residual-identification leg of the literal-instance claim) + 1 display (all-roots cite) + 1 artifact (disc ≠ 0 = frame data) | R1 (substantive) |
| GENTOW1 | **CHALLENGE** | 2 CRITICAL + 1 GAP + 1 MINOR | 3 REAL (unclipped count display; ONTO under-specified; cap-iff self-contradiction — Codex's CRITICALs regraded GAP-with-repair: no CONCLUSION refuted) + 1 wording | R2a/b/c |
| GENTOW2 | **RATIFIED-WITH-ANNEX** | 4 MINOR | 4 REAL MINOR (hygiene) | R3 (batch) |

Acceptances stand ANNOTATED (standing vocabulary: challenges annotate,
never revoke). The pattern across the batch: the three notes' NEWEST
mathematics (the wrap cocycle, the carry/budget arithmetic, LEMMA B″)
survived the decorrelated attack; the hits landed on IDENTIFICATION and
DISPLAY layers (a twist-coverage claim asserted without its formula, an
unclipped count, a compressed iff) — the same genre HE7RAT's F1 found
(§S6 ladder) and GRB's Def-3.15 artifact before that: the decorrelated
model's yield is highest exactly where same-family passes read past
what the author "obviously meant."

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

**Run:** session `019fe98f-1e70-7321-9422-de37059d2b46`, ~7 min, 48,140
tokens, log `/tmp/codex_towerrat_gentow2_out.log` (raw output in the
appendix). **Codex outcome: RATIFIED-WITH-ANNEX — 4 findings, each
classified MINOR by Codex, and 21 CHECKED CLEAN lines covering the
charged load-bearing surfaces in full**: B″ steps (i)–(iv) each
re-derived (peel orientation with grades in Γ₂; ν(G) = dκ̄ = β_t
established BEFORE Def 1.8 is used; λ₃'s exact order e₃ mod Γ₂ forces
e₃ | j; eq (14) placement at y^{j/e₃} ≥ 1; step (iv) NON-CIRCULAR —
B-1 pins ν(Q₀) = β_t before B′(3) fires), the γ-calculus eliminations,
ϑ(f₃−1) = 1, the Cor 6.4 non-equivalence display (both keys in KP(ν),
R₃ values 𝜓₃ ≠ 1, Prop 5.7 applies exactly — my scaffold's main
predicted finding, which the note's r1 repair had already discharged),
Thm 6.3 role consistency, chain optimality at the use-site, clause (d)
conversions, ψ^{(w)} admissibility + the prescription algebra, the
(B-law) abscissa bookkeeping, the [Q6] degree-forcing chain, the on-line
height arithmetic, the Def 3.18 j₀ = 0 passage, honesty-box scope (the
refuted B-2 consumed NOWHERE in the repaired proof), S7's consumption
list (w = 1 needed nowhere), and LD3's f₃ = 1 consistency.

### The four MINORs, adjudicated (each REAL at annex grade)

- **F-1 (Codex: MINOR-OVERCONSUMPTION) — REAL MINOR.** S6's hypothesis
  audit sentence "Cor 6.4 needs only 'a MacLane chain', not optimality"
  outruns [Q10], which asks for a chain "as in (4)" = the optimal chain
  of the note's own S2 dictionary. Verified at note line 925. Harmless
  at the use-site: the SAME audit row derives optimality from stage
  properness before the overreaching clause. Repair: strike or weaken
  the clause (annex).
- **F-2 (Codex: MINOR) — REAL MINOR.** B″ step (iv)'s "digit(Q₀) =
  digit(G)" applies the S5.1 `digit` notation to G = ẑN^d, which can
  have degree ≥ m₃ (outside `digit`'s defined scope); the displayed
  computation is the normalized evaluation residue res(G(x₀)/M(x₀)) and
  is used as such — B-1 is invoked only on Q₀ (in scope). Notation
  hygiene repair.
- **F-3 (Codex: MINOR) — REAL MINOR.** The S5 proof's opening display
  "Write α := e₃f₃(w₃..." is syntactically truncated (note line 342);
  the parenthetical supplies α = e₃f₃(w₃ + λ₃) and the sequel uses it.
  Typographical.
- **F-4 (Codex: MINOR) — REAL MINOR.** The symbol ψ₂ is overloaded
  between FGMN's minpoly(z₂) and the repo's minpoly(η₂) (which differ
  by the z₁-twist the note itself establishes, e.g. LP1's z₂ = 1 vs
  η₂ = z₁ ≠ 1); the S4 consumption note translates correctly through
  the single embedding, so no consumed inference is false. Notation
  hygiene repair.

**GENTOW2 outcome: RATIFIED-WITH-ANNEX.** No GAP-or-worse; the note
that survived the hardest same-family arc (six passes, one machine
refutation, the B″ r3 repair) is the one the decorrelated model
ratifies. The four annex items are queued as a single hygiene batch
(TOWERRAT-R3).

## S5. Scaffold match record

Pre-verdict key (`towerrat_scaffold_2026-08-10.md`, committed 3be19b4
before any output) vs outcomes:

- **HETOW** — predicted RATIFIED(-WITH-ANNEX) with the residual risk
  named EXACTLY at the S1 normalizer row's twist-invariance discharge
  ("a hostile read could grade the row's reliance on twist-invariance
  as a GAP"); actual: CHALLENGE with the heaviest finding on that row.
  Direction right, severity under-called (I said "at most MINOR"
  because HETOW-1(b) is pointwise — Codex correctly observed the
  ROUTING predicates consume more than the single-height letter).
  Termination + multi-wrap predicted HOLD: held. F-2/F-3 (frame
  consumption surfaces) unpredicted.
- **GENTOW1** — predicted RATIFIED-WITH-ANNEX; predicted the ONTO
  cardinality as "the thinnest step... possible GAP grade... REAL only
  if a concrete count mismatch is exhibited" — hit exactly (Codex F-2,
  GAP, no mismatch exists). Predicted (c) CLEAN: held. Predicted the
  [pin] corner as a risk: came back CLEAN (w(a,b) < E₂ ≤ (μ₂−j)E₂).
  Unpredicted: F-1 (clipping) and F-3 (the cap iff) — both real; the
  window-cap axis was not in my key at all. Outcome CHALLENGE, one
  grade beyond my call.
- **GENTOW2** — predicted RATIFIED-WITH-ANNEX: hit. My main predicted
  finding (Cor 6.4's φ ≁_µ φ_r hypothesis) came back CHECKED CLEAN,
  correctly — I verified pre-read that the note's r1 paragraph (PE1 F4)
  discharges it via Prop 5.7 with both keys certified in KP(ν). The
  γ-calculus residue-leg risk I flagged did not materialize (Codex
  re-derived the eliminations).

## S6. REPAIR QUEUE (charges, not executions — for the orchestrator)

- **TOWERRAT-R1 (HETOW, the one substantive charge):** HETOW-4 bridge
  lemma — n̂₂(m)/n₂(m) residue = grade-determined letter monomial of the
  J-D0-covered cocycle species (template: GENTOW2 LEMMA B″'s
  γ-calculus), + transport of the two routing predicates (separability;
  repeated-factor letter K₂-rationality). Until it lands, HETOW.A(i)'s
  final clause ("composed residuals ARE the P₂ data") carries the gap
  annotation; HE7.A's applicability at the instantiated datum is NOT
  affected.
- **TOWERRAT-R2a/b/c (GENTOW1):** clip the (b) free-count display +
  re-scope (e)'s exactness; supply the clipped-count (or direct
  surjection) ONTO argument at GENTOW-2 layer 3; restate GENTOW-5(a)
  as the three-band form its own first-band paragraph carries.
- **TOWERRAT-R3 (GENTOW2, hygiene batch):** strike the "not optimality"
  clause; digit(G) → res(G(x₀)/M(x₀)) at B″(iv); fix the truncated α
  display; disambiguate ψ₂^{FGMN} vs ψ₂^{repo} at the two S4 sites.

---

## APPENDIX — RAW CODEX OUTPUTS (verbatim)

### A.1 HETOW run (session 019fe985-2c4b-7fc0-9885-5e558447502d)

```
1. > “unit-residue discrepancy in K₂^× only; σ-content twist-invariant per HE7 §S1 CONVENTION (J-D0)”
   >
   > “(residues: same content, letters related by HETOW-1's unit)”
   >
   > “GENHN-T(b)′'s composed pins/polygon/residuals ARE THEOREM HE7.A's P₂ data at that datum”

   **Classification: JUSTIFICATION GAP.**

   A coefficientwise discrepancy by elements of \(K_2^\times\) is not, by itself, a twist under which residual factorization is invariant. HE7 fixes
   \[
   n_2(k)=\varpi^{m(k)}\Phi'^{s(k)}
   \]
   and controls the explicit \(\beta\)-cocycle of that system. GENHN instead uses monomials \(\widehat n_2(k)=\pi^a x^i\Phi'^b\). HETOW never computes
   \[
   \operatorname{res}\!\left(\widehat n_2(k)/n_2(k)\right)
   \]
   along an arbitrary level-2 side, nor proves that the resulting coefficient factors form the geometric variable-rescaling prescribed by HE7’s convention. Merely observing that each ratio lies in \(K_2^\times\) is insufficient: over \(\mathbf F_3\), \(Z^2+1\) is irreducible, whereas independently multiplying its constant coefficient by the unit \(2\) gives
   \[
   Z^2+2=(Z-1)(Z+1).
   \]
   Thus arbitrary unit discrepancies can alter degrees, multiplicities, and the separable/repeated branch.

   HETOW-1 translates only the initial letter
   \[
   \beta=\eta^{-Q(u_2)}\eta_2
   \]
   and the slots defining the composed key. It supplies no coefficientwise translation for the later residual polynomials \(R_{\lambda_2}\) of arbitrary \(A_j^{(2)}\). This matters precisely in HETOW.A(ii)–(iii): a repeated \(K_2\)-rational linear factor consumes its actual root \(s_2\) to choose the lift \(w\) and continue the refine chain. The pointwise proof of HETOW-1(b) does not translate those later \(s_2\)-letters. Consequently the coordinate-free HE7 decision may remain true, but the asserted literal identification with GENHN’s residual data is not established.

2. > “| level-1 frame: f monic, disc f ≠ 0, Φ′ ∤ f | Φ′ ∤ f automatic at a full side | **HETOW-3(a)** ✓ |”
   >
   > “A root x₀ has dv(Φ′(x₀)) = a slope of the polygon (COROLLARY HE6-2″); the only slope is κ₂; … So every root carries the label (κ₂, r̃); \(|roots| = deg f\), \(f_S=f\) …”

   **Classification: JUSTIFICATION GAP.**

   The check column establishes only \(\Phi'\nmid f\). It does not establish \(\operatorname{disc}(f)\ne0\), and the HETOW-3(b) proof then uses the separability consequence \(|\operatorname{roots}(f)|=\deg f\).

   This omission is not automatic from the displayed full-side conditions. For example, take \(\mathcal O=\mathbf Z_5\),
   \[
   e_1=2,\quad f_1=h=1,\quad D'=2,\quad \Phi'=x^2-5,
   \]
   and put
   \[
   \Phi_2=\Phi'^2-5^2x,\qquad f=\Phi_2^3.
   \]
   In the reduced \(\Phi'\)-development, the finite pins include
   \[
   (0,15),(1,13),(2,10),(3,8),(4,5),(6,0),
   \]
   whose lower hull is the full side of slope \(5/2>D'h=2\). Its residual is \((Z-1)^3\), so it has
   \[
   (e_2,f_2,\mu_2)=(2,1,3),\qquad \mu_1=6,
   \]
   and \(A_0=-5^7x\ne0\), hence \(\Phi'\nmid f\). Nevertheless \(\operatorname{disc}(f)=0\), and its distinct-root set is the root set of the degree-four polynomial \(\Phi_2\), not a set of cardinality \(\deg f=12\). Thus HETOW-3(b), \(f_S=f\), and the application of HE7.A do not follow from the hypotheses actually checked in S1. If “outer genre” is intended to import separability, that import is not stated or verified in the self-contained instantiation table.

3. > “| level-2 point: (T1),(T2), dv(Φ′(ξ)) = λ, ι(r)(βξ) = 0 | tower-node locus: (T1),(T2),(T1₂),(T2₂) | HETOW-1(b): … hence the tower-node locus IS the level-2 point set … |”
   >
   > “A root x₀ has dv(Φ′(x₀)) = a slope of the polygon … the only slope is κ₂ … So every root carries the label \((κ₂,r̃)\).”

   **Classification: JUSTIFICATION GAP.**

   HETOW-1(b) proves the translation of the final two conditions:
   \[
   dv(\Phi'(x_0))=\kappa_2,\qquad
   \widetilde r(\beta_{x_0})=0
   \Longleftrightarrow
   \psi_2(\eta_2(x_0))=0.
   \]
   It does not prove that every root of \(f\) satisfies the inherited base-frame conditions (T1) and (T2). The table places (T1),(T2) into the definition of “tower-node locus” and then cites that locus as their verification; HETOW-3(b) derives only the Newton slope and residual label. A full \(\Phi'\)-side controls \(dv(\Phi'(x_0))\) and its side residue, not membership in an independently prescribed opening disk. Hence the equality “tower-node locus IS the level-2 point set,” and especially the subsequent assertion that every root lies in it, requires an unstated inheritance result from the outer label block.

CHECKED CLEAN — The wrap identity and \(Q\)-cocycle have the correct sign:
\(\widehat n(a)\widehat n(b)=\widehat n(a+b)(x^{e_1}/\pi^h)^{\mathrm{wrap}}\) and \(Q(a+b)=Q(a)+Q(b)+\mathrm{wrap}\).

CHECKED CLEAN — Multi-wrap telescoping is valid: the sum of all intermediate carries is \(\lfloor q\,i(u_2)/e_1\rfloor\), so a single \(W(t)\) correctly represents the accumulated carries.

CHECKED CLEAN — HETOW-1(c)’s exponent cancellation is correct:
\(W(t)-Q((f_2-t)u_2)=-(f_2-t)Q(u_2)\).

CHECKED CLEAN — The valuation part of (SLOT2) re-derives exactly as
\[
\min_{i,s}\bigl(e_1e_2v(c_{i,s})+i e_2h+s u_2\bigr).
\]
The unresolved issue is its residue-letter transfer, recorded in Finding 1.

CHECKED CLEAN — For the actually consumed corrected \((\mathrm{LIFT})\)-slot construction, every coefficient is already reduced and \(w=0\); the dated C-A rider correctly prevents consumption of the defective leading-slot overflow generalization.

CHECKED CLEAN — In the auxiliary carry calculation, moved material gains exactly \(u_2-e_2D'h>0\), stationary material never decreases in value, and the ultrametric pointwise residue equality is valid when the moved summand has strictly greater value.

CHECKED CLEAN — HE7.C licenses the tower entry as a jump: the outer side carries \(\psi_2^{\mu_2}\) with multiplicity at least \(2\) and \(e_2f_2\ge2\), and full-side equality coheres with \(\mu_2\le\mu_1/(e_2f_2)\).

CHECKED CLEAN — The termination arithmetic is correct:
\[
\mu_1\ge\mu_2e_2f_2,\qquad
J\le\log_2\mu_1-1\le\log_2n-2.
\]

CHECKED CLEAN — The minimal live-degree calculation is correct:
\(D'\ge2\), \(e_2f_2\ge2\), and \(\mu_2\ge3\) give \(n\ge12\), with equality exactly at \((D',e_2f_2,\mu_2)=(2,2,3)\).

CHECKED CLEAN — At \(n=12\), integrality gives \(J\le1\); the existing tower entry supplies one jump, while \(\mu_2=3\) excludes a second jump because HE7.A(3) requires side length at least \(4\).

CHECKED CLEAN — HETOW-3(a) is valid: a finite attained left endpoint gives \(A_0\ne0\), and the reduced \(\Phi'\)-development then gives \(\Phi'\nmid f\).

CHECKED CLEAN — Conditional on the missing base-frame and locus hypotheses, the full-side Newton-polygon argument does put every root on slope \(\kappa_2\), and a residual with the sole irreducible factor \(\widetilde r\) gives the asserted label.

CHECKED CLEAN — The \(\mu_2=2\) trichotomy and both displayed \(\mu_2=3\) sigma menus have the correct degree accounting.

The wrap repair, multi-wrap algebra, termination bounds, and minimal-degree claim survive. Ratification nevertheless fails because the central “literal instance” transfer does not establish the later residual-letter transformation, and the block identification \(f_S=f\) consumes base-frame/separability and opening-locus hypotheses that the table does not actually discharge.

OUTCOME: CHALLENGE
```

### A.2 GENTOW1 run (session 019fe98a-19ed-7400-8b02-46117f9dd15b)

```
1. Quote: “per window N the free-O-digit count is Sum_{j,a,b} (N − floor(j,a,b)).”

   Classification: CRITICAL ERROR.

   The formula omits truncation at zero. Coefficients lie in \(\mathcal O\), so a slot whose required floor \(L\ge N\) contributes zero free digits modulo \(\pi^N\), not \(N-L<0\).

   Concrete counter-configuration requested in the charge: take
   \[
   \mu_2=2,\quad e_1=f_1=e_2=1,\quad f_2=2,\quad h=1,\quad u_2=2.
   \]
   Then \(D'=1\), \(e_2f_2=2\), \(E_2=4\), and \(w(0,b)=2b\). The four floors are
   \[
   9,\ 7,\ 5,\ 3
   \]
   for \((j,b)=(0,0),(0,1),(1,0),(1,1)\). At \(N=1\), the displayed sum is
   \[
   (1-9)+(1-7)+(1-5)+(1-3)=-20,
   \]
   while the actual budget box modulo \(\pi\) has exactly one string: all four coefficients are zero. Thus the exact per-window count asserted in GENTOW-1(b), and consumed again in GENTOW-5(e), is false unless an unstated large-\(N\) hypothesis is imposed. This also deprives GENTOW-2 layer 3 of its advertised unrestricted per-window cardinality input.

2. Quote: “onto by cardinality: slot strings are key-independent (GENHN-2' at Phi2+ via (i)), the mu2 pinned digits are the event data and the remaining slots biject.”

   Classification: JUSTIFICATION GAP.

   For fixed \(s\) and \(N\), the two sets that must be compared are:

   - the reductions modulo \(\pi^N\) of old-key arrays for which, at \(H_j=(\mu_2-j)\lambda\), every lower \(K_2\)-height digit is zero and the height-\(H_j\) digit equals the prescribed coefficient of \((T-s)^{\mu_2}\), including prescribed zero coefficients;
   - the reductions modulo \(\pi^N\) of new-key arrays for which all digits through height \(H_j\) are zero.

   Because a \(K_2\)-digit has ragged \(\mathcal O\)-components, these must technically be defined as truncated strings admitting full completions. The proof defines neither finite set and supplies no clipped count. On full infinite slot strings, equal cardinality plus injectivity does not imply surjectivity; a proper subset may have the same infinite cardinality. On finite windows, the only explicit count supplied is the false formula identified in finding 1.

   There is no intrinsic counter-count in the charged small case: after using clipped counts, both sides fix the same visible components. For the parameters in finding 1 and \(N=1\), both projected sets are singletons. Thus the ONTO conclusion may be true, but the stated cardinality argument does not establish it for every window.

3. Quote: “a computed dv2-value is LIFT-STABLE iff < e1e2*N” and, later in the same clause, “at the FIRST band height m = e1e2*N exactly: … the VALUE is exact for every lift”.

   Classification: CRITICAL ERROR.

   These assertions directly contradict one another. The first-band independence mechanism itself supplies counterexamples to the “iff”.

   Use the parameters from finding 1 and take \(N=5\). In coordinate \(j=1\), the slot \(b=1\) has budget floor \(3\). Set
   \[
   c_{1,0,1}=\pi^3\cdot\text{unit}
   \]
   and all other perturbation slots to zero. Its height is
   \[
   3+w(0,1)=3+2=5=e_1e_2N.
   \]
   The unread \(b=0\) coefficient beginning at valuation \(N=5\) also has height \(5\), but it occupies the \(1\)-flavor, whereas the readable term occupies the \(\eta_2\)-flavor in \(K_2/K\). Tower-basis independence prevents cancellation. Hence the value is \(5\) for every lift: it is lift-stable but is not \(<e_1e_2N\).

   The proof’s related phrase “undercutting every computed value \(\ge e_1e_2N\)” also fails at equality: an unread term at the cap ties rather than undercuts. The below-cap implication survives, but the stated biconditional in LEMMA GENTOW-5(a) is false.

4. Quote: “strictly above the x-side through (D2, 0), constant term untouched.”

   Classification: MINOR.

   The constant term need not be literally untouched. The document’s own B-R2 example has
   \[
   \operatorname{lift}(s;\lambda)=16+4x\Phi',
   \]
   so \(\Phi_2^+=\Phi_2-\operatorname{lift}(s;\lambda)\) changes the constant coefficient by \(-16\). What remains untouched is the constant-term side digit or initial form, because the change lies strictly above the side. The invariant argument only needs that weaker statement.

CHECKED CLEAN — The event slice constrains residual equalities, not merely valuations: for every \(j\), its height-\(H_j\) \(K_2\)-digit is prescribed, with a zero prescription when the relevant binomial coefficient vanishes.

CHECKED CLEAN — In the small \(\mu_2=2,\ e_1=f_1=1,\ e_2f_2=2\) case, properly clipped old-event and new-node counts agree; no genuine counter-count exists.

CHECKED CLEAN — “new digit = old digit + strictly-lower-height data” has unit diagonal and gives recursive injectivity over the residue-digit alphabet; monic key division also gives an ambient unipotent map over \(\mathcal O\).

CHECKED CLEAN — GENTOW-5(c)’s congruence bound is valid with literal \(w(a,b)\): writing \(w=qk+r\), \(q=e_1e_2\), gives \(m\le q(N-1)+r\le q(N-1)+w\).

CHECKED CLEAN — GENTOW-5(d) does not conflate two unrelated quantities: slot weight is precisely the composed digit height, so weight-nondecreasing carries imply that an output at height \(d\) uses old digits only at heights \(\le d\).

CHECKED CLEAN — The first-band tower-basis argument is coherent even when \(e_2\ge2\): the products \(\eta^r\eta_2^t\) form successive independent component directions, so complementary unread flavors cannot cancel a nonzero readable component.

CHECKED CLEAN — The budget pin guard causes no negative-corner error because
\[
w(a,b)<u_2+(e_2f_2-1)u_2=E_2,
\]
while \((\mu_2-j)E_2\ge E_2\); hence the guarded difference is always positive.

CHECKED CLEAN — Step 0’s \(n(m)=x^i\pi^a\) merely reuses \(a\) as a local dummy variable: its arithmetic
\[
e_1e_2a+i e_2h=e_2(e_1a+ih)=e_2m
\]
is correct.

CHECKED CLEAN — Both Step-0 carries are weight-monotone: the \(x\)-tail is priced by the \(\Phi'\)-side, and every corrected \(\Phi'\)-carry lift has weight exactly \(E_2\).

CHECKED CLEAN — Equality of a coherent \(K_2\)-residue digit implies equality of every basis component modulo \(\pi\); subtracting therefore raises each component by one \(\pi\)-power and its weight by \(e_1e_2\).

CHECKED CLEAN — The corollary’s convexity direction is correct: for a lower hull with endpoint \((\mu_2,0)\), the rightmost positive slope magnitude is \(\min_j p_j/(\mu_2-j)\), and slopes can only increase moving left.

CHECKED CLEAN — GENTOW-2(i)’s arithmetic follows from \(\lambda>E_2\) and \(u_2>e_2D'h\), yielding a strict height above \(D_2e_2h\).

CHECKED CLEAN — GENTOW-2(iv) handles \(p\mid\binom{\mu_2}{j}\) correctly: the leading graded coefficient is then zero, while all \(i<\mu_2\) contributions are strictly above the node height.

CHECKED CLEAN — Step 4’s CRT construction reaches every residue modulo \(e_1e_2\) with \(b<e_2\) and \(a<e_1\); its restricted ranges are sufficient.

CHECKED CLEAN — The corrected \(\widehat c_t\) convention is present at every value-sensitive use identified in the note; no remaining clause visibly consumes the gauge-naive residue formula.

CHECKED CLEAN — GENTOW-5(e)’s ambient coefficient-to-composed-coordinate map is genuinely unipotent over \(\mathcal O\) and therefore bijective modulo \(\pi^N\); the failure is the subsequent unrestricted budget count, not the ambient change of coordinates.

The central valuation and carry arithmetic survives, as do the residual-event correspondence and triangular injectivity. Nevertheless, the note contains a false unrestricted window-count formula, an explicit contradiction in the cap theorem, and an incomplete finite-cardinality argument for ONTO. Those are GAP-or-worse defects in stated lemmas, so post-acceptance ratification cannot stand.

OUTCOME: CHALLENGE
```

### A.3 GENTOW2 run (session 019fe98f-1e70-7321-9422-de37059d2b46)

```
1. Verbatim quote: “and Cor 6.4 needs only ‘a MacLane chain’, not optimality.”

   Classification: MINOR — OVERCONSUMPTION.

   Precise failure: [Q10] requires a chain “as in (4),” while the note itself identifies display (4) with an optimal MacLane chain. Thus the quoted statement does not justify the broader claim that an arbitrary, nonoptimal chain suffices. This does not damage the present application: S4 expressly assumes the chain is optimal and records \(\deg x<\deg\Phi'<\deg\Phi_2\).

2. Verbatim quote: “so digit(\(Q_0\)) = digit(\(G\)) = res(\(\hat z(x_0)\))·res((\(N^d/M\))(\(x_0\)))”

   Classification: MINOR.

   Precise failure: `digit` was defined in S5.1 for \(\Phi_2\)-free elements of degree \(<m_3\), whereas \(G=\hat zN^d\) need not satisfy either condition; for \(d\ge2\), its degree can exceed \(m_3\). The argument remains valid if “digit(\(G\))” is read merely as shorthand for the explicitly displayed normalized evaluation residue \( \operatorname{res}(G(x_0)/M(x_0))\). No use of B-1 is made on \(G\).

3. Verbatim quote: “**Proof.** Write α := e₃f₃(w₃... (FGMN: α = e_r f(w_r + λ_r)”

   Classification: MINOR.

   Precise failure: the first definition of \(\alpha\) is syntactically truncated. The parenthetical immediately supplies the intended expression
   \[
   \alpha=e_3f_3(w_3+\lambda_3),
   \]
   and every subsequent calculation uses that expression, so the defect is typographical rather than logical.

4. Verbatim quote: “\(R_2(\Phi_3)=\psi_2^{\ell_3}\)” together with “clause (c) in the twist-aware form.”

   Classification: MINOR.

   Precise failure: the same symbol \(\psi_2\) is used for both the FGMN minimal polynomial of \(z_2\) and the repo minimal polynomial of \(\eta_2\), although the note establishes that these can differ by a \(z_1\)-twist. For example, at the disclosed LP1 configuration \(z_2=1\) and \(\eta_2=z_1\ne1\), their linear minimal polynomials over the relevant coefficient field are different. The proof and consumption note correctly use the FGMN polynomial in the displayed residual equality and translate the repo letter through the single embedding, so this is notation hygiene, not a false consumed inference.

CHECKED CLEAN — B″ step (i): every peel can be oriented with the split-off \(N\) or \(\hat z\) as the second factor; its grade is respectively \(\bar\kappa\) or \(0\), both in \(\Gamma_2\), while the remaining product has the complementary exact grade.

CHECKED CLEAN — B″ step (ii): valuation multiplicativity gives
\[
\nu(G)=0+d\bar\kappa=d\,u_3/e(\mu_2)=\beta_t,
\]
and Def. 1.8 then gives the asserted minimum over the \(\Phi_2\)-adic terms.

CHECKED CLEAN — B″ step (iii), divisibility: the normalized data make the class of \(\lambda_3\) have exact order \(e_3\) modulo \(\Gamma_2\); hence equality with \(\beta_t\in\Gamma_2\) forces \(e_3\mid j\).

CHECKED CLEAN — B″ step (iii), residual degree: when \(e_3\mid j\), the grade of \(\Phi_2^j\) lies in \(\Gamma_2\), Cor. 4.7(2) applies, and eq. (14) places the contribution at \(y^{j/e_3}\), never at degree zero for \(j\ge1\).

CHECKED CLEAN — B″ step (iv): \(\deg Q_0<m_3\); the normalized evaluation equals \(1\), so B-1 establishes \(\nu(Q_0)=\beta_t\) before B′(3) is invoked. There is no circularity.

CHECKED CLEAN — γ-calculus: reduction modulo \(e_2\) forces \(e_2\mid b\); division by \(\gamma_2^{b/e_2}\), followed by reduction modulo \(e_1\), forces the remaining \(x,\pi\)-monomial to be a power of \(\gamma_1\).

CHECKED CLEAN — \(\vartheta(f_3-1)=1\): here \(d=1\), so the defining quotient is \(N/N\).

CHECKED CLEAN — Cor. 6.4 non-equivalence: both \(\Phi_3\) and \(\Phi_2\) are in \(KP(\nu)\), while \(R_3(\Phi_3)=\psi_3\ne1=R_3(\Phi_2)\); Proposition 5.7 therefore applies exactly.

CHECKED CLEAN — Theorem 6.3 roles: throughout S4, \(F=\phi=\Phi_3\), \(\mu=\nu\); no later argument silently places \(\Phi_3\) in the key-polynomial role for another valuation.

CHECKED CLEAN — chain hypothesis at the actual use-site: optimality is explicitly assumed through the strict degree chain; the earlier stages belong to the given proper tower setting.

CHECKED CLEAN — clause (d): Cor. 6.4 directly gives \(\nu(\phi_i)=v(\phi_i(\xi))\), and the conversions \(u_2/e(\mu_2)\) and \(\kappa_3/e(\mu_2)\) follow from the displayed definitions.

CHECKED CLEAN — admissibility: \(w^{f_3}\psi_3(y/w)\) is monic of degree \(f_3\), has nonzero constant \(w^{f_3}\psi_3(0)\), and is irreducible because variable scaling and multiplication by a unit are automorphisms up to associates.

CHECKED CLEAN — prescription algebra:
\[
y^{f_3}-\sum_t\vartheta(t)w^{f_3-t}\vartheta(t)^{-1}a_ty^t
=w^{f_3}\psi_3(y/w).
\]

CHECKED CLEAN — substitution into GENTOW2-A: the theorem is universally parameterized by its admissible residual, and the note explicitly consumes it with the formal parameter instantiated as \(\psi_3^{(w)}\).

CHECKED CLEAN — correction-term B-law: the grades add to \(\alpha\), and eq. (14) gives \(y^{e_3t/e_3}=y^t\).

CHECKED CLEAN — degree-forcing argument: \(\deg\Phi_3\ge s'm_3\), Cor. 4.4 gives \(s'-s=e_3\deg\psi_3\), and equality at both ends forces \(s=0\) and \(\deg\Phi_3=s'm_3\).

CHECKED CLEAN — on-line height:
\[
\beta_t+e_3t(w_3+\lambda_3)
=e_3(f_3-t)(w_3+\lambda_3)+e_3t(w_3+\lambda_3)=\alpha.
\]

CHECKED CLEAN — passage from \(R_{3,\alpha}\) to \(R_3\): the nonzero constant coefficient makes the initial abscissa \(j_0=0\), exactly the condition cited from Def. 3.18.

CHECKED CLEAN — honesty-box scope: the refuted on-the-nose B-2 assertion is not used in the repaired proof; the load-bearing dependencies are B′(3), B″, and the independently re-derived Cor. 4.7 sum.

CHECKED CLEAN — S7 consumption: only admissibility, intermediate one-sidedness, the translated residual-root statement, and exact intermediate values are consumed; none requires \(w=1\) or a naked coefficient string.

CHECKED CLEAN — LD3: \(f_3=1\) leaves only \(t=0\), hence \(d=1\) and \(\vartheta(0)=1\).

The four findings are confined to an unsupported non-load-bearing generalization, two notation/scope blemishes, and one malformed display. The FGMN hypotheses hold at the actual invocation, B″’s grade bookkeeping and noncircular exactness argument are sound, and the \(w\)-substitution preserves precisely the properties required downstream. No justification gap or critical error remains.

OUTCOME: RATIFIED-WITH-ANNEX
```

---

## S7. REPAIR-COMPLETION RECORD (2026-08-10, appended by the TOWERRAT
## REPAIR unit — per-finding outcome)

All three legs executed as dated appends/corrections on the FROZEN
notes (pure-append verified by prefix md5 before each commit; statement
displays byte-untouched; the appends govern their quoted sentences).
Re-derivation discipline held: every repair derived from the notes' own
lemmas + the frozen primary sources (HE7 §S1/§S5.3, GENHN/T(b)′, FGMN),
none transcribed from the verifier's text.

**HETOW (TOWERRAT-R1 + F-2 + F-3) — commits 3f23b88 (seal) / 9ee7c92
(verdict) / 7fb8823 (append).**
- **F-1 → REPAIRED (the substantive charge).** LEMMA HETOW-4 (the
  normalizer bridge) PROVED as a dated append: (a) n̂₂(k)/n₂(k) =
  n̂(m(k))/ϖ^{m(k)} = (x^{e₁}/π^h)^{−Q(m(k))}, residue the wrap letter
  τ(k) = η^{−Q(m(k))} ∈ K^×; (b) τ is a two-floor cocycle, NOT a
  character — the honest answer to "does the twist cancel?": NOT per
  height (the raw pin-residue strings differ, non-geometrically —
  tooth T-RAW machine-fired at frames X and Z); (c) the ASSEMBLED
  residuals (each with its own cocycle bracket, HE7 §S5.3 Step 2 /
  GENTOW-2(iv)) telescope to R = τ(H₀)·R̂(Z/δ), δ = τ(u₃) — a global
  unit × K^×-rescale, the J-D0-covered species; (d) both routing
  predicates of HE7.A(2)/(3) and the α-refine chain transport
  (s₂ = δŝ₂; one w serves both systems). The §S6 gap annotation on
  HETOW.A(i)'s final clause is DISCHARGED at the note's grade.
  Machine: sealed `hetow_r2_hetow4.py` GREEN — 203 checks, 37 dual-
  route gp jobs, 0 violations at frames X, Z (η-letter live) and S
  (e₂ = 2, bracket live: c_1 = 1 rows; HALF43 letter-live τ(43) = 2);
  sealed-instrument isolation re-run first: `hetowr1_supp.py` 29 jobs
  / 0 violations, output content-identical modulo the runtime stamp,
  results.json md5 58f1ce0c unchanged.
- **F-2 → REPAIRED (display).** The GENTOW1-Step-4 all-roots
  transport cite attached at HETOW-3(b)'s use site (same append).
- **F-3 → REPAIRED (annotation).** The S1 level-1 frame row annotated:
  monic + disc ≠ 0 = inherited T(b)′ frame data; the ✓ scoped to
  Φ′ ∤ f (same append).

**GENTOW1 (TOWERRAT-R2a/b/c + F-4) — commits 28f0bf3 (supplement) /
4caf0fb (corrections).**
- **R2a → REPAIRED.** GENTOW-1(b)'s display of record gains the clip
  Σ max(0, N − floor); GENTOW-5(e)'s exactness re-scoped to it.
  Verified at the challenge instance (floors (9,7,5,3); N = 1: sealed
  −20 vs true 0 free digits, box = 1 string) AND at battery rows
  FAM-A5 + FAM-B (floor tables re-derived = the committed S1 tables;
  clip inactive at N ≥ max floor, values unchanged).
- **R2b → REPAIRED.** DOM_N / COD_N defined with the shared clipped
  counting formula q^{Σ max(0, N − floor_λ)}; equal-cardinality lemma
  stated properly (fixed prescriptions ≠ free digits; height-
  preserving triangular injection; inverse limit over windows).
  Machine: ONTO verified by EXACT ENUMERATION at the A5-R1 battery
  row (λ = 13, N = 4): 16 event members → 16 distinct images = the
  full λ-floored box.
- **R2c → REPAIRED.** GENTOW-5(a) restated THREE-BAND (below cap:
  stable; at cap: value exact / K₂-residue undetermined at f₁f₂ ≥ 2;
  above: unstable; "undercutting ≥ cap" re-scoped strict — ties at
  equality). Each band machine-checked at FAM-B (N = 4, cap 8): band
  1 value 7 stable across 6 lifts (slot-arith + PARI); band 2 value
  8 = cap exact across 6 lifts with the (0,0)-flavor digit flipping
  between two lifts — the sealed iff's counter-instance live; band 3
  values 14 vs 11. Runner `gentow1_r2_units.py` GREEN 41 checks / 14
  gp jobs / 0 violations.
- **F-4 → REPAIRED.** "constant term untouched" → the constant term's
  x-side digit (the change sits strictly above the x-side; B-R2's own
  −16 shift displayed).

**GENTOW2 (TOWERRAT-R3, hygiene batch) — commit 33f8620.**
- **F-1 → REPAIRED:** the "not optimality" clause STRUCK ([Q10] asks
  for a chain "as in (4)" = the optimal chain; the audit row itself
  derives optimality).
- **F-2 → REPAIRED:** digit(G) fenced to res(G(x₀)/M(x₀)) at B″(iv);
  B-1/B′(3) applied only to Q₀ (in scope).
- **F-3 → REPAIRED:** the truncated α display completed:
  α := e₃f₃(w₃ + λ₃).
- **F-4 → REPAIRED:** ψ₂^{FGMN} = minpoly(z₂) vs ψ₂^{repo} =
  minpoly(η₂) disambiguation line, fencing the two S4 sites.

Acceptance state after the batch: all three notes remain ACCEPTED 2/2;
HETOW's challenge annotation is now DISCHARGED-at-grade by HETOW-4;
GENTOW1's three GAP-with-repair items and GENTOW2's four annex items
are closed as above. Every repair verified pure-append (prefix md5s
e27b97f2 / 254d1765 / 29908cb4 re-checked post-append).
