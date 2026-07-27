# FABLE FRESH-INSTANCE VERIFICATION — §R-LEDGER rev 3 (2026-07-27)

Verifier: fresh Fable instance (dual bar, Codex side already accepted at passes 3+4).
Text: lean/notes/MOVES_2026-07-24.md §R-LEDGER (lines ~9297–9715, rev 3).
Charge: quote-and-classify, fix nothing; banner audit hardest; ambiguity
construction on REL.2(b)/(e); worked alphabet example at δ=2; §T.5 cross-check.

## Verdict summary
NOT CLEAN: 0 critical / 3 gaps (F1 the E·F∣d_j unfenced parenthetical;
F2 the R.0 "heights untouched" strong reading; F3 (EQ-2)'s prediction not
refutation-stable at split positions) + 2 cross-note WATCH items. Banner
survives at derivation granularity; the "literally every display"
sharpening does not. Full findings in sections A–E below.

## A. Honesty-banner audit (R.5 "DERIVED IN THIS NOTE: nothing")

## B. Ambiguity constructions — REL.2(b) and REL.2(e)

## C. Worked alphabet example (δ = 2, F₃-line in F₉)

## D. (SIB-Oδ) vs §T-ASSEMBLY §T.5 cross-check

## E. Fresh sweep (verifier's own emphasis)

### A. Banner audit — full assertion inventory under "derives nothing"

Swept every indicative-mood mathematical claim. Standard-algebra imports
(uniformizer of W(F_{p^δ}) is p; subfield lattice of F̄_p / (O_δ)_{δ′} =
O_{δδ′}; unramified-over-unramified; F_{p^k}⊗F_{p^δ} decomposition; "digit
cylinders generate"; p^{δ_j} = q_δ^{δ_j^rel}) — citable textbook facts or
arithmetic, not MOVES derivations: PASS. Conditional compositions (R.2's
closing β-paragraph; (SIB-Oδ)) carry explicit GIVEN/FENCED tags: PASS.
Residues found:

FINDING 1 [GAP — banner residue, same class as pass-2 crit 1]. (REL.2a)(a2)
parenthetical: "integrality of d_j^rel is part of the obligation — the
tower data give E·F ∣ d_j". The clause after the dash is an unfenced
indicative assertion of a divisibility fact, derived nowhere and cited
nowhere; moreover E and F are UNDEFINED in §R-LEDGER (imported Montes
notation, never bound here). The obligation head keeps the burden, and
nothing downstream consumes the parenthetical, so no chain breaks — but
R.5's "LITERALLY true of every display" is punctured by it. Repair shape:
retype "expected from the tower data (E·F ∣ d_j, walked in (a)'s pass)" or
delete; bind E, F.

FINDING 2 [GAP — two-reading wording]. R.0 head: "unramified base change
leaves levels, heights, and the v_p-scale untouched". Weak reading (the
AMBIENT valuation: value group ℤ, uniformizer p) is standard and fine.
Strong reading — MOVES height bookkeeping (side heights, stretches, κ_r)
unchanged — is exactly what (R0-tower) two paragraphs later fences as
PREDICTED ("walked in REL.1's pass, not asserted here"). "Heights" is a
term of art in this ledger, so the strong reading is live; as written the
head sentence asserts what the tower clause fences. Repair shape: scope to
"the ambient v_p-scale"; leave MOVES heights to the PREDICTED clause.

FINDING 3 [GAP — refutation-stability of (EQ-2)'s open prediction; the
substantive fresh-eyes catch, developed in §C below]. The prediction
"a_δ = δ·a, i.e. |𝔸_δ| = q_δ^a = |𝔸|^δ" compares the re-based exponent at
"a shape position" with the OLD exponent a at (implicitly) the matched
position — but the note itself states (R0-reads, rev-3 repair) that there
is "no canonical inclusion" and the re-based tower is rebuilt afresh. At a
node whose residual factor SPLITS under re-basing, the old position has NO
shape-matching counterpart (g drops), so two readings of the prediction
disagree on concrete instances (worked example in §C: a candidate
a_δ = 2 ≠ δ·a = 4 instance that the vacuous-at-split reading dismisses).
As stated the prediction is not refutation-stable: a REL-n4 exponent
mismatch at a split node could be adjudicated either way. Repair shape:
one sentence pinning the comparison's domain — either "at positions whose
species persists under re-basing, per (a6)/(EQ-1)'s dictionary (owed)" or
"per-digit-factor exponents along matched READS, not positions". Note
REL-n4 "tests (EQ-2)'s exponents", so (g2)/(g5)'s spec inherits this
until pinned. GAP not CRIT: the law is OPEN and walk item (iv) + (a6)
must produce the dictionary anyway; no downstream display consumes the
law unconditionally.

Banner verdict: the global "DERIVED IN THIS NOTE: nothing" survives at
derivation granularity — no smuggled derivation chain found (nothing is
proved from anything). The "LITERALLY true of every display" sharpening
does not survive Finding 1, and Finding 2's strong reading is an
assertion-shaped duplicate of a fenced clause.

### B. Ambiguity constructions — REL.2(b) and REL.2(e)

REL.2(b), attempted splits (construct two readings that disagree):
 (b-i) Marginal vs joint: could "(b) done" mean per-branch marginal only,
   or joint across siblings (smuggling independence)? RESOLVED by the
   display itself — μ(Θ_j⁻¹(W)│Σ_c) = vol(W) involves one branch's Θ_j;
   independence is visibly (c)/(SIB)'s, re-homed. No disagreement case.
 (b-ii) Full box vs constrained sub-box: if Θ_j's image were a proper
   sub-box (e.g. reductions constrained), "pushforward = box measure"
   reads differently normalized. RESOLVED by (a2) + (R0-box): the target
   is THE monic degree-d_j^rel coefficient box, vol normalized to 1 —
   full-box reading pinned; a constrained image would REFUTE (b), which
   is the desired refutability. No disagreement case.
 (b-iii) f-dependent coordinate lists: if the free coordinates on Σ_c
   vary with f, (a1)'s "measurable product" has no single domain and
   Θ_j⁻¹(W) forks. NOT resolved by (b) itself but honestly deferred:
   (b) is "stated RELATIVE to (a1)–(a4), which supply its domain and
   target" — the fork must be closed by (a1)'s pass, and (b)'s own
   fencing says exactly that. Verdict: (b) genuinely refutable GIVEN
   (a1)–(a4); the note claims no more.

REL.2(e), attempted splits:
 (e-i) Subtree sharing (two prescribed T_j, one entry): CLOSED by (e5)
   explicitly (either indices determine T_j or T_j is an index). This was
   pass-2 crit 2's ambiguity; the rev-3 repair is genuine.
 (e-ii) "realizes T_j" — containment (T_j a rooted prefix of T_can) vs
   exact fiber (truncation equals T_j): the two readings give different
   masses on a concrete instance (T_j = root + one child A; g's tree has
   children A, B: containment YES, fiber NO). WHO owns it: the phrase is
   (SIB)'s quantifier, stated at §T.3 and consumed here by citation; §T.4
   TREE-EXP's "μ(fiber T │ Σ)" language indicates the EXACT-fiber reading
   there. [2r]'s fence "no re-statement of (SIB)'s product law, which
   lives at §T.3 alone" puts the definition duty at [3t]/[1]. Verdict:
   real two-reading residue, but NOT this note's defect — recorded as a
   WATCH for the CL-10 sync: (e3)'s displayed equation and (SIB-Oδ)'s
   pricing line must inherit whichever reading [1]/[3t] pin.
 (e-iii) (e2)'s exponent: absolute vs relative δ_j — CLOSED by the
   BASE-INDEX CONVENTION (all indices absolute; p^{δ_j} = q_δ^{δ_j^rel}
   displayed). No disagreement case.

### C. Worked alphabet example (δ = 2): the F₃-line in F₉, re-based

Setup (D¹¹c mechanism, p = 3 transposition of its p = 5 instance): tower
stage ψ = z² + 1, irreducible over F₃ (checked: no roots mod 3); tower
field F_{k+1} = F₉ = F₃[z̄]. Shallow height (one predecessor index
attainable, I(γ) = {0}): 𝔸 = u·F₃·z̄⁰ = an F₃-line in F₉, |𝔸| = 3, a = 1.
Computation: /tmp/rled_alpha.py (exact F₉ arithmetic, output recorded).

Re-base δ = 2 (F_δ = F₉): ψ = z² + 1 SPLITS over F₉ (roots ±i computed) —
the g = 2 stage is GONE; the re-based tower has TWO branches with linear
residual factors, each with tower field F₉ (degree 1 over the new base).
 (C-1) SHALLOW position: re-based span = u·F₉ = all of F₉; |𝔸_δ| = 9 =
   p², a_δ = 2 = δ·a. THE PREDICTED LAW HOLDS NUMERICALLY — per-digit
   factor 1/3 = p^{−a} becomes 1/9 = q_δ^{−a}, exponent preserved in base
   q_δ. But it holds at a node of DIFFERENT SHAPE (g: 2 → 1) reached only
   through the (owed) read dictionary — the gcd caveat does not bite the
   CARDINALITY here, because the re-based computation rebuilds the tower
   and never forms the decomposing tensor F₉ ⊗_{F₃} F₉ (gcd(2,2) = 2).
 (C-2) DEEP/full position (𝔸 = F₃·1 ⊕ F₃·z̄ = F₉, a = 2): each re-based
   branch's alphabet is F₉, a_δ = 2 ≠ δ·a = 4. Reading 1 (children
   correspond to the old position): REFUTES the law. Reading 2 (species
   changed, no corresponding position, prediction vacuous there): law
   untouched. This is Finding 3's concrete disagreement instance — and
   note the per-CLUSTER mass bookkeeping recombines across the two new
   branches (correctly REL.2/SIB territory, fenced).
Outcome: the gcd caveat bites POSITIONALLY (species/position matching),
never cardinality-wise in this instance; a_δ = δ·a holds where a matched
position exists and is not even well-posed where it doesn't.

### D. (SIB-Oδ) vs §T-ASSEMBLY §T.5 — exact match check

§T.5 item (5) names "[2r] REL.2(a)/(b)/(d) — the base-changed sibling
factors" and "the (SIB) statement's O_δ quantifier is consumed from
there". (SIB-Oδ) is fenced "= REL.1 + REL.2(a)+(b)+(d), composed" and
prices μ(S_j│Σ_c) as the REL.1 mass. VERDICT: MATCH on the REL.2 legs —
(a)+(b)+(d) exactly, (e) correctly absent from both (it enters only at
β-substitution/PCI, per REV 13, listed separately on both sides). REL.1
is explicit in (SIB-Oδ)'s fence but only implicit in §T.5's "per [2r]" —
a strengthening of honesty on [2r]'s side, not a mismatch ((b)'s right
side is a REL.1 mass, so REL.1 was always inside). R.2's quotation of
§T.3's quantifier is verbatim (trailing clause "where b_j's cluster has
residue degree δ_j" elided without loss). WATCH (cross-note, for the
CL-10 sync): §T.3's inline "residue degree δ_j" carries no ABSOLUTE
annotation; [2r]'s convention says consumer displays carry absolute
indices — one word owed to §T.3 at consumption, not a defect here.

### E. Fresh sweep (verifier's emphasis)

- BASE-INDEX arithmetic checked: δ_j = δ·δ_j^rel, p^{δ_j} = q_δ^{δ_j^rel},
  recursion target O_{δ_j·δ″} a literal subring chain — all consistent.
- Five-count sweep: "FIVE named obligations (a)–(e)" consistent at the
  scope head, R.1 head, R.3's CL-8 line, R.5; historical "four" marked
  superseded at each site. Pass-2 finding 3's repair is genuine.
- REL-n4 coherence: p = 2, n = 4, quadratic root cluster ⇒ d_j = 2,
  δ_j^rel = 2, d_j^rel = 1 — the W(F₄)-side is a degree-1 box; sensible.
  Side-(ii)'s INTERNAL CONSISTENCY retype and (g5)'s function-of-factor-
  data restriction are honest; (g1)–(g7) owed is correctly load-bearing.
- REL.3's deferred-statement form: genuinely empty of claims; the
  acceptance criterion (restate [4]'s displays verbatim, re-scoped) is a
  well-posed trigger. PASS.
- Consumer edges in R.5 agree with the scope head's "Consumed by" list.

## Verdict (filled)

FINDINGS: 0 critical / 3 gaps (all wording-level, one-line repairs;
Finding 3 the substantive one) + 2 cross-note WATCH items (B(e-ii)
"realizes"; D's ABSOLUTE annotation at §T.3).
BANNER: survives at derivation granularity (no smuggled derivation
chain); the rev-3 sharpening "LITERALLY true of every display" is
punctured by Finding 1's E·F ∣ d_j parenthetical.
OBLIGATION STATEMENTS: (a) checklist, (b), (d), (e1)–(e5), REL.3,
(g1)–(g7) — each provable/refutable as stated modulo its own displayed
fences; the one refutation-stability defect is (EQ-2)'s prediction
(Finding 3).
DUAL-BAR CALL: NOT CLEAN at the letter of the bar (3 gaps > 0); none
critical, none blocking the ledger's function; a rev-4 wording pass on
Findings 1–3 should be cheap and is recommended before dual acceptance
is recorded.
