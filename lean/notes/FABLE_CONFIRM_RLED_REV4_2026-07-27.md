# FABLE CONFIRMING PASS — §R-LEDGER rev 4 (2026-07-27)

Verifier: fresh Fable instance, confirming half of the dual-acceptance shot
(Codex runs in parallel on identical text). Text: MOVES_2026-07-24.md
§R-LEDGER (lines ~9297–9760, rev 4). Predecessor: FABLE_VERIFY_RLED
_2026-07-27.md (rev 3: 0 crit / 3 gaps + 2 WATCH). Charge: (a) verify the
rev-4 repairs; (b) confirming sweep at fresh emphasis (REL.2(d) square,
(g1)–(g7) coherence, REL.1 walk-order vs §C structure); (c) own
computation check (/tmp/rled_confirm_rev4.py).

## Verdict summary

NOT CLEAN at the letter: 0 critical / 1 wording gap (G1: the shallow
"(law holds)" label inside (EQ-2)'s rev-4 worked display contradicts the
pin's own not-well-posed-at-split-positions clause — a one-clause repair)
+ 2 spec-sheet NOTES on REL-n4 (fenced, not defects) + 1 recommendation
(REL.1 walk order). All three rev-4 repairs are otherwise genuine; the
displayed split instance matches the predecessor's computation exactly
(recomputed independently, §E).

## A. Rev-4 repair verification (F1, F2, F3, WATCH)

F1 [PASS]. (a2) now reads "EXPECTED from the tower data, walked in (a)'s
pass, not asserted here", with "E := ∏_r e_r and F := ∏_r g_r" bound to
C.0's SHAPE fields and the whole divisibility in subjunctive mood ("the
saturation identity ... would give E·F ∣ d_j"). E, F bound as demanded;
the mood fences it. Arithmetic sound: d_j = E·F·μ ⇒ E·F ∣ d_j, and
E·F ∣ d_j ⇒ F = δ_j^rel ∣ d_j, giving (a2)'s integrality. Exactly the
predecessor's prescribed repair shape.

F2 [PASS]. R.0 head now scoped: "unramified base change leaves the
AMBIENT v_p-scale untouched", with "MOVES height bookkeeping (side
heights, stretches, κ_r) is NOT asserted here" and an explicit pointer to
(R0-tower)'s PREDICTED bracket, which exists two paragraphs down. The
strong reading is dead; the assertion/fence duplication is gone.

F3 [PASS with residue G1]. The comparison domain is pinned PER POSITION
CLASS: the a_δ = δ·a law now quantifies over "a fixed shape position
WHOSE SPECIES IS δ-STABLE", split positions declared "NOT well-posed",
and REL-n4's exponent test inherits the pin (R.4's rev-4 note).
FALSIFIER, restated — now stable: exhibit δ ≥ 2 and a shape position
whose species letter (stage tuple (e,h,g,μ) + side data, per (EQ-1))
persists under re-basing, at which either a re-based piece map fails
F_δ-linearity or the F_p-additive-span dimension a_δ ≠ δ·a. Split
positions can no longer be adjudicated either way — they are excluded by
the domain clause, not by a reading choice. δ-stability is checkable from
the two towers directly (concrete tuples), so the falsifier is executable
even while (a6)'s matching dictionary is owed. The displayed instance
(shallow a=1 → a_δ=2; full a=2 → per-branch 𝔸_δ=F₉, a_δ=2 ≠ 4) matches
the predecessor's §C computation exactly and my recomputation (§E).

G1 [GAP — wording, one clause]. In the same display, "the shallow
position a = 1 gives a_δ = 2 = δ·a (law holds)". But the split of
ψ = z²+1 changes the species letter (g: 2→1) at BOTH positions of this
instance, so by the pin's own clause the shallow comparison is equally
"NOT well-posed" — yet it is performed and labeled "law holds" while the
sibling clause "the species did not persist, so the position is OUTSIDE
the pinned domain" is applied only to the full position. The
predecessor's C-1 carried exactly this caveat ("holds at a node of
DIFFERENT SHAPE ... reached only through the (owed) read dictionary");
rev-4's compression dropped it. As written a fresh reader takes the
shallow half as an in-domain confirming instance, which the pin denies.
Also weakly re-punctures R.5's re-sharpened "LITERALLY true of every
display": "(law holds)" is an indicative label not adjudicable under the
note's own domain pin. REPAIR SHAPE: relabel the shallow half, e.g.
"(exponent equality holds numerically, though this position's species
also changed — out of domain; the coincidence: the re-based computation
never forms the decomposing tensor)".

WATCH ledger [PASS]. R.5's CROSS-NOTE WATCH records (W1) realizes-T_j
prefix-vs-fiber with the definition duty at §T.3/[1] and (e3)/(SIB-Oδ)
inheriting the pinned reading, and (W2) the ABSOLUTE annotation owed to
§T.3 — both faithful to the predecessor's B(e-ii) and D items, both
correctly typed as owed elsewhere, no edit to the dual-accepted §T.

## B. Fresh sweep 1 — REL.2(d)'s commutative square

Well-posedness as an ACCEPTANCE CRITERION: PASS. Four vertices typed
(continuation data on Σ_c; O_{δ_j} box; continuation subtree of
T_can(f); T_can^{O_{δ_j}}(Θ_j(·))); horizontals are Θ_j ((a4)) and the
node-data correspondence; verticals (f ↦ its subtree, g ↦ T_can(g)) are
implicit but forced — and (d) is fenced "well-posed only AFTER
(a1)–(a6)", so the pass must display them. Left vertical constant-prefix
issue closed by Σ_c fixing the prefix. Key check: the correspondence
cites "(EQ-2)'s alphabets" — this consumes (EQ-2)'s UNCONDITIONAL
definition layer (re-based spans exist at every position, split or not),
NOT the pinned a_δ = δ·a law, so rev-4's domain pin does not narrow
(d)'s scope. Without (d), (SIB-Oδ) ill-typed — the dependency is stated.

## C. Fresh sweep 2 — REL-n4 (g1)–(g7) internal coherence

Coherent as an outline: two levels N₀ (conditioning, g1) vs N (census,
g4) kept distinct; (g5)'s function-of-factor-data restriction is what
lets side (i) alone carry the (retyped, decision-level) independence
claim; (g7)'s SPEC-FAIL default composes with (g4); side (i)'s 2^{4N}
count matches (R0-box) at p=2, n=4; side (ii) honestly retyped internal.
Two NOTES for the owed spec sheet (fenced — "RUNNABLE SPEC OWED" — so
not defects):
 (N1) MULTIPLICITY μ UNPINNED. "Root reads whose residual factor is an
   irreducible quadratic over F₂" does not pin μ. At μ=1 the cluster has
   d_j = 2, d_j^rel = 1 — a degree-1 box over W(F₄) with NO refinement:
   the "conditional refinement law of that quadratic cluster" is trivial
   there. The gate's substance is the μ=2 stratum (f̄ = φ̄², d_j^rel = 2,
   genuine split/inert/ramified families). (g1)/(g2) must pin μ or
   display the trivial μ=1 family explicitly.
 (N2) IN-DOMAIN EXPONENT INSTANCES MAY BE EMPTY. The unique irreducible
   monic quadratic over F₂ is z²+z+1, and it SPLITS over F₄ (checked,
   §E) — the base-change stage itself is a split position. Whether ANY
   refinement position in the gate's scope is δ-stable (so that rev-4's
   inherited domain admits an exponent-comparison instance at all) is a
   (g2) family-list question; if none, the exponent leg of the seal is
   vacuous and the gate tests masses only. Worth one line in the spec.

## D. Fresh sweep 3 — REL.1 walk order vs §C's statement heads

§C rev-14 statement heads enumerated: move-map Lemma, C.1.0, DOM, LST,
TYP, C.1, C.1.5/(ZC), Theorem C (+ C.0/C.0.5 conventions, C.3 via
scope head). Walk items (i)–(iv) cover TYP(a), Fact A/B + C.0.5 +
PIN-WELLDEF, C.0 BLOCK CONVENTION, D.3(e)(i)/D.11. NOT in the order:
C.1, C.1.0, C.1.5/(ZC), LST, DOM, C.3. NO CLAIM VIOLATED — the list is
a priority order ("the one flagged hiding spot FIRST", matching the
plan's §3r charge), and the completeness burden sits on the pass itself
("listing every step that touches the base"). C.1.5's fresh-digit
counts route through (iv)'s D.11-nominal cardinalities by reference.
RECOMMENDATION (not a gap): C.1's clause-species selection consumes
residual-polynomial IRREDUCIBILITY over the residue field — named in
REL.1's own reconstructed-objects list — yet sits in no walk item; add
it (say as (v)) at the next revision. LST/DOM expected base-free
(valuation geometry / floor inequalities), fine as unlisted.

## D. Fresh sweep 3 — REL.1 walk order vs §C's statement heads

## E. Own-construction check

/tmp/rled_confirm_rev4.py (exact arithmetic, pure python), all pass:
z²+1 rootless over F₃ (irreducible), roots (0,±1) in F₉ (splits);
shallow span dims a=1, a_δ=2 = δ·a; full a=2, a_δ=2 ≠ δ·a=4 — the
(EQ-2) display's numbers confirmed against both the text and the
predecessor's §C. REL-n4 side: (b,c)=(1,1) the unique irreducible monic
quadratic over F₂; roots ω, ω+1 in F₄ (splits — N2's witness). (a2)
divisibility d_j = E·F·μ ⇒ E·F ∣ d_j checked over a grid.

## Final verdict

0 critical / 1 gap (G1, one-clause wording) + 2 REL-n4 spec-sheet notes
(N1 μ-pin, N2 possible vacuity of the exponent leg — both inside the
"spec owed" fence) + 1 walk-order recommendation. Repairs F1/F2/WATCH
genuine; F3's pin makes (EQ-2) refutation-stable, with G1 the sole
residue of its worked display. NOT CLEAN at the letter of the dual bar;
nothing blocks the ledger's function; a rev-5 relabel of the shallow
half of (EQ-2)'s instance (and optionally N1/N2 lines in R.4) should be
minutes, after which this verifier's list is exhausted.
