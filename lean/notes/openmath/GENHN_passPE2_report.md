# GENHN passPE2 — second hostile pass (2026-08-09, at r2 HEAD)

**VERDICT: NOT CLEAN — 0 CRITICAL + 2 GAP + 2 MINOR. The clean count
stays 0/2.** The r2's new mathematics HOLDS everywhere this pass
could reach it: LEMMA GENHN-T(b)′'s clauses (i)–(iv) were re-derived
by hand and survived every constructed attack, and a fresh
instrument (`genhn_pe2_fresh.py`, GREEN 219 checks / 0 violations,
4 teeth) confirms the composed carrier at the [r1]-floor boundary,
the slot lemma's exactness DIRECTLY (72 nfeltval legs — first direct
(ii) contact), and the never-before-tested (iii) dictionary branches
(first 2-stage composed-INERT/2SIDED/SPLIT, first outer-f₁ = 2 tower
genres, the η₂-cocycle division adjudicated by PARI, first
non-prime-q tower contact at Q = 4 — 4/4 exact at absolute degree
16). The two GAPs are both COVERAGE defects of the r2 *displays*,
not of the lemma: (G1) the depth-≥ 3 iterated key composition
(first live n = 16) is neither proved by the one-step T(b)′ nor
named among [GENHN-TOW-1]'s five items, yet GENHN.B's corrected
conditionality claims the amended list is correct at n ≥ 8; (G2)
GENHN.B's (CS-3) rider extends T(b)′(iii) to "every tower leaf with
inner μ₂ = 2", but (iii) is proved for FULL inner sides only —
partial-side μ₂ = 2 leaves are first live at n = 10 and sit in the
box's own item (4) (a constructed n = 10 member exhibits the case).
Target: `lean/notes/openmath/GENHN_PROOF_2026-08-08.md` at HEAD
(r2 = d16869c/7650b20/438608a/9636b7e; machine leg 7b504ba).

## FINDINGS

### F1 — GAP. Depth-≥ 3 iterated key composition (first live n = 16)
### is neither proved by T(b)′ nor named in [GENHN-TOW-1]; GENHN.B's
### "correct for the amended list" over-reaches at n ≥ 16.

**Quoted claims.** GENHN.B [r2] (S1): "at n ≥ 8 P(n) rests on
{[GENHN-HE(μ ≥ 3)]} ∪ {[GENHN-TOW-1] (S9.1: composed entry budgets,
inner refine transfer, faithfulness geography, partial inner sides,
composed window ledger)} ∪ {S9 boxes} ∪ {arc stack} ... The sealed
word 'EXACTLY' was FALSE at n ≥ 8 (passPE1 F1); it is correct for
the amended list." The box (S9.1) enumerates exactly five open
items; none is the ITERATED composition.

**The defect.** T(b)′'s setting and proof are ONE composition step:
the outer key Φ′ must carry S3.1's invariants (one-sided x-polygon
of slope h/e₁ with IRREDUCIBLE residual ψ; normalizer MONOMIALS
n̂(m) = x^i π^a, i < e₁). The composed key Φ₂ fails both re-entry
conditions: its x-polygon residual is the POWER ψ^{e₂f₂} (proof of
(i)), and normalizers on the dv₂-ladder are polynomials in Φ′ —
the supp runner's own 3-stage construction uses n₂(21) = 16·Φ′
(`genhnr2_supp.py` L388–389), outside the displayed normalizer
form. So T(b)′ does not self-apply, and a third-level CS event
(inner μ₂ ≥ 4, forced μ₁ ≥ e₂f₂μ₂ ≥ 8, hence n ≥ 16 — the note's
own R1 arithmetic) has no proved or boxed carrier/slot/read: the
level-2→3 analogue of the withdrawn "no new mechanism: GENHN.A
applied inside its own stages" recurs one level up, unaddressed.
The supp leg's three n = 16 instances matched PARI (so no
refutation — this is a justification/coverage gap, not an error),
but they are parse-gated instances of an UNSTATED lemma.

**Failure scenario.** A density assembly at n = 16 prices a
3-stage genre through GENHN.B's tower clause; every displayed
authority (T(b)′ + the five TOW-1 items) is silent on the
Φ₃-carrier and dv₃-slot exactness, so the assembly either stalls
or silently reuses the stage-shadow pattern PE1 refuted at level
1→2. Scope: n ∈ {8, ..., 15} is UNAFFECTED (depth-3 needs μ₁ ≥ 8,
n ≥ 16); the cure is one new box item (or a T(b)″ iteration
lemma) plus a scope word in the GENHN.B display.

### F2 — GAP. GENHN.B's (CS-3) rider over-covers: T(b)′(iii) is
### proved for FULL inner sides only, but the rider claims every
### tower leaf with inner μ₂ = 2 (partial sides first live n = 10).

**Quoted claim.** GENHN.B [r2] (S1): "(CS-3) holds at every μ = 2
genre (THEOREM GENHN.C [r2: and at every tower leaf with inner
μ₂ = 2 by GENHN-T(b)′(iii); inner μ₂ ≥ 3 sits in [GENHN-HE]])."
But T(b)′'s setting: "e₂f₂μ₂ = μ₁ (FULL inner side — the first-live
shape; partial sides sit in [GENHN-TOW-1])", and its (iii) requires
deg f = μ₂D₂ with C_{μ₂} = 1.

**The defect + constructed witness.** A partial inner side with an
inner CS event needs e₂f₂μ₂ < μ₁ with e₂f₂ ≥ 2, μ₂ ≥ 2, so
μ₁ ≥ 5 and n ≥ 10 — live BELOW nothing the r2 proof covers. This
pass constructed one (PE2-P): n = 10, genre (2,1,5) over ℚ₂,
f = Φ′⁵ + 4Φ′⁴ + 32Φ′ + 64x (Φ′ = x²−2) — level-1 polygon
(0,13)–(1,10)–(5,0), a slope-3 sibling side plus a slope-5/2
inner side of length 4 < μ₁ = 5 carrying (T+1)², i.e. an inner
μ₂ = 2 event on a PARTIAL side. It is a "tower leaf with inner
μ₂ = 2" in the note's vocabulary, (iii) does not apply (the
Φ₂-development of the degree-10 f is not monic-of-length-μ₂ — the
corrected reader refuses it, verified), and no proved display
prices its σ (PARI: {(2,1),(4,1),(4,1)} — sibling × tower part;
disc ≠ 0). MITIGATION (why not CRITICAL): the failure is LOUD, not
silent — (iii)'s hypotheses visibly fail, no wrong σ is emitted —
and the surrounding conditionality display is protected because
[GENHN-TOW-1] item (4) names partial sides. The defective sentence
is the (CS-3) parenthetical itself, which a GENHN.B consumer at
n ≥ 10 would cite as a proved σ-decision. Cure: one scope
parenthetical ("full inner side; partial sides via TOW-1(4)").

### F3 — MINOR. The [r2] budget erratum's f₁ ≥ 2 magnitude
### parenthetical has the wrong sign (the old base UNDERSHOOTS at
### f₁ ≥ 2, μ−j ≥ 2; it does not "exceed by more").

**Quoted claim** (S3.2 [r2] erratum): "The old base
(μ−j)h + (e₁−i)h/e₁ = ((μ−j+1)e₁ − i)h/e₁ is the side height ONE
KEY-DEGREE too high: at f₁ = 1 (D′ = e₁) it exceeds the truth by
exactly h at every slot; at f₁ ≥ 2 by more
((μ−j)e₁(f₁−1)h/e₁ + h)."

**The arithmetic.** old − correct = ((μ−j+1)e₁ − i)h/e₁ −
((μ−j)e₁f₁ − i)h/e₁ = h·(1 − (μ−j)(f₁−1)). At f₁ = 1 this is +h
(the erratum's f₁ = 1 clause is right). At f₁ ≥ 2 it is ≤ 0 for
μ−j ≥ 1 — the old base COINCIDES at μ−j = 1, f₁ = 2 and
UNDERSHOOTS for (μ−j)(f₁−1) ≥ 2. Instance (genre F = (1,2,2),
h = 1, j = 0, i = 0): old base 3h = 3 < correct base 4h = 4. The
quoted magnitude ((μ−j)(f₁−1)h + h) matches neither sign nor
size (true gap: (μ−j)(f₁−1)h − h). Same-block symptom: the NODE
counterfactual "from the OLD floors it would compute
(μ−j)S + h + 1-ish" — the old-floor node computes to
(μ−j)S + S + 1 (checked at e₁ = 2, h = 1); the "-ish" hedge and
the counterfactual's role (contradicting battery rows — still
true) keep this a symptom, not a separate finding. Display-scope:
the CORRECTED formula itself is right (re-derived at E3, E31,
GENH4-E, and freshly at genre F; the erratum's three instance
checks verified), and the consumption audit holds (grep: the old
formula appears only at the tagged sites L496/L530/L580/L592/L622,
each inside a tagged display or the erratum itself).

### F4 — MINOR. T(b)′(iv)'s divergence tally "supp sweep: 35/38
### rows diverge at pin level" counts 3 structurally-excluded rows
### in its denominator.

The supp runner compares stage-vs-corrected pins only on the 35
non-SUPP-C rows (the three 3-stage rows have no stage read —
`continue` at the divergence tally); ALL 35 comparable rows
diverged. "35/38" (transcribed from the output line's "(of 38
tower rows)") reads as if 3 rows agreed; the honest fraction on
the compared set is 35/35. Strengthens, not weakens, "fails
generically at leaf depth" — but the denominator should be 35.

## CLEAN CHARGES (attacked and held)

(section filled below)

## MACHINE LEG (integrity) + FRESH ROUTE

(section filled below)

## GRADE LINE

(section filled below)
