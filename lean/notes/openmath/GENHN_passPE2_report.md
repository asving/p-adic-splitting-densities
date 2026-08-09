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

1. **T(b)′(i) forcing chain, at the [r1]-floor boundary.**
   Re-derived: each lift-term monomial clears Φ₂'s side with gap
   (f₂−t)(u₂ − e₂D′h)/e₁ > 0 — needing EXACTLY u₂ > e₂D′h, the
   [r1] node floor (arithmetic checked from e₁a + ih = u₂(f₂−t)
   and Φ′^{e₂t}'s side g ≥ (e₂tD′−c)h/e₁); the T-polygon step,
   gcd(u₂,e₂) = 1 exactness, and the value-group/residue forcing
   ⟨1/e₁, u₂/(e₁e₂)⟩ = (1/(e₁e₂))ℤ, [K(η₂):K] = f₂, ef ≤ D₂ all
   check. Machine (PE2-K): the five composed keys — A(u₂=5),
   A(u₂=7), B(κ₂=3), and the FIRST outer-f₁ = 2 keys F1a/F1b —
   each irreducible with (e,f) = (e₁e₂, f₁f₂) and
   v_L(Φ′(ξ)) = u₂ EXACT by nfeltval; u₂ = 5 at e₂D′h = 4 IS the
   boundary instance the dispatch asked for.
2. **T(b)′(ii) GENHN-2′ exactness.** The two-step class separation
   re-derived (mod e₂ kills b-ties via gcd(u₂,e₂) = 1; per-t the
   a-class is forced via gcd(h,e₁) = 1; ≤ f₁f₂ tying monomials;
   K-components of the η₂-split force each residue 0). Machine
   (PE2-S): 72 direct slot-min-vs-nfeltval legs (random +
   tie-constructed) at genre A and at the f₁ = 2 genre F1b — the
   FIRST direct (ii) contact (supp touched (ii) only through
   pins); wrong-offset control mismatched 7/72 (T-SLOT tooth).
3. **T(b)′(iii) σ-composition at μ₂ = 2.** S7-at-composed-data
   re-derived, including the F4-rider point one level up:
   lcm(e₁e₂, 2e₁e₂/gcd(p₀, e₁e₂)) = 2e₁e₂ since gcd is odd.
   Machine (PE2-D, 27 instances + perturbations, PARI both routes):
   the branches with ZERO prior 2-stage TRUE-read contact all
   confirmed — composed-INERT {(4,2)} and composed-2SIDED
   {(4,1),(4,1)} at genre A; RAM/INERT/SPLIT/2SIDED at the first
   outer-f₁ = 2 tower genres (1,2,4)→(2,1,2), keys ψ₂ = T−1 AND
   the η-letter key ψ₂ = T−η ({(4,2)}/{(2,4)}/{(2,2)}²); the
   η₂-COCYCLE division at odd w ADJUDICATED (F1b-COCY: naive read
   without the η₂-division says tSPLIT, the note's read says
   tINERT, PARI: {(2,4)} — T-COCYCLE tooth); swapped-dictionary
   tooth T-DICT fired.
4. **T(b)′(iv)'s faithfulness "iff" at the tie edge.** Attack
   constructed: a discrepancy class tying the composed slot-min
   with cancelling residue (shadow pin rises, reads disagree) —
   WITHDRAWN: the antecedent requires "weakly above BOTH reads'
   slot-min", and the risen shadow min breaks it; slot digits of
   the assembled discrepancy live at distinct heights (GENHN-2′),
   so no self-cancellation case survives. The clause is sound as
   displayed.
5. **The f₁ ≥ 2 overflow parenthetical (9636b7e).** Re-derived:
   an x-degree-D′ carry moves (level e₂t, dv₀) ↦ (e₂t+1,
   dv₀ − D′h), and above-the-side is exactly u₂/e₂ > D′h — the
   [r1] floor again; side and residual untouched.
6. **F2's repair (the corrected budget display).** Re-derived at
   E3 (floors (4,3,3,2,2,1), total 15), E31 ((3,2,2,2,1,1), 11),
   GENH4-E ((2h+1,⌈3h/2⌉,h+1,⌈h/2⌉), 8 at h=1), and freshly at
   genre F (1,2,2) ((4h,3h,2h,h) bases) — side height at abscissa
   jD′+i, ceiled, +1 per consumed pin, matching S2's lists and
   the battery exponents; grep-audit of old-formula sites clean
   (F3 above concerns only the erratum's own commentary).
7. **F3's repair (the band-transport derivation).** Checked: (1)
   unread digits sit at heights ≥ N and join height N only on the
   complementary η-basis (comp(N) at (1,3,2)/k=1 is 2, at N+1 is
   1 — recomputed); (2) the trichotomy transports at m = N with
   the census Q^{comp(N)}−1; (3) deeper band heights honestly
   drain (the undercut is real); the E2 parenthetical scoping and
   the upgrade sentence's scope (μ = 2, e₁ = 1, f₁ ≥ 2) match the
   derivation's actual perimeter.
8. **F4/F5 riders.** The S7 rider's arithmetic verified
   (2e₁/gcd(u,e₁) alone at e₁ = 3, u = 9 gives 2; lcm with (T1)
   restores 6 = 2e₁; gcd odd since u odd); the 349/350
   reconciliation is consistent with PE1's forensics (350 = 349 +
   1 gp-miss None) and the isolated battery re-run of THIS pass
   reproduces 1,216/349 deterministically.
9. **[GENHN-TOW-1] honesty at items (1)–(5).** Item (4)
   load-bearing and honest: the PE2-P partial-side member is
   refused by the corrected reader (non-monic composed
   development) and its PARI σ {(2,1),(4,1),(4,1)} is priced by
   no r2 display — the box's claim that this case is OPEN is
   accurate (the box INVENTORY defect is F1, an item missing, not
   a false item). Items (1)/(2)/(3)/(5) checked as genuinely
   unconsumed by T(b)′'s proof text.
10. **First non-prime-q tower contact (PE2-Q).** Genre (2,1,4)→
    (2,1,2) over the 2-inert quadratic base ℚ(ω) (residue F₄,
    Q = 4, ω-letters), absolute degree 16 via rnfequation:
    RAM {(8,2)}, INERT {(4,4)}, SPLIT {(4,2),(4,2)},
    2SIDED {(4,2),(4,2)} — 4/4 exact, including the first
    composed-level SPLIT-vs-INERT residual decision over a
    non-prime residue field.

## MACHINE LEG (integrity) + FRESH ROUTE

* **Pins:** 7/7 md5 match S11.A (runner-as-run 637427dc…, and the
  five supplier pins), plus artifacts dd9edbea…/7d4a3e86… and the
  supp pair (genhnr2_supp.py 51154c95…, output 664036bc…).
* **Sealed battery isolated re-run** (fresh dir, 24-module import
  closure): **GREEN — 2,223,050 checks / 0 violations, teeth
  2/2/2/2/1, 448.8 s**; results JSON content-identical to the
  committed artifact (0 field diffs, elapsed included); output txt
  differs in exactly two per-family timing figures; the V p=2
  diagnostic tail 1,216/349 reproduced (F5's reconciliation
  machine-confirmed on this pass's own run).
* **genhnr2_supp.py isolated re-run** (fresh dir, no local
  imports): exit 0, output BIT-IDENTICAL to the committed artifact
  (md5 664036bc), GREEN 147/0, teeth ×5/×2/×13.
* **Tautology audit of the supp:** scored checks compare the
  corrected reader (own division + slot code) against PARI on two
  independent oracle routes; the stage-shadow read enters only as
  refuted control/teeth; SUPP-A0 pins are cross-checked against
  PE1's hand values; the genre-A INERT branch's hard-coded
  T²+T+1 is forced (F₂ digits at u = 2w make both residues 1 —
  re-derived); genre-B's tDBL guard is unreachable (attaining
  flavors cannot cancel) — dead code, harmless. Non-tautological.
* **Fresh instrument** `verification/openmath/genhn_pe2_fresh.py`
  (independent: own readers, no battery/supp imports; PARI via
  nfinit/idealprimedec/nfeltval + factorpadic route 2 + rnfequation
  for the ℚ(ω) legs): **GREEN — 219 checks / 0 violations
  (PE2-K 5, PE2-S 72, PE2-D 119, PE2-P 3, PE2-Q 16), 4/4 teeth
  (T-DICT, T-SLOT, T-COCYCLE, T-PARSE)**; artifact
  `genhn_pe2_fresh_output.txt`. Disclosure: the instrument ran
  GREEN on its first full run (no reseal events).
* **Fresh-route disjointness:** supp swept outer-f₁ = 1 genres
  ((2,1,4)→(2,1,2) u₂ ∈ {5,7}, (2,1,4)→(1,2,2)) with TRUE-read
  decided rows tRAM only at 2 stages; PE1's legs were the (1,3,2)
  sweeps + the four refuted (2,1,4) instances; the battery had no
  tower leaf rows. THIS pass's territory: outer-f₁ = 2 tower
  genres (1,2,4)→(2,1,2) with both rational and η-letter keys
  (first f₁ ≥ 2 OUTER stage under a tower), first 2-stage
  composed-INERT/2SIDED/SPLIT dictionary contact, first direct
  GENHN-2′ exactness legs, the η₂-cocycle adjudication, a
  partial-side n = 10 member (box item (4) witness), and the
  first non-prime-q (Q = 4) tower legs. Not attempted: d ≥ 2
  ambient towers beyond the ℚ(ω) base change (the Q = 4 legs ARE
  the base-change case), deeper f₂ = 2 outer-f₁ = 2 mixes
  (K₂ = F₁₆) — disclosed.

## GRADE LINE

**passPE2 = NOT CLEAN under the charge bar: CRITICAL ×0, GAP ×2
(F1 the depth-≥ 3 iterated composition missing from [GENHN-TOW-1]'s
five items while GENHN.B claims the amended list correct at n ≥ 8 —
live at n ≥ 16 only; F2 the (CS-3) rider's "every tower leaf with
inner μ₂ = 2" vs (iii)'s full-side perimeter — live at n ≥ 10,
loud-failure mitigation noted), MINOR ×2 (F3 the budget erratum's
f₁ ≥ 2 sign-flipped magnitude parenthetical; F4 the 35/38
denominator). Clean count 0/2 → stays 0/2.** What this pass
POSITIVELY establishes: LEMMA GENHN-T(b)′ (i)–(iv) held against
re-derivation and against every constructed instance at four fresh
genre families incl. Q = 4 — the r2's new mathematics is real; both
GAPs are one-sentence-scale display cures (a sixth box item + two
scope parentheticals), n ∈ {8, 9} is unaffected by either, and
n ≤ 7 is untouched by every finding of this pass. Repair scope by
clause: (F1) one [GENHN-TOW-1] item (the composed-key ITERATION:
carrier/slot/read at level ≥ 3) + the GENHN.B display's n ≥ 16
word; (F2) scope parenthetical at the (CS-3) rider (and its echo in
the T(b)′ annex's (iii) sentence if desired); (F3)/(F4) one-line
corrections inside [r2] blocks. Consumers to notify: GENIND's
n ≥ 8 conditionality line (fe0ed6c) inherits F1/F2's refined
scoping (n ≥ 10 / n ≥ 16) — orchestrator's fold.
