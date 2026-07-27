# HC1 BLUEPRINT — FRESH-FABLE SEMANTIC AUDIT (2026-07-28)

ARTIFACT: `HC1_LEAN_BLUEPRINT_2026-07-28.md` (865 lines, 54 units), read in full.
GROUND TRUTH consulted: `MOVES_2026-07-24.md` §B2-DEF final text 1849–2745 (D.0–D.12)
+ pass-7 carry-algebra spec 1456–1530 + §C displays 3598–3831 (C.1.0(c), DOM 3644,
LST 3728, TYP 3783) + Case-K v2 seal 3017–3045 + REL.1/EQ-2 9379–9418, 9570–9588;
`MOVESGR_LEAN_BLUEPRINT_2026-07-26.md` §8.2 (the three fence certificates + the two
held-unit repairs); `MOVESR_LEAN_BLUEPRINT_2026-07-28.md` §0 (D4 CInterface) +
`MOVESR_AUDIT_FABLE3_2026-07-28.md` (F3-1/2/3, G3-1..4); the campaign ledger's MovesR
PARKED entry + wave-5 resumption charge; the on-disk Moves tail (`grep sorry`, git log
35bf18a / 4b29f6e / 3005c2e, file headers incl. the landTwoSided countermodel);
`verification/case_k_gate_v2_p3.py`. Checks verified BY COMPUTATION where flagged below
(κ arithmetic, F₄ factorization, F₉ both-rise cells, G3's F₂ polynomial identity,
the carry-cocycle laws D1/D2/D4/D5/D6).

## VERDICT: **REJECT (3 crit / 6 gap)**

The architecture is sound and the fence discipline is genuinely respected: all three
MovesGr certificates are honored by construction (IsBaseStage = the faithful Gauss-pin
D.2 bundle, T1/T2; TransHyp carries 1 ≤ e′, 1 ≤ h′, gcd, IsStandardLift, ψ-irr ≠ X,
IAug, per `transitionCoreL_e0_false`; every recentering consumer takes
`IsRecenteringCore`, and S8 derives the child T-law from parent `tvec_unit` +
`child_Tvec` per the L4_TRANSvi fence). The MovesR resumption charge is discharged
item-for-item (R2 = the composite + span pricing; R1 = blockEdge + inlined staircase
equation + window predicate; R3 per-i displayed conclusion; R5 ∀-instances antecedent;
C2's TYP(a) additivity is typed on (levelSet → F_Q, +) → Gr γ — an F_p-space domain,
so the F3-1 p^N-torsion countermodel is evaded, checked explicitly). D.11's one-move
scope is kept everywhere; zero axioms per D9 = the note's literature clause. But three
displayed statements contradict the ground truth, two of them machine-refutable.

---

## CRITICAL FINDINGS

### C-1 (§2.2 `Tower.str`/`Tower.kappa` doc-display; consumed by ht/T3/T4/C1/R6):
the κ formula double-counts e_k — the note's exclusive-STR formula pasted onto an
inclusive-STR definition.

Quote (§2.2): "accumulated stretch `STR_k = e₀·e₁·…·e_k` (C.1.0(c)); κ_k :=
h_k/(e_k·STR_k)". Note (LST head 3731–3735 + base 3752–3754): κ_r := h_r/(e_r·STR_r)
with **STR₀ = 1** ("the root read fixes w(x) = h₀/e₀ = κ₀ (STR₀ = 1)") — the note's
STR_r is the stretch accumulated BEFORE the read (exclusive), so κ_r =
h_r/(e₀·…·e_r) = h_r/(inclusive product). The blueprint redefines STR_k as the
INCLUSIVE product (which T3's stage-scale factor `(T.str T.K)` genuinely needs:
w_K(p) = e₀·…·e_K) while retaining the note's formula verbatim. COMPUTED: at
(e₀,h₀) = (2,1), note κ₀ = 1/2, blueprint formula κ₀ = 1/4. Consequence: `ht` is
wrong at every level with e_r ≥ 2, falsifying T3's displayed equation
(w(mono c) = str·ht c) and everything downstream (T4, T5, C1, C2, T10, R6) on any
ramified tower — precisely the "stale-κ artifact" class the note warns about (3640).
§2 is declared "normative for CONTENT", so this is a statement defect, not syntax.
Repair: κ_k := h_k / STR_k (in the blueprint's inclusive convention), or keep the
note's formula with an exclusive STR and change T3's factor to STR_K·e_K.

### C-2 (unit S1_transHypGate, leg (a)): the concrete increment gate is
UNSATISFIABLE over T2's base — ψ = z² + z + 1 is reducible over F₄, and no degree-2
TransHyp can exist at ambient F = GaloisField 2 2 at all.

Quote (S1): "(a) a concrete inhabitant at p = 2 (base stage of T2, ψ = z² + z + 1,
g = 2, the D.5 lift, (e′,h′) = (1, w(Φ̂)+1))". T2 pins F := GaloisField 2 2,
φ = X² + X + 1, so σ.K = F_Q = F₄ = the WHOLE ambient field. COMPUTED: z² + z + 1
has both roots in F₄ ((0,1) and (1,1) in the F₂[ω]-basis — the cube roots of unity;
F₄ˣ has order 3), so `hirr` is false. Worse, structurally: `hirr` (deg 2 over K) +
`hroot` (z̄ ∈ F a root) jointly force z̄ ∉ K = F — contradiction; so over T2's base
NO TransHyp with g ≥ 2 is inhabitable, whatever ψ. The non-vacuity gate as specified
sends a prover into a wall. Repair: enlarge the gate's ambient (e.g. F := GaloisField
2 4 with the F₄-subfield base, ψ any irreducible quadratic over F₄, z̄ ∈ F₁₆), or run
the gate over a base with K = F₂ (degree-1 φ) inside ambient F₄ — either way T2/S1's
data must be made coherent; T2's own gate (base only) is fine as stated.

### C-3 (unit G4_caseKGate, clause (i)): the both-rise cell predicate `d₀ = d₁³`
contradicts the sealed record's `d₀ = d₁²` cells — the wrong-cells check would PASS
on counts while probing the wrong algebra.

Quote (G4): "(i) the Frobenius-matched both-rise set {(d₀,d₁) ∈ (F9ˣ)² : d₀ = d₁³}
meets the census's 8-of-512 count pattern at the gate's cell granularity". Sealed
record (Q4, MOVES 3030–3032): "the unique both-rise is the Frobenius-matched τ = d₁
on each **d₀ = d₁²** cell — 8 both-rise combos of 512". Script ground truth
(`case_k_gate_v2_p3.py` :396): `d0 = f9mul(d1, d1)`. COMPUTED from the seal's own
algebra: both-rise ⟺ R₂ = X² + d₁X + d₀ has the double root τ ⟺ τ = −d₁/2 = d₁
(char 3) and d₀ = τ² = d₁² — exactly 8 triples, all satisfying d₀ = d₁², τ = d₁;
d₁³ = d₁² on only 1 of the 8 units. Both predicates have cardinality 8, so a
count-only decide passes SILENTLY on the wrong set — the exact species of
prediction-derivation error that voided the v1 seal (adjudication on record at
MOVES 2934). The E-phase transcription note does not cure a displayed wrong
predicate in the normative statement. Repair: d₀ = d₁² (one character).

---

## GAP FINDINGS

### G-1 (§4 dep-sorry ledger vs disk): entries 4.1, 4.2, 4.4 are STALE at the
blueprint's own commit. `L1_baseWeight_R3` ("1 sorry :62 … proof outstanding") was
discharged IN THE SAME COMMIT (35bf18a, +823 lines, direct-MacLane, header dated
2026-07-27); `L2_iaugStep` ("1 sorry :72") was proved the previous day (4b29f6e);
`L5_landVertexDigit` ("1 sorry :70") discharged in 35bf18a (+757 lines). Consumers
T1, S12, C4, S16 carry phantom `dep-sorry:` tags; §4.3's TRANSv cone is likely clean
post-repair ("fresh-recompile axiom-clean", 4b29f6e). Conservative direction, but
the ledger misdirects wave-5 scheduling and contradicts the header's own census
citation. Repair: re-census §4 against disk; only 4.5 (:964) and 4.6 (:143/:189)
remain genuinely open.

### G-2 (§4.5/§4.6 repair specs vs the recorded countermodel): (a) §4.5's
parenthetical gloss — "ord_z of the vertex slot term = 0 after anchoring" — is NOT
the cited file's own proposed clause (`¬ X ∣ Σ_j Cdig j · ψ^j`, the digit TOTAL,
R5 header :62) and is FALSE on honest strata by rev-D¹¹ F4 (MOVES 2500–2505:
individual anchored slot terms need not have ord_z 0 — the anchor is the ord of the
SUM; bottom coefficients cancel across slots); implemented literally it would empty
legitimate strata. (b) The repair ALREADY LANDED fence-safe as an explicit `hexact`
hypothesis on a new theorem (`L5_landTwoSided_repair.lean` :755, commit 4b29f6e) —
no LandingCylinderL field change and no sign-off event is needed; §4.5's fence-gated
plan is moot. (c) §4.6's ":143 resolves with 4.5" is imprecise: the inlined
`L5_landTwoSided_missing` (measureExact :130–:143) is stated WITHOUT the exactness
clause and is refuted-as-stated by the same shifted-anchor countermodel — closing
4.5 does not discharge it; the clause must be THREADED through L6_measureExact's
hypotheses (a restatement, like :189's E.IsSolution-at-Θ(0) leg, which §4.6 does
describe correctly per the in-file FLAG).

### G-3 (§2.2 `Tower.Coord`/`slotBound`/`kappa` underspecification): `slot : Fin
(T.K + 1) → ℕ` gives the TOP level a slot whose bound ("e_r·g_r ratios; def
in-file") is not derivable from Tower data — the note's coordinates live in the
PENDING read's Ĉ (D.3(e): C_{k+1} = stage k's Ĉ needs move k+1's g), which a K-move
Tower does not carry; recentered levels are handled only implicitly (degree-ratio 1
⟹ slot ≡ 0 — correct, and it auto-selects current-frame keys in `mono`, but
unrecorded); `kappa` is total on Fin (T.K+1) though the note assigns κ only to
AUGMENTED levels (benign with slot ≡ 0; unrecorded). Also unpinned: the root birth
index (`eBirth` at 0 := "base e", where the pass-7/§B2-FINAL language has e_birth =
1 at the root; HC1's choice is coherent with the (S5) positions −t·v, but the
convention should be recorded as a decision). One recorded paragraph fixes all four.

### G-4 (unit C6 vs MOVES 2160–2165): states only the SUFFICIENT direction
("IF every slot height clears its stage bound THEN aDim = full piece dimension"),
dropping the display's "exactly when every height in γ's slot tree is attainable"
(only-if) and the "STRICTLY SMALLER at shallow heights" clause. Recorded in-unit and
unconsumed downstream (S17 needs only T7/C6's cardinality equation), so tolerable —
but it is a weaker-than-display statement and should say so in the unit text.

### G-5 (unit T9 vs (ii.3), MOVES 2175–2188): as re-typed, the statement is
definitionally trivial (ht is a function ⟹ level sets at γ ≠ γ′ are disjoint); the
note's content — disjointness of LEAF ADDRESS blocks through distinct slot classes
(t invertible mod e) and distinct p-adic heights — is claimed "absorbed into ht
being single-valued on coordinates", but no unit certifies the absorption (that
distinct Coords address independent base digit coordinates — the injectivity the
S17 counting ultimately consumes via the Moves L6 layer). Either point T9's
docstring at the Moves unit that carries the leaf-partition content, or add the
one-line coordinate-independence lemma to T12.

### G-6 (unit S12): "(I-aug) holds at every read of a tower" is ambiguous between
the projection-trivial reading (each TransHyp already CARRIES hiaug — the D4(ii)
fence design) and the substantive D.4 derivation (every side of the child polygon
available to the NEXT read is steeper than w(Φ̂) — what L2_iaugRoot/Step/Recenter
prove). As worded, the trivial reading satisfies the statement and the L2 deps
become dead weight. Pin the quantifier: (I-aug) for every side of every landing's
child polygon along the tower, per D.4's three bullets.

---

## CHARGE-ITEM RECORD (what passed)

* **Fences (charge 2)** — all three MovesGr certificates respected by construction
  (D4(i)–(iii), §1 table); verified against `HeldUnits_certs` §8.2 text. The
  L4_TRANSvi held-unit repair shape (child law DERIVED, S8) matches §8.2's proposed
  repair exactly. `MoveWitness.rec`, D8, S10, S15, S16 all consume
  `IsRecenteringCore` (`reps_eq`/`Tvec_eq` present in Moves/DefsCore §7 — checked on
  disk). No fenced Moves/MovesGr/MovesC statement is restated or weakened; MovesC is
  consumed via its proved units (C2_DOM / C2_DOM_floorForm / LevelClause — floorOf =
  the pointwise line max on disk, so C4's floor form matches the PROVED statement,
  with the staircase evaluation correctly delegated to T10's blockEdge).
* **MovesR re-key (charge 3)** — R1–R5 implement the wave-5 resumption charge and
  all seven Fable-3 repairs (F3-1/2/3, G3-1/2/3/4), each checked against the audit
  text and the note displays; R6's exclusions (jets/counting legs = HC-2's seam)
  match the PARKED entry. R2's span form corrects Fable-3's per-position "e.g." to
  the note's level-set union — right call, worth one attribution sentence.
* **Tail specs (charge 4)** — 4.5's operative clause (the file's own `¬X ∣ Σ Cdig ψ^j`)
  DOES evade the shifted-anchor countermodel (shifted total = z^Δ·Ranch₀, X-divisible
  — checked); 4.6's :189 spec matches the in-file FLAG. The defects are the gloss and
  staleness (G-1/G-2), not the evasion.
* **Gates (charge 5)** — G1 matches the pass-6 verifier value (MOVES 2318–2322,
  recomputed: z̄² = z̄ + 1 in F₄); G2's carry table recomputed from `carryExp` (dOf 1 1
  * dOf 1 1 = dOf 0 z̄ ✓); G3's Case-J instance verified symbolically over F₂
  (P(z+1) = (z+1)·z²·(z²+z+1), a′ = 2 = μ, R′_anch = (z′+1)·h(z′+1), ψ′ ∤ z^a h ✓);
  G5 matches MOVES 9580–9582 (span card 9 = 3², single line 3). G4 fails at C-3.
* **Carry algebra (D-layer)** — D1's cocycle identity, D2's product law, D4's iso,
  D5's e = 1 collapse (carryExp 0 0 = 0 at e = 1 — the blueprint's own mid-sketch
  correction is right), D6's inverse formula: all recomputed, all faithful to MOVES
  1508–1514. D7 = the correct 𝒟-shadow of DIV(iii) (position additivity from the
  exact remainder weight; carry = the alignment quotient), with the (S5)-shape riding
  as hypothesis — honest. D8 matches MOVES 2668 + the e_birth threading 1478–1499.
* **LST/TYP/DOM (the most-audited displays)** — T3/T4/T5/T10/C1 quantifier-exact
  against LST's three legs incl. the (i-c) downset precondition (which TYP(a) types);
  C2/C3 against TYP(a)/(b) incl. the piece-vs-L₀ relocation (cardinality-preserving,
  fine); C4 against DOM's displayed conclusion with per-i interiors (G3-3 repaired);
  `TowerRealizable` rides as hypothesis exactly where the note's own quantifier
  demands (3670–3677). C2 checked explicitly against the p^N-torsion impossibility:
  domain (levelSet → F_Q, +), an F_p-space — the killed typing cannot recur.
* **Doctrine (charge 6)** — hypothesis fields faithful (TowerRealizable, REL.1 open,
  no new axioms per D9 = MOVES 2738–2743); units short with pre-approved splits;
  census arithmetic (54 = 8+12+6+17+5+6, 10 hard) checks; moves_ref line numbers
  spot-checked ~25 sites, all accurate.

DISPOSITION: three surgical criticals (κ formula; S1's gate field/data; one exponent
in G4) plus the §4 re-census. None is architectural; a rev 2 folding C-1..C-3 and
G-1..G-6 should pass quickly.
