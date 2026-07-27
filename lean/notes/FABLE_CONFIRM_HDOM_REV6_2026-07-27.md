# FABLE FRESH-INSTANCE CONFIRM — §H-DOMAINS rev 6 (2026-07-27)

Verifier: fresh Fable instance (dual bar; Codex pass runs in parallel).
Text: MOVES_2026-07-24.md lines 9890–10850 (§H-DOMAINS rev 6). Charge:
(a) rev 6 encodes the (E5) transitive-enumeration repair faithfully;
(b) SIXTH construction break attempt (unprobed territory: deep cascades
D ≥ 4, cascade×re-split interaction, congruence-heavy cascades);
(c) confirming sweep, own emphasis; (d) independent gate-scoping proof.

## A. Encoding faithfulness (rev 6 vs the repair) — FAITHFUL

Corrected step (4) quoted (MOVES ~10272): "fixing h_k = t substitutes a
constant into the bounds that CITE h_k (those stay (TRI)); but h_k's OWN
bound ... becomes the INDUCED UPPER CONSTRAINT (U_k) φ_k restricted to its
live citations ≤ t − 1". Repair = retain (U_k), discharge by transitive
enumeration; matches the predecessor's Finding-1 repair exactly. Both fix
sites covered: (i) enumeration fixes (checker lines 65-67: bound of a fixed
coord with live citations → upper appended in cascade mode, DROPPED in
literal mode — the two modes are exactly rev 5 vs rev 6); (ii) slab
below-part fixes (lines 171-174) and B-side fixes (lines 140-143) respawn
(U) from an 'A'-resolved coord's stored bound — the integerized form
(c+crc+1, co, v), equivalent on the cell lattice to φ_k ≤ v−1 since v ∈ ℤ
and ⌈φ⌉ = φ+crc there. The re-split-with-ORIGINAL-bound sentence (MOVES
~10303) is implemented at checker line 163 (res[k][2] = the original
(c, co), floor raised first) — note and checker agree. TERMINATION: note
argues finite descent through strictly earlier levels, depth < D; checker
enforces no explicit level order but every upper cites h_{<k} of the fixed
k (triangularity), so the implicit descent is the same argument; the fuel
guard is engineering, and the note correctly bills the census as
"EVIDENCE, NOT PROOF" with the displayed argument as the proof. (E5) is
displayed counterexample-then-fix with the stray (5,1,0); gate scoping and
the H.5.2 REV-6 column bump are all present. One checker-quality remark
(not a note defect): solve()'s fuel is a shared mutable default — a
GLOBAL 2M budget across all systems in a process, fine for the preserved
405-run but worth knowing before reuse.

## B. Preserved-checker rerun (literal vs cascade) — CONFIRMED

Rerun bit-faithful to the record: 4 displayed examples OK, gate OK,
E5-literal FAIL (1995 strays on box 20, (5,1,0) among them — the note's
displayed stray verified), E5-cascade OK 15 pieces (note says 15 ✓),
random failures: 0 (400/400). Total 405/405 as recorded.

## C. Sixth break attempt — NO BREAK (409/409 on unprobed territory)

Attack chosen: the territory the five previous breaks and the 405-run
never entered — DEEP cascades (depth ≥ 2 spawn chains), the cascade ×
re-split interaction, congruence-stride cascades, multi-citation uppers,
D ∈ {4, 5}. Nine hand-built in-class systems (/tmp/sixth2.py): S1 depth-3
chain (y≥x+1, z≥y+1, w≥z−10); S2 cascade through moduli (2,3,2) with a
half-integer slope; S3 multi-citation upper (z≥x+y−7 then w≥z−9: fixing z
confines x+y JOINTLY); S4 slab-raise re-split then below-part cascade
(y≥x−2, z≥2y−3); S5 rational slopes both levels (2/3 then 3/2) + moduli;
S6 residue UNION on the cascade-enumerated coordinate; S7 D=5 chain with
nested below-parts; S8 two bounds sharing one source (two uppers on the
same x); S9 floor-1 + modulus-4 lift arithmetic in enumeration ranges.
ALL NINE: cascade mode EXACT (union = brute force, disjoint, no strays/
orphans) and ALL NINE literal-divergent — each one refutes rev 5 and is
fixed by rev 6's cascade. Plus 400 fresh-seed randoms (seed 20260727,
D ∈ {2,3,3,4}, moduli ≤ 5 with unions, slopes ≤ 3 denominators ≤ 4,
constants in [−9,4] — fatter floor sides than the preserved campaign —
floors {0,1}, boxes 22/14/10): 400/400 EXACT, 0 fuel-skips, 54 of 400
literal-divergent. Combined 409/409; the step-(5) consistency assert
never fired. The sixth break DID NOT MATERIALIZE.

## D. Gate scoping (adjacent-only ⟹ cascade-unreachable) — VERIFIED

Independent derivation: an adjacent-only census has bounds = (I-aug)
only, φ affine in earlier rises with POSITIVE INTEGER coefficients
(e_{i+1}·e_i·g_i ≥ 1) and constant term 0, over floors h_i ≥ 1. So
(a) φ ≥ 1 on every admissible point, while the floor-dominated side
needs ⌈φ⌉ ≤ f − 2 ≤ −1: EMPTY, no enumeration fix; (b) integer slopes
give crc = 0, so the slab threshold t0 = f − 1 − crc − c = f − 1 ≤ 0 and
each solo threshold T = (t0 − rest)/a ≤ 0 < 1 ≤ the cited floor: no
floor-raise (no re-split) and an empty below-part (no slab fix). NO
coordinate is ever fixed ⟹ no (U) arises ⟹ cascade unreachable; the
same holds for multi-cited (I-aug) (rest ≥ 0). Matches the note's REV-6
SCOPING paragraph clause for clause. Empirical: literal vs cascade give
IDENTICAL piece sets on the gate family (2 pieces = the sealed
components), a 3-read adjacent chain with moduli (2,3), and a
multi-cited adjacent system — rev 5 ≡ rev 6 on the campaign class; the
H-n3 seal is untouched by the repair.

## E. Confirming sweep (own emphasis: the rev-6 delta text)

- (E5) display arithmetic re-derived: φ_y = x, φ_z = y−6, floor side
  y ≤ 4 nonempty with y ∈ {1..4} in S, (U_y): x ≤ t−1, t=0 empty,
  t=1 leaves x=0; affine side y ≥ 5 merges into y's floor and re-splits
  ⌈φ_y⌉+1 = x+1 vs 5, cascade-free (x cites nothing) — all correct;
  15 pieces on box 20 confirmed.
- Machine-check paragraph vs checker source: parameters match exactly
  (D ∈ {2,3}, slopes ≤ 3, constants [−6,3], floors {0,1}, moduli ≤ 4
  with unions, boxes 20 random / 24 displayed; 405 = 4+1+400); billed
  as evidence-not-proof with the displayed argument as proof — correct.
- REORDER-SOUND (step (1)): sub-systems only drop/substitute bounds and
  re-add ORIGINALS at re-splits, so the stride lcm is over a superset of
  the surviving pairs — sound; checker computes strides once, globally.
- H.3's consumption: terminal pieces are genuinely (TRI) with no live
  upper (the cascade discharges every (U)), so step (6)'s free
  parameterization and the geometric-sum factorization apply per piece.
- H.5.2 column reads REV 6; every remaining "keeps (TRI)" occurrence is
  a historical quote of the refuted rev-5 claim, not live text.
- Cosmetic from the rev-5 pass (H.1 "E equals the ratio" — should be
  negated log_q) is recorded in the pass record as not yet applied, and
  indeed still stands in H.1's statement — cosmetic only, carried.

## VERDICT: CLEAN — 0 critical, 0 gaps, 1 carried cosmetic

(a) Rev 6 encodes the transitive-enumeration repair FAITHFULLY at both
fix sites, with termination argument matching the checker's implicit
descent and the census correctly billed as evidence. (b) The sixth
break attempt — deep/interacting cascade territory, 9 hand-built + 400
fresh randoms, 63 of them rev-5-refuting — found nothing: 409/409
exact. (c) Sweep of the rev-6 delta clean; the rev-5 cosmetic is
honestly carried. (d) Gate scoping proved independently and confirmed
empirically (identical literal/cascade pieces on campaign-class
systems). Fable half of the dual bar: ACCEPT rev 6.
