# O1thr — the per-site read package — Phase-B attempt REV 2 (Fable, 2026-07-31)

Repair of the hostile verification `V12_o1thr.jsonl` (verdict SOUND-WITH-GAPS)
of the rev-1 attempt (`O1thr_phaseB_attempt.md`) / brief
(`O1thr_phaseB_verifybrief.md`). V12 CONFIRMED: Theorem 1's transfer core (the
R1/R2 clause transfers, the noncircularity of D-14 — "the proof assumes READ on
one polynomial only to transfer a fixed list of constraints attached to an
already supplied site"), every displayed step of W-ADD, the SPAN
induction-and-contradiction, Theorem 3's cylinder argument (both directions,
the full-preimage strengthening), the p^{n(N−t)} scaling factor, per-box tree
uniqueness/disjointness, and the entire Eisenstein guard placement ("precisely
the guarded/unguarded distinction"). V12 found no critical error and a set of
justification gaps. This rev repairs ALL of them — and the repair round's own
new falsifier caught a REAL defect hiding inside the R5-ambiguity gap (§1
below), the round's headline.

The repaired self-contained brief is `O1thr_phaseB_verifybrief_rev2.md`
(rev-1 verified passages byte-stable except where a listed disposition touches
them). New falsifier: `verification/openmath/o1thr_rev2_checks.py` (run FIRST,
2026-07-31, this machine: ALL PASS; the rev-1 suite `o1thr_persite_check.py`
re-run unchanged: ALL PASS).

## 0. V12 findings → dispositions (no silent drops)

| # | V12 finding (quoted anchor) | class | disposition |
|---|---|---|---|
| G1 | "level-0 data … contains no information about f̄" — root policy input incoherent under the box convention | GAP | **FIXED** (brief §1.1): Φ_0's policy input is the mod-p reduction f̄ = level-1 box data, stated explicitly |
| G2 | "LAWFUL is not actually defined … names rather than predicates"; "Nothing displayed proves L(H) ∈ ℕ" (γ ∈ ℤ arbitrary ⟹ possibly L ≤ 0, p^L ill-formed); the suggested arithmetic law γ ≡ s0·h (mod e) | GAP | **FIXED** (brief §1.2 + §3): LAWFUL := CORE ∧ AUX with CORE fully displayed — new node laws (N2) stride integrality (exactly the verifier's γ ≡ s0·h (mod e)), (N3) height positivity γ ≥ (s0+wSide)·h, (N4) vertex band — plus displayed coherence; AUX an explicit box-free PARAMETER (only box-freeness used; theorems hold for every AUX). NEW Lemma NAT proves L(H) ≥ 2 ∈ ℕ from (N3). (N2)/(N3) exclude only READ-unrealizable records (displayed argument). Consistency/existence never consumed; non-vacuity witnessed (Eisenstein site + harvest) |
| G3 | policy "honest conditionality, but it defeats 'explicitly defined OM read machine' … per any policy satisfying M4" | GAP | **FIXED by explicit parametrization** (brief §1.1): a policy 𝒫 is a displayed formal parameter (degree laws only); Theorems 1/2(a) proved for EVERY 𝒫, Theorems 2(b)/3 for every 𝒫 satisfying (M6b); existence trivial, canonicity/uniqueness scoped out (S-3). No "explicitly defined total machine" claim survives — the per-𝒫 quantifier is now part of every statement's frame |
| G4 | "(M6) … READ also contains R5. Harvesting R1–R3 does not definitionally establish R5 … M6 is a substantive existence/correctness invariant, not merely a definition. Theorems 2(b) and 3 are conditional on it." | GAP | **FIXED** (brief §2.4, §0, §8): (M6) split into (M6a) definitional harvest (R1–R5 data READ off f, incl. the new vertex pair) and (M6b) THE single substantive interface assumption (vertex read well-defined C_μ ≠ 0; harvested vhtx in the (N4) band; AUX at harvest) — honestly tagged ASSUMPTION, cited (GMN vertex transport, attribution flagged), machine-checked exhaustively at depth 1 (T-E: 33,043 instances, 0 violations), and threaded through §0/§8's conditionality statements ("proved modulo exactly ONE substantive interface assumption") |
| A1 | "There is also an ambiguity in R5 … The valuation used for that coefficient is not stated. Theorem 1 treats it as a w_i-graded residual with stretch E_i. That interpretation must be made explicit." | GAP (ambiguity) | **FIXED — and the ambiguity concealed a falsehood** (§1 below; brief §1.3, §9): (R5) restated with the valuation explicit (w_i, current frame, stretch E_i) AND with a RECORDED vertex height vhtx replacing the implicit β*-pin, which the new falsifier REFUTED (1,644 machine countermodel instances). New law (N4): β* ≤ vhtx ≤ I |
| G5 | "(†) was written for the coefficients of the Φ_i-development … the analogous bound for the Φ_{i+1}-development … must be rederived; it is not literally (†)" | GAP | **FIXED** (brief §4): the R5 bullet now displays (†′) — DEV+POS applied to the monic key Φ_{i+1} with heights in w_i — and states that (†) is NOT invoked; the exact-pin and residual transfer run through (†′) + (N4) + R-LOC |
| G6 | "Neither accE, accF, nor Dwidth is defined in a way connecting it to deg Φ_H … Those identifications are asserted here, not derived from §1." | GAP | **FIXED** (brief §1.4, §5): accE/accF/Dwidth defined as record functions, the key-degree identity accE·accF = Dwidth displayed (induction on the degree recursion), verdict := (accE, accF) by definition; saturation ⟺ μ = 1 derived; L-SAT is now a chain of §1.4 definitions + the identity — "nothing is read off any true factorization of f" |
| G7 | "F6 says only that leaf degrees 'match' … does not formally state the sum identity m·deg φ̄. The alternative F3+F5 argument works if 'simple part,' track partition, and verdict degrees have the asserted degree interpretation, but those relations are likewise not fully defined." | GAP | **FIXED** (brief §1.4, §5): track partition (∗∗) displayed (simple part := multiplicity-1 product; n = simple + Σ m_τ·deg φ̄_τ); (F3) = the displayed Hensel multiset with its degree total; (F5) = the displayed checksum; (F6) = the displayed PER-TRACK sum identity Σ_leaves accE·accF = m_τ·deg φ̄_τ; both SPAN routes rewritten against the displayed identities |
| P1 | W-ADD "Correct only if the roster contains every irreducible factor with its full multiplicity. That is precisely the substantive harvest-totality part of M6." | proviso | **FIXED** (brief §5): new displayed "Roster totality" paragraph in SPAN's proof — recorded = candidates exactly, via (M6a)+(M6b)+(F1), both inclusions spelled out |
| P2 | "Correct provided the recorded faces really are distinct faces of one lower polygon." | proviso | **FIXED** (same paragraph): on a fiber the recorded children ARE the candidate pairs of f's ONE window polygon — whence the disjoint interiors |
| P3 | "(F1) forces chains(T) = chains(T″) … assuming 'chains' include their node records" | proviso | **FIXED** (brief §6(c)): parenthesis added — chains are sequences of node RECORDS, chain equality = record equality |
| P4 | "The finiteness sentence is slightly imprecise because trees have varying thresholds t, but disjointness at the common level N repairs it: every nonempty tree with threshold at most N owns at least one distinct level-N box." | imprecision (repair supplied) | **FIXED as the verifier prescribed** (brief §6(c)): empty fibers dropped (mass 0); each remaining T with thr ≤ N has #Φ_N(T) ≥ 1 by (b); level-N fibers of distinct trees disjoint inside the p^{nN} boxes ⟹ at most p^{nN} trees |
| — | "its 'all lawful sites' formulation remains conditional on the missing definition of LAWFUL and the unproved nonnegativity of its ceiling" | corollary of G2 | **FIXED by G2's repair**: LAWFUL displayed-or-parametrized in full; NAT proves the ceiling |

Everything V12 confirmed is carried byte-stable (Theorem 1's statement and
R1/R2 bullets, W-ADD, the SPAN induction paragraph, Theorem 2(b)'s Case 2,
Theorem 3(a)/(b) proofs, §7 Eisenstein, T-A..T-D reports).

## 1. THE ROUND'S HEADLINE — falsifier-first caught a real defect inside A1

Per the standing falsifier-first rule, the (M6b) assumption was given a direct
machine check BEFORE the repaired text was finalized:
`verification/openmath/o1thr_rev2_checks.py` implements the depth-1 vertex
read from first principles (standard key lift Φ_1 = Σ_k ψ̂_k p^{(g−k)h} X^{ek};
exact integer Φ_1-adic development of the decode; Gauss height of the slot-μ
coefficient C_μ).

* The natural reading of rev-1's (R5) — vertex coefficient pinned at the
  side's right-end height β* — is **FALSE at harvest**: 1,644 violations
  across the five configurations. Minimal countermodel: f = X³ + 10X², p = 2,
  face (2,1)–(3,0) (e = h = 1, ψ = z+1, μ = 1, β* = 0): C_1 = f′(−2) = −28,
  height v₂(−28) = 2 ≠ 0. (Mechanism: the polynomial part BELOW the face —
  here the exact factor X² — contributes mass to C_μ, so the vertex height is
  face-external data.) V12's A1 ("the valuation used is not stated") was
  therefore not a mere ambiguity: one of its two natural readings is refuted.
* The repaired (R5) records the height as node data (vhtx, mirroring the
  source machine's clause (vi), which reads the digit at the coefficient's OWN
  weight) and bounds it by the new law **(N4): β* ≤ vhtx ≤ I**. The upper
  bound is exactly what Lemma CEIL and Theorem 1's transfer consume (the read
  stays below the site ceiling); the falsifier confirms the band
  **exhaustively: 33,043 harvested site-instances, 0 violations** (and C_μ ≠ 0
  throughout), alongside the (N2)/(N3)/NAT laws at every harvested site.
* Consequence for the package: Theorem 1 is UNAFFECTED in architecture (the
  R5 transfer now runs at height vhtx ≤ I instead of β* ≤ I); SPAN and the
  cylinder law never used the β*-pin; the Eisenstein guards are untouched. The
  (M6b) seam SHRANK: its checkable kernel (C_μ ≠ 0 ∧ the band) is now
  machine-verified at depth 1, leaving vertex transport at depth ≥ 2 + the AUX
  laws as the assumed residue, cited to GMN (attribution flagged for lookup).

## 2. What the rev-2 brief now claims (delta to rev 1 only)

* Theorem 1 / Theorem 2(a): PROVED OUTRIGHT, now explicitly for every policy 𝒫
  and every box-free AUX; modulus well-formed by Lemma NAT. Statements
  otherwise unchanged.
* Theorem 2(b) / Theorem 3: PROVED MODULO (M6b) — the honest re-tag V12's G4
  demanded (rev 1 said "modulo nothing new beyond (M1)–(M6)" while tagging M6
  a definition; rev 2 names (M6b) as the package's single substantive
  interface assumption, with its depth-1 kernel machine-checked). L-SAT and
  the (F6)-route are now derivations from displayed §1.4 definitions.
* The machine definition gained: the vertex record pair (vhtx, vtx); laws
  (N2)/(N3)/(N4); accE/accF/Dwidth/verdict as displayed record functions; the
  track partition (∗∗); precise (F3)/(F5)/(F6).

## 3. Files

* `lean/notes/openmath/O1thr_phaseB_verifybrief_rev2.md` — the self-contained
  rev-2 brief (verification target; hand THIS to the next pass).
* `verification/openmath/o1thr_rev2_checks.py` — the new T-E falsifier
  (ALL PASS; refutation count of the β*-pin reading reported per config:
  36/144/1008/24/432).
* `verification/openmath/o1thr_persite_check.py` — UNCHANGED rev-1 suite
  (T-A..T-D re-run 2026-07-31: ALL PASS).
* Rev-1 artifacts left in place for the audit trail.

## 4. Verification protocol note

Per the standing discipline this rev is PROVED-UNVERIFIED until fresh-context
passes accept it. Suggested checks for pass 2, beyond the standard charge:
(i) audit that the (N4) band is EXACTLY what Theorem 1's R5 bullet and CEIL
consume (no hidden use of the refuted β*-pin anywhere); (ii) audit the M6a/M6b
split against SPAN's roster-totality paragraph and Theorem 2(b) Case 1's
lawfulness cite; (iii) re-derive the key-degree identity and the
saturation ⟺ μ = 1 equivalence from §1.4 alone; (iv) the depth-2 harvesting
falsifier extension remains open (rev-1 suggestion, still the right next
numeric investment — now doubly so, since vertex transport at depth ≥ 2 is the
assumed residue of (M6b)).
