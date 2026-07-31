# O12 — (REG-p) emptiness at 𝔅_n — Phase-B attempt REV 4 (Fable, 2026-07-31)

Repair of the V13 hostile verification (`V13_o12r3.jsonl`, verdict UNSOUND)
of the rev-3 attempt (`O12_phaseB_attempt_rev3.md`) / brief
(`O12_phaseB_verifybrief_rev3.md`). V13 CONFIRMED the entire rev-3
mechanism — "The new L6d/Fact F argument is correct": (T1) genuinely
c-independent, the shared-vertex telescope leakage-free, Fact F's
falling-factorial count correct in every characteristic — plus the seven
row families' explicitness and grammar annotations, the noncircular
lower-block induction, the determinant/gcd/margin/base-change/solve
algebra, and characteristic-freeness. It found TWO criticals and ONE gap.
The repaired self-contained brief is `O12_phaseB_verifybrief_rev4.md`
(produced by copying rev 3 and editing ONLY the preamble, §1's instance/
claim/scope lines, §2.2's two partition lines, §2.3(iv)+closing, §2.4's
three O2 lines, new Lemma L6e inserted after L6′, Theorem 1's (1)-clause
and its proof's exhaustion sentence and the (3) "designated" phrase,
Theorem 2's statement + (iv) adjustment sentence, Theorem 3's quantifiers,
§7, §8's new rev-4 paragraph, §9 items 8/10/11 + new 12 — verified against
the diff: every confirmed lemma body L1–L5, L6a–L6d, Fact F, L6′, L7,
Corollary D, Theorem 4 is byte-stable). New falsifier:
`verification/openmath/O12_rev4_checks.py` (§5; ALL 12 PASS, zero
findings), run BEFORE L6e was enshrined.

## 0. FINDINGS-WERE audit (the round-4 churn check, per the charge)

Classification of the three V13 findings:

* **V13-1 (O2 allocation underdefined) = class (a)**: a residue/deepening
  of the old V9-F1 gap ("E(e) not actually explicit"), NOT a defect the
  rev-3 repair introduced. The phrase "κ₁ distributed into designated exit
  rows" is verbatim in the REV-2 brief (line 213) and survived rev 3's F1
  repair unnoticed; the repair's new explicitness is exactly what exposed
  it.
* **V13-2 (degree-3 conjunct unverifiable) = class (c)**: a fresh
  discovery in a previously-confirmed section — the §7 degree-3 data is
  byte-identical since rev 1, V7 explicitly checked its kernels/dets, V9
  found no §7 defect beyond the ordering slip. V13 pressed the SCOPE
  sentence (the claim asserted the full sealed tables instantiate (O3)
  while §7 quotes only samples): a statement-completeness defect, not a
  math error.
* **V13-3 (a.e. exhaustion) = class (c)**: fresh discovery in a
  previously-confirmed section — the exhaustion sentence in Theorem 1(1)'s
  proof is verbatim since rev 1 and Theorem 1 was carried as confirmed by
  V9.

**Class (b) count: ZERO.** No finding is a defect introduced by the rev-3
repairs; the round-3 mechanism (L6d/Fact F) was confirmed whole. The
package is NOT churning — the general-grammar/count-rationality layer that
the orchestrator flagged as the rescope trigger is verified-stable. So: no
global rescope to the three-organizations core; instead two genuine repairs
(V13-1, V13-3) and ONE LOCAL RESCOPE (V13-2 — where self-containedness
would require transcribing the complete sealed degree-3 tables, a
high-churn/low-value move; the honest fix is to shrink the conjunct to the
displayed data and label the remainder as an open interface item).

## 1. V13 findings → dispositions (no silent drops)

| V13 finding | class | disposition |
|---|---|---|
| 1: no datum says WHICH terminal rows are "designated" under (O2) nor how the single mass κ₁ is distributed among several — 𝔅_n's O2 members, their E(e), and t_σ not determined for general n | CRITICAL, (a) | **FIXED §2**: the allocation datum α_e : {verdicts of block e} → ℚ[q] with Σ_σ α_e(σ) = q−1 is now displayed table data in §2.3(iv); the O2 verdict row is t_σ + α_e(σ)·q^{−E} (total added mass = κ₁); 𝔅_n gains this datum as a family coordinate and the claim is proved for EVERY choice (Theorem 2 needs only α_e(σ) ∈ ℚ[q] ⊂ ℛ — the verifier itself noted any finite allocation is denominator-harmless); the concrete degree-2 table is identified as the member α₂ = (0, q−1), verified symbolically (CHECK G) |
| 2: the claim included "the project's concrete sealed degree-3 tables are instances of O3 and every concrete entry satisfies the denominator condition", but §7 supplies only example entries + a blanket assertion — not verifiable self-containedly | CRITICAL, (c) | **RESCOPED §3**: the in-claim conjunct now covers (a) the degree-2 table IN FULL (it is displayed in full) and (b) exactly the QUOTED degree-3 items (kernels, dets — which ARE the (O3) forms at E=3,6 — one junction mass, one final density, each checkable by hand); the complete-table identification is now expressly the labeled open interface item **OL-O12-2**, same status as the standing general-n pin; §7's blanket phrases ("stratum masses with denominators…", "final densities with denominators dividing…", "All are elements of ℛ") DELETED |
| 3: the exhaustion "every g ∈ C_e\R_e has SOME polygon" is literally false under the finite-polygon definition — a_e = 0 gives v = ∞ at column 0, the finite polygon need not begin at column 0, such g lie in no L6 cell (Haar-null locus) | GAP, (c) | **FIXED §4**: new Lemma L6e displays the EXACT statement — (C_e\R_e)\Z_e = ⊔_P cell(P) disjointly, Z_e := (C_e\R_e) ∩ {a_e = 0} Haar-null and EMPTY at e = 2 — with proof (the finite-point hull starts at column 0 iff a_e ≠ 0; every cell requires the finite vertex equality at column 0; L1's slope argument invoked only where all root valuations are finite) and clause (iii): no statement of the package consumes set-theoretic completeness (only per-cell closed masses and L4(ii) bounds enter the table; the Σ=1 identity lives only in the non-proof §8); §2.2 and Theorem 1(1) now say "complete up to the Haar-null Z_e (L6e)" |

Everything V13 confirmed is carried byte-stable (§6).

## 2. Repair of V13-1: the allocation datum α_e

§2.3(iv) now displays, as (O2) table data:

    α_e : {verdicts of block e} → ℚ[q],   Σ_σ α_e(σ) = q − 1,
    O2 verdict row := t_σ + α_e(σ)·q^{−E}   [(g1)·(g2), then (g6)]

replacing "the designated terminal rows additionally carry the summand κ₁"
(and §2.4's "t := s + (κ₁ distributed into designated exit rows)" becomes
the displayed t_σ := s_σ + α_e(σ)·q^{−E}). Every occurrence of
"designated" in the O2 role is gone. 𝔅_n is now bookings × composition
data × (for O2) allocation data; the allocation data form an infinite but
explicitly described set — quantifying the theorem over ALL of them only
strengthens it, and each member's E(e) stays a finite displayed list (the
finiteness paragraph is reworded per-member; family-finiteness was
consumed nowhere). Theorem 2(iv) needs exactly one new line: α_e(σ) ∈
ℚ[q] ⊂ ℛ is (g1), the product with q^{−E} and the sum are ring operations.
The e = 2 §2.4 divergence display and §7 both pin the concrete member:
1/q − q^{−3} = (q^{−1} − q^{−2}) + (q−1)·q^{−3}, i.e. α₂ = (0, q−1).
This is a definitional completion, not a new mechanism; its check is
CHECK G (§5).

## 3. Rescope of V13-2: the degree-3 conjunct + OL-O12-2

§1's scope declaration now states the concrete-table conjunct as: (a) the
FULL machine-checked degree-2 table (displayed in full in §7, with its α₂
and composition datum named) is an (O2) member and satisfies (i)+(ii);
(b) each degree-3 item QUOTED in §7 matches the (O3) forms and satisfies
(i)+(ii). §7's degree-3 bullet is retitled "QUOTED DATA ONLY" and stripped
of the blanket all-entry sentences.

**OL-O12-1** (standing, unchanged): 𝔅_n-instance identification for future
non-𝔅_n organizations. **OL-O12-2** (NEW, labeled open interface item,
outside the claim): *the complete sealed degree-3 tables — every stratum
mass, kernel, junction row, and final density on record — are,
entry-for-entry, an (O3) member of 𝔅₃ with its recorded composition
datum.* Dischargeable by a finite transcription-and-correspondence pass
(map each concrete row to its §2.3 family (i)–(vii)); until then the
degree-3 all-entry denominator statement rests on the project's separate
sealed-table verifications (the 95-prime scan of §8), NOT on this theorem.
This mirrors the honest general-n pin rather than smuggling an instance
claim the brief cannot exhibit.

## 4. Repair of V13-3: Lemma L6e (exhaustion off a displayed null set)

Statement (brief §3, inserted after L6′): Z_e := (C_e\R_e) ∩ {a_e = 0};
(i) (C_e\R_e)\Z_e = ⨆_{admissible P} cell(P), disjoint — every g with
a_e ≠ 0 lies in exactly one cell, every g with a_e = 0 in none; (ii) Z_e
is Haar-null and Z_2 = ∅; (iii) nothing downstream consumes set-theoretic
completeness. Proof mechanism: for a_e ≠ 0 all diagram points at columns
0 and e are finite, zero-coefficient columns sit at v = ∞ ABOVE every
finite convex function, so the hull is the finite-point hull — a finite
convex PL function with H(0) = v(a_e) ≥ 1, integral attained vertex
heights, strictly decreasing face slopes; L1 (all root valuations finite
here) forces slopes > 0 with min in (0,1), so H is one admissible P and
L6a's (α)/(β) conditions hold (v = ∞ qualifies for the ≥ conditions);
conversely cell(P) ⇒ {polygon = P} (L6a) gives disjointness. For a_e = 0
every cell demands the finite vertex EQUALITY v(a_e) = h₀ at column x₁ = 0
— impossible at v = ∞. Nullity: {a_e = 0} = ∩_t {v(a_e) ≥ t}, measure
lim q₀^{−t} = 0; at e = 2, a_2 = 0 puts g in R_2, so Z_2 = ∅ (matching
rev-2's verified "e = 2 has exactly one polygon stratum" exactness).
Consumers re-worded: §2.2's "COMPLETE one-step partition" and Theorem
1(1)'s statement + proof now carry "complete up to the Haar-null Z_e
(L6e)" with the booked-nowhere/consumed-nowhere clause. The verifier's
own acceptance route ("the displayed mass calculations can still be
accepted after assuming the required almost-everywhere exhaustion") is
thereby made a proved lemma rather than an assumption.

## 5. Numerics executed (falsifier-first; run before enshrining L6e)

Script `verification/openmath/O12_rev4_checks.py`; log
`O12_rev4_checks.log`; results `O12_rev4_results.json`. ALL 12 PASS:

* **CHECK F (L6e, the finding's direct falsifier).** Exhaustive
  enumeration over exact integer lifts of (ℤ/p^M)^e — genuine ℤ_p
  polynomials — for (e,p,M) ∈ {(2,2,7), (2,3,5), (3,2,6), (3,3,4),
  (4,2,4)}: every C_e\R_e tuple with a_e ≠ 0 has an admissible hull
  (column-0 start, integral vertex heights, strictly decreasing positive
  slopes, min slope in (0,1), b_k ≥ 2, b_j | L_j) and satisfies its own
  cell's conditions; for e ≤ 3, membership counted against an
  INDEPENDENTLY enumerated admissible-P list is exactly 1 there and
  exactly 0 for every other tuple (a_e = 0, in R_e, or outside C_e); the
  exceptional counts equal the exact volume identity
  #Z = p^{(e−1)M}(p^{−(e−1)} − p^{−e(e−1)/2}): 0, 0, 512, 486, 448; and
  Z₂ = ∅ at both primes. REFUTES-hook: one uncovered in-range tuple, one
  double-covered tuple, one covered a_e = 0 tuple, or one Z-count
  deviation kills L6e.
* **CHECK G (allocation datum).** Symbolic (sympy), e = 2, E = 3:
  α₂ = (0, q−1) reproduces the §7 machine-checked rows AND solved vector
  exactly; a 7-member battery of ℚ[q] allocations with Σα = q−1 —
  (q−1,0), (1,q−2), (q−2,1), ((q−1)/2,(q−1)/2), (q,−1), (q³,q−1−q³) —
  keeps every adjusted row and solved entry with reduced denominator
  dividing q⁵(q³−1)² (ℛ-shape) and Σ(solved) = 1. (Definitional check,
  not a mechanism falsifier: the q−2-style weights land in NUMERATORS,
  demonstrating why arbitrary ℚ[q] allocations are pole-harmless.)

Rev-1/rev-2/rev-3 numerics stand unchanged; rev-2's CHECK (a) aggregate
identity (Σ cell volumes = q^{−e} − q^{−E}) is retroactively explained by
L6e (the missing mass is exactly the null Z_e, zero in the limit and
absent at the enumerated in-range heights).

## 6. Byte-stable perimeter (what V13 confirmed; carried verbatim)

Fact F (Möbius formula, multiset denominator ∏c_{D,m}!); L6d in full ((T1)
c-independence via the inverse bijections, the leakage-free telescope, the
(JC) division, shape-event independence); "consecutive faces share exactly
one residue coordinate"; the seven row families' explicitness and grammar
annotations (modulo the O2 allocation now displayed); the noncircular
lower-block induction; all determinant reductions, the gcd calculation,
margins, base changes, solve algebra; no characteristic/tameness/large-q
restriction anywhere. Also carried: L1–L5, L6a–L6c, L6′, L7, Theorems 1–4
bodies except the six seam lines listed in the header, §8's rev ≤ 3
corroborations, the §2.4 booking display. Diff-verified: the only edits
are the header-listed lines.

## VERDICT

VERDICT: REPAIRED-WITH-LOCAL-RESCOPE (findings_were: 1×(a) old-gap residue
— the O2 allocation, now a displayed ℚ[q]-valued datum with the theorem
quantified over every choice and the concrete member pinned as α₂ =
(0, q−1); 2×(c) fresh discoveries in previously-confirmed sections — the
degree-3 conjunct, RESCOPED to exactly the §7-displayed data with the
complete-table identification now the labeled open interface item
OL-O12-2; and the exhaustion gap, CLOSED by the new Lemma L6e proving
exact partition off the displayed Haar-null set Z_e (empty at e = 2),
falsifier-tested to 12/12 exact passes BEFORE enshrinement; 0×(b) — no
defect was introduced by prior repairs, so the verified core is stable and
no global rescope to the three-organizations backup was warranted. The
O-12 theorem now stands at the honestly-narrowed scope: at every member of
𝔅_n — every booking, composition datum, and allocation datum — every block
determinant and every entry denominator is cyclotomic-type and the (REG-p)
failing set is EMPTY at every prime, every δ ≥ 1; concrete-instance
conjuncts: degree-2 in full, degree-3 for the quoted data. Seams: instance
pin = D-11/O-2/T-7/O-14d; value correctness excluded (V7-F1 on record);
OL-O12-1 (future non-𝔅_n organizations); OL-O12-2 (complete degree-3 table
correspondence) — both outside the claim, both labeled.)
