# O13 rev-2 package — hostile verification, PASS 2 (model: Claude Fable 5, fresh context)

Date: 2026-07-31. Input: ONLY `O13_phaseB_verifybrief_rev2.md`. No other project file,
note, or Lean source was read; the first verifier's report was not sought or seen.

Method: every definition and proof audited line by line against the package's own
clauses; all ∀-claims checked for general arguments (not instances); numeric anchors
independently reproduced by re-implementing D1–D5 as an enumerator from the package
text alone (code at /tmp/o13_pass2/enum.py, results quoted in §V below).

**VERDICT: SOUND-WITH-GAPS.** No CRITICAL ERROR found. Every displayed theorem and
lemma (Theorems 1, 2, 3, 5; Lemmas B, L, E, T, T′; the D10 construction; the §5
Corollary conditional on (COMP)) has a correct proof from the package's definitions,
modulo the JUSTIFICATION GAPS listed in §F — all minor, all fillable by one-to-three
lines, none breaking any logical chain.

---

## §V Verification record, item by item (per the §7 checklist)

**1. p-freeness (checklist 1).** Confirmed by inspection. D1–D10 quantify over
integers, multisets of integer pairs, integer compositions, indicator data, the fixed
symbol sets {ROOT, INC, REC}, {z, ep, ns}, {⊥}, and trees labeled by such data; every
bound is a function of n. No prime, residue field, or valuation appears. ✓

**2. Theorem 1 (checklist 2).** Ranges: tag ∈ {0,1,2} ⊆ {0..n+1} needs n ≥ 1 ✓;
D, w ≤ n by (B1)/(B2); W, e, ℓ, s₀ ≤ n by (B5); a ≤ a+ℓ ≤ W ≤ n by (B3)+(B5);
d ≤ n+1 by (B5); S ⊆ {0..n} via (C3) + a+ℓ ≤ W ≤ n; c(g,μ)·g·μ ≤ ℓ ≤ n forces
c(g,μ) ≤ n, and (B5) puts λ's members in {1..n}², so the n²-matrix c determines λ ✓.
Flank bijection: compositions of m ↔ subsets of {1..m−1} (proper partial sums) is a
genuine bijection AT FIXED m; the cut set alone does NOT determine the composition
across different m, and the proof correctly recovers the spans from separately-encoded
fields (s₀ for F_L; W − s₀ − e·ℓ for F_R, nonnegative by (C1)) — injectivity holds ✓.
Length arithmetic re-verified: 1+3+5+(n+1)+n²+2+2n = n²+3n+12 ✓. Sound.
(The trailing Remark's exponent is wrong — finding G4 — but it is explicitly not
consumed.)

**3. Theorem 2(i) (checklist 3).** Forcing chain checked in order: (C5) ⇒ W ≥ 2;
(B4) gives W = 1·W ≤ ℓ, (B3) gives a+ℓ ≤ W with a ≥ 0, so ℓ = W, a = 0; (C4) with
member (1,W) ∈ λ (sel ∈ λ by D1) contributing exactly the whole sum forces
λ = {(1,W)} with multiplicity 1; (B3) s₀ + e·W ≤ W with e,W ≥ 1 forces e = 1, s₀ = 0;
(C1) empties both flanks; (C2)/(C3) pin a, d, S. All fields determined by
(tag, D, w, W) ✓. Existence of the full letter at any occupied stage (needed for
(ii)'s converse) checked against every remaining clause of D1 — all satisfied ✓.

**4. Theorem 2(ii).** s → s forces e·g = 1 (D ≥ 1), tag REC by D3's rule, and
W = μ i.e. sel = (1,W): full REC ✓. Converse: full REC letter has child stage equal
to its own stage (e = g = 1, μ = W), and D3 constrains the successor only through its
stage, so s → s ✓. Both endpoints in 𝒮_n by hypothesis ✓.

**5. Theorem 2(iii) (checklist 4).** The three cases each strictly raise
ρ = (D, t, n−W, φ) lexicographically; in the delicate third case I confirmed that s′
shares ALL FOUR stage coordinates with s (tag′ = REC = tag when t = 2; D′ = D;
w′ = 1·w = w; W′ = μ = W), so (i)'s per-stage uniqueness applies and s′ ≠ s forces
φ(s′) = 1 > 0 = φ(s) ✓. Acyclicity and the ≤ 6n² bound (n·3·n·2 rank values, D ∈
{1..n}, n−W ∈ {0..n−1}) ✓. Walk count Σ_{k≤6n²}|𝒮_n|^k ≤ (|𝒮_n|+1)^{6n²} by binomial
comparison ✓. Also confirmed: "self-loop-free walk" = "collapsed walk", since D5 has
exactly one edge per related pair, so consecutive equal letters can only ride the
self-loop edge ✓. ONE GAP: exhaustiveness of the trichotomy needs μ ≤ W(s), which is
derivable ((B4): μ ≤ g·μ ≤ ℓ; (B3): ℓ ≤ W) but nowhere stated — finding G1.

**6. Lemma B (checklist 5).** Group count ≤ |λ_G| via (S3)'s multiplicity cap;
|λ_G| ≤ Σ g′μ′ = ℓ_G by (C4) (each member weighs ≥ 1) — (C4) correctly used as an
equality with multiplicity, applied to the CHILDREN's shared letter fields ✓;
disjoint nonempty intervals of lengths e_G·ℓ_G ≥ 1 inside [0, μ) give Σ_G e_G·ℓ_G ≤ μ,
and ℓ_G ≤ e_G·ℓ_G bridges to Σ_G ℓ_G ≤ μ ≤ n ((B5) on the parent's selected member) ✓.
Scope note verified: the proof touches only (S2), (S3), (C4), (B5), D3 at the single
node — no finiteness, no (S4). Valid on pre-skeletons ✓.

**7. Lemma L (checklist 5).** (a) root budget σ ≤ e·ℓ = w′ ≤ W = n via (B4)+(B3),
terminal root (n = 1) covered ✓. (b) μ = 1 corner: child stage has window 1, (C5)
makes every letter there terminal, Lemma B caps children at 1, and 1 ≤ σ(ν) ✓;
μ ≥ 2: children continuing by (C5), per-group Σ g″μ″ ≤ ℓ_G by the multiplicity cap
+ (C4), so Σ_G σ ≤ D′·Σ_G e_G·ℓ_G ≤ D′·μ = σ(ν) ✓ — the group strides e_G enter
exactly through e_G·ℓ_G ≤ interval length, as the checklist demands. (c) finite
induction gives #leaves ≤ σ(root) ≤ n; root-to-leaf paths are collapsed walks by
(S4)+(S2), ≤ 6n² nodes each by 2(iii); every node lies on one; #nodes ≤ 6n³ ✓.

**8. Lemma E (checklist 6).** The self-loop comes from (S2) alone at the equal-label
edge ✓ (no appeal to Lemma T's overstated rev-1 clause — the rev-2 repair is real).
Theorem 2(ii)+(i) force all fields; ν′'s group's side data are s's own fields, its
interval is [0, μ) entire, so a second group's nonempty interval is impossible; all
children share λ = {(1, W(s))}; child window μ = W(s) ≥ 2 + (C5) excludes terminal
children, so every child's sel ∈ λ is forced to (1, W(s)); the multiplicity-1 cap
then caps children at one ✓. Line-by-line sound. This is the load-bearing new lemma
and it holds.

**9. D10 well-definedness + Lemma T′ (checklist 7).** ent(ν) exists and is unique
(finite ancestor chain, root is entry) ✓; parent_T̄ strictly decreases (finite) depth,
so T̄ is a rooted tree ✓. Step 0's two descriptions agree (both directions checked,
including the downward induction) ✓. Step 1: incomparable pair ⇒ their meet z is in
run(x), and the two distinct children of z toward them are equal-label children,
contradicting Lemma E's only-child conclusion; closure under parents makes consecutive
chain members parent–child ✓. Step 2: infinite runs — every member non-final, its
run-internal child is its ONLY child (Lemma E), so no entry node has its T̂-parent in
the run: x childless in T̄ ✓; finite runs — an equal-label child of ν_k would extend
the run (step 0), so all T̂-children of ν_k are entry nodes with ent-parent x, and
non-final members export nothing: T̄-children of x = T̂-children of ν_k EXACTLY ✓.
Step 3: (S1) trivial; (S2)+(S4) from T̂'s (S2) at ν_k plus s(ν_k) = s(x) and label
change; (S3) transfers verbatim (same child multiset, same labels, same parent
selection); (S5) — v̄(x) defined ⇒ ν_k an annotated childless leaf ⇒ x childless in
T̄ ✓. Step 4: T̄-depth < 6n² (root paths are collapsed walks, 2(iii)); T̄-branching
≤ n (Lemma B at ν_k, pre-skeleton scope — legitimate, per B's scope note); the
Σ_{d<6n²} n^d count is constructive, and indeed NO König/choice appeal is needed ✓.
Step 5 applies Lemma L to the now-finite skeleton ✓. Sound, modulo finding G2 (a
definition-ordering blemish in D10's annotation clause, repaired by step 1 itself).

**10. Lemma T (checklist 8).** Prefix-collapse argument correct (a run of the whole
sequence puts its first element in some finite prefix, so > 6n² runs would contradict
2(iii) on that prefix's collapse — which IS a walk, since run boundaries are original
edges); the infinite final run yields an s → s EDGE of the walk, hence a self-loop ✓.
The rev-1 overstatement ("a run's letter has a self-loop") is correctly retracted, and
the parenthetical honestly notes nothing downstream needs it — confirmed: Lemma T′
never cites Lemma T ✓ (Lemma T is in fact consumed by NOTHING else in the package;
harmless).

**11. Theorem 3 (checklist 8).** Ordering children injects classes into ordered
labeled annotated trees (equal ordered representatives ⇒ isomorphic unordered) ✓;
plane trees on N nodes = C_{N−1} ≤ 4^N ✓ (checked numerically N ≤ 14); annotations
≤ 4 per node ✓; Σ_{N=1}^{6n³}(16|𝒮_n|)^N ≤ (16|𝒮_n|)^{6n³+1} for base ≥ 2 ✓;
16 ≤ (n+2)^4 and 6n³+1 ≤ 7n³ for n ≥ 1 ✓; exponent 4+(n²+3n+12) = n²+3n+16 matches
the stated (n+2)^{7n³(n²+3n+16)} ✓. Sound.

**12. Theorem 5 (checklist 9).** Tower: perfect residue field gives K^ur with
[K^ur:K] = f and L/K^ur totally ramified separable; unramified different trivial +
tower multiplicativity gives 𝔇_{L/K} = 𝔇_{L/K^ur}; v_K∘N_{L/K} = f·v_L gives
v_K(disc) = f·d; Serre's Prop 13 (correctly cited — its standing separable-residue
hypothesis holds since the residue extension of L/K^ur is trivial) gives
d ≤ e−1+v_L(e); v_L(e) = e·v_p(e) since v_K(p) = 1 and prime-to-p integers are units
(residue char p) ✓. Chain (m−f)+m·v_p(e) ≤ (m−1)+m·v_p(m) ≤ (m−1)+m·log₂m ≤
(n−1)+n·log₂n via f ≥ 1, e | m, p ≥ 2, monotonicity ✓. Sharpness example x^{2^k}−2:
Eisenstein, d = e−1+ek; e = 4, k = 2 gives 11 = 3+4·2 ✓. B(n,p) claims ✓ (p > n ⇒
v_p(m) = 0 for all m ≤ n). Independence: no proof of Theorems 1–3 or Lemmas B/E/L/T/T′
references Theorem 5, tameness, or any p — verified by rereading each ✓.

**13. Conditionality hygiene (checklist 10).** (COMP) is displayed, explicitly
quantified (∀ prime p, ∀ monic degree-n f over ℤ_p), and consumed ONLY by the §5
Corollary, whose proof is the one-line composition (COMP) + Lemma T′ — correct as a
conditional statement ✓. The residual chain (verdict-pin totality) is disclosed rather
than hidden ✓. (VAL-DIV) is consumed by nothing — verified: no displayed proof
references heights, slopes, masses, or realizability ✓. The Corollary's "superset
menu" caveat honestly blocks any realizability reading ✓. The Status-labels section
labels the 2n-path observation as a conjecture consumed nowhere ✓ — no ∀-by-example
anywhere in the accepted chain.

## §N Independent numeric reproduction (enumerator written from this package alone)

| n | |𝒮_n| mine | package | edges (total / non-self-loop) | self-loops | loops=fullREC | rank mono | longest collapsed path | 6n² |
|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 1 | 0 / 0 | 0 | ✓ | ✓ | 1 | 6 |
| 2 | 15 | 15 | 22 / 21 | 1 | ✓ | ✓ | 4 | 24 |
| 3 | 53 | 53 | 123 / 121 | 2 | ✓ | ✓ | 6 | 54 |
| 4 | 197 | 197 | 621 / 616 | 5 | ✓ | ✓ | 8 | 96 |
| 5 | 509 | 509 | 2252 / 2246 | 6 | ✓ | ✓ | 10 | 150 |
| 6 | 1460 | 1460 | 8235 / 8224 | 11 | ✓ | ✓ | 12 | 216 |

All six catalogue sizes match the package exactly; self-loops are exactly the full
REC letters; ρ strictly increases on every non-self-loop edge; longest collapsed path
= 2n for 2 ≤ n ≤ 6, matching the package's (properly conjecture-labeled) observation.
The package's "8224 built edges at n = 6" equals my NON-self-loop count (total 8235
including the 11 self-loops) — consistent under that reading; see G6.

## §F Findings (quote → classification)

**G1 — JUSTIFICATION GAP (Theorem 2(iii), §3).** Quote: "Case e·g ≥ 2 … Case
e = g = 1 and μ < W(s) … Case e = g = 1 and μ = W(s)". The proof never argues these
cases are exhaustive: it needs μ ≤ W(s), which follows from (B4) (μ ≤ g·μ ≤ ℓ) and
(B3) (a + ℓ ≤ W, a ≥ 0) but is stated nowhere. One line fills it. Assumed and
continued; everything downstream of 2(iii) then checks.

**G2 — JUSTIFICATION GAP (D10, §1).** Quote: "v̄(x) := v(ν) if run(x) is finite, its
deepest member ν is a leaf of T̂ …". At the point of definition, run(x) is only known
to be a set; a finite set of tree nodes has a unique "deepest member" only if it is a
chain, which is proved later (Lemma T′, step 1, via Lemma E). The definition
forward-depends on a lemma stated after it. No substantive circularity — step 1 uses
no annotations — so reordering (state the chain lemma before D10) repairs it; but as
written the annotation clause of D10 is not yet well-defined. (Same blemish, milder:
D10's parenthetical "two pre-skeletons differing only in run lengths have the same
collapse" is an unproved gloss with "differing only in run lengths" never defined;
consumed nowhere.)

**G3 — JUSTIFICATION GAP (§6, "The wild corner — exactly what is PROVED
(theorem-grade, to audit)", item 2).** Quote: "The residual pattern λ is well-typed at
every p because residue fields of local fields are finite, hence perfect (irreducible
residual factors are separable; …)". This sentence is about the OM process's residual
factorizations — semantic territory belonging to (COMP)'s chain — and is not derivable
from D1–D10 (in which λ is bare integer data, trivially "well-typed"). Placing it under
a "theorem-grade, PROVED" header overstates its grade. Also, in the same item, "no
clause degenerates at p ≤ n" uses an undefined predicate ("degenerates") and is
auditable only as a restatement of p-freeness. Nothing consumes either sentence
(checked), so this is a labeling/scope defect, not a chain break.

**G4 — JUSTIFICATION GAP (§2, Remark after Theorem 1).** Quote: "dropping the
redundant S, d coordinates gives the leaner bound (n+2)^{n²+2n+8}". False as stated:
dropping S (n+1 entries) and d (1 entry) from n²+3n+12 gives n²+2n+10. Reaching
n²+2n+8 requires also dropping a and s₀ — and dropping s₀ breaks the displayed flank
decoding (F_L's span is recovered FROM s₀), so the leaner encoding would need a
different argument. Explicitly non-consumed ("only finiteness is consumed
downstream"), so harmless; but the number is wrong.

**G5 — JUSTIFICATION GAP (D4, §1).** Quote: "Equivalently: call a stage *reachable*
if it is (ROOT, 1, 1, n) or the child stage of some member of 𝒮_n; 𝒮_n = all letters
whose stage is reachable." As literally phrased this is circular (reachability is
defined via 𝒮_n, then 𝒮_n via reachability); it is a fixed-point characterization
asserted as an equivalence without proof. The equivalence is true (one-line induction
using D3's stage-only constraint) and, as far as I can trace, no displayed proof
consumes the "equivalently" clause (Theorem 2(ii)'s converse uses D3 directly). Cosmetic.

**G6 — JUSTIFICATION GAP (Status labels, §7 tail).** Quote: "the self-loop
characterization and rank monotonicity hold on all built edges (8224 at n = 6)". My
independent build gives 8235 edges INCLUDING self-loops at n = 6, of which exactly
8224 are non-self-loop. The anchor is consistent iff "built edges" means non-self-loop
edges — but then "the self-loop characterization holds on all built edges" is odd
phrasing (the characterization is about the 11 excluded edges). Evidence-grade only,
consumed nowhere; flagged for precision.

## §S Standalone-ness

The package stands alone as promised: every symbol used in a displayed proof is
defined in §1, and the two semantic imports ((COMP), (VAL-DIV)) are displayed,
quantified, and firewalled. No finding of the "package cannot stand alone" type.

## Verdict

**SOUND-WITH-GAPS.** Zero critical errors. Six justification gaps (G1–G6), each minor,
none load-bearing: G1 and G2 are one-line/reordering repairs inside otherwise-correct
proofs; G3 is a grade-label overstatement in expository §6; G4 and G6 are numeric/
phrasing slips in explicitly non-consumed remarks; G5 is a cosmetic unproved
equivalence. Theorems 1, 2, 3, 5, Lemmas B, L, E, T, T′, the D9/D10 formalization, and
the (COMP)-conditional Corollary are verified correct as stated; the rev-2 additions
(D9, D10, Lemma E, Lemma T′) do close the rev-1 gaps they were built to close; all six
numeric catalogue anchors reproduce exactly under an independent re-implementation.

— Pass-2 verifier (Claude Fable 5, fresh context, package-only diet)
