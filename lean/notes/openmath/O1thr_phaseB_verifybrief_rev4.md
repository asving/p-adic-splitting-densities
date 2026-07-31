# The per-site read package (REV 4): lawful-site locality, the realized tier with window closure, and the cylinder law

*(Self-contained verification brief. Everything used is defined here; no external
project files are needed. Charge for the verifier: quote each offending passage and
classify it as CRITICAL ERROR (breaks the logical chain) or JUSTIFICATION GAP (assume
and continue); fix nothing. Labels on claims: (a) known, (b) new proof of known,
(c) claimed new.)*

*(This is revision 2. A prior audit (verdict SOUND-WITH-GAPS) confirmed the transfer
core of Theorem 1, the R1/R2 clause transfers, the W-ADD accounting steps, the SPAN
induction and contradiction, the cylinder/scaling/uniqueness arguments of Theorem 3,
and the Eisenstein guard placement, and flagged justification gaps, all repaired
here: the root policy's input data is mod-p, not "level-0" (§1.1); the policy is now
an explicit universal parameter (§1.1); LAWFUL is restructured into a fully displayed
CORE plus a box-free parameter AUX, with new displayed node laws (N2)–(N4) and Lemma
NAT proving L(H) ∈ ℕ (§1.2, §3); (R5)'s valuation is made explicit — and the repair
round's own new falsifier REFUTED the natural implicit reading of rev 1 (vertex
height pinned at β*), forcing a restatement with a RECORDED vertex height (§1.3, §9
T-E); (M6) is split into its definitional half (M6a) and its substantive half (M6b),
now the package's SINGLE substantive interface assumption, machine-checked at depth 1
(§2.4, §9); the R5 transfer bound (†′) is rederived rather than borrowed from (†)
(§4); accE/accF/Dwidth/verdict are defined and L-SAT is DERIVED (§1.4, §5); the fiber
clauses (F3)/(F5)/(F6) are stated as displayed degree identities over a displayed
track partition (§1.4, §5); and Theorem 3(c)'s finiteness sentence is tightened to
disjointness at the common level N (§6).)*

*(Revision 3, after a second audit (verdict SOUND-WITH-GAPS) that confirmed Theorem 1
and the lemma layer and exposed one load-bearing gap and five smaller ones. The main
repair: the second audit found substantive, f-dependent content hiding under (M6a)'s
"[Definition of harvesting]" tag — that harvested children satisfy (R1) at slots
BEYOND the window, and that every realized child arises from a window face. Rev 3
DECLARES this as the named interface condition **(M6c) (window-harvest completeness,
§2.5)** and then PROVES it: outright at root states and at first key transitions over
degree-1 root keys (Lemmas ROOT-M, VAL1, KEY1, DIV1, WGEO — self-contained), and at
general states modulo two named citation-grade inputs (V1)/(V2) (MacLane/GMN key-
polynomial theory). The proof forced a definitional PIN: the window heights at
non-root states, left under-specified at rev 2, are the READ-SLOPED heights (the
w-recursion of §1.1 is repaired accordingly, and the read clauses (R1)/(R2) carry an
explicit slot shear at order ≥ 1) — the rev-3 depth-2 falsifier REFUTES the plain
unsloped reading (440 + 7,472 countermodel instances, §9 T-F) and confirms the sloped
one exhaustively (41,720 instances, zero violations). The same lemmas DISCHARGE
(M6b)(i) and (M6b)(ii)'s consumed upper half, shrinking the assumed interface to
AUX-at-harvest plus (V1)/(V2). Also repaired: "realized" is now ONE displayed notion
(REALIZED, §1.3) with a realization-coherence lemma (REAL≡, §2.5) replacing the
silent equivocation; Theorem 2(a) is restated in that notion and its conditionality
row corrected (§5, §8); Theorem 3(c)'s σ-count is given a displayed definition and
its exhaustion caveat (E-N) is stated as OPEN rather than implied (§6); the root
window's face confinement is displayed (Lemma ROOT-M, §2.5) and cited in W-ADD; the
garbled sentence in Theorem 3(a) is fixed; and the editorial minors (ceiling gloss,
integer-valuedness of heights, P_β^+, IrrHalts/NsHalts/irrVerdict) are displayed.)*

*(Revision 4, after a third audit (verdict UNSOUND: three criticals, five gaps) that
RE-VERIFIED the rev-3 sheared displays — Theorem 1, POS, DEV, R-LOC and §4's sloped
re-derivation all confirmed, the §1.1 convention pin standing — and broke the rev-3
PACKAGING at three points, all repaired here. (1) Circularity: rev 3 stated (M6c) at
"REALIZED NON-HALTED" states, while its consumers (Lemma REAL≡'s ⟸ direction;
Theorem 3's (F1)/(F4) legs) invoked (M6c)(ii) precisely to PROVE non-ns-halting — at
states not yet known non-halted. Rev 4 REQUANTIFIES (M6c) with NO halting hypothesis
(§2.5): none of its proofs ever used the guard, the child hypothesis is weakened to
READ + (N1) (full REALIZED not needed), and non-ns-halt becomes a CONCLUSION of
(M6c)(ii); the depth-2 falsifier had already enumerated ALL depth-1 states, saturated
and ns-halted included, confirming the requantified laws exhaustively (§9 T-F).
(2) Policy over-claim: "proved outright for every policy" was FALSE for §2.5 —
Lemma KEY1's hypothesis is the displayed STANDARD key lift, an arbitrary monic lift
of the right degree need not satisfy it (nor MacLane's key conditions, so (V1)/(V2)
cannot rescue arbitrary lifts). Rev 4 restates (V1)/(V2) as KEY-COMPLIANCE conditions
on the policy's assigned keys, scopes Theorems 2(b)/3 to compliant policies, and
proves compliance exactly for the standard lift over degree-1 root keys
(VAL1/KEY1/DIV1); Theorems 1/2(a) remain every-policy. (3) Root-kernel mislabel: the
ledger claimed the vertex kernel ((M6b)(i) + (N4)-upper) proved "at root states"
while Corollary VTX's own text deferred root-harvested children to the T-E check;
rev 4 PROVES that kernel (WGEO applies at the first-transition state under a fresh
root harvest — its read hypotheses are supplied by (M6a) + ROOT-M) and corrects the
one-level over-claim in rev 3's "and first transitions" phrasing (children harvested
AT first-transition states have their vertex law at order 2, inside the (V1)/(V2)
perimeter). Also repaired per the audit: (V2a) is restated as the exact divisibility
block WGEO consumes (rev 3's "Φ_i-degree" gloss left the grading undefined); the
WGEO(b) "unit bracket" step is replaced by a domain-cancellation argument; DIV1's
reduction step is rewritten Φ_0-adically (rev 3 wrote X^{d−D}, not weight-graded when
Φ_0 = X − a ≠ X); WGEO(b) is flagged as FIRST-attainment only; Theorem 1's proof
notes the record-only third REALIZED clause; AUX's prefix closure is displayed
(silently consumed by rev 3's Theorem 3 (F1)-backward prefix step); and (V1)/(V2) are
demoted from "citation-grade" to CITED-WITH-OWED-DICTIONARY, exact loci displayed
(§2.5, §8 S-4).)*

## 0. What is claimed, in one paragraph

We study a digit-reading classifier for monic degree-n polynomials over ℤ_p — an
Okutsu–Montes (OM) read machine that factors a polynomial by iterated Newton-polygon
side reads in a tower of MacLane frames. Three theorems are proved about it.
**Theorem 1 (lawful-site locality, "D-14")**: for every LAWFUL read-site — lawful
meaning its recorded data satisfy the machine's box-free laws, NOT presupposed
realized on any run — there is a modulus L, computable from the site's recorded data
alone (1 + the largest ⌈de-normalized side-line intercept⌉ over the site's reads, §3),
such that whether the machine reads that site on f is determined by f's coefficient
digits below level L. **Theorem 2 ("O-1(thr)")**: (a) the realized-site two-lift
comparison form of Theorem 1, uniform over working precisions ≥ L; and (b) window
closure: at every state of a decided ns-free classification tree T, on the whole
cylinder of boxes agreeing below thr(T) the REALIZED-children roster (§1.3) is
exactly T's recorded roster — deep candidate children are excluded, not merely
untransported.
**Theorem 3 (the cylinder law, "D-15")**: the fiber of a decided ns-free tree T
(the set of boxes fibering T, §1.4 (F1)–(F6)) is, at every precision
N ≥ thr(T), an EXACT finite union of level-thr(T) coefficient cylinders; fiber
counts consequently scale by p^n per level, giving the per-tree mass tie. Theorem 1
and 2(a) are proved outright for the machine defined below — for every policy and
every box-free lawfulness completion, both explicit universal parameters (§1.1,
§1.2). Theorem 2(b) and 3 are proved modulo the interface residue displayed in §2.4
and §8: **(M6b)(iii)** (harvested records satisfy AUX), the lower (N4) band, and —
beyond the proved slice below — the named inputs **(V1)/(V2)** of §2.5, stated at
rev 4 as KEY-COMPLIANCE conditions on the policy's assigned keys (MacLane
augmentation multiplicativity; the key initial-form/development/residual
dictionary; attributions displayed, normalization dictionary OWED). *(Rev-4
honesty repair: an arbitrary monic lift of the right degree need NOT comply, so
2(b)/3 are claimed for COMPLIANT policies only, compliance itself PROVED for the
standard lift on the slice below.)* The rev-2 assumption's checkable kernel
((M6b)(i) vertex nonzero; (M6b)(ii)'s consumed upper half) and the window-harvest
completeness **(M6c)** — requantified at rev 4 with NO halting hypothesis, so that
non-ns-halting is a conclusion of (M6c)(ii), never a hypothesis (rev 3's guarded
form made its consumers circular; pass-3 finding) — are PROVED in §2.5 on the
displayed perimeter: (M6c) outright at root states (any policy, any root-key
degree) and, under a standard first key, at first-transition states over degree-1
root keys; the vertex kernel outright for children harvested at root states there
(rev 4 repairs rev 3's contradictory root-kernel labeling); modulo (V1)/(V2)
elsewhere. The honest conditionality ledger is §8. An exhaustive machine
falsifier (28,036 boxes, 115 sites, five (p, n) configurations, zero violations,
ceilings sharp; the (M6b) kernel checked on 33,043 harvested site-instances with
zero violations; plus, new at rev 3, the (M6c)/window-geometry laws checked on
41,720 depth-2 state instances with zero violations and the unsloped window
reading REFUTED) is reported in §9.

## 1. Setting

Fix a prime p and n ≥ 2. Monic f = X^n + a_{n−1}X^{n−1} + ⋯ + a_0, a_i ∈ ℤ_p.
Normalize v_p(p) = 1.

* A **level-M box** x is a tuple (a_0, …, a_{n−1}) of coefficients mod p^M; its
  **decode** f_x is the integer-lift polynomial (digits ≥ M set to 0). Boxes at
  levels M, M′ **agree below level L** (L ≤ M, M′) iff corresponding coefficients
  are congruent mod p^L. A **level-L cylinder** is a full congruence class mod p^L.
* For polynomials: f ≡ f′ (mod p^L) means coefficientwise congruence.

### 1.1 Frames (MacLane/OM valuation tower)

A **frame** of order i is F_i = (Φ_i, w_i, K_i) built recursively:

* Order 0: Φ_0 = a monic lift, prescribed by a fixed policy from the mod-p
  reduction f̄ ∈ 𝔽_p[X] alone (= level-1 box data — the residue coefficients; no
  deeper digits enter), of an irreducible factor φ̄ of f̄ (deg Φ_0 = deg φ̄ =: d_0);
  w_0 = the Gauss valuation relative to Φ_0: for B = Σ_j c_j Φ_0^j with deg c_j < d_0,
  w_0(B) := min_j v_p(c_j) — here v_p on the coefficients of the c_j (equivalently
  the Gauss valuation of the multivariable rewrite; the standard order-1 OM
  valuation). K_0 = 𝔽_p[z]/(φ̄) — the residue field of the track.
* Order i+1: given F_i and a read ν_i (data in §1.2: coprime pair (e_i, h_i),
  e_i, h_i ≥ 1, and an irreducible ψ_i ∈ K_i[z] of degree g_i), the successor key
  Φ_{i+1} is a monic polynomial of degree e_i·g_i·deg Φ_i determined by ν_i's
  recorded data and the policy (a "lift of ψ_i along the side", MacLane key /
  GMN representative); w_{i+1} is the augmented valuation **along the CURRENT key
  and the read's slope**: for B = Σ_j c_j Φ_i^j (deg c_j < deg Φ_i, the unique
  Φ_i-adic development), w_{i+1}(B) := min_j ( e_i·w_i(c_j) + j·γ_{i+1} ), with
  γ_{i+1} := e_i·w_i(Φ_i) + h_i (> e_i·w_i(Φ_i)). K_{i+1} = K_i[z]/(ψ_i).
  *(Rev-3 repair, forced by the depth-2 falsifier: rev 2 developed B in Φ_{i+1}
  with weight e_i·w_i(Φ_{i+1}) + h_i, which leaves the read heights at order ≥ 1
  effectively unsloped; the plain reading's window harvest is REFUTED by machine
  countermodels (§9 T-F), while the chain displayed here — the MacLane composite,
  augmenting w_i at its own key Φ_i by the read's slope h_i/e_i — passes the
  depth-2 check exhaustively and supports the §2.5 completeness proofs.)*

Write E_i := w_i(p) = e_0·e_1⋯e_{i−1} (E_0 = 1) — the **stretch** (w_{i+1}(p) =
e_i·w_i(p) from the slot-0 development of p). The **de-normalized level** of a
w_i-height β is β/E_i (so p^L-divisibility is height L·E_i). Write

    γ̂_i := w_{i+1}(Φ_{i+1})   (the successor key's own height; γ̂_{−1} := 0, and
                               w_0(Φ_0) = 0 since Φ_0 is monic),

the **key height** — a function of records and policy ((M4)). Reads at frame i
measure the Φ_i-development of f in the **sheared heights**

    u^{(i)}_j (B) := w_i(B) + j·γ̂_{i−1}     (slot j; γ̂_{i−1} = w_i(Φ_i) for i ≥ 1),

i.e. the height of B_j·Φ_i^j rather than of the bare coefficient; at i = 0 the
shear vanishes and u^{(0)}_j = w_0. On nonzero integral polynomials every w_i —
hence every u^{(i)}_j — takes values in ℕ: induction, since v_p does, each
w_{i+1} is a min of the integers e_i·w_i(c_j) + j·γ_{i+1} over integral c_j
(Lemma DEV), and γ̂_i ∈ ℕ. All frame data along a history are functions
of the RECORDS and the policy — never of f. This is interface property (M4) below.

*(Standard facts, MacLane 1936 / GMN Trans. AMS 364 (2012) §§1–2, stated here as
they are used; proofs of the two we rely on are given as Lemmas POS and DEV.)*

**The policy is a formal parameter.** A **policy** 𝒫 is any function assigning
(i) to each monic irreducible φ̄ ∈ 𝔽_p[X] a monic lift Φ_0 ∈ ℤ_p[X] with
deg Φ_0 = deg φ̄, and (ii) to each lawful node ν over a frame F_i a monic key
Φ_{i+1} ∈ ℤ_p[X] with deg Φ_{i+1} = e_i·g_i·deg Φ_i. The machine, LAWFUL, READ,
and every statement below are relative to ONE fixed 𝒫. Theorems 1 and 2(a) are
proved for EVERY policy — only the degree laws and pinnedness ((M4)) are consumed.
Theorems 2(b)/3 are proved for every policy satisfying the §2.4/§2.5 interface
residue: (M6b)(iii), the lower (N4) band, and (V1)/(V2) **key compliance** of its
assigned keys beyond the proved slice (§2.5). *(Rev-4 repair of a pass-3 critical:
monicity + degree do NOT imply compliance — Lemma KEY1's hypothesis is the
displayed STANDARD lift, and MacLane's augmented-value theorem requires genuine
key polynomials, not arbitrary lifts. Call 𝒫 **standard at a degree-1 root node**
if at a root read over a degree-1 root key it assigns the standard lift displayed
in Lemma KEY1; compliance is PROVED there (VAL1/KEY1/DIV1) and ASSUMED — the
(V1)/(V2) content, cited with owed dictionary — at all other nodes. For genuine
MacLane-key/GMN-representative policies compliance is the key-polynomial content
of OM theory — seam S-4; machine-checked at depths 1 and 2 in §9 on the standard
slice.)* Existence of policies is trivial (any lifts of the right degrees);
existence of COMPLIANT keys beyond the proved slice is MacLane/GMN key-polynomial
theory — part of the (V1)/(V2) citation, NOT proved here. Canonicity and
uniqueness are a separate well-posedness node (seam S-3) and are used NOWHERE in
this brief.

### 1.2 Nodes, sites, lawfulness

A **node** ν records one side read: the frame index; the side pair (e, h) coprime,
e, h ≥ 1; left slot s0 ∈ ℕ; slot width wSide with e ∣ wSide; the side value γ ∈ ℤ
(the side line is ℓ(j) := (γ − j·h)/e in SHEARED height units u^{(i)}, §1.1 — at
the root frame these are plain w_0-heights); the residual pattern
pat : {0, …, wSide/e} → K with pat 0 ≠ 0 and pat(wSide/e) ≠ 0; the residual
polynomial R(z) = Σ_k pat(k)·z^k; a monic irreducible ψ ∈ K[z] of degree g with
ord_ψ(R) = μ ≥ 1 exactly; the transported vertex pair (vhtx ∈ ℤ, vtx) — the
recorded vertex height and residual value consumed by clause (R5) of §1.3; the
produced key data; and species (root / increment / recentering). A **site** (H, ν)
is a history H = [ν_0, …, ν_{k−1}] (possibly empty above the root state) together
with a next node ν; write H·ν for the extended history.

**The displayed per-node laws.** Write β* := ℓ(s0 + wSide) (the side's right-end
height) and I := ℓ(0) = γ/e (the intercept). For a node ν:

* **(N1) shape:** the record constraints already listed — e, h ≥ 1 coprime;
  s0 ∈ ℕ; wSide ≥ 1 with e ∣ wSide (so wSide ≥ e); γ ∈ ℤ; g, μ ≥ 1;
  pat(0) ≠ 0 and pat(wSide/e) ≠ 0; ψ monic irreducible, ord_ψ(R) = μ exactly.
* **(N2) stride integrality:** γ ≡ s0·h (mod e) — equivalently the side line ℓ
  takes INTEGER values at the stride slots s0 + e·κ, where the exact pins of
  (R2) live (w-heights of nonzero integral polynomials are integers, §1.1).
* **(N3) height positivity:** γ ≥ (s0 + wSide)·h — equivalently β* ≥ 0, hence
  ℓ(j) ≥ 0 for every slot j ≤ s0 + wSide of the side.
* **(N4) vertex band:** β* ≤ vhtx ≤ I. (The upper bound is consumed by Lemma
  CEIL and Theorem 1's (R5) transfer, and is PROVED at harvest where Lemma WGEO
  applies (Corollary VTX, §2.5); the lower bound is consumed only in Lemma
  REAL≡'s lawfulness step and remains machine-checked, §9 T-E.)

Every READ-realizable node satisfies (N2)/(N3): (R2) pins integer heights ≥ 0
(Lemma POS) at the stride endpoints, where pat ≠ 0. So (N2)/(N3) exclude only
records no polynomial can realize. (N4) is the vertex-band law consumed by
Lemma CEIL and Theorem 1's (R5) transfer; that the machine's own harvest
respects it is part proved (Corollary VTX, §2.5) and part (M6b) (§2.4),
machine-checked exhaustively at depths 1 and 2 (§9 T-E, T-F).

**History coherence (displayed):** along H = [ν_0, …, ν_{k−1}], key degrees and
stretches compose (deg Φ_{i+1} = e_i·g_i·deg Φ_i, E_{i+1} = e_i·E_i); slopes
strictly increase in de-normalized units along recenterings.

**LAWFUL(H) := CORE(H) ∧ AUX(H)**, where **CORE** := (N1)–(N4) at every node plus
history coherence — all displayed above — and **AUX** is the machine's remaining
canonical-presentation bundle (transition admissibility: span-entry conditions;
the policy pins each node's lift and the canonical root of ψ), carried here as an
EXPLICIT PARAMETER: any PREFIX-CLOSED predicate of the record chain and the policy
alone (holding of a chain only if of each of its prefixes — true of the source
machine's per-transition admissibility bundle by construction). *(Rev-4 display:
prefix closure was silently consumed by rev 3's "a prefix of a REALIZED pruned run
is one" step — Theorem 3, (F1) backward; it is now part of the parameter's
definition.)* Every theorem below holds for every such AUX. **The only properties
of AUX used in this brief are that it does not mention f and that it is
prefix-closed**; the only properties of CORE used are the
displayed laws themselves ((N2)–(N4) enter through Lemmas NAT and CEIL). LAWFUL
is therefore box-free in full. Consistency and existence of lawful extensions are
NEVER consumed (every theorem is universally quantified over sites or fibered
boxes); non-vacuity is nonetheless witnessed — the Eisenstein site of §7
satisfies CORE, and harvested sites satisfy CORE by construction plus the
displayed vertex laws ((M6a)/(M6b)/Corollary VTX, §2.4–2.5). (§8, seam S-2.)

### 1.3 The run predicate

For monic f of degree n and a history H = [ν_0, …, ν_{k−1}] with frames F_i and
developments f = Σ_j B^{(i)}_j Φ_i^j (the unique Φ_i-adic development):

**READ(f, H)** := deg f = n, f monic, and for each i < k, with ℓ_i(j) := (γ_i − j·h_i)/e_i
and the slot thresholds β_{i,j} := ℓ_i(j) − j·γ̂_{i−1} (the side line pulled back to
bare-coefficient heights through the shear of §1.1; β_{0,j} = ℓ_0(j)):

* **(R1) side support:** for every j with B^{(i)}_j ≠ 0:
  u^{(i)}_j(B^{(i)}_j) ≥ ℓ_i(j) — equivalently w_i(B^{(i)}_j) ≥ β_{i,j} —
  with equality ONLY at the stride slots j = s0_i + e_i·κ having pat_i(κ) ≠ 0;
* **(R2) digit pins:** at every stride slot j = s0_i + e_i·κ with pat_i(κ) ≠ 0:
  B^{(i)}_j ≠ 0, w_i(B^{(i)}_j) = β_{i,j} exactly, and the height-β_{i,j} residual of
  B^{(i)}_j (image in gr_{β_{i,j}}(w_i) = P_{β_{i,j}}/P_{β_{i,j}}^+, read through the
  recorded unit normalization) equals pat_i(κ);
* **(R3) order:** ord_{ψ_i}(R_i) = μ_i (a condition on records alone, kept in the
  bundle for faithfulness to the source machine);
* **(R4) landing:** Φ_{i+1} (when i+1 < k, and the produced key of ν_{k−1} in any
  case) is the recorded successor key — a function of ν_i and the policy;
* **(R5) vertex read-off:** let (C_j) be the Φ_{i+1}-adic development of f,
  Φ_{i+1} the recorded successor key of ν_i. Then w_i(C_{μ_i}) = vhtx_i EXACTLY,
  and the height-vhtx_i residual of C_{μ_i} — its image in gr_{vhtx_i}(w_i), read
  through the recorded unit normalization — equals the recorded transported
  vertex value vtx_i. The valuation and grading are those of w_i (the CURRENT
  frame, stretch E_i): Φ_{i+1} enters only as the development key, never through
  w_{i+1}. By law (N4), vhtx_i ≤ I_i, so this read sits below the site ceiling
  like every other clause (Lemma CEIL). *(Rev-2 restatement. Rev 1 left the
  coefficient's valuation implicit, and the one natural implicit reading — the
  height pinned at the side's right-end β*_i itself — is REFUTED by the machine:
  the rev-2 falsifier found 1,644 depth-1 countermodel instances, e.g.
  f = X³ + 10X² at p = 2, whose harvested face (2,1)–(3,0) has its vertex
  coefficient at height 2 ≠ β* = 0 (§9, T-E). Recording the height and bounding
  it by law (N4) is also the faithful reading of the source machine, whose
  vertex clause reads the digit at the coefficient's OWN weight.)*

**REALIZED(f, H·ν)** := READ(f, H·ν) ∧ LAWFUL(H·ν) ∧ (no proper prefix of H·ν is
saturated — a record-only clause, §1.4). "**The machine reads site (H, ν) on f**"
:= REALIZED(f, H·ν). *(Rev-3 repair: this is THE single notion of realization in
this brief. A second audit found rev 2 silently equivocating between READ∧LAWFUL
and machine-execution realization; rev 3 uses REALIZED everywhere below, and the
identification with machine execution — the machine's harvest walk reaches exactly
the REALIZED sites — is stated and proved as Lemma REAL≡ (§2.5), from (M6a) +
(M6c), not smuggled. The new third clause is what rev 2's Note asserted without
proof: a REALIZED site includes realization of all prefix reads ((R1)–(R5)
quantify over every i), witnesses non-ns-halting of every proper prefix (the next
node's side is a principal window face, by (M6c)(ii)), and excludes saturation
halts by the record-only clause — so site-reading is exactly membership of H·ν in
the pruned run set: by definition on the record side, by REAL≡ on the execution
side.)*

### 1.4 States, windows, children, halts, trees

* A **state** o is the root state (before any read on a track) or a history. Let
  Φ_o be the state key (Φ_0 at a root state; the produced key Φ_{|H·ν|} at state
  H·ν), w_o the state frame valuation, and γ̂_o the state key height (0 at a root
  state, §1.1). The **development polygon** at o is the FULL Φ_o-adic development
  of f — slots j = 0, …, ⌊n/deg Φ_o⌋ — with the SHEARED points

      (j, u_j),   u_j := w_o(B_j) + j·γ̂_o,   for B_j ≠ 0.

  The **window width** W_o is m at a root state of a track with reduction factor
  φ̄^m (m ≥ 2 the repeated multiplicity) and μ_ν at state H·ν (the residual
  multiplicity of the last read); the **window** is the slot range 0..W_o. The
  side constraint of a read at o ((R1)) is global over ALL slots of the
  development; harvesting (next bullet) inspects the lower hull of the WINDOW
  points. That no principal face of the full polygon escapes the window — the
  coherence of these two scopes — is NOT definitional: it is the (M6c) content,
  proved at root states by Lemma ROOT-M and at non-root states by Lemma WGEO
  (§2.5). *(Rev-3 display; rev 2's "0..m-and-beyond" gloss left both the height
  convention and the confinement unstated.)*
* **Candidate children** at a REALIZED non-halted state = pairs (principal face of
  the window polygon, monic irreducible factor ψ of that face's residual
  polynomial), each yielding a node ν by harvesting the face's data (e, h, s0,
  wSide, γ, pat — read from f's own development digits, in the sheared heights
  u_j) and the policy's lift. A **principal face** is a face of the lower convex
  hull of the window points with h/e > 0 in the sheared (slot, u-height) plane
  ("negative slope"). Interface properties
  (M6a)/(M6b) of §2.4: the (R1)–(R5) data of a harvested child are read off f by
  construction of harvesting (including the vertex pair (vhtx, vtx), read from
  the slot-μ coefficient of the successor development); that these reads are
  well-defined (the vertex coefficient is nonzero) and the resulting records
  LAWFUL is the substantive half, (M6b).
* **Accumulated invariants and verdicts.** For a history H = [ν_0, …, ν_{k−1}]:
  accE(H) := e_0⋯e_{k−1}, accF(H) := d_0·g_0⋯g_{k−1}, and Dwidth(H) := deg Φ_k
  (the state key's degree). The **key-degree identity**

      accE(H)·accF(H) = Dwidth(H)

  is immediate by induction from the degree recursion
  deg Φ_{i+1} = e_i·g_i·deg Φ_i, deg Φ_0 = d_0 (§1.1). The **verdict** of a
  (τ-irr) leaf H is the pair (accE(H), accF(H)); its **verdict degree** is
  accE(H)·accF(H).
* **Halts:** (τ-irr) saturation — write **IrrHalts(H)** := the recorded identity
  accE·accF = Dwidth·μ at the last node; by the key-degree identity this is
  EQUIVALENT to μ_{k−1} = 1 (window width one); a record-only condition — the
  machine has NO children at saturated states, by definition, and the leaf's
  **irrVerdict** is the verdict pair (accE(H), accF(H)); (τ-hen) simple factors
  of f̄ are certified from the mod-p data with verdict (1, deg); (τ-ns) — write
  **NsHalts(o, f)** := o is a REALIZED non-saturated state whose window has no
  principal face on f — the ns-halt, MARKED.
* **Track partition (degree bookkeeping).** For monic f̄ ∈ 𝔽_p[X] of degree n,
  factor into distinct monic irreducibles and split by multiplicity:
  f̄ = (∏_{φ̄ simple} φ̄)·(∏_τ φ̄_τ^{m_τ}) with each m_τ ≥ 2 — the
  multiplicity-one product is the **simple part**; each repeated φ̄_τ carries
  one **track**. Taking degrees:

      n = deg(simple part) + Σ_τ m_τ·deg φ̄_τ.        (∗∗)
* A **classification tree** T: a finite prefix-closed set of chains (histories)
  per track, a Hensel payload (multiset of (1, g) verdicts), leaf verdicts, and
  ns-marks; **decided ns-free** := every maximal chain is a (τ-irr) leaf and the
  Hensel payload covers the simple part — no ns-marks. Its **type** is the
  multiset of leaf + Hensel verdicts; the **degree checksum** is
  Σ_{(e,f)} e·f over the type.
* The **fiber** of T at a level-M box x, fiber(T, x), is the conjunction:
  **(F1)** T's chains are ALL AND ONLY the REALIZED pruned runs on f_x
  (REALIZED in the single sense of §1.3);
  **(F2)** every maximal chain is a certified leaf on f_x whose kind (τ-irr; τ-ns
  is excluded here by ns-freeness) and verdict match T's records; **(F3)** T's
  Hensel payload equals the simple-factor data of f̄_x — the multiset
  {(1, deg φ̄) : φ̄ a simple factor of f̄_x}, so its degree total is
  deg(simple part of f̄_x); **(F4)** interior chains do not halt on f_x;
  **(F5)** the degree checksum is n: Σ_{(e,f) ∈ type(T)} e·f = n;
  **(F6)** per-track degree checksum: for EVERY track τ of f̄_x (repeated factor
  φ̄_τ^{m_τ}), Σ over T's leaves H on track τ of the verdict degree
  accE(H)·accF(H) equals m_τ·deg φ̄_τ — "per-track leaf degrees match the
  repeated-factor multiplicities", in displayed sum form.
* **thr(T)** := max(1, max over T's chains H of L(H)) with L(·) the read ceiling
  of §3. *(In the source machine the threshold is the join of a shape bound and a
  per-site band level; L as defined in §3 is that join's mathematical content —
  any majorant works, only "thr majorizes the tree's own ceilings" is used.)*

## 2. Three lemmas and the interface

### 2.1 Lemma DEV (development congruence). *(a/b — elementary; proof supplied)*

Let Φ be monic of degree d ≥ 1 with ℤ_p-coefficients, and B, B′ ∈ ℤ_p[X] with
B ≡ B′ (mod p^L). Then the Φ-adic developments B = Σ c_j Φ^j, B′ = Σ c′_j Φ^j
satisfy c_j ≡ c′_j (mod p^L) for all j, and all c_j are integral.

*Proof.* Division with remainder by monic Φ over ℤ_p keeps ℤ_p-coefficients and is
ℤ_p-linear in the dividend; reduction mod p^L is a ring map commuting with it
(divide B − B′ = p^L·C: quotient and remainder are p^L·(quotient/remainder of C),
by uniqueness of division by a monic polynomial over the ring ℤ_p/p^L). Induct
along the development (c_0 = remainder, recurse on the quotient). ∎

### 2.2 Lemma POS (positivity and p-stretch). *(a — MacLane; proof supplied)*

Each frame valuation satisfies: (i) w_i(B) ≥ 0 for every B ∈ ℤ_p[X];
(ii) w_i(p·B) = E_i + w_i(B); (iii) w_i(B + B″) ≥ min(w_i(B), w_i(B″)).
Consequently B ≡ B′ (mod p^L) ⟹ w_i(B − B′) ≥ L·E_i.

*Proof.* Induction on i. Order 0: Gauss valuation over v_p ≥ 0 on integral
polynomials (development coefficients are integral by Lemma DEV), and
w_0(p·B) = 1 + w_0(B), E_0 = 1. Step: w_{i+1}(B) = min_j (e_i·w_i(c_j) + j·γ_{i+1})
with c_j integral (DEV), w_i(c_j) ≥ 0 (induction), γ_{i+1} > 0 — so (i); the
development of p·B is (p·c_j)_j, and e_i·(w_i(c_j) + E_i) = e_i·w_i(c_j) + E_{i+1}
uniformly in j — so (ii); (iii) is standard for min-of-develop valuations.
The consequence: B − B′ = p^L·C with C integral, so
w_i(B − B′) = L·E_i + w_i(C) ≥ L·E_i. ∎

*Remark (updated at rev 3).* Properties (i)–(iii) of the frame maps w_i are all
that Lemmas DEV/R-LOC/NAT/CEIL, Theorem 1, and Theorem 2(a) use: for them the
w_i are just given height functions and the theorems quantify over recorded
data. Genuine multiplicativity of the §1.1 chain (it is the MacLane composite)
IS consumed at exactly one place — §2.5's window-geometry proofs — where it is
the named input (V1): proved there at degree-1 first transitions (Lemma VAL1),
cited (MacLane) beyond.

### 2.3 Lemma R-LOC (residual locality). *(a — definitional for graded residues)*

If w_i(B − B′) > β and w_i(B) ≥ β, then B and B′ have the same image in
gr_β(w_i) = P_β/P_β^+ (P_β := {C : w_i(C) ≥ β}, P_β^+ := {C : w_i(C) > β}). Any residual/digit value the
machine reads at height β — including the pattern entries of (R2) and the vertex
value of (R5), which are recorded-unit-normalized coordinates of such images —
therefore agrees between B and B′.

*Proof.* B − B′ ∈ P_β^+, so the classes coincide; normalizations are fixed
functions of the class and the records. ∎

### 2.4 The interface ledger (M1)–(M6)

The theorems below use exactly these properties of the machine; each is tagged
with its status. *(This is where any transcription to a different formalization of
the same machine must be audited — §8.)*

* **(M1)** Reads constrain f only through the clauses (R1), (R2), (R5) displayed
  in §1.3 — valuation lower bounds, exact valuation pins, and height-β graded
  residual reads on development coefficients in policy-pinned keys — plus
  record-only conditions. [Definition of READ.]
* **(M2)** = Lemmas DEV + POS + R-LOC. [PROVED above.]
* **(M3)** Every residual/digit read of a read at height β is a function of the
  gr_β-class. [Definition; = R-LOC's applicability.]
* **(M4)** Along a lawful history the frame tower (keys, valuations, residue
  fields) is a function of the records and the policy alone. [Definition of the
  frame recursion + (R4); box-free.]
* **(M5)** LAWFUL is box-free. [By construction at rev 2: CORE is displayed in
  §1.2 and mentions records only; AUX is box-free by fiat (it is a parameter
  ranging over record-chain predicates) — seam S-2.]
* **(M6a)** Harvest, definitional half: at a REALIZED non-halted state, every
  (principal face, irreducible residual factor) pair of the WINDOW polygon
  yields a harvested node whose WINDOW-SLOT read data are read off f by
  construction — (R1)/(R2) hold at the window slots because the face and its
  digits are read from f's own development, (R3) records ord_ψ exactly, (R4)
  records the policy's lift, and (R5)'s vertex pair (vhtx, vtx) is READ from
  the slot-μ coefficient of the successor development (so (R5) holds by
  definition WHENEVER that coefficient is nonzero); saturated states have no
  children. [Definition of harvesting — now GENUINELY definitional. Rev-3 note:
  rev 2's version of this tag also covered (R1) at slots BEYOND the window and
  the converse "every realized child arises from a (face, ψ) pair"; the second
  audit exposed both as substantive f-dependent claims. They are now the named
  condition (M6c), stated and proved in §2.5.]
* **(M6b)** Harvest, substantive residue: at every harvested child, (i) the
  vertex coefficient C_μ is NONZERO (the (R5) read is well-defined), (ii) the
  harvested vertex height satisfies the (N4) band β* ≤ vhtx ≤ I, and (iii) the
  harvested records satisfy AUX. ((N1)–(N3) and coherence at harvest are
  displayed facts: (N1) is read off the face; (N2)/(N3) hold because face
  endpoints are attained integer heights ≥ 0 — Lemma POS; degrees/stretches
  compose by the policy's degree law.) **Status at rev 4:** (i) and the upper
  half of (ii) — the only half any proof consumes (Lemma CEIL, (†′)) — are
  PROVED: Corollary VTX (§2.5) — outright for children harvested at ROOT states
  over degree-1 root keys under a policy standard there (rev-4 repair of two
  pass-3 findings: rev 3's ledger claimed this slice while VTX's own text
  deferred root children to the T-E check, and rev 3's "and first transitions"
  phrasing over-claimed by one level — children harvested AT first-transition
  states have their vertex law at the order-2 state, where (V1)/(V2) are
  consumed); modulo (V1)/(V2) key compliance at all other harvests (deeper
  states; root keys of degree ≥ 2; non-standard first keys);
  the unconsumed lower half of (ii) remains machine-checked only (§9 T-E); (iii)
  remains the assumption proper. Machine checks: §9 T-E (depth 1, 33,043
  instances) and T-F (depth 2, 41,720 instances), zero violations.
  Consequently (induction along runs from the root, Lemma REAL≡) machine
  execution and REALIZED coincide — displayed, no longer silent. [ASSUMPTION,
  reduced to (iii) + the cited (V1)/(V2). Used ONLY in Theorem 2(b)/Theorem 3,
  never in Theorem 1.]
* **(M6c)** Window-harvest completeness — the rev-3-exposed second interface
  condition, named and discharged: (i) harvested children satisfy (R1) at
  ALL slots of the full development (not only the window slots that harvesting
  inspects); (ii) every child read at a state (READ + (N1) — in particular
  every REALIZED child) arises from a (window face, ψ) pair with exactly the
  harvested records — in particular the window then HAS a principal face, so
  the state's non-ns-halting is a CONCLUSION of (ii), never a hypothesis.
  *(Rev-4 requantification: rev 3 guarded (M6c) by "REALIZED non-halted",
  which made its consumers circular — pass-3 critical.)* Precise
  statement, proof, and status: §2.5. [PROVED at root states (any policy, any
  root-key degree) and — under a standard first key — at first-transition
  states over degree-1 root keys; PROVED MODULO (V1)/(V2) key compliance in
  general; machine-checked at depth 2 over ALL depth-1 states, halted ones
  included, §9 T-F.]

### 2.5 Window-harvest completeness: (M6c), Lemma WGEO, realization coherence *(new at rev 3)*

Fix a monic degree-n f and a state o **on f** — meaning: o is a root state of a
track of f̄ (ord_{φ̄}(f̄) = m ≥ 2, ROOT-M's setting), or o = H·ν is a non-root
state whose creating read ν satisfies, on f and in the parent frame, (R1) at ALL
slots and (R2) at its strides. Every REALIZED state qualifies (READ restricts to
each of its reads); so does the state under any freshly HARVESTED child, whose
window clauses ((M6a)) plus (M6c)(i) at the parent supply exactly these — used
by Corollary VTX. **NO halting hypothesis enters.** *(Rev-4 requantification,
repairing the pass-3 critical: rev 3 fixed a "REALIZED non-halted" o, and its
consumers used (M6c)(ii) precisely to PROVE non-ns-halting — circular. The
halting status of o plays no role in any proof below, and the falsifier T-F
enumerated ALL depth-1 states, saturated and ns-halted included: the
requantified laws are exhaustively confirmed, §9.)* Write Φ := Φ_o (the
state key), w := w_o (the state frame valuation), γ̂ := γ̂_o (the state shear; 0
at root states), (C_j) the full Φ-development of f, u_j := w(C_j) + j·γ̂ the
sheared points, W := W_o the window width, and — at a non-root state o = H·ν —
(e, h, γ, ψ, μ = W) the creating read ν's data, with ℓ(j) = (γ − jh)/e its side
line in the PARENT frame's sheared heights.

**Condition (M6c) (window-harvest completeness).** At every state o on f as
above (no halting hypothesis):
(i) *Beyond-window support:* every harvested child ν′ of o satisfies (R1) at ALL
slots of the Φ-development: for every j > W with C_j ≠ 0, the point u_j lies
STRICTLY above ν′'s side line (window slots hold by the harvest construction,
(M6a); strictness is what (R1) demands off the recorded strides; harvested
children exist only where harvest applies — non-halted o — but that is a fact
about ν′'s provenance, not a hypothesis on o).
(ii) *No phantom:* every child ν′ at o whose chain o·ν′ satisfies READ(f, o·ν′)
and whose record satisfies (N1) — in particular every REALIZED child — arises
from a (window principal face, ψ′) pair, with records equal to that pair's
harvest. IN PARTICULAR, if such a child exists then o's window HAS a principal
face — so ¬NsHalts(o, f) is a CONCLUSION of (ii); and when ν′ is REALIZED, o is
also non-saturated (REALIZED's prefix clause), hence non-halted, and the pair
is a candidate pair in the §1.4 sense. *(Rev-4: child hypothesis weakened from
REALIZED to READ + (N1) — the proof never used more — so consumers need not
establish LAWFUL/AUX of prefixes to use (ii).)*

**Named inputs** — stated at rev 4 as KEY-COMPLIANCE conditions on the POLICY's
assigned keys (consumed ONLY at states of order ≥ 1 other than first
transitions over degree-1 root keys under a standard first key; attributions
displayed below, normalization dictionary OWED):

* **(V1) augmentation multiplicativity:** every w_i of §1.1 built over the
  policy's keys is a valuation, w_i(AB) = w_i(A) + w_i(B) — in particular
  gr(w_i) is a domain. [MacLane, Trans. AMS 40 (1936): Definition 4.1 (key
  polynomials) and Theorem 4.2 (augmented values) — loci per the pass-3
  literature check; the §1.1 chain is the MacLane composite. Proved below at
  degree-1 first transitions (Lemma VAL1). NOT a fact about arbitrary lifts:
  MacLane's theorem requires genuine key polynomials — pass-3 finding.]
* **(V2) key initial form, development identity, residual dictionary:** the
  policy's key Φ_{i+1} satisfies, in the graded ring gr(w_{i+1}):
  (a) in(Φ_{i+1}) = u·ψ̂_hom with u an invertible homogeneous monomial, and
  ψ̂_hom ∤ in(B) for EVERY nonzero B ∈ ℤ_p[X] with deg B < deg Φ_{i+1} — the
  exact divisibility block WGEO(b) consumes *(rev-4 restatement of a pass-3
  gap: rev 3's "smaller Φ_i-degree" gloss left the grading undefined and the
  membership of the in(C_k) unstated)*; (b) the
  Φ_{i+1}-development computes w_{i+1}: for every B, w_{i+1}(B) =
  min_k (w_{i+1}(C_k) + k·γ̂_i) over B's Φ_{i+1}-development — the min over the
  sheared slot heights; (c)
  ord_{ψ̂_hom}(in(f)) = ord_{ψ_i}(R_i(f)) — the residual polynomial computes
  ψ-order of the initial form — whenever the creating read's (R1)/(R2) hold on
  f. [GMN, Trans. AMS 364 (2012): the representative construction (Prop. 2.10 /
  Thm. 2.11) and the §2.6 Theorem of the product — loci per the pass-3
  literature check; proved below at degree-1 first transitions for the standard
  lift (Lemmas KEY1, DIV1).]
* **Status (rev-4 honesty downgrade, per pass 3):** (V1)/(V2) are NOT
  citation-grade as bundled — GMN's types, representatives, v_r, admissible
  developments, and residual operators are not, by citation alone, identified
  with this package's (w_i, γ̂_i, Φ_i) normalization and gr-divisibility. That
  translation is an OWED, explicit open correspondence (seam S-4). (V1)/(V2)
  are consumed as named ASSUMPTIONS on the policy's keys, proved here only on
  the displayed perimeter (standard lift over degree-1 root keys).

**Lemma ROOT-M (root confinement).** *(b — elementary; proof displayed)* At a
root state of a track with reduction factor φ̄^m (m ≥ 2, so ord_{φ̄}(f̄) = m
exactly): w_0(B_j) ≥ 1 for j < m and w_0(B_m) = 0; consequently every principal
face of the (unsheared, γ̂ = 0) root polygon lies in slots [0, m], and every
point at a slot j > m lies strictly above every principal face's extended line.

*Proof.* The Φ_0-development reduces mod p to the φ̄-adic development of f̄
(Lemma DEV with L = 1), and ord_{φ̄}(f̄) = m means exactly: the φ̄-digits of f̄
below slot m vanish (w_0(B_j) ≥ 1, j < m) and the slot-m digit does not
(w_0(B_m) = 0). Faces: heights are ≥ 0 (POS) and the point (m, 0) is at the
floor, so the lower hull is non-decreasing from slot m on; a strictly descending
face touching a slot > m would need a point of height < 0. Beyond-window: a
principal face F ⊆ [0, m] has ℓ_F(m) ≤ 0 (its extended line lies on or below
the hull to its right, and hull(m) = 0), so for j > m: ℓ_F(j) < ℓ_F(m) ≤ 0 ≤
w_0(B_j), strictly. ∎

**Lemma VAL1 (first-transition valuation, degree-1 root key).** *(a/b — proof
displayed)* Let d_0 = deg Φ_0 = 1 and ν_0 a root read with side (e, h). Then
w_1(B) = min_t (e·v_p(b_t) + t·h) over the Φ_0-monomial expansion B = Σ b_t Φ_0^t,
and w_1 is a valuation. Its graded ring is gr(w_1) = 𝔽_p[x̄, p̄] (x̄ := in(Φ_0),
p̄ := in(p)), a UFD, with the weighting wt(p̄) = e, wt(x̄) = h.

*Proof.* The formula is §1.1's recursion at i = 0 (γ_1 = e·w_0(Φ_0) + h = h).
Multiplicativity: w_1 is the (e, h)-weighted Gauss valuation in the variable
Φ_0; on products, min-weights add because 𝔽_p[x̄, p̄] is a domain: the
weight-w_1(A) initial form in(A) := Σ over minimizing (t, s) of
(s-th p-digit of b_t)·x̄^t·p̄^s is nonzero, and in(A)·in(B) ≠ 0 is the initial
form of AB at weight w_1(A) + w_1(B) (weighted Gauss lemma). ∎

**Lemma KEY1 (key initial form, degree-1 root key, STANDARD lift).** *(b —
proof displayed)* In the setting of VAL1, with ψ of degree g (ord_ψ(R_0) = μ)
and the **standard key lift** — an explicit HYPOTHESIS on the policy's choice
(rev-4 flag; a policy assigning it is *standard* at this node, §1.1) —
Φ_1 = Σ_κ ψ̂_κ p^{(g−κ)h} Φ_0^{eκ} (ψ̂_κ any fixed integer lifts of ψ's
coefficients, ψ̂_g = 1): every monomial of Φ_1 has w_1-weight exactly
egh, so Φ_1 is w_1-homogeneous with γ̂_0 = w_1(Φ_1) = egh, and

    in(Φ_1) = ψ_hom := Σ_κ ψ̄_κ x̄^{eκ} p̄^{(g−κ)h},

the (e, h)-homogenization of ψ. ψ_hom is irreducible in 𝔽_p[x̄, p̄], and a
nonzero homogeneous element of x̄-degree < eg is not divisible by ψ_hom;
consequently, for every nonzero B ∈ ℤ_p[X] with deg B < eg = deg Φ_1, in(B) is
a sum of monomials x̄^t p̄^s with t ≤ deg B < eg, so ψ_hom ∤ in(B) — the exact
form (V2a) that WGEO(b) consumes (rev-4 bridge sentence).
Moreover ord_{ψ_hom}(in(f)) = μ.

*Proof.* Weights: e·(g−κ)h + eκ·h = egh for every κ. Irreducibility: c(y) ↦ its
(e, h)-homogenization (y := x̄^e p̄^{−h}) is multiplicative from 𝔽_p[y] to
homogeneous elements; a factorization of ψ_hom into homogeneous factors
descends to one of ψ (gcd(e, h) = 1 matches x̄- and p̄-degrees to y-degrees) up
to monomial factors, and monomials are excluded: x̄ ∤ ψ_hom (the κ = 0 term
ψ̄_0 ≠ 0 = pat-constant of an irreducible factor of R_0 with R_0(0) ≠ 0 — (N1)
gives pat(0) ≠ 0, so ψ ≠ z and ψ̄_0 ≠ 0) and p̄ ∤ ψ_hom (the κ = g term is
x̄^{eg}). Degree block: ψ_hom·(homogeneous) has x̄-degree ≥ eg. Initial form of
f: by the root read's (R1)/(R2), the w_1-minimizing monomials of f are exactly
the stride digits of the side, and their digit values are pat — so
in(f) = x̄^{s0}·p̄^{β*}·R_hom (R_hom the homogenization of the residual
polynomial R_0), whence ord_{ψ_hom}(in f) = ord_ψ(R_0) = μ. ∎

**Lemma DIV1 (development identity, degree-1 root key).** *(b — proof
displayed)* In the setting of KEY1, the Φ_1-development f = Σ_k C_k Φ_1^k
satisfies w_1(C_k Φ_1^k) = w_1(C_k) + k·egh = u_k ≥ w_1(f) for every k, and
w_1(f) = min_k u_k.

*Proof.* Division bound: for any A and the division A = Q·Φ_1 + B (Φ_1 monic of
degree D = eg), perform the division Φ_0-ADICALLY — d_0 = 1, so X-degree and
Φ_0-degree coincide, Φ_0-expansions A = Σ_t b_t Φ_0^t have integral b_t, and
the Φ_0-adic division IS the unique X-division. Induct on the top slot d: the
top reduction step subtracts b_d·Φ_0^{d−D}·Φ_1, whose every monomial
b_d·ψ̂_κ p^{(g−κ)h}·Φ_0^{d−D+eκ} has w_1-weight e·v_p(b_d·ψ̂_κ p^{(g−κ)h})
+ (d−D+eκ)h ≥ e·v_p(b_d) + dh ≥ w_1(A) (the middle step: e(g−κ)h + (d−D+eκ)h =
dh using D = eg), and the top slot cancels (ψ̂_g = 1), so the remainder chain
keeps w_1 ≥ w_1(A) *(rev-4 repair of a pass-3 gap: rev 3 wrote the reduction
step as a_d·X^{d−D}·Φ_1, which is not weight-graded when the policy's root key
is Φ_0 = X − a ≠ X; the Φ_0-adic form is, and is the same division)*; hence
w_1(B) ≥ w_1(A) and
w_1(Q) ≥ w_1(A) − egh (the same computation, one Φ_1-slot up). Iterating along
the development gives u_k ≥ w_1(f); the ultrametric inequality (POS(iii)) gives
w_1(f) ≥ min_k u_k. ∎

**Lemma WGEO (window geometry).** Let o be a non-root state on f as above —
the creating read ν satisfies (R1) at all slots and (R2) at its strides on f;
NO halting or full-REALIZED hypothesis (rev-4 requantification: this weaker
hypothesis is all the proof uses, and it is what Corollary VTX's fresh-harvest
application supplies). Then, with γ the creating read's side value:

* (a) u_k ≥ γ for every k with C_k ≠ 0, and w(f) = γ;
* (b) min_k u_k = γ, attained at k = μ and at NO k < μ — FIRST attainment
  (rev-4 flag, per pass 3: u_k = γ at slots k > μ is neither excluded nor
  needed; (c)/(d) consume only first attainment, and T-F checks exactly that);
  in particular C_μ ≠ 0;
* (c) every face of the window hull (slots ≤ μ) has strictly negative slope;
  the window hull descends to the right-edge vertex (μ, γ); and the principal
  part of the FULL polygon coincides with the window hull;
* (d) every point at a slot k > μ lies strictly above every window face's
  extended line.

Status: PROVED OUTRIGHT when o is a first-transition state over a degree-1 root
key with the STANDARD first key (via VAL1/KEY1/DIV1 — the standard-lift
hypothesis is KEY1's, rev-4 policy scoping); PROVED MODULO (V1)/(V2) key
compliance in general (the proof below
consumes exactly their clauses). Machine-checked exhaustively at depth 2 (§9
T-F: 41,720 instances, zero violations of (a)–(d)).

*Proof.* Throughout, w = w_{i+1} is the state valuation, in(·) initial forms in
gr(w), and ψ̂_hom = in(Φ) up to unit monomial ((V2a)/KEY1).

(a) First, w(f) = γ is DISPLAYED from the parent read, at every order: by §1.1,
w(f) = min_j (e·w_i(B^{(i)}_j) + j·γ_{i+1}) = min_j (e·u^{(i)}_j + j·h) over the
parent development, and (R1) gives e·u^{(i)}_j + j·h ≥ e·ℓ(j) + j·h = γ with
equality exactly at the side's touching strides, which (R2) makes nonempty. The
per-slot bound u_k ≥ w(f) is the development identity ((V2b)/DIV1).

(b) Let S_0 := {k : u_k = γ} (nonempty by (a)). The graded piece of f at weight
γ is in(f) = Σ_{k∈S_0} in(C_k)·in(Φ)^k (term-wise weights add by (V1)/VAL1),
and it is nonzero (else w(f) > γ). Each C_k is nonzero with deg C_k < deg Φ,
hence ψ̂_hom ∤ in(C_k) ((V2a)/KEY1's degree block, in its displayed
deg-B < deg-Φ form). Write m := min S_0, in(Φ)^k = u_k′·ψ̂_hom^k (u_k′
invertible monomials, (V2a)), and factor:

    in(f) = ψ̂_hom^m · β,   β := Σ_{k∈S_0} in(C_k)·u_k′·ψ̂_hom^{k−m}.

Then ψ̂_hom ∤ β: otherwise ψ̂_hom would divide the k = m term in(C_m)·u_m′
(every other summand carries a positive power of ψ̂_hom), hence divide in(C_m)
(u_m′ invertible) — excluded. So ψ̂_hom^m ∣ in(f); and ψ̂_hom^{m+1} ∤ in(f):
from ψ̂_hom^{m+1}·δ = ψ̂_hom^m·β, cancel ψ̂_hom^m — gr(w) is a domain, (V1) —
to get ψ̂_hom·δ = β, excluded. Hence ord_{ψ̂_hom}(in f) = m exactly. *(Rev-4
repair of a pass-3 gap: rev 3 said the bracket is "unit-plus-multiple-of-
ψ̂_hom" — not-divisible does not mean unit; the argument above uses only
non-divisibility and domain cancellation, no primeness, no unit status.)*
By ((V2c)/KEY1), ord_{ψ̂_hom}(in f) =
ord_ψ(R) = μ. Hence min S_0 = μ: u_μ = γ (so C_μ ≠ 0) and u_k > γ for k < μ.

(c) By (b) the window points have u_k > γ for k < μ and u_μ = γ: every window
hull face has its right endpoint strictly below its left (convexity: slopes
increase left to right and the minimum sits at the right edge, attained only
there) — all faces strictly descend. Full polygon: u_k ≥ γ = u_μ for ALL k, so
the full lower hull is non-decreasing from slot μ on; its strictly-descending
part lies in slots [0, μ] and, on [0, μ], hull-of-all-points = hull-of-window-
points (points beyond μ, all at height ≥ the value at μ of any candidate face,
cannot cut below the window hull there: a face of the full hull over [0, μ]
with an endpoint beyond μ would descend to a height < γ at its right end,
impossible).

(d) A window face F ⊆ [a, b] (b ≤ μ) has ℓ_F(μ) ≤ hull(μ) = γ (its extended
line lies on or below the hull to its right, by increasing slopes), and ℓ_F is
strictly decreasing (F principal: h_F/e_F > 0 by (c)); so for k > μ:
ℓ_F(k) < ℓ_F(μ) ≤ γ ≤ u_k. ∎

**Corollary VTX (vertex laws; (M6b)(i) and (N4)-upper discharged).** Let ν′ be
a child harvested at ANY state o on f, and o′ := o·ν′ the child state. WGEO's
hypothesis holds at o′ — ν′'s (R1) at window slots and (R2) at strides by the
harvest construction ((M6a)), (R1) at beyond-window slots by (M6c)(i) AT o
(ROOT-M when o is a root state; WGEO(d) at o otherwise) — so WGEO applies at
o′: with (C_k) the development of f in ν′'s produced key and (e′, h′, γ′, μ′)
ν′'s data, C_{μ′} ≠ 0, and the sheared vertex height is PINNED exactly:
u_{μ′} = w_{o′}(C_{μ′}) + μ′·γ̂_o′ = γ′. Consequently vhtx′ (the (R5) record —
the vertex coefficient's own frame height w_o(C_{μ′}), cf. §1.3) satisfies
vhtx′ ≤ I′. For ν′ harvested at a ROOT state over a degree-1 root key,
displayed —
e·vhtx = e·w_0(C_μ) ≤ w_1(C_μ) = γ − μ·γ̂_0 ≤ γ, i.e. vhtx ≤ γ/e = I
(the first inequality: w_1(C_μ) = min_t (e·v_p(c_t) + t·h) ≥
e·min_t v_p(c_t) = e·w_0(C_μ), the last equality definitional at
d_0 = 1; here (e, h, γ, μ) are ν′'s own data). At deeper harvests the same
chain needs e_i·w_i(C_{μ′}) ≤ w_{i+1}(C_{μ′}), i.e. that C_{μ′}'s
Φ_i-development
computes w_i from below — the development identity (V2b) at level i, part of
the cited perimeter, NOT of POS.
**Perimeter (rev-4 correction of two pass-3 findings):** the kernel is PROVED
OUTRIGHT exactly for children harvested at ROOT states over degree-1 root keys
under a standard first key — there WGEO at o′ runs on VAL1/KEY1/DIV1 and
(M6c)(i)-at-o is Lemma ROOT-M, everything displayed. Rev 3 both claimed this
slice ("outright at root states") in its ledgers AND deferred it to the T-E
check in this corollary's text — contradictory labeling, now resolved: it is
PROVED, and T-E stands as its exhaustive machine corroboration (33,043
instances). Rev 3's "and first transitions over degree-1 root keys" phrasing
over-claimed by one level: a child harvested AT a first-transition state has
its vertex law at the ORDER-2 state o′, whose WGEO consumes (V1)/(V2) at level
≥ 1 — inside the cited perimeter, not outright. The
UNCONSUMED lower half of the (N4) band stays with (M6b)(ii). *(So the checkable
kernel of (M6b) is now derived where WGEO applies; what (M6b) still asserts is
the lower band and AUX.)*

**Proof of (M6c).** (i) Within-window slots: harvest construction ((M6a)).
Beyond-window slots: Lemma ROOT-M (root states) / WGEO(d) (non-root states)
give STRICT inequality above every window face's line at every slot > W with
C_j ≠ 0 — which is (R1) there (no stride slots of the child's side lie beyond
the face, so no equality is permitted or needed). (ii) Let ν′ be a
child at o with READ(f, o·ν′) and (N1) — the rev-4 hypothesis; note the proof
below uses ONLY the child's (R1), (R2), (R3), (R5) and (N1), never LAWFUL, AUX,
prefix clauses, or any halting status of o. Say its side is [s0, s0+wSide],
line ℓ′. By (R1) on f, ℓ′ supports ALL
points (u_j ≥ ℓ′(j) everywhere); by (R2) + (N1) (pat(0) ≠ 0, pat(wSide/e) ≠ 0)
BOTH endpoints are touched: u = ℓ′ exactly there. A supporting line touching
two slots, with all points on or above it, makes [s0, s0+wSide] part of the
lower hull, lying inside ONE face F of the hull (faces have distinct slopes);
F's slope is ν′'s −h′/e′ < 0, so F is principal, and F ⊆ [0, W] (ROOT-M /
WGEO(c)). F cannot be larger than the side: an endpoint of F outside
[s0, s0+wSide] would be a touching slot that is not a recorded stride with
nonzero pattern — forbidden by (R1)'s "equality only at strides". So the side
IS the face F: (e′, h′) is F's primitive slope pair (coprimality pins it),
wSide its width, γ′ its line value, and — by (R2) — pat′ is exactly F's digit
pattern; ψ′ is a monic irreducible with ord_{ψ′}(R_F) = μ′ ≥ 1 ((R3)/(N1)),
i.e. a factor of F's residual polynomial; and the vertex pair agrees — ν′'s
(R5) and the (F, ψ′)-harvest both read (vhtx, vtx) off the SAME slot-μ′
coefficient of f's development in the policy-pinned produced key ((R4)), (R5)'s
exact height pin making that coefficient nonzero (rev-4 sentence: the record
match includes the vertex data). Hence ν′'s records are exactly the
(F, ψ′)-harvest; in particular o's window HAS the principal face F, so
¬NsHalts(o, f) — the displayed conclusion — and when ν′ is REALIZED, o is also
non-saturated (prefix clause), hence non-halted, making (F, ψ′) a candidate
pair in the §1.4 sense. ∎

**Lemma REAL≡ (realization coherence).** Assume (M6a), (M6b)(i)–(iii), (M6c).
Then for every f and every site (H, ν): the machine's execution walk (start at
a track's root state; at each REALIZED non-halted state harvest all candidate
children per (M6a); halt at saturation/ns) visits H·ν if and only if
REALIZED(f, H·ν).

*Proof.* (⟸) Write o_0 (the root state), o_1, …, o_k = the state of H·ν for
the prefix states, ν_j the node extending o_j. Induct on j: the walk visits
o_{j+1} given it stands at o_j. First, o_j is non-saturated — for j < k its
chain is a proper prefix of H·ν, so REALIZED's record-only clause applies.
Second, o_j is not ns-halted: the extending node ν_j satisfies READ(f, o_j·ν_j)
— READ(f, H·ν) quantifies over EVERY read i < k, so each prefix chain's READ
holds — and (N1) (CORE's per-node laws restrict to prefixes); (M6c)(ii), whose
child hypothesis is exactly READ + (N1) and which carries NO halting hypothesis
on o_j — the rev-4 requantification; rev 3's proof was circular precisely here,
invoking a lemma quantified over non-halted states to prove non-halting —
exhibits ν_j's side as a principal face of o_j's window, so NsHalts(o_j, f)
fails. Hence o_j is non-halted; and o_j is itself REALIZED for j ≥ 1 (READ and
CORE restrict to prefixes, AUX by its displayed prefix closure (§1.2), prefix
non-saturation is inherited) — so the walk, standing at the REALIZED non-halted
state o_j, harvests ALL candidate pairs ((M6a) totality), among them the pair
from (M6c)(ii), a genuine candidate pair with records exactly ν_j's:
the walk visits o_{j+1}. (⟹) Induction along the walk: a
harvested child satisfies full READ ((M6a) window clauses + (M6c)(i) beyond-
window + (M6b)(i)/Corollary VTX for (R5)) and is LAWFUL ((N1)–(N3) displayed at
harvest;
(N4) by Corollary VTX plus (M6b)(ii)'s lower half; AUX by (M6b)(iii)); its
prefixes are non-saturated because the walk only extends non-halted states.
∎ *(This is the displayed replacement for rev 2's silent "every realized
pruned run is LAWFUL"; note it consumes the lower (N4) band — the one place
that half is used.)*

## 3. The read ceiling

For a nonempty history H with reads ν_0, …, ν_{k−1}:

    I_i := ℓ_i(0) = γ_i / e_i           (the side line's value at slot 0),
    L(H) := 1 + max_{i<k} ⌈ I_i / E_i ⌉    ∈ ℕ,    L(root state) := 1.

**Lemma NAT (the ceiling is a positive integer).** For every LAWFUL nonempty H:
each I_i ≥ 1 — by (N3), γ_i ≥ (s0_i + wSide_i)·h_i ≥ wSide_i ≥ e_i (using
h_i ≥ 1 and e_i ∣ wSide_i, wSide_i ≥ 1), so I_i = γ_i/e_i ≥ 1 — hence
⌈I_i/E_i⌉ ≥ 1 (E_i ≥ 1), and L(H) = 1 + max_i ⌈I_i/E_i⌉ ≥ 2 is a well-defined
positive integer; L(root state) = 1. ∎ *(This is where (N3) earns its place:
without it a recorded γ ∈ ℤ could drive L(H) ≤ 0 and the modulus p^{L} of
Theorem 1 would be ill-formed. (N3) excludes only READ-unrealizable records —
§1.2.)*

**Lemma CEIL (clause-height audit).** Every f-dependent constraint of read i lies
at w_i-height ≤ I_i, hence at de-normalized level < L(H): (R1) constrains
w_i(B_j) against β_{i,j} = ℓ_i(j) − j·γ̂_{i−1} ≤ ℓ_i(j) ≤ ℓ_i(0) = I_i
(h_i > 0, j ≥ 0, γ̂_{i−1} ≥ 0); constraints with
β_{i,j} < 0 are vacuous by POS(i); (R2) pins heights β_{i,s0+eκ} ≤ I_i; (R5) pins
w_i(C_{μ_i}) = vhtx_i and reads the height-vhtx_i residual, with vhtx_i ≤ I_i by
law (N4), on a development in the pinned key Φ_{i+1}. ∎ *(This is the whole
content of the audit; the machine has no other f-dependent clause, by (M1).)*

## 4. Theorem 1 (lawful-site read locality — the "D-14" statement). *(c)*

**Theorem 1.** Let (H, ν) be any LAWFUL site and L := L(H·ν). Let f, f′ be monic
degree-n polynomials over ℤ_p with f ≡ f′ (mod p^L). Then

    the machine reads (H, ν) on f   ⟺   the machine reads (H, ν) on f′.

In particular, for boxes x (level M ≥ L) and x′ (level M′ ≥ L) agreeing below
level L: the machine reads (H, ν) on f_x iff on f_{x′} — the verdict is determined
by the digits below level L, uniformly over working levels ≥ L. The quantifier is
over ALL lawful sites: (H, ν) is NOT assumed realized on any run.

*Proof.* LAWFUL(H·ν) is shared (box-free, (M5)), and so is the third clause of
REALIZED — prefix non-saturation is record-only (§1.3) — so "the machine reads
the site" (= REALIZED) reduces to READ on both sides *(rev-4 sentence, closing
a pass-3 gap: rev 3 transferred READ without noting the reduction)*. It
suffices to transfer
READ(f, H·ν) ⟹ READ(f′, H·ν); the converse is symmetric. Fix a read i. By (M4)
the key Φ_i and valuation w_i are the same for f and f′. Let (B_j), (B′_j) be the
Φ_i-developments; by DEV, B_j ≡ B′_j (mod p^L), so by POS,

    w_i(B_j − B′_j) ≥ L·E_i > I_i ≥ every constrained height of read i     (†)

(the strict middle inequality: I_i/E_i ≤ ⌈I_i/E_i⌉ ≤ L − 1 < L). The slot shear
j·γ̂_{i−1} of §1.3's clauses is a record function ((M4)), identical for f and
f′, so every sheared-height comparison reduces to the bare coefficient heights
w_i(B_j) against the pulled-back thresholds β_{i,j} ≤ I_i (Lemma CEIL). Now
check each clause for f′:

* (R1) at slot j: if B′_j = 0 the clause is vacuous. If B′_j ≠ 0 and B_j ≠ 0:
  by (†) and ultrametricity, for every threshold β ≤ I_i: w_i(B_j) ≥ β ⟺
  w_i(B′_j) ≥ β, and w_i(B_j) = β ⟺ w_i(B′_j) = β; thresholds β_{i,j} > I_i do
  not occur, and β_{i,j} < 0 is vacuous by POS. So the support inequality and the
  equality-only-at-strides pattern transfer. If B′_j ≠ 0 but B_j = 0: then
  w_i(B′_j) ≥ L·E_i > I_i ≥ β_{i,j} by (†), so the strict inequality holds at j and
  no forbidden equality occurs.
* (R2) at a stride slot j: w_i(B_j) = β_{i,j} ≤ I_i < L·E_i, so by (†)
  w_i(B′_j) = β_{i,j} exactly and B′_j ≠ 0; by R-LOC (w_i(B_j − B′_j) > β_{i,j})
  the height-β_{i,j} residuals agree, so the recorded pattern value is read
  identically.
* (R3), (R4): record-only / policy-pinned — shared.
* (R5): Φ_{i+1} is pinned by (M4) and monic. Let (C_j), (C′_j) be the
  Φ_{i+1}-adic developments of f, f′; by DEV (applied with Φ = Φ_{i+1}),
  C_j ≡ C′_j (mod p^L), so by POS

      w_i(C_j − C′_j) ≥ L·E_i > I_i ≥ vhtx_i          (†′)

  — the Φ_{i+1}-analogue of (†), rederived rather than reused: DEV and POS apply
  verbatim to the monic key Φ_{i+1} while the heights stay measured in w_i, as
  (R5) prescribes (§1.3); (†) itself was stated for the Φ_i-development and is
  NOT invoked here. The last inequality of (†′) is law (N4). Since
  w_i(C_{μ_i}) = vhtx_i ≤ I_i < L·E_i, ultrametricity and (†′) give
  w_i(C′_{μ_i}) = vhtx_i exactly, and R-LOC (w_i(C_{μ_i} − C′_{μ_i}) > vhtx_i)
  transfers the height-vhtx_i residual; the recorded vertex value vtx_i is read
  identically.

All clauses of every read transfer; READ(f′, H·ν) holds. ∎

**Remark 1 (noncircularity).** The proof never inspects the run of f or f′ — the
site supplies its own keys and heights through its records ((M4)). This is what
makes the lawful-site quantifier available to a no-missing argument: locality is a
theorem about the SITE, not about the realized tree of any particular polynomial.

**Remark 2 (two-tier reading).** Theorem 1 is the thr-tier: L(H, ν) is
tree-intrinsic (computable from the node data). The δ-tier (modulus δ + 1,
δ = v_p(disc f)) is NOT claimed and NOT derivable from Theorem 1; it is a separate
statement requiring execution transport and the engine↔OM dictionary, out of scope
here by design.

## 5. Theorem 2 (O-1(thr): realized tier + window closure). *(c)*

**Theorem 2(a) (realized-site two-lift comparison).** Let x be a box with
REALIZED(f_x, H·ν) (the single notion of §1.3 — no "canonical run" enters), and
let L := L(H·ν). For every box x′ at any working level M′ ≥ L agreeing with x
below level L: REALIZED(f_{x′}, H·ν); and conversely. Uniformly over working
levels ≥ L.

*Proof.* READ ∧ LAWFUL transfers by Theorem 1; REALIZED's third clause (prefix
non-saturation) is record-only, hence shared. ∎ *(Rev-3 note, repairing the
audit's conditionality finding: as restated, 2(a) is an unconditional — indeed
nearly tautological — restriction of Theorem 1, and the §8 row now says exactly
that. Identifying REALIZED with the machine's execution walk is Lemma REAL≡
(§2.5) and costs (M6a)/(M6b)/(M6c); rev 2's wording "the canonical run realizes
the site" hid that choice behind an undefined "canonical" — purged here.)*

**Theorem 2(b) (window closure, "K2").** Let T be a decided ns-free tree,
t := thr(T), N ≥ t. Let x be a level-M box (M ≥ N) with fiber(T, x), and x′ a
level-M′ box (M′ ≥ N) agreeing with x below level N. Then at EVERY state o of T
(a root state of a track, or an interior chain), the set of REALIZED children
(§1.3) on f_{x′} at o equals the set on f_x at o, and both equal T's recorded
roster at o. In particular deep candidate children (sites with ceiling > N) are
excluded at ALL boxes agreeing with x below level N — not merely not transported.

The proof needs one lemma, of independent interest: on a decided fiber every
window is fully spanned by the recorded reads.

**Lemma SPAN (full-span ledger).** *(b — the elementary bookkeeping underlying
GMN's f-complete degree additivity, re-proved here for the machine's records.)*
Let fiber(T, x) hold with T decided ns-free. Then at every non-saturated state o
of T:
(i) the recorded children's sides span the full window: the union of their slot
intervals [s0, s0 + wSide] is [0, W_o] (W_o = the window width: the repeated
multiplicity m at a root state, μ of the parent read otherwise);
(ii) consequently the leftmost recorded side has s0 = 0, so slot 0 carries an
exact pin: w_o(B_0) = its ℓ(0) ≤ (L(that site) − 1)·E_o < t·E_o.

*Proof.* Define the weight of a state o as wt(o) := deg Φ_o · W_o. Two ledger
identities, both definitional in the records:

* **(W-ADD)** For one face of width wSide and slope denominator e, the residual
  polynomial has degree wSide/e, so Σ over its irreducible factors ψ (with
  multiplicity μ_ψ = ord_ψ) of g_ψ·μ_ψ = wSide/e. A child (face, ψ) has
  wt(child) = deg Φ_{o}·e·g_ψ · μ_ψ (key degree multiplies by e·g, window width
  becomes μ_ψ). Hence Σ over children on ONE face of wt = deg Φ_o · wSide, and
  Σ over ALL recorded children of wt = deg Φ_o · (total recorded span) ≤ wt(o),
  with deficit deg Φ_o·(W_o − span) ≥ 1 whenever the span is proper. (Faces of
  one polygon have disjoint slot interiors, so spans add; and every principal
  face lies inside the window [0, W_o] — Lemma ROOT-M at root states, Lemma
  WGEO(c) otherwise — so the total span is ≤ W_o, which is what ≤ wt(o) uses.)
* **(L-SAT)** At a (τ-irr) leaf H: verdict degree = accE(H)·accF(H) =
  Dwidth(H) = deg Φ_H — the key-degree identity of §1.4 — and the saturation
  clause accE·accF = Dwidth·μ_H then forces μ_H = 1, so
  verdict degree = deg Φ_H = deg Φ_H·μ_H = wt(leaf). Every equality here is a
  §1.4 definition or the displayed key-degree identity; nothing is read off any
  true factorization of f.

*Roster totality (where (M6a)/(M6b)/(M6c) enter).* At every fibered
non-saturated state o, the recorded children are EXACTLY the candidate
(face, ψ) pairs of f's window polygon, each with its exact multiplicity
μ_ψ = ord_ψ ((R3)). Candidate ⟹ recorded: the harvested child satisfies FULL
READ — window clauses by (M6a), beyond-window (R1) by **(M6c)(i)**, the (R5)
vertex read well-defined by (M6b)(i)/Corollary VTX — and is LAWFUL ((N1)–(N3)
displayed at harvest, (N4) by VTX + (M6b)(ii), AUX by (M6b)(iii)); its prefixes
are non-saturated chains of T (interior states of a decided tree are not
leaves), so REALIZED holds, and (F1) all-and-only makes its pruned run a chain
of T — recorded. Recorded ⟹ candidate: a recorded child is REALIZED by (F1) and
arises from a (window face, ψ) pair carrying exactly the harvested records by
**(M6c)(ii)**. So the per-face sums in (W-ADD) run over ALL irreducible factors
of each face's residual polynomial, and the all-faces sum runs over ALL
principal faces of ONE lower polygon, all confined to the window (ROOT-M /
WGEO(c)) — whence the disjoint interiors and the span accounting used above.

By induction on the subtree below o (finite, T decided): the total verdict degree
of the leaves below o is ≤ wt(o), with equality iff every state weakly below o has
full span. [Leaves: (L-SAT), equality. Interior: Σ over children of (subtree
totals) ≤ Σ wt(children) ≤ wt(o) by (W-ADD), deficits accumulating.]

Now sum over the tree. Per track of the reduction f̄_x with repeated factor
φ̄^{m}: the root state's weight is wt(root) = deg Φ_0·W = m·deg φ̄ (window width
W = m, deg Φ_0 = deg φ̄), and (F6) — in its displayed sum form, §1.4 — says
Σ over the track's leaves of verdict degree = m·deg φ̄ = wt(root): the track
subtree's verdict total equals its root weight, forcing EQUALITY in the
induction, hence full span at every state of the track. (Alternative route,
(F3) + (F5) + the track partition (∗∗) of §1.4: Σ over ALL tracks of the
leaf-degree totals = n − (Hensel payload degree) [(F5), splitting type(T) into
leaf verdicts and Hensel payload] = n − deg(simple part of f̄_x) [(F3)]
= Σ_τ m_τ·deg φ̄_τ [(∗∗)] = Σ_τ wt(root_τ); each track total is ≤ its root
weight by the induction, and the totals sum to equality, so EVERY track total
equals its root weight. Either route uses only displayed fiber clauses and
displayed degree identities.) This proves (i).

(ii): with span reaching slot 0, the leftmost recorded side has s0 = 0 and pat
0 ≠ 0, so (R2) pins w_o(B_0) = ℓ(0) = I ≤ (L − 1)·E_o where L is that recorded
site's ceiling; L ≤ t (thr majorizes the tree's own sites), so
w_o(B_0) ≤ (t − 1)·E_o < t·E_o. ∎

*Proof of Theorem 2(b).* The state o itself is REALIZED on both decodes: o's
chain has ceiling ≤ t ≤ N, and Theorem 2(a) transfers REALIZED from x to x′.

(⊇, recorded ⊆ REALIZED at both): each recorded child's site has ceiling
≤ t ≤ N; it is REALIZED at x by fiber clause (F1); Theorem 2(a) transfers it
to x′.

(⊆): let ν′ be a REALIZED child on f_{x′} at o (if o is saturated there are
none, on either side, by the DEFINITION of REALIZED — its prefix-non-saturation
clause — matching the empty recorded roster; rev 2 routed this through (M6a)).
Two cases.

*Case 1: L(o·ν′) ≤ N.* Theorem 2(a) applies directly — REALIZED includes
LAWFUL by definition (§1.3; rev 2 obtained lawfulness through an implicit
realized ⟹ harvested step, which is (M6c)(ii)'s content and is no longer
needed here) — and transfers REALIZED(o·ν′) to f_x; by (F1) all-and-only,
o·ν′ is a chain of T — recorded. ((F4) is consistency, not an input: interior
chains of T do not halt on f_x.) ∎(case)

*Case 2: L(o·ν′) > N ("deep").* We show this cannot occur. By Lemma SPAN(ii) at
x: w_o(B_0) = β_0 < t·E_o ≤ N·E_o. Since x′ agrees with x below N, Lemma DEV +
POS give w_o(B_0 − B′_0) ≥ N·E_o > β_0, so w_o(B′_0) = β_0 as well (ultrametric).
The REALIZED child ν′ satisfies (R1) on f_{x′}, whose side line ℓ′ must support
ALL sheared development points, in particular slot 0, where the shear vanishes:
I(ν′) = ℓ′(0) ≤ u′_0 = w_o(B′_0) = β_0.
By SPAN(ii), β_0 ≤ (t − 1)·E_o, so ⌈I(ν′)/E_o⌉ ≤ t − 1. The reads of o itself
are recorded, with ⌈I/E⌉ ≤ t − 1 each (thr majorizes them). Hence
L(o·ν′) = 1 + max(⌈I/E⌉ over all reads of o·ν′) ≤ t ≤ N — contradicting
deepness. ∎

**Remark 3 (where each hypothesis bites).** Decidedness + ns-freeness enter ONLY
through Lemma SPAN (a window with an unspanned left segment — e.g. an ns-halt
state, or an undecided deep side — voids the slot-0 pin, and the Eisenstein
family of §7 shows the conclusion then genuinely fails). (M6a), (M6b) and (M6c)
enter ONLY through Lemma SPAN's roster totality (each cited at its displayed
step there); the saturated-state emptiness and the lawfulness of REALIZED
children are now definitional in REALIZED (§1.3); Theorem 1/2(a) does all
transport. Reading the fiber clauses as statements about the machine's
EXECUTION additionally costs Lemma REAL≡ ((M6a)+(M6b)+(M6c)).

## 6. Theorem 3 (the cylinder law "D-15" + the mass/count tie). *(c)*

Throughout: T decided ns-free, t := thr(T), fibers per §1.4.

**Theorem 3.** (a) **(CYL)** For all N ≥ t, all working levels M, M′ ≥ N, and all
boxes x (level M), x′ (level M′) agreeing below level N:
fiber(T, x) ⟺ fiber(T, x′). Consequently the level-N fiber
Φ_N(T) := {x level-N : fiber(T, x)} is an EXACT finite union of level-t
coefficient cylinders (its indicator depends only on digits below t).
(b) **(scaling / mass tie)** #Φ_N(T) = #Φ_t(T) · p^{n(N−t)} for every N ≥ t;
with mass(T) := #Φ_t(T)/p^{nt}, every level: #Φ_N(T) = mass(T)·p^{nN}.
(c) **(uniqueness/disjointness/count)** a box fibers at most one decided ns-free
tree, and distinct trees have disjoint fibers. Define, for a type multiset σ
(§1.4), the **level-N decided-σ count**

    D_σ(N) := #{x level-N : fiber(T, x) for some decided ns-free T with
               type(T) = σ and thr(T) ≤ N}.

Then D_σ(N) = Σ_{T : type(T) = σ, thr(T) ≤ N} mass(T)·p^{nN}, a finite sum.
*(Rev-3 scoping, and caveat (E-N) — OPEN: whether the clause thr(T) ≤ N inside
D_σ(N) is redundant, i.e. whether a level-N box can fiber a decided ns-free
tree of threshold > N, is NOT settled here. A box doing so would be counted by
the unrestricted reading of "decided-σ at level N" and missed by the sum; rev 2
displayed the formula for the unrestricted reading without proof. The
plausibility argument — a level-N decode has no digits at or above N to pin —
is not a proof: deep-frame development coefficients are ℤ-combinations of
digits and key coefficients and can carry any valuation.)*

*Proof.* (a) By symmetry (the hypotheses on x, x′ are symmetric once each is
fibered — and we only assume fiber(T, x); the converse direction then follows by
running the same argument from x′) it suffices: fiber(T, x) ⟹ fiber(T, x′).

* (F3)/(F6): f̄_{x′} = f̄_x (N ≥ 1) — reduction-level clauses transfer verbatim.
* (F1) forward (chains REALIZED at x′): a chain H has L(H) ≤ t ≤ N; Theorem
  2(a). Pruning: IrrHalts is record-only; a proper prefix o's non-ns-halt is
  witnessed by its tree child, REALIZED at x′ by Theorem 2(a): by
  **(M6c)(ii)** — whose child hypothesis (READ + (N1)) the child carries and
  which, at rev 4, puts NO halting hypothesis on o (rev 3's form was circular
  exactly here: it presupposed o non-halted to conclude non-halting — pass-3
  critical, repaired) — the child's side is a
  window principal face at o, so the prefix's window has a
  principal face and NsHalts fails.
* (F1) backward (no strays at x′): suppose K is a REALIZED pruned run on f_{x′}
  with K ∉ chains(T). Walk K from the root: since the root state qualifies and K
  is finite, there is a longest prefix o of K lying in {root states} ∪ chains(T);
  let ν′ be K's next node. Then (o, ν′) is REALIZED at x′ (a prefix of a
  REALIZED pruned run is one: READ restricts — it quantifies per read; CORE's
  per-node laws and coherence restrict; AUX restricts by its displayed prefix
  closure, §1.2 — rev-4 display of a silently consumed property; and the
  prefix-non-saturation clause is inherited). By Theorem 2(b) at state o, ν′ is
  in T's recorded roster, so o·ν′ ∈ chains(T) — contradicting maximality of o.
  So no strays exist.
* (F2): leaf kind and verdict are record-only for (τ-irr) leaves (saturation +
  verdict function of H); ns legs are absent. The maximality of each leaf among
  REALIZED runs at x′ follows from (F1)-at-x′ just established (chains =
  REALIZED runs, so maximal chain = maximal run).
* (F4): ¬IrrHalts record-only; ¬NsHalts at interior chains: the tree child is
  REALIZED at x′ (Theorem 2(a)) and arises from a window principal face by
  **(M6c)(ii)** — no halting hypothesis on the interior state at rev 4 (same
  repair as (F1) forward) — so the window has a principal face.
* (F5): record-only. 

All six clauses hold at x′. For the "consequently": any two level-N boxes in
one level-t cylinder agree below t; apply the just-proved equivalence with its
N instantiated to t (its hypothesis reads t ≥ t — satisfied; working levels
M = M′ = N ≥ t): membership is constant on level-t cylinders, and Φ_N(T) is the
union of those (finitely many) cylinders' level-N members. *(Rev-3 repair of a
garbled sentence; the instantiation is unchanged.)*

(b) The reduction map from level-N boxes to level-t boxes is exactly
p^{n(N−t)}-to-1; by (a), Φ_N(T) is the full preimage of Φ_t(T) — indeed
membership at level N is constant on reduction fibers (same-t-cylinder boxes),
and a level-t box g is in Φ_t(T) iff any (equivalently every) level-N lift is in
Φ_N(T) (the cross-level instance M = N, M′ = t of (a)). Count. ∎(b)

(c) Given fiber(T, x) and fiber(T″, x): (F1) forces chains(T) = chains(T″) (both
equal the REALIZED pruned runs on f_x; chains are sequences of node RECORDS, so
chain equality is equality of all recorded data); (F2) forces equal leaf
verdicts (for ns-free T, T″ the verdict is the record-only irrVerdict, §1.4, and
the leaf sets coincide); (F3) forces equal Hensel payloads; ns-marks are empty on
both. So T = T″ as classification trees. Disjointness follows; and D_σ(N) counts
each qualifying box once (uniqueness), box-partitioned by its unique tree, so
D_σ(N) = Σ_{type(T)=σ, thr(T) ≤ N} #Φ_N(T) = Σ mass(T)·p^{nN} by (b).
Finiteness: drop the trees with empty fibers (they contribute mass 0 to
the sum); for the rest, disjointness at the COMMON level N does the work —
every decided ns-free T with thr(T) ≤ N and nonempty fiber has #Φ_N(T) ≥ 1 (a
nonempty Φ_t(T) has level-N lifts, all in Φ_N(T) by (b)), and the level-N
fibers of DISTINCT trees are disjoint subsets of the p^{nN} level-N boxes; so
at most p^{nN} such trees appear — a finite count at every N. ∎

**Remark 4 (what Theorem 3 feeds).** (b) + (c) constitute exactly the per-tree
counting tie ("count_tie"/TREE-N) in its repaired ns-free form: the equivalence
of that row with (SCALE) — fiber counts multiply by p^n per level above thr — is
a rigorous two-line cross-multiplication on file in the source campaign (M02
Lemmas A/B) and is not repeated here. (a) is the cylinder structure that the
measure bridge (decided loci are unions of cylinders, masses tie to tree fibers)
consumes. The ns-free hypothesis is NOT removable: an exact-square family
(n = 2: classes of (X − b)², v_p(b) = 1 held to level N) fibers an ns-marked
tree whose counts scale by p, not p² — the countermodel is PARI-verified in the
source campaign. Undecided/ns loci drain into the undecided envelope instead;
their treatment is the drainage node, not this package.

## 7. Countermodel compatibility (the shape constraints honored)

* **The Eisenstein family** f_N = X^n + p^N (any prime, any n ≥ 2, any N ≥ 1):
  its root-window site reads the single principal face from (0, N) to (n, 0);
  intercept I = N, ceiling L = N + 1. The zero box (decode X^n) agrees with f_N
  below level N and does NOT read the site (slot 0 pin fails: B_0 = 0). This
  family REFUTES every tree-keyed, all-sites locality statement (for every
  cutoff N there is a site reading level-N digits) — and sits OUTSIDE every
  guard claimed here: Theorem 1 requires agreement below L = N + 1 (f_N and X^n
  agree only below N); Theorem 2(b)/3 require an ns-free decided fiber (X^n
  fibers none: its run ns-halts; f_N's tree records the deep site so its thr is
  ≥ N + 1, consistent). Simultaneously the family is the SHARPNESS witness: the
  modulus L = N + 1 cannot be improved to N, at any prime, so the ceiling
  formula is exact at the countermodel family.
* **The exact-square (ns) family** shows Theorem 3's ns-free hypothesis is
  necessary (Remark 4).
* **No uniform threshold exists** across sites (the classical reflection: the
  Krasner-type modulus 2·v_p(disc f) + 1 is per-polynomial and unbounded on any
  level cylinder); all statements here are keyed per-site or per-decided-tree,
  never globally. 

## 8. Honesty ledger (exact conditionality; what a hostile reader should attack)

Proved outright, from the definitions in this brief, for every policy and every
box-free prefix-closed AUX completion of LAWFUL: Lemmas DEV, POS, R-LOC, NAT,
CEIL, ROOT-M;
Theorem 1; Theorem 2(a) (as restated at rev 3 — REALIZED, no execution
reading); and condition (M6c) at ROOT states (any policy, any root-key degree —
its proof there is ROOT-M plus the hull argument, key-free). Proved outright
under the STANDARD first key over a degree-1 root key — Lemmas VAL1/KEY1/DIV1
prove the policy (V1)/(V2)-compliant exactly there: Lemma WGEO and (M6c) at
first-transition states, and Corollary VTX's vertex kernel ((M6b)(i) +
(N4)-upper) for children harvested at ROOT states. *(Rev-4 perimeter
corrections, per pass 3: rev 3 claimed the whole block "outright ... for every
policy" — false, KEY1's hypothesis is the standard lift; claimed the vertex
kernel "at root states" while VTX's text deferred root children to T-E — it is
now PROVED there; and its "first transitions" phrasing over-claimed the kernel
by one level — see §2.4/§2.5.)* Proved from the
definitions PLUS the interface residue — namely (M6b)(iii) (AUX at harvest),
the lower (N4) band (M6b)(ii−) (consumed only in REAL≡'s lawfulness step), and,
at states beyond the perimeter above, (V1)/(V2) key compliance of the policy
(§2.5 — named assumptions with displayed attributions and an OWED normalization
dictionary, carrying WGEO/VTX/(M6c) there): Lemma SPAN; Lemma REAL≡; Theorem
2(b); Theorem 3 — with Theorem 3(c)'s count scoped by the OPEN caveat (E-N)
(§6). Machine checks: §9 T-A..T-F. The remaining conditionality is in the
INTERFACE — the displayed seams:

* **(S-1) Machine transcription.** The theorems are about the machine DEFINED in
  §1 ((R1)–(R5) reads in MacLane frames, harvest-total children, saturation
  halts, fiber clauses (F1)–(F6)). Any consumer whose classifier is formalized
  differently owes a clause-by-clause audit that its run predicate instantiates
  (M1)–(M6). In the source project this audit is the graded-presentation
  dictionary layer plus the SideReads↔(R1)–(R5) correspondence; it is
  bookkeeping, but it is OWED, and it is where a formal-corpus discharge would
  live. Nothing in this brief proves anything about a Lean object.
* **(S-2) LAWFUL content.** LAWFUL = CORE ∧ AUX (§1.2): CORE is displayed in
  full and carries the laws the proofs consume ((N2)/(N3) via Lemma NAT, (N4)
  via Lemma CEIL and the (R5) transfer); AUX is an explicit box-free parameter,
  and only its box-freeness is used. If a machine's lawfulness laws inspected
  f, Theorem 1 would need those clauses audited into (M1)'s shape. (In the
  source machine they are box-free by construction: they are record laws.)
  Consistency/existence of lawful extensions is never consumed; non-vacuity is
  witnessed (§1.2).
* **(S-3) Policy pinning.** The policy is a formal parameter (§1.1): (M4) makes
  keys record/policy-determined; Theorems 1/2(a) are proved for every policy,
  and Theorems 2(b)/3 for every policy satisfying the residue — (M6b)(iii), the
  lower band, and (V1)/(V2) compliance of its assigned keys (rev-4 repair of a
  pass-3 critical: compliance does NOT follow from monicity + degree, so it is
  part of the hypothesis, proved only for the standard first key over degree-1
  root keys). Nothing here proves the
  policy is canonical or unique (a separate well-posedness node owns that);
  existence of policies is trivial, existence of COMPLIANT keys is MacLane/GMN
  theory — cited, not proved here (§1.1, §2.5).
* **(S-4) Harvest realization ((M6b)/(M6c)/(V1)/(V2)).** Split into proved and
  assumed parts; rev 4 corrects the split's labeling. PROVED (§2.5, Lemmas
  WGEO + Corollary VTX + condition (M6c), the latter REQUANTIFIED with no
  halting hypothesis): vertex coefficient nonzero, the (N4) UPPER bound,
  beyond-window (R1), and no-phantom — (M6c) outright at root states (any
  policy) and, under a standard first key, at first-transition states over
  degree-1 root keys; the vertex kernel outright for root-harvested children
  there; modulo (V1)/(V2) key compliance at all other states;
  machine-checked at depth 1 (§9 T-E: 33,043 instances) and depth 2 (§9 T-F:
  41,720 instances, ALL depth-1 states, halted ones included), zero
  violations. ASSUMED: (M6b)(iii) AUX-at-harvest; the
  LOWER (N4) band (consumed only inside Lemma REAL≡'s lawfulness step); and
  (V1)/(V2) themselves — MacLane's augmentation theorem (Def. 4.1/Thm. 4.2)
  and the GMN key-form/development/residual dictionary (Prop. 2.10/Thm. 2.11,
  §2.6 Theorem of the product; loci per the pass-3 literature check) — NOT
  citation-grade as bundled: the normalization dictionary into this package's
  (w_i, γ̂_i, Φ_i) is an OWED open correspondence (rev-4 honesty downgrade,
  §2.5). Consumers: Lemma SPAN's roster totality, Lemma REAL≡,
  and Theorem 3's (F1)/(F4) steps via (M6c)(ii). A machine violating the
  residue would have candidate-but-unrealized faces (the ledger would
  under-count) or unlawful harvests. This seam is the realization-faithfulness
  node's territory (no-phantom/no-missing), consumed here only in this
  displayed form.
* **(S-5) Semantic identification.** NOTHING here identifies the machine's
  verdicts with true ℚ_p-factorization data (that is the halt-soundness and
  dictionary nodes). Theorem 3's "mass tie" is a statement about the machine's
  own fibers and counts.
* **δ-tier explicitly excluded** (Remark 2): no claim relating L(H, ν) to
  v_p(disc f) is made or needed here.

## 9. Numerical corroboration (falsification-grade, run before writing)

An exhaustive machine check of the depth-1 slice (where the read machine is
directly computable from first principles: boxes with reduction X^n, root window
= the full Newton polygon of f w.r.t. X; sites = (principal face, irreducible
residual factor) pairs; ceilings L = 1 + ⌈intercept⌉):

| test | content | result |
|---|---|---|
| T-A | per-site membership is an exact union of level-L(site) cylinders — Theorem 1's depth-1 instance, exhaustive over all boxes and all harvested sites | **0 violations** (5 configs: (p,n,M) = (2,2,5), (2,2,6), (3,2,5), (2,3,4), (3,3,4); 28,036 boxes; 115 sites) |
| T-B | sharpness: membership NOT constant on level-(L−1) cylinders | 112/115 sites sharp — the ceiling formula is tight (the 3 non-sharp sites are wide-window shapes whose lower digits force the top) |
| T-C | roster/cylinder law: boxes with polygon closed below M have their FULL site roster constant on the level-t cylinder, t = max site ceiling — Theorem 3(a)'s depth-1 proxy | **0 violations** (27,114 closed boxes) |
| T-D | the Eisenstein family: unique site at ceiling N+1, not realized at the zero box (agreement below N) — outside-guard placement | PASS at every (p, n, N) tested |
| T-E | NEW AT REV 2 — the (M6b) kernel, exhaustively at depth 1: for every harvested site, under the standard key lift Φ_1 = Σ_k ψ̂_k p^{(g−k)h} X^{ek}, the slot-μ coefficient C_μ of the Φ_1-development of the decode is NONZERO and its Gauss height w_0(C_μ) lies in the (N4) band [β*, I]; plus the (N2)/(N3) laws and Lemma NAT's I ≥ 1 at every harvested site | **0 violations** (same five configs; 33,043 harvested site-instances) |
| T-F | NEW AT REV 3 — window geometry and (M6c) at DEPTH 2, exhaustively at every depth-1 state (the slice the audit noted depth-1 checks are structurally blind to): with u_k := w_1(C_k) + k·γ̂_0 the sheared points of the full Φ_1-development: (T-F.1) min_k u_k = γ, first attained exactly at k = μ, so C_μ ≠ 0 and u_μ = γ (WGEO(b)/Corollary VTX); (T-F.2) all window faces strictly descend and every beyond-window point is strictly above every window face's extended line ((M6c)(i)); (T-F.3) the full polygon's principal part equals the window hull ((M6c)(ii) content); (T-F.4) vhtx = w_0(C_μ) ≤ (γ − μγ̂_0)/e ≤ I (the rederived (N4)-upper) | **0 violations** (configs (p,n,M) = (2,3,4), (2,4,4), (3,3,4), (3,4,3), (2,6,3); 41,720 site-instances, 7,912 with beyond-window slots) |

T-E's run also REFUTED, 1,644 times, the alternative reading in which the vertex
height is pinned at β* itself (w_0(C_μ) = β*): e.g. f = X³ + 10X² at p = 2 has
its harvested face (2,1)–(3,0) with vertex coefficient C_1 = f′(−2) = −28 at
height 2, not β* = 0 — precisely the reading a prior audit flagged as implicit.
This is the machine countermodel that forced (R5)'s rev-2 restatement with a
RECORDED vertex height (§1.3). T-A/T-B/T-C exercise the (R1)–(R3) clause core;
T-E exercises (R5)'s well-definedness and band; the full-READ cylinder law over
all five clauses is Theorem 1's content.

T-F's run also REFUTED the PLAIN reading of the window heights (rev 2's literal
w-recursion: coefficient heights e·w_0(C_k), no slope, no shear): **440**
beyond-window support violations (first: f = X⁴ + 2X³ + 2X² at p = 2, whose
harvested face line meets the beyond-window slot 2 with equality) and **7,472**
principal-part/window mismatches (phantom principal faces on beyond-window
support; first: f = X³ + 2X² at p = 2, a SATURATED state whose plain polygon
grows a phantom face (1,2)–(3,0)); the two readings harvest different depth-2
face data (e′, h′) in 41,406 of 41,720 instances. This is the machine evidence
that forced rev 3's §1.1 convention pin (the sloped MacLane composite), under
which the same 41,720 instances show ZERO violations of WGEO/(M6c). Script:
`verification/openmath/o1thr_rev3_depth2_check.py`.

*(Rev-4 perimeter note.)* T-F's enumeration runs over ALL depth-1 states of
each box — no halting filter: saturated states (μ = 1) and ns-halted states
(no principal window face; there the no-phantom check T-F.3 is exactly the
requantified (M6c)(ii) content) are included — and uses the STANDARD first key
over the degree-1 root key X. That is precisely rev 4's requantified-(M6c)
quantifier and standard-policy slice: the falsifier-confirmed perimeter and
the proved perimeter now coincide by construction. (Rev 3's first plain-reading
countermodel was itself a saturated state — the enumeration's width is not
incidental.) All three suites were RE-RUN unchanged on 2026-07-31 for this
revision: T-A..T-E ALL PASS, T-F ALL PASS with the same
0-sloped / 440 + 7,472-plain counts.

Prior corroborating suites from the source campaign (reported for context; not
inputs to any proof): exact per-tree fiber-count scaling by p² at p = 3, n = 2
levels 2–4; the equal-fiber law exact on 174/174 length-2 strata at all four
(n, p) ∈ {2, 3}² including both wild corners; two-sided bracket + drainage
confirmed at 20/20 (n, p) configurations.

## 10. Known/new labels

* Lemmas DEV/POS/R-LOC: (a)/(b) — MacLane-theory standard; proofs supplied to
  keep the brief self-contained.
* Lemma NAT: elementary (rev-2 repair of the ceiling well-definedness gap);
  proof supplied.
* Lemmas ROOT-M/VAL1/KEY1/DIV1: (a)/(b) — elementary or MacLane-standard
  facts; proofs displayed at rev 3 to make the completeness proof
  self-contained on its unconditional perimeter.
* Lemma WGEO + Corollary VTX + condition (M6c): (b) — the principal-part-length
  fact of higher-order Newton polygons (GMN §2 territory), re-proved here from
  the package's own stock on the displayed perimeter; (c) in the per-state
  record-language form used here (beyond-window (R1) + no-phantom for a
  machine's harvest).
* Lemma REAL≡: (c) — the realization-coherence bridge, displayed here.
* Named inputs (V1)/(V2): (a) as mathematical content — MacLane 1936
  (Def. 4.1/Thm. 4.2) / GMN Trans. AMS 364 (2012) (Prop. 2.10/Thm. 2.11, §2.6
  Theorem of the product; loci per the pass-3 literature check) — but consumed
  as named ASSUMPTIONS on the policy's keys: the normalization dictionary into
  this package is OWED, not citation-discharged (rev-4 downgrade; seam S-4).
* Lemma SPAN: (b) — the degree-additivity bookkeeping is GMN-adjacent (their
  f-complete/index apparatus); the ledger form over the machine's records with
  the fiber checksums is written out here.
* Theorems 1, 2, 3: (c) as stated — no published statement matches the
  tree-intrinsic per-site modulus or the per-tree cylinder law (the published
  precision results for OM factorization are discriminant-based, per-polynomial,
  and quantified over factorizations rather than sites; a citation-grade match
  was searched for in the source campaign and does not exist).

