# The per-site read package: lawful-site locality, the realized tier with window closure, and the cylinder law

*(Self-contained verification brief. Everything used is defined here; no external
project files are needed. Charge for the verifier: quote each offending passage and
classify it as CRITICAL ERROR (breaks the logical chain) or JUSTIFICATION GAP (assume
and continue); fix nothing. Labels on claims: (a) known, (b) new proof of known,
(c) claimed new.)*

## 0. What is claimed, in one paragraph

We study a digit-reading classifier for monic degree-n polynomials over ℤ_p — an
Okutsu–Montes (OM) read machine that factors a polynomial by iterated Newton-polygon
side reads in a tower of MacLane frames. Three theorems are proved about it.
**Theorem 1 (lawful-site locality, "D-14")**: for every LAWFUL read-site — lawful
meaning its recorded data satisfy the machine's box-free laws, NOT presupposed
realized on any run — there is a modulus L, computable from the site's recorded data
alone (1 + the largest de-normalized side-line intercept over the site's reads),
such that whether the machine reads that site on f is determined by f's coefficient
digits below level L. **Theorem 2 ("O-1(thr)")**: (a) the realized-site two-lift
comparison form of Theorem 1, uniform over working precisions ≥ L; and (b) window
closure: at every state of a decided ns-free classification tree T, on the whole
cylinder of boxes agreeing below thr(T) the realized-children roster is exactly T's
recorded roster — deep candidate children are excluded, not merely untransported.
**Theorem 3 (the cylinder law, "D-15")**: the fiber of a decided ns-free tree T
(the set of boxes whose canonical tree is exactly T) is, at every precision
N ≥ thr(T), an EXACT finite union of level-thr(T) coefficient cylinders; fiber
counts consequently scale by p^n per level, giving the per-tree mass tie. Theorem 1
and 2(a) are proved outright for the machine defined below; Theorem 2(b) and 3 are
proved modulo NOTHING NEW beyond the displayed interface properties (M1)–(M6) of
§2.4 — the honest conditionality ledger is §8. An exhaustive machine falsifier
(28,036 boxes, 115 sites, five (p, n) configurations, zero violations, ceilings
sharp) is reported in §9.

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

* Order 0: Φ_0 = a monic lift, prescribed by a fixed policy from level-0 data only,
  of an irreducible factor φ̄ of the reduction f̄ ∈ 𝔽_p[X] (deg Φ_0 = deg φ̄ =: d_0);
  w_0 = the Gauss valuation relative to Φ_0: for B = Σ_j c_j Φ_0^j with deg c_j < d_0,
  w_0(B) := min_j v_p(c_j) — here v_p on the coefficients of the c_j (equivalently
  the Gauss valuation of the multivariable rewrite; the standard order-1 OM
  valuation). K_0 = 𝔽_p[z]/(φ̄) — the residue field of the track.
* Order i+1: given F_i and a read ν_i (data in §1.2: coprime pair (e_i, h_i),
  e_i, h_i ≥ 1, and an irreducible ψ_i ∈ K_i[z] of degree g_i), the successor key
  Φ_{i+1} is a monic polynomial of degree e_i·g_i·deg Φ_i determined by ν_i's
  recorded data and the policy (a "lift of ψ_i along the side", MacLane key /
  GMN representative); w_{i+1} is the augmented valuation: for
  B = Σ_j c_j Φ_{i+1}^j (deg c_j < deg Φ_{i+1}, the unique Φ_{i+1}-adic
  development), w_{i+1}(B) := min_j ( e_i·w_i(c_j) + j·γ_{i+1} ), with
  γ_{i+1} := e_i·w_i(Φ_{i+1}) + h_i (> e_i·w_i(Φ_{i+1})). K_{i+1} = K_i[z]/(ψ_i).

Write E_i := w_i(p) = e_0·e_1⋯e_{i−1} (E_0 = 1) — the **stretch**. The
**de-normalized level** of a w_i-height β is β/E_i (so p^L-divisibility is height
L·E_i). All frame data along a history are functions of the RECORDS and the policy —
never of f. This is interface property (M4) below.

*(Standard facts, MacLane 1936 / GMN Trans. AMS 364 (2012) §§1–2, stated here as
they are used; proofs of the two we rely on are given as Lemmas POS and DEV.)*

### 1.2 Nodes, sites, lawfulness

A **node** ν records one side read: the frame index; the side pair (e, h) coprime,
e, h ≥ 1; left slot s0 ∈ ℕ; slot width wSide with e ∣ wSide; the side value γ ∈ ℤ
(the side line is ℓ(j) := (γ − j·h)/e in w-height units); the residual pattern
pat : {0, …, wSide/e} → K with pat 0 ≠ 0 and pat(wSide/e) ≠ 0; the residual
polynomial R(z) = Σ_k pat(k)·z^k; a monic irreducible ψ ∈ K[z] of degree g with
ord_ψ(R) = μ ≥ 1 exactly; the produced key data; and species (root / increment /
recentering). A **site** (H, ν) is a history H = [ν_0, …, ν_{k−1}] (possibly empty
above the root state) together with a next node ν; write H·ν for the extended
history. **LAWFUL(H)** is the conjunction of the machine's structural laws on the
records: the per-node record laws just listed, history coherence (key degrees and
stretches compose; slopes strictly increase in de-normalized units along
recenterings), transition admissibility (span-entry and vertex-transport
conditions), and canonical presentation (the policy pins each node's lift and the
canonical root of ψ). **The only property of LAWFUL used in this brief is that it
does not mention f** — it is a predicate on the record chain alone. (§8, seam S-2.)

### 1.3 The run predicate

For monic f of degree n and a history H = [ν_0, …, ν_{k−1}] with frames F_i and
developments f = Σ_j B^{(i)}_j Φ_i^j (the unique Φ_i-adic development):

**READ(f, H)** := deg f = n, f monic, and for each i < k, with ℓ_i(j) := (γ_i − j·h_i)/e_i:

* **(R1) side support:** for every j with B^{(i)}_j ≠ 0: w_i(B^{(i)}_j) ≥ ℓ_i(j),
  with equality ONLY at the stride slots j = s0_i + e_i·κ having pat_i(κ) ≠ 0;
* **(R2) digit pins:** at every stride slot j = s0_i + e_i·κ with pat_i(κ) ≠ 0:
  B^{(i)}_j ≠ 0, w_i(B^{(i)}_j) = ℓ_i(j) exactly, and the height-ℓ_i(j) residual of
  B^{(i)}_j (image in gr_{ℓ_i(j)}(w_i) = P_{ℓ_i(j)}/P_{ℓ_i(j)}^+, read through the
  recorded unit normalization) equals pat_i(κ);
* **(R3) order:** ord_{ψ_i}(R_i) = μ_i (a condition on records alone, kept in the
  bundle for faithfulness to the source machine);
* **(R4) landing:** Φ_{i+1} (when i+1 < k, and the produced key of ν_{k−1} in any
  case) is the recorded successor key — a function of ν_i and the policy;
* **(R5) vertex read-off:** the Φ_{i+1}-development of f has, at slot μ_i, a
  coefficient whose height-β*_i residual equals the recorded transported vertex
  value, where β*_i := ℓ_i(s0_i + wSide_i) is the side's right-end height.

"**The machine reads site (H, ν) on f**" := READ(f, H·ν) ∧ LAWFUL(H·ν). Note this
includes realization of all PREFIX reads (R1)–(R5) quantify over every i), and it
witnesses non-halting of every proper prefix (each has a realized child, namely the
next node), so site-reading is exactly membership of H·ν in the pruned run set.

### 1.4 States, windows, children, halts, trees

* A **state** o is the root state (before any read on a track) or a history.
  The **window** at a state: at a root state of a track with reduction factor
  φ̄^m (m ≥ 2 the repeated multiplicity; m = window width), the development of f
  in Φ_0 over slots 0..m-and-beyond with the side constraint global over all
  slots; at state H·ν, the development of f in the produced key Φ_{|H·ν|}, window
  width μ_ν (the residual multiplicity of the last read). Points: (j, w(B_j)) for
  B_j ≠ 0.
* **Candidate children** at a realized state = pairs (principal face of the window
  polygon, monic irreducible factor ψ of that face's residual polynomial), each
  yielding a node ν by harvesting the face's data (e, h, s0, wSide, γ, pat from
  f's own development digits) and the policy's lift. A **principal face** is a
  face of the lower convex hull of the window points with h/e > 0 in the current
  frame ("negative slope" in the (slot, height) plane). Interface property (M6):
  harvested children are LAWFUL and, by construction, READ-realized on f.
* **Halts:** (τ-irr) saturation: accE·accF = Dwidth·μ at the last node
  (accumulated e and f invariants; a record-only condition — the machine has NO
  children at saturated states, by definition); (τ-hen) simple factors of f̄ are
  certified at level 0 with verdict (1, deg); (τ-ns) a realized non-saturated
  state whose window has no principal face — the ns-halt, MARKED.
* A **classification tree** T: a finite prefix-closed set of chains (histories)
  per track, a Hensel payload (multiset of (1, g) verdicts), leaf verdicts, and
  ns-marks; **decided ns-free** := every maximal chain is a (τ-irr) leaf and the
  Hensel payload covers the simple part — no ns-marks. Its **type** is the
  multiset of leaf + Hensel verdicts; the **degree checksum** is
  Σ_{(e,f)} e·f over the type.
* The **fiber** of T at a level-M box x, fiber(T, x), is the conjunction:
  **(F1)** T's chains are ALL AND ONLY the realized pruned runs on f_x;
  **(F2)** every maximal chain is a certified leaf on f_x whose kind (τ-irr; τ-ns
  is excluded here by ns-freeness) and verdict match T's records; **(F3)** T's
  Hensel payload equals the simple-factor data of f̄_x; **(F4)** interior chains
  do not halt on f_x; **(F5)** the degree checksum is n; **(F6)** per-track leaf
  degrees match the repeated-factor multiplicities of f̄_x.
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

*Remark.* Only properties (i)–(iii) of the frame maps w_i are used anywhere in
this brief (together with R-LOC, which needs only (iii)). Whether the recursion
of §1.1 yields genuinely multiplicative (MacLane) valuations is standard but
NEVER needed: the machine's reads treat the w_i as given height functions, and
the theorems quantify over the recorded data.

### 2.3 Lemma R-LOC (residual locality). *(a — definitional for graded residues)*

If w_i(B − B′) > β and w_i(B) ≥ β, then B and B′ have the same image in
gr_β(w_i) = P_β/P_β^+ (P_β := {C : w_i(C) ≥ β}). Any residual/digit value the
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
* **(M5)** LAWFUL is box-free. [Definition; content unaudited here — seam S-2.]
* **(M6)** Harvest totality: at a realized non-saturated state, every (principal
  face, irreducible residual factor) pair yields a node that is LAWFUL and
  READ-realized on f; saturated states have no children; every realized child
  arises this way. [Definition of the machine's children for the harvested
  clauses (R1)–(R3); the LAWFUL half is the design invariant of the lawfulness
  laws — seam S-4. Used ONLY in Theorem 2(b)/Theorem 3, never in Theorem 1.]

## 3. The read ceiling

For a nonempty history H with reads ν_0, …, ν_{k−1}:

    I_i := ℓ_i(0) = γ_i / e_i           (the side line's value at slot 0),
    L(H) := 1 + max_{i<k} ⌈ I_i / E_i ⌉    ∈ ℕ,    L(root state) := 1.

**Lemma CEIL (clause-height audit).** Every f-dependent constraint of read i lies
at w_i-height ≤ I_i, hence at de-normalized level < L(H): (R1) constrains
w_i(B_j) against ℓ_i(j) ≤ ℓ_i(0) = I_i (h_i > 0, j ≥ 0); constraints with
ℓ_i(j) < 0 are vacuous by POS(i); (R2) pins heights ℓ_i(s0+eκ) ≤ I_i; (R5) reads
at height β*_i = ℓ_i(s0_i + wSide_i) ≤ I_i, on a development in the pinned key
Φ_{i+1}. ∎ *(This is the whole content of the audit; the machine has no other
f-dependent clause, by (M1).)*

## 4. Theorem 1 (lawful-site read locality — the "D-14" statement). *(c)*

**Theorem 1.** Let (H, ν) be any LAWFUL site and L := L(H·ν). Let f, f′ be monic
degree-n polynomials over ℤ_p with f ≡ f′ (mod p^L). Then

    the machine reads (H, ν) on f   ⟺   the machine reads (H, ν) on f′.

In particular, for boxes x (level M ≥ L) and x′ (level M′ ≥ L) agreeing below
level L: the machine reads (H, ν) on f_x iff on f_{x′} — the verdict is determined
by the digits below level L, uniformly over working levels ≥ L. The quantifier is
over ALL lawful sites: (H, ν) is NOT assumed realized on any run.

*Proof.* LAWFUL(H·ν) is shared (box-free, (M5)). It suffices to transfer
READ(f, H·ν) ⟹ READ(f′, H·ν); the converse is symmetric. Fix a read i. By (M4)
the key Φ_i and valuation w_i are the same for f and f′. Let (B_j), (B′_j) be the
Φ_i-developments; by DEV, B_j ≡ B′_j (mod p^L), so by POS,

    w_i(B_j − B′_j) ≥ L·E_i > I_i ≥ every constrained height of read i     (†)

(the strict middle inequality: I_i/E_i ≤ ⌈I_i/E_i⌉ ≤ L − 1 < L). Now check each
clause for f′:

* (R1) at slot j: if B′_j = 0 the clause is vacuous. If B′_j ≠ 0 and B_j ≠ 0:
  by (†) and ultrametricity, for every threshold β ≤ I_i: w_i(B_j) ≥ β ⟺
  w_i(B′_j) ≥ β, and w_i(B_j) = β ⟺ w_i(B′_j) = β; thresholds ℓ_i(j) > I_i do
  not occur, and ℓ_i(j) < 0 is vacuous by POS. So the support inequality and the
  equality-only-at-strides pattern transfer. If B′_j ≠ 0 but B_j = 0: then
  w_i(B′_j) ≥ L·E_i > I_i ≥ ℓ_i(j) by (†), so the strict inequality holds at j and
  no forbidden equality occurs.
* (R2) at a stride slot j: w_i(B_j) = ℓ_i(j) ≤ I_i < L·E_i, so by (†)
  w_i(B′_j) = ℓ_i(j) exactly and B′_j ≠ 0; by R-LOC (w_i(B_j − B′_j) > ℓ_i(j))
  the height-ℓ_i(j) residuals agree, so the recorded pattern value is read
  identically.
* (R3), (R4): record-only / policy-pinned — shared.
* (R5): the Φ_{i+1}-development transfers by DEV (Φ_{i+1} pinned by (M4)); the
  slot-μ_i coefficient's height-β*_i residual transfers by (†) + R-LOC since
  β*_i ≤ I_i < L·E_i.

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

**Theorem 2(a) (realized-site two-lift comparison).** Let x be a box on whose
decode the canonical run realizes the site (H, ν), and let L := L(H·ν). For every
box x′ at any working level M′ ≥ L agreeing with x below level L, the run on
f_{x′} also reads (H, ν); and conversely. Uniformly over working levels ≥ L.

*Proof.* Immediate restriction of Theorem 1's quantifier to realized sites. ∎

**Theorem 2(b) (window closure, "K2").** Let T be a decided ns-free tree,
t := thr(T), N ≥ t. Let x be a level-M box (M ≥ N) with fiber(T, x), and x′ a
level-M′ box (M′ ≥ N) agreeing with x below level N. Then at EVERY state o of T
(a root state of a track, or an interior chain), the set of children realized on
f_{x′} at o equals the set realized on f_x at o, and both equal T's recorded
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
  one polygon have disjoint slot interiors, so spans add.)
* **(L-SAT)** At a (τ-irr) leaf H the saturation identity accE·accF = Dwidth·μ
  says exactly: verdict degree = deg Φ_H · μ_H = wt(leaf). (accE·accF is the
  certified factor's e·f = its degree over ℚ_p; Dwidth·μ = key degree × window
  width.)

By induction on the subtree below o (finite, T decided): the total verdict degree
of the leaves below o is ≤ wt(o), with equality iff every state weakly below o has
full span. [Leaves: (L-SAT), equality. Interior: Σ over children of (subtree
totals) ≤ Σ wt(children) ≤ wt(o) by (W-ADD), deficits accumulating.]

Now sum over the tree. Per track of the reduction f̄_x with repeated factor
φ̄^{m}: the root state's weight is m·deg φ̄, and (F6) says T's per-track leaf
degrees match exactly these multiplicities — i.e. the track subtree's verdict
total equals its root weight, forcing EQUALITY, hence full span at every state of
the track. (Equivalently: (F3) + (F5) — Hensel payload degree = simple part of
f̄_x, total checksum n = Σ track weights + simple part — force zero total
deficit; either route uses only the fiber clauses.) This proves (i).

(ii): with span reaching slot 0, the leftmost recorded side has s0 = 0 and pat
0 ≠ 0, so (R2) pins w_o(B_0) = ℓ(0) = I ≤ (L − 1)·E_o where L is that recorded
site's ceiling; L ≤ t (thr majorizes the tree's own sites), so
w_o(B_0) ≤ (t − 1)·E_o < t·E_o. ∎

*Proof of Theorem 2(b).* The state o itself is realized on both decodes: o's
chain has ceiling ≤ t ≤ N, Theorem 1 transfers its realization from x to x′.

(⊇, recorded ⊆ realized at both): each recorded child's site has ceiling
≤ t ≤ N; it is realized at x by fiber clause (F1); Theorem 1 transfers it to x′.

(⊆): let ν′ be a child realized on f_{x′} at o (if o is saturated there are none,
on either side, by (M6) — matching the empty recorded roster). Two cases.

*Case 1: L(o·ν′) ≤ N.* Theorem 1 transfers realization to f_x; the pruned run
o·ν′ is then realized at x (prefixes are chains of T, non-halted by (F4)); by
(F1) all-and-only, o·ν′ is a chain of T — recorded. ∎(case)

*Case 2: L(o·ν′) > N ("deep").* We show this cannot occur. By Lemma SPAN(ii) at
x: w_o(B_0) = β_0 < t·E_o ≤ N·E_o. Since x′ agrees with x below N, Lemma DEV +
POS give w_o(B_0 − B′_0) ≥ N·E_o > β_0, so w_o(B′_0) = β_0 as well (ultrametric).
The realized child ν′ satisfies (R1) on f_{x′}, whose side line ℓ′ must support
ALL development points, in particular slot 0: I(ν′) = ℓ′(0) ≤ w_o(B′_0) = β_0.
By SPAN(ii), β_0 ≤ (t − 1)·E_o, so ⌈I(ν′)/E_o⌉ ≤ t − 1. The reads of o itself
are recorded, with ⌈I/E⌉ ≤ t − 1 each (thr majorizes them). Hence
L(o·ν′) = 1 + max(⌈I/E⌉ over all reads of o·ν′) ≤ t ≤ N — contradicting
deepness. ∎

**Remark 3 (where each hypothesis bites).** Decidedness + ns-freeness enter ONLY
through Lemma SPAN (a window with an unspanned left segment — e.g. an ns-halt
state, or an undecided deep side — voids the slot-0 pin, and the Eisenstein
family of §7 shows the conclusion then genuinely fails). (M6) enters only through
the saturated-state clause and (F1)'s harvest reading; Theorem 1 does all
transport.

## 6. Theorem 3 (the cylinder law "D-15" + the mass/count tie). *(c)*

Throughout: T decided ns-free, t := thr(T), fibers per §1.4.

**Theorem 3.** (a) **(CYL)** For all N ≥ t, all working levels M, M′ ≥ N, and all
boxes x (level M), x′ (level M′) agreeing below level N:
fiber(T, x) ⟺ fiber(T, x′). Consequently the level-N fiber
Φ_N(T) := {x level-N : fiber(T, x)} is an EXACT finite union of level-t
coefficient cylinders (its indicator depends only on digits below t).
(b) **(scaling / mass tie)** #Φ_N(T) = #Φ_t(T) · p^{n(N−t)} for every N ≥ t;
with mass(T) := #Φ_t(T)/p^{nt}, every level: #Φ_N(T) = mass(T)·p^{nN}.
(c) **(uniqueness/disjointness)** a box fibers at most one decided ns-free tree;
distinct trees have disjoint fibers, so per splitting type σ the decided-σ count
at level N is Σ_{T : typemult = σ, thr(T) ≤ N} mass(T)·p^{nN}.

*Proof.* (a) By symmetry (the hypotheses on x, x′ are symmetric once each is
fibered — and we only assume fiber(T, x); the converse direction then follows by
running the same argument from x′) it suffices: fiber(T, x) ⟹ fiber(T, x′).

* (F3)/(F6): f̄_{x′} = f̄_x (N ≥ 1) — reduction-level clauses transfer verbatim.
* (F1) forward (chains realized at x′): a chain H has L(H) ≤ t ≤ N; Theorem 1.
  Pruning: IrrHalts is record-only; a proper prefix's non-ns-halt is witnessed by
  its tree child, realized at x′ by Theorem 1.
* (F1) backward (no strays at x′): suppose K is a realized pruned run on f_{x′}
  with K ∉ chains(T). Walk K from the root: since the root state qualifies and K
  is finite, there is a longest prefix o of K lying in {root states} ∪ chains(T);
  let ν′ be K's next node. Then (o, ν′) is realized at x′ (a prefix of a realized
  pruned run is one). By Theorem 2(b) at state o, ν′ is in T's recorded roster,
  so o·ν′ ∈ chains(T) — contradicting maximality of o. So no strays exist.
* (F2): leaf kind and verdict are record-only for (τ-irr) leaves (saturation +
  verdict function of H); ns legs are absent. The maximality of each leaf among
  realized runs at x′ follows from (F1)-at-x′ just established (chains = realized
  runs, so maximal chain = maximal run).
* (F4): ¬IrrHalts record-only; ¬NsHalts at interior chains: the tree child is
  realized at x′ (Theorem 1).
* (F5): record-only. 

All six clauses hold at x′. For the "consequently": any two level-N boxes in one
level-t cylinder agree below t ≥ ... apply the equivalence with N replaced by t
(hypothesis N ≥ t ≥ t holds; levels M = M′ = N ≥ t): membership is constant on
level-t cylinders, and Φ_N(T) is the union of those (finitely many) cylinders'
level-N members.

(b) The reduction map from level-N boxes to level-t boxes is exactly
p^{n(N−t)}-to-1; by (a), Φ_N(T) is the full preimage of Φ_t(T) — indeed
membership at level N is constant on reduction fibers (same-t-cylinder boxes),
and a level-t box g is in Φ_t(T) iff any (equivalently every) level-N lift is in
Φ_N(T) (the cross-level instance M = N, M′ = t of (a)). Count. ∎(b)

(c) Given fiber(T, x) and fiber(T″, x): (F1) forces chains(T) = chains(T″) (both
equal the realized pruned runs on f_x); (F2) forces equal leaf verdicts (for
ns-free T, T″ the verdict is the record-only irrVerdict, and the leaf sets
coincide); (F3) forces equal Hensel payloads; ns-marks are empty on both. So
T = T″ as classification trees. Disjointness and the σ-count formula follow;
finiteness of {T : thr ≤ N, typemult = σ} follows since each such T is
determined by its fiber's members at level t ≤ N (nonempty fibers — trees with
empty fibers contribute mass 0 and can be dropped) and there are finitely many
level-N boxes. ∎

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

Proved outright, from the definitions in this brief: Lemmas DEV, POS, R-LOC,
CEIL; Theorem 1; Theorem 2(a); Lemma SPAN; Theorem 2(b); Theorem 3. The
conditionality is thus NOT in the proofs but in the INTERFACE — the displayed
seams:

* **(S-1) Machine transcription.** The theorems are about the machine DEFINED in
  §1 ((R1)–(R5) reads in MacLane frames, harvest-total children, saturation
  halts, fiber clauses (F1)–(F6)). Any consumer whose classifier is formalized
  differently owes a clause-by-clause audit that its run predicate instantiates
  (M1)–(M6). In the source project this audit is the graded-presentation
  dictionary layer plus the SideReads↔(R1)–(R5) correspondence; it is
  bookkeeping, but it is OWED, and it is where a formal-corpus discharge would
  live. Nothing in this brief proves anything about a Lean object.
* **(S-2) LAWFUL content.** Only box-freeness of the lawfulness bundle is used.
  If a machine's lawfulness laws inspected f, Theorem 1 would need those clauses
  audited into (M1)'s shape. (In the source machine they are box-free by
  construction: they are record laws.)
* **(S-3) Policy pinning.** (M4) makes keys record/policy-determined. The
  theorems are per-policy; nothing here proves the policy exists, is canonical,
  or is unique (a separate well-posedness node owns that).
* **(S-4) Harvest lawfulness (M6, LAWFUL half).** That harvested children
  satisfy the box-free lawfulness laws is a design invariant of the machine
  (the laws were abstracted FROM harvested reads). It is used only in Lemma
  SPAN/(F1)-backward. A machine violating it would have realized-but-unlawful
  faces; the ledger argument would then under-count. This seam is the
  realization-faithfulness node's territory (no-phantom/no-missing), consumed
  here only in this weak, box-free-side form.
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

Prior corroborating suites from the source campaign (reported for context; not
inputs to any proof): exact per-tree fiber-count scaling by p² at p = 3, n = 2
levels 2–4; the equal-fiber law exact on 174/174 length-2 strata at all four
(n, p) ∈ {2, 3}² including both wild corners; two-sided bracket + drainage
confirmed at 20/20 (n, p) configurations.

## 10. Known/new labels

* Lemmas DEV/POS/R-LOC: (a)/(b) — MacLane-theory standard; proofs supplied to
  keep the brief self-contained.
* Lemma SPAN: (b) — the degree-additivity bookkeeping is GMN-adjacent (their
  f-complete/index apparatus); the ledger form over the machine's records with
  the fiber checksums is written out here.
* Theorems 1, 2, 3: (c) as stated — no published statement matches the
  tree-intrinsic per-site modulus or the per-tree cylinder law (the published
  precision results for OM factorization are discriminant-based, per-polynomial,
  and quantified over factorizations rather than sites; a citation-grade match
  was searched for in the source campaign and does not exist).

