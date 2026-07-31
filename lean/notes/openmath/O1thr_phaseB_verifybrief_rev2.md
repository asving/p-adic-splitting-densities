# The per-site read package (REV 2): lawful-site locality, the realized tier with window closure, and the cylinder law

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
and 2(a) are proved outright for the machine defined below — for every policy and
every box-free lawfulness completion, both explicit universal parameters (§1.1,
§1.2); Theorem 2(b) and 3 are proved modulo exactly ONE substantive interface
assumption, (M6b) of §2.4 (harvested children are lawful and their vertex read is
well-defined) — the honest conditionality ledger is §8. An exhaustive machine
falsifier (28,036 boxes, 115 sites, five (p, n) configurations, zero violations,
ceilings sharp; plus, new at rev 2, the (M6b) kernel checked on 33,043 harvested
site-instances with zero violations) is reported in §9.

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

**The policy is a formal parameter.** A **policy** 𝒫 is any function assigning
(i) to each monic irreducible φ̄ ∈ 𝔽_p[X] a monic lift Φ_0 ∈ ℤ_p[X] with
deg Φ_0 = deg φ̄, and (ii) to each lawful node ν over a frame F_i a monic key
Φ_{i+1} ∈ ℤ_p[X] with deg Φ_{i+1} = e_i·g_i·deg Φ_i. The machine, LAWFUL, READ,
and every statement below are relative to ONE fixed 𝒫. Theorems 1 and 2(a) are
proved for EVERY policy — only the degree laws and pinnedness ((M4)) are consumed;
Theorems 2(b)/3 are proved for every policy satisfying (M6b) (for genuine
MacLane-key policies (M6b) is the vertex-transport content of OM theory — seam
S-4; its depth-1 instance is machine-checked in §9). Existence of policies is
trivial (any lifts of the right degrees); canonicity and uniqueness are a separate
well-posedness node (seam S-3) and are used NOWHERE in this brief.

### 1.2 Nodes, sites, lawfulness

A **node** ν records one side read: the frame index; the side pair (e, h) coprime,
e, h ≥ 1; left slot s0 ∈ ℕ; slot width wSide with e ∣ wSide; the side value γ ∈ ℤ
(the side line is ℓ(j) := (γ − j·h)/e in w-height units); the residual pattern
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
* **(N4) vertex band:** β* ≤ vhtx ≤ I. (Only the upper bound is consumed — by
  Lemma CEIL and Theorem 1's (R5) transfer; the band is the vertex-transport
  geometry, machine-checked exhaustively at depth 1, §9 T-E.)

Every READ-realizable node satisfies (N2)/(N3): (R2) pins integer heights ≥ 0
(Lemma POS) at the stride endpoints, where pat ≠ 0. So (N2)/(N3) exclude only
records no polynomial can realize. (N4) is the vertex-band law consumed by
Lemma CEIL and Theorem 1's (R5) transfer; that the machine's own harvest
respects it is part of (M6b) (§2.4), machine-checked exhaustively at depth 1
(§9 T-E).

**History coherence (displayed):** along H = [ν_0, …, ν_{k−1}], key degrees and
stretches compose (deg Φ_{i+1} = e_i·g_i·deg Φ_i, E_{i+1} = e_i·E_i); slopes
strictly increase in de-normalized units along recenterings.

**LAWFUL(H) := CORE(H) ∧ AUX(H)**, where **CORE** := (N1)–(N4) at every node plus
history coherence — all displayed above — and **AUX** is the machine's remaining
canonical-presentation bundle (transition admissibility: span-entry conditions;
the policy pins each node's lift and the canonical root of ψ), carried here as an
EXPLICIT PARAMETER: any predicate of the record chain and the policy alone. Every
theorem below holds for every such AUX. **The only property of AUX used in this
brief is that it does not mention f**; the only properties of CORE used are the
displayed laws themselves ((N2)–(N4) enter through Lemmas NAT and CEIL). LAWFUL
is therefore box-free in full. Consistency and existence of lawful extensions are
NEVER consumed (every theorem is universally quantified over sites or fibered
boxes); non-vacuity is nonetheless witnessed — the Eisenstein site of §7
satisfies CORE, and harvested sites satisfy CORE by construction
((M6a)/(M6b), §2.4). (§8, seam S-2.)

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
  frame ("negative slope" in the (slot, height) plane). Interface properties
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
* **Halts:** (τ-irr) saturation: the recorded identity accE·accF = Dwidth·μ at
  the last node — by the key-degree identity this is EQUIVALENT to μ_{k−1} = 1
  (window width one); a record-only condition — the machine has NO children at
  saturated states, by definition; (τ-hen) simple factors of f̄ are certified
  from the mod-p data with verdict (1, deg); (τ-ns) a realized non-saturated
  state whose window has no principal face — the ns-halt, MARKED.
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
  **(F1)** T's chains are ALL AND ONLY the realized pruned runs on f_x;
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
* **(M5)** LAWFUL is box-free. [By construction at rev 2: CORE is displayed in
  §1.2 and mentions records only; AUX is box-free by fiat (it is a parameter
  ranging over record-chain predicates) — seam S-2.]
* **(M6a)** Harvest, definitional half: at a realized non-saturated state, every
  (principal face, irreducible residual factor) pair yields a harvested node
  whose READ data are read off f by construction — (R1)/(R2) record f's own side
  data and digits, (R3) records ord_ψ exactly, (R4) records the policy's lift,
  and (R5)'s vertex pair (vhtx, vtx) is READ from the slot-μ coefficient of the
  successor development (so (R5) holds by definition WHENEVER that coefficient
  is nonzero); saturated states have no children; every realized child arises
  from a (face, ψ) pair. [Definition of harvesting.]
* **(M6b)** Harvest, substantive half — THE package's single substantive
  interface assumption: at every harvested child, (i) the vertex coefficient
  C_μ is NONZERO (the (R5) read is well-defined), (ii) the harvested vertex
  height satisfies the (N4) band β* ≤ vhtx ≤ I, and (iii) the harvested records
  satisfy AUX. ((N1)–(N3) and coherence at harvest are displayed facts: (N1) is
  read off the face; (N2)/(N3) hold because face endpoints are attained integer
  heights ≥ 0 — Lemma POS; degrees/stretches compose by the policy's degree
  law.) Parts (i)+(ii) are the vertex-transport content of OM theory (MacLane
  key polynomials; GMN Trans. AMS 364 (2012), the product-theorem/vertex
  apparatus of §§2–3 — precise proposition flagged for lookup, seam S-4), and
  are machine-checked EXHAUSTIVELY at depth 1: §9 T-E, 33,043 harvested
  site-instances, zero violations. Consequently (induction along runs from the
  root) every realized pruned run is LAWFUL — used silently wherever Theorem 1
  is applied to realized chains or children. [ASSUMPTION. Used ONLY in Theorem
  2(b)/Theorem 3, never in Theorem 1.]

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
w_i(B_j) against ℓ_i(j) ≤ ℓ_i(0) = I_i (h_i > 0, j ≥ 0); constraints with
ℓ_i(j) < 0 are vacuous by POS(i); (R2) pins heights ℓ_i(s0+eκ) ≤ I_i; (R5) pins
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
* **(L-SAT)** At a (τ-irr) leaf H: verdict degree = accE(H)·accF(H) =
  Dwidth(H) = deg Φ_H — the key-degree identity of §1.4 — and the saturation
  clause accE·accF = Dwidth·μ_H then forces μ_H = 1, so
  verdict degree = deg Φ_H = deg Φ_H·μ_H = wt(leaf). Every equality here is a
  §1.4 definition or the displayed key-degree identity; nothing is read off any
  true factorization of f.

*Roster totality (where (M6) enters).* At every fibered non-saturated state o,
the recorded children are EXACTLY the candidate (face, ψ) pairs of f's window
polygon, each with its exact multiplicity μ_ψ = ord_ψ ((R3)): a candidate is
READ-realized in full by (M6a)+(M6b), so its pruned run is a chain of T by
(F1) all-and-only — recorded; conversely a recorded child is realized by (F1)
and arises from a (face, ψ) pair by (M6a). So the per-face sums in (W-ADD) run
over ALL irreducible factors of each face's residual polynomial, and the
all-faces sum runs over ALL faces of ONE lower polygon (whence the disjoint
interiors used above).

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

*Proof of Theorem 2(b).* The state o itself is realized on both decodes: o's
chain has ceiling ≤ t ≤ N, Theorem 1 transfers its realization from x to x′.

(⊇, recorded ⊆ realized at both): each recorded child's site has ceiling
≤ t ≤ N; it is realized at x by fiber clause (F1); Theorem 1 transfers it to x′.

(⊆): let ν′ be a child realized on f_{x′} at o (if o is saturated there are none,
on either side, by (M6a) — matching the empty recorded roster). Two cases.

*Case 1: L(o·ν′) ≤ N.* Theorem 1 — applicable since o·ν′ is LAWFUL by (M6b) at
x′ (realized children are harvested, and harvested records are lawful) —
transfers realization to f_x; the pruned run o·ν′ is then realized at x
(prefixes are chains of T, non-halted by (F4)); by (F1) all-and-only, o·ν′ is a
chain of T — recorded. ∎(case)

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
family of §7 shows the conclusion then genuinely fails). (M6a) enters through the
saturated-state clause and (F1)'s harvest reading; (M6b) — the single
substantive interface assumption — enters through Lemma SPAN's roster totality
and through the lawfulness of realized children (Case 1); Theorem 1 does all
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
equal the realized pruned runs on f_x; chains are sequences of node RECORDS, so
chain equality is equality of all recorded data); (F2) forces equal leaf
verdicts (for ns-free T, T″ the verdict is the record-only irrVerdict, and the
leaf sets coincide); (F3) forces equal Hensel payloads; ns-marks are empty on
both. So T = T″ as classification trees. Disjointness and the σ-count formula
follow. Finiteness: drop the trees with empty fibers (they contribute mass 0 to
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
box-free AUX completion of LAWFUL: Lemmas DEV, POS, R-LOC, NAT, CEIL; Theorem 1;
Theorem 2(a). Proved from the definitions PLUS the single substantive interface
assumption (M6b) (harvested vertex reads well-defined and in the (N4) band;
harvested records lawful — §2.4, machine-checked at depth 1 per §9 T-E): Lemma
SPAN; Theorem 2(b); Theorem 3. The remaining conditionality is in the INTERFACE
— the displayed seams:

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
  keys record/policy-determined, and every theorem is proved for every policy
  (Theorems 2(b)/3: every policy satisfying (M6b)). Nothing here proves the
  policy is canonical or unique (a separate well-posedness node owns that);
  existence is trivial (§1.1).
* **(S-4) Harvest realization (M6b).** That harvested children have nonzero
  vertex coefficients with heights in the (N4) band, and satisfy the box-free
  AUX laws, is ASSUMED — cited to MacLane/GMN key-polynomial theory (§2.4;
  attribution flagged for lookup) and machine-checked exhaustively at depth 1
  (§9 T-E: 33,043 instances, zero violations). It is used only in Lemma SPAN's
  roster totality, the saturated/empty-roster clause, (F1)-backward, and the
  lawfulness of realized children (Theorem 2(b) Case 1). A machine violating it
  would have candidate-but-unrealized faces; the ledger argument would then
  under-count. This seam is the realization-faithfulness node's territory
  (no-phantom/no-missing), consumed here only in this displayed form.
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

T-E's run also REFUTED, 1,644 times, the alternative reading in which the vertex
height is pinned at β* itself (w_0(C_μ) = β*): e.g. f = X³ + 10X² at p = 2 has
its harvested face (2,1)–(3,0) with vertex coefficient C_1 = f′(−2) = −28 at
height 2, not β* = 0 — precisely the reading a prior audit flagged as implicit.
This is the machine countermodel that forced (R5)'s rev-2 restatement with a
RECORDED vertex height (§1.3). T-A/T-B/T-C exercise the (R1)–(R3) clause core;
T-E exercises (R5)'s well-definedness and band; the full-READ cylinder law over
all five clauses is Theorem 1's content.

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
* Lemma SPAN: (b) — the degree-additivity bookkeeping is GMN-adjacent (their
  f-complete/index apparatus); the ledger form over the machine's records with
  the fiber checksums is written out here.
* Theorems 1, 2, 3: (c) as stated — no published statement matches the
  tree-intrinsic per-site modulus or the per-tree cylinder law (the published
  precision results for OM factorization are discriminant-based, per-polynomial,
  and quantified over factorizations rather than sites; a citation-grade match
  was searched for in the source campaign and does not exist).

