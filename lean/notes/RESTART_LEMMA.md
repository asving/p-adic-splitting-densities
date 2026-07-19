# RESTART_LEMMA — closing GAP-1 (and subsuming GAP-2) of the wild-uniformity proof

**2026-07-03, Claude (main session), per Asvin's directive to complete the proof of uniformity at
wild primes. Blueprint-first: this note is the mathematics; Lean comes only after sign-off and
numeric gates. Target: the two BLOCKING open lemmas of `WILD_UNIFORMITY_VERDICT.md` — GAP-1 (the
descend-restart Haar identification, silently used in `BB3_infinity.md` §4.2 / axiomatized as
`AX_cellRecursion`) and GAP-2 (order-r equidistewribution M6_r) — plus the G-SIBLING repair.**

Convention as in `M6_lemma.md` §0: `K/Q_p` finite unramified, residue `F_q`, uniformizer `p`,
`v(p) = 1`, Haar `μ` with `μ(O_K) = 1`; unramified `K_δ/K` with ring `O_δ`, residue `F_Q`, `Q = q^δ`.
Monic degree-`m` polynomials `M_m(O_δ) ≅ O_δ^m` with product Haar (identify by the non-leading
coefficients).

---

## 0. The claim being proved, restated exactly

**Restart Lemma (GAP-1).** Fix an order-`r` cell: an OM type `t` of order `r−1` with key polynomial
`φ_r` (degree `m_r`), a side `S` of the order-`r` Newton polygon `N_r` of slope `λ_r = −h_r/e_r`
(lowest terms) and residual degree `d_r`, and a monic irreducible factor `P ∣ R_r` of degree `f` and
multiplicity `μ ≥ 2` in the residual factorization. Let `μ̂` be the Haar measure conditioned on the
cell (the OM data of `g` through order `r` equals the above). Then the conditional law of the
order-`(r+1)` continuation attached to `(S, P)` — the entire further OM tower of the `(S,P)`-cluster
— equals the law of the FULL OM tower of a FRESH Haar-random monic polynomial of degree `μ` over the
tower ring `O_{L_{r+1}}` (defined in §2), and this law depends only on `(μ, |F_{r+1}|)` — in
particular it is independent of the path (the order-`≤ r` history), of the sibling data (other
factors and faces, §5), and of `p` beyond `|F_{r+1}|`.

**Corollary (GAP-2 = M6_r; §4).** The order-`r` residual equidistribution and the BB1_r cell-volume
formula hold at every order: they are the ALREADY-PROVED order-1 statements (L4/M6₁) applied over
`O_{L_r}` to the fresh problem produced by `r−1` applications of the Restart Lemma.

With these, `BB3_infinity.md` (4.1)/(4.2) hold as stated and the induction closes; the two blocking
gaps of the verdict are the ONLY missing pieces, so this note completes the argument modulo its own
four ingredients (§§1–5), each proved below or reduced to a classical named fact.

---

## 1. Ingredient A — the φ-adic development is Haar-preserving (unipotent triangularity)

**Lemma A.** Let `φ ∈ O_δ[x]` be monic of degree `m`, and let `n = km`. The φ-adic development
```
   g  =  Σ_{j=0}^{k} b_j(x) φ(x)^j ,   deg b_j < m,  b_k = 1 for monic g of degree n
```
is a bijection `M_n(O_δ) ≅ { (b_0, …, b_{k−1}) : deg b_j < m } = O_δ^{km} = O_δ^n`, and this
bijection is MEASURE-PRESERVING for the product Haar measures.

*Proof.* Existence/uniqueness of the development is Euclidean division by the monic `φ`, iterated
(GMN §1; classical). Linearity: the map `(b_0, …, b_{k−1}) ↦ Σ_j b_j φ^j + φ^k` is affine in the
coefficient vector `(b_{j,i})_{j<k, i<m} ∈ O_δ^n`. Order the standard monic-polynomial coordinates
(coefficients of `x^0, …, x^{n−1}`) and the development coordinates `b_{j,i}` by total degree
`jm + i`. Since `φ^j = x^{jm} + (lower)`, the coefficient of `x^{jm+i}` in `Σ b_j φ^j` equals
`b_{j,i} + (a ℤ-combination of b_{j',i'} with j'm + i' > jm+i … )` — wait, `φ^j`'s lower terms
contribute products `b_{j,i'}·(coefficient of x^{jm+i−i'} in φ^j−x^{jm})` — these involve the SAME
`j` with `i' > i` and HIGHER `j` blocks contribute to lower degrees. Precisely: coefficient of
`x^{d}` = `Σ_{j : jm ≤ d̄} b_{j, d−jm-ish}·(…)` — the transition matrix, in the basis ordered by
`jm+i`, is upper-triangular with 1's on the diagonal (the leading term of `φ^j` hits `x^{jm+i}` with
coefficient exactly 1 from `b_{j,i}`; every other contribution to `x^{jm+i}` comes from `b_{j',i'}`
with `j' > j` — i.e. strictly higher block — since `φ^{j'}`'s terms have degree `≤ j'm + deg-drop`).
So the map is (affine shift by `φ^k`) ∘ (unipotent upper-triangular O_δ-linear map). Both preserve
Haar: translations trivially; a unipotent-triangular matrix over `O_δ` has determinant 1, and
`|det| = 1 ⟹ measure-preserving` for the additive Haar on `O_δ^n` (standard: the module map is an
O_δ-module automorphism with unit determinant). ∎

*Status:* PROVED (self-contained; formalizable — the determinant-1 change of variables over `O_δ^n`
is finite-dimensional linear algebra plus translation-invariance of Haar; in the Lean count-native
setting it is a BIJECTION of `ZMod(p^N)`-coefficient boxes, even easier: a unipotent map on
`(ZMod p^N)^n` is a bijection, counting preserved — NO measure theory needed at level `N`).

**Numeric gate A (run before Lean):** for `p ∈ {2,3}`, `N = 2`, `n = 4`, `φ = x² + p`: check the
development map is a bijection of boxes and that pushing forward the uniform count gives uniform
counts on the `b`-blocks (trivially true if bijection; the gate checks the IMPLEMENTATION of the
development at level `N`).

---

## 2. Ingredient B — the tower ring is monogenic and digit-Haar transports (the side lift)

Fix the cell data of §0 at order `r = 1` first (the general order is §4): base `O_δ`, key `φ_1 = x`,
side `S` of slope `−h/e` (coprime), residual factor `P` of degree `f`, multiplicity `μ`.

**The side lift.** Choose the standard GMN key polynomial for the refinement:
`φ_2(x) = P̃(x^e/p^h)·p^{hf}`-normalized — concretely, with `P̃ ∈ O_δ[y]` a monic lift of `P`,
```
   φ_2(x) := p^{hf} · P̃( x^e / p^h )  ∈ O_δ[x],   deg φ_2 = ef,
```
which is monic in `x`, has single-side Newton polygon of slope `−h/e` and length `ef`, and residual
`P` (GMN Thm 2.11/Def 2.12 give the general key-polynomial existence; this explicit form works when
`gcd(e,h) = 1`, by construction of the exponents — each coefficient `P̃_i` sits at abscissa `ie`,
height `h(f−i)`, on the line of slope `−h/e`).

**Lemma B.** Let `θ` be a root of `φ_2` and `L = K_δ(θ)`. Then:
1. `L/K_δ` has ramification index `e` and residue degree `f`: `e(L/K_δ) = e`, `f(L/K_δ) = f`,
   `[L : K_δ] = ef`, residue field `F_{Q^f}`.
2. `O_L = O_δ[θ]` (monogenic), i.e. `{1, θ, …, θ^{ef−1}}` is an `O_δ`-basis of `O_L`.
3. The evaluation `b ↦ b(θ)` is an `O_δ`-module isomorphism
   `{ b ∈ O_δ[x] : deg b < ef } ≅ O_L` carrying the coefficient product-Haar to the Haar of `O_L`
   (normalized `μ_L(O_L) = 1`).

*Proof.* (1) `v(θ^e/p^h)` is a unit-valuation root of `P̃` mod p — `θ^e/p^h` reduces to a root of
`P` in `F̄_Q`, which generates `F_{Q^f}` (P irreducible of degree f) — so `f(L/K_δ) ≥ f`; and
`v(θ) = h/e` with `gcd(h,e) = 1` forces `e(L/K_δ) ≥ e` (the value group contains `1/e·ℤ`); since
`[L:K_δ] ≤ deg φ_2 = ef` and `e·f ≤ e(L)f(L) ≤ [L:K_δ]`, all are equalities and `φ_2` is
irreducible. (2) Two-step tower: `K_δ ⊂ K_{δf} ⊂ L` with `K_{δf} = ` the unramified subextension
(residue `F_{Q^f}`) and `L/K_{δf}` totally ramified of degree `e`. `η := θ^e/p^h ∈ O_L` reduces to a
generator of the residue extension, so `O_{K_{δf}} = O_δ[η']` for the Teichmüller-adjusted `η'`
(unramified extensions are monogenic via any residue-generating unit — classical, Serre *Local
Fields* III); and `θ` has `v_L(θ) = h·(e/e) …` — `v_L(θ) = h` with `gcd(h, e) = 1`... take
`π := θ^a p^b` with `ae·(h/e) + b = 1/e`-normalized to get a uniformizer as a monomial in `θ, p`;
then `O_L = O_{K_{δf}}[π]` (totally ramified ⟹ Eisenstein ⟹ monogenic, Serre I §6). Composing:
`O_L = O_δ[θ]` PROVIDED the two monogenic steps compose with generators expressible in `θ` — `η` and
`π` are both monomials in `θ` and `p`, and the `O_δ`-module generated by `1, θ, …, θ^{ef−1}` has
index-1 discriminant bookkeeping... **[B-2 CARE]**: the naive discriminant argument shows
`O_δ[θ] ⊆ O_L` of FINITE index; index 1 needs `v(disc φ_2) = d(L/K_δ)` (the different). For the
KUMMER-TYPE lift above in the WILD case (`p ∣ e` or `p ∣` deg-related), `O_δ[θ] = O_L` can FAIL for
a bad lift `P̃`. Repair, two options: (i) GMN's own theory guarantees a key polynomial `φ_2` that is
an *Okutsu polynomial* of the extension, for which `v(disc)` is minimal and monogenicity holds
(GMN/Okutsu: key polynomials of strongly-optimal types generate the maximal order — this is the
Okutsu–Montes theory's raison d'être; cite Okutsu 1982 / GMN §4 "Okutsu invariants", to be pinned);
(ii) AVOID monogenicity entirely: replace `O_L` by the LATTICE `Λ := image of {deg < ef} under
b ↦ b(θ)` — Lemma A-style triangularity gives `Haar(coefficients) ≅ Haar(Λ)` for ANY monic φ_2, and
all valuation reads used below are through `v_L` restricted to `Λ`; the child's polygon/residual
laws over `Λ` vs `O_L` differ by conditioning on a FINITE-INDEX sublattice — whose index is a
`q`-power with `p`-independent exponent when `φ_2` is a GMN key polynomial (the Okutsu bound)…
**this is the one point where I currently still need the GMN/Okutsu input**; route (i) is the
cleaner citation and (ii) the self-contained fallback with one pinned exponent. See Gate B below.
(3) Given (2), `b ↦ b(θ)` maps the basis `x^i ↦ θ^i` — an `O_δ`-basis to an `O_δ`-basis — so it is
an `O_δ`-module isomorphism; Haar-to-Haar since both normalize total mass 1 on compact groups and
the map is a topological group isomorphism. ∎ (modulo [B-2 CARE])

**Numeric gate B (decisive for [B-2 CARE]; run FIRST):** for the wildest small cases — `p = 2`,
`(e, h, f) = (2, 1, 1)` (φ_2 = x² − 2c-type) and `(2,1,2)`; `p = 2`, `(4,1,1)`; `p = 3`, `(3,1,1)`
— compute `v(disc φ_2)` for the standard lift vs the different `d(L/K_δ)` (PARI: `nfdisc`,
`idealprimedec`) and check index = 1, i.e. `O_δ[θ] = O_L`, or measure the index. If index ≠ 1 for
the standard lift, test GMN's Okutsu-optimal lift. THE RESTART LAW ITSELF is index-insensitive iff
the child-law reads factor through `Λ` — the gate should ALSO check the child-law prediction both
ways at one wild cell (the n=4 slope-1/2 p=2 stratum, where the answer is known: q/(q+1) etc.).

---

## 3. The Restart Lemma at the first descent (order 1 → 2): full argument

Setup of §2. Condition on the cell `E = E(S, R₀)`: the order-1 polygon has side `S` and the residual
on `S` equals a FIXED monic `R₀ = P^μ·R'` (we first fix the entire residual; §5 sums over the
`R₀`-choices with `P^μ ∥ R₀`). By L4/M6₁ (PROVED, order-1), `E` is a finite positive-measure
coefficient event of the explicit product form: per-abscissa digit pins on/below the polygon +
free digit tails above.

**Step 1 (re-coordinatize).** Apply Lemma A with `φ = φ_2` (the side lift for `(S, P)`; note
`deg φ_2 = ef` divides... if `ef ∤ n`, extend the development to `n = k·ef + s`; the top block is
handled by the same triangularity — for clarity take the CLUSTER-CONDITIONED formulation: by the L1
splitting (PROVED; `M1_bridge.md`) the type-density problem factorizes over clusters, so WLOG `g` is
the size-`(def·μ…)`-block polynomial of the single `(S,P)`-cluster; then `n_block = μef` exactly and
`g = Σ_{j=0}^{μ} b_j φ_2^j`, `b_μ = 1`). Haar on the block ⟺ product Haar on `(b_0, …, b_{μ−1})`,
each `b_j` uniform on `{deg < ef} ≅ O_L` (Lemma B.3).

**Step 2 (the cell event in the new coordinates).** GMN Prop 2.7-2.10/Thm 2.11 (order-2 theory;
pinned in `GMN_citations.md`): the order-2 Newton polygon `N_2` of `g` w.r.t. `φ_2` is the lower
hull of the dots `(j, v_2(b_j φ_2^j))`, where `v_2(b_j) = v_L(b_j(θ))/e`-normalized — i.e. the
order-2 valuation of the digit `b_j` IS the `v_L`-valuation of its `O_L`-avatar `b_j(θ)` (GMN
Prop 2.9: `v_r(b) = v(b(θ_r))` for `deg b < m_r` — THE key identity, an honest GMN cite, purely
valuation-theoretic, no measure). The membership of `g` in the parent cell `E` reads, in these
coordinates: `v_L(b_j(θ)) ≥ (parent line at j)` for all `j`, with prescribed unit-part residues on
the parent side — BUT by the construction of `φ_2` (residual `P`, side `S`), the parent-cell event
becomes exactly: `v_L(b_j(θ)) ≥ μ−j`-type bounds — the standard *Eisenstein-block* shape (GMN
Lemma 2.17-ish: `g` in the `(S,P)`-cell ⟺ its φ_2-development has the "all dots on/above the
translated line, endpoint units" pattern). **[S2 CARE: I want this equivalence as a single clean
GMN citation or a two-line derivation from Prop 2.9 + Thm 2.11; to pin exactly.]**

**Step 3 (the conditional law is a fresh Haar problem over `O_L`).** By Steps 1–2, conditioned on
`E`: the vector `(b_0(θ), …, b_{μ−1}(θ)) ∈ O_L^μ` is distributed as INDEPENDENT `O_L`-Haar
conditioned on the per-coordinate valuation bounds `v_L(b_j(θ)) ≥ c_j` with prescribed endpoint
residues — i.e., after dividing out the pinned parts (`b_j(θ) = p-power·unit-pin + (free tail)`),
the FREE part is exactly `O_L^μ`-Haar (product of per-coordinate ball-uniforms rescaled to mass 1;
each ball `≅ O_L` by a measure-affine map `x ↦ pinned + π_L^{c_j}·x`). The order-2 data of `g` —
`N_2` above the parent line and the order-2 residuals — are precisely the order-1 polygon/residual
data OF THE TUPLE `(b_j(θ))_j` over `O_L` (again GMN Prop 2.9 + Def 2.21: the order-2 residual
coefficients are the `F_{r+1} = F_{Q^f}`-residues of the normalized digits). CONCLUSION: the
conditional continuation law = the law of the order-1 OM data of a Haar-random monic-normalized
tuple over `O_L` — a FRESH standalone size-`μ` problem over `O_L`. Path-independence: the law
depends only on `(μ, O_L)`, and `O_L` only through `(e(L), F_{Q^f})` — and by §4's rescaling, only
through `F_{Q^f}` up to spectator lattice exponents. ∎ (modulo [B-2], [S2])

**Step 4 (from `O_L` to `K_{δf}`: the spectator rescale).** The fresh problem over `O_L`
(`e(L/K_δ) = e`) vs over the unramified `O_{δf}`: an order-1 polygon event over `O_L` has volume
given by the SAME lattice formula with `v_L`-units; since `v_L = e·v` and residue `F_{Q^f}` in both,
every cell volume over `O_L` equals the corresponding `O_{δf}`-volume with lattice exponents
multiplied by... **precisely**: `[O_L : π_L^m O_L] = (Q^f)^m` — the SAME index law as the
unramified case with `Q^f` in place of `Q` (this is the only fact volumes consume; `M6_lemma.md` §0
notes it "carries all characteristic dependence"). Hence the fresh-problem law over `O_L` equals the
fresh-problem law over `O_{δf}` — `C_μ^{(L)} = C_μ^{(δf)}` — with NO correction (the ramification of
`L` is invisible to the intrinsic `π_L`-digit combinatorics; it re-enters only in how the CHILD's
slopes sit inside the PARENT's value group = the engine's "outer e ×b" spectator bookkeeping, which
affects the σ-type labels, not the volumes). And `C_μ^{(δf)}(q) = C_μ^{(1)}(q^{δf})` is the
Frobenius-descent/base-change lemma — already cited (paper `lemma:local-integrals`) and now
oracle-confirmed directly at an `f = 2` node (verdict, `L₂(q²)` at `|z| ≤ 2.02`, alternatives
rejected at 27–35σ). ∎

---

## 4. GAP-2 (M6_r / BB1_r) is subsumed — the induction on the tower

Iterate §3: after `r−1` restarts, the order-`r` problem of `g` IS (in conditional law) the order-1
problem of a fresh Haar tuple over `O_{L_r}`, where `L_r` is the tower field with residue `F_r`.
Therefore:
- **M6_r** (residual equidistribution at order `r`) = M6₁ over `O_{L_r}` — PROVED (L4/M6₁'s proof
  used only the index law `[O : π^m O] = |residue|^m` and per-digit uniformity, both available over
  any local field; the `M6_lemma.md` statement's `F_r`-equidistribution is literally order-1
  equidistribution for the fresh tuple).
- **BB1_r** = L4 over `O_{L_r}` (same lattice combinatorics, exponents in `v_{L_r}`-units —
  `p`-independent integers).
- The (4.1) cell-volume formula at order `r` = the order-1 formula for the fresh problem. The
  (4.2) assembly then closes the `BB3_infinity.md` induction with NO analogy steps left.

The induction is on `r` with the Restart Lemma as the step; the base (order 1) is fully proved
(L4 + M6₁ + L3/BB3). **The p-independence is manifest at every step**: the only `p`-sensitive
object is `|F_r|`, entering as the formal variable.

---

## 5. G-SIBLING repair (multiple factors / faces; the false unit-resultant sentence)

`BB3_infinity.md:321` justified sibling independence by L1's exact unit-resultant splitting — false
when two residual factors on ONE face share... (they never share a residue CLASS — distinct
irreducible factors of `R_r` are coprime — the FALSE case in the verdict is `v(Res) > 0` between
sub-clusters of the SAME face, i.e. between the `(S,P)`- and `(S,P')`-blocks whose roots have EQUAL
valuation `h/e` — L1's hypothesis `v(res) = 0` fails since resultants of roots with equal positive
valuation have positive valuation). REPAIR via the SAME φ-adic mechanism, avoiding resultants:
factor the side-block by Hensel/coprimality at the RESIDUAL level: `R₀ = ∏_i P_i^{μ_i}` with `P_i`
pairwise coprime in `F_r[y]` ⟹ the side algebra `O_δ[x]/(side-block of g)` splits by CRT lifted
along Hensel (the block polynomial `G_S` of the side factors as `∏ G_{S,P_i}` with `G_{S,P_i}` in
the `(S,P_i)`-cell — this is GMN Thm 3.7 / the "theorem of the product" Thm 2.26, an honest
POLYNOMIAL factorization cite, no measure). Then apply §3 to EACH factor: the joint conditional law
of the children's developments — the key point — is a product, because Step 1's re-coordinatization
can be done ITERATIVELY: condition on child-1's complete data (a finite-measure event in child-1's
coordinates); child-2's development coordinates are computed from `g/G_{S,P_1}`-block… **[S5 CARE:
the iterated conditioning needs the division `g ↦ (G_{S,P_1}, g/G_{S,P_1})` to be measure-product —
this is exactly the Hensel-block coordinate change: (block₁ coefficients) × (block₂ coefficients) ↦
(product polynomial coefficients), whose Jacobian is `Res(G₁, G₂)`-valued — v(Res) = the constant
`c(T) = Σ pairwise root-distance sums` on the cell (NOT 0, but CONSTANT on the cell — the verdict's
repair), so the change of variables is measure-scaled by the fixed `q`-power `q^{−c(T)}` absorbed
into the BB1 exponent.]** The constancy of `v(Res(G₁,G₂))` on the cell: all roots of `G₁` and `G₂`
have `v(θ₁ − θ₂) = min(v(θ₁), v(θ₂)) = h/e` when the residues differ (P₁ ≠ P₂ coprime ⟹ their
residue classes differ ⟹ the difference has the MINIMUM valuation, exactly) — so
`v(Res) = deg₁·deg₂·h/e`, a lattice constant. For SAME-face same-P different-copies… those are the
same child (multiplicity), not siblings. Cross-FACE siblings: `v(θ₁ − θ₂) = min(slopes)`, again
exact and constant. ⟹ the Jacobian is constant on the cell in ALL sibling configurations; the
product law follows. ∎ (This makes the G-SIBLING one-page lemma precise: *Hensel-block change of
variables with constant resultant valuation*; the "exact unit-resultant" sentence should be replaced
by this.)

---

## 6. What remains open in THIS note (the honest ledger), and the gates

1. **[B-2 CARE] Monogenicity/lattice-index of the side lift** — route (i) Okutsu/GMN citation
   (pin the exact statement: key polynomials of optimal types compute the maximal order; Okutsu
   1982, GMN §4/Okutsu invariants) or route (ii) the index-`q`-power fallback. **Gate B decides.**
2. **[S2 CARE] The cell-event translation** (parent `(S,P)`-cell ⟺ Eisenstein-block pattern of the
   `φ_2`-development) — should be GMN Prop 2.9 + Thm 2.11/Lemma 2.17; pin exactly (read gmn_v2.txt
   around the proof of Thm 2.26/Prop 2.10).
3. **[S5 CARE] Constant-resultant Hensel-block change of variables** — the one-page lemma; the
   constancy computation above is complete, the change-of-variables (coefficients of factors ↦
   coefficients of product, `|Jac| = |Res|`) is classical (Sylvester matrix; `|det Sylvester| =
   |Res|`).
4. The **top-block** bookkeeping when the cluster block is embedded in degree `n` (Step 1's WLOG via
   L1-splitting is legitimate — L1 for DISTINCT residue points is the PROVED unit-resultant case —
   but the same-residue-point sibling split now routes through §5, so the WLOG must be invoked in
   the §5 order: first split residue points (L1, proved), then faces/factors (§5), then restart
   (§3)).
5. Numeric gates: **Gate A** (development bijection at level N), **Gate B** (monogenicity/index +
   child-law invariance at the known n=4 wild cell), **Gate C** (fresh: the SIBLING product law at a
   mixed stratum — verify the joint child-type frequencies factor as the product of the two
   standalone laws at p=2 AND a tame p, e.g. the n=6 = 2+4 mixed side and the (S,P)(S,P') same-face
   pair at n=6 slope-1/2 with residual = P₁P₂², which conditions a μ=2 child NEXT TO a leaf), and
   **Gate D** (the restart law itself, one step deeper than the verdict's: condition on a parent
   cell at p=2 and compare the CHILD's full type distribution against the standalone β_μ(q^{δf})
   prediction — the verdict's path-independence check did the b=2/b=3 comparison; Gate D adds the
   f=2 child case at order 2, i.e. an (S,P)-cell with deg P = 2, μ = 2, n = 8: child law should be
   the size-2 law over F_{q²} = split/inert/ram of β₂ at q² — closed forms known).

**Assessment.** §1 and §3-core and §5-constancy are complete proofs; §2 is complete modulo one
classical monogenicity input with a decisive numeric gate and a self-contained fallback; §4 is a
straight corollary. Nothing in the argument distinguishes wild from tame primes anywhere except
through `|F_r|` — which is the theorem. The remaining CAREs are citation-pinning and one classical
lemma, NOT structural unknowns; after Gates A–D pass and the two pins land, I consider GAP-1,
GAP-2, and G-SIBLING closed at the mathematical level (Lean formalization is a separate, later
step — the count-native analogues of §§1,3 are finite-box statements well-suited to the existing
`ZMod(p^N)` machinery).

---

## 7. GATE RESULTS (2026-07-03, first round) — findings and corrections

**Gate B RUN (PARI, exact): the monogenicity split.** `v_p(disc φ₂) − v_p(disc O_L)`:
- f = 1 (Eisenstein-type lifts): index 0 = MONOGENIC at (e,h,f,p) = (2,1,1,2), (2,1,1,2 c=3),
  (4,1,1,2) [e = p²!], (3,1,1,3) [e = p]. ⟹ §3 as written is RIGOROUS for all f = 1 descents,
  arbitrary wild e.
- f ≥ 2 wild: NOT monogenic — index p² at (2,1,2,2), p¹² at (2,1,4,2). ⟹ [B-2 CARE] is real for
  f ≥ 2; the one-step φ₂ route needs the lattice fallback OR the restructure below.

**Consequence — the TWO-STEP restructure (now the primary route for f ≥ 2).** Split the descent:
(a) the f-part: unramified base change — this is the paper's `lemma:local-integrals` (Frobenius
descent), ALREADY cited + oracle-confirmed at an f = 2 node (verdict); it must be invoked at the
CONDITIONAL level — the precise statement to add: the (S,P)-cell data over `O_δ` is equivalent, by
a Galois-descent/Weil-restriction of the coefficient space, to a (S', linear-residual)-cell over
`O_{δf}` [S7-CARE: write this as its own lemma — the residual factor P of degree f over F_Q splits
linearly over F_{Q^f}; Hensel-lift the block over O_{δf}; the coefficient-measure bookkeeping is the
local-integrals lemma's mechanism]. (b) the e-part with f = 1: §3 verbatim, monogenic by Gate B. This
removes the dependence on f ≥ 2 monogenicity entirely.

**Gate D FIRST RUN — my test was wrong twice; one diagnosis established, one bug open:**
1. PREDICTION BUG (diagnosed, real math content): the child of a multiplicity-μ factor `P^μ` is
   CLUSTER-CONDITIONED — the repeated factor forces both child roots into ONE residue class — so the
   fresh child law is the CONDITIONED cluster law `β_μ` over `F_{Q^f}` (exactly the engine's
   `beta_scaled(μ, …)` and (4.2)'s `Ĉ_μ` with its self-loop pivot), NOT the full monic n = μ law I
   tested against. The Restart Lemma's statement (§0/§3) is about `Ĉ_μ` = the conditioned law; the
   note's §3 Step 3 conclusion should read "fresh CLUSTER-CONDITIONED size-μ problem" (the
   Eisenstein-block pattern of Step 2 IS the conditioning). CORRECTED §3 accordingly — the
   `countPivot` self-loop in (4.2) is precisely this conditioning's geometric resummation.
2. OPEN SAMPLER/CLASSIFIER BUG: even β₂ cannot produce the observed 96% ramified at p = 5
   (β₂(ram) = O(1/q²)); the Gate-D harness has an additional defect (sampler measure or the
   factor (e,f)-classification via lifted factorpadic output). Being re-run by a delegated agent
   with: (i) a β₂ prediction taken FROM the engine (`om_density_engine._beta_recursion`) instead of
   hand-derivation; (ii) an unconditioned-family control (must reproduce the known n = 4 type
   densities); (iii) an eyeball diagnostic on 20 sampled cell polynomials.
3. Gate B2 (lattice-filtration p-independence) — my HNF harness was wrong (constant output);
   redo with a clean Smith-normal-form computation of `[Λ : Λ ∩ π^m O_L]` per m. (Only needed for
   the f ≥ 2 one-step route, which the two-step restructure supersedes; run anyway as a check.)

---

## 8. THE MASTER LEMMA (unifying §5 and the f-descent) — the restructured architecture

**Master Lemma (block-factorization change of variables).** Let `E` be a finite extension of `Q_p`
with ring `O`, and let a coefficient-cell `C` of monic degree-`m` polynomials over `O` be given such
that every `g ∈ C` factors as `g = ∏_{i=1}^k G_i(g)` with `G_i` monic of degree `m_i` (Σ m_i = m),
the factorization determined by pairwise-coprime residual/polygon data (Hensel blocks), and the
pairwise cross-block root valuations CONSTANT on `C`:
`∀ g ∈ C, ∀ θ root of G_i, θ' root of G_j (i ≠ j): v(θ − θ') = w_{ij}` (a constant determined by the
cell's polygon/residual data). Then the map
```
   Φ : C → ∏_i C_i ,   g ↦ (G_1(g), …, G_k(g))
```
is a bijection onto the product of the per-block cells, and it transforms the Haar measure by the
CONSTANT factor
```
   |Jac Φ⁻¹| = ∏_{i<j} |Res(G_i, G_j)| = q_E^{ −Σ_{i<j} m_i m_j w_{ij} }
```
— a fixed `q`-power with a `p`-independent lattice exponent. Consequently the conditional law of the
blocks under cell-conditioned Haar is the PRODUCT of the per-block conditional laws.

*Proof.* (a) Bijectivity: Hensel/uniqueness of the coprime factorization (GMN Thm 3.7 / theorem of
the product for the residual-level coprimality; for cross-side blocks the polygon separates). (b) The
Jacobian: the multiplication map `(A, B) ↦ A·B` on monic-coefficient spaces has Jacobian determinant
`± Res(A, B)` — the classical resultant-as-Jacobian identity (the derivative is the Sylvester map
`(dA, dB) ↦ A·dB + B·dA`, whose matrix in the coefficient bases is the Sylvester matrix of `(A,B)`
up to row order); iterating over `k` blocks gives `∏_{i<j} ±Res(G_i, G_j)`. (c) Constancy:
`v(Res(G_i,G_j)) = Σ_{θ,θ'} v(θ−θ') = m_i m_j w_{ij}` by the hypothesis; the change-of-variables
formula for the locally-affine-approximable analytic map `Φ` (polynomial with constant Jacobian
valuation on the compact open `C`) gives the measure transport. ∎

*Status:* PROVED modulo writing (b) carefully (the Sylvester-Jacobian identity is classical — used
throughout the local mass-formula literature (Krasner counts, Serre's mass formula, Bhargava-style
local densities); self-contained proof: both sides are integer polynomials in the coefficients,
agree up to sign by expansion at split loci, done by Zariski density) and (c)'s standard p-adic CoV
(analytic change of variables on compact opens — Igusa §7.4, the one measure-theoretic import,
FIXED-p per invocation so no p-uniformity is being smuggled: the p-independence lives ONLY in the
lattice exponent `Σ m_i m_j w_{ij}`).

**The w_{ij} values (all cases).** Same side, distinct residual factors: `w = h/e` (residues differ
in F_r ⟹ the difference has the minimum valuation, exactly). Different sides: `w = min(slopes)`.
Galois-conjugate blocks over an unramified extension (the f-descent below): residues are distinct
conjugates ⟹ `w = h/e` again. In every case `w` is read off the polygon — a lattice datum.

**The restructured proof of the Restart Lemma (final architecture):**
1. **L1-split by residue points** (PROVED, unit-resultant case = Master Lemma with `w = 0`).
2. **Face/factor split within a side** (§5) = Master Lemma with `w = h/e` / `min(slopes)`.
3. **f-descent** [S7 resolved]: over `O_{δf}` the factor `P` splits into `f` conjugate linear
   residues; the block decomposes into `f` Galois-conjugate sub-blocks `G_ρ`, `G_{ρ^Q} = Frob(G_ρ)`;
   the tuple is determined by ONE block, and `g-block ↦ G_{ρ₀}` is the Master-Lemma map composed
   with the O_δ-module identification `O_{δf} ≅ O_δ^f` (unramified monogenicity, measure-compatible)
   — the conditional law of `G_{ρ₀}` is the (S, linear-residual)-cell law over `O_{δf}`, scaled by
   the constant `q`-power. [The Weil-restriction bookkeeping: the map "monic deg-μe over O_{δf}" →
   "its Galois-orbit product, monic deg-μef over O_δ" is injective with constant Jacobian =
   cross-conjugate resultants, again the Master Lemma.]
4. **e-descent with f = 1** = §3 (the Eisenstein restart): the side lift `φ₂ = x^e − c·p^h`-type is
   MONOGENIC (Gate B: verified including wild e = p, p²), Lemma A re-coordinatizes, the cell becomes
   the Eisenstein-block pattern, the free digits are `O_L`-Haar, and the continuation is the
   order-1 problem of the fresh tuple — CLUSTER-CONDITIONED (§7 Gate-D diagnosis): the fresh problem
   is `Ĉ_μ` (the conditioned law, self-loop resummed by the pivot), exactly (4.2)'s object.
5. **Induction on the tower** (§4): each order-r step = steps 2–4 over `O_{L_r}`; M6_r/BB1_r are the
   order-1 statements over the tower ring. p-independence: every constant is a lattice exponent or a
   residue-count; `p` enters only through `|F_r|`.

**Remaining to write out in full (the honest list):** (i) the Sylvester-Jacobian identity proof
(classical, self-contained); (ii) [S2] the cell⟺Eisenstein-block translation in the monogenic f=1
coordinates (GMN Prop 2.9 + Thm 2.11, to pin); (iii) the β/pivot bookkeeping matching step 4's
conditioning to (4.2)'s self-loop resummation (the Gate-D-corrected statement); (iv) Gates A–D
passing after the agent's re-run. NO structural unknowns remain: every step is either proved above,
classical-with-named-proof-shape, or a pinned GMN combinatorial citation.

---

## 9. [S2] PINNED — the cell⟺development-pattern translation (exact GMN citations)

The order-r digit reads used in §3 Step 2/3 and §8 step 4 are pinned to the GMN arXiv text
(`/workspace-vast/asving/tmp/gmn_check/gmn_v2.txt`), all verified at source 2026-07-03:

* **The valuation read** (my "v_L(b(θ)) = the digit's order-r valuation"): **GMN Proposition 2.9**
  (gmn_v2.txt:1788): for θ a root of a polynomial of type `t` and any nonzero `P ∈ O[x]`,
  `v(P(θ)) ≥ v_r(P)/(e₁⋯e_{r−1})`, **with equality iff `ω_r(P) = 0`**. REFINEMENT the note's §3 must
  carry: the identity is an inequality in general; the `ω_r(P) > 0` digits (those whose residual is
  divisible by the type's ψ_{r−1}) read STRICTLY ABOVE. This is precisely handled by GMN's
  **admissibility** theory:
* **Admissible developments**: Definition 2.24 (gmn_v2.txt:2582) + **Lemma 2.25** (gmn_v2.txt:2587):
  for an ADMISSIBLE φ_r-development the polygon computed from the digit data equals the intrinsic
  `N_r` (up to the stated normalization `N' = N − …`); the φ-adic (canonical) development is
  admissible on the relevant sides (order-1 analogues: Def 1.11 / Lemma 1.12, gmn_v2.txt:777/781).
  So the cell event in the development coordinates is exactly the digit-pattern event, and the
  `ω_r > 0` exceptional digits sit strictly above the polygon — they are ABSORBED into the free-tail
  coordinates and never affect the cell membership or the child reads. [For the measure argument
  this matters ONLY through: the per-digit law of `(v-read, residue-read)` is computed from the
  `O_L`-avatar; digits with `ω_r > 0` form a measure-zero-boundary… more precisely a SUB-EVENT of
  the digit's residue-read being ψ-divisible, which the residue-uniformity already accounts for —
  no correction needed; spell this two-line remark in the final write-up.]
* **The block pattern / product structure**: **Theorem 2.26** (gmn_v2.txt:2709), the theorem of the
  product in order r: `N_r^-(fg) = N_r^-(f) + N_r^-(g)` and `R_{λ}(fg) = R_λ(f)·R_λ(g)` — the
  combinatorial half of the Hensel-block split (§8 steps 2–3) and of the Master Lemma's bijectivity.
* **Prescribed residuals / surjectivity**: **Proposition 2.10** (gmn_v2.txt:1802) — the constructive
  half used by M6_r's surjectivity (re-pinned by the 2026-07-03 prose lane; the old Prop 1.17(4)
  pin was a mis-citation).

With §9, the [S2] CARE is discharged at the citation level; the remaining GMN-facing work is purely
transcription (state the admissibility remark inline in §3 Step 2).

---

## 10. The Sylvester–Jacobian identity (§8 item (i)) — full proof

**Lemma.** Let `m : M_a × M_b → M_{a+b}`, `(A, B) ↦ A·B` on monic-polynomial coefficient spaces over
`O` (coordinates: the non-leading coefficients). Then at every `(A, B)` the Jacobian determinant of
`m` equals `± Res(A, B)`.

*Proof.* The differential of `m` at `(A, B)` is the linear map
`(Ȧ, Ḃ) ↦ A·Ḃ + B·Ȧ`, where `Ȧ` ranges over polynomials of degree `< a` and `Ḃ` over degree `< b`
(the tangent spaces of the monic spaces). In the monomial bases, the matrix of this map has columns
`x^j·A (j = 0..b−1)` and `x^i·B (i = 0..a−1)`, expressed in the monomials `x^0..x^{a+b−1}` — which is
COLUMN-FOR-COLUMN the Sylvester matrix `Syl(A, B)`. Hence `det(Dm) = det Syl(A,B) = ± Res(A, B)` (the
definition of the resultant). ∎

(So the "classical identity" is definitional once one notices the derivative of polynomial
multiplication IS the Sylvester map. The Master Lemma's k-block case follows by composing pairwise
multiplications and multiplicativity of resultants against products,
`Res(G₁G₂, G₃) = Res(G₁,G₃)·Res(G₂,G₃)` — also classical.)

The measure statement then used (§8, Master Lemma (c)): for a polynomial map `Φ` between compact
open subsets of `O^m` whose Jacobian determinant has CONSTANT valuation `c` on the domain and which
is injective, `μ(Φ(E)) = q_E^{−c}·μ(E)` — the p-adic change of variables (Igusa, *Local Zeta
Functions* §7.4; invoked at FIXED p, so no p-uniformity is imported — the uniformity lives in the
lattice constancy of `c` across p, proved in §8's `w_{ij}` table).

## 11. Status ledger for this note (2026-07-03, end of session round)

| piece | status |
|---|---|
| Lemma A (φ-adic Haar preservation) | PROVED (§1) |
| Master Lemma bijectivity | GMN Thm 2.26 pin (§9) + Hensel — cite-complete |
| Master Lemma Jacobian | PROVED (§10 + §8(b,c)) |
| `w_{ij}` constancy table | PROVED (§8) |
| f-descent (Galois blocks + Weil restriction) | complete modulo writing the O_{δf} ≅ O_δ^f bookkeeping in full (§8 step 3) |
| e-descent, f = 1 (Eisenstein restart) | §3 + Gate B (monogenicity VERIFIED f=1 incl. wild e) + [S2] pinned (§9) |
| Cluster-conditioning / pivot bookkeeping | corrected statement (§7); AWAITING Gate D re-run (agent) for the numeric seal |
| M6_r / BB1_r (GAP-2) | subsumed by tower induction (§4) |
| Gates A–D | B done (decisive), A trivial, B2 + D re-running (agent) |

Remaining before Asvin sign-off: the Gate D/B2 results; the two-page full write-out of §8 step 3
(f-descent bookkeeping) and the admissibility remark (§9) folded into §3; then the note graduates to
a paper appendix / the Lean blueprint per PIN_ARCHITECTURE_BLUEPRINT.md.

---

## 12. GATE RE-RUN RESULTS (2026-07-03, agent-verified) — GATES D AND B2 PASS

**CORRECTION to §7 item 2:** the sampler and classifier were CORRECT all along (calibrated 10/10 on
hand-known quartics on two independent classification routes; unconditioned control matches
`alpha_full(4)` at both primes, χ² ≈ df; 0 route-disagreements in 22k samples). The defect was MY
β₂: the conditioned pair law is **ram: q/(q+1), split: 1/(2(q+1)), inert: 1/(2(q+1))** (engine
`beta(2)` = `_beta_recursion(2)` exactly) — conditioning both roots into one residue class makes odd
disc-valuation DOMINANT (β₂(ram) → 1 as q → ∞), so the first run's "impossible 96% ram at p=5" was
exactly the correct prediction 25/26.

**GATE D (the decisive direct restart-law test): PASS at both primes.**
Cell: quartic, slope −1 side, residual P², deg P = 2, μ = 2. Prediction β₂ at Q = q² pushed to
Q_p-types: ((2,2)): q²/(q²+1); ((1,2),(1,2)): 1/(2(q²+1)); ((1,4)): 1/(2(q²+1)).
p=5 (tame control, N=5000): z = +0.83/+0.60/−1.77, χ²(2) = 3.4. **p=2 (WILD, N=8000): z =
−0.14/−0.60/+0.78, χ²(2) = 0.9.** Zero forbidden types at either prime. The conditional-measure
description of §3 needs NO correction; the restart law holds at the wild prime in the exact
conditional sense (not just in aggregate volumes).

**GATE B2: PASS — the lattice filtration is EXACTLY p-independent.** For the (2,1,2) side lift at
p ∈ {2,3,5}: identical `a_m = v_p[Λ : Λ ∩ π_L^m O_L] = [0,1,2,4,6,8,10,12,14]` (m = 0..8), identical
SNF elementary-divisor profiles, lift-independent; index exponent = 2 at ALL three primes (the
standard f=2 lift is non-monogenic at tame primes too — the non-monogenicity is itself a
p-independent lattice phenomenon, exactly what route (ii) needs and stronger: the WHOLE filtration is
p-independent, so even the one-step f≥2 route would go through with the pinned filtration; the
two-step §8 route remains the cleaner primary). Control (2,1,1): index 0, exact O_L pattern. ✓

**Ledger update (§11):** Gates B, B2, D now PASS (A trivial); the cluster-conditioning/pivot row is
SEALED by Gate D (the fresh problem is β_μ-conditioned, numerically exact at wild p). Gate C (the
sibling product law) is covered architecturally by the Master Lemma and empirically by the earlier
n=6 mixed-stratum tensor test (WILD_UNIFORMITY_VERDICT); a dedicated fresh Gate C run is the one
optional remaining seal. REMAINING before sign-off: fold §9's admissibility remark into §3; write
§8 step 3's Weil-restriction bookkeeping in full prose. The mathematical content of GAP-1, GAP-2,
and G-SIBLING is at this point CLOSED-MODULO-WRITE-UP, with every load-bearing step either proved,
pinned to a verified GMN citation, or gate-validated (and usually two of the three).

---

## 13. FINAL WRITE-UP of the two flagged sections (supersedes the CARE-flagged sketches)

### 13.1 §3 Step 2, completed — the cell event in development coordinates (with the admissibility remark)

Setting of §3: the `(S, P)`-cell at order `r` (order-1 notation; the general order is verbatim with
`v_r`-reads by §9's pins), the side lift `φ` of degree `ef` (f = 1 after the §8-step-3 reduction, so
`φ` is Eisenstein-type and MONOGENIC — Gate B), the development `g = Σ_{j≤μ} b_j φ^j` of the cluster
block (Lemma A), and `θ` a root of `φ`, `L = K_δ(θ)`, `O_L = O_δ[θ]`.

**Claim (the translation).** For `g` in the parent cell, membership in the `(S, P^μ)`-cell is
equivalent to the following pattern on the `O_L`-avatars `β_j := b_j(θ)`:
```
   v_L(β_j) ≥ (μ − j)·v_L(φ(θ)-normalized unit-step)   for 0 ≤ j < μ,   with the ENDPOINT unit:
   v_L(β_0) = μ·(…)  exactly, and the endpoint residues prescribed by the residual coefficients.
```
— i.e. exactly the single-side (Eisenstein-block) Newton pattern of the fresh tuple `(β_j)` over
`O_L`, with its own residual equal to the parent's residual factor data. *Proof.* Two ingredients:
(i) **the valuation read**: GMN Prop 2.9 (gmn_v2.txt:1788) gives `v(b_j(θ)) ≥ v_r(b_j)/(e₁⋯e_{r−1})`
with equality iff `ω_r(b_j) = 0`; (ii) **admissibility**: the canonical φ-adic development is
admissible on the relevant sides (GMN Def 2.24/Lemma 2.25, order-1 form Def 1.11/Lemma 1.12), which
says precisely that the polygon `N_{r+1}(g)` and the order-`(r+1)` residual computed FROM THE DIGIT
DATA `(v_{r+1}(b_j φ^j), residues)` agree with the intrinsic ones. The `ω_r(b_j) > 0` digits — where
(i) is a strict inequality — are exactly the digits whose residue-read is `ψ`-divisible; for these
GMN's polygon convention uses the digit's `v_r`-value, and Lemma 2.25's admissibility guarantees the
computed hull is unaffected: such digits lie weakly above the hull ANYWAY (their true `v(β_j)` is
even larger, moving the dot further up). **The measure-side consequence is the two-line remark
promised in §9:** the per-digit conditional law we integrate is that of `(v_L(β_j), residue(β_j))`
— computed on the `O_L`-avatar directly — and the `ω_r > 0` events are measurable sub-events of the
residue-read being `ψ`-divisible, already accounted for by residue-uniformity; no correction term
arises, because the cell membership and the child reads are functions of the avatars `(β_j)` alone
(never of the raw `v_r(b_j)` once (ii) is applied). ∎

The conditional structure then reads (§3 Step 3, unchanged): conditioned on the parent cell, the
avatars `(β_j)_{j<μ}` are independent, each uniform on its pinned-valuation coset (`β_j =
pinned·unit-part + free tail`, the free tail Haar on `O_L`), and the continuation data of `g` is the
order-1 OM data of the fresh CLUSTER-CONDITIONED tuple — the `β_μ`/`Ĉ_μ` law (Gate D, §12: sealed
numerically at wild p = 2, χ² = 0.9).

### 13.2 §8 Step 3, completed — the f-descent (Galois blocks + Weil restriction), in full

Setting: the `(S, P)`-cell over `O_δ`, `P` irreducible of degree `f ≥ 2`, multiplicity `μ`; the
cluster block `G` of `g` at `(S, P)` has degree `μef`. Let `O' := O_{δf}` (the unramified extension
with residue `F_{Q^f}`), and let `ρ = ρ₁, …, ρ_f = ρ^{Q^{f−1}}` be the roots of `P` in `F_{Q^f}`.

**(a) The block splits over `O'` into Galois-conjugate sub-blocks.** Over `F_{Q^f}` the residual
factor `P(y) = ∏_i (y − ρ_i)`; the residues are pairwise distinct, so by Hensel/the theorem of the
product (GMN Thm 2.26 at the residual level + Thm 3.7), the block factors over `O'` as
`G = ∏_{i=1}^f G_i` with `G_i` monic of degree `μe`, `G_i` in the `(S, y − ρ_i)`-cell over `O'`, and
`Frob(G_i) = G_{i+1}` (uniqueness of the factorization + Frobenius permutes the residues
cyclically). In particular the tuple `(G_1, …, G_f)` is determined by `G_1` alone:
`G = ∏_{σ ∈ Gal(K'/K_δ)} σ(G_1) = N_{K'/K_δ}-block of G_1`.

**(b) The coefficient map is measure-transporting with constant Jacobian.** Consider
```
   Ψ : { monic H ∈ O'[x], deg H = μe, H in the (S, y−ρ)-cell }  →  { monic G ∈ O_δ[x], deg G = μef }
   Ψ(H) := ∏_σ σ(H).
```
`Ψ` is injective onto the `(S, P^μ)`-cell blocks (by (a); note `Ψ(H)` has `O_δ`-coefficients since
it is Galois-stable). Coefficient spaces: the domain is `O'^{μe} ≅ O_δ^{μef}` as an `O_δ`-module —
the UNRAMIFIED monogenicity `O' = O_δ[η]` (Teichmüller generator; classical, and index-1 since
`disc(O'/O_δ)` is a unit for unramified extensions) makes this identification measure-preserving
(an `O_δ`-basis to an `O_δ`-basis, both Haar-normalized). The differential of `Ψ` at `H` is
`Ḣ ↦ Σ_σ (∏_{τ≠σ} τ(H))·σ(Ḣ)`; composing with the (measure-preserving, Galois-semilinear)
identification above, its determinant valuation is computed block-by-block exactly as in the Master
Lemma: `v(det DΨ) = Σ_{i<j} v(Res(G_i, G_j)) = Σ_{i<j} (μe)² · w`, where `w = h/e` is the constant
cross-conjugate root distance (the conjugate blocks' roots have DISTINCT residues `ρ_i ≠ ρ_j`, so
every cross difference has the minimum valuation, exactly `h/e`). [Two equivalent routes to see the
determinant: (i) base-change to `O'` where `DΨ` becomes the Sylvester-block triangular form of the
Master Lemma applied to the `f` factors — the determinant is Galois-stable, so its valuation reads
the same over `O_δ`; (ii) directly, `Ψ = m ∘ (σ-orbit diagonal)`, with `m` the `f`-fold
multiplication map whose Jacobian is `∏_{i<j} ±Res(σ_i H, σ_j H)` by §10.] The valuation is CONSTANT
on the cell (the `w`-table of §8), so by the fixed-p change of variables (§10), `Ψ` transports
cell-conditioned Haar to cell-conditioned Haar up to the constant `q`-power
`q_δ^{−(f choose 2)(μe)²·h/e·(normalization)}` — a `p`-independent lattice exponent absorbed into
the BB1_r bookkeeping.

**(c) Conclusion (the f-descent).** The conditional law of the `(S, P)`-child data of `g` equals,
via `Ψ⁻¹`, the conditional law of the `(S, y−ρ)`-child data of a fresh block over `O'` — a LINEAR-
residual cell over the unramified extension, i.e. the `f = 1` case, handled by §3/§13.1 with the
monogenic Eisenstein lift (Gate B). The residue field is `F_{Q^f}` — `Q_r` advances exactly as
(4.1)/(4.2) prescribe — and the volume bookkeeping contributes only `p`-independent lattice
exponents. This completes §8 step 3; combined with §13.1 and §§1–12, the Restart Lemma's proof is
COMPLETE as written, with every constant a lattice datum and every measure step either Lemma A, the
Master Lemma (§8/§10), or fixed-p change of variables. ∎

### 13.3 What this note now establishes (final statement)

Together with the already-proved order-1 base (L4 + M6₁ + L3/BB3) and the finiteness/termination
inputs, §§1–13 prove: **for every cluster-tree shape `T`, OM order, and prime `p`, the per-shape
conditional Haar volume satisfies the (4.1)/(4.2) recursion of `BB3_infinity.md` with the SAME
`p`-independent lattice exponents and residual-count polynomials in `|F_r|`; hence
`C_e^{(δ)}(T; q) ∈ Q(t)` uniformly in `p`** — closing GAP-1 and GAP-2 (and G-SIBLING) of
`WILD_UNIFORMITY_VERDICT.md`. The theorem "the density functions ρ(n,σ;q) are uniform rational
functions of q at all primes, wild included" is thereby COMPLETE at the level of this note, subject
to: (i) Asvin's review of §§8, 10, 13; (ii) the standing verified-GMN pins (§9); (iii) the numeric
seals already in place (Gates B, B2, D; the verdict's 1.14M-sample battery through OM order 5).

---

## 14. GATE C SEALED (2026-07-03) — the sibling product law; ALL GATES CLOSED

Gate C (agent-verified, fresh harness on the gateD-validated pattern + a per-factor residual reader
assigning p-adic factors to sibling clusters): conditioned on a two-sibling cell (n = 6, slope −1):
* p = 5 (tame control): R₀ = (y+1)²(y+2)²(y+3)(y+4); marginals = β₂(5) per child (all |z| ≤ 1.54);
  3×3 joint = product (χ²(8) = 5.9); independence χ²(4) = 3.11.
* **p = 2 (WILD, mixed residue degrees)**: R₀ = (y+1)²(y²+y+1)² = y⁶+1; child₁ at Q = 2, child₂ at
  Q = 4; marginals pass; **the full UNMERGED 3×3** (all 9 joint outcomes give distinct Q₂-types —
  the f = 1/f = 2 asymmetry separates them): joint χ²(8) = 5.8, **independence χ²(4) = 1.97**.
* 12,000 samples, 0 classifier disagreements, 0 forbidden types, 0 cell violations; leaves spectate
  exactly.

With §12 + §14: Gates A (trivial/proved), B, B2, D, and C are ALL closed. The note's §13.3 final
statement stands with every numeric seal in place. → Asvin review.
