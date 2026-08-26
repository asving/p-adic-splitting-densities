# Ramified level-1 norm exactness at the frame key — completion-free (unit MRAMX, 2026-08-26)

**Charge** (BLOCKERS_PLAN_2026-08-26.md, F2 nodes F2.3–F2.6; `runs/wave-b/brief_MRAMX.md`):
state and prove, as rigorous informal mathematics fit to the landed corpus, the ramified
level-1 exactness at `AdjoinRoot F.key` — the B53b analogue one level up — including the
initial-determinant noncancellation as its own named statement, **completion-free** (the
signed C.27 carries no `IsAdicComplete`; `leanspec/Leanspec/ChapC.lean:883-889`).

**Contract** (fixed by the plan; the bare norm-nonzero implication was REFUTED and is NOT
resurrected here): this unit's exactness SUPPLIES a nonzero scalar principal-ideal-membership
certificate; the landed quotient symmetry TRANSFERS it (BW1 interfaces
`DEC4Check.addVal_norm_symm`, `DEC4Check.normA_ne_zero_of_normB_ne_zero`,
`DEC4Check.normB_ne_zero_of_normA_ne_zero`, `leanfinal/scratch/DEC4_check.lean:42-131`).

**Status of this document: the theorem is PROVED below with no open gaps at math level.**
Every step is finite/graded commutative algebra over the DVR — no completion, no Hensel, no
new cite. The examples-first certificate (`verification/ramx_cert.py`, log
`verification/ramx_cert.log`) checks the formula exactly on 4,433 instances across 7 frames
(two independent norm computations per instance) and exhibits the predicted violation when
residual irreducibility is dropped. Definition-faithfulness of the STATEMENT (like all new
statements) is flagged for the standing trust-boundary review.

---

## 0. Setting and notation (corpus vocabulary, re-bound)

Throughout: `O` a commutative domain and discrete valuation ring, `π : O` with
`hπ : Irreducible π`, `v := IsDiscreteValuationRing.addVal O` (values in `ℕ∞`), residue field
`k := IsLocalRing.ResidueField O`, `res : O → k` the residue map.

`F : KeyFrame O π` (`leanfinal/Uniformity/ChapC/C01.lean:80-100`) carries:
`e₁ f₁ h : ℕ` with `0 < e₁`, `0 < f₁`, `Nat.Coprime h e₁`; `Φ′ := F.key` monic irreducible
with `Φ′.natDegree = e₁ * f₁ =: D′`; purity `hpure : IsPure Polynomial.X Φ′ h e₁`
(B34: `OnSide` at BOTH abscissae `0` and `D′`); `hne : (sideSet X Φ′ h e₁).Nonempty`; and
`hresirr`: for the pinned height `H₀`, `resPoly π X Φ′ h e₁ hne H₀` is irreducible of
`natDegree = f₁`.

**The weight.** For `P : Polynomial O` write `W(P) := F.stageHeight P ∈ ℕ∞`
(C02: `stageHeight F A := suppVal X A F.h F.e₁`), i.e. by the landed flattening
`stageHeight_eq_coeff_inf` (`leanfinal/Uniformity/ChapC/C131p.lean:112-117`):

    W(P) = inf_{a ≤ natDegree P} ( e₁ • v(P.coeff a) + h·a ) .

`W(P) = ⊤ ↔ P = 0`; `W(P·Q) ≥ W(P) + W(Q)` is LANDED (B33
`suppVal_add_le_suppVal_mul` at `φ := X`, `(u,ℓ) := (h,e₁)`). For `P ≠ 0` the inf is over a
finite set and is attained; write `Att(P) := {a : e₁·v(P.coeff a) + h·a = W(P)}` ≠ ∅.

**Purity reads on the key** (used throughout; all one-line consequences of `hpure`):

- (P1) `W(Φ′) = h·D′` — `hpure.2` (`OnSide` at `D′`) with monic top coefficient:
  `e₁•v(1) + h·D′ = suppVal`, so the inf equals `h·D′`.
- (P2) `e₁·v(Φ′.coeff 0) = h·D′`, i.e. `v(Φ′.coeff 0) = h·f₁` — `hpure.1`; this is the landed
  `isPure_addVal_coeff_zero F.hmonic F.hpure` (`leanfinal/Uniformity/ChapC/C27.lean:164-171`).
- (P3) every `a ∈ Att(Φ′)` satisfies `e₁ ∣ a` (from `e₁·v = h·(D′−a)` and `Coprime h e₁`),
  and `{0, D′} ⊆ Att(Φ′)`.

**The module.** `A := AdjoinRoot Φ′`, free over `O` with power basis `1, β, …, β^{D′−1}`
(`AdjoinRoot.powerBasis' F.hmonic`), `β := AdjoinRoot.root Φ′`; `finrank O A = D′ > 0`.
`A` is a domain: `Φ′` is irreducible (`F.hirr`) in the UFD `O[X]`, hence prime, hence
`Ideal.span {Φ′}` prime (the B53b `keyIsDomain` argument verbatim, keyed on `F.hirr` instead
of `IsKey`).

**The filtration.** `Fil_γ(A) := (Ideal.span {Φ′}).Quotient`-image of
`{P : W(P) ≥ γ}` under `AdjoinRoot.mk Φ′`, for `γ : ℕ` — an `O`-submodule chain,
decreasing, `Fil_0(A) = A`, with `π·Fil_γ ⊆ Fil_{γ+e₁} ⊆ Fil_{γ+1}` (so each
`Fil_γ/Fil_{γ+1}` is a `k`-vector space).

---

## 1. The theorems

**THEOREM T1 (ramified level-1 norm exactness; the plan's F2.3+F2.4+F2.6 value clause).**
For every `A₀ : Polynomial O` with `A₀ ≠ 0` and `A₀.natDegree < D′`:

    v( Algebra.norm O (AdjoinRoot.mk Φ′ A₀) )  =  f₁ • W(A₀)        (in ℕ∞; both sides finite)

Proposed Lean signature (elaboration-probed, `leanfinal/scratch/MRAMX_probe.lean`):

    theorem ramified_addVal_norm_exact (hπ : Irreducible π) (F : KeyFrame O π)
        {A₀ : Polynomial O} (h0 : A₀ ≠ 0) (hdeg : A₀.natDegree < F.key.natDegree) :
        addVal O (Algebra.norm O (AdjoinRoot.mk F.key A₀)) = F.f₁ • F.stageHeight A₀

At the degenerate frame `h = 0` (forcing `e₁ = 1`, `D′ = f₁`) this is exactly the landed
B53c `addVal_norm_key_eval` instance read through `stageHeight = gaussVal` (C05); at `h ≥ 1`
it is the ramified generalization: B53b's `π^c`-times-unit mechanism is unavailable because
`A` is no longer a DVR with uniformizer `π`.

**THEOREM T2 (the scalar-membership certificate; the plan's F2.6 membership clause).**
For every `z : A`, `z ≠ 0`:

    Algebra.norm O z ≠ 0   ∧   algebraMap O A (Algebra.norm O z) ∈ Ideal.span {z} .

In particular at `z := AdjoinRoot.mk Φ′ A₀` (nonzero whenever `A₀ ≠ 0` and
`natDegree A₀ < D′`, since monic `Φ′` cannot divide `A₀`), the scalar
`c := Algebra.norm O z` is a nonzero element of `O` with `algebraMap c ∈ (z)` and, by T1,
`v(c) = f₁ • W(A₀)`. **This is exactly the input shape of the landed transfer**
`normA_ne_zero_of_normB_ne_zero` / `normB_ne_zero_of_normA_ne_zero` and hence of
`addVal_norm_symm` — the honest contract: exactness supplies membership, symmetry transfers.

**What "exact" means here.** The trivial half is `v(norm) ≥ f₁•W(A₀)` (every determinant
term pays the weight); exactness is the equality — the initial (least-weight) contribution
does not cancel. The entire cancellation analysis is isolated in NC/SPREAD below.

---

## 2. The noncancellation, as its own statements

**LEMMA NC (level-1 ramified product exactness — the "initial-determinant
noncancellation" of the plan's F2.5, in polynomial form).** For `P, Q : Polynomial O`
nonzero with `natDegree P < D′` and `natDegree Q < D′`:

    W( (P * Q) %ₘ Φ′ ) = W(P) + W(Q) .

(Consequently `Fil` is multiplicative-exact on canonical representatives; §3.6 turns this
into the graded band count that replaces the plan's initial-matrix determinant.)

**LEMMA SPREAD (the initial-form arithmetic feeding NC).** Work in the two-variable
polynomial ring `k[t,x]` (a domain), graded by `wt(t) = e₁`, `wt(x) = h`. For nonzero
`P` with `W(P) = γ < ⊤` define the **initial form**

    in(P) := Σ_{a ∈ Att(P)} res( P.coeff a · π^{−v(P.coeff a)} ) · t^{v(P.coeff a)} x^a ∈ k[t,x],

a nonzero wt-homogeneous element of weight γ. Then:

1. (additive extraction) for each γ the map `in_γ` — defined coefficientwise by
   `in_γ(P) := Σ_{a : e₁ ∣ (γ−h·a), i(a) := (γ−h·a)/e₁ ≥ 0} res(P.coeff a · π^{−i(a)}) t^{i(a)} x^a`
   — is additive on `{P : W(P) ≥ γ}`, equals `in(P)` when `W(P) = γ`, and equals `0` when
   `W(P) > γ`;
2. (multiplicativity) `W(P·Q) = W(P) + W(Q)` and `in(P·Q) = in(P)·in(Q)` for all nonzero
   `P, Q` — level-1 Gauss exactness at slope `h/e₁`;
3. (spread decomposition, `h ≥ 1`) every nonzero wt-homogeneous `H ∈ k[t,x]` factors
   UNIQUELY as `H = x^α t^β · S(u)` with `α, β : ℕ`, `u ∈ k[y]`, `u(0) ≠ 0`, where
   `S(u) := Σ_m u_m t^{h·(deg u − m)} x^{e₁·m}`; and `S(u)·S(v) = S(u·v)`;
4. (the key's initial form) `in(Φ′) = S(ψ)` where
   `ψ(y) := Σ_{b=0}^{f₁} res(Φ′.coeff (e₁·b) · π^{−h(f₁−b)}) y^b` is **monic of degree `f₁`
   with `ψ(0) ≠ 0`**, and — via the interface I1 below — `ψ` is `hresirr`'s residual
   polynomial, hence **irreducible in `k[y]`**.

**INTERFACE I1 (resPoly identification; bookkeeping, no mathematics).** At the frame key,
`sideMin X Φ′ h e₁ hne = 0` and `sideMax = D′` (both endpoints on-side by `hpure`; the
range caps at `D′`), so `sideDeg = f₁`, the pin is `H₀ = h·f₁` (P2), and B29's
`resPoly π X Φ′ h e₁ hne (h·f₁)` has `k`-th coefficient the residue of
`Φ′.coeff (e₁·k)` read at height `h·f₁ − h·k` — coefficientwise equal to `ψ` above under
the canonical identification `resField X ≅ k`. `hresirr H₀ rfl` then supplies
`Irreducible ψ` and `ψ.natDegree = f₁`. (`ψ(0) ≠ 0` is NOT taken from B.30 — it is (P2)
directly, so no `IsKey` detour is needed.)

---

## 3. Proofs

### 3.1 Attainment and the purity reads

For `P ≠ 0` the set `{a ≤ natDegree P : P.coeff a ≠ 0}` is nonempty and finite, and on it
the weight `e₁•v + h·a` is `ℕ`-valued, so `W(P) < ⊤` and `Att(P) ≠ ∅`. (P1)–(P3) are as
displayed in §0; (P3): `e₁·v(c_a) = h·D′ − h·a = h·(D′−a)`, and `Coprime h e₁` forces
`e₁ ∣ (D′−a)`, i.e. `e₁ ∣ a`.

### 3.2 Initial forms: additivity and multiplicativity (SPREAD 1–2)

*Additivity.* Fix γ and `P, Q` with `W ≥ γ`. For each admissible `a` (i.e. `e₁ ∣ γ−ha`,
`i(a) ≥ 0`): `v(P.coeff a) ≥ i(a)` (from `e₁•v + ha ≥ γ`), and residue extraction
`c ↦ res(c·π^{−i})` is additive on `{c : v(c) ≥ i}`. Coefficients with `v > i(a)` extract
to `0`; hence `in_γ(P) = in(P)` iff some coefficient attains (iff `W(P) = γ`), else `0`. ∎

*Multiplicativity.* Let `γ = W(P)`, `δ = W(Q)`. For an index `c` with `e₁ ∣ (γ+δ−hc)` and
`i(c) := (γ+δ−hc)/e₁ ≥ 0`:

    (P·Q).coeff c = Σ_{a+b=c} P.coeff a · Q.coeff b ,

and each summand has `e₁·v(P_a·Q_b) ≥ (γ−ha) + (δ−hb) = e₁·i(c)`, so `v((PQ)_c) ≥ i(c)`
— this is `W(PQ) ≥ γ+δ` again (or cite B33). Extracting the residue at `i(c)`:
summands with `v(P_a) + v(Q_b) > i(c)` die; a summand survives only when BOTH factors
attain their own weights (each `≥` its bound, the sum an equality), and then
`res(P_aQ_bπ^{−i(c)}) = res(P_aπ^{−v(P_a)})·res(Q_bπ^{−v(Q_b)})`. Summing over `a+b=c`:
the `t^{i(c)}x^c`-coefficient of `in_γ+δ(PQ)` equals the corresponding coefficient of the
product `in(P)·in(Q)` (in the product of two wt-homogeneous elements, every monomial pair
`t^{v(P_a)}x^a · t^{v(Q_b)}x^b` with `a+b=c` lands in the single slot `t^{i(c)}x^c`, by
homogeneity). Hence `in_{γ+δ}(P·Q) = in(P)·in(Q)`, which is **nonzero** because `k[t,x]`
is a domain and `in(P), in(Q) ≠ 0`. A nonzero extraction at weight `γ+δ` forces
`W(PQ) = γ+δ` and `in(PQ) = in(P)in(Q)`. ∎

### 3.3 The spread decomposition (SPREAD 3–4); `h ≥ 1` here, `h = 0` in §3.8

Let `H ≠ 0` be wt-homogeneous of weight `w`. Every monomial `t^i x^a` of `H` satisfies
`e₁ i + h a = w`, so `h·a ≡ w (mod e₁)`; since `Coprime h e₁`, the exponents `a` in the
support of `H` lie in ONE residue class mod `e₁`. Let `α := min` such `a` (the x-order),
so the support is `{α + e₁ m : m ∈ M}` for a finite `M ∋ 0`, with t-exponents
`i(m) = (w − hα − he₁ m)/e₁` strictly decreasing in `m`; let `Mx := max M` and
`β := i(Mx) ≥ 0` (the t-order). Then

    H = x^α t^β · Σ_m c_m t^{h·(Mx−m)} x^{e₁ m} = x^α t^β · S(u),  u(y) := Σ_m c_m y^m,

with `deg u = Mx`, `u(0) = c_0 ≠ 0` (definition of α). Uniqueness: in `x^α t^β S(u)` with
`u(0) ≠ 0`, the x-order is `α` (as `S(u)`'s x-order is `e₁·ord_y(u) = 0`) and the t-order
is `β` (as `S(u)`'s t-order is `h·(deg u − deg u) = 0`, the top coefficient of `u` being
nonzero); then `u` is forced coefficientwise. Product law: for `u, v ∈ k[y]` with
`deg(uv) = deg u + deg v` (automatic over the field `k`),

    S(u)·S(v): the x^{e₁c}-coefficient is Σ_{m+m'=c} u_m v_{m'} t^{h(deg u−m)+h(deg v−m')}
             = (uv)_c · t^{h(deg uv − c)},   i.e.  S(u)S(v) = S(uv).

(No Laurent ring is needed; the t-exponent is the same for every pair in the convolution.)

*SPREAD 4.* By (P3) the attaining abscissae of `Φ′` are `a = e₁ b`; by (P1) the attained
values give `v(Φ′.coeff (e₁b)) = h·(f₁ − b)`. So `in(Φ′) = Σ_b ψ_b t^{h(f₁−b)} x^{e₁ b}`
`= S(ψ)` with `ψ_b := res(Φ′.coeff(e₁b)·π^{−h(f₁−b)})` (non-attaining `b` giving `ψ_b = 0`
consistently). Top: `b = f₁`, coefficient `res(1) = 1` — `ψ` monic of degree `f₁`
(so `x`-order of `S(ψ)` is `0` and t-order `0`). Bottom: `b = 0`, `ψ_0 ≠ 0` by (P2).
Irreducibility via I1. ∎

### 3.4 Proof of LEMMA NC

Write `w := W(P) + W(Q)` (finite, §3.1), `R := (P·Q) %ₘ Φ′` and `Sq := (P·Q) /ₘ Φ′`, so
`P·Q = R + Sq·Φ′` (`Polynomial.modByMonic_add_div`, `F.hmonic`).

*(≥, the division estimate — the plan's F2.4 in one induction.)* Claim: for every `T`,
`W(T %ₘ Φ′) ≥ W(T)`. Induction on `natDegree T`: if `deg T < D′` then `T %ₘ Φ′ = T`.
Otherwise, with `d := natDegree T` and `τ := T.coeff d`:
`T' := T − τ·X^{d−D′}·Φ′` has degree `< d`, the same class mod `Φ′` and the same `%ₘ`, and

    W(τ·X^{d−D′}·Φ′) ≥ (e₁•v(τ) + h(d−D′)) + W(Φ′) = e₁•v(τ) + h·d ≥ W(T)

(B33 submultiplicativity; (P1); the last step because `e₁•v(τ) + h·d` is one of the terms
in `W(T)`'s inf). Ultrametrically `W(T') ≥ min(W(T), W(τX^{d−D′}Φ′)) ≥ W(T)`; induct.
Applied to `T := P·Q` with `W(PQ) = w` (§3.2): `W(R) ≥ w`.

*(≤, the noncancellation.)* Suppose `W(R) > w` (including `R = 0`). Apply the additive
extraction `in_w` (§3.2.1) to `P·Q = R + Sq·Φ′` — all three terms have `W ≥ w`
(for `Sq·Φ′`: `W(SqΦ′) ≥ min(W(PQ), W(R)) ≥ w` since `SqΦ′ = PQ − R`; if `Sq = 0` then
`R = PQ` and `W(PQ) = w`, contradiction):

    in(P)·in(Q) = in_w(P·Q) = in_w(R) + in_w(Sq·Φ′) = 0 + in_w(Sq·Φ′).

So `in_w(SqΦ′) ≠ 0`, forcing `W(Sq·Φ′) = w`, and by §3.2.2 (applied to `Sq, Φ′`):
`W(Sq) = w − h·D′` and

    in(P)·in(Q) = in(Sq)·in(Φ′) = in(Sq)·S(ψ).

Decompose each initial form by SPREAD 3: `in(P) = x^{α}t^{β}S(u)`,
`in(Q) = x^{α'}t^{β'}S(v)`, `in(Sq) = x^{α''}t^{β''}S(z)`. Using `S(·)`'s product law and
matching the unique decompositions of the two sides (`z·ψ` and `u·v` have nonzero constant
terms, so both sides are decomposed forms):

    α'' = α + α',  β'' = β + β',  z·ψ = u·v   in k[y].

`ψ` is irreducible in `k[y]` (I1) and `k[y]` is a UFD, so `ψ ∣ u` or `ψ ∣ v` — say
`ψ ∣ u`, so `deg u ≥ f₁`. But the x-degree of `in(P)` is `α + e₁·deg u ≥ e₁·f₁ = D′`,
while the x-degree of `in(P)` is at most `natDegree P < D′`. Contradiction. Hence
`W(R) = w`. ∎

*(Remark.)* The same argument with `P·Q` replaced by a monic factorization `Φ′ = U·V`
shows `F.hirr` is implied by purity + `hresirr` — the mechanism is strictly stronger than
the frame needs. Not used below.

### 3.5 The filtration on `A`: canonical representatives and graded dimensions

*(Canonical representative computes the filtration.)* For `P₀` with `natDegree P₀ < D′`:
`mk Φ′ P₀ ∈ Fil_γ(A)` **iff** `W(P₀) ≥ γ`. (⇐) by definition. (⇒) if `mk P₀ = mk P` with
`W(P) ≥ γ` then `P₀ = P %ₘ Φ′` (uniqueness of the `< D′` representative), and the division
estimate (§3.4 ≥) gives `W(P₀) ≥ W(P) ≥ γ`. Consequently define, for `z ∈ A` nonzero with
canonical representative `P₀`: `W_A(z) := W(P₀)`; then `Fil_γ(A) = {z : W_A(z) ≥ γ}` (with
`W_A(0) = ⊤`).

*(Filtration product exactness.)* For nonzero `y, z ∈ A` with canonical reps `P, Q`:
the canonical rep of `y·z` is `(P·Q) %ₘ Φ′`, so **NC says `W_A(y·z) = W_A(y) + W_A(z)`**
(in particular `A` is again seen to be a domain, and `W_A` is a `ℕ`-valued additive
weight on `A ∖ {0}`).

*(Graded dimensions.)* For `γ : ℕ` set

    d(γ) := #{ (i,a) : i ≥ 0, 0 ≤ a < D′, e₁·i + h·a = γ } .

Claim: `dim_k ( Fil_γ(A) / Fil_{γ+1}(A) ) = d(γ)`. The map sending `(i,a)` to the class
of `mk(π^i X^a)` lands in `Fil_γ/Fil_{γ+1}` and is `k`-linearly EXTENDED; it is:

- *surjective*: a class of `mk P₀`, `W(P₀) = γ`, equals `Σ_{a ∈ Att(P₀)} res(P₀_a π^{−v})·
  [mk(π^{v(P₀_a)}X^a)]` modulo `Fil_{γ+1}` (non-attaining coefficients have weight `> γ`);
- *injective*: a `k`-combination `Σ r_{(i,a)}·[mk(π^i X^a)]` with lifts `r̃` assembles to
  `R₀ := Σ r̃_{(i,a)} π^i X^a`, of degree `< D′` — its OWN canonical representative — and if
  some `r_{(i,a)} ≠ 0` then `W(R₀) = γ` exactly (distinct basis monomials do not interact:
  the coefficient of `X^a` is `r̃ π^i` with `v = i` iff `r ≠ 0`), so `mk R₀ ∉ Fil_{γ+1}`
  by the canonical-representative characterization. **No irreducibility is used here.**

So `dim_k gr_γ(A) = d(γ)`, and explicitly: the admissible `a` form one residue class mod
`e₁` intersected with `[0, D′)` and `{a : h·a ≤ γ}` — hence

    d(γ) = #{a ∈ [0,D′) : h·a ≡ γ (mod e₁), h·a ≤ γ},   and   d(γ) = f₁  for  γ ≥ h·(D′−1).

(For `γ ≥ h(D′−1)` every one of the `f₁` class members `a < D′ = e₁f₁` satisfies `ha ≤ γ`.)

### 3.6 The band count on `A ⧸ zA`

Fix `z ≠ 0` in `A`, `s := W_A(z)`. Give `A ⧸ zA` the image filtration
`Fil_γ(A/zA) := (Fil_γ(A) + zA)/zA`. Then, for every `γ`:

    dim_k ( Fil_γ(A/zA) / Fil_{γ+1}(A/zA) ) = d(γ) − d(γ−s)      (d(negative) := 0).

Proof. By the second isomorphism and the modular law (`Fil_{γ+1} ⊆ Fil_γ`):

    gr_γ(A/zA) ≅ Fil_γ(A) / ( Fil_{γ+1}(A) + (zA ∩ Fil_γ(A)) ).

By §3.5 product exactness, `z·a ∈ Fil_γ(A) ⇔ W_A(a) ≥ γ − s`, so
`zA ∩ Fil_γ(A) = z·Fil_{γ−s}(A)` (`:= zA` when `γ ≤ s`). The image of `z·Fil_{γ−s}(A)`
inside `gr_γ(A)` is the image of the `k`-linear map `gr_{γ−s}(A) → gr_γ(A)`,
`[a] ↦ [z·a]` (well-defined and `k`-linear since `z·Fil_{γ−s+1} ⊆ Fil_{γ+1}`), which is
INJECTIVE: `z·a ∈ Fil_{γ+1} ⇒ W_A(a) ≥ γ+1−s ⇒ [a] = 0` — product exactness again, i.e.
NC. (For `γ < s` the image is `0` and `d(γ−s) = 0` consistently.) Hence
`dim gr_γ(A/zA) = d(γ) − d(γ−s)`. ∎

### 3.7 Assembly: proof of T1

Let `z := mk Φ′ A₀`, `s := W(A₀) = W_A(z)` (§3.5; `A₀` is its own canonical rep).

1. `z ≠ 0` (monic `Φ′` of degree `D′` cannot divide nonzero `A₀` of smaller degree), so
   `Algebra.norm O z ≠ 0` by T2's first clause (§3.8, independent of T1), and by the
   LANDED dictionary `length_quot_eq_addVal_norm`
   (`leanfinal/Uniformity/ChapB/B53c.lean:121-140`; `A` free of positive rank `D′`):

       λ := Module.length O (A ⧸ Ideal.span {z}) = v(Algebra.norm O z) < ⊤.

2. *(Chain finiteness.)* `𝔪^λ` kills the length-`λ` module `A/zA` (Jordan–Hölder: each
   simple subquotient over the local ring `O` is `≅ k`, so `𝔪` moves each step down).
   For the canonical representative of any element of `Fil_γ(A)`, every coefficient has
   `v ≥ (γ − h(D′−1))/e₁`, so `Fil_γ(A) ⊆ π^{N(γ)}·A` with `N(γ) := ⌈(γ−h(D′−1))/e₁⌉`.
   Hence `Fil_γ(A/zA) ⊆ π^{N(γ)}(A/zA) = 0` once `N(γ) > λ.toNat`; fix
   `Γ := e₁·(λ.toNat + 1) + h·(D′−1) + s` (so also `Γ − s + 1 > h(D′−1)`).

3. *(Length along the finite chain.)* `A/zA = Fil_0 ⊇ Fil_1 ⊇ … ⊇ Fil_{Γ+1} = 0`, and
   length is additive with `length(k-space of dim d) = d`:

       λ = Σ_{γ=0}^{Γ} dim_k gr_γ(A/zA) = Σ_{γ=0}^{Γ} ( d(γ) − d(γ−s) )
         = Σ_{γ=Γ−s+1}^{Γ} d(γ)                                    (telescoping)
         = f₁ · s                                                  (§3.5: d ≡ f₁ on that range).

So `v(Algebra.norm O z) = λ = f₁·s = f₁ • W(A₀)`. ∎

### 3.8 Proof of T2, and the degenerate frame

*(Norm nonzero.)* `A` is a domain (§0) and `z ≠ 0`, so multiplication by `z` is an
injective `O`-linear endomorphism of the free module `A`; over the fraction field
`K := Frac O` the induced endomorphism of `A ⊗ K` is still injective (localization is
flat/exact), hence bijective on the finite-dimensional `K`-space, hence
`Algebra.norm O z = det ≠ 0` (the determinant is unchanged by scalar extension).

*(Membership.)* Let `χ ∈ O[T]` be the characteristic polynomial of `lmul z` (an `O`-linear
endomorphism of free `A` of rank `n := D′`). Cayley–Hamilton (`LinearMap.aeval_self_charpoly`)
gives `aeval (lmul z) χ = 0`; since `Algebra.lmul : A →ₐ End_O(A)` is an algebra
homomorphism, `aeval (lmul z) χ = lmul (aeval z χ)`, and `lmul` is injective (`w·1 = 0 ⇒
w = 0`). So `χ(z) = 0` in `A`. With `χ = T^n + c_{n−1}T^{n−1} + … + c_1 T + c_0` and
`c_0 = (−1)^n · Algebra.norm O z`:

    algebraMap (Algebra.norm O z) = (−1)^{n+1} · z · ( z^{n−1} + c_{n−1} z^{n−2} + … + c_1 )
      ∈ Ideal.span {z}. ∎

*(Degenerate frame `h = 0`.)* Then `Coprime 0 e₁` forces `e₁ = 1`; weights: `wt(x) = 0`,
`in(Φ′) = ψ(x)·t^0` with `ψ` = the residue-reduction of `Φ′`, irreducible by `hresirr`
(this is the `IsKey` regime). The SPREAD-3 argument is not needed: in the divisibility
endgame of §3.4, `in(Sq)·ψ(x) = in(P)·in(Q)` in `k[t][x]` where `ψ(x)` is irreducible in
`k[x]`, hence prime in `k[t][x]` (`(k[x]/ψ)[t]` is a domain), so `ψ ∣ in(P)` or
`ψ ∣ in(Q)` in `k[t][x]`, contradicting `deg_x < D′` as before. All other sections are
uniform in `h`. (Consistency: T1 at `h = 0` is B53c's `addVal_norm_key_eval` read through
C05's `stageHeight = gaussVal` — and battery 7 of the cert checks it numerically.)

---

## 4. The certificate (examples-first record)

`verification/ramx_cert.py` (log `verification/ramx_cert.log`, run 2026-08-26): for each
frame, EVERY nonzero `A₀` over a coefficient grid with `deg A₀ < D′` is checked for
`v_p(N) = f₁·min_j(e₁·v_p(a_j) + h·j)`, with the norm computed TWO independent ways
(`Res(Φ′, A₀)` and `det` of the multiplication matrix on the power basis; asserted equal).

| battery | p | (e₁,h,f₁) | Φ′ | instances | result |
|---|---|---|---|---|---|
| eisenstein-x2-2 | 2 | (2,1,1) | x²−2 | 63 | exact |
| eisenstein-x2+2x+2 | 2 | (2,1,1) | x²+2x+2 | 63 | exact |
| ram-res-x4+2x2+4 | 2 | (2,1,2) | x⁴+2x²+4 (ψ=y²+y+1) | 2400 | exact |
| slope23-x3-4 | 2 | (3,2,1) | x³−4 | 511 | exact |
| p3-x4+3x2+18 | 3 | (2,1,2) | x⁴+3x²+18 (ψ=y²+y+2) | 1295 | exact |
| p5-e1-h1-f2 | 5 | (1,1,2) | x²+5x+50 (ψ=y²+y+2) | 48 | exact |
| degenerate-h0 | 2 | (1,0,2) | x²+x+1 | 63 | exact |
| **NEG control** | 3 | (1,1,2) | x²+18, ψ=(y−1)(y+1) REDUCIBLE | 63 | **10 violations** |

The negative control keeps every frame hypothesis EXCEPT `hresirr` — including
irreducibility of `Φ′` over the (incomplete) base — and fails exactly as §3.4 predicts
(first violation `A₀ = x+3`: `v(N) = 3 > f₁·s = 2`; the residual of `A₀` is `y+1`, a root
of ψ). Residual irreducibility is the load-bearing hypothesis, also over incomplete `O`.

---

## 5. Formalization-trivial node decomposition (wired to the plan's C.27 rows)

The plan priced F2.3–F2.6 at 285–485 lines for the determinant-expansion route and flagged
F2.5's basis permutation as unclear. The route above REPLACES the determinant expansion by
the graded-length route through the LANDED B53c dictionary; the honest re-estimate is
**480–780 lines** — larger in total, but every node is finite `Polynomial`/`Finset`
arithmetic with no graded-ring typeclasses, no completion, no new cite, and the one
genuinely new mechanism (X5) is one-variable UFD reasoning. Node ↔ plan-row wiring:
X1–X4 + X6 replace F2.4's weighted filtration; X5 + NC are F2.5's noncancellation (initial
matrix superseded); X7–X9 are F2.6; X0 is F2.3.

| node | statement (Lean shape) | inputs (landed names) | mechanism | est. lines |
|---|---|---|---|---|
| X0 (=F2.3) | `ramified_addVal_norm_exact` and `ramified_norm_scalar_membership` statement carriers as in §1 | `KeyFrame`, `stageHeight`, `AdjoinRoot`, `Algebra.norm`, `addVal` | statement only; elaboration probed in `leanfinal/scratch/MRAMX_probe.lean` | 15–25 |
| X1 | weight basics: attainment, `W = ⊤ ↔ P = 0`, purity reads (P1)–(P3) | `stageHeight_eq_coeff_inf` (C131p), `isPure_addVal_coeff_zero` (C27), `OnSide`, `F.hmonic`, `F.hcop` | Finset.inf attainment; `Nat.Coprime.dvd_of_dvd_mul_left` for (P3) | 40–70 |
| X2 | `in_γ` extraction into `k[t][x]` (`Polynomial (Polynomial k)`): additivity; `in(P)≠0` at attainment | X1; `IsLocalRing.residue`; polynomial `ext` | coefficientwise definition of §2; residue additivity on `v ≥ i` | 60–100 |
| X3 | level-1 Gauss exactness: `W(PQ) = W(P)+W(Q)` and `in(PQ) = in(P)·in(Q)` | X2; B33 `suppVal_add_le_suppVal_mul` (φ := X) for the ≥ half | §3.2 convolution + domain `k[t][x]`; NOT the C66b cite (level-2, above-floor — disjoint) | 90–150 |
| X4 | spread decomposition + `S(u)S(v)=S(uv)` + `in(Φ′)=S(ψ)`, ψ monic/deg f₁/ψ(0)≠0 | X1–X3; I1 (below) | §3.3; single-residue-class support from `hcop` | 90–150 |
| I1 | resPoly interface: `sideMin = 0`, `sideMax = D′`, `sideDeg = f₁`, `H₀ = h·f₁`, `resPoly ... = ψ` coefficientwise; import `Irreducible ψ` from `F.hresirr` | B16/B20/B28/B29 defs; `hpure`; (P2) | bookkeeping only; check B.30's `φ = X` instance for reuse | 40–80 |
| X5 (=F2.5 core) | LEMMA NC: `W((P*Q) %ₘ F.key) = W(P) + W(Q)` for nonzero `P,Q` of degree `< D′` | X1–X4, I1; `Polynomial.modByMonic_add_div` | §3.4: division estimate (induction) + `in_w` cancellation analysis + `ψ ∣ u ∨ ψ ∣ v` in the UFD `k[y]` + x-degree fence; `h = 0` branch via `ψ(x)` prime in `k[t][x]` | 80–130 |
| X6 | filtration `Fil_γ(A)`; canonical-rep characterization; `dim_k gr_γ(A) = d(γ)`; `d(γ) = f₁` for `γ ≥ h(D′−1)` | X1, X5(≥ half); `AdjoinRoot.powerBasis'`; `keyIsDomain`-analogue at `F.hirr` | §3.5; the injectivity needs NO irreducibility | 70–120 |
| X7 | band count: `dim_k gr_γ(A/zA) = d(γ) − d(γ−s)` | X5, X6; modular law (`Submodule` lattice) | §3.6 | 50–90 |
| X8 (=F2.6 value) | T1 assembly: chain finiteness, telescoping, dictionary | X6, X7; **landed** `length_quot_eq_addVal_norm` (B53c); `Module.length` additivity (mathlib) | §3.7; `𝔪^λ`-kill of finite-length modules (mathlib or 15-line induction) | 70–120 |
| X9 (=F2.6 membership) | T2: norm ≠ 0 for `z ≠ 0` in the domain `A`; `algebraMap (norm z) ∈ span {z}` | `F.hirr` (domain); `LinearMap.aeval_self_charpoly`, `LinearMap.det_eq_sign_charpoly_coeff`, `Algebra.norm_apply` | §3.8. **Membership half + the domain instance ALREADY PROVED Lean-core** in `leanfinal/scratch/MRAMX_probe.lean` (`norm_mem_span_self` — fully generic in the algebra — and `keyFrame_isDomain`; exit 0, footprints `[propext, Classical.choice, Quot.sound]`) | 25–50 remaining (norm ≠ 0 via `Frac O`) |

Consumer wiring (NOT this unit's scope, recorded for F2.7): at `A₀ := dev F.key g 0`
(nonzero iff `F.key ∤ g`, degree `< D′` by B.03), X0's certificate is exactly the
`hmemB`/`hc` input pair of `normA_ne_zero_of_normB_ne_zero`, whose output plus
`addVal_norm_symm` converts T1's value into the `AdjoinRoot g`-side norm valuation that
`slot2_exact_resigned_key` (plan F2.7) needs, together with `dv2Hgt_key` (LANDED,
`leanfinal/Uniformity/ChapC/C27x.lean:241`) on the slot side.

## 6. Fences (mandated)

1. **Factor-label heredity: NOT assumed, NOT supplied.** T1/T2 are `KeyFrame`-only
   statements about an arbitrary nonzero `A₀` of degree `< D′`; no `LevelDatum`, no
   `HasLabel`, no factorization of any `g` occurs. The general-`C` C.27 additionally needs
   label heredity to monic factors and sits STRICTLY ABOVE the C.35 frontier
   (`leanfinal/Uniformity/ChapC/C27x.lean:77-82`); nothing here weakens that.
2. **Order-2 no-cancellation: OUT of scope.** All grading here is the level-1 X-polygon of
   the key frame (slope `h/e₁`). The level-2 analogue (F2.G2) is untouched.
3. **The bare norm-nonzero implication stays dead.** T2 supplies the nonzero scalar
   MEMBERSHIP certificate; transfer is exclusively through the landed membership-assisted
   theorems (DEC4_check.lean:68-131). No implication between bare norm-nonzero
   propositions is claimed or used.
4. **No cite consumed.** In particular NOT `fgmn_dv_exact_mul` (C66b): that cite is the
   level-2 `dv`-polygon product law above the frame floor (`ℓ·(e₁f₁h) < u`); X3/X5 are the
   level-1 X-polygon statements, proved Lean-core here. No overlap, no re-derivation of a
   cited result under a proof-obligation name.
5. **`D′ ∤ deg g` endpoint caveat unchanged.** C27x's note that `HasLabel` closes the
   F.key-read only when `D′ ∣ deg g` is a CONSUMER (F2.7) matter; T1 is exact for every
   `A₀` and takes no position on it.
6. **Trust boundary.** T1/T2 are new statements: flagged for the standing human review of
   definition faithfulness (statement only; the proof is self-contained above).

## 7. Open items

None at math level: §3 is a complete proof. Probe results
(`leanfinal/scratch/MRAMX_probe.lean`, `lake env lean` exit 0, all footprints Lean-core):
both T1/T2 statement carriers ELABORATE against the landed vocabulary (F2.3 de-risked), and
X9's membership half (`norm_mem_span_self`, generic Cayley–Hamilton) plus the domain
instance (`keyFrame_isDomain`, from `F.hirr` alone) are PROVED. Transcription notes: (a) X3 is the largest
single proof — the convolution bookkeeping should follow §3.2's per-slot residue
extraction literally; (b) mathlib names in X8/X9 (`Module.length` additivity on a chain,
Cayley–Hamilton, charpoly constant coefficient) should be re-searched at the pin, not
trusted from this document; (c) I1 should check whether B.30 at `φ = X` already lands
`ψ(0) ≠ 0`/degree reads before re-proving them.
