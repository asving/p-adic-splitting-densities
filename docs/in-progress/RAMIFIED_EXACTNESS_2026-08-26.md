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

**[MRFIX 2026-08-27] Status of this document: T1 is PARTIAL; T2 is PROVED.**  The adversarial
`Nat`-subtraction error in the extraction map is repaired below, and the guarded definition
supports SPREAD 2, NC, the multiplicative filtration, the band count, and the conditional T1
assembly.  However, the load-bearing coefficient transport **INTERFACE I1 remains OPEN**: until
that explicit bridge is landed, irreducibility of the scalar polynomial `ψ` and hence NC/T1 are
conditional on I1.  No completion or Hensel input is used. The examples-first certificate
(`verification/ramx_cert.py`, log
`verification/ramx_cert.log`) checks the formula exactly on 4,443 instances across 7 frames
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

**[MRFIX 2026-08-27]** At the degenerate frame `h = 0` (forcing `e₁ = 1`, `D′ = f₁`), T1 is
obtained from B53b `span_mk_eq_span_algebraMap_pow` for the arbitrary degree-`<D′` polynomial
`A₀`, followed by the determinant--length dictionary and the length of the scalar-power
quotient; it is **not** an instance of B53c `addVal_norm_key_eval`, whose input is a key
evaluated in a different `AdjoinRoot`.  At `h ≥ 1` this is the ramified generalization:
B53b's `π^c`-times-unit mechanism is unavailable because `A` is no longer a DVR with
uniformizer `π`.

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
polynomial ring `k[t,x]` (a domain), graded by `wt(t) = e₁`, `wt(x) = h`.

**[MRFIX 2026-08-27] Normalized residues.** For `i : ℕ` and `c ∈ (π^i)`, write

    [c]_i := digAt π i c ∈ k.

This is the landed scalar digit of ChapB B21--B22, not the ill-typed expression
`res(c·π^{-i})`.  If `c = π^i u`, B22 `digAt_eq` says `[c]_i = res(u)`; independence of the
chosen `u` follows by cancellation of the nonzero `π^i` in the domain.  B22
`digAt_add` gives additivity on `(π^i)`, and `digAt_eq_zero_iff` says `[c]_i = 0` exactly when
`c ∈ (π^{i+1})`.  The law

    [c d]_{i+j} = [c]_i [d]_j       (c ∈ (π^i), d ∈ (π^j))

is the scalar/constant-polynomial specialization of B35a `resMk_mul`, transported back from
`resField X` along B59a's landed `resFieldXEquiv`; equivalently it follows by writing
`c = π^i u`, `d = π^j v` and applying multiplicativity of `res`.  Thus existence,
independence, additivity, multiplicativity, and exact-vanishing are all supplied by landed
corpus constructions.

For nonzero `P` with `W(P) = γ < ⊤`, define the **initial form** honestly by

    in(P) := Σ_{a ∈ Att(P)} [P.coeff a]_{v(P.coeff a)}
                                      · t^{v(P.coeff a)} x^a ∈ k[t,x].

No attaining coefficient is zero, and `digAt_eq_zero_iff` makes its exact digit nonzero, so
this is a nonzero wt-homogeneous element of weight `γ`. Then:

1. **[MRFIX 2026-08-27] (guarded additive extraction)** for each `γ : ℕ`, define

       in_γ(P) := Σ_{0 ≤ a ≤ natDegree P,
                     h*a ≤ γ AND e₁ ∣ (γ - h*a)}
                     [P.coeff a]_{(γ-h*a)/e₁}
                     · t^{(γ-h*a)/e₁} x^a .

   The conjunction `h*a ≤ γ AND e₁ ∣ (γ - h*a)` is part of the definition; subtraction is
   `Nat` subtraction and is never evaluated as a line height before the inequality guard is
   known.  On `{P : W(P) ≥ γ}`, `in_γ` is additive, equals `in(P)` when `W(P) = γ`, and is
   `0` when `W(P) > γ`;
2. (multiplicativity) `W(P·Q) = W(P) + W(Q)` and `in(P·Q) = in(P)·in(Q)` for all nonzero
   `P, Q` — level-1 Gauss exactness at slope `h/e₁`;
3. (spread decomposition, `h ≥ 1`) every nonzero wt-homogeneous `H ∈ k[t,x]` factors
   UNIQUELY as `H = x^α t^β · S(u)` with `α, β : ℕ`, `u ∈ k[y]`, `u(0) ≠ 0`, where
   `S(u) := Σ_m u_m t^{h·(deg u − m)} x^{e₁·m}`; and `S(u)·S(v) = S(u·v)`;
4. (the key's initial form) `in(Φ′) = S(ψ)` where
   `ψ(y) := Σ_{b=0}^{f₁} [Φ′.coeff (e₁·b)]_{h(f₁−b)} y^b` is **monic of degree `f₁`
   with `ψ(0) ≠ 0`**, and — via the interface I1 below — `ψ` is `hresirr`'s residual
   polynomial, hence **irreducible in `k[y]`**.

**[MRFIX 2026-08-27] INTERFACE I1 (resPoly/scalar-digit identification; OPEN, real proof
node).** The needed statement is the following explicit transport, not definitional
bookkeeping.  Put `H₀ := h*f₁` and let
`E := (resFieldXEquiv O).symm : resField X ≃+* k`. One must prove:

1. `sideMin X Φ′ h e₁ hne = 0`, `sideMax X Φ′ h e₁ hne = D′`, and therefore
   `sideDeg X Φ′ h e₁ hne = f₁`, from both `hpure` endpoints, the range cap, `hdeg`, and
   `he₁`;
2. the non-definitional pin
   `hpin : npHgt X Φ′ (sideMin X Φ′ h e₁ hne) = (H₀ : ℕ∞)`, by rewriting `sideMin = 0`,
   using B15 `npHgt_X`, and converting (P2) to the natural height `v(Φ′.coeff 0)=h*f₁`;
3. coefficientwise, for every `b`,

       E ((resPoly π X Φ′ h e₁ hne H₀).coeff b)
         = [Φ′.coeff (e₁*b)]_{h*(f₁-b)} = ψ.coeff b,

   with the right side read as `0` outside `b ≤ f₁`.  The left equality uses B35c
   `resPoly_coeff_of_pure`, specializes `dev X Φ′ (e₁*b)` via B15 `dev_X`, unfolds
   B25 `resMk`/B23--B24 `digPoly` to the scalar `digAt`, and then uses B59a
   `resFieldXEquiv`/`resFieldXEquiv_coe`.  The height rewrite must use `b ≤ f₁` before the
   `Nat` subtraction.  Polynomial extensionality then gives
   `ψ = (resPoly ... H₀).map E` (with the direction adjusted to the chosen `map`).

Only after these three obligations are proved may `F.hresirr H₀ hpin` be transported along
`Polynomial.mapEquiv E` to obtain `Irreducible ψ` and `ψ.natDegree = f₁`.  In particular the
argument is **not** `hresirr H₀ rfl`: `hpin` is propositionally derived.  Estimated Lean size:
**90--160 lines** (side geometry/pin 25--45; coefficient transport 50--85; irreducibility and
degree transport 15--30).  This node is OPEN.  (`ψ(0) ≠ 0` still comes directly from (P2),
not from B30.)

---

## 3. Proofs

### 3.1 Attainment and the purity reads

For `P ≠ 0` the set `{a ≤ natDegree P : P.coeff a ≠ 0}` is nonempty and finite, and on it
the weight `e₁•v + h·a` is `ℕ`-valued, so `W(P) < ⊤` and `Att(P) ≠ ∅`. (P1)–(P3) are as
displayed in §0; (P3): `e₁·v(c_a) = h·D′ − h·a = h·(D′−a)`, and `Coprime h e₁` forces
`e₁ ∣ (D′−a)`, i.e. `e₁ ∣ a`.

### 3.2 Initial forms: additivity and multiplicativity (SPREAD 1–2)

**[MRFIX 2026-08-27] Additivity and the two comparison laws.** Fix `γ` and `P,Q` with
`W(P),W(Q) ≥ γ`. An index `a` is admissible only after both guards

    h*a ≤ γ,       e₁ ∣ (γ-h*a)

have been proved; put `i(a) := (γ-h*a)/e₁`. The guard and divisibility give the honest
natural-number identity `γ = h*a + e₁*i(a)`. Since each coefficient weight is at least
`W(P) ≥ γ`, cancellation of `h*a` and positivity of `e₁` give
`v(P.coeff a) ≥ i(a)`, and similarly for `Q`. Thus B22 `digAt_add` applies in every admitted
slot and proves `in_γ(P+Q)=in_γ(P)+in_γ(Q)`.

If `W(P)>γ`, then at each admissible slot either `P.coeff a=0`, or

    e₁*v(P.coeff a)+h*a > γ = e₁*i(a)+h*a,

so `v(P.coeff a) ≥ i(a)+1`; B22 `digAt_eq_zero_iff` kills that slot. Hence
`in_γ(P)=0`. If `W(P)=γ`, every attaining `a` automatically satisfies `h*a≤γ` and
`e₁ ∣ (γ-h*a)`, with `i(a)=v(P.coeff a)`; every admitted non-attaining slot has valuation
at least `i(a)+1` and dies. Therefore `in_γ(P)=in(P)`.

The old counterexample is now rejected by the first guard: in the nondegenerate branch
`h≥1`, for `P=X` and `γ=0`, the only possibly nonzero coefficient has `a=1`, but
`h*1≤0` is false. Therefore **`in_0(X)=0`**, in agreement with `W(X)=h>0`. ∎

**[MRFIX 2026-08-27] Multiplicativity.** Let `γ = W(P)`, `δ = W(Q)`. For an output index
`c`, extraction occurs only under the guards

    h*c ≤ γ+δ,       e₁ ∣ ((γ+δ)-h*c),

and then `i(c) := ((γ+δ)-h*c)/e₁` satisfies
`γ+δ = h*c+e₁*i(c)`. Now

    (P·Q).coeff c = Σ_{a+b=c} P.coeff a · Q.coeff b .

Each factor weight is at least `γ` or `δ`; after adding and using `a+b=c`, every product
summand has valuation at least `i(c)`. Extract its digit at height `i(c)`. If the two factor
weights do not both attain `γ` and `δ`, the total weight is strictly larger, so the summand
has valuation at least `i(c)+1` and its digit vanishes. A surviving summand therefore forces
both attainments. Those attainments supply the individual guards `h*a≤γ`, `h*b≤δ` and
heights `v(P_a)=(γ-h*a)/e₁`, `v(Q_b)=(δ-h*b)/e₁`, whose sum is `i(c)`. The landed
normalized-residue product law gives

    [P_a Q_b]_{i(c)} = [P_a]_{v(P_a)} [Q_b]_{v(Q_b)}.

After summing over `a+b=c`, the `t^{i(c)}x^c` coefficient of `in_{γ+δ}(PQ)` equals that of
`in(P)in(Q)`. If an output index fails either guard, no pair of attaining monomials can land
there, because such a pair would prove the output guards. Hence equality also holds in every
zero slot:

    in_{γ+δ}(P·Q) = in(P)·in(Q).

The right side is nonzero in the domain `k[t,x]`. A nonzero extraction at weight `γ+δ`
forces `W(PQ)=γ+δ`, and the already-proved agreement law then gives
`in(PQ)=in(P)in(Q)`. ∎

### 3.3 The spread decomposition (SPREAD 3–4); `h ≥ 1` here, `h = 0` in §3.8

Let `H ≠ 0` be wt-homogeneous of weight `w`. Every monomial `t^i x^a` of `H` satisfies
`e₁ i + h a = w`, so `h·a ≡ w (mod e₁)`; since `Coprime h e₁`, the exponents `a` in the
support of `H` lie in ONE residue class mod `e₁`. Let `α := min` such `a` (the x-order),
so the support is `{α + e₁ m : m ∈ M}` for a finite `M ∋ 0`, with t-exponents
`i(m) = (w − hα − he₁ m)/e₁` strictly decreasing in `m` (here the monomial equality
`e₁*i+h*a=w` proves the minuend bounds before either `Nat` subtraction); let `Mx := max M` and
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

**[MRFIX 2026-08-27] SPREAD 4.** By (P3) the attaining abscissae of `Φ′` are `a = e₁ b`; by (P1) the attained
values give `v(Φ′.coeff (e₁b)) = h·(f₁ − b)`. So `in(Φ′) = Σ_b ψ_b t^{h(f₁−b)} x^{e₁ b}`
`= S(ψ)` with `ψ_b := [Φ′.coeff(e₁b)]_{h(f₁−b)}` for `b≤f₁`; the bound guards the
subtraction, and non-attaining `b` have valuation at least one higher, so their digit is `0`.
Top: `b = f₁`, coefficient `[1]_0 = res(1) = 1` — `ψ` monic of degree `f₁`
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

**[MRFIX 2026-08-27] (≤, guarded noncancellation; conditional on OPEN I1.)** Suppose
`W(R) > w` (including `R = 0`). Apply the guarded additive
extraction `in_w` (§3.2.1) to `P·Q = R + Sq·Φ′` — all three terms have `W ≥ w`
(for `Sq·Φ′`: `W(SqΦ′) ≥ min(W(PQ), W(R)) ≥ w` since `SqΦ′ = PQ − R`; if `Sq = 0` then
`R = PQ` and `W(PQ) = w`, contradiction):

    in(P)·in(Q) = in_w(P·Q) = in_w(R) + in_w(Sq·Φ′) = 0 + in_w(Sq·Φ′).

The equality is legitimate coefficientwise even for monomials with `h*a>w`: the repaired
definition omits those slots on both sides rather than evaluating a truncated height. Thus
`in_w(SqΦ′) ≠ 0`, forcing `W(Sq·Φ′) = w`. By guarded SPREAD 2 applied to `Sq,Φ′`,
`W(Sq)+h·D′=w` (no subtraction is used) and

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

**[MRFIX 2026-08-27] (Filtration product exactness, conditional on I1 through NC.)** For
nonzero `y, z ∈ A` with canonical reps `P, Q`:
the canonical rep of `y·z` is `(P·Q) %ₘ Φ′`, so **NC says `W_A(y·z) = W_A(y) + W_A(z)`**
(in particular `A` is again seen to be a domain, and `W_A` is a `ℕ`-valued additive
weight on `A ∖ {0}`).

**[MRFIX 2026-08-27] (Graded dimensions.)** For `γ : ℕ` set

    d(γ) := #{ (i,a) : i ≥ 0, 0 ≤ a < D′, e₁·i + h·a = γ } .

Claim: `dim_k ( Fil_γ(A) / Fil_{γ+1}(A) ) = d(γ)`. The map sending `(i,a)` to the class
of `mk(π^i X^a)` lands in `Fil_γ/Fil_{γ+1}` and is `k`-linearly EXTENDED; it is:

- *surjective*: for each `a ∈ Att(P₀)`, choose a lift `u_a ∈ O` of the normalized digit
  `[P₀_a]_{v(P₀_a)}`. Then `P₀_a-π^{v(P₀_a)}u_a` has valuation at least
  `v(P₀_a)+1` by B22's digit/exact-vanishing laws, so modulo `Fil_{γ+1}` the class of
  `mk P₀` equals

      Σ_{a ∈ Att(P₀)} [P₀_a]_{v(P₀_a)} · [mk(π^{v(P₀_a)}X^a)].

  Every attaining `a` satisfies the extraction guard `h*a≤γ`, and
  `e₁∣(γ-h*a)` with quotient `v(P₀_a)`; non-attaining coefficients have weight `>γ`
  and their `γ`-digit vanishes by §3.2;
- *injective*: a `k`-combination `Σ r_{(i,a)}·[mk(π^i X^a)]` with lifts `r̃` assembles to
  `R₀ := Σ r̃_{(i,a)} π^i X^a`, of degree `< D′` — its OWN canonical representative — and if
  some `r_{(i,a)} ≠ 0` then `W(R₀) = γ` exactly (distinct basis monomials do not interact:
  the coefficient of `X^a` is `r̃ π^i` with `v = i` iff `r ≠ 0`), so `mk R₀ ∉ Fil_{γ+1}`
  by the canonical-representative characterization. **No irreducibility is used here.**

So `dim_k gr_γ(A) = d(γ)`, and explicitly: the **guarded** admissible `a` form one residue class mod
`e₁` intersected with `[0, D′)` and `{a : h·a ≤ γ}` — hence

    d(γ) = #{a ∈ [0,D′) : h·a ≡ γ (mod e₁), h·a ≤ γ},   and   d(γ) = f₁  for  γ ≥ h·(D′−1).

(For `γ ≥ h(D′−1)` every one of the `f₁` class members `a < D′ = e₁f₁` satisfies `ha ≤ γ`.)

### 3.6 The band count on `A ⧸ zA`

Fix `z ≠ 0` in `A`, `s := W_A(z)`. Give `A ⧸ zA` the image filtration
`Fil_γ(A/zA) := (Fil_γ(A) + zA)/zA`. Then, for every `γ`:

    dim_k gr_γ(A/zA) = { d(γ),          if γ < s;
                       { d(γ)-d(γ-s),  if s ≤ γ.

Equivalently, extend `d` to integers by `d̄(n)=0` for `n<0` and `d̄(n)=d(n)` for `n≥0`, and
write `d(γ)-d̄(γ-s)`. **[MRFIX 2026-08-27] This is integer/piecewise semantics:** it must not
be encoded as the unguarded natural subtraction `d(γ-s)`, which would read `d(0)` when
`γ<s`.

Proof. By the second isomorphism and the modular law (`Fil_{γ+1} ⊆ Fil_γ`):

    gr_γ(A/zA) ≅ Fil_γ(A) / ( Fil_{γ+1}(A) + (zA ∩ Fil_γ(A)) ).

**[MRFIX 2026-08-27]** By §3.5 product exactness, split on the required guard.

- If `γ<s`, then `zA⊆Fil_s⊆Fil_{γ+1}`, so its image in `gr_γ(A)` is zero and the quotient
  band has dimension `d(γ)`.
- If `s≤γ`, then the honest identity
  `W_A(za)=s+W_A(a)` gives
  `zA∩Fil_γ(A)=z·Fil_{γ-s}(A)`. Its image in `gr_γ(A)` is the image of
  `gr_{γ-s}(A)→gr_γ(A)`, `[a]↦[za]`. It is well-defined because multiplication shifts
  weights by exactly `s`, and injective because
  `za∈Fil_{γ+1}` implies `W_A(a)≥(γ-s)+1`. Its dimension is therefore `d(γ-s)`.

This proves the piecewise formula. Every subtraction in the second branch is preceded by
`s≤γ`; the proof uses NC only through the exact multiplicative filtration. ∎

### 3.7 Assembly: proof of T1

**[MRFIX 2026-08-27] This assembly is conditional on OPEN I1**, through
`I1 → SPREAD 4 irreducibility → NC → multiplicative filtration → band count`. Subject to that
single interface, every following subtraction is guarded or uses the integer extension `d̄`.

Let `z := mk Φ′ A₀`, `s := W(A₀) = W_A(z)` (§3.5; `A₀` is its own canonical rep).

1. `z ≠ 0` (monic `Φ′` of degree `D′` cannot divide nonzero `A₀` of smaller degree), so
   `Algebra.norm O z ≠ 0` by T2's first clause (§3.8, independent of T1), and by the
   LANDED dictionary `length_quot_eq_addVal_norm`
   (`leanfinal/Uniformity/ChapB/B53c.lean:121-140`; `A` free of positive rank `D′`):

       λ := Module.length O (A ⧸ Ideal.span {z}) = v(Algebra.norm O z) < ⊤.

2. *(Chain finiteness.)* `𝔪^λ` kills the length-`λ` module `A/zA` (Jordan–Hölder: each
   simple subquotient over the local ring `O` is `≅ k`, so `𝔪` moves each step down).
   Put `B:=h(D′−1)` and define, piecewise,

       N(γ) := 0                         if γ≤B,
               ⌈(γ-B)/e₁⌉              if B<γ.

   For the canonical representative of an element of `Fil_γ(A)`, the second branch's guard
   gives `e₁*v(coeff a) ≥ γ-h*a ≥ γ-B`; hence every coefficient is divisible by `π^{N(γ)}`.
   Thus `Fil_γ(A) ⊆ π^{N(γ)}·A`.
   Hence `Fil_γ(A/zA) ⊆ π^{N(γ)}(A/zA) = 0` once `N(γ) > λ.toNat`; fix
   `Γ := e₁·(λ.toNat + 1) + h·(D′−1) + s` (so also `Γ − s + 1 > h(D′−1)`).

3. *(Length along the finite chain.)* `A/zA = Fil_0 ⊇ Fil_1 ⊇ … ⊇ Fil_{Γ+1} = 0`, and
   length is additive with `length(k-space of dim d) = d`:

       λ = Σ_{γ=0}^{Γ} dim_k gr_γ(A/zA) = Σ_{γ=0}^{Γ} ( d(γ) − d̄(γ−s) )
         = Σ_{γ=Γ−s+1}^{Γ} d(γ)                                    (telescoping)
         = f₁ · s                                                  (§3.5: d ≡ f₁ on that range).

Here `Γ≥s`, so `Γ-s+1` is guarded, and `d̄` makes the first `s` shifted terms zero rather
than reading `d(0)`. Thus, conditional on I1,
`v(Algebra.norm O z) = λ = f₁·s = f₁ • W(A₀)`. ∎

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

**[MRFIX 2026-08-27] (Degenerate frame `h = 0`.)** Then `Coprime 0 e₁` forces `e₁ = 1`;
weights: `wt(x) = 0`,
`in(Φ′) = ψ(x)·t^0` with `ψ` = the residue-reduction of `Φ′`, irreducible by `hresirr`
(this is the `IsKey` regime). The SPREAD-3 argument is not needed: in the divisibility
endgame of §3.4, `in(Sq)·ψ(x) = in(P)·in(Q)` in `k[t][x]` where `ψ(x)` is irreducible in
`k[x]`, hence prime in `k[t][x]` (`(k[x]/ψ)[t]` is a domain), so `ψ ∣ in(P)` or
`ψ ∣ in(Q)` in `k[t][x]`, contradicting `deg_x < D′` as before. All other sections are
uniform in `h`.

There is also a direct landed route in this branch. The transported residual irreducibility
makes `Φ′` an `IsKey`, and `stageHeight A₀ = gaussVal A₀ =:c`. Apply B53b
`span_mk_eq_span_algebraMap_pow` to the arbitrary `A₀` (using `degree A₀ < degree Φ′`) to get

    span{mk Φ′ A₀} = span{algebraMap O A (π^c)}.

The corresponding quotient has length `D′*c=f₁*c` (rank `D′` and the scalar-power quotient),
while B53c's generic `length_quot_eq_addVal_norm` identifies that length with
`v(norm(mk Φ′ A₀))`. This proves the degenerate instance. The theorem
`addVal_norm_key_eval` is **not** used: its element is a key evaluated in `AdjoinRoot g`, not
an arbitrary `A₀` evaluated in `AdjoinRoot Φ′`. Battery 7 remains only a numerical check.

---

## 4. The certificate (examples-first record)

**[MRFIX 2026-08-27] Verification rerun.** The guarded initial-form definition does not alter
the norm formula checked by `verification/ramx_cert.py`, so the verifier source required no
edit. A full rerun on 2026-08-27 exited `0`: all 4,443 positive instances remained exact and
the reducible-residual negative control retained 10 violations.

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

## 5. Formalization node decomposition (wired to the plan's C.27 rows)

The plan priced F2.3–F2.6 at 285–485 lines for the determinant-expansion route and flagged
F2.5's basis permutation as unclear. The route above REPLACES the determinant expansion by
the graded-length route through the LANDED B53c dictionary; the honest re-estimate is
**[MRFIX 2026-08-27] 530–860 lines**, including I1 as a real 90–160-line node — larger in
total, but every node is finite `Polynomial`/`Finset`
arithmetic with no graded-ring typeclasses or completion, and the one
genuinely new mechanism (X5) is one-variable UFD reasoning. Node ↔ plan-row wiring:
X1–X4 + X6 replace F2.4's weighted filtration; X5 + NC are F2.5's noncancellation (initial
matrix superseded); X7–X9 are F2.6; X0 is F2.3.

| node | statement (Lean shape) | inputs (landed names) | mechanism | est. lines |
|---|---|---|---|---|
| X0 (=F2.3) | `ramified_addVal_norm_exact` and `ramified_norm_scalar_membership` statement carriers as in §1 | `KeyFrame`, `stageHeight`, `AdjoinRoot`, `Algebra.norm`, `addVal` | statement only; elaboration probed in `leanfinal/scratch/MRAMX_probe.lean` | 15–25 |
| X1 | weight basics: attainment, `W = ⊤ ↔ P = 0`, purity reads (P1)–(P3) | `stageHeight_eq_coeff_inf` (C131p), `isPure_addVal_coeff_zero` (C27), `OnSide`, `F.hmonic`, `F.hcop` | Finset.inf attainment; `Nat.Coprime.dvd_of_dvd_mul_left` for (P3) | 40–70 |
| X2 | guarded `in_γ` extraction into `k[t][x]` (`Polynomial (Polynomial k)`): additivity; strict-weight vanishing; equality with `in(P)` at attainment | X1; B21/B22 `digAt`, `digAt_add`, `digAt_eq_zero_iff`; B35a `resMk_mul`; B59a `resFieldXEquiv`; polynomial `ext` | coefficientwise definition of §2 with `h*a≤γ ∧ e₁∣(γ-h*a)` guard | 70–120 |
| X3 | level-1 Gauss exactness: `W(PQ) = W(P)+W(Q)` and `in(PQ) = in(P)·in(Q)` | X2; B33 `suppVal_add_le_suppVal_mul` (φ := X) for the ≥ half | §3.2 convolution + domain `k[t][x]`; NOT the C66b cite (level-2, above-floor — disjoint) | 90–150 |
| X4 | spread decomposition + `S(u)S(v)=S(uv)` + `in(Φ′)=S(ψ)`, ψ monic/deg f₁/ψ(0)≠0 | X1–X3; I1 (below) | §3.3; single-residue-class support from `hcop` | 90–150 |
| **I1 (OPEN)** | explicit `resPoly`/scalar-digit interface: side endpoints/degree; propositional `hpin`; coefficientwise equality after `(resFieldXEquiv O).symm`; transport `Irreducible`/degree from `F.hresirr` | B15/B16/B20/B25/B28/B29; B35c `resPoly_coeff_of_pure`; B59a `resFieldXEquiv`; `hpure`; (P2) | real proof node detailed at §2; `hresirr H₀ hpin`, **not** `rfl` | **90–160; OPEN** |
| X5 (=F2.5 core; conditional on I1) | LEMMA NC: `W((P*Q) %ₘ F.key) = W(P) + W(Q)` for nonzero `P,Q` of degree `< D′` | X1–X4, I1; `Polynomial.modByMonic_add_div` | §3.4: guarded `in_w` cancellation analysis + `ψ ∣ u ∨ ψ ∣ v` in the UFD `k[y]` + x-degree fence; `h = 0` branch via `ψ(x)` prime in `k[t][x]` | 80–130 |
| X6 | filtration `Fil_γ(A)`; canonical-rep characterization; `dim_k gr_γ(A) = d(γ)`; `d(γ) = f₁` for `γ ≥ h(D′−1)` | X1, X5(≥ half); `AdjoinRoot.powerBasis'`; `keyIsDomain`-analogue at `F.hirr` | §3.5; the injectivity needs NO irreducibility | 70–120 |
| X7 | guarded band count: `d(γ)` for `γ<s`, and `d(γ)-d(γ-s)` under `s≤γ` | X5, X6; modular law (`Submodule` lattice) | §3.6; no truncated subtraction | 50–90 |
| X8 (=F2.6 value; conditional on I1) | T1 assembly: chain finiteness, integer-extended telescoping, dictionary | X6, X7; **landed** `length_quot_eq_addVal_norm` (B53c); `Module.length` additivity (mathlib) | §3.7; `𝔪^λ`-kill of finite-length modules (mathlib or 15-line induction) | 70–120 |
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
   definition faithfulness. T2 is proved; T1's guarded argument is complete only conditional
   on OPEN I1.

## 7. Open items

**[MRFIX 2026-08-27] OPEN: I1**, exactly as specified in §2 and the node table. Therefore T1
is **PARTIAL**, while T2 is **PROVED**. The guarded repairs themselves leave no named gap in
X2, SPREAD 2, NC-after-I1, the multiplicative filtration, the piecewise band count, or the
telescoping assembly-after-I1. The full T1/X0 value-node transcription **may not fire** until
I1 is proved and reviewed; guarded X1–X3 may be transcribed independently, and X9/T2 remains
available.

Probe results
(`leanfinal/scratch/MRAMX_probe.lean`, `lake env lean` exit 0, all footprints Lean-core):
both T1/T2 statement carriers ELABORATE against the landed vocabulary (F2.3 de-risked), and
X9's membership half (`norm_mem_span_self`, generic Cayley–Hamilton) plus the domain
instance (`keyFrame_isDomain`, from `F.hirr` alone) are PROVED. Transcription notes: (a) X3 is the largest
single proof — the convolution bookkeeping should follow §3.2's per-slot residue
extraction literally; (b) mathlib names in X8/X9 (`Module.length` additivity on a chain,
Cayley–Hamilton, charpoly constant coefficient) should be re-searched at the pin, not
trusted from this document; (c) I1 must use B35c's pure coefficient theorem, B59a's explicit
`resFieldXEquiv`, and a propositionally proved `hpin` as detailed above.
