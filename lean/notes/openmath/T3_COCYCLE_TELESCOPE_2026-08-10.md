# T3 — LEMMA COCYCLE-TELESCOPE (one telescope shape; 3 instances + 1 displayed non-instance)
## RCT unit T3-cocycle-telescope — CODEX arm — 2026-08-10

**[RCT CODEX-arm: composed by gpt-5.6-sol high; transcribed unaltered.]**
Everything below the marker line is the composing model's text, VERBATIM
(source: `verification/openmath/t3_codex_run1_output.txt`, the final agent
message, log lines 1227–2450 — duplicated byte-identical at 2453–3676;
body md5 a4cc25c136af65d595ff3ff2552ebc2e; one foreground call, wall
≤ 5m41s (brief commit 17:13:41Z → output mtime 17:19:22Z), 44,580 tokens,
no continuation). Per the prover-RCT protocol
(docs/PROVER_RCT_PROTOCOL_2026-08-10.md §3 + Amendment 1) the lab tech may
NOT alter mathematical content; this header is the tech's record, not part
of the composed note.

**GRADE: attempt 0/2.** The 2-clean hostile arc has not run. Charge and
gate: blueprint T3 (docs/SIMPLIFICATION_BLUEPRINT_2026-08-10.md §2) as
amended by Plan revision 1 §R.2's S-2 pre-compose gate (side-by-side
displays + withdrawal tooth) and §R.3's S-2 battery rule (joint frames;
per-consumer regression legs), PLUS the post-blueprint fourth source
[GENTOW5-W(i)] (GENTOW5_WI_2026-08-10.md @ ec30256c, arc 1/2 — cited at
attempt grade throughout, per the brief).

**S-2 gate record (tech audit of FORM, not content).** (i) Side-by-side
display: PRESENT (§S1.1, four source displays quoted; §S1.2 the candidate
common signature; §S1.3/S1.4/S1.6 three instantiation maps; §S1.5 the
GENTOW-6.4 adjudication row-by-row). (ii) Withdrawal tooth: NOT fired —
the composer's verdict is that the signature covers THREE of the four
sources without taking an endpoint equation as input (§S1.7 carrier-field
audit; §S2.5's explicit no-endpoint sentence after conclusion 2), and
GENTOW-6.4 is recorded as a DISPLAYED NON-INSTANCE via the brief's escape
hatch (§S1.5, §S5) rather than force-fitted — honest absorption count is
3, not 4. (iii) Per-consumer regression legs (R.3): PRESENT — §S7.4 names
all four committed runners unmodified. (iv) Joint-frame rule: §S7.5
declares FRAME-C joint at the abstract carrier (θ₂ ≠ 1 ∧ τ non-character
∧ δ ≠ 1 ∧ w ≠ 1) and honestly labels the realized-tower joint cell
(θ ≠ 1 ∧ intrinsic w ≠ 1 in one B″ instance) MACHINE-UNEXPLORED (§S8.3
OPEN COVERAGE T3-JOINT).

**Tech implementation record (appended after the sealed run; see the
MACHINE VERDICT append at the bottom of this file).**

---- MARKER: COMPOSED NOTE BEGINS (verbatim) ----

# T3_COCYCLE_TELESCOPE_2026-08-10.md

## S0. VERDICT UP FRONT

**Verdict: LEMMA COCYCLE-TELESCOPE is proved, with three genuine instances and one explicit non-instance.** The lemma has two ports built from the same normalizer cocycle: a boundary-read port, which gives GENTOW2-B'' and [GENTOW5-W(i)], and an assembled-comparison port, which gives the telescope in HETOW-4(c) and its polynomial rescaling. GENTOW-6.4 is not an instance: its proof is filtration-triangular and additive, and contains no normalizer section, multiplicative residue cocycle, or cocycle bracket from which its window cap can be recovered. Treating its already-proved block-translation equation as carrier data would violate the G3 withdrawal tooth. Thus T3 is not withdrawn, but its honest absorption count is three telescope statements, not four.

Grade: 0/2 attempt (CODEX arm, RCT unit T3-cocycle-telescope); hostile arc owed.

---

## S1. THE SIDE-BY-SIDE GATE

### S1.1 The four source displays

The following are the key source displays, quoted verbatim. Greek characters occur only inside these frozen quotations; the common signature below is written in ASCII.

| SOURCE 1: GENTOW2-B'' | SOURCE 2: HETOW-4 | SOURCE 3: GENTOW-6.4 | SOURCE 4: [GENTOW5-W(i)] |
|---|---|---|---|
| <pre>(6)  u(β_t) = ϑ(t) · w^{f₃−t}.</pre> | <pre>ρ_t = ρ̂_t · τ(H₀) · δ^{−t} ,   i.e.   R_{λ₂}(Z) = τ(H₀) · R̂_{λ₂}(Z/δ) ,</pre> | <pre>(block value at block height m) = (f-value at height m + c_g) − c_g</pre><pre>the block read is lift-stable below e1e2·N − c_g.</pre> | <pre>u_i(beta_t) = theta_i(t) * w_i^{f_{i+1}-t},<br>w_i = R_{i+1,kbar_i}(nhat_i(u_{i+1})).</pre> |

The first, second, and fourth displays are multiplicative normalizer-cocycle telescopes. The third is an additive translation followed by a filtration bound.

### S1.2 Candidate common signature

The common carrier consists of the following data.

1. An additive height group `Lambda`.

2. An abelian multiplicative group `A` of nonzero homogeneous monomials, with a homomorphism

       ht : A -> Lambda.

3. The degree-zero group `A_0 := ker(ht)` and a multiplicative residue map

       res : A_0 -> K^x

   into the multiplicative group of a field `K`.

4. A normalized height section

       N : S -> A,    ht(N(k)) = k,    N(0) = 1,

   on the finite set of heights used in the calculation.

5. Its ladder cocycle

       c_N(a,b) := N(a) N(b) / N(a+b) in A_0.

6. A ladder step `q`, its multiples `dq`, and, for the comparison port, a descending ladder

       H_t := H_0 - tq.

7. For the boundary-read port: a residual read `R_k`, constant-coefficient extraction `ct`, a `Phi`-adic expansion, and a coherent digit functional satisfying the source-level peel, expansion, positive-degree, and digit-factorization laws stated precisely in S2.2.

8. For the comparison port: a second normalized height section `Nhat`, its ratio

       tau(k) := res(Nhat(k)/N(k)),

   and coefficient carriers `A_t` of height `H_t`.

The lemma does not assume either target identity.

### S1.3 Instantiation map: SOURCE 1, GENTOW2-B''

| Source symbol | Common-signature symbol |
|---|---|
| Height group at level 2 | `Lambda` |
| Tower ladder monomial `nhat_2(k)` | `N(k)` |
| `u_3` | `q` |
| `d := f_3-t` | `d` |
| `M := nhat_2(du_3)` | `N(dq)` |
| `N := nhat_2(u_3)` | `N(q)` |
| `res((M/N^d)(x_0)) = vartheta(t)` | `theta_d` |
| `R_{3,kbar}(N) = w` | `w` |
| Per-grade factor `u(beta_t)` | `U(dq)` |
| `Phi_2`-adic expansion | Boundary-read expansion |
| `y`-degree-zero part | `ct` |

Thus the common conclusion `U(dq)=theta_d w^d` is exactly source display (6).

### S1.4 Instantiation map: SOURCE 2, HETOW-4

| Source symbol | Common-signature symbol |
|---|---|
| HE7 normalizer `n_2(k)` | `N(k)` |
| Tower normalizer `nhat_2(k)` | `Nhat(k)` |
| `res(nhat_2(k)/n_2(k)) = tau(k)` | `tau(k)` |
| Side step `u_3` | `q` |
| `H_t=H_0-tu_3` | `H_t=H_0-tq` |
| `delta=tau(u_3)` | `delta=tau(q)` |
| HE7 assembled coefficient `rho_t` | `rho_t` |
| Tower assembled coefficient `rhohat_t` | `rhohat_t` |
| `R_{lambda_2}` | `R` |
| `Rhat_{lambda_2}` | `Rhat` |

The comparison conclusion becomes

    rho_t = rhohat_t tau(H_0) delta^(-t),
    R(Z) = tau(H_0) Rhat(Z/delta).

### S1.5 Instantiation map: SOURCE 3, GENTOW-6.4

| Proposed source symbol | Candidate common symbol | Adjudication |
|---|---|---|
| Composed digit map | Boundary read | No: the source map is additive and filtration-triangular, not a homogeneous residual read with multiplicative peel |
| Window cap `e1e2 N` | Boundary height | A numerical analogy only |
| Translation by `c_g` | Gauge monomial | No: `c_g` is an additive value shift, not an element of `K^x` |
| `(f-value+c_g)-c_g` | Cocycle telescope | Only the tautological additive cancellation remains |
| Lift-stability below the cap | Boundary-monomial conclusion | No implication in either direction |

There is no valid instantiation map. Supplying the block equation as a hypothesis would supply the very projection identity needed to prove clause (c), and the common multiplicative lemma would still not prove triangularity or lift-stability. SOURCE 3 is therefore a displayed non-instance.

### S1.6 Instantiation map: SOURCE 4, [GENTOW5-W(i)]

This source is cited at **ATTEMPT GRADE, arc 1/2** throughout.

| Source symbol | Common-signature symbol |
|---|---|
| Level-`i` height group | `Lambda` |
| `nhat_i(k)` | `N(k)` |
| `u_{i+1}` | `q` |
| `d=f_{i+1}-t` | `d` |
| `theta_i(t)=res(nhat_i(dq)/nhat_i(q)^d)` | `theta_d` |
| `R_{i+1,kbar_i}(nhat_i(q))` | `w` |
| `u_i(beta_t)` | `U(dq)` |
| `Phi_i`-adic expansion | Boundary-read expansion |
| `y`-degree-zero part | `ct` |

The conclusion is the source display

    u_i(beta_t) = theta_i(t) w_i^(f_{i+1}-t).

### S1.7 Carrier-field audit

| Carrier field | Why it is legitimate input and not a disguised conclusion |
|---|---|
| `Lambda`, `A`, `ht`, `A_0` | These specify where heights and homogeneous monomials live. They contain no boundary value or telescope identity. |
| `res : A_0 -> K^x` | This is the ordinary multiplicative residue of a value-zero quotient. It does not prescribe the residue of a nonzero-height normalizer. |
| Section `N` | It chooses one monomial at each height. Its failure of multiplicativity is left unrestricted. |
| `c_N(a,b)` | This is a definition from `N`, not an assumed cocycle value or endpoint formula. |
| Ladder `q`, `dq`, `H_t` | These select the heights traversed. |
| Peel law | This is the cited multiplicativity of residual operators, Cor 4.7(2), not the sought comparison between different grades. |
| Expansion additivity | This is Def 1.8 plus Cor 4.7(1), applied before taking the constant coefficient. |
| Positive-`Phi` elimination | This is the source-local consequence of Lemma 3.17, Prop 1.9(2), Cor 4.7(2), and eq (14). It does not determine the surviving constant digit. |
| Per-grade digit factorization `ct R_k(Q)=U(k) digit_k(Q)` | It defines an otherwise arbitrary per-grade family `U(k)`. It imposes no relation between `U(q)` and `U(dq)`. Arbitrary fixed families generally do not satisfy a one-`w` law. |
| Evaluation digit | This computes the digit of the surviving `Phi`-adic coefficient from `N(q)^d/N(dq)`. It is a local quotient computation, not the conclusion `U(dq)=theta_d w^d`. |
| Second section `Nhat` and `tau(k)` | `tau` is a pointwise ratio. It is not assumed constant, geometric, or a character. |
| Assembled coefficient recipe | The formula using `A_t N(q)^t/N(H_0)` is the source definition after its own brackets are collected. The comparison of the two systems remains to be proved. |

---

## S2. LEMMA COCYCLE-TELESCOPE

### S2.1 Algebraic setting

Let `Lambda` be an additive abelian group. Let `A` be an abelian multiplicative group and let

    ht : A -> Lambda

be a homomorphism. Put `A_0 := ker(ht)`. Let `K` be a field and let

    res : A_0 -> K^x

be a group homomorphism.

Let `S` be a subset of `Lambda` containing every height used below. A normalized section is a map

    N : S -> A

such that `ht(N(k))=k` and `N(0)=1`.

Whenever `a,b,a+b` lie in `S`, define

    c_N(a,b) := N(a)N(b)/N(a+b) in A_0.

Fix `q in Lambda`. For each relevant integer `d>=0`, assume `dq in S`, and define

    vartheta_d := res(N(q)^d/N(dq)),
    theta_d := vartheta_d^(-1)
             = res(N(dq)/N(q)^d).

Thus `vartheta_0=vartheta_1=theta_0=theta_1=1`.

### S2.2 Boundary-read hypotheses

For the boundary-read conclusion, fix `d>=1` and suppose the following source-level data are available.

- There is an element `Phi` and an expansion

      G := N(q)^d = Sum_{j>=0} Q_j Phi^j.

- There are residual reads `R_k` with values in `K[y]`, and `ct` denotes the coefficient of `y^0`.

- Exactness and multiplicative peel give

      ct R_dq(N(q)^d) = (ct R_q(N(q)))^d.

  Put

      w := ct R_q(N(q)) in K^x.

- Expansion additivity gives

      R_dq(G) = Sum_j R_dq(Q_j Phi^j).

- For `j>=1`,

      ct R_dq(Q_j Phi^j) = 0.

- The constant coefficient `Q_0` has exact grade `dq`, and there is a coherent digit map and a per-grade unit `U(dq) in K^x` such that

      ct R_dq(Q_0) = U(dq) digit_dq(Q_0).

- Evaluation at a `Phi`-root, together with exactness of the ladder monomials, gives

      digit_dq(Q_0)
        = res(N(q)^d/N(dq))
        = vartheta_d.

These are the primitive peel, expand, positive-degree elimination, and digit-read inputs used by the source proofs.

### S2.3 Comparison hypotheses

For the assembled-comparison conclusion, let `Nhat` be a second normalized section on the same heights and define

    tau(k) := res(Nhat(k)/N(k)) in K^x.

Let

    H_t := H_0-tq,    0<=t<=D,

and let `A_t in A` have height `H_t`. Define the assembled coefficients

    rho_t
      := res(A_t N(q)^t/N(H_0)),

    rhohat_t
      := res(A_t Nhat(q)^t/Nhat(H_0)).

All displayed quotients have height zero.

Define

    R(Z) := Sum_{t=0}^D rho_t Z^t,
    Rhat(Z) := Sum_{t=0}^D rhohat_t Z^t,
    delta := tau(q).

### S2.4 Statement

**LEMMA COCYCLE-TELESCOPE.** Under the algebraic setting above:

1. **Power-cocycle telescope.** For `d>=0`,

       vartheta_{d+1}
         = vartheta_d res(c_N(dq,q)),

   and hence

       vartheta_d
         = Product_{s=0}^{d-1} res(c_N(sq,q)),

       theta_d
         = Product_{s=0}^{d-1} res(c_N(sq,q))^(-1).

2. **Boundary times gauge monomial.** Under S2.2,

       U(dq) = theta_d w^d.

   In particular, the per-grade family is not assumed to obey a power law; the formula is forced by the peel and constant-digit comparison.

3. **Bracket telescope.** For `H_t=H_0-tq`,

       N(H_t)N(q)^t/N(H_0)
         = Product_{s=0}^{t-1} c_N(H_{s+1},q).

   Thus the product of local cocycle brackets is exactly one boundary quotient.

4. **Change of section and assembled residual.** The pointwise ratio `tau` satisfies

       tau(a)tau(b)/tau(a+b)
         = res(c_Nhat(a,b)c_N(a,b)^(-1)).

   No character law for `tau` is required. Moreover,

       rho_t = rhohat_t tau(H_0) delta^(-t),

   and therefore

       R(Z) = tau(H_0) Rhat(Z/delta).

5. **Polynomial-routing consequences.** Multiplication by the nonzero scalar `tau(H_0)` and the substitution `Z -> Z/delta` preserve separability and the multiset of irreducible-factor degrees and multiplicities. For a monic factor `rhat(Z)` of degree `m`, the corresponding monic factor is

       r(Z) := delta^m rhat(Z/delta).

   Roots correspond by `shat -> delta shat`; membership of a root in any field containing `K` is preserved.

### S2.5 Proof

For conclusion 1, define in `A_0`

    P_d := N(q)^d/N(dq).

Then `P_0=P_1=1`, and

    P_{d+1}
      = N(q)^(d+1)/N((d+1)q)
      = (N(q)^d/N(dq))
        (N(dq)N(q)/N((d+1)q))
      = P_d c_N(dq,q).

Applying the multiplicative homomorphism `res` gives

    vartheta_{d+1}
      = vartheta_d res(c_N(dq,q)).

Iteration from `vartheta_0=1` gives the product formula. Inverting it gives the formula for `theta_d`.

For conclusion 2, the peel hypothesis gives

    ct R_dq(G) = w^d.                                      (2.1)

By expansion additivity,

    R_dq(G) = Sum_j R_dq(Q_j Phi^j).

Every `j>=1` summand has zero constant coefficient, so

    ct R_dq(G) = ct R_dq(Q_0).                             (2.2)

The digit factorization and evaluation-digit hypotheses give

    ct R_dq(Q_0)
      = U(dq) digit_dq(Q_0)
      = U(dq) vartheta_d.                                  (2.3)

Combining (2.1), (2.2), and (2.3),

    w^d = U(dq) vartheta_d.

Since `vartheta_d` lies in `K^x`,

    U(dq)
      = vartheta_d^(-1)w^d
      = theta_d w^d.

The endpoint identity was not supplied as a hypothesis: its two sides arose independently from the peeled read of `N(q)^d` and the constant digit of its `Phi`-adic expansion.

For conclusion 3, the ladder identity `H_s=H_{s+1}+q` gives

    c_N(H_{s+1},q)
      = N(H_{s+1})N(q)/N(H_s).

Multiplying this identity for `s=0,...,t-1` cancels every intermediate factor `N(H_1),...,N(H_{t-1})` and yields

    Product_{s=0}^{t-1} c_N(H_{s+1},q)
      = N(H_t)N(q)^t/N(H_0).

This is literal telescoping inside `A_0`.

For the first part of conclusion 4, use the definitions of `tau` and the two cocycles:

    tau(a)tau(b)/tau(a+b)
      = res(
          (Nhat(a)/N(a))
          (Nhat(b)/N(b))
          (N(a+b)/Nhat(a+b))
        )
      = res(
          (Nhat(a)Nhat(b)/Nhat(a+b))
          (N(a+b)/(N(a)N(b)))
        )
      = res(c_Nhat(a,b)c_N(a,b)^(-1)).

Thus `tau` is a character exactly when the two section cocycles have the same residue. Character behavior is not part of the carrier.

For the coefficient comparison,

    rho_t/rhohat_t
      = res(
          (A_t N(q)^t/N(H_0))
          (A_t Nhat(q)^t/Nhat(H_0))^(-1)
        )
      = res(
          (N(q)/Nhat(q))^t
          (Nhat(H_0)/N(H_0))
        )
      = tau(q)^(-t)tau(H_0).

Therefore

    rho_t = rhohat_t tau(H_0)delta^(-t).

Summing over `t` gives

    R(Z)
      = Sum_t rhohat_t tau(H_0)delta^(-t)Z^t
      = tau(H_0) Rhat(Z/delta).

For conclusion 5, `Z -> Z/delta` is a `K`-algebra automorphism because `delta` is nonzero. It preserves irreducibility, multiplicities, and separability. If `rhat` is monic of degree `m`, then `delta^m rhat(Z/delta)` is monic and irreducible precisely when `rhat` is. Finally,

    r(delta shat)
      = delta^m rhat(shat),

so roots correspond by multiplication by `delta`. Multiplication by an element of `K^x` preserves membership in every extension field containing `K`. This proves all conclusions. QED.

---

## S3. INSTANCE 1: GENTOW2-B'' RE-DERIVED

Fix `t<f_3` and put

    d := f_3-t,
    q := u_3,
    N(q) := nhat_2(u_3),
    N(dq) := nhat_2(du_3).

The source defines

    vartheta(t)
      := res((nhat_2(du_3)/nhat_2(u_3)^d)(x_0)).

Thus the source's `vartheta(t)` is the common lemma's `theta_d`, not its reciprocal `vartheta_d`.

Take

    w := R_{3,kbar}(nhat_2(u_3)),
    U(dq) := u(beta_t).

The `Phi_2`-adic expansion of `G=N(q)^d` has constant coefficient `Q_0`. Evaluation at `Phi_2(x_0)=0` gives

    digit(Q_0)
      = res((N(q)^d/N(dq))(x_0))
      = vartheta(t)^(-1).

The source's peel/expand/kill/read calculation is therefore exactly conclusion 2:

    u(beta_t)
      = vartheta(t) w^d
      = vartheta(t) w^(f_3-t).                             (3.1)

This is source display (6).

For the residual polynomial,

    y^f_3 - Sum_{t<f_3} vartheta(t)w^(f_3-t)c_t y^t
      = w^f_3 P(y/w),

where

    P(y) := y^f_3-Sum_{t<f_3} vartheta(t)c_t y^t.

No value of `w` is needed for preservation of the factor pattern.

### Enumerated inputs consumed

1. The recipe slot geometry `beta_t=d kbar` and exact ladder heights.

2. Definition of `u(beta)` and B'(3):

       R_{3,beta}(Q)=u(beta) digit(Q)

   for `Phi_2`-free `Q` of exact grade.

3. B-1 exactness for a nonzero coherent digit of a coefficient of degree `<m_3`.

4. The coherent evaluation digit and `Phi_2(x_0)=0`.

5. Def 1.8 for the augmentation minimum.

6. Prop 1.9(2) for values of `Phi_2`-free coefficients.

7. Lemma 3.17 for terms strictly above the target grade.

8. Cor 4.4(3), Cor 4.7(1)/(2), and eq (14) for peel, additivity, and positive-`y` degree.

9. The gamma-calculus identifying the value-zero ladder quotient as a fixed `z_1,z_2` monomial.

The absorbed conclusion GENTOW2-B''(6) is not on this list. The grade-zero lift used in the pasted source proof is unnecessary for this instantiation: using `G=N(q)^d` directly leaves the nonzero digit `vartheta(t)^(-1)`, which the digit-factorization law reads without first changing it to `1`.

---

## S4. INSTANCE 2: HETOW-4 RE-DERIVED

Set

    N(k) := n_2(k),
    Nhat(k) := nhat_2(k),
    tau(k) := res(nhat_2(k)/n_2(k)),
    q := u_3,
    delta := tau(u_3),
    H_t := H_0-tu_3.

The source's elementary ladder equations independently compute

    tau(k)=eta^(-Q(m(k))).

This is an arithmetic identification of the comparison ratio, not an assumption about assembled coefficients.

### S4.1 Clause (b): the non-character law

Conclusion 4 of the common lemma gives

    tau(k)tau(k')/tau(k+k')
      = res(c_nhat(k,k')c_n(k,k')^(-1)).                   (4.1)

Substituting the source's independently computed formula
`tau(k)=eta^(-Q(m(k)))`, together with

    m(k+k')=m(k)+m(k')+u_2 w_2

and the two applications of

    Q(a+b)=Q(a)+Q(b)+wrap_1(a,b),

reproduces the HETOW-4(b) display

    tau(k)tau(k')/tau(k+k')
      = eta^(
          wrap_1(m(k),m(k'))
          + w_2(
              Q(u_2)+wrap_1(m(k)+m(k'),u_2)
            )
        ).

Thus the common lemma supplies the exact cocycle-comparison shape; the two-floor exponent is the source-specific ladder arithmetic.

### S4.2 Clause (c): assembled telescope

Each normalizer system collects its local brackets into

    res(A_{j(t)} N(u_3)^t/N(H_0)).

Conclusion 3 proves that these brackets telescope internally. Conclusion 4 then gives

    rho_t
      = rhohat_t tau(H_0)delta^(-t),

and hence

    R_{lambda_2}(Z)
      = tau(H_0) Rhat_{lambda_2}(Z/delta).                 (4.2)

This is exactly HETOW-4(c).

The side-letter comparison is the pointwise ratio at `k=u_3`:

    beta_{2,xi}=iota_xi(delta) zhat_xi.

This requires the source's identification of each side letter with its own normalizer quotient; once that definition is inserted, it is the same section-ratio calculation.

### S4.3 Clause (d): routing transport

Conclusion 5 gives:

- separability equivalence;
- equality of the multisets of irreducible-factor degrees and multiplicities;
- the monic bijection

      rhat_2(Z) -> r_2(Z)
        := delta^(deg rhat_2) rhat_2(Z/delta);

- root transport `shat_2 -> delta shat_2`;
- preservation of `K_2`-rationality.

These are the routing portions of HETOW-4(d).

The final assertion that one polynomial lift `w in O[x]` realizes both refinement prescriptions, and the system-independence of every later refined key, additionally consumes the source's lifting and chain-iteration lemmas. It is not a conclusion of the abstract cocycle telescope alone.

### S4.4 Exact absorption boundary

| HETOW-4 clause | Status under LEMMA COCYCLE-TELESCOPE |
|---|---|
| (a), explicit formula `tau(k)=eta^(-Q(m(k)))` | Not abstractly supplied; re-proved from the two ladder equations and the definition of `Q` |
| (b), cocycle-comparison shape | Supplied by conclusion 4 |
| (b), explicit two-floor exponent | Obtained by substituting source-specific floor arithmetic |
| (c), coefficient telescope and polynomial rescale | Fully supplied by conclusions 3 and 4 |
| (d), separability/factor/root routing | Fully supplied by conclusion 5 |
| (d), common polynomial lift and iterate independence | Remains on HETOW-4's own lifting inputs |

### Enumerated inputs consumed

1. Definitions of `n_2(k)`, `nhat_2(k)`, `s(k)`, `m(k)`, and `Q(k)`.

2. The two exact ladder equations

       e1 e2 a + i e2 h + b u2 = k,
       e1 a + i h = m(k).

3. `gcd(u_2,e_2)=gcd(h,e_1)=1`.

4. The residue identity `res(x^e1/pi^h)=eta`.

5. The addition laws for `m` and `Q`, including `wrap_1`.

6. The source definition of each system's assembled coefficient after its own brackets are collected.

7. The source definitions of its side letters.

8. Ordinary field-polynomial algebra for substitution by `delta in K^x`.

9. For the last refinement sentence only: HETOW-4's cited lift and finite-chain inputs.

Neither HETOW-4(c)'s coefficient identity nor its polynomial-rescaling conclusion is on this list.

---

## S5. INSTANCE 3: GENTOW-6.4 ADJUDICATED

### S5.1 Displayed non-instance verdict

**GENTOW-6.4 is not an instance of LEMMA COCYCLE-TELESCOPE.**

Its proof uses:

1. triangularity of repeated monic division in the `x`-degree filtration;

2. congruence of digit coordinates modulo `pi^N`;

3. nonnegativity of the offset `w(a,b)`;

4. ultrametric minima below `e1e2 N`;

5. the separately proved projection equation

       block value
         = (f-value+c_g)-c_g.

No multiplicative height section, degree-zero residue quotient, normalizer cocycle, peel law, or cocycle bracket occurs in that proof.

### S5.2 Fragment that does follow formally

Once the projection equation is independently known, its additive shifts cancel:

    (v+c_g)-c_g=v.

This is an additive one-line identity. It does not prove:

- triangularity of the digit map;
- bijectivity modulo `pi^N`;
- stability of in-window valuations and residues;
- exclusion of unread digits below the cap;
- realization of the undercut at exactly `e1e2 N`;
- the shifted block cap `e1e2 N-c_g`.

### S5.3 Why forcing an instantiation would be vacuous

One could manufacture an additive analogue by declaring the projection equation itself to be the comparison rule. But then the endpoint relation required by GENTOW-6.4(c) has been inserted as carrier data. That violates G3 and G4. Encoding addition as multiplication in a formal group would not repair the problem: the filtration-triangular and valuation-cap assertions still would not follow.

Therefore the source remains a regression neighbor, not an absorbed instance. T3's honest mathematical absorption is GENTOW2-B'', HETOW-4(c) with its routing consequences, and [GENTOW5-W(i)].

---

## S6. INSTANCE 4: [GENTOW5-W(i)] RE-DERIVED

This source is consumed only at **ATTEMPT GRADE, arc 1/2**.

Fix `i>=3`, `t<f_{i+1}`, and put

    d := f_{i+1}-t,
    q := u_{i+1},
    N(q) := nhat_i(u_{i+1}),
    N(dq) := nhat_i(du_{i+1}),
    beta_t := d kbar_i.

The source defines

    theta_i(t)
      := res(N(dq)/N(q)^d)
      = theta_d

in the notation of the common lemma. Put

    w_i := R_{i+1,kbar_i}(N(q)),
    U(dq) := u_i(beta_t).

Take `G=N(q)^d` and expand

    G=Sum_{j>=0}Q_j Phi_i^j.

The peel input gives

    ct R_{i+1,beta_t}(G)=w_i^d.

The `j>=1` terms have positive `y`-degree or die above the target grade. Evaluation at a `Phi_i`-root gives

    digit_i(Q_0)
      = res(N(q)^d/N(dq))
      = theta_i(t)^(-1).

The per-grade digit law gives

    ct R_{i+1,beta_t}(Q_0)
      = u_i(beta_t)theta_i(t)^(-1).

Conclusion 2 therefore yields

    u_i(beta_t)
      = theta_i(t)w_i^d
      = theta_i(t)w_i^(f_{i+1}-t).                         (6.1)

This is [GENTOW5-W(i)] at **ATTEMPT GRADE, arc 1/2**. At `i=2`, the same instantiation is S3 and gives GENTOW2-B''.

### Enumerated inputs consumed

1. DEF GENTOW5-1's level-`i` normalizer recursion and ladder heights.

2. The level-`i` per-grade family and digit factorization

       R_{i+1,beta}(Q)=u_i(beta)digit_i(Q).

3. LEMMA GENTOW5-C's exact-value clause for degree `<D_i` coefficients.

4. The accepted level-`i` cocycle computation and the reciprocity between `theta_i(t)` and `vartheta_{i,d}`.

5. The exact-value/node-point clause used to evaluate ladder monomials at a `Phi_i`-root.

6. Def 1.8.

7. Prop 1.9(2).

8. Lemma 3.17.

9. Cor 4.4(1)/(3).

10. Cor 4.7(1)/(2).

11. Eq (14).

12. Prop 1.15 for the canonical residue-field identification.

Neither (6.1) nor any one-`w_i` power law is on this list. Thm 4.8 and a grade-zero lift are not consumed.

---

## S7. MACHINE-VERIFICATION PLAN

### S7.1 M1: one fresh instrument

Create one new self-contained runner:

    verification/openmath/t3_cocycle_telescope.py

Requirements:

- Python 3;
- integer-exact polynomial and exponent-vector arithmetic;
- finite-field arithmetic implemented directly for prime fields;
- optional PARI/gp subprocess only for the stated p-adic factorization and residue-field legs;
- no import from a committed verification runner;
- predictions P-A through P-E and teeth T-1 through T-4 written in the runner docstring before its first run;
- first-run output retained whether GREEN or RED.

#### FRAME-C: direct common-carrier frame

Use

    p=5,
    pi=5,
    e_1=2,
    f_1=1,
    h=1,
    psi_1(Z)=Z-2,
    Phi_1(x)=x^2-10.

At a root of `Phi_1`, the level-1 letter is

    eta=res(x^2/5)=2 in F_5^x.

Use doubled height:

    ht(x)=1,
    ht(5)=2.

The ladder section is

    N(k)=x^i 5^a,
    i=k mod 2,
    a=(k-i)/2.

Introduce a formal multiplicative reference element `T` of height `1`. Define the degree-zero residue character by the two independent assignments

    res(x/T)=3,
    res(x^2/5)=2.

These force

    res(5/T^2)=res(x/T)^2/res(x^2/5)
              =3^2/2
              =2 mod 5.

This formal reference is used only to construct an independent boundary read

    U(k):=res(N(k)/T^k).

It is not a claimed polynomial in the p-adic tower.

Use `q=1` and `d=0,1,2,3,4`.

##### P-A: exact section and cocycle checks

The runner must compute:

| `k` | `N(k)` | `U(k)=res(N(k)/T^k)` |
|---:|---|---:|
| 0 | `1` | 1 |
| 1 | `x` | 3 |
| 2 | `5` | 2 |
| 3 | `5x` | 1 |
| 4 | `25` | 4 |

The successive cocycles are:

    c_N(0,1)=1,
    c_N(1,1)=x^2/5,
    c_N(2,1)=1,
    c_N(3,1)=x^2/5,

with residues

    1,2,1,2.

Hence the predicted telescope values are:

| `d` | `vartheta_d=res(x^d/N(d))` | `theta_d` |
|---:|---:|---:|
| 0 | 1 | 1 |
| 1 | 1 | 1 |
| 2 | 2 | 3 |
| 3 | 2 | 3 |
| 4 | 4 | 4 |

The runner must verify both the recurrence and the product formula, using exponent vectors before taking residues.

##### P-B: boundary-times-monomial conclusion

Here

    w=U(1)=3.

Compute `U(d)` independently from `N(d)/T^d`, not from the target formula. Verify:

| `d` | `theta_d w^d mod 5` | independently computed `U(d)` |
|---:|---:|---:|
| 1 | 3 | 3 |
| 2 | 2 | 2 |
| 3 | 1 | 1 |
| 4 | 4 | 4 |

Also verify the pre-cancellation equality

    w^d=U(d)vartheta_d

at each `d`. Exact predicted values of `w^d` for `d=1,2,3,4` are

    3,4,2,1.

This directly exercises the lemma's carrier without importing a source endpoint.

##### P-C: direct assembled-comparison port

Define a second section

    Nhat(k):=x^k.

Then

    tau(k)=res(x^k/N(k))=2^floor(k/2) mod 5.

Predicted values for `k=0,...,6` are

    1,1,2,2,4,4,3.

This is not a character, since

    tau(1)^2=1 != 2=tau(2).

Take

    q=2,
    H_0=6,
    H_t=6-2t,    t=0,1,2,3,
    A_t=T^(6-2t).

Then

    tau(H_0)=tau(6)=3,
    delta=tau(2)=2.

The exact assembled coefficients are predicted to be

    (rho_0,rho_1,rho_2,rho_3)=(2,4,3,1),

    (rhohat_0,rhohat_1,rhohat_2,rhohat_3)=(4,1,4,1).

Thus

    R(Z)=2+4Z+3Z^2+Z^3,
    Rhat(Z)=4+Z+4Z^2+Z^3,

and the runner must verify coefficientwise

    R(Z)=3 Rhat(Z/2) in F_5[Z].

It must separately multiply the local cocycles

    Product_{s=0}^{t-1} c_N(H_{s+1},2)

as exponent vectors and compare the result with

    N(H_t)N(2)^t/N(6).

This tests the bracket telescope before residues are taken.

#### FRAME-LW3: direct tower boundary-read port

Reuse SOURCE 4's explicit letter-live frame:

    p=3,
    (e_1,f_1,h)=(2,1,1),
    (e_2,f_2)=(2,1),
    (e_3,f_3)=(2,1),
    (e_4,f_4)=(1,2),
    heights=(1,5,21,43),

    psi_1=y-2,
    psi_2=y-2,
    psi_3=y-2,
    psi_4=y^2-y-1,

    Phi_1=x^2-6,
    Phi_2=Phi_1^2-18x,
    Phi_3=Phi_2^2-162Phi_1,

    Phi_4=
      Phi_3^2
      -3xPhi_1Phi_2 Phi_3
      -2*3^9 xPhi_1.

The fresh runner must reconstruct

    nhat_3(43)=3xPhi_1Phi_2,
    nhat_3(86)=3^9 xPhi_1,

and the exact quotient

    nhat_3(86)/nhat_3(43)^2
      =3^7/(xPhi_1Phi_2^2)
      =gamma_1^(-1)gamma_2^(-1)gamma_3^(-1).

Predicted letter values are

    res(gamma_1)=res(gamma_2)=res(gamma_3)=2,

so

    theta_3(0)=2,
    vartheta_{3,2}=2,
    theta_3(1)=1.

The optional PARI leg must reproduce:

    one degree-16 factor,
    (e,f)=(8,2),
    valuation ladder (4,10,21,43),
    tr(Y)=1,
    norm(Y)=2.

Thus the boundary-read conclusion is checked at both slots:

    w_3=1,
    u_3(beta_1)=1=theta_3(1)w_3,
    u_3(beta_0)=2=theta_3(0)w_3^2.

These values are PREDICTED, not merely measured, because they are committed source values.

### S7.2 M2: per-instance legs

#### LEG-I1: GENTOW2-B''

Use the committed LP1 quotient:

    nhat_2(19)=4xPhi',
    nhat_2(38)=512x,

    nhat_2(19)^2/nhat_2(38)
      =xPhi'^2/32
      =gamma_2 gamma_1^5.

With

    z_2=1,
    z_1^3=1,

the runner must verify symbolically

    res(nhat_2(19)^2/nhat_2(38))=z_1^2,
    theta(0)=z_1,
    theta(1)=1.

It must then reproduce:

    LD1: P=y^2+z_1 y+z_1,
    LD2: P=y^2+z_1 y+1.

The quotient-ring arithmetic for this leg is exact symbolic arithmetic modulo `z_1^3-1`.

#### LEG-I2: HETOW-4

Encode the committed X/Z source fixtures:

    tau(H_0)=2,
    delta=2,

and the raw strings

    (2,2,1),
    (1,2,2,1).

Checks:

1. Each raw string is non-geometric over the committed residue field: consecutive ratios are not constant.

2. A character-law reconstruction from its first entry fails at a later entry.

3. For symbolic coefficients `a_0,...,a_D`, verify exactly that the map

       rhohat_t -> rhohat_t tau(H_0)delta^(-t)

   equals the polynomial substitution

       R(Z)=tau(H_0)Rhat(Z/delta).

4. Repeat with fixture lengths `3` and `4`, matching the two raw strings.

The fresh leg verifies the instantiation algebra. The unmodified committed runner in M4 remains responsible for the complete X/Z/S p-adic realization.

#### LEG-I3: GENTOW-6.4 non-instance regression

Reuse FRAME-P:

    p=3,
    Phi'=x^2-3,
    (e_1,f_1,h)=(2,1,1),
    (e_2,f_2,u_2)=(2,1,5),
    psi_2=T-1,
    Phi_2=Phi'^2-9x,

    f=(Phi_2^2+81Phi')(Phi'-27).

Implement exact monic division first by `Phi_2` and then by `Phi'`. Reconstruct the composed digits and verify the committed pin tuple

    (26,16,5),

with

    c_g=5.

For ambient lifts modulo `3^N`, verify the source's digit congruence and below-cap pin stability exactly as in the pasted frame. This leg is labelled `NON_INSTANCE_REGRESSION`; its success must not increment the count of common-lemma instantiations.

#### LEG-I4: [GENTOW5-W(i)]

At FRAME-LW3 reproduce exactly:

    theta_3(0)=2,
    theta_3(1)=1,
    w_3=tr(Y)=1,
    u_3(beta_0)=norm(Y)=2,
    u_3(beta_1)=1.

Then verify

    u_3(beta_0)=theta_3(0)w_3^2,
    u_3(beta_1)=theta_3(1)w_3.

This leg is recorded as checking [GENTOW5-W(i)] at **ATTEMPT GRADE, arc 1/2**.

### S7.3 M3: teeth

The fresh runner must contain at least the following four mutants, each required to fail.

#### T-1: character-law mutant

Replace the computed `tau(2)=2` in FRAME-C by the character prediction

    tau(2)=tau(1)^2=1.

This must fail both the exact quotient `x^2/5` and the coefficient comparison in P-C.

#### T-2: theta-free mutant

Replace

    U(d)=theta_d w^d

by

    U(d)=w^d.

At `d=2` in FRAME-C, the mutant predicts `4`, while the independently computed value is

    U(2)=res(5/T^2)=2.

At FRAME-LW3 it predicts

    u_3(beta_0)=w_3^2=1,

against the exact value `2`. Both kills must fire.

#### T-3: endpoint-as-input vacuity probe

Feed the false endpoint value

    U_mut(2)=4

while leaving the independently computed carrier data unchanged. The runner must check the pre-cancellation identity:

    w^2=4,

but

    U_mut(2)vartheta_2=4*2=3 mod 5.

The mismatch `4 != 3` must be reported as a detected contradiction. The runner must not overwrite `U_mut(2)` with the theorem's output or silently define it from `theta_2 w^2`.

This tooth witnesses that the endpoint is tested against independent peel and digit paths.

#### T-4: inverse-orientation mutant

Replace `theta_d` by `vartheta_d` in the boundary conclusion. At `d=2` in FRAME-C this predicts

    vartheta_2 w^2=2*4=3,

against `U(2)=2`.

This kills the common orientation error between the source's `theta` and the background's `vartheta`.

### S7.4 M4: regression legs

The technician must rerun the following committed runners unmodified.

1. `hetow_r2_hetow4.py`: GREEN at 203 checks and 37 dual-route gp jobs on frames X/Z/S certifies the realized section ratio, live raw non-character strings, assembled rescaling, and routing transport.

2. `gentow2_pe6_fresh.py`: GREEN at 68 checks certifies the B''/single-`w` residual realization in the committed PE6 frames.

3. `gentow6_r1_caplemma.py`: GREEN at 303 checks on frames P/P2/F certifies that the explicitly excluded non-instance remains valid and that T3 has not damaged its independent triangular-cap proof.

4. `gentow5_wi_checks.py`: GREEN at 60 checks on F-A/F-LW3 certifies the level-`i` normalizer recursion and the letter-live `i=3` instance of the boundary-read conclusion.

A regression mismatch is a T3 verification failure even when the fresh abstract runner remains green.

### S7.5 M5: joint-frame status

FRAME-C is a direct common-carrier joint frame:

    theta_2=3 != 1,
    tau is non-character,
    delta=2 != 1,
    w=3 != 1.

Thus both ports of the abstract lemma are simultaneously live.

However, FRAME-C's multiplicative reference `T` is formal; it is not claimed to be a realized FGMN tower normalizer. No pasted committed polynomial frame simultaneously records a live `theta` and a proved intrinsic B'' unit `w!=1`.

The reachable committed approximations are:

- X/Z: `tau` non-character and comparison unit `delta=2`;
- LW3: `theta_3(0)=2` but intrinsic `w_3=1`;
- LP1: live `theta(0)=z_1`, with the intrinsic `w` not priced in the paste;
- LW3's avatar is `2`, but the source explicitly records that the avatar is not the intrinsic `w_3`.

Therefore the cell

    realized p-adic tower with theta != 1 and intrinsic w != 1

remains **MACHINE-UNEXPLORED**. The fresh runner must print that coverage label and must not promote FRAME-C into a realized tower claim.

---

## S8. HONESTY BOX

### S8.1 Proven without an open sub-lemma

The abstract LEMMA COCYCLE-TELESCOPE, including its power telescope, boundary-read conclusion, bracket telescope, comparison formula, polynomial rescaling, and basic routing consequences, is completely proved from its stated hypotheses.

### S8.2 Source-specific facts not absorbed

1. The explicit gamma-letter evaluation of a ladder quotient is source-specific.

2. HETOW-4(a)'s formula

       tau(k)=eta^(-Q(m(k)))

   is source-specific floor arithmetic.

3. HETOW-4(b)'s displayed two-floor exponent requires that arithmetic after the common cocycle-comparison formula.

4. HETOW-4(d)'s common polynomial lift and independence of later refined keys require its own lift and iteration inputs.

5. GENTOW-6.4's triangularity, window stability, undercut, and projected block cap are not consequences of the common lemma.

6. [GENTOW5-W(i)] is cited only at **ATTEMPT GRADE, arc 1/2**. The re-derivation is conditional on the enumerated level-`i` input record and does not upgrade that source's repository grade.

### S8.3 Explicit open machine-coverage item

**OPEN COVERAGE T3-JOINT.** Exhibit a realized p-adic tower frame, with an independently computed intrinsic residual-read unit, for which both

    theta_d != 1
    and
    w != 1

hold in the same B'' boundary-read instance.

This is not needed for the proof. It is needed only to close the strongest joint machine-coverage cell.

### S8.4 What is not claimed

- No universal closed formula for `w_i`.
- No character law for a comparison ratio `tau`.
- No identification of an avatar unit with an intrinsic residual-read unit.
- No absorption of GENTOW-6.4.
- No extension to a source whose peel, expansion, positive-degree elimination, exact constant digit, or per-grade digit-factorization inputs have not been established.
- No statement that the enumerated machine frames exhaust the possible tower geography.

Grade: 0/2 attempt (CODEX arm, RCT unit T3-cocycle-telescope); hostile arc owed.
