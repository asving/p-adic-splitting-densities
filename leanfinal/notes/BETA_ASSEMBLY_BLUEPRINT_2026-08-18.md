# The beta assembly: a blueprint for classifier faithfulness at order at least two

Date: 2026-08-18

Scope: mathematical amendment to Chapter H, obstruction 2 of H.123

Disposition: **PROVE the new assembly; inherit the two already signed Chapter-B cites; add no new cite**

## 0. Executive conclusion

The cofactor in `betaChild_spec` must **not** be read as `typeOf H'`.  The polynomial `H'`
in the divided, recentred frame need not be monic.  In fact H.116's own blocker cell has

\[
  5Y^3+4Y^2=Y^2(5Y+4),
\]

so its `H' = 5Y+4` is non-monic.  By the definition in `Density/TypeOf.lean`, `typeOf` returns
the empty junk value on a non-monic polynomial.  Thus the sentence in the obstruction record
that informally writes

\[
  \operatorname{typeOf}(F)=\operatorname{typeOf}(B)+\operatorname{typeOf}(H')
\]

is not a theorem one should attempt to formalize.

The object with an honest splitting type is the unique **monic original-coordinate cofactor**
`Q` in H.116bR:

\[
  F=\operatorname{alphaParent}(b,k,\widehat z)\,Q.
\]

If `D = betaContent c k`, `mu` is the chosen child's multiplicity, and `A = monicPoly b`,
then `Q` represents `H'` through the exact frame identity

\[
 Q\bigl(\pi^k(Y+\widehat z)\bigr)
   =\pi^{D-\mu k}H'(Y).                                      \tag{0.1}
\]

Here `mu*k <= D` is landed as `mul_le_betaContent` (up to commutation of multiplication).
Equation (0.1), not `typeOf H'`, is the missing semantic bridge.

Let `L(c)` be the finite set of all triples `(mu,k,z)` satisfying `HasChildAt pi c mu k z`.
For a lift `F = monicPoly a`, put

\[
  \Omega_c:=\operatorname{order1Type}(\pi,X,F).
\]

This is independent of the lift: `visible_of_not_isDrainState`, the coefficient congruence
obtained from `pow_dvd_coeff_comp_sub` at the key `X`, and `order1Type_congr` prove that
assertion.  If `c` is neither DRAIN nor CS, the repeated residual blocks are exactly the members
of `L(c)`, and every such block has order-one label `(1,1)`.  Define

\[
 R_c:=\Omega_c.\mathrm{data}
       - \operatorname{replicate}(|L(c)|,(1,1)).               \tag{0.2}
\]

If every beta child `p in L(c)` is decided with type `sigma_p`, the exact assembly is

\[
 \operatorname{typeOf}(F).\mathrm{data}
   =R_c+\sum_{p\in L(c)}\sigma_p.\mathrm{data}.                \tag{0.3}
\]

For a selected child `p0`, the exact reading of its H.116 cofactor is

\[
 \boxed{
 \operatorname{typeOf}(Q).\mathrm{data}
   =R_c+\sum_{p\in L(c)\setminus\{p_0\}}\sigma_p.\mathrm{data}}
                                                                    \tag{0.4}
\]

together with (0.1).  Formula (0.4) is the requested missing `typeOf`-reading.  Formula (0.3)
is the form H.123b should consume.

## 1. Exact theorem to add to Chapter H

The following is the mathematical statement.  The displayed Lean is a signature sketch; in
particular, proofs of `Finset` membership may require harmless dependent transports.

```lean
noncomputable def betaIndexFinset
    (pi : O) {m N : Nat} (c : ClusterState O m N) :
    Finset (Nat × Nat × ResidueField O) :=
  (childSet_finite pi c).toFinset

noncomputable def betaRemainderData
    (pi : O) {m N : Nat} (c : ClusterState O m N) :
    Multiset (Nat × Nat) :=
  (Leaf.order1Type pi X (monicPoly (classSect O m N c.1))).data -
    Multiset.replicate (betaIndexFinset pi c).card (1, 1)
```

The public assembly theorem should not expose a choice of B.42/B.48 factors:

```lean
theorem typeOf_beta_assembly
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {pi : O} (hpi : Irreducible pi) {m N : Nat}
    (hm : 2 <= m) (hN : 1 <= N) (c : ClusterState O m N)
    (h0 : Not (IsDrainState c)) (hcs : Not (IsCSState pi c))
    (sigma : Nat × Nat × ResidueField O -> FactorizationType)
    (hsigma : forall p, p ∈ betaIndexFinset pi c ->
      DecidedAt O p.1 (sigma p) (N - betaContent c p.2.1)
        (betaChild pi c (betaIndexFinset_mem.mp ‹p ∈ betaIndexFinset pi c›)
          (N - betaContent c p.2.1)).1) :
    forall a : Fin m -> O, proj O m N a = c.1 ->
      (typeOf (monicPoly a)).data =
        betaRemainderData pi c +
          ∑ p ∈ betaIndexFinset pi c, (sigma p).data
```

The selected-cofactor theorem should say exactly what `H'` means:

```lean
theorem exists_beta_frame_cofactor_read
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {pi : O} (hpi : Irreducible pi) {m N : Nat}
    (hm : 2 <= m) (hN : 1 <= N) (c : ClusterState O m N)
    (h0 : Not (IsDrainState c)) (hcs : Not (IsCSState pi c))
    (sigma : Nat × Nat × ResidueField O -> FactorizationType)
    (hsigma : forall p, p ∈ betaIndexFinset pi c ->
      DecidedAt O p.1 (sigma p) (N - betaContent c p.2.1)
        (betaChild pi c (betaIndexFinset_mem.mp ‹p ∈ betaIndexFinset pi c›)
          (N - betaContent c p.2.1)).1)
    (p0 : Nat × Nat × ResidueField O)
    (hp0 : p0 ∈ betaIndexFinset pi c)
    (a : Fin m -> O) (ha : proj O m N a = c.1) :
    exists (b : Fin p0.1 -> O) (H' Q : Polynomial O),
      (forall i, b i ∈ maximalIdeal O) /\
      Q.Monic /\ Q.natDegree = m - p0.1 /\
      monicPoly a =
        alphaParent pi b p0.2.1 (resSect O p0.2.2) * Q /\
      (monicPoly a).comp
          (Polynomial.C (pi ^ p0.2.1) *
            (X + Polynomial.C (resSect O p0.2.2))) =
        Polynomial.C (pi ^ betaContent c p0.2.1) *
          (monicPoly b * H') /\
      IsCoprime (X ^ p0.1) (H'.map (IsLocalRing.residue O)) /\
      Q.comp
          (Polynomial.C (pi ^ p0.2.1) *
            (X + Polynomial.C (resSect O p0.2.2))) =
        Polynomial.C
          (pi ^ (betaContent c p0.2.1 - p0.1 * p0.2.1)) * H' /\
      proj O p0.1 (N - betaContent c p0.2.1) b =
        (betaChild pi c (betaIndexFinset_mem.mp hp0)
          (N - betaContent c p0.2.1)).1 /\
      (typeOf Q).data =
        betaRemainderData pi c +
          ∑ p ∈ (betaIndexFinset pi c).erase p0, (sigma p).data
```

The exponent in this sketch is written `D - mu*k`; changing it to `D - k*mu` is only a
normal-form choice.  This theorem deliberately makes no assertion about `typeOf H'`.

## 2. Mathematical proof, with every dependency classified

Throughout, fix a complete DVR `O`, an irreducible uniformizer `pi`, `2 <= m`, `1 <= N`, a
cluster state `c`, and a lift `a` of `c.1`.  Assume `c` is neither DRAIN nor CS.

### Step 1: put every lift in Chapter B's order-one arena

The following facts are routine consequences of landed declarations:

1. `monicPoly_monic` and `monicPoly_natDegree` give that `F := monicPoly a` is monic of degree
   `m`.
2. `mem_maximalIdeal_of_proj hN c ha` puts every coefficient `a i` in the maximal ideal.
   Then `monicPoly_map_residue` gives `F_bar = X^m`.
3. `h0` implies `a 0 != 0`: if `a 0 = 0`, its level-`N` class has residual order `N`, and
   `isDrainState_iff` makes `c` a DRAIN.  Since `dev_X` identifies `dev X F 0` with the constant
   coefficient, `dev X F 0 != 0`.
4. The key hypothesis for `X` is the public
   `Uniformity.Density.Leaf.GateKit.isKey_X` in `ChapB/B83Kit`.

Only item 3 lacks a convenient exported wrapper.  Add the routine lemma:

```lean
theorem cluster_lift_order1_input
    {pi : O} (hpi : Irreducible pi) {m N : Nat} (hN : 1 <= N)
    {c : ClusterState O m N} (h0 : Not (IsDrainState c))
    {a : Fin m -> O} (ha : proj O m N a = c.1) :
    (monicPoly a).Monic /\
    (monicPoly a).map (IsLocalRing.residue O) = X ^ m /\
    dev X (monicPoly a) 0 != 0
```

This is **OPEN-ROUTINE**, not open mathematics and not a citation candidate.

### Step 2: form the canonical double dissection

Apply `exists_slope_factorization hpi isKey_X` (B.42) to `F`.  It produces a finite set of
coprime slopes `p=(u,ell)`, monic pure factors `F_p`, their product `F`, and a unit residual tie
between the residual polynomial of `F` on that side and that of `F_p`.

For each `p`, apply `exists_residual_dissection` (B.48) to `F_p`.  The side is nonempty and has
positive degree because B.42's slope-index clause says its side has more than one point.
The standard height pins, divisibility by `deg X = 1`, and support non-top conditions are the
same derivations already carried out in `typeOf_of_separable_residuals` (B.63).  One obtains

\[
 F=\prod_{(p,\psi)\in T}G_{p,\psi},                           \tag{2.1}
\]

where, writing `a(p,psi)>0`,

* `G_(p,psi)` is monic and `(u,ell)`-pure;
* `deg G_(p,psi) = ell * a(p,psi) * deg psi`, because `deg X=1`;
* its residual polynomial is a nonzero scalar times `psi ^ a(p,psi)`;
* `psi` is monic irreducible;
* `T` is exactly the double index used by `order1Type`, namely `slopeFinset` followed by
  `resFactorFinset`.

B.48's public existential does not export that last canonical-index equality.  B.63 proves it
only inside a private local construction and under separability.  Therefore add:

```lean
theorem exists_canonical_order1_dissection
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {pi : O} (hpi : Irreducible pi) {f : Polynomial O}
    (hf : f.Monic) {mu : Nat} (hmu : 0 < mu)
    (hres : f.map (IsLocalRing.residue O) = X ^ mu)
    (hdev : dev X f 0 != 0) :
    exists (G : (Nat × Nat) × Polynomial (Leaf.resField X) -> Polynomial O)
      (mult : (Nat × Nat) × Polynomial (Leaf.resField X) -> Nat),
      f = ∏ p ∈ Leaf.slopeFinset pi X f,
            ∏ psi ∈ Leaf.resFactorFinset pi X f p, G (p, psi) /\
      forall p ∈ Leaf.slopeFinset pi X f,
        forall psi ∈ Leaf.resFactorFinset pi X f p,
          0 < mult (p, psi) /\
          (G (p, psi)).Monic /\
          Leaf.IsPure X (G (p, psi)) p.1 p.2 /\
          (G (p, psi)).natDegree =
            p.2 * mult (p, psi) * psi.natDegree /\
          exists hne H cunit,
            Leaf.resPoly pi X (G (p, psi)) p.1 p.2 hne H =
              Polynomial.C cunit * psi ^ mult (p, psi)
```

This is **OPEN-PROOF**, but its proof is a general rerun of landed B.42, B.48, B.45,
`natDegree_resPoly`, `mem_slopeFinset`, and `mem_resFactorFinset`.  It imports no new
mathematics.  The theorem must be proved for arbitrary `m`, arbitrary finite residue field,
and every lift satisfying the displayed hypotheses; a bounded-degree census is not a proof.

### Step 3: classify the repeated blocks on a non-CS state

Fix a double block `(p,psi)` and put `r=a(p,psi)`.  If `r >= 2`, then `psi^2` divides the
residual polynomial on the corresponding side.  The residual tie in B.42, together with
`resPoly_mul_of_pure` where product transport is needed, moves this divisibility to the
residual polynomial of `F`.

If `p.2 * deg psi >= 2`, this gives the CS witness at the chosen lift: the slope denominator is
positive and coprime to its numerator, the side and height pin came from B.42, `psi` is
irreducible, and `psi^2` divides the residual polynomial.  To meet `IsCSState`'s **universal
lift** quantifier, transport that witness to an arbitrary lift with
`visible_of_not_isDrainState`, `sideSet_congr`, `npHgt_min_congr`, `H₀_lt_of_visible`, and
`resPoly_congr`; H.120's proof of `isCSState_clusterTrunc` contains this exact transport
pattern.  This contradicts `hcs`.  Hence

\[
 p.2\deg\psi<2.
\]

Both factors are positive (`p.2>0`; an irreducible polynomial has positive degree), so

\[
 p.2=1,\qquad \deg\psi=1.                                    \tag{3.1}
\]

A monic degree-one polynomial has the form `X - C z`; this is `Monic.eq_X_add_C` followed by
the definition `z = -psi.coeff 0`.  Moreover `z != 0`.  Indeed `natDegree_resPoly` says the
whole residual polynomial has nonzero constant coefficient; since `psi` divides it, `psi`
cannot be `X`.

With `k=p.1` and this nonzero `z`, the statement that `psi^r` is the residual block is
equivalent, coefficient by coefficient, to H.109's recentred divisibility pattern:

* every coefficient is divisible by `pi^D`;
* coefficients below `r` are divisible by `pi^(D+1)`;
* coefficient `r` is not divisible by `pi^(D+1)`.

The one-lift calculation is promoted to all lifts by `hasChildAt_of_exists`.  It gives
`HasChildAt pi c r k z`.

Conversely, if `HasChildAt pi c mu k z`, `exists_dividedFrame_at` and
`exists_residue_split` show that the divided frame has reduction `X^mu U` with `U(0) != 0`.
Undoing the translation sends `X^mu` to `(X-C z)^mu`; the canonical B.42/B.48 dissection
therefore contains the block `(p,psi)=((k,1),X-C z)` with multiplicity `mu`.  Uniqueness of
factorization in the residue polynomial ring excludes a second such block.  On the H.109
side, `hasChildAt_mult_unique` excludes a second multiplicity at the same `(k,z)`.

Package both directions as the core dictionary:

```lean
theorem repeated_order1Block_iff_hasChildAt
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {pi : O} (hpi : Irreducible pi) {m N : Nat}
    (hm : 2 <= m) (hN : 1 <= N) (c : ClusterState O m N)
    (h0 : Not (IsDrainState c)) (hcs : Not (IsCSState pi c))
    {a : Fin m -> O} (ha : proj O m N a = c.1)
    (G mult : /* data supplied by exists_canonical_order1_dissection */) :
    exists e :
      {t // t ∈ order1BlockFinset pi X (monicPoly a) /\ 2 <= mult t} ≃
      {p // p ∈ betaIndexFinset pi c},
      forall t,
        let p := e t
        p.1.1 = mult t /\ t.1.2 = 1 /\ t.2.natDegree = 1 /\
        t.2 = X - Polynomial.C p.1.2.2
```

The precise sign in the last linear polynomial depends on the chosen `z` convention and must
be checked once against `X + C (resSect z)`; the mathematical assertion is that translating
the residual root `z` to zero gives `X^mu`.

This is **OPEN-MATH / PROVE** and is the first genuinely new node.  Its proof is the general
argument above.  No step depends on a degree bound.

### Step 4: identify H.116's planted factor with the repeated B.48 block

For a repeated block corresponding to `p=(mu,k,z)`, recenter its factor `G_(p,psi)` and divide
by its pure content.  By (3.1), its divided residual is `X^mu`; the resulting monic degree-`mu`
factor is therefore a cluster development `monicPoly b'`.  Undoing the shift and scaling gives

\[
 G_{p,\psi}=\operatorname{alphaParent}(b',k,\widehat z),       \tag{4.1}
\]

using `alphaParent_recentre`, `alphaParent_monic`, and `alphaParent_natDegree`.

H.116's construction supplies another monic degree-`mu` factor `monicPoly b` of the same
divided frame, with reduction `X^mu`, and its cofactor is residually coprime to `X^mu`.
Importantly, the public conclusion of `betaChild_spec` drops that last coprimality fact even
though its local `split` proves it.  Export the following strengthening before attempting the
match:

```lean
theorem betaChild_spec_with_coprime
    [IsAdicComplete (maximalIdeal O) O]
    {pi : O} (hpi : Irreducible pi) {m N mu k : Nat}
    {z : ResidueField O} (hm : 2 <= m) (hN : 1 <= N)
    (c : ClusterState O m N) (h : HasChildAt pi c mu k z)
    (h0 : Not (IsDrainState c))
    (a : Fin m -> O) (ha : proj O m N a = c.1) :
    exists (b : Fin mu -> O) (H' : Polynomial O),
      (forall i, b i ∈ maximalIdeal O) /\
      (monicPoly a).comp
          (Polynomial.C (pi ^ k) * (X + Polynomial.C (resSect O z))) =
        Polynomial.C (pi ^ betaContent c k) * (monicPoly b * H') /\
      IsCoprime (X ^ mu) (H'.map (IsLocalRing.residue O)) /\
      proj O mu (N - betaContent c k) b =
        (betaChild pi c h (N - betaContent c k)).1
```

This is **OPEN-ROUTINE**: refactor the already landed proof of `betaChild_spec`, or rerun
`exists_dividedFrame_at`, `exists_residue_split`, and
`exists_monic_factorization_of_monic_left`.  It adds no mathematical hypothesis.

Now apply
`monicFactor_congr_of_pow_dvd_sub` to the two factorizations for every power `pi^s`; the product
difference is zero, hence divisible by every power.  A DVR is separated, so a coefficient
divisible by every `pi^s` is zero.  Thus `b=b'`, (4.1) is exactly H.116's planted factor, and
the projection statement in `betaChild_spec` identifies its coefficient class with the beta
child.

The only missing general helper in that paragraph is:

```lean
theorem monicFactor_eq_of_same_dividedFrame
    {pi : O} (hpi : Irreducible pi) {mu : Nat}
    {A A' B B' : Polynomial O}
    (hA : A.Monic) (hA' : A'.Monic)
    (hAd : A.natDegree = mu) (hA'd : A'.natDegree = mu)
    (hAr : A.map (IsLocalRing.residue O) = X ^ mu)
    (hA'r : A'.map (IsLocalRing.residue O) = X ^ mu)
    (hcop : IsCoprime (X ^ mu) (B.map (IsLocalRing.residue O)))
    (heq : A * B = A' * B') :
    A = A'
```

It is **OPEN-ROUTINE**: iterate the landed `monicFactor_congr_of_pow_dvd_sub` and use the DVR
valuation to separate the powers.  If a direct coprimality/cancellation lemma already in
mathlib shortens it, that is an implementation choice, not a citation.

The resulting block match should be exported separately:

```lean
theorem order1Block_eq_alphaParent_of_child
    /* common hypotheses and canonical dissection data */
    (p : {p // p ∈ betaIndexFinset pi c}) :
    exists b : Fin p.1.1 -> O,
      (forall i, b i ∈ maximalIdeal O) /\
      G (repeatedBlockOfChild p) =
        alphaParent pi b p.1.2.1 (resSect O p.1.2.2) /\
      proj O p.1.1 (N - betaContent c p.1.2.1) b =
        (betaChild pi c (betaIndexFinset_mem.mp p.2)
          (N - betaContent c p.1.2.1)).1
```

This is **OPEN-MATH / PROVE** and is the second genuinely new node.

### Step 5: read every simple block

If `a(p,psi)=1`, B.48 gives an irreducible residual polynomial up to a unit.  Apply the landed
`typeOf_leaf_of_cite bBox1_cite` to the block.  Since the key is `X`, its type is the singleton

\[
  \{(p.2,\deg\psi)\}.                                        \tag{5.1}
\]

The scalar multiple of an irreducible polynomial is irreducible, and the side-degree equality
is supplied by `natDegree_resPoly` and B.48's residual identity.  This is the same plumbing as
the private `typeOf_leaf_block` inside B.63, with the general perimeter now discharged by the
landed cite.

No new open mathematics occurs in this step.  A public wrapper is still worthwhile:

```lean
theorem typeOf_simple_order1Block
    /* hypotheses and one canonical block t */
    (hsimple : mult t = 1) :
    typeOf (G t) =
      ⟨{(t.1.2, (X : Polynomial O).natDegree * t.2.natDegree)}⟩
```

This is **OPEN-ROUTINE**, with axiom footprint exactly `bBox1_cite`.

### Step 6: identify the all-child cofactor

Take `L=betaIndexFinset pi c` in the landed `exists_peel_finset`.  It gives

\[
 F=\left(\prod_{p\in L}\operatorname{alphaParent}(b_p,k_p,\widehat z_p)\right)Q_L, \tag{6.1}
\]

with `Q_L` monic.  Steps 3 and 4 identify the product in (6.1) with the product of **all and
only** repeated B.48 blocks.  Compare with (2.1) and cancel that monic nonzero product in the
domain `O[X]`.  The result is

\[
 Q_L=\prod_{t:\,a(t)=1}G_t.                                  \tag{6.2}
\]

Repeated application of landed `typeOf_prod` (or `typeOf_mul`) and (5.1) yields

\[
 \operatorname{typeOf}(Q_L).\mathrm{data}
   =\sum_{t:\,a(t)=1}\{(\ell_t,\deg\psi_t)\}.                 \tag{6.3}
\]

By `order1Type_data` / `order1Type_data_eq_sum`, `Omega_c.data` is the same sum over **all**
double blocks, once each and without residual multiplicity.  Steps 3 and 4 say the omitted
blocks are in bijection with `L` and each omitted label is `(1,1)`.  Multiset subtraction is
therefore exact, not truncated accidentally, and (6.3) is exactly (0.2).

This gives the central cofactor node:

```lean
theorem typeOf_allChildCofactor
    /* common hypotheses; L is betaIndexFinset pi c */
    (a : Fin m -> O) (ha : proj O m N a = c.1) :
    exists bb Q,
      monicPoly a =
        (∏ p ∈ (betaIndexFinset pi c).attach,
          alphaParent pi (bb p) p.1.2.1 (resSect O p.1.2.2)) * Q /\
      Q.Monic /\
      (typeOf Q).data = betaRemainderData pi c
```

This is **OPEN-MATH / PROVE** but contains no mathematics beyond the two core open nodes and
landed `exists_peel_finset`, `typeOf_prod`, and `order1Type_data_eq_sum`.

For a selected child `p0`, repeat the same comparison after peeling only `p0`, or regroup
(2.1) with that block first.  The remaining monic cofactor is the product of all simple blocks
and all repeated blocks other than `p0`.  Child decision and
`order1Block_eq_alphaParent_of_child`, followed by `typeOf_scaleRoots` and `typeOf_shift`, read
each remaining repeated block as `sigma_p`.  This proves (0.4).

Finally derive (0.1).  Compose `F=P Q` with the selected frame.  `alphaParent_recentre` gives
the frame of `P` as `pi^(mu*k) monicPoly b`; `betaChild_spec` gives the frame of `F` as
`pi^D (monicPoly b) H'`; `mul_le_betaContent` allows
`pi^D=pi^(mu*k)pi^(D-mu*k)`.  Cancel the nonzero scalar and the nonzero monic polynomial.

### Step 7: reassemble the parent

Use (6.1), `typeOf_prod`, and the child projection equalities.  For every `p`, `hsigma p`
reads `typeOf (monicPoly (bb p))` as `sigma_p`.  From the definition of `alphaParent`, landed
`typeOf_scaleRoots` and `typeOf_shift` give

\[
 \operatorname{typeOf}(\operatorname{alphaParent}(b_p,k_p,\widehat z_p))
   =\operatorname{typeOf}(\operatorname{monicPoly} b_p)
   =\sigma_p.                                                  \tag{7.1}
\]

Combining (7.1) with `typeOf_allChildCofactor` proves (0.3).  Export the routine transport:

```lean
theorem typeOf_alphaParent
    {pi : O} (hpi : Irreducible pi) {mu : Nat}
    (b : Fin mu -> O) (k : Nat) (w : O) :
    typeOf (alphaParent pi b k w) = typeOf (monicPoly b)
```

This is **OPEN-ROUTINE**, directly from `alphaParent`, `typeOf_scaleRoots`, and `typeOf_shift`.

## 3. Closing H.123b once the assembly lands

Prove the contrapositive of `BridgeA` by well-founded induction on the lexicographic pair
`(m,N)`:

\[
  \neg\operatorname{ClusterUndecided}(c)
  \quad\Longrightarrow\quad
  \exists\sigma,\operatorname{DecidedAt}(m,\sigma,N,c.1).      \tag{3.1}
\]

Use `cluster_partition`.

* DRAIN and CS contradict `not ClusterUndecided` by the corresponding constructors of H.118.
* In an alpha state, `clusterUndecided_iff` says the alpha child is not cluster-undecided.
  The alpha window strictly decreases (`alphaChild_window_lt` in H.118), so the induction
  hypothesis decides it.  `alphaChild_spec`, `typeOf_shift`, and `typeOf_scale` transport that
  decision to every parent lift.
* In a beta state, every beta child is not cluster-undecided: one undecided child would invoke
  H.118's beta constructor.  `betaChild_mult_lt` strictly decreases the first lexicographic
  coordinate; `betaChild_window_le` controls the second.  The induction hypothesis therefore
  supplies `sigma_p` and `DecidedAt` for every member of the finite child set.  Apply
  `typeOf_beta_assembly` to obtain one parent type, independent of the lift.
* In a DEC state the child finset is empty by the definition of `IsDecState`.  Apply the same
  assembly with the empty family.  It says the parent type is the lift-independent
  order-one read, exactly the simple-block case.

Negating (3.1) is `UndecidedAt -> ClusterUndecided`, because `UndecidedAt` is defined as the
failure of `DecidedAt` for every type.  This is `BridgeA`; the landed
`h123Target_of_bridgeA` / `undecidedCount_le_uCluster_of_bridge` then closes H.123.

The induction theorem should be its own node:

```lean
theorem decidedAt_of_not_clusterUndecided
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {pi : O} (hpi : Irreducible pi) {m N : Nat}
    (hm : 2 <= m) (hN : 1 <= N) (c : ClusterState O m N)
    (hread : Not (ClusterUndecided O pi m N c)) :
    exists sigma, DecidedAt O m sigma N c.1

theorem bridgeA_betaFaithful
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
    {pi : O} (hpi : Irreducible pi) {m N : Nat}
    (c : ClusterState O m N) :
    UndecidedAt O m N c.1 -> ClusterUndecided O pi m N c
```

The low-degree or zero-window goals generated by the induction should be discharged from
`hm`, `hN`, `one_le_window_of_not_drain`, and the branch hypotheses; they must not be hidden in
an extra theorem assumption.

## 4. Citation decision and citable clauses

### 4.1 New beta assembly: prove, do not cite

No new literature cite is needed for Steps 3, 4, or 6.  They are:

* a comparison between the repo's own definitions of residual multiplicity and `HasChildAt`;
* uniqueness of a monic factor with specified residual factor in one divided frame;
* cancellation and `typeOf_mul` over a finite product.

These statements are narrower than a published Montes-classifier theorem and are designed to
connect two repo-specific interfaces.  Citing a broad classifier theorem would still leave the
interface-faithfulness map unproved.  The owner's paper is not cited anywhere in this route.

### 4.2 Literature input that is genuinely needed: B.42, already signed

**Minimal citable clause.**  Over a complete DVR, a monic polynomial whose reduction is a
positive power of an order-one key and whose zeroth development coefficient is nonzero admits
the finite factorization by the sides of its key-Newton polygon; the factors are monic and pure
at their respective coprime slopes, their product is the original polynomial, and each
factor's residual polynomial agrees with the corresponding side residual polynomial up to a
unit.

**Published source.**  J. Guàrdia and E. Nart, *Genetics of polynomials over local fields*,
Contemporary Mathematics 637 (2015), 207-241, Theorem 2.3, together with the full-key-scope leg
of J. Fernández, J. Guàrdia, J. Montes, and E. Nart, *Residual ideals of MacLane valuations*,
*Journal of Algebra* 427 (2015), 30-75, Theorem 6.6.  This is precisely the existing
`exists_slope_factorization` import.

**Faithfulness paragraph.**  The clause is used only with the Gauss key `X`; completeness is
explicit; the finite slope set, purity, product equality, exact side-index characterization,
and unit residual tie are each consumed.  The FGMN co-primary is retained because GN15's
chain-relative formulation alone does not cover the whole `IsKey` binder of the landed axiom.
No stronger assertion about irreducibility or splitting type is attributed to B.42.

### 4.3 Literature input that is genuinely needed: B-BOX-1, already signed

**Minimal citable clause.**  A monic one-side block with residual multiplicity one and
irreducible residual factor `psi` has exactly one splitting-type entry
`(ell, deg(phi)*deg(psi))`.

**Published source.**  FGMN, Theorem 6.6, and Guardia-Nart, Theorem 2.3 and equation (2.1), with
the classical residue-degree/norm glue recorded in the existing Serre/Neukirch faithfulness
entry.  This is precisely the existing `bBox1_cite`, consumed through
`typeOf_leaf_of_cite bBox1_cite`.

**Faithfulness paragraph.**  The beta assembly invokes the clause only for B.48 blocks whose
residual exponent is exactly one.  It does not apply the cite to repeated residual factors;
those are sent to beta children and handled inductively.  The hypotheses `Monic`, `IsPure`,
positive side degree, key-power reduction, pinned height, and residual irreducibility are all
supplied by B.48 and the B.30 degree calculation.  Thus the known multiplicity-two failure is
outside the invocation.

No duplicate axiom or fresh gate-(b) declaration should be introduced.  The final H.123b
axiom footprint should visibly inherit `exists_slope_factorization` and `bBox1_cite` and no
additional literature name from this unit.

## 5. Node decomposition and dependency order

| Node | Status | Content | Principal landed inputs |
|---|---|---|---|
| `H.betaA0` | routine proof | `betaIndexFinset`, membership iff `HasChildAt` | `childSet_finite` |
| `H.betaA1` | routine proof | `cluster_lift_order1_input`; lift-independent `order1Type` | `mem_maximalIdeal_of_proj`, `monicPoly_map_residue`, `visible_of_not_isDrainState`, `order1Type_congr`, `GateKit.isKey_X` |
| `B.betaA2` | proof | canonical nonseparable double dissection | `exists_slope_factorization`, `exists_residual_dissection`, B.45, `natDegree_resPoly`, slope/residual finset membership lemmas |
| `H.betaA3` | **new math** | repeated double blocks iff children | `IsCSState`, `hasChildAt_of_exists`, `exists_dividedFrame_at`, `exists_residue_split`, `hasChildAt_mult_unique`, `resPoly_mul_of_pure` |
| `H.betaA4` | routine proof | export `betaChild_spec_with_coprime`; exact monic-left-factor uniqueness in one divided frame | H.116 extraction lemmas, `monicFactor_congr_of_pow_dvd_sub`, DVR separatedness |
| `H.betaA5` | **new math** | repeated B.48 block equals H.116 `alphaParent` factor | `H.betaA3`, `H.betaA4`, `betaChild_spec`, `alphaParent_recentre` |
| `B.betaA6` | routine, cite-conditional | type of a simple block | `typeOf_leaf_of_cite bBox1_cite`, B.30/B.48 |
| `H.betaA7` | assembly proof | all-child cofactor formula (0.2) | `exists_peel_finset`, `typeOf_prod`, `order1Type_data_eq_sum`, `H.betaA5`, `B.betaA6` |
| `H.betaA8` | assembly proof | selected `H'` representation (0.1), cofactor read (0.4), parent formula (0.3) | `betaChild_spec`, `mul_le_betaContent`, `alphaParent_recentre`, `typeOf_alphaParent`, `H.betaA7` |
| `H.betaA9` | bridge proof | `not ClusterUndecided -> exists DecidedAt`; `BridgeA` | `cluster_partition`, `clusterUndecided_iff`, H.118 measure lemmas, alpha spec, `H.betaA8` |

Suggested file order:

1. a Chapter-B amendment exporting `exists_canonical_order1_dissection` and
   `typeOf_simple_order1Block`;
2. an H.116-adjacent dictionary/matching file for `betaA0` through `betaA5`;
3. a dedicated beta-assembly file for `betaA7` and `betaA8`;
4. H.123b for `betaA9`, followed by the existing H.123 counting reduction.

The axiom checks should be placed at `B.betaA2`, `B.betaA6`, `H.betaA8`, and `H.betaA9`.
Expected non-core footprint: `exists_slope_factorization` and `bBox1_cite` only (plus whatever
already appears through unrelated imported bridge infrastructure); B.48 and every new beta
node are proofs.

## 6. Failure modes this amendment must forbid

1. **Do not state `typeOf H'`.**  It is junk when `H'` is non-monic.
2. **Do not assume residual separability.**  The repeated exceptional blocks are the entire
   point of the beta recursion.
3. **Do not subtract residual multiplicity from `order1Type`.**  `order1Type` records each
   distinct `(p,psi)` once.  One `(1,1)` is removed per child, not `mu` copies.
4. **Do not enumerate degrees.**  The dictionary and matching lemmas are universal in `m`.
5. **Do not identify blocks merely by equal degree.**  The proof must use the residual
   `X^mu`/coprime-cofactor uniqueness in the same divided frame.
6. **Do not pick only one beta child in the parent assembly.**  The cofactor after one peel
   still contains every other repeated block.  Formula (0.4) records them explicitly.
7. **Do not let the canonical centre drift.**  `betaChild_spec` is pinned at `resSect O z`;
   every block match must use that same centre.
8. **Do not duplicate the signed cites.**  Consume B.42 and B-BOX-1 under their existing names,
   with their footprints visible.

With those fences, the beta assembly is a finite algebraic comparison theorem, and obstruction
2 of H.123 reduces to the two explicit new mathematical nodes `H.betaA3` and `H.betaA5` plus
the stated assembly bookkeeping.
