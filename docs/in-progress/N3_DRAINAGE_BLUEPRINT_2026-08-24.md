# U10 blueprint — formalizing cubic drainage (HYP.08 → `DrainageAt 3`)

**Date:** 2026-08-24  
**Scope:** `leanfinal/`; complete DVRs with finite residue field, including residue
characteristic `2` and `3`.  
**Source proof:** `docs/in-progress/N3_DRAINAGE_PROOF_2026-08-24.md` (U8).  
**Signature check:** `leanfinal/scratch/U10_sig_check.lean`.

## 0. Executive verdict and two necessary honesty corrections

U8's main counting argument has a clean Lean carrier and is already represented in the present
tree by `Uniformity/ChapH/H97r1.lean` through `H97r4.lean`.  Its central theorem is the natural
number recurrence

```lean
theorem undecidedCount_three_recursion (M : ℕ) :
    undecidedCount O 3 (M + 3)
      ≤ residueCard O ^ (2 * (M + 3))
        + residueCard O ^ 4 * undecidedCount O 3 M
```

(`H97r4.lean:251`).  It counts the **actual** `undecidedSet O 3 N`, not `Menu.hex3U`.
The recurrence is unrolled in `H97b.lean` to

```lean
theorem rate_three :
    Induction.RateSpecies (residueCard O) 1 0 3 (undecidedSeq O 3)
```

and the same file already lands `drainageAt_three : DrainageAt 3`.  Thus the mathematical and
formal HYP.08 → HYP.09 drainage path is closed in the current tree.

Two statements must nevertheless not be conflated.

1. **H.97's literal historical hypothesis remains a different, sharper small-level
   statement.**  It asks for constants `(K,B,c) = (1,1,0)`.  U8 proves the recurrence and
   convergence, but does not prove the sharp level-1 census needed by that exact constant tuple.
   The present corpus explicitly records this in `H97b.lean:37–44`: `rate_three` has constants
   `(1,0,3)`, and does not discharge `(1,1,0)`.  Nodes U10.12–U10.15 below give a fixed design for
   closing the literal hypothesis; they are **BLUEPRINT**, not PROVED from U8.
2. **The explicit Haar-null assertion in U8 §9 has no present Lean carrier.**
   `Density/Drainage.lean:14–23` and `Density/GenuineDensity.lean:263–267` expressly say that the
   corpus proves equality/limits of cylinder-count proportions, not measurability or Haar measure
   of the underlying type locus.  `DrainageAt 3` needs only the former.  An explicit Haar-null
   theorem is therefore isolated as U10.17 **OPEN**, outside the capstone path.

No step below uses `hex3U`, `hex3U_rec`, or the sidecar-only
`UniformityCheck.drainage_three_of_triple`.

## 1. Exact targets in the current Lean vocabulary

### 1.1 H.97's `hrate`, verbatim from its use site

The use site is `leanfinal/Uniformity/ChapH/H97.lean:77–81`:

```lean
theorem package_three_of_rate
    (hrate : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
      [Finite (IsLocalRing.ResidueField O)],
      Induction.RateSpecies (residueCard O) 1 1 0 (undecidedSeq O 3)) :
    InductionPackage 3
```

By `H65.lean:38`, the body demanded at each `O` is exactly

```lean
∀ M, 1 ≤ M →
  undecidedSeq O 3 M
    ≤ 1 * (M : ℝ) ^ 1 * ((residueCard O : ℝ) ^ (M - 0))⁻¹
```

or, after simplification, `undecidedSeq O 3 M ≤ M * q⁻ᴹ` for `M ≥ 1`.

### 1.2 The formal HYP.09 target

`Density/Statement.lean:118` defines

```lean
def DrainageAt (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
    ∀ σ : FactorizationType, UndecidedVanishes O n σ
```

and `GenuineDensity.lean:335` defines

```lean
def UndecidedVanishes (n : ℕ) (σ : FactorizationType) : Prop :=
  Tendsto (gapSeq O n σ) atTop (nhds 0)
```

The target is therefore literally:

```lean
theorem drainageAt_three : DrainageAt 3
```

### 1.3 The type-correct corollary chains

The **current unconditional chain**, all with verified names, is

```text
undecidedCount_three_recursion
  → undecidedCount_three_mul_le
  → rate_three : RateSpecies q 1 0 3 (undecidedSeq O 3)
  → package_three : InductionPackage 3

undecidedCount_three_mul_le
  → undecidedSeq_three_tendsto_zero
  → drainage_of_undecided_comp (with φ = id)
  → drainage_three σ : UndecidedVanishes O 3 σ
  → drainageAt_three : DrainageAt 3.
```

The public declarations are in `H97b.lean:87,136,184,217,236`; the general last-mile theorem
`drainage_of_undecided_comp` is at `Density/DensityAPI.lean:213` and internally uses
`gapSeq_le_undecidedSeq` (`Density/Drainage.lean:716`).

The historical exact `(1,1,0)` chain starts with

```text
hrate → package_three_of_rate hrate : InductionPackage 3.
```

There is a typing caveat in the chapter-I prose.  The landed H.98 theorem is

```lean
theorem drainage_of_package (hp : ∀ n, InductionPackage n) : ∀ n, DrainageAt n
```

(`H98.lean:148`), so it cannot be applied to `package_three_of_rate hrate` alone.  It fires at
degree `3` only after a global supplier `hp : ∀ n, InductionPackage n` has been assembled.
For a degree-3-only proof, use the named local chain
`undecidedSeq_three_tendsto_zero → drainage_of_undecided_comp → drainageAt_three`, as the
current corpus does.  This is an API correction, not a mathematical obstruction.

## 2. The actual counting carrier (and the H-1 fence)

The corpus does **not** represent the coefficient box as a `Finset` of triples.  It uses finite
types and `Set` subtypes:

```lean
Coeff O n N                    -- coefficient vectors, definitionally Fin n → Res O N
undecidedSet O n N            -- Set (Coeff O n N)
undecidedCount O n N          -- Nat.card (undecidedSet O n N)
undecidedSeq O n N            -- (undecidedCount : ℝ) / q^(n*N)
```

The normalization is supplied by

```lean
card_res   (N)   : Nat.card (Res O N)       = residueCard O ^ N
card_coeff (n N) : Nat.card (Coeff O n N)   = residueCard O ^ (n * N)
```

(`Density/LocalData.lean:228,293`).  Subset and union bounds use `Set.ncard_le_ncard`,
`Set.ncard_union_le`, and `Nat.card_coe_set_eq`; injections use
`Nat.card_le_card_of_injective`; products use `Nat.card_prod`.  Equal-fibre calculations use
`card_preimage_of_surjective`, `card_preimage_coeffFactor`, and the cubic-specific
`card_preimage_mtrunc`.

This matches U8 exactly:

* the peel branch is the subtype
  `(undecidedSet O 3 N ∩ peelBranch N : Set (Coeff O 3 N))`;
* the triple branch is
  `(undecidedSet O 3 (M+3) ∩ tripleSet (M+3) : Set (Coeff O 3 (M+3)))`;
* the mixed box is the finite type
  `MBox O M = Res O M × Res O (M+1) × Res O (M+2)`;
* `mtrunc : MBox O M →+ Coeff O 3 M` reduces the last two coordinates to level `M`.

By contrast, `Menu.hex3U` (`ChapG/G66.lean:38`) is a pure arithmetic reader and
`Menu.hex3U_rec` (`ChapG/G67.lean:195`) is only its telescoping identity.  Chapter G's H-1 note
explicitly says that `hex3U_div_tendsto_zero` does not imply anything about
`undecidedCount O 3 N` without a bridge.  The U8/H97r route respects that fence: it proves a new
injection directly out of the actual `undecidedSet`, so no `hex3U` bridge is asserted.

The requested name `drainage_three_of_triple` is also not a `leanfinal` declaration: `rg` finds
it only in `leancheck/UniformityCheck/N3Drain.lean:350` (plus comments).  The present
`leanfinal` replacement is the stronger direct actual-set route above.

## 3. Node plan

Status vocabulary is literal:

* **PROVED**: U8 supplies the mathematics; only Lean transcription is required.  In the current
  checkout these nodes also happen already to be landed and can be used as reference
  implementations.
* **BLUEPRINT**: the design and proof route are fixed below, but the claim is not proved by U8's
  written argument.
* **OPEN**: a genuinely missing formal carrier or mathematical bridge.

Each row is sized as one focused 30–60 minute Lean task.

| node | status | content | dependencies |
|---|---|---|---|
| U10.00 | PROVED | Pin the target definitions and actual-set counting API | `H65`, `Drainage`, `Statement`, `LocalData` |
| U10.01 | PROVED | Characteristic-free cubic trichotomy and lift to `cubic_structure` | `cubic_trichotomy`, `exists_cubic_root` |
| U10.02 | PROVED | Recentring and the E/L/R decision certificates | P5 invariance, strong Hensel, `H97r1` |
| U10.03 | PROVED | Force case S and descend undecidedness through extraction | U10.02, `decidedAt_of_congr`, `typeOf_scale` |
| U10.04 | PROVED | Define the mixed box and prove its equal-fibre count | `card_res`, `card_coeff`, `card_preimage_of_surjective` |
| U10.05 | PROVED | Sharp triple-branch injection and `q⁴ C_M` bound | U10.03–04 |
| U10.06 | PROVED | Lossless movement of a simple root and its quadratic cofactor | `exists_root_congr`, `peel_congr`, `typeOf_linear_mul` |
| U10.07 | PROVED | Sharp peel injection and `q^(2N)` bound | U10.06, `undecidedCount_two_eq` |
| U10.08 | PROVED | Actual-undecided peel/triple dichotomy | U10.01, U10.07, `inert3_decided` |
| U10.09 | PROVED | Union bound and natural-number cubic recurrence | U10.05, U10.07–08 |
| U10.10 | PROVED | Unroll to the sufficient `(1,0,3)` `RateSpecies` | U10.09, `undecidedCount_le_card` |
| U10.11 | PROVED | Limit, `UndecidedVanishes`, and `DrainageAt 3` | U10.10, `drainage_of_undecided_comp` |
| U10.12 | BLUEPRINT | Sharp level-1 count `C₁ ≤ q²` for literal H.97 | U10.01, U10.06, G.36 quadratic reader |
| U10.13 | BLUEPRINT | Level-2 bound `C₂ ≤ 2q⁴` for literal H.97 | U10.04–05, U10.07–08 |
| U10.14 | BLUEPRINT | Strong induction `C_N ≤ N q^(2N)` for `N ≥ 1` | U10.09, U10.12–13 |
| U10.15 | BLUEPRINT | Cast U10.14 to H.97's exact `RateSpecies q 1 1 0` | U10.14, positivity of `residueCard` |
| U10.16 | PROVED | Feed packages and record the type-correct drainage chains | U10.11 or U10.15, `package_three_of_rate`, `drainage_of_package` |
| U10.17 | OPEN | Optional literal Haar-null locus theorem | missing Haar/measurability carrier; not needed by `DrainageAt` |

## 4. Per-node Lean proof plans

### U10.00 — interfaces and normalization — PROVED

Use the definitions as they stand, without introducing a parallel notion of undecidedness:

```lean
undecidedCount O 3 N = Nat.card (undecidedSet O 3 N)
undecidedSeq O 3 N = (undecidedCount O 3 N : ℝ) / (residueCard O : ℝ)^(3*N)
```

Record `two_le_residueCard`, `residueCard_pos`, `qR_pos`, `card_res`, and `card_coeff` once in the
file header.  Obtain a uniformizer locally with
`IsDiscreteValuationRing.exists_irreducible O`; do not add a uniformizer to the theorem
signature.  This is the convention used by all landed nodes.

### U10.01 — cubic structure — PROVED

U8 §4 is exactly `cubic_trichotomy` (`H97r1.lean:187`): a coefficient vector over a field has
a simple root, no root, or equals `cubeCoeff γ`.  Its proof is characteristic-free: if a root
`ρ` is multiple, the third root `-c₂-2ρ` is either distinct and simple, or equal to `ρ`, in
which case coefficient identities give `cubeCoeff ρ`.  `cubeCoeff_injective` supplies the
unique centre, including characteristic `3`.

Lift the simple residue root using `exists_cubic_root`; lift a triple-root centre using
`IsLocalRing.residue_surjective`.  The public result is `cubic_structure`
(`H97r1.lean:343`).  The three branches are exactly those consumed later; no five-type
enumeration is needed.

### U10.02 — recentring and E/L/R — PROVED

Use `shiftVec` and the identities `monicPoly_shiftVec`, `typeOf_shiftVec`,
`shiftVec_shiftVec_neg`, `dvd_shiftVec_sub`, and `shiftVec_mem_iff` from `H97r1`.
`typeOf_shiftVec` is the U8 translation step and is proved from the landed P5 theorem
`typeOf_shift` (`Density/TypeOfInvariance.lean:156`).

At a triple residual root all three shifted coefficients are divisible by `π`.  Split in the
U8 order:

* E: `typeOf_ram3_of_val_one` (`H97r2.lean:70`);
* L: `typeOf_linRam_of_val_one` (`H97r2.lean:149`), whose shifted centre is constructed by
  `exists_root_of_val_one` and whose only analytic input is landed
  `strongHensel`/`strongHensel_addVal` (`StrongHensel.lean:340,351`);
* R: `typeOf_ram3_of_val_two` (`H97r2.lean:272`).

Wrap each certificate with `decidedAt_of_shift_cert`: because it reads only divisibility modulo
`π³`, any level-`M+3` lift has the same verdict.  No division by `2` or `3` occurs.

### U10.03 — legal extraction and descent — PROVED

`legal_of_undecided_triple` negates the three decision certificates.  The remaining conjunction
is exactly

```lean
π^3 ∣ shiftVec a γ 0 ∧ π^2 ∣ shiftVec a γ 1 ∧ π ∣ shiftVec a γ 2.
```

Choose the quotients `d₀,d₁,d₂`.  `typeOf_extract` proves type preservation from
`typeOf_cubic_scale`, which in turn invokes the landed `typeOf_scale`
(`TypeOfInvariance.lean:521`; `typeOf_scaleRoots` is at line 486).

For another lift congruent modulo `π^(M+3)`, `dvd_shiftVec_sub` preserves that congruence.
Cancel `π³`, `π²`, and `π` in the domain to obtain precisions `M`, `M+1`, and `M+2`.
Weakening all three to `M` gives the same `Coeff O 3 M` class via `proj_eq_iff_dvd`.
Contraposition against `DecidedAt` proves `undecided_of_extract`; package choice and legality as
`undecided_triple_step` (`H97r3.lean:201,253`).

### U10.04 — mixed-precision box — PROVED

Use the already fitting carrier

```lean
abbrev MBox O M := Res O M × Res O (M+1) × Res O (M+2)
```

and `mtrunc : MBox O M →+ Coeff O 3 M`.  Prove surjectivity coordinatewise with
`resFactor_surjective`.  Then:

```lean
card_mbox M : Nat.card (MBox O M) = q^(3*M+3)
card_preimage_mtrunc M S :
  Nat.card (mtrunc M ⁻¹' S) * Nat.card (Coeff O 3 M)
    = Nat.card S * Nat.card (MBox O M)
```

The second statement uses `card_preimage_of_surjective` at `S` and `Set.univ`, exactly like
`card_preimage_coeffFactor`.  Cancellation by positive `q^(3M)` gives fibre multiplier `q³`.
`mkBox`, `mtrunc_mkBox`, and `dvd_of_mkBox_eq` are the record constructor and its three
congruence projections.

### U10.05 — sharp triple count — PROVED

For every element of
`undecidedSet O 3 (M+3) ∩ tripleSet (M+3)`, use `resSect` to choose the centre solely from its
residue class, and U10.03 to choose an extraction `d`.  Map it into

```lean
ResidueField O × (mtrunc M ⁻¹' undecidedSet O 3 M).
```

If two records agree, `dvd_of_mkBox_eq` gives precisions `(M,M+1,M+2)`.  Multiply by the extracted
powers `(π³,π²,π)` to recover congruence modulo `π^(M+3)` in each shifted coefficient;
apply `dvd_shiftVec_sub` at `-γ`, simplify by `shiftVec_shiftVec_neg`, and use
`proj_eq_iff_dvd`.  This proves injectivity.

Now `Nat.card_le_card_of_injective`, `Nat.card_prod`, `Nat.card (ResidueField O) = q`, and
U10.04 give

```lean
card_undecidedTriple_sharp hπ M :
  Nat.card (undecidedSet O 3 (M+3) ∩ tripleSet (M+3))
    ≤ q^4 * undecidedCount O 3 M.
```

This is U8's `q⁴ C_M`, hence the normalized `q⁻⁵`; the uniform-precision box must not be
substituted.

### U10.06 — lossless peel — PROVED

Define `peel a r` as in `H97r1.lean:114`; `cubic_peel` is the factorization
`monicPoly a = (X-C r) * monicPoly (peel a r)` at a root.

For `a' ≡ a mod π^N`, `N ≥ 1`, and a unit-derivative root `r`,
`exists_root_congr` produces `r'` with the **same** precision `π^N ∣ r'-r`.
`peel_congr` then proves the two quadratic cofactors congruent modulo `π^N`.
Together with `typeOf_linear_mul`, this yields `decidedAt_of_peel_decided`
(`H97r4.lean:107`): a decided cofactor would decide the cubic.  Contraposition says an
undecided cubic in the peel branch has an actually undecided quadratic cofactor.

### U10.07 — sharp peel count — PROVED

Choose `(a,r)` for each element of the peel intersection and map it to

```lean
Res O N × (undecidedSet O 2 N : Set (Coeff O 2 N)).
```

Equal records give congruence of `r` and both cofactor coefficients.  Reconstruct `a₂,a₁,a₀`
using the polynomial identities in U8 (the constant identity is exported as `peel_const`), then
use `proj_eq_iff_dvd`.  Thus the map is injective.  `card_res` and the exact quadratic theorem

```lean
undecidedCount_two_eq N : undecidedCount O 2 N = residueCard O ^ N
```

(`ChapG/G36.lean:43`) give `q^N · q^N = q^(2N)`.  The public result is
`card_undecidedPeel_le` (`H97r4.lean:125`).

### U10.08 — exhaustive actual-set dichotomy — PROVED

Take a lift of an actual undecided class using `proj_surjective`, and apply `cubic_structure`.
The simple-root case lies in `peelBranch`; the cube case lies in `tripleSet`.  In the rootless
case, `inert3_decided` decides the level-1 class as `c3inert`; lift it to level `N` with
`preimage_decidedSet_subset`, contradicting `UndecidedAt`.  This is
`undecidedSet_subset_sharp` (`H97r4.lean:219`).

This is the decisive H-1 honesty bridge: it is a theorem about `undecidedSet`, not a statement
about the conservative arithmetic function `hex3U`.

### U10.09 — recurrence — PROVED

Use `Set.ncard_le_ncard` on U10.08 and `Set.ncard_union_le`; rewrite subtype cards with
`Nat.card_coe_set_eq` and `undecidedCount`.  Apply `Nat.add_le_add` to U10.07 and U10.05.  The
result is exactly `undecidedCount_three_recursion`.

Dividing by `card_coeff 3 (M+3) = q^(3(M+3))` gives U8's real recurrence

```text
undecidedSeq O 3 (M+3)
  ≤ q^(-(M+3)) + q^(-5) * undecidedSeq O 3 M.
```

There is no separately named real-valued theorem in the present tree; do not cite the
nonexistent name `undecidedSeq_three_recursion`.  The natural-number statement is the stable
public API.

### U10.10 — sufficient rate `(1,0,3)` — PROVED

First prove `undecidedCount_le_card` from subtype inclusion into `Coeff`.  Strong-induct on `M`
to show

```lean
undecidedCount O 3 M * q^M ≤ q^(3*M+3).
```

For `M<3`, use the trivial count and exponent monotonicity.  For `M=K+3`, multiply U10.09 by
`q^(K+3)`, use the induction hypothesis at `K`, and close with `1+q ≤ q³`, whose only input is
`two_le_residueCard`.

For `M≥3`, cancel `q³` to obtain the `q^(M-3)` denominator; for `M<3`, natural subtraction
makes the right side `1`, so the trivial proportion bound suffices.  This is `rate_three`
(`H97b.lean:136`) with constants `(1,0,3)`.  It is enough for `InductionPackage 3` and for
drainage, even though it is not H.97's literal tuple.

### U10.11 — convergence and `DrainageAt 3` — PROVED

From the master bound obtain

```lean
undecidedSeq O 3 N ≤ q^3 * (q⁻¹)^N.
```

The right side tends to zero because `1 < q`; squeeze with nonnegativity of `undecidedSeq`.
This is `undecidedSeq_three_tendsto_zero` (`H97b.lean:184`).  Then use exactly

```lean
drainage_of_undecided_comp (φ := id)
  tendsto_id undecidedSeq_three_tendsto_zero σ
```

to get `drainage_three σ`, and introduce the bundle arguments and `σ` to obtain
`drainageAt_three`.

This formalizes the cylinder-count conclusion of U8 §9.  It does not assert a Haar-measure
identity.

### U10.12 — exact level-1 count for `(1,1,0)` — BLUEPRINT

Required signature (elaborated in the scratch file):

```lean
∀ O [bundle], undecidedCount O 3 1 ≤ residueCard O ^ 2.
```

The U8 recurrence does not imply this base case.  The fixed proof is a residue-field count.
Use U10.08 at `N=1` and refine its peel record.  By
`undecidedSet_eq_tangSet` at quadratic level `1`, an undecided cofactor reduces to
`(X-s)²`.  The chosen cubic root `r` is simple, so `r̄ ≠ s`; otherwise the derivative of
`(X-r) (X-s)²` at `r` would vanish.  Hence the peel part injects into
`{(r,s) : ResidueField O × ResidueField O // r ≠ s}`, of cardinal `q(q-1)`.

The triple part injects into `ResidueField O` through its unique centre
(`cubeCoeff_injective`), hence has card at most `q`.  The two branches are disjoint because one
has a simple root and the other is a cube.  Thus

```text
C₁ ≤ q(q-1) + q = q².
```

Lean implementation notes: formulate the off-diagonal type as a subtype of the product; count
its complement (the diagonal is equivalent to `ResidueField O`) using `Nat.card_congr` and
`Fintype.card_subtype_compl`, or prove the subtraction-free identity
`card offDiag + q = q²`.  Reconstruction uses the same `peel_const` identities as U10.07.
This is a finite-field bookkeeping node, not new p-adic mathematics.

### U10.13 — level-2 base bound for `(1,1,0)` — BLUEPRINT

Required signature:

```lean
∀ O [bundle], undecidedCount O 3 2 ≤ 2 * residueCard O ^ 4.
```

U10.07 at `N=2` contributes `q⁴`.  For the triple part, identify `tripleSet O 2` with the
preimage under `coeffFactor 3 (1≤2)` of the `q` level-1 cube classes.  Unique centres are again
`cubeCoeff_injective`; `card_preimage_coeffFactor` says each level-1 coefficient class has
`q³` refinements at level `2`.  Therefore the entire triple set has card `q·q³=q⁴`, and its
undecided intersection has no larger card.  U10.08 and the union bound yield `C₂≤2q⁴`.

This node should export the triple-set preimage equality separately if rewriting the existential
definition becomes longer than the count itself.

### U10.14 — exact natural-number master bound — BLUEPRINT

Prove by strong induction:

```lean
theorem undecidedCount_three_le_linear (N : ℕ) (hN : 1 ≤ N) :
  undecidedCount O 3 N ≤ N * residueCard O ^ (2*N)
```

Use U10.12 and U10.13 at `N=1,2`.  At `N=3`, U10.09 with `M=0` plus
`undecidedCount_le_card 3 0` gives
`C₃ ≤ q⁶ + q⁴ ≤ 2q⁶ ≤ 3q⁶`.

For `N=M+3` with `M≥1`, insert the induction hypothesis into U10.09:

```text
C_(M+3) ≤ q^(2M+6) + q⁴ M q^(2M)
          ≤ q^(2M+6) + M q^(2M+6)
          ≤ (M+3) q^(2(M+3)).
```

The middle inequality uses `1 ≤ q²`; keeping the proof in `ℕ` avoids division and inverse
normalization entirely.

### U10.15 — H.97's exact `hrate` — BLUEPRINT

Unfold `undecidedSeq` and `Induction.RateSpecies`; simplify `Nat.sub_zero`, `pow_one`, and
`one_mul`.  Cast U10.14 to `ℝ`, rewrite
`q^(3N) = q^(2N) * q^N`, and divide by positive powers using `qpow_pos`.  This yields

```lean
undecidedSeq O 3 N ≤ (N : ℝ) * ((residueCard O : ℝ) ^ N)⁻¹
```

for `N≥1`, exactly the H.97 use-site hypothesis.  Quantify `O` outside the proof to obtain the
verbatim `hrate` from §1.1.  The scratch alias `U10HRate110` confirms that this type elaborates
and that `package_three_of_rate hrate` accepts it.

### U10.16 — package and drainage bookkeeping — PROVED

There are two supported endpoints:

* **Present shortest path:** use `package_three : InductionPackage 3` and
  `drainageAt_three : DrainageAt 3`, both already supplied by U10.10–11.
* **Historical H.97 path:** U10.15 gives
  `package_three_of_rate hrate : InductionPackage 3`.  Once an all-degree
  `hp : ∀ n, InductionPackage n` is available, `drainage_of_package hp 3` gives
  `DrainageAt 3`.  Before that global assembly, the degree-3 limit must use U10.11's direct
  `drainage_of_undecided_comp` chain.

Do not manufacture `hp` from its degree-3 component, and do not claim that H.98's public theorem
has a single-degree signature.

### U10.17 — literal Haar-null theorem — OPEN (non-capstone)

U8's sets `E_N ⊆ O³`, their measurability, equal-cylinder measure formula, continuity from
above, and the identity of `⋂ E_N` with the infinite undecided locus cannot presently be stated
using a landed project-specific measure carrier.  The exact missing package is:

1. a normalized additive Haar probability measure instance on the complete DVR `O` (or an
   explicit measure parameter with normalization);
2. measurability of coefficient reduction cylinders and the formula
   `μ (proj_N ⁻¹' S) = Nat.card S / q^(3N)`;
3. a coefficient-space definition of the infinite undecided locus and its identification with
   the decreasing intersection of those cylinders.

This is a genuine formalization gap, already acknowledged in the module documentation quoted in
§0.  It is **not** a dependency of `UndecidedVanishes`, `DrainageAt 3`, or the capstone.

## 5. Signature elaboration check

`leanfinal/scratch/U10_sig_check.lean` contains sorry-free `example` forms for all landed public
interfaces and `True`-body signature checks for the extra `(1,1,0)` base-count/master-bound
targets.  It also checks the H.98 quantifier shape explicitly.

Command run from `leanfinal/`:

```text
$ lake env lean scratch/U10_sig_check.lean
```

**Result:** exit status `0`; no stdout/stderr diagnostics.

## 6. Final disposition

* HYP.08's actual-set cubic recurrence: **PROVED** by U8 and already landed as
  `undecidedCount_three_recursion`.
* HYP.09 / `DrainageAt 3`: **PROVED** and already landed as `drainageAt_three`.
* H.97's exact historical `hrate (1,1,0)`: **BLUEPRINT**, with the precise extra work isolated
  to U10.12–U10.15; it is not required to recover `DrainageAt 3` in the current tree.
* Any claim equating `undecidedCount` to, or bounding it through, `hex3U`: **not used and not
  asserted**.
* Literal Haar-nullness of the infinite undecided locus: **OPEN carrier**, explicitly outside
  the formal capstone target.
