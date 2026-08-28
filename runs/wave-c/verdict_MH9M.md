# VERDICT — UNIT MH9M, 2026-08-28

## Overall

**MATH PROVED; LEAN TRANSCRIPTION REMAINS.**  The above-support mixed read law is proved
coefficientwise in landed vocabulary; it discharges the exact
`C133mh5.LemmaSStatement`; Lemma S plus the landed perturbation, lift, and limit nodes
assembles the exact `C133mh14.TheoremAStatement`.  No `.lean` or leanspec file was edited.
The dated proof and the Lean-ready node list are appended to
`docs/in-progress/HENSEL_ENGINE_2026-08-26.md` under `[MH9M 2026-08-28]`.

There is no identified mathematical gap.  Four named issues remain for the later Lean
unit: private MH.3 pricing helpers, limit-monic packaging, the constant-factor branches,
and universal-pin packaging.  None requires weakening either signed statement.

## 1. Above-line mixed read law — PROVED

Define the bounded landed-vocabulary line polynomial

```text
dvLinePoly(F,H₀,hpin,u,ℓ,j₀,M,A,f)
 := ∑ t ∈ range A,
      C (F.twistRead H₀ hpin (M-t*u)
           (dev F.key f (j₀+t*ℓ))) * X^t.
```

For monic positive `p`, `IsDvPure F p u ℓ`, `D′ ∣ p.natDegree`, left pin `Mp`,
`P=R(p)`, `b=P.natDegree`, and `z` in the degree window
`z.natDegree < ℓ*(A*D′)`, if

```text
j₀ < ℓ,  0 < A,  u*(A-1) ≤ M,
((ℓ*M+u*j₀ : ℕ) : ℕ∞) ≤ dvSupp F z u ℓ,
```

then

```text
dvLinePoly ... j₀ (Mp+M) (A+b) (p*z)
  = P * dvLinePoly ... j₀ M A z.
```

Exact landed dependencies:

* pure endpoints and lattice: `dvSideMin_eq_zero_of_isDvPure`,
  `natDegree_div_eq_of_isDvPure`, `dvOnSide_modEq`;
* pin normalization: `C133mh4.dvHgt_dvSideMin_eq_mul_dvSideDeg_of_isDvPure` and
  `natDegree_dvResPoly`;
* product development: `dev_mul_conv_split`;
* common-floor linearity/vanishing: `twistRead_add_of_le`,
  `twistRead_finsetSum_of_le`, `twistRead_eq_zero_of_lt`;
* digit multiplication: `C133mh3.m1TwistProductLaw`, whose shape is
  `C133mh1.M1TwistProductLawStatement`;
* carry arithmetic: `C133mh1.twistExp_add_carry`;
* support multiplication: `C133mh3.dvSupp_mul`.

The proof splits `W(z)>d` (both requested lines vanish) from `W(z)=d`.  In the equality
case `dev_mul_conv_split` is read at `J=j₀+nℓ`, `K=Mp+M-nu`.  Strict pricing kills the
one-key carry diagonal and every main pair not simultaneously on the two complementary
grade lines.  Surviving indices are exactly `tℓ` and `j₀+sℓ`, `t+s=n`.  Termwise the raw
read carries `η^δ`, where
`q(kp)+q(kz)+δ=q(kp+kz)`.  Thus the inverse twists cancel it exactly and the normalized
law has `τ=1`.  Only `e₁=1` forces `δ=0`; the generic proof permits both branches.

## 2. Exact `LemmaSStatement` — PROVED

This discharges, without strengthening, the definition at
`C133mh5.lean:830`.

Let `G=R(p₁)`, `H=R(p₂)`, `a=deg G`, `b=deg H`.  The landed pure endpoint formulas give

```text
deg p₁=ℓ*a*D′, M₁=u*a, w₁=ℓ*u*a,
deg p₂=ℓ*b*D′, M₂=u*b, w₂=ℓ*u*b.
```

Choose the unique `j₀<ℓ` representing `c mod ℓ` under multiplication by `u`, and write

```text
c-w₂=ℓ*MU+u*j₀,  c-w₁=ℓ*MV+u*j₀.
```

The fullness check is rigorous: from `c-w₂≥w₁=ℓua`,

```text
ℓ*(MU-u*(a-1)) ≥ u*(ℓ-j₀) ≥ u > ℓ*(D′h),
```

so `D′h+u*deg Ubar<MU`; similarly for `Vbar`.

Consumed exact signatures:

* `C133mh5.exists_stageField_bezout_degree_lt` gives
  `Ebar=H*Ubar+G*Vbar` with the two degree windows;
* `C133mh5.natDegree_dvWindowLift_lt'` gives `deg U<deg p₁`, `deg V<deg p₂`;
* `C133mh5.le_dvSupp_dvWindowLift` gives the two split support floors;
* `C133mh5.twistRead_dvWindowLift` gives the prescribed line reads;
* the proved mixed read law gives `read_c(p₂U)=H*Ubar` and
  `read_c(p₁V)=G*Vbar`;
* `C133mh5.le_dvSupp_succ_of_lineReads_eq_zero` gives the final `c+1` contraction.

These are exactly the five conclusion conjuncts of `LemmaSStatement`.

## 3. Exact `TheoremAStatement` — PROVED

The target is the following landed definition (`C133mh14.lean:264`), quoted without
weakening:

```lean
def TheoremAStatement (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : Prop :=
  ∀ (π : O) (F : KeyFrame O π), Irreducible π → 0 < F.h →
  ∀ (H₀ : ℕ) (hpin : F.Pin H₀),
  ∀ u ℓ : ℕ, 0 < ℓ → Nat.Coprime u ℓ → ℓ * ((F.e₁ * F.f₁) * F.h) < u →
  ∀ g : Polynomial O, g.Monic → 0 < g.natDegree → (F.e₁ * F.f₁) ∣ g.natDegree →
    IsDvPure F g u ℓ →
  ∀ (hne : (dvSideSet F g u ℓ).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)),
  ∀ G H : Polynomial (F.stageField H₀ hpin), G.Monic → H.Monic → IsCoprime G H →
    G.coeff 0 ≠ 0 → H.coeff 0 ≠ 0 →
    dvResPoly F H₀ hpin g u ℓ hne M₀ hp = G * H →
  ∃ g₁ g₂ : Polynomial O, g = g₁ * g₂ ∧ g₁.Monic ∧ g₂.Monic ∧
    g₁.natDegree = ℓ * (F.e₁ * F.f₁) * G.natDegree ∧
    g₂.natDegree = ℓ * (F.e₁ * F.f₁) * H.natDegree ∧
    IsDvPure F g₁ u ℓ ∧ IsDvPure F g₂ u ℓ ∧
    dvHgt F g₁ 0 = ((u * G.natDegree : ℕ) : ℕ∞) ∧
    dvHgt F g₂ 0 = ((u * H.natDegree : ℕ) : ℕ∞) ∧
    (∀ (hne₁ : (dvSideSet F g₁ u ℓ).Nonempty) (M₁ : ℕ)
      (hp₁ : dvHgt F g₁ (dvSideMin F g₁ u ℓ hne₁) = (M₁ : ℕ∞)),
      dvResPoly F H₀ hpin g₁ u ℓ hne₁ M₁ hp₁ = G) ∧
    (∀ (hne₂ : (dvSideSet F g₂ u ℓ).Nonempty) (M₂ : ℕ)
      (hp₂ : dvHgt F g₂ (dvSideMin F g₂ u ℓ hne₂) = (M₂ : ℕ∞)),
      dvResPoly F H₀ hpin g₂ u ℓ hne₂ M₂ hp₂ = H)
```

Assembly, clause by clause:

1. For positive `deg G,deg H`, initialize with `C133mh5.dvSideLift`; its exact clause
   lemmas give monicity, degrees, purity, weights/heights, and residuals.
2. Equal initial support-line reads and
   `C133mh5.le_dvSupp_succ_of_lineReads_eq_zero` give initial error weight `w+1`.
3. Lemma S at `c=w+k+1`, followed by `C133mh0.dv_pure_add_of_lt`, preserves all factor
   invariants.  The quadratic correction has weight at least `2c-w≥c+1`, so the error
   contracts one grade.
4. Apply the exact `C133mh8.exists_dvGradedLimit` signature to the two fixed degree
   windows.  Its support-tail conclusion plus
   `C133mh8.gaussVal_of_shifted_dvSupp`, `gaussVal_le_addVal_coeff`, and
   `addVal_eq_top_iff` proves the limits monic of the exact fixed degrees.
5. Apply `C133mh0.dv_pure_add_of_lt` once more to a sufficiently late iterate to transfer
   purity, height, and exact residual to each limit.
6. The approximation errors and product-tail errors have arbitrarily large support.
   `C133mh8.gaussVal_of_shifted_dvSupp` and `gaussVal_eq_top_iff` force
   `g=g₁∞*g₂∞` exactly.
7. If `deg G=0` or `deg H=0`, monicity makes that factor `1`; take `(1,g)` or `(g,1)`.
   This is required because `TheoremAStatement` permits constant factors while the landed
   `dvSideLift_*` clauses assume positive residual degree.

Thus every displayed conclusion conjunct is obtained.  The theorem can be passed directly
to `C133mh14.blockFrontier_of_context_of_theoremA`; no adapter or weaker form is needed.

## 4. Lean transcription node list — OPEN, precisely scoped

Required new public nodes:

1. `dvLinePoly` and its coefficient lemma.
2. `dvLinePoly_dvWindowLift`.
3. `dvLinePoly_mul_of_isDvPure` (AMR).
4. `lemmaS : C133mh5.LemmaSStatement O`.
5. `dvSupp_sub_succ_of_same_residual`.
6. `monic_of_dvGradedLimit`.
7. `eq_zero_of_forall_dvSupp`.
8. `isDvPure_one`, `dvHgt_one_zero`, `dvResPoly_one`.
9. `theoremA : C133mh14.TheoremAStatement O`.

Named opens:

* **OPEN-MH9-PRIVATE-PRICING:** `C133mh3.carry_term_floor`, `read_kill`, and its residual
  coefficient helpers are private.  Their arguments must be copied locally or promoted.
* **OPEN-MH9-LIMIT-MONIC:** `C133mh8.exists_dvGradedLimit` returns a degree window and
  tail bound, not monicity; node 6 packages the proved separatedness argument.
* **OPEN-MH9-UNIT-BRANCH:** positive-degree hypotheses on `C133mh5.dvSideLift_*` do not
  cover constant `G/H`; node 8 and the explicit branches do.
* **OPEN-MH9-UNIVERSAL-PIN:** `C133mh0.dv_pure_add_of_lt` returns one witness/pin while
  `TheoremAStatement` quantifies over all; proof irrelevance and uniqueness of the finite
  height pin must be packaged.

Classification: all four are **TRANSCRIPTION OPEN**, not `GAP` or `BLOCKED-BECAUSE`.

## 5. Numeric certificate — PROVED / ALL PASS

`verification/dv_hensel_cert.py` was extended with Part 3b and run with `python3`.

Exact MH9M counts:

* 356 Part-3b checks;
* 16 above-line grades: eight in the original `e₁=1` `Z₂/F₄` frame and eight in the
  live-carry `(e₁,f₁,h,u,ℓ)=(2,2,1,5,1)` frame;
* 88 surviving term checks in the `δ=0` branch;
* 8 surviving term checks in the `δ=1` branch;
* both the raw `η^δ` formula and twist-normalized `τ=1` formula checked;
* strict-above zero-read branch checked at every grade.

Full script result: **3,188 checks, 0 FAILS, ALL PASS**.

## Rule audit

* No git commit.
* No landed `.lean` or leanspec edit.
* No bare `lake build`.
* Signed `LemmaSStatement` and `TheoremAStatement` were not weakened.
