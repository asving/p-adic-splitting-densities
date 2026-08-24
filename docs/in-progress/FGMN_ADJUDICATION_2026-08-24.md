# U9 — `FGMNCalculus` adjudication (recorded amendment A-C.11)

Date: 2026-08-24  
Status: **DECIDED**  
Scope: U7 §9 Q1–Q7; exact replacement of the provisional `FGMNCalculus` body

## 1. Verdict

All seven questions are decided.

| question | decision |
|---|---|
| Q1 | The class is the calculus of the **next augmented valuation**. At repo depth `r`, `keyAt r` is the augmentation key, `(e',f',u')` is the next augmentation data, and `Rgr`, `Rres`, `KP`, `nuEquiv` mean `R_{r+1,β}`, `R_{r+1}`, `KP(μ_{r+1})`, and `∼_{μ_{r+1}}`. |
| Q2 | `Rgr β g` is the **degree-zero coefficient** of the polynomial-valued `R_{r+1,β}(g)`, transported to `W.fld r`. It is not evaluation at a letter. `Rgr_ne_zero` is restricted by `deg g < deg (keyAt r)`. |
| Q3 | A natural grade is a nonnegative grade of the preceding group, cleared by `e(μ_r)`. Thus every class grade is already in `Γ_r`; `PrevGrade` is redundant and is removed. |
| Q4 | Keep the class syntactically available at `r = 0`, because the level-general consumers quantify over the zero truncation. Do not add base-case law fields. The last-live-key laws remain fenced by `0 < r`. |
| Q5 | The Gauss theorem exists under the current pinned mathlib name `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`; `KP_irred` loses `OPEN-GAUSS`. |
| Q6 | The FGMN condition is **μ-divisibility**, not ordinary polynomial divisibility. The proof document actually proves the smaller `deg g < D₂` scope, where μ-freeness is automatic. C.100 and its iff companion must be re-signed to that degree scope and their ordinary `hfree` binder deleted. No opaque μ-divisibility field is added to A-C.11. |
| Q7 | C.90 needs the **full published Corollary 6.3 package**, not merely the residual-power equality. It remains `OPEN-LEVEL-GENERAL` and no fake class field is added. |

The orchestrator's standing decisions are preserved: `FGMNCalculus` is a hypothesis carrier,
`fgmn_calculus_exists` remains undeclared, and the faithfully typed laws below live in the class.

## 2. Fixed index and grade dictionary

The published chain is indexed by

> “For such a chain of augmented valuations `μ_i = [μ_{i−1}; (φ_i, ν_i)]`, `1 ≤ i ≤ r`, we write … `μ_r = μ`.”

(FGMN, published §3, display (4)). The paper then says:

> “The operators `R_{i,α}`, `R_i` are attached to the MacLane chain of `μ_i` obtained by truncation.”

(FGMN, published §3.4).

The consumer proof fixes the repo shift explicitly:

> “`μ₀ →(x, λ₁) μ₁ →(Φ′, λ₂) μ₂ →(Φ₂, λ₃) μ₃ = ν`.”

(`GENTOW2_PROOF_2026-08-09.md`, S2/S4 setting.) At the depth-two consumer,
`keyAt 1 = Φ′`, `keyAt 2 = Φ₂`, and `(e',f',u') = (e₃,f₃,u₃)`. Therefore the only
indexing which makes the recipe and the proof agree is:

```text
keyAt i        ↔ φ_{i+1}                       (1 ≤ i ≤ r)
keyAt r        ↔ φ_{r+1}, the last carried key
(e',f',u')     ↔ next augmentation data at φ_{r+1}
Rgr β g        ↔ coeff 0 of R_{r+1, β/e(μ_r)}(g)
Rres g         ↔ R_{r+1}(g)
KP g           ↔ g ∈ KP(μ_{r+1})
nuEquiv g h    ↔ g ∼_{μ_{r+1}} h
letterZ i      ↔ z_i transported into F_{r+1} ≃ W.fld r
ExactGrade β g ↔ μ_{r+1}(g) = β/e(μ_r)
AboveGrade β g ↔ μ_{r+1}(g) > β/e(μ_r)
```

This is the **next-augmentation convention**. In particular, the old class comment calling
`Rres` the residual of the “depth-`r` valuation” was off by one.

## 3. Q1 — index convention: DECIDED

Published Proposition 1.7(4) says:

> “The polynomial `φ` is a key polynomial for `μ′`.”

Here `μ′ = [μ; (φ,ν)]`. Published equation (11) says, for positive residual index,

> “`R_{r,α}(φ_r^s) = y^{⌊s/e_r⌋}`, `R_r(φ_r^s) = 1`.”

The recipe proof uses these with `μ₃`, `φ₃ = Φ₂`:

> “Eq (14) gives `R_{3,α}(Φ₂^{e₃f₃}) = y^{f₃}`.”

(`GENTOW2_PROOF`, GENTOW2-B proof.) Thus `Rres_keyAt` must mean
`R_{r+1}(φ_{r+1}) = 1`, not `R_r(φ_r) = 1` in repo indexing.

Consequences for the class:

- `Rgr`, `Rres`, `KP`, and `nuEquiv` all use the next augmented valuation `μ_{r+1}`.
- `Rres_recipe` and `KP_criterion` correctly use `keyAt r` and `(e',f',u')` unchanged.
- `KP_keyAt` is justified by Proposition 1.7(4).
- `Rres_keyAt` is justified by equation (11), with the repo-to-paper index shift made explicit.
- `letterZ i` is live for `1 ≤ i ≤ r`, since `z_i` is defined before the following augmentation and embeds into `F_{r+1}`.

No law in the diff retains the contradictory “depth-`r` residual” reading.

## 4. Q2 — scalar `Rgr`: DECIDED

Published Definition 3.13 does **not** define a scalar. It defines

> “`R_{r,α}(g) = Σ … y^j`”

as an element of `F_r[y]`. Published Corollary 4.9(1) then speaks coefficientwise:

> “The `j`-th coefficient of `R_{r,α}(g)` is non-zero if and only if `μ_{r−1}(a_{s_j}) = α_j`.”

The consumer proof supplies the specialization actually used:

> “`R_{3,β}(g) ∈ F₃ = K₂` — Def 3.16 at `i = 3`, single `j = 0` term.”

(`GENTOW2_PROOF`, S5.1, `(R-FGMN)`.) It also repeatedly calls the result a
“`y`-degree-0 scalar” for polynomials of degree below `m₃ = deg Φ₂`.

Hence:

```text
Rgr β g := (transported R_{r+1,β}(g)).coeff 0.
```

This selects candidate 3, the degree-zero residual in the next augmentation. It is neither
evaluation at `z_r` nor an assertion that every exact-grade residual polynomial is constant.
The previous `ScalarAt` proposal is unnecessary: the actual consumed source criterion is the
typeable inequality `g.natDegree < (keyAt r).natDegree`, so A-C.11 uses that inequality directly.

### 4.1 Law-by-law check under this meaning

| field | check |
|---|---|
| `Rgr_zero_of_above` | Published Lemma 3.14 says `R_{r+1,β}` vanishes on `P_β⁺`; its coefficient zero is therefore zero. |
| `Rgr_add` | Published Corollary 4.12(1) is a polynomial identity; applying `coeff 0` gives the scalar identity. The exact-grade sum hypothesis avoids asserting a nonzero-grade conclusion after cancellation. |
| `Rgr_mul` | Published Corollary 4.12(2) is a polynomial product identity. Constant coefficients multiply. Q3 makes its preceding-value-group premise automatic. |
| `Rgr_ne_zero` | Exact grade makes the polynomial residual nonzero. If `deg g < deg keyAt r`, the `φ_{r+1}`-expansion has only its `s = 0` term, and the grade lies in `Γ_r`, so Corollary 4.9(1) makes the zero coefficient nonzero. Exact grade alone would be false here; the degree fence is essential. |
| `Rres_mul` | Independent of the scalar convention; it is published Corollary 4.12(3). |
| `Rres_recipe` | Every `khat t` has degree below `keyAt r`; its graded residual is therefore exactly its degree-zero coefficient. Additivity, Corollary 4.12(2), and equation (11) give the displayed polynomial. |
| `Rres_exists` | Independent of `Rgr`. It is restricted to irreducible `ψ`: Theorem 5.7 constructs a key polynomial and Corollary 1.10 then supplies `O[x]`. U7's broader `O[x]` output for arbitrary monic `ψ` was not justified by the printed proof. |
| `KP_criterion` | Independent of the scalar convention. The nonzero constant hypothesis is retained because it is what forces `s(g)=0` in the Theorem 5.7 degree argument. |
| `KP_irred` | Independent; Q5 supplies the Lean Gauss leg. |
| `KP_keyAt` | Independent; Proposition 1.7(4). |
| `Rres_keyAt` | Independent; equation (11). |
| `nuEquiv_iff_Rres` | Independent; published Proposition 5.6(2)⇔(3), with both `KP` hypotheses. |
| `letterZ_ne_zero` | Independent; published §3.3 states `z_i ≠ 0` for positive live indices. |

## 5. Q3 — `PrevGrade`: DECIDED

Published Corollary 4.12(2) says:

> “If `β ∈ Γ_{r−1}`, then `R_{r,α+β}(gh) = R_{r,α}(g)R_{r,β}(h)`.”

After Q1's shift, the class uses `R_{r+1}` and the premise is `β ∈ Γ_r`. The consumer proof
uses precisely this clearing:

> “`β̂ = e(μ₂)β`”

and, for recipe slots,

> “`ν(k̂_t) = μ₂(k̂_t) = dv₂(k̂_t)/e(μ₂)`.”

(`GENTOW2_PROOF`, S5/S5.1.) Thus the natural argument to `ExactGrade` is by definition a
nonnegative element of `Γ_r` after clearing. There is no larger grade domain in this interface.

Decision: remove `PrevGrade` and remove its premise from `Rgr_mul`. The realization obligation is
to prove the clearing equivalence once; consumers do not carry a repetitive predicate which is
true by construction.

## 6. Q4 — `r = 0`: DECIDED

The paper explicitly permits the base valuation:

> “We agree that `μ₀ ∈ V_ind` by admitting empty chains of augmentations of length `r = 0`.”

(FGMN, published §3.) But equation (11) and Proposition 5.6 distinguish the base case. The proof
of Proposition 5.6 says:

> “`R_r(φ) = y` (for `r = 0`) and `R_r(φ) = 1` (for `r > 0`).”

The repo also has a structural reason not to put `0 < r` in the class: C.90 accepts
`I : ∀ i, (hi : i ≤ r) → FGMNCalculus (W.trunc i hi) …`, which includes `i = 0`.
A positivity field would make that consumer premise unconstructible and hence vacuous.

Decision:

- the carrier remains available at `r = 0`;
- no `depth_pos` field is added;
- no `keyAt_zero` or separate base residual law is added;
- `Rres_exists`, `KP_keyAt`, and `Rres_keyAt` retain `0 < r` fences;
- all live consumers at `r ≥ 1` obtain the source laws they need, while the zero truncation carries
  only the common interface.

This is the smaller class and does not silently choose a base-key convention.

## 7. Q5 — Gauss transport: DECIDED

Published Lemma 1.8 says:

> “Every `φ ∈ KP(μ)` is irreducible in `K_v[x]`.”

Published Corollary 1.10 says:

> “`KP(μ) ⊂ O[x]`.”

The pinned mathlib v4.31.0 theorem is present at
`Mathlib/RingTheory/Polynomial/GaussLemma.lean`:

```lean
Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map
```

Its checked type specializes in ENV-C1 to:

```lean
example {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
    (g : Polynomial O) (hg : g.Monic) :
    Irreducible g ↔ Irreducible (g.map (algebraMap O K)) :=
  hg.irreducible_iff_irreducible_map_fraction_map (K := K)
```

This exact probe is in `leanfinal/scratch/U9_class_check.lean` and compiles. Therefore
`KP_irred` is no longer `OPEN-GAUSS`. The future realization still owes the ordinary embedding
step from the paper's `K_v` to the fraction field dictionary; that is a realization transport,
not a missing Gauss lemma.

## 8. Q6 — C.100 divisibility: DECIDED

Published Proposition 1.7(2) says:

> “`μ(g) = μ′(g)` if and only if `φ ∤_μ g`.”

Published Proposition 1.9(1) repeats the same μ-divisibility criterion for root evaluation.
Neither statement uses ordinary polynomial divisibility.

The proof document's actual B′ scope is smaller than the current C.100 signature:

> “Two reads are in play on `Φ₂`-free elements `g` (`deg g < m₃ = deg Φ₂`) of exact grade.”

(`GENTOW2_PROOF`, S5.1.) Its later invocations likewise say `deg Q₀ < m₃` and use
μ-minimality/Proposition 1.9. The current C.100 binders

```lean
(hdeg : g.natDegree < e' * f' * T.D₂) (hfree : ¬ composedKey T ∣ g)
```

are therefore not the proved statement: ordinary `∣` cannot replace `∣_μ`, and the displayed
degree bound does not imply μ-freeness.

Decision and downstream cost:

```diff
- (hdeg : g.natDegree < e' * f' * T.D₂) (hfree : ¬ composedKey T ∣ g)
+ (hdeg : g.natDegree < T.D₂)
```

Apply that re-sign to both `gentow2_Bp` and `gentow2_Bp_unit_iff`. At this degree,
μ-freeness follows from μ-minimality of the key, so no `muDvd` carrier is required. The recipe
coefficients consumed by C.101 are already in this low-degree scope.

Named revisit trigger: if a consumer genuinely needs the interval
`T.D₂ ≤ deg g < e'f'T.D₂`, it must first supply a proof at that scope and A-C must then add a
realized `MuDvd` relation and replace `hfree` by `¬ I.MuDvd (composedKey T) g`. Ordinary
divisibility is never an admissible substitute.

## 9. Q7 — strength needed by C.90: DECIDED

Published Corollary 6.3 says, under its hypotheses:

> “For any `1 ≤ i ≤ r`, the Newton polygon `N_i(F)` is one-sided of slope `−ν_i`, we have `v(φ_i(θ)) = μ(φ_i)` and … `R_{i−1}(F) = (ψ_{i−1})^{ℓ_i}`.”

It concludes additionally:

> “In particular, `ℓ_i = e_i f_i ℓ_{i+1}` for all `1 ≤ i < r`.”

The GENTOW2 proof consumes all of this, not only the residual equality: its conclusion list has
the intermediate polygon, residual power, exact root values, and the length recurrence; its proof
says “Corollary 6.4 [published 6.3] applies” before extracting each of those clauses.

Decision: C.90(b) must expose the full package:

- per-level `N_i(F)` and one-sidedness/slope;
- side lengths `ℓ_i`;
- exact root evaluations `v(φ_i(θ))`;
- `F ∼_{μ_{i−1}} φ_i^{ℓ_i}` and the degree equality;
- `R_{i−1}(F) = ψ_{i−1}^{ℓ_i}`;
- `ℓ_i = e_i f_i ℓ_{i+1}`.

Cost: none of the polygon, root, valuation, or per-level residual-field carriers exists in
`DeepTower`. The law cannot be faithfully typed today. It remains `OPEN-LEVEL-GENERAL`, is dropped
from A-C.11, and must be added only after `FGMNChainRealization` carries those source objects and
their repo transports. A residual-only opaque predicate would not prove the consumer theorem.

## 10. Other source-tightening adopted in A-C.11

Published Theorem 5.7 constructs the desired `O[x]` polynomial through key-polynomialhood. Its
proof starts with a **monic irreducible** `ψ`, constructs `φ`, proves Lemma 5.2(2), and only then
Corollary 1.10 places the key polynomial in `O[x]`. Consequently `Rres_exists` now requires
`Irreducible ψ`. This is exactly the target used in GENTOW2 and avoids asserting an `O[x]` lifting
for arbitrary monic residual polynomials without a printed justification.

No other U7 law is broadened. Q3/Q9/Q10 and the graded-algebra evaluation isomorphisms remain
outside this class until their carriers exist.

## 11. A-C.11 — exact unified diff

This diff replaces only the provisional class body. It does **not** enact the separate C.100
re-sign recorded in §8.

```diff
--- a/leanspec/Leanspec/ChapC.lean
+++ b/leanspec/Leanspec/ChapC.lean
@@ -1320,58 +1320,59 @@
 /-- NODE C.92 — the MacLane-chain certificate interface ([cite:FGMN-chain], gate (b)). -/
 class FGMNCalculus {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
     (W : DeepTower F H₀ hpin r) (e' f' u' : ℕ) where
-  /-- the MacLane chain keys `Φ_1 … Φ_r` (`Φ_1 = F.key`); junk outside. -/
   keyAt : ℕ → Polynomial O
   keyAt_one : keyAt 1 = F.key
-  /-- `deg Φ_i = D_i` (chain-degree law; published §§5–6 chain conventions). -/
   keyAt_deg : ∀ i, 1 ≤ i → i ≤ r → (keyAt i).natDegree = W.Dcum i
-  /-- the exact-grade pin (`ν`-value data): the scope carrier of R3-2's fence — every graded
-  read below is conditioned on it (`digit` applied only in scope). -/
+
   ExactGrade : ℕ → Polynomial O → Prop
-  /-- the graded coefficient read `R_{r+1,β}` at cleared grade `β`, valued in the top residue
-  field (C.104's `(R-FGMN)`, the `ε₂`-normalized coordinate; published §4). -/
+  AboveGrade : ℕ → Polynomial O → Prop
+
   Rgr : ℕ → Polynomial O → W.fld r
-  /-- the residual operator `R_ν(·)` of the depth-`r` valuation, valued in `K_r[y]`
-  (published §§4–6). -/
   Rres : Polynomial O → Polynomial (W.fld r)
-  /-- `KP(ν)`-membership (key/prime polynomial for the depth-`r` MacLane valuation). -/
   KP : Polynomial O → Prop
-  /-- `ν`-equivalence `∼_ν`. -/
   nuEquiv : Polynomial O → Polynomial O → Prop
-  /-- the FGMN residue letters `z_i` (published Def 3.12-family `γ_i`-letters), in `K_r`. -/
   letterZ : ℕ → W.fld r
-  /-- [published **Cor 4.12(3)**; was Cor 4.7(3)] graded multiplicativity of the `R`-read. -/
-  Rgr_mul : ∀ β β' (g g' : Polynomial O), ExactGrade β g → ExactGrade β' g' →
-    ExactGrade (β + β') (g * g') ∧ Rgr (β + β') (g * g') = Rgr β g * Rgr β' g'
-  /-- [published **Cor 4.9(3)**; was Cor 4.4(4)] nonvanishing of the in-scope graded read
-  (the single-pin polygon leg C.100's `u(β) ≠ 0` consumes). -/
-  Rgr_ne_zero : ∀ β (g : Polynomial O), ExactGrade β g → g ≠ 0 → Rgr β g ≠ 0
-  /-- [published **Prop 5.6 + eq (11)**; was Prop 5.7 + eq (14), plus Def 1.8's
-  expansion-minimum and **Cor 4.12(1)**] the recipe expansion law: the residual of the
-  recipe key is the `y`-polynomial of the graded slot reads — the raw (B-law) sum. -/
+
+  Rgr_zero_of_above : ∀ β (g : Polynomial O),
+    AboveGrade β g → Rgr β g = 0
+  Rgr_add : ∀ β (g h : Polynomial O),
+    ExactGrade β g → ExactGrade β h → ExactGrade β (g + h) →
+      Rgr β (g + h) = Rgr β g + Rgr β h
+  Rgr_mul : ∀ β β' (g h : Polynomial O),
+    ExactGrade β g → ExactGrade β' h →
+      ExactGrade (β + β') (g * h) ∧
+      Rgr (β + β') (g * h) = Rgr β g * Rgr β' h
+  Rgr_ne_zero : ∀ β (g : Polynomial O),
+    ExactGrade β g → g.natDegree < (keyAt r).natDegree → g ≠ 0 → Rgr β g ≠ 0
+  Rres_mul : ∀ g h : Polynomial O,
+    Rres (g * h) = Rres g * Rres h
   Rres_recipe : ∀ (khat : ℕ → Polynomial O),
     (∀ t, t < f' → ExactGrade ((f' - t) * u') (khat t)) →
     (∀ t, t < f' → (khat t).natDegree < (keyAt r).natDegree) →
-    Rres ((keyAt r) ^ (e' * f') - ∑ t ∈ Finset.range f', khat t * (keyAt r) ^ (e' * t))
-      = Polynomial.X ^ f'
-        - ∑ t ∈ Finset.range f',
-            Polynomial.C (Rgr ((f' - t) * u') (khat t)) * Polynomial.X ^ t
-  /-- [published **Lemma 5.2(2)**; was Lemma 5.3(2)] the key-polynomial criterion at the
-  recipe degree (admissibility/degree forcing). -/
-  KP_criterion : ∀ (g : Polynomial O), g.Monic →
+    Rres ((keyAt r) ^ (e' * f') -
+        ∑ t ∈ Finset.range f', khat t * (keyAt r) ^ (e' * t)) =
+      Polynomial.X ^ f' -
+        ∑ t ∈ Finset.range f',
+          Polynomial.C (Rgr ((f' - t) * u') (khat t)) * Polynomial.X ^ t
+  Rres_exists : 0 < r → ∀ ψ : Polynomial (W.fld r),
+    ψ.Monic → Irreducible ψ → ψ.natDegree = f' → ψ.coeff 0 ≠ 0 →
+      ∃ g : Polynomial O,
+        g.Monic ∧
+        g.natDegree = e' * f' * (keyAt r).natDegree ∧
+        Rres g = ψ
+  KP_criterion : ∀ g : Polynomial O,
+    g.Monic →
     g.natDegree = e' * f' * (keyAt r).natDegree →
-    Irreducible (Rres g) → (Rres g).natDegree = f' → KP g
-  /-- [published **Lemma 1.8 + Cor 1.10**; were Lemma 1.11 + Cor 1.13] key polynomials are
-  irreducible (over `K_v[x]` in the source; monic + `KP(µ) ⊂ O[x]` transports it to `O[x]`
-  by Gauss — the transport recorded in the faithfulness entry). -/
-  KP_irred : ∀ (g : Polynomial O), KP g → g.Monic → Irreducible g
-  /-- [published **Thm 6.2**; was Thm 6.3 items (1)(2)(3), v3's (3) absorbed into (2)] the
-  chain key's own residual is trivial — the non-equivalence pivot C.103 reads. -/
-  Rres_keyAt : Rres (keyAt r) = 1
-  /-- [published **Prop 5.6**, the consumed equivalence] distinct residuals ⟹ not
-  `ν`-equivalent. -/
-  nuEquiv_ne_of_Rres : ∀ (g g' : Polynomial O), KP g → KP g' →
-    Rres g ≠ Rres g' → ¬ nuEquiv g g'
+    Irreducible (Rres g) →
+    (Rres g).natDegree = f' →
+    (Rres g).coeff 0 ≠ 0 →
+      KP g
+  KP_irred : ∀ g : Polynomial O, KP g → g.Monic → Irreducible g
+  KP_keyAt : 0 < r → KP (keyAt r)
+  Rres_keyAt : 0 < r → Rres (keyAt r) = 1
+  nuEquiv_iff_Rres : ∀ g h : Polynomial O,
+    KP g → KP h → (nuEquiv g h ↔ Rres g = Rres h)
+  letterZ_ne_zero : ∀ i, 1 ≤ i → i ≤ r → letterZ i ≠ 0
 
 /-! ### ⛔ C.92's EXISTENCE AXIOM IS **RETIRED** — DECISION A-C.6, option (1) (hypothesis-form)
```

## 12. Elaboration verification

The exact proposed class signature is transcribed in:

```text
leanfinal/scratch/U9_class_check.lean
```

That file imports landed `Uniformity.ChapC.C83`, recreates only the leanspec-side `KeyFrame.Pin`
abbreviation, declares the A-C.11 class, and includes the Q5 Gauss probe. Verification command:

```text
cd leanfinal
lake env lean scratch/U9_class_check.lean
```

Result on 2026-08-24: **exit 0, no output**.

`leanspec/` and `leanfinal/Uniformity/` were not modified.
