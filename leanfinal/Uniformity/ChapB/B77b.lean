/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B20
import Uniformity.ChapB.B22
import Uniformity.ChapB.B24
import Uniformity.ChapB.B25
import Uniformity.ChapB.B29
import Uniformity.ChapB.B77a

/-!
# Uniformity.ChapB.B77b — level stability, the residual half

**Chapter B, NODE B.77** (`blueprint/CHAP-B_leaf_layer.md` §9), ENV-A′, **part (b) of the
mandated 2-way split** (step 5 of the node's proof; `B77a.lean` carries steps 1–4,
`suppVal_congr` and `sideSet_congr`).  One signed declaration:

* `resPoly_congr` — for every `H₀ < N`, the residual polynomial of the `(u,ℓ)`-side is a
  function of the level-`N` congruence class of `f`:
  `resPoly π φ f' u ℓ h' H₀ = resPoly π φ f u ℓ h H₀`, with `h'` the nonemptiness witness
  obtained from `h` by rewriting along B77a's `sideSet_congr` — exactly as the blueprint (and
  the frozen stub **B.77c**) writes it.  Separability, degree, constant term and the residual
  factorization therefore transport as well, being properties of this polynomial.

## `H₀ < N` is the whole hypothesis, and it is convention-free

Two `H₀`-pinning conventions coexist upstream — B.28/B.30 pin `H₀` at the side's **left
endpoint** `sideMin`, while B.63/B.65/B.73/B.74 pin it at **abscissa 0** — and they disagree on
an interior side of a multi-slope polygon.  This node assumes **neither**: it transports the
polynomial named by `H₀` for *every* `H₀ < N`, junk or not, so both conventions' consumers
compose with it unchanged.  The convention seam is a §8-owned repair (defect notice D-§9.1,
§14 item 13) and is not touched here.

`H₀ < N` is also exactly the guard that the unsound reader of `HE-T-CAP` violates: the read
heights are `H₀ - u·k ≤ H₀ < N`, all strictly inside the window, so every lift of the level-`N`
class carries the same digits at all of them.

## The digit lemma

The one place §9 touches digits directly (`digAt_congr`, private): for `x y : O` with
`π ^ N ∣ x - y` and `k < N`, `digAt π k x = digAt π k y`.  On the divisible branch write
`y = x + -(x - y)`; B.22's `digAt_add` splits the digit, and B.22's `digAt_eq_zero_iff` kills
the correction term because `π ^ (k+1) ∣ π ^ N ∣ x - y` — this is where `k < N`, and not merely
`k ≤ N`, is consumed.  On the non-divisible branch `π ^ k ∤ x` forces `π ^ k ∤ y` (else
`x = y + (x - y)` would be divisible) and both digits are the junk value `0`.  Lifting it
coefficientwise through B.24's `digPoly_coeff` gives `digPoly_congr`, and pushing that through
the quotient map gives `resMk_congr` (B.25).

DEPENDS: B.10 (`dev_congr`) · B.20 (`sideMin`, `sideMax`, `sideDeg`) · B.21/B.22 (`digAt`,
`digAt_add`, `digAt_eq_zero_iff`) · B.23/B.24 (`digPoly`, `digPoly_coeff`) · B.25 (`resMk`) ·
B.28 (`resCoeff`) · B.29 (`resPoly`) · B.75 (`Visible`) · B.77a (`sideSet_congr`) · mathlib
`Finset.sum_congr`, `Polynomial.ext`, `pow_dvd_pow`.

**PROOF (the node's step 5).**

1. **The side's combinatorics transport.**  B77a's `sideSet_congr` makes the two `Finset`s
   equal, and `Finset.min'`/`Finset.max'` depend on the set alone (the nonemptiness argument is
   a proof, hence irrelevant): `min'_congr`/`max'_congr` are one `subst` each.  Hence
   `sideMin_congr`, `sideMax_congr`, `sideDeg_congr` — so the two `resPoly` sums run over the
   *same* range `Finset.range (sideDeg + 1)`.
2. **Each residual coefficient transports.**  B.28 unfolds `resCoeff π φ f u ℓ h H₀ k` to
   `resMk π φ (H₀ - u*k) (dev φ f (sideMin φ f u ℓ h + ℓ*k))`.  The `sideMin`s agree by step 1,
   the read height satisfies `H₀ - u*k ≤ H₀ < N` (`Nat.sub_le`), and B.10's `dev_congr` carries
   the level-`N` congruence from `f` to every development coefficient; `resMk_congr` then
   equates the two reductions.
3. **The polynomials agree termwise** (`Finset.sum_congr rfl`), which is `resPoly_congr'` — the
   private form taking an arbitrary witness `h'`.  The signed statement is that form applied to
   the blueprint's rewritten witness; proof irrelevance makes the application definitional.

**SOURCE.** `EFF.W12.27` verbatim ("All data the read consumes sit at heights `≤ N−1`, so every
lift of the window class shares them") — this file is that sentence for the residual read;
`EFF.HE3.67` (R8-1 clause 2, through B77a); `spec/EFF-HE3.md` XREF `GENHN-3(a)` (via B.76).

**TEETH.** `HE-T-CAP` (`EFF.HE3.54`, 17 + 43 members: the unsound reader's dropped digits are
exactly a violation of the `k < N` guard consumed in `digAt_congr`) → **Lean theorem** (this
file, with B77a); `HE-BND` (`EFF.HE3.55`, RE-SCOPED by R8-1) → executable regression, scored on
the aligned rows only.

ENVIRONMENT: ENV-A′ (ENV-A, with `hπ : Irreducible π` carried explicitly).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The digit lemma and its two liftings -/

/-- **The digit lemma** (the node's step 5, the only place §9 touches digits).  Strictly inside
the window a level-`N` congruence preserves every digit: `π ^ N ∣ x - y` and `k < N` give
`digAt π k x = digAt π k y`. -/
private theorem digAt_congr (hπ : Irreducible π) {N k : ℕ} (hk : k < N) {x y : O}
    (h : π ^ N ∣ x - y) : digAt π k x = digAt π k y := by
  classical
  have hsub : π ^ k ∣ x - y := (pow_dvd_pow π hk.le).trans h
  have hsub1 : π ^ (k + 1) ∣ x - y := (pow_dvd_pow π (Nat.succ_le_of_lt hk)).trans h
  by_cases hx : π ^ k ∣ x
  · have hneg : π ^ k ∣ -(x - y) := (dvd_neg).2 hsub
    have hz : digAt π k (-(x - y)) = 0 := (digAt_eq_zero_iff hπ hneg).2 ((dvd_neg).2 hsub1)
    have hyx : y = x + -(x - y) := by ring
    rw [hyx, digAt_add hπ hx hneg, hz, add_zero]
  · have hy : ¬ π ^ k ∣ y := by
      intro hy
      refine hx ?_
      have hxy : x = y + (x - y) := by ring
      rw [hxy]
      exact dvd_add hy hsub
    simp only [digAt, dif_neg hx, dif_neg hy]

/-- The digit lemma, coefficientwise: inside the window the digit polynomial only sees the
level-`N` class. -/
private theorem digPoly_congr (hπ : Irreducible π) {N k : ℕ} (hk : k < N) {a b : Polynomial O}
    (h : ∀ i, π ^ N ∣ (a - b).coeff i) : digPoly π k a = digPoly π k b := by
  refine Polynomial.ext fun i => ?_
  rw [digPoly_coeff hπ, digPoly_coeff hπ]
  refine digAt_congr hπ hk ?_
  simpa only [Polynomial.coeff_sub] using h i

/-- The digit lemma, pushed into the residual field. -/
private theorem resMk_congr (hπ : Irreducible π) {N k : ℕ} (hk : k < N) {φ a b : Polynomial O}
    (h : ∀ i, π ^ N ∣ (a - b).coeff i) : resMk π φ k a = resMk π φ k b := by
  rw [resMk, resMk, digPoly_congr hπ hk h]

/-! ### The side's endpoints depend on the side alone -/

/-- `Finset.min'` depends only on the set: the nonemptiness argument is a proof. -/
private theorem min'_congr {s t : Finset ℕ} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst hst; rfl

/-- `Finset.max'` depends only on the set: the nonemptiness argument is a proof. -/
private theorem max'_congr {s t : Finset ℕ} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by subst hst; rfl

/-- Step 4 of the node, the piece B77b consumes: `sideMin` transports along `sideSet_congr`. -/
private theorem sideMin_congr {φ f f' : Polynomial O} {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) :
    sideMin φ f' u ℓ h' = sideMin φ f u ℓ h :=
  min'_congr hset h' h

/-- Step 4 of the node, the piece B77b consumes: `sideMax` transports along `sideSet_congr`. -/
private theorem sideMax_congr {φ f f' : Polynomial O} {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) :
    sideMax φ f' u ℓ h' = sideMax φ f u ℓ h :=
  max'_congr hset h' h

/-- Step 4 of the node, the piece B77b consumes: `sideDeg` transports along `sideSet_congr`. -/
private theorem sideDeg_congr {φ f f' : Polynomial O} {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) :
    sideDeg φ f' u ℓ h' = sideDeg φ f u ℓ h := by
  rw [sideDeg, sideDeg, sideMin_congr hset h h', sideMax_congr hset h h']

/-! ### The residual coefficients, and the residual polynomial -/

/-- Every residual coefficient of the side is read strictly inside the window, hence transports:
the read height is `H₀ - u*k ≤ H₀ < N`. -/
private theorem resCoeff_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) {H₀ : ℕ} (hH₀ : H₀ < N) (k : ℕ) :
    resCoeff π φ f' u ℓ h' H₀ k = resCoeff π φ f u ℓ h H₀ k := by
  have hsym : ∀ i, π ^ N ∣ (f' - f).coeff i := by
    intro i
    have hi := hff' i
    rw [Polynomial.coeff_sub] at hi ⊢
    exact (dvd_sub_comm).1 hi
  rw [resCoeff, resCoeff, sideMin_congr hset h h']
  exact resMk_congr hπ (lt_of_le_of_lt (Nat.sub_le H₀ (u * k)) hH₀)
    (dev_congr hπ hφ hsym (sideMin φ f u ℓ h + ℓ * k))

/-- The signed statement with an arbitrary nonemptiness witness on the `f'` side; the signed
form below is this one applied to the blueprint's rewritten witness. -/
private theorem resPoly_congr' (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) {H₀ : ℕ} (hH₀ : H₀ < N) :
    resPoly π φ f' u ℓ h' H₀ = resPoly π φ f u ℓ h H₀ := by
  rw [resPoly, resPoly, sideDeg_congr hset h h']
  exact Finset.sum_congr rfl fun k _ => by
    rw [resCoeff_congr hπ hφ hff' hset h h' hH₀ k]

/-! ### The signed transport -/

/-- **B.77, clause `resPoly`.**  Inside the window the residual polynomial of the `(u,ℓ)`-side
is a function of the level-`N` congruence class of `f`: for every `H₀ < N`,

`resPoly π φ f' u ℓ h' H₀ = resPoly π φ f u ℓ h H₀`,

with `h'` obtained from `h` by rewriting along `sideSet_congr`.  Separability, the degree, the
constant term and the residual factorization all transport with it.  No convention on `H₀` is
assumed — see the module note. -/
theorem resPoly_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hdeg : f'.natDegree = f.natDegree)
    (hvis : Visible π φ f N) {u ℓ : ℕ} (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : H₀ < N) :
    resPoly π φ f' u ℓ (by rw [sideSet_congr hπ hφ hd hff' hdeg hvis]; exact h) H₀
      = resPoly π φ f u ℓ h H₀ :=
  resPoly_congr' hπ hφ hff' (sideSet_congr hπ hφ hd hff' hdeg hvis u ℓ) h _ hH₀

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.resPoly_congr
end AxCheck
