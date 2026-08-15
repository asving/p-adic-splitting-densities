/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B03
import Uniformity.ChapB.B17
import Uniformity.ChapB.B24
import Uniformity.ChapB.B29
import Uniformity.ChapB.B36

/-!
# Uniformity.ChapB.B30 — the residual polynomial has degree `d` and nonzero constant term

**Chapter B, NODE B.30** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §4, the order-1 residual
layer), ENV-A′.

*The residual polynomial has degree `d` and nonzero constant term.*  With the data of B.28 —
an order-1 key `φ`, a polynomial `f`, a slope `−u/ℓ` in lowest terms with `0 < ℓ`, a finite
cleared support value `suppVal φ f u ℓ ≠ ⊤`, a nonemptiness witness `h` for `sideSet φ f u ℓ`
and the left-endpoint height `H₀` (pinned by `npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)`):

* `resCoeff π φ f u ℓ h H₀ k = 0 ↔ ¬ OnSide φ f u ℓ (sideMin φ f u ℓ h + ℓ * k)` for `k ≤ d`;
* consequently `resCoeff … 0 ≠ 0` and `resCoeff … d ≠ 0` (both endpoints *are* on the side),
  hence `(resPoly π φ f u ℓ h H₀).natDegree = d` and `(resPoly π φ f u ℓ h H₀).coeff 0 ≠ 0`,
  where `d := sideDeg φ f u ℓ h`.

This is the pair of facts every consumer of B.29's `resPoly` needs, and the two that are
invariant under the `K^×`-rescaling B.29 deliberately does not normalize away.

DEPENDS: B.03 (`degree_dev_lt` — the development sits below the key's degree) · B.08
(`gaussVal`, through B.24) · B.11 (`npHgt`) · B.16 (`OnSide`, `sideSet`) · B.17
(`npHgt_ne_top_of_onSide`, `onSide_nat_eq` — the `ℕ∞`-to-`ℕ` conversions of steps 1–2) · B.20
(`sideMin`, `sideMax`, `sideDeg`, `onSide_of_mem_sideSet`, `sideMax_eq`) · B.24
(`digPoly_eq_zero_iff`) · B.25 (`resField`, `resMk`) · B.28 (`resCoeff`) · B.29 (`resPoly`) ·
B.36 (`resMk_eq_zero_iff` — **the slot lemma**, the forward dependency inside §5 that the
blueprint's DEPENDS block sanctions: B.36 needs only B.03/B.08/B.24/B.25, so the DAG stays
acyclic and the topological order is B.36 before B.30) · landed
`Uniformity.Hensel.coeff_sum_range_C_mul_X_pow` · mathlib
`Polynomial.natDegree_le_iff_coeff_eq_zero`, `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`,
`Finset.min'_mem`, `Finset.max'_mem`, `ENat.ne_top_iff_exists`.

**PROOF.**
1. *(private `side_line`, the line-versus-point inequality.)*  Write `j₀ := sideMin φ f u ℓ h`,
   `d := sideDeg φ f u ℓ h`, `j_k := j₀ + ℓ*k`.  Both endpoints are on the side
   (`Finset.min'_mem`, `Finset.max'_mem` through B.20's `onSide_of_mem_sideSet`), the right one
   at abscissa `sideMax = j₀ + ℓ*d` (B.20's `sideMax_eq`, where `hℓ`/`hcop`/`htop` are spent).
   B.17 makes the right endpoint's height a natural `Hd`, and B.17's `onSide_nat_eq` turns the
   two on-side equations into the `ℕ`-equation `ℓ*H₀ + u*j₀ = ℓ*Hd + u*(j₀ + ℓ*d)`; cancelling
   `u*j₀` and then `ℓ > 0` gives **`H₀ = Hd + u*d`**, hence `u*k ≤ u*d ≤ H₀` for `k ≤ d` — the
   truncated subtraction `H₀ - u*k` is therefore the honest line height, which is what makes
   the node true (see the minimum-hypothesis note).
2. Against `j_k` (which lies in `Finset.range (f.natDegree + 1)`, since `j_k ≤ sideMax` and
   `sideSet` is carved out of that range) the `inf` defining `suppVal` gives
   `ℓ*H₀ + u*j₀ ≤ ℓ • npHgt φ f j_k + u*j_k`.  On the branch `npHgt φ f j_k = ⊤` the point is
   off the side (B.17: an on-side height is finite when `suppVal ≠ ⊤`) and both sides of the
   node's iff are false.  On the finite branch `npHgt φ f j_k = (p : ℕ∞)` the inequality is the
   `ℕ`-inequality `ℓ*H₀ ≤ ℓ*(p + u*k)`, i.e. `H₀ - u*k ≤ p`; and `OnSide φ f u ℓ j_k` is
   `ℓ*p + u*j_k = ℓ*H₀ + u*j₀`, i.e. `p = H₀ - u*k` — equality in the same computation.
3. `resCoeff_eq_zero_iff`: `resCoeff π φ f u ℓ h H₀ k = resMk π φ (H₀ - u*k) (dev φ f j_k)`, and
   `(dev φ f j_k).degree < φ.degree` by B.03, so B.36's slot lemma turns vanishing of the class
   into vanishing of `digPoly π (H₀ - u*k) (dev φ f j_k)`.  B.24's `digPoly_eq_zero_iff` — whose
   hypothesis `((H₀ - u*k : ℕ) : ℕ∞) ≤ gaussVal (dev φ f j_k) = npHgt φ f j_k` is step 1's
   inequality — rewrites that as `((H₀ - u*k) + 1 : ℕ∞) ≤ npHgt φ f j_k`, i.e. *strict*
   inequality, i.e. `¬ OnSide` by step 2.
4. `resCoeff … 0 ≠ 0`: at `k = 0` the abscissa is `j₀` itself, which is on the side.
5. `resCoeff … d ≠ 0`: at `k = d` the abscissa is `j₀ + ℓ*d = sideMax` (B.20's `sideMax_eq`),
   which is on the side.
6. `natDegree_resPoly`: `(resPoly …).coeff i = if i < d + 1 then resCoeff … i else 0` by the
   landed `coeff_sum_range_C_mul_X_pow`, so `natDegree ≤ d`
   (`Polynomial.natDegree_le_iff_coeff_eq_zero`) and the coefficient at `d` is `resCoeff … d ≠ 0`
   (step 5), whence `natDegree = d`; the coefficient at `0` is `resCoeff … 0 ≠ 0` (step 4).

## Minimum-hypothesis note

`htop` cannot be dropped: with `suppVal φ f u ℓ = ⊤` every abscissa is vacuously "on side" and
`sideMax_eq` fails, so step 1's `u*d ≤ H₀` — the fact that `H₀ - u*k` is a real line height and
not a `ℕ`-truncation artefact — is lost.  `hℓ` is used twice (to cancel `ℓ` and to know
`ℓ • ⊤ = ⊤`), `hcop` only through `sideMax_eq`, and `hH₀` is the GC-1/A-F.1 `sideMin` pin: the
node is stated for the left-endpoint convention and for no other.

## ⚠ THIS NODE IS `docs/GMN_citations.md` Def 2.21's LOAD-BEARING CLAUSE, AT ORDER 1 AND AT
GENERAL `O`

The corpus states *"`c_s` and `c_{s+de}` are always nonzero, so `R_λ(f)` has degree `d` and is
never divisible by `y`"* as part of a **definition**; here it is a theorem, and its proof is
where the slot lemma (B.36) is actually consumed.  `EFF.HE3.13` says the same in the form
*"a residual polynomial `R_λ ∈ K[Z]` of degree `d_λ` with `R_λ(0) ≠ 0`"*.
**Flagged for human review** (the faithfulness question is whether `OnSide`-at-the-endpoints is
the corpus's "`c_s`, `c_{s+de}` nonzero"; steps 4–5 are exactly that reading).

## Packaging

The blueprint records a SPLIT CANDIDATE at step 3/step 6 (`B30a`/`B30b`).  It is not taken: the
two signed declarations are 60 lines together, and `natDegree_resPoly` consumes
`resCoeff_eq_zero_iff` three times, so keeping them adjacent costs nothing.  The `ℕ∞` arithmetic
of steps 1–2 is factored into the private `side_line`, exactly the piece the blueprint says
"belongs with step 3".

SOURCE: `docs/GMN_citations.md` Def 2.21; `EFF.HE3.13`; `EFF.HE3.14`; `EFF.W12.23` (the vertex
clause's `digit ≠ 0`).

**TEETH.** `W12-SHAPE` (0/164, both directions) → **Lean theorem** (the degree-and-endpoints
half of every row's polygon key).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial

-- ENV-A (blueprint §0.1): the polynomial arena.  ENV-A′ adds `(hπ : Irreducible π)` per
-- signature.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- Auxiliary (not a signed node statement): `sideSet` is carved out of
`Finset.range (f.natDegree + 1)`, so every on-side abscissa is at most `f.natDegree`. -/
private theorem le_natDegree_of_mem_sideSet {φ f : Polynomial O} {u ℓ j : ℕ}
    (hj : j ∈ sideSet φ f u ℓ) : j ≤ f.natDegree := by
  classical
  have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj').1)

/-- Auxiliary: the cleared `ℕ∞`-term of the polygon at a finite height is the cast of its
`ℕ`-value. -/
private theorem nsmul_add_cast (ℓ a b : ℕ) :
    ℓ • (a : ℕ∞) + ((b : ℕ) : ℕ∞) = ((ℓ * a + b : ℕ) : ℕ∞) := by
  push_cast [nsmul_eq_mul]
  ring

/-- **B.30, steps 1–2 (private) — the side's line lies below the polygon, with equality exactly
on the side.**  At the on-side lattice abscissa `j_k = sideMin + ℓ*k` (`k ≤ d`) the line height
`H₀ - u*k` is a lower bound for the point height `npHgt φ f j_k`, and the two agree exactly when
`j_k` is on the side.  The `ℕ`-subtraction is honest here: step 1 derives `u*d ≤ H₀` from the
right endpoint's on-side equation. -/
private theorem side_line {φ f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) {k : ℕ} (hk : k ≤ sideDeg φ f u ℓ h) :
    ((H₀ - u * k : ℕ) : ℕ∞) ≤ npHgt φ f (sideMin φ f u ℓ h + ℓ * k) ∧
      (OnSide φ f u ℓ (sideMin φ f u ℓ h + ℓ * k) ↔
        npHgt φ f (sideMin φ f u ℓ h + ℓ * k) = ((H₀ - u * k : ℕ) : ℕ∞)) := by
  classical
  set j₀ := sideMin φ f u ℓ h with hj₀def
  set d := sideDeg φ f u ℓ h with hddef
  -- The two endpoints are on the side, and the right one sits at `j₀ + ℓ*d`.
  have hminmem : j₀ ∈ sideSet φ f u ℓ := Finset.min'_mem _ _
  have hmaxmem : sideMax φ f u ℓ h ∈ sideSet φ f u ℓ := Finset.max'_mem _ _
  have honmin : OnSide φ f u ℓ j₀ := onSide_of_mem_sideSet hminmem
  have honmax : OnSide φ f u ℓ (sideMax φ f u ℓ h) := onSide_of_mem_sideSet hmaxmem
  have hmaxeq : sideMax φ f u ℓ h = j₀ + ℓ * d := sideMax_eq hℓ hcop htop h
  -- Step 1: `H₀ = Hd + u*d`, hence `u*k ≤ H₀` for every `k ≤ d`.
  obtain ⟨Hd, hHd⟩ : ∃ Hd : ℕ, (Hd : ℕ∞) = npHgt φ f (sideMax φ f u ℓ h) :=
    ENat.ne_top_iff_exists.mp (npHgt_ne_top_of_onSide hℓ htop honmax)
  have hnat : ℓ * H₀ + u * j₀ = ℓ * Hd + u * sideMax φ f u ℓ h :=
    onSide_nat_eq hH₀ hHd.symm honmin honmax
  have hsum : ℓ * H₀ = ℓ * (Hd + u * d) := by
    refine Nat.add_right_cancel (m := u * j₀) ?_
    rw [hnat, hmaxeq]
    ring
  have hH₀d : H₀ = Hd + u * d := Nat.eq_of_mul_eq_mul_left hℓ hsum
  have hud : u * k ≤ H₀ := by
    refine le_trans (Nat.mul_le_mul_left u hk) ?_
    rw [hH₀d]
    exact Nat.le_add_left _ _
  -- Step 2: the `inf` bound at the abscissa `j₀ + ℓ*k`, and the value of `suppVal`.
  have hjkle : j₀ + ℓ * k ≤ f.natDegree := by
    refine le_trans ?_ (le_natDegree_of_mem_sideSet hmaxmem)
    rw [hmaxeq]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left ℓ hk) _
  have hSle : suppVal φ f u ℓ ≤ ℓ • npHgt φ f (j₀ + ℓ * k) + ((u * (j₀ + ℓ * k) : ℕ) : ℕ∞) :=
    Finset.inf_le (f := fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hjkle))
  have hS : suppVal φ f u ℓ = ((ℓ * H₀ + u * j₀ : ℕ) : ℕ∞) := by
    have h1 : ℓ • npHgt φ f j₀ + ((u * j₀ : ℕ) : ℕ∞) = suppVal φ f u ℓ := honmin
    rw [← h1, hH₀, nsmul_add_cast]
  rcases eq_or_ne (npHgt φ f (j₀ + ℓ * k)) ⊤ with hP | hP
  · -- The point at height `⊤` is off the side, and the bound is vacuous.
    refine ⟨by rw [hP]; exact le_top, iff_of_false ?_ ?_⟩
    · exact fun hon => (npHgt_ne_top_of_onSide hℓ htop hon) hP
    · intro heq
      rw [hP] at heq
      exact (ENat.coe_ne_top _) heq.symm
  · -- The finite branch: everything is a `ℕ`-computation.
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℕ∞) = npHgt φ f (j₀ + ℓ * k) := ENat.ne_top_iff_exists.mp hP
    rw [hS, ← hp, nsmul_add_cast] at hSle
    have hSnat : ℓ * H₀ + u * j₀ ≤ ℓ * p + u * (j₀ + ℓ * k) := by exact_mod_cast hSle
    have hmul : ℓ * H₀ ≤ ℓ * (p + u * k) := by
      have e : ℓ * p + u * (j₀ + ℓ * k) = ℓ * (p + u * k) + u * j₀ := by ring
      rw [e] at hSnat
      exact Nat.le_of_add_le_add_right hSnat
    have hle' : H₀ ≤ p + u * k := Nat.le_of_mul_le_mul_left hmul hℓ
    have honiff : OnSide φ f u ℓ (j₀ + ℓ * k) ↔
        ℓ * p + u * (j₀ + ℓ * k) = ℓ * H₀ + u * j₀ := by
      constructor
      · intro hon
        have h1 : ℓ • npHgt φ f (j₀ + ℓ * k) + ((u * (j₀ + ℓ * k) : ℕ) : ℕ∞)
            = suppVal φ f u ℓ := hon
        rw [← hp, nsmul_add_cast, hS] at h1
        exact_mod_cast h1
      · intro hnat2
        show ℓ • npHgt φ f (j₀ + ℓ * k) + ((u * (j₀ + ℓ * k) : ℕ) : ℕ∞) = suppVal φ f u ℓ
        rw [← hp, nsmul_add_cast, hS]
        exact_mod_cast hnat2
    have hfinal : (ℓ * p + u * (j₀ + ℓ * k) = ℓ * H₀ + u * j₀) ↔ (p = H₀ - u * k) := by
      constructor
      · intro e
        have e2 : ℓ * (p + u * k) + u * j₀ = ℓ * H₀ + u * j₀ := by rw [← e]; ring
        have e3 : p + u * k = H₀ := Nat.eq_of_mul_eq_mul_left hℓ (Nat.add_right_cancel e2)
        rw [← e3, Nat.add_sub_cancel]
      · intro e
        have e3 : p + u * k = H₀ := by rw [e, Nat.sub_add_cancel hud]
        calc ℓ * p + u * (j₀ + ℓ * k) = ℓ * (p + u * k) + u * j₀ := by ring
          _ = ℓ * H₀ + u * j₀ := by rw [e3]
    refine ⟨?_, ?_⟩
    · rw [← hp]
      exact_mod_cast Nat.sub_le_iff_le_add.mpr hle'
    · rw [honiff, hfinal, ← hp]
      constructor
      · intro e; exact_mod_cast e
      · intro e; exact_mod_cast e

/-- **B.30 (a) — a residual coefficient vanishes exactly off the side.**  For `k ≤ d` the `k`-th
residual coefficient of the `(u,ℓ)`-side vanishes precisely when the lattice abscissa
`sideMin + ℓ*k` fails to be on the side, i.e. when the polygon's point there sits strictly above
the side's line.  This is where B.36's slot lemma is consumed. -/
theorem resCoeff_eq_zero_iff (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) {k : ℕ} (hk : k ≤ sideDeg φ f u ℓ h) :
    resCoeff π φ f u ℓ h H₀ k = 0 ↔ ¬ OnSide φ f u ℓ (sideMin φ f u ℓ h + ℓ * k) := by
  obtain ⟨hle, honiff⟩ := side_line hℓ hcop htop h hH₀ hk
  have hdegdev : (dev φ f (sideMin φ f u ℓ h + ℓ * k)).degree < φ.degree :=
    degree_dev_lt hφ.monic hφ.pos _ _
  have hgv : gaussVal (dev φ f (sideMin φ f u ℓ h + ℓ * k))
      = npHgt φ f (sideMin φ f u ℓ h + ℓ * k) := rfl
  rw [resCoeff, resMk_eq_zero_iff hπ hφ hdegdev, digPoly_eq_zero_iff hπ hle, hgv, honiff]
  constructor
  · -- strict inequality forbids equality with the line height
    intro hge heq
    rw [heq] at hge
    have hcontra : (H₀ - u * k + 1 : ℕ) ≤ H₀ - u * k := by exact_mod_cast hge
    omega
  · -- and conversely, `≥` plus `≠` is `>`
    intro hne
    have hlt : ((H₀ - u * k : ℕ) : ℕ∞) < npHgt φ f (sideMin φ f u ℓ h + ℓ * k) :=
      lt_of_le_of_ne hle (fun hh => hne hh.symm)
    rcases eq_or_ne (npHgt φ f (sideMin φ f u ℓ h + ℓ * k)) ⊤ with hT | hT
    · rw [hT]; exact le_top
    · obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℕ∞) = npHgt φ f (sideMin φ f u ℓ h + ℓ * k) :=
        ENat.ne_top_iff_exists.mp hT
      rw [← hq] at hlt ⊢
      have hq' : H₀ - u * k < q := by exact_mod_cast hlt
      exact_mod_cast hq'

/-- **B.30 (b) — the residual polynomial has degree `d` and nonzero constant term.**  Both
endpoints of the side carry nonvanishing residual coefficients (B.30 (a) at `k = 0` and
`k = d`), and B.29's sum has no coefficients above `d`. -/
theorem natDegree_resPoly (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (htop : suppVal φ f u ℓ ≠ ⊤) (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) :
    (resPoly π φ f u ℓ h H₀).natDegree = sideDeg φ f u ℓ h ∧
      (resPoly π φ f u ℓ h H₀).coeff 0 ≠ 0 := by
  classical
  have hcoeff : ∀ i, (resPoly π φ f u ℓ h H₀).coeff i =
      if i < sideDeg φ f u ℓ h + 1 then resCoeff π φ f u ℓ h H₀ i else 0 := by
    intro i
    rw [resPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  -- Step 4: the left endpoint is on the side.
  have hzero : resCoeff π φ f u ℓ h H₀ 0 ≠ 0 := by
    rw [Ne, resCoeff_eq_zero_iff hπ hφ hℓ hcop htop h hH₀ (Nat.zero_le _), not_not]
    have hmem : sideMin φ f u ℓ h ∈ sideSet φ f u ℓ := Finset.min'_mem _ _
    simpa using onSide_of_mem_sideSet hmem
  -- Step 5: the right endpoint is `sideMin + ℓ*d`, and it is on the side.
  have hlead : resCoeff π φ f u ℓ h H₀ (sideDeg φ f u ℓ h) ≠ 0 := by
    rw [Ne, resCoeff_eq_zero_iff hπ hφ hℓ hcop htop h hH₀ le_rfl, not_not]
    have hmem : sideMax φ f u ℓ h ∈ sideSet φ f u ℓ := Finset.max'_mem _ _
    have hm := onSide_of_mem_sideSet hmem
    rwa [sideMax_eq hℓ hcop htop h] at hm
  have hdegle : (resPoly π φ f u ℓ h H₀).natDegree ≤ sideDeg φ f u ℓ h := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    rw [hcoeff m, if_neg (by omega)]
  refine ⟨Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegle ?_, ?_⟩
  · rw [hcoeff, if_pos (Nat.lt_succ_self _)]
    exact hlead
  · rw [hcoeff, if_pos (Nat.succ_pos _)]
    exact hzero

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.resCoeff_eq_zero_iff
#print axioms Uniformity.Density.Leaf.natDegree_resPoly
end AxCheck
