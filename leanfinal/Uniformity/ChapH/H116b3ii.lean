/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B39a
import Uniformity.ChapB.B39b
import Uniformity.ChapB.B77b

/-!
# Uniformity.ChapH.H116b3ii — the above-the-line transport (NODE H.116b3-ii)

## ⚠ FLAGGED FOR HUMAN REVIEW (new general polygon statement, parent CLAUDE.md trust boundary)

**Chapter H, NODE H.116b3-ii** (`blueprint/CHAP-H_general_induction.md`, AMENDMENT **A-H.8**
§3.2), the second of the three sub-nodes A-H.8 split `H.116b3` into.  Three declarations, at
the frozen A-H.8 signatures:

* `suppVal_congr_of_above_line`;
* `sideSet_congr_of_above_line`;
* `resPoly_congr_of_above_line`.

**What is new.** B.77 (`B77a`/`B77b`) transports the polygon along a UNIFORM depth
`π ^ N ∣ (f − f').coeff i`.  That hypothesis FAILS for the planted swap of H.116b3: `bb` and
`bb'` are different level-`N` classes, so the difference is only `π ¹`-deep relative to the
planted floor (A-H.8 §1).  What DOES hold there is a LINE-depth hypothesis — the perturbation
sits strictly above the supporting line at every abscissa:

`habove : ∀ j, suppVal φ f u ℓ < ℓ • npHgt φ (f' - f) j + ((u * j : ℕ) : ℕ∞)`

and that is enough for the same three conclusions.  This is the one genuinely new general
polygon statement in the repaired route, hence the flag.  Nothing here is a signed §-node of
chapter B; the content is chapter-B-shaped but lives in chapter H because chapter B is closed
(A-H.8 §3.2 design note (f)).

## Why the statement is at general monic `φ`, not at `φ = X`

The block record states (3d) at `φ = X`.  The general form costs nothing: `dev` is additive
(`dev_add_of_monic`, B32a), so a line-depth hypothesis phrased on `npHgt φ (f' − f)` passes to
developments, and `min_gaussVal_le_gaussVal_add` (B32a) with `gaussVal_neg`/`dev_neg` (B39b)
supplies the ultrametric bookkeeping in both directions.  The consumer (H.116b3-iii)
instantiates at `φ = X`, where `habove` is read off `npHgt_X` as a plain coefficient bound.

## The dichotomy, and why `hcop` is load-bearing

`npHgt_dichotomy_line` is the line-depth analogue of B77a's `npHgt_dichotomy`: at every
abscissa either the two polygon heights are EQUAL (this is the branch where `f`'s point is ON
the supporting line, where the hypothesis forces the perturbation strictly higher, so the
ultrametric sum is exact), or BOTH points sit strictly above the line (and so leave both
`inf`s and both `sideSet`s).  Clauses 1 and 2 are that dichotomy read at the `inf` and at the
defining equation of `OnSide`, exactly as at B77a.

Clause 3 reads the digit at the LINE height `H₀ − u·k` with `ℕ`-subtraction.  The needed depth
`npHgt φ (f' − f) (sideMin + ℓk) > H₀ − u·k` follows from `habove` only because `u·k ≤ H₀` on
the range `k ≤ sideDeg` that `resPoly` sums over — which is B39a's `u_mul_sideDeg_le`, and THAT
needs `hcop`.  Without `hcop` the clause is not provable as stated (A-H.8 §2.2 (3d), §3.2
design note (b)).  `htop` is redundant (it follows from `hH₀` and `sideMin` being on-side) and
is carried anyway to match `B39a`'s shape at the call site (design note (c)).

## The `private`-declaration tax

B77a's `npHgt_dichotomy`, `cast_mul_le_term`, `suppVal_lt_of_visible` and B77b's `digAt_congr`,
`digPoly_congr`, `resMk_congr`, `sideMin_congr` are all `private` and do not export.  The
pieces of them this file needs are COPIED here (primed names), not cited — A-H.8 §2.3.  This is
why the node is 120 lines and not 60.

DEPENDS: B.02/B.07/B.08 (`dev`, `gaussVal`, `le_gaussVal_iff`) · B.11 (`npHgt`) · B.14
(`suppVal`) · B.16 (`OnSide`, `sideSet`) · B.20 (`sideMin`, `sideMax`, `sideDeg`,
`onSide_of_mem_sideSet`) · B.21/B.22/B.23/B.24/B.25 (`digAt`, `digAt_eq_zero_iff`, `digAt_add`,
`digPoly`, `digPoly_coeff`, `resMk`) · B.28/B.29 (`resCoeff`, `resPoly`) · B.32a
(`dev_add_of_monic`, `min_gaussVal_le_gaussVal_add`) · B.35b (`suppVal_le_weight`) · **B39a**
(`suppVal_eq_of_onSide`, `u_mul_sideDeg_le`) · **B39b** (`gaussVal_neg`) · **B77a/B77b as the
TEMPLATE** (their private helpers are copied, not cited).

**Unused signed binders are KEPT and the linter suppressed** (A-H.8 §3.2 design note (d)):
`hπ` is not consumed by clauses 1 and 2, and the signatures are frozen by the amendment.
B77a does exactly the same, with the reason in its docstring.

**ENVIRONMENT — ENV-A′** (chapter-B environment), inside a chapter-H file.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

open Polynomial Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 0. `ℕ∞` and `ℕ` bookkeeping -/

private theorem enat_smul_nat'' (ℓ t : ℕ) : ℓ • ((t : ℕ) : ℕ∞) = ((ℓ * t : ℕ) : ℕ∞) := by
  simp [nsmul_eq_mul]

private theorem enat_smul_mono'' {ℓ : ℕ} {x y : ℕ∞} (h : x ≤ y) : ℓ • x ≤ ℓ • y := by
  simp only [nsmul_eq_mul]
  gcongr

/-- Pure `ℕ` arithmetic, factored out so `omega` never meets a product of variables. -/
private theorem nat_sub_lt_of_lt_add {a b c : ℕ} (hba : b ≤ a) (h : a < c + b) : a - b < c := by
  omega

/-! ## 1. The ultrametric exactness lemma -/

/-- **The ultrametric sum is exact at the strictly lower term.**  If `gaussVal a < gaussVal b`
then `gaussVal (a + b) = gaussVal a`.  Both halves run off B32a's
`min_gaussVal_le_gaussVal_add`, the second one against `a = (a + b) + (−b)` with
`gaussVal_neg` (B39b). -/
private theorem gaussVal_add_eq_of_lt {a b : Polynomial O} (h : gaussVal a < gaussVal b) :
    gaussVal (a + b) = gaussVal a := by
  refine le_antisymm ?_ ?_
  · have h1 : min (gaussVal (a + b)) (gaussVal (-b)) ≤ gaussVal ((a + b) + -b) :=
      min_gaussVal_le_gaussVal_add _ _
    rw [show (a + b) + -b = a by ring, gaussVal_neg] at h1
    by_contra hcon
    exact absurd h1 (not_le.2 (lt_min (not_le.1 hcon) h))
  · have h2 := min_gaussVal_le_gaussVal_add a b
    rwa [min_eq_left h.le] at h2

/-! ## 2. The line-depth dichotomy (the analogue of B77a's `npHgt_dichotomy`) -/

/-- **The transport dichotomy, at LINE depth.**  At every abscissa, a perturbation strictly
above the supporting line either leaves the polygon height *unchanged*, or leaves *both* points
strictly above the line (so neither participates in the `inf`, and neither is on the side).

The first branch is where `f`'s point is ON the line: there `habove` forces
`npHgt φ f j < npHgt φ (f' − f) j`, and the ultrametric sum is exact. -/
private theorem npHgt_dichotomy_line {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {f f' : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (habove : ∀ j, suppVal φ f u ℓ < ℓ • npHgt φ (f' - f) j + ((u * j : ℕ) : ℕ∞)) (j : ℕ) :
    npHgt φ f' j = npHgt φ f j ∨
      (suppVal φ f u ℓ < ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) ∧
        suppVal φ f u ℓ < ℓ • npHgt φ f' j + ((u * j : ℕ) : ℕ∞)) := by
  have hdev : npHgt φ f' j = gaussVal (dev φ f j + dev φ (f' - f) j) := by
    have h := dev_add_of_monic hφ f (f' - f) j
    rw [show f + (f' - f) = f' by ring] at h
    rw [npHgt, h]
  rcases eq_or_lt_of_le (suppVal_le_weight hφ hd hℓ u f j) with heq | hlt
  · refine Or.inl ?_
    have hAB : ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞)
        < ℓ • npHgt φ (f' - f) j + ((u * j : ℕ) : ℕ∞) := by
      rw [← heq]; exact habove j
    have hsmul : ℓ • npHgt φ f j < ℓ • npHgt φ (f' - f) j := by
      by_contra hcon
      exact absurd (add_le_add (not_lt.1 hcon) (le_refl ((u * j : ℕ) : ℕ∞))) (not_le.2 hAB)
    have hAltB : npHgt φ f j < npHgt φ (f' - f) j := by
      by_contra hcon
      exact absurd (enat_smul_mono'' (not_lt.1 hcon)) (not_le.2 hsmul)
    rw [hdev]
    exact gaussVal_add_eq_of_lt hAltB
  · refine Or.inr ⟨hlt, ?_⟩
    have hminle : min (npHgt φ f j) (npHgt φ (f' - f) j) ≤ npHgt φ f' j := by
      rw [hdev]
      exact min_gaussVal_le_gaussVal_add (dev φ f j) (dev φ (f' - f) j)
    refine lt_of_lt_of_le ?_ (add_le_add (enat_smul_mono'' hminle) (le_refl _))
    rcases le_total (npHgt φ f j) (npHgt φ (f' - f) j) with hc | hc
    · rw [min_eq_left hc]; exact hlt
    · rw [min_eq_right hc]; exact habove j

/-! ## 3. H.116b3-ii (1/3) — the support value transports -/

-- `hπ` is part of the frozen A-H.8 signature and is not consumed by this clause; see the
-- module docstring (design note (d)).
set_option linter.unusedVariables false in
/-- **H.116b3-ii (1/3). ⚠ FLAGGED FOR HUMAN REVIEW.**  A perturbation strictly above the
supporting line at every abscissa leaves the cleared support value unchanged.

`≥` is pointwise (`Finset.le_inf`): at an abscissa in the equal-height branch the `f'`-term IS
the `f`-term, and in the above-the-line branch it is strictly above the value.  `≤` needs the
`f`-side `inf` to be ATTAINED (`Finset.exists_mem_eq_inf`) at some `j₀`: attainment rules out
the above-the-line branch at `j₀`, so the heights agree there. -/
theorem suppVal_congr_of_above_line (hπ : Irreducible π) {φ : Polynomial O}
    (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f f' : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hdeg : f'.natDegree = f.natDegree)
    (habove : ∀ j, suppVal φ f u ℓ < ℓ • npHgt φ (f' - f) j + ((u * j : ℕ) : ℕ∞)) :
    suppVal φ f' u ℓ = suppVal φ f u ℓ := by
  classical
  have hdich := npHgt_dichotomy_line hφ hd hℓ habove
  refine le_antisymm ?_ ?_
  · obtain ⟨j₀, hj₀mem, hj₀⟩ := Finset.exists_mem_eq_inf (Finset.range (f.natDegree + 1))
      ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
      (fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞))
    have hval : suppVal φ f u ℓ = ℓ • npHgt φ f j₀ + ((u * j₀ : ℕ) : ℕ∞) := hj₀
    have heq : npHgt φ f' j₀ = npHgt φ f j₀ := by
      rcases hdich j₀ with h1 | ⟨h2, _⟩
      · exact h1
      · exact absurd hval (ne_of_lt h2)
    have hmem' : j₀ ∈ Finset.range (f'.natDegree + 1) := by rw [hdeg]; exact hj₀mem
    calc suppVal φ f' u ℓ
        ≤ ℓ • npHgt φ f' j₀ + ((u * j₀ : ℕ) : ℕ∞) :=
          Finset.inf_le (f := fun j => ℓ • npHgt φ f' j + ((u * j : ℕ) : ℕ∞)) hmem'
      _ = suppVal φ f u ℓ := by rw [heq]; exact hval.symm
  · change suppVal φ f u ℓ
      ≤ (Finset.range (f'.natDegree + 1)).inf (fun j => ℓ • npHgt φ f' j + ((u * j : ℕ) : ℕ∞))
    refine Finset.le_inf fun j _ => ?_
    rcases hdich j with h1 | ⟨_, h2⟩
    · rw [h1]
      exact suppVal_le_weight hφ hd hℓ u f j
    · exact h2.le

/-! ## 4. H.116b3-ii (2/3) — the on-side abscissae transport -/

-- `hπ` is part of the frozen A-H.8 signature and is not consumed by this clause.
set_option linter.unusedVariables false in
/-- **H.116b3-ii (2/3). ⚠ FLAGGED FOR HUMAN REVIEW.**  The same, `sideSet` clause: in the
equal-height branch the two `OnSide` equations are literally the same (their right-hand sides
agree by clause 1), and in the above-the-line branch both are false.  `sideMin`, `sideMax`,
`sideDeg` and `IsPure` transport by rewriting along this, exactly as at B77a. -/
theorem sideSet_congr_of_above_line (hπ : Irreducible π) {φ : Polynomial O}
    (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f f' : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hdeg : f'.natDegree = f.natDegree)
    (habove : ∀ j, suppVal φ f u ℓ < ℓ • npHgt φ (f' - f) j + ((u * j : ℕ) : ℕ∞)) :
    sideSet φ f' u ℓ = sideSet φ f u ℓ := by
  classical
  have hsupp : suppVal φ f' u ℓ = suppVal φ f u ℓ :=
    suppVal_congr_of_above_line hπ hφ hd hℓ hdeg habove
  have hdich := npHgt_dichotomy_line hφ hd hℓ habove
  have hOn : ∀ j, OnSide φ f' u ℓ j ↔ OnSide φ f u ℓ j := by
    intro j
    rcases hdich j with h1 | ⟨h2, h3⟩
    · rw [OnSide, OnSide, h1, hsupp]
    · constructor
      · intro hon
        have hT : ℓ • npHgt φ f' j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ := hon.trans hsupp
        exact absurd h3 (by rw [hT]; exact lt_irrefl _)
      · intro hon
        have hT : ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = suppVal φ f u ℓ := hon
        exact absurd h2 (by rw [hT]; exact lt_irrefl _)
  ext j
  simp only [sideSet, Finset.mem_filter, Finset.mem_range, hdeg, hOn j]

/-! ## 5. The copied digit chain (B77b's private helpers, A-H.8 §2.3) -/

/-- B77b's `digAt_congr`, copied (it is `private` there). -/
private theorem digAt_congr' (hπ : Irreducible π) {N k : ℕ} (hk : k < N) {x y : O}
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

/-- B77b's `digPoly_congr`, copied. -/
private theorem digPoly_congr' (hπ : Irreducible π) {N k : ℕ} (hk : k < N)
    {a b : Polynomial O} (h : ∀ i, π ^ N ∣ (a - b).coeff i) : digPoly π k a = digPoly π k b := by
  refine Polynomial.ext fun i => ?_
  rw [digPoly_coeff hπ, digPoly_coeff hπ]
  refine digAt_congr' hπ hk ?_
  simpa only [Polynomial.coeff_sub] using h i

/-- B77b's `resMk_congr`, copied. -/
private theorem resMk_congr' (hπ : Irreducible π) {N k : ℕ} (hk : k < N)
    {φ a b : Polynomial O} (h : ∀ i, π ^ N ∣ (a - b).coeff i) :
    resMk π φ k a = resMk π φ k b := by
  rw [resMk, resMk, digPoly_congr' hπ hk h]

/-- B77b's `min'_congr`, copied. -/
private theorem min'_congr' {s t : Finset ℕ} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst hst; rfl

/-- B77b's `max'_congr`, copied. -/
private theorem max'_congr' {s t : Finset ℕ} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by subst hst; rfl

/-- B77b's `sideMin_congr`, copied. -/
private theorem sideMin_congr' {φ f f' : Polynomial O} {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) :
    sideMin φ f' u ℓ h' = sideMin φ f u ℓ h :=
  min'_congr' hset h' h

/-- B77b's `sideMax_congr`, copied. -/
private theorem sideMax_congr' {φ f f' : Polynomial O} {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) :
    sideMax φ f' u ℓ h' = sideMax φ f u ℓ h :=
  max'_congr' hset h' h

/-- B77b's `sideDeg_congr`, copied. -/
private theorem sideDeg_congr' {φ f f' : Polynomial O} {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) :
    sideDeg φ f' u ℓ h' = sideDeg φ f u ℓ h := by
  rw [sideDeg, sideDeg, sideMin_congr' hset h h', sideMax_congr' hset h h']

/-! ## 6. H.116b3-ii (3/3) — the residual polynomial transports -/

/-- **The residual coefficient at a lattice abscissa transports.**  At `J = sideMin + ℓ·k` with
`k ≤ sideDeg`, the line height is `H = H₀ − u·k`, honest in `ℕ` because `u·k ≤ u·sideDeg ≤ H₀`
(`u_mul_sideDeg_le`, whence `hcop`).  `habove` at `J` then reads `npHgt φ (f' − f) J > H`, i.e.
`π ^ (H+1)` divides every coefficient of `dev φ (f' − f) J`, and the copied digit chain
equates the two reductions. -/
private theorem resCoeff_congr_line (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    {f f' : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (habove : ∀ j, suppVal φ f u ℓ < ℓ • npHgt φ (f' - f) j + ((u * j : ℕ) : ℕ∞))
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) (htop : suppVal φ f u ℓ ≠ ⊤) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) {k : ℕ}
    (hk : k ≤ sideDeg φ f u ℓ h) :
    resCoeff π φ f' u ℓ h' H₀ k = resCoeff π φ f u ℓ h H₀ k := by
  classical
  have hukH : u * k ≤ H₀ :=
    le_trans (Nat.mul_le_mul_left u hk) (u_mul_sideDeg_le hℓ hcop htop h hH₀)
  have hS : suppVal φ f u ℓ = ((ℓ * H₀ + u * sideMin φ f u ℓ h : ℕ) : ℕ∞) :=
    suppVal_eq_of_onSide hH₀ (onSide_of_mem_sideSet (Finset.min'_mem _ h))
  -- the depth of the perturbation at the lattice abscissa `J`
  have hdepth : ((H₀ - u * k + 1 : ℕ) : ℕ∞)
      ≤ gaussVal (dev φ (f' - f) (sideMin φ f u ℓ h + ℓ * k)) := by
    rcases eq_or_ne (npHgt φ (f' - f) (sideMin φ f u ℓ h + ℓ * k)) ⊤ with hT | hT
    · rw [show gaussVal (dev φ (f' - f) (sideMin φ f u ℓ h + ℓ * k))
        = npHgt φ (f' - f) (sideMin φ f u ℓ h + ℓ * k) from rfl, hT]
      exact le_top
    obtain ⟨V, hV⟩ := ENat.ne_top_iff_exists.1 hT
    have hab := habove (sideMin φ f u ℓ h + ℓ * k)
    rw [hS, ← hV, enat_smul_nat'', ← Nat.cast_add] at hab
    have hnat : ℓ * H₀ + u * sideMin φ f u ℓ h
        < ℓ * V + u * (sideMin φ f u ℓ h + ℓ * k) := by exact_mod_cast hab
    have hexp : ℓ * V + u * (sideMin φ f u ℓ h + ℓ * k)
        = ℓ * (V + u * k) + u * sideMin φ f u ℓ h := by ring
    rw [hexp] at hnat
    have h4 : H₀ < V + u * k :=
      Nat.lt_of_mul_lt_mul_left (Nat.lt_of_add_lt_add_right hnat)
    have h5 : H₀ - u * k < V := nat_sub_lt_of_lt_add hukH h4
    rw [show gaussVal (dev φ (f' - f) (sideMin φ f u ℓ h + ℓ * k))
      = npHgt φ (f' - f) (sideMin φ f u ℓ h + ℓ * k) from rfl, ← hV]
    exact_mod_cast (by omega : H₀ - u * k + 1 ≤ V)
  -- the two developments differ by `dev φ (f' - f) J`, which is `π ^ (H+1)`-deep
  have hdiff : ∀ i, π ^ (H₀ - u * k + 1) ∣
      (dev φ f' (sideMin φ f u ℓ h + ℓ * k) - dev φ f (sideMin φ f u ℓ h + ℓ * k)).coeff i := by
    have hsplit : dev φ f' (sideMin φ f u ℓ h + ℓ * k)
        - dev φ f (sideMin φ f u ℓ h + ℓ * k) = dev φ (f' - f) (sideMin φ f u ℓ h + ℓ * k) := by
      have hadd := dev_add_of_monic hφ f (f' - f) (sideMin φ f u ℓ h + ℓ * k)
      rw [show f + (f' - f) = f' by ring] at hadd
      rw [hadd]; ring
    rw [hsplit]
    exact (le_gaussVal_iff hπ).1 hdepth
  rw [resCoeff, resCoeff, sideMin_congr' hset h h']
  exact resMk_congr' hπ (Nat.lt_succ_self _) hdiff

/-- The signed clause with an ARBITRARY nonemptiness witness on the `f'` side; the frozen form
below is this one applied to the amendment's rewritten witness (proof irrelevance makes the
application definitional).  This mirrors B77b's `resPoly_congr'`. -/
private theorem resPoly_congr_line' (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    {f f' : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (habove : ∀ j, suppVal φ f u ℓ < ℓ • npHgt φ (f' - f) j + ((u * j : ℕ) : ℕ∞))
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) (htop : suppVal φ f u ℓ ≠ ⊤) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) :
    resPoly π φ f' u ℓ h' H₀ = resPoly π φ f u ℓ h H₀ := by
  rw [resPoly, resPoly, sideDeg_congr' hset h h']
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [resCoeff_congr_line hπ hφ hℓ hcop habove hset h h' htop hH₀
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

-- `hd` is part of the frozen A-H.8 signature and is consumed only through the two clauses
-- above; it is kept and the linter suppressed (design note (d)).
set_option linter.unusedVariables false in
/-- **H.116b3-ii (3/3). ⚠ FLAGGED FOR HUMAN REVIEW.**  The same, `resPoly` clause — the
analogue of B77b's `resPoly_congr` with `π ^ N`-depth replaced by LINE depth.

`hcop` is load-bearing, not decoration: `resCoeff` reads the digit at the `ℕ`-subtracted line
height `H₀ − u·k`, honest only because `u · sideDeg ≤ H₀` (B39a's `u_mul_sideDeg_le`, which
needs `hcop`).  `htop` is redundant and carried to match `B39a`'s shape at the call site.  The
`(by …)` nonemptiness argument mirrors B77b's frozen form verbatim. -/
theorem resPoly_congr_of_above_line (hπ : Irreducible π) {φ : Polynomial O}
    (hφ : φ.Monic) (hd : 0 < φ.natDegree) {f f' : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hdeg : f'.natDegree = f.natDegree)
    (habove : ∀ j, suppVal φ f u ℓ < ℓ • npHgt φ (f' - f) j + ((u * j : ℕ) : ℕ∞))
    (h : (sideSet φ f u ℓ).Nonempty) (htop : suppVal φ f u ℓ ≠ ⊤) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) :
    resPoly π φ f' u ℓ
        (by rw [sideSet_congr_of_above_line hπ hφ hd hℓ hdeg habove]; exact h) H₀
      = resPoly π φ f u ℓ h H₀ :=
  resPoly_congr_line' hπ hφ hℓ hcop habove
    (sideSet_congr_of_above_line hπ hφ hd hℓ hdeg habove) h _ htop hH₀

end Uniformity.Density.Induction

/-! ## 7. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.suppVal_congr_of_above_line
#print axioms Uniformity.Density.Induction.sideSet_congr_of_above_line
#print axioms Uniformity.Density.Induction.resPoly_congr_of_above_line

end AxCheck
