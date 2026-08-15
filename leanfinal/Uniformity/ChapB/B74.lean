/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B04
import Uniformity.ChapB.B12
import Uniformity.ChapB.B17
import Uniformity.ChapB.B22
import Uniformity.ChapB.B24
import Uniformity.ChapB.B73
import Uniformity.ChapB.B76

/-!
# Uniformity.ChapB.B74 — the descent trigger is decidable from the window

**Chapter B, NODE B.74** (`blueprint/CHAP-B_leaf_layer.md` §8), ENV-C.  One signed
declaration, `needsDescent_congr`:

`NeedsDescent π φ f` (B.73 — *some* side of `f`'s `φ`-adic polygon has a non-separable
residual polynomial) depends only on the level-`N` congruence class of `f`, provided the
window sees the polygon (`hvis : Visible π φ f N`, B.75).  The height at which each side's
residual read enters is `H₀` with `npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)` — the
A-F.1/PA-1 `sideMin` pin, carried verbatim from B.73's body — and every such `H₀` is proved
here to be `< N`, so the whole read sits strictly inside the window.

DEPENDS: B.04 (`dev_eq_zero_of_lt`) · B.10 (`dev_congr`) · B.12 (`npHgt_eq_top_of_lt`) ·
B.17 (`npHgt_ne_top_of_onSide`) · B.20 (`onSide_of_mem_sideSet`, `sideMin`) ·
B.22 (`digAt_eq_zero_iff`, `digAt_add`) · B.24 (`digPoly_coeff`) · B.25 (`resMk`) ·
B.28/B.29 (`resCoeff`, `resPoly`) · B.73 (`NeedsDescent`) ·
B.76 (`npHgt_min_congr`, `visible_iff_npHgt_lt`, `visible_congr`).

## ⚠ Why B.77 is not cited here, and what replaces it

The blueprint's PROOF field reads "B.77's level-stability transports `npHgt`, `suppVal`,
`sideSet` and `resPoly` from `f` to `f'` under `hvis`; `Separable` is a property of
`resPoly`, so it transports."  **That citation does not typecheck against the frozen
signatures.**  All three landed B.77 clauses (`suppVal_congr`, `sideSet_congr`,
`resPoly_congr`, `B77a.lean`/`B77b.lean`) carry the extra hypothesis

`(hdeg : f'.natDegree = f.natDegree)`,

which B.74's frozen SIGNATURE does **not** supply — B.74 constrains `f` and `f'` only by the
coefficientwise congruence `hff' : ∀ i, π ^ N ∣ (f - f').coeff i`, which is satisfied by e.g.
`f' = f + π ^ N * X ^ M` for arbitrarily large `M`.  Rather than weaken the statement (the
statement fence forbids it) or leave the node blocked, this file re-derives the three
transports in a **degree-free** form.  The mathematical content that replaces `hdeg` is a
single observation, isolated below as `suppVal_le_term` and `mem_sideSet_iff`:

* `suppVal φ f u ℓ ≤ ℓ • npHgt φ f j + u * j` holds for **every** `j : ℕ`, not only for
  `j ≤ f.natDegree`, because past the degree the height is `⊤` (B.12's `npHgt_eq_top_of_lt`)
  and the term is `⊤` (here `0 < ℓ` is load-bearing); and
* every abscissa that is `OnSide` at a **finite** cleared support value is automatically
  `≤ f.natDegree` (B.17's `npHgt_ne_top_of_onSide` plus the same B.12 fact), so
  `j ∈ sideSet φ f u ℓ ↔ OnSide φ f u ℓ j` outright.

With those two, the `Finset.range (f.natDegree + 1)` that `suppVal` and `sideSet` are built
over stops being visible to the argument, and the landed B.77 proofs go through with the
degree bookkeeping deleted.  The private helpers below (`npHgt_dich`, `cast_mul_le_term'`,
`suppVal_lt_of_vis`, the three digit lemmas, the `min'`/`max'` congruences) are the
degree-free counterparts of B77a's and B77b's own private helpers, which are `private` and
therefore unavailable across modules; nothing landed is edited.

## PROOF

1. `suppVal_le_of_congr` — the cleared support value only decreases: pick `j₀` attaining
   `suppVal φ f u ℓ`; B.76(i)'s dichotomy (`npHgt_dich`) either matches the two heights at
   `j₀` (and then `suppVal φ f' u ℓ ≤` that term `= suppVal φ f u ℓ`) or puts both at or
   above the cap `N`, which contradicts `suppVal φ f u ℓ < ℓ * N` (`suppVal_lt_of_vis`,
   from `hvis`).  Applied in both directions this gives `suppVal φ f' u ℓ = suppVal φ f u ℓ`.
2. `sideSet_congr'` — with the two support values equal and both `< ℓ * N`, the dichotomy
   makes `OnSide` pointwise equivalent (capped abscissae are off-side on both sides), and
   `mem_sideSet_iff` turns that into equality of the two `Finset`s.
3. The endpoints (`sideMin`, `sideMax`, `sideDeg`) transport because they are functions of
   the `Finset` alone.
4. `resPoly_congr''` — each residual coefficient is read at the line height `H₀ - u * k ≤ H₀`,
   and `H₀ < N` (`H₀_lt_of_visible`: the left endpoint is on the side, so
   `ℓ * H₀ + u * sideMin = suppVal < ℓ * N`), so the digit lemma applies strictly inside the
   window.
5. `Separable` is a property of `resPoly`, and `1 < (sideSet …).card` a property of
   `sideSet`; both transport, in both directions (the hypotheses are symmetric once
   `Visible π φ f' N` is obtained from B.76(iv)'s `visible_congr`).

SOURCE: `EFF.HE3.67` (R8-1's recursive certificate, clause 2); `EFF.W12.27` ("All data the
read consumes sit at heights `≤ N−1`, so every lift of the window class shares them").

## Status

Sorry-free, axiom-free (Lean core only).  ENV-C's `[IsAdicComplete (maximalIdeal O) O]` and
`[Finite (ResidueField O)]` are carried on the signed theorem to match the frozen stub; the
proof consumes neither.
-/

namespace Uniformity.Density.Leaf

open IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## §1 — reading B.76(i) on each side of the cap

The degree-free counterparts of `B77a.lean`'s private helpers. -/

/-- Below the cap the truncated congruence is an honest equality. -/
private theorem eq_of_min_lt {a b : ℕ∞} {N : ℕ} (h : min a (N : ℕ∞) = min b (N : ℕ∞))
    (ha : a < (N : ℕ∞)) : b = a := by
  rw [min_eq_left ha.le] at h
  rcases min_cases b (N : ℕ∞) with ⟨hb, _⟩ | ⟨hb, _⟩
  · rw [hb] at h; exact h.symm
  · rw [hb] at h; exact absurd ha (by simp [h])

/-- At or above the cap the truncated congruence transports the bound. -/
private theorem le_of_min_le {a b : ℕ∞} {N : ℕ} (h : min a (N : ℕ∞) = min b (N : ℕ∞))
    (ha : (N : ℕ∞) ≤ a) : (N : ℕ∞) ≤ b := by
  rw [min_eq_right ha] at h
  exact h.trans_le (min_le_left b (N : ℕ∞))

/-- **The transport dichotomy.**  At every abscissa a level-`N` congruence either leaves the
Newton-polygon height unchanged, or leaves it at or above the cap on both sides. -/
private theorem npHgt_dich (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (j : ℕ) :
    npHgt φ f' j = npHgt φ f j ∨
      ((N : ℕ∞) ≤ npHgt φ f j ∧ (N : ℕ∞) ≤ npHgt φ f' j) := by
  have hmin := npHgt_min_congr hπ hφ hd hff' j
  rcases lt_or_ge (npHgt φ f j) (N : ℕ∞) with hlt | hge
  · exact Or.inl (eq_of_min_lt hmin hlt)
  · exact Or.inr ⟨hge, le_of_min_le hmin hge⟩

/-- Every capped abscissa contributes a support term at least `ℓ·N`. -/
private theorem cast_mul_le_term' {ℓ N c : ℕ} {x : ℕ∞} (hx : (N : ℕ∞) ≤ x) :
    ((ℓ * N : ℕ) : ℕ∞) ≤ ℓ • x + (c : ℕ∞) :=
  calc ((ℓ * N : ℕ) : ℕ∞) = ℓ • (N : ℕ∞) := by rw [nsmul_eq_mul, Nat.cast_mul]
    _ ≤ ℓ • x := nsmul_le_nsmul_right hx ℓ
    _ ≤ ℓ • x + (c : ℕ∞) := le_self_add

/-- **The window bound.**  A visible abscissa-`0` height puts the whole cleared support value
strictly below `ℓ·N`. -/
private theorem suppVal_lt_of_vis (hπ : Irreducible π) {φ : Polynomial O} {N : ℕ}
    {f : Polynomial O} (hvis : Visible π φ f N) {ℓ : ℕ} (hℓ : 0 < ℓ) (u : ℕ) :
    suppVal φ f u ℓ < ((ℓ * N : ℕ) : ℕ∞) := by
  have hvisN : npHgt φ f 0 < (N : ℕ∞) := (visible_iff_npHgt_lt hπ).1 hvis
  obtain ⟨H, hH⟩ : ∃ H : ℕ, (H : ℕ∞) = npHgt φ f 0 :=
    ENat.ne_top_iff_exists.1 (ne_top_of_lt hvisN)
  have hHN : H < N := by
    have hlt : (H : ℕ∞) < (N : ℕ∞) := hH ▸ hvisN
    exact_mod_cast hlt
  have hmem0 : 0 ∈ Finset.range (f.natDegree + 1) := Finset.mem_range.2 (Nat.succ_pos _)
  have hle : suppVal φ f u ℓ ≤ ((ℓ * H : ℕ) : ℕ∞) := by
    have hinf := Finset.inf_le (f := fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞)) hmem0
    simpa [suppVal, ← hH, nsmul_eq_mul] using hinf
  exact hle.trans_lt (by exact_mod_cast mul_lt_mul_of_pos_left hHN hℓ)

/-! ## §2 — the degree-free readings of `suppVal` and `sideSet`

These two lemmas are what replaces B.77's `hdeg`; see the module note. -/

/-- **Degree-free lower bound.**  The cleared support value is below the support term at
*every* abscissa, including those past `f.natDegree`, where the term is `⊤`. -/
private theorem suppVal_le_term {φ f : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {ℓ : ℕ} (hℓ : 0 < ℓ) (u j : ℕ) :
    suppVal φ f u ℓ ≤ ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) := by
  rcases Nat.lt_or_ge f.natDegree j with hj | hj
  · have htopterm : ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞) = ⊤ := by
      rw [npHgt_eq_top_of_lt hφ hd f hj]
      simp [nsmul_eq_mul, hℓ.ne']
    rw [htopterm]
    exact le_top
  · have hinf := Finset.inf_le (f := fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    simpa [suppVal] using hinf

/-- **Degree-free membership.**  At a finite cleared support value, an abscissa is on the side
exactly when it lies in `sideSet` — the `Finset.range (f.natDegree + 1)` carried by B.16's
definition is automatic. -/
private theorem mem_sideSet_iff {φ f : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (htop : suppVal φ f u ℓ ≠ ⊤) {j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ OnSide φ f u ℓ j := by
  classical
  refine ⟨onSide_of_mem_sideSet, fun hon => ?_⟩
  have hne : npHgt φ f j ≠ ⊤ := npHgt_ne_top_of_onSide hℓ htop hon
  have hjle : j ≤ f.natDegree := by
    by_contra hcon
    exact hne (npHgt_eq_top_of_lt hφ hd f (not_le.1 hcon))
  have hmem : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hjle), hon⟩
  exact hmem

/-! ## §3 — the degree-free transports -/

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- The congruence hypothesis is symmetric. -/
private theorem coeff_sub_symm {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (i : ℕ) : π ^ N ∣ (f' - f).coeff i := by
  have h := hff' i
  rw [Polynomial.coeff_sub] at h ⊢
  exact (dvd_sub_comm).1 h

/-- **Step 1, one direction.**  Under a level-`N` congruence with `f`'s polygon visible, the
cleared support value can only drop. -/
private theorem suppVal_le_of_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hvis : Visible π φ f N)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) : suppVal φ f' u ℓ ≤ suppVal φ f u ℓ := by
  classical
  have hmem0 : (0 : ℕ) ∈ Finset.range (f.natDegree + 1) := Finset.mem_range.2 (Nat.succ_pos _)
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf (Finset.range (f.natDegree + 1))
    ⟨0, hmem0⟩ (fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞))
  have hval : suppVal φ f u ℓ = ℓ • npHgt φ f j₀ + ((u * j₀ : ℕ) : ℕ∞) := hj₀
  rcases npHgt_dich hπ hφ hd hff' j₀ with h1 | ⟨h2, -⟩
  · calc suppVal φ f' u ℓ
        ≤ ℓ • npHgt φ f' j₀ + ((u * j₀ : ℕ) : ℕ∞) := suppVal_le_term hφ hd hℓ u j₀
      _ = ℓ • npHgt φ f j₀ + ((u * j₀ : ℕ) : ℕ∞) := by rw [h1]
      _ = suppVal φ f u ℓ := hval.symm
  · have hbig : ((ℓ * N : ℕ) : ℕ∞) ≤ suppVal φ f u ℓ :=
      (cast_mul_le_term' h2).trans_eq hval.symm
    exact absurd hbig (not_le.2 (suppVal_lt_of_vis hπ hvis hℓ u))

/-- **Step 1.**  The cleared support value is a function of the level-`N` class — with no
hypothesis relating `f.natDegree` and `f'.natDegree`. -/
private theorem suppVal_congr' (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hvis : Visible π φ f N)
    (hvis' : Visible π φ f' N) {u ℓ : ℕ} (hℓ : 0 < ℓ) :
    suppVal φ f' u ℓ = suppVal φ f u ℓ :=
  le_antisymm (suppVal_le_of_congr hπ hφ hd hff' hvis hℓ)
    (suppVal_le_of_congr hπ hφ hd (coeff_sub_symm hff') hvis' hℓ)

/-- **Step 2.**  The on-side abscissae are a function of the level-`N` class — again with no
degree hypothesis. -/
private theorem sideSet_congr' (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hvis : Visible π φ f N)
    (hvis' : Visible π φ f' N) {u ℓ : ℕ} (hℓ : 0 < ℓ) :
    sideSet φ f' u ℓ = sideSet φ f u ℓ := by
  classical
  have hlt : suppVal φ f u ℓ < ((ℓ * N : ℕ) : ℕ∞) := suppVal_lt_of_vis hπ hvis hℓ u
  have hlt' : suppVal φ f' u ℓ < ((ℓ * N : ℕ) : ℕ∞) := suppVal_lt_of_vis hπ hvis' hℓ u
  have hsupp : suppVal φ f' u ℓ = suppVal φ f u ℓ :=
    suppVal_congr' hπ hφ hd hff' hvis hvis' hℓ
  ext j
  rw [mem_sideSet_iff hφ hd hℓ (ne_top_of_lt hlt'), mem_sideSet_iff hφ hd hℓ (ne_top_of_lt hlt)]
  rcases npHgt_dich hπ hφ hd hff' j with h1 | ⟨h2, h2'⟩
  · simp only [OnSide, h1, hsupp]
  · constructor
    · intro hon
      exact absurd ((cast_mul_le_term' h2').trans_eq hon) (not_le.2 hlt')
    · intro hon
      exact absurd ((cast_mul_le_term' h2).trans_eq hon) (not_le.2 hlt)

/-! ## §4 — the endpoints, and the residual polynomial -/

/-- `Finset.min'` depends only on the set. -/
private theorem min'_congr' {s t : Finset ℕ} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by subst hst; rfl

/-- `Finset.max'` depends only on the set. -/
private theorem max'_congr' {s t : Finset ℕ} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.max' hs = t.max' ht := by subst hst; rfl

/-- `sideMin` transports along an equality of `sideSet`s. -/
private theorem sideMin_congr' {φ f f' : Polynomial O} {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) :
    sideMin φ f' u ℓ h' = sideMin φ f u ℓ h :=
  min'_congr' hset h' h

/-- `sideMax` transports along an equality of `sideSet`s. -/
private theorem sideMax_congr' {φ f f' : Polynomial O} {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) :
    sideMax φ f' u ℓ h' = sideMax φ f u ℓ h :=
  max'_congr' hset h' h

/-- `sideDeg` transports along an equality of `sideSet`s. -/
private theorem sideDeg_congr' {φ f f' : Polynomial O} {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) :
    sideDeg φ f' u ℓ h' = sideDeg φ f u ℓ h := by
  rw [sideDeg, sideDeg, sideMin_congr' hset h h', sideMax_congr' hset h h']

/-- **The digit lemma.**  Strictly inside the window a level-`N` congruence preserves every
digit. -/
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

/-- The digit lemma, coefficientwise. -/
private theorem digPoly_congr' (hπ : Irreducible π) {N k : ℕ} (hk : k < N) {a b : Polynomial O}
    (h : ∀ i, π ^ N ∣ (a - b).coeff i) : digPoly π k a = digPoly π k b := by
  refine Polynomial.ext fun i => ?_
  rw [digPoly_coeff hπ, digPoly_coeff hπ]
  refine digAt_congr' hπ hk ?_
  simpa only [Polynomial.coeff_sub] using h i

/-- The digit lemma, pushed into the residual field. -/
private theorem resMk_congr' (hπ : Irreducible π) {N k : ℕ} (hk : k < N) {φ a b : Polynomial O}
    (h : ∀ i, π ^ N ∣ (a - b).coeff i) : resMk π φ k a = resMk π φ k b := by
  rw [resMk, resMk, digPoly_congr' hπ hk h]

/-- Every residual coefficient of the side is read strictly inside the window, hence
transports. -/
private theorem resCoeff_congr' (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) {H₀ : ℕ} (hH₀ : H₀ < N) (k : ℕ) :
    resCoeff π φ f' u ℓ h' H₀ k = resCoeff π φ f u ℓ h H₀ k := by
  rw [resCoeff, resCoeff, sideMin_congr' hset h h']
  exact resMk_congr' hπ (lt_of_le_of_lt (Nat.sub_le H₀ (u * k)) hH₀)
    (dev_congr hπ hφ (coeff_sub_symm hff') (sideMin φ f u ℓ h + ℓ * k))

/-- **Step 4.**  The residual polynomial of the `(u,ℓ)`-side is a function of the level-`N`
class of `f`, for every read height `H₀ < N` — with no degree hypothesis. -/
private theorem resPoly_congr'' (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic) {N : ℕ}
    {f f' : Polynomial O} (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) {u ℓ : ℕ}
    (hset : sideSet φ f' u ℓ = sideSet φ f u ℓ) (h : (sideSet φ f u ℓ).Nonempty)
    (h' : (sideSet φ f' u ℓ).Nonempty) {H₀ : ℕ} (hH₀ : H₀ < N) :
    resPoly π φ f' u ℓ h' H₀ = resPoly π φ f u ℓ h H₀ := by
  rw [resPoly, resPoly, sideDeg_congr' hset h h']
  exact Finset.sum_congr rfl fun k _ => by
    rw [resCoeff_congr' hπ hφ hff' hset h h' hH₀ k]

/-! ## §5 — the read height is inside the window -/

/-- **The `H₀` bound.**  The height at a side's left endpoint — B.73's A-F.1/PA-1 pin — is
strictly inside the window whenever the polygon is visible.  This is what licenses the digit
lemma at every residual coefficient. -/
private theorem H₀_lt_of_visible (hπ : Irreducible π) {φ : Polynomial O} {N : ℕ}
    {f : Polynomial O} (hvis : Visible π φ f N) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (h : (sideSet φ f u ℓ).Nonempty) {H₀ : ℕ}
    (hH₀ : npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)) : H₀ < N := by
  have hon : OnSide φ f u ℓ (sideMin φ f u ℓ h) :=
    onSide_of_mem_sideSet (Finset.min'_mem _ _)
  have hone : ℓ • npHgt φ f (sideMin φ f u ℓ h) + ((u * sideMin φ f u ℓ h : ℕ) : ℕ∞)
      = suppVal φ f u ℓ := hon
  have hcast : ((ℓ * H₀ + u * sideMin φ f u ℓ h : ℕ) : ℕ∞) = suppVal φ f u ℓ := by
    rw [← hone, hH₀]
    push_cast [nsmul_eq_mul]
    ring
  have hlt : ((ℓ * H₀ + u * sideMin φ f u ℓ h : ℕ) : ℕ∞) < ((ℓ * N : ℕ) : ℕ∞) := by
    rw [hcast]
    exact suppVal_lt_of_vis hπ hvis hℓ u
  have hnat : ℓ * H₀ + u * sideMin φ f u ℓ h < ℓ * N := by exact_mod_cast hlt
  exact Nat.lt_of_mul_lt_mul_left (a := ℓ) (by omega)

/-! ## §6 — the signed transport -/

/-- One direction of B.74; the hypotheses are symmetric in `f`, `f'`. -/
private theorem needsDescent_imp (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hvis : Visible π φ f N)
    (hvis' : Visible π φ f' N) : NeedsDescent π φ f → NeedsDescent π φ f' := by
  rintro ⟨u, ℓ, h, H₀, hℓ, hcop, hcard, hH₀, hsep⟩
  have hset : sideSet φ f' u ℓ = sideSet φ f u ℓ :=
    sideSet_congr' hπ hφ hd hff' hvis hvis' hℓ
  have h' : (sideSet φ f' u ℓ).Nonempty := by rw [hset]; exact h
  have hH₀N : H₀ < N := H₀_lt_of_visible hπ hvis hℓ h hH₀
  have hmin : sideMin φ f' u ℓ h' = sideMin φ f u ℓ h := sideMin_congr' hset h h'
  have hnp : npHgt φ f' (sideMin φ f' u ℓ h') = (H₀ : ℕ∞) := by
    rw [hmin]
    rcases npHgt_dich hπ hφ hd hff' (sideMin φ f u ℓ h) with h1 | ⟨h2, -⟩
    · rw [h1]; exact hH₀
    · rw [hH₀] at h2
      have : N ≤ H₀ := by exact_mod_cast h2
      omega
  refine ⟨u, ℓ, h', H₀, hℓ, hcop, by rw [hset]; exact hcard, hnp, ?_⟩
  rw [resPoly_congr'' hπ hφ hff' hset h h' hH₀N]
  exact hsep

section ENVC
-- ENV-C.  Neither instance is consumed by the proof; both are kept so that the binder list
-- matches the frozen stub (`leanspec/Leanspec/ChapB.lean`, **B.74**).
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

set_option linter.unusedSectionVars false in
/-- **B.74 — the descent trigger is decidable from the window.**  `NeedsDescent π φ f` depends
only on the development coefficients at the on-side abscissae and on their digits at the
side-line heights — each side's residual read entering at the side's left endpoint, `H₀` with
`npHgt φ f (sideMin φ f u ℓ h) = (H₀ : ℕ∞)` (the A-F.1/PA-1 pin; on-side heights are then
`H₀ − u·k` counted from `sideMin`, all *on* the side's line).  Consequently it is determined
by `f mod π ^ N` for every `N` that the polygon is visible at.

*(`Visible` is B.75.)*  See the module note for why the landed B.77 clauses are not cited:
they carry a degree hypothesis this signature does not supply, and the transports are
re-derived degree-free above. -/
theorem needsDescent_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ) {N : ℕ}
    {f f' : Polynomial O} (hff' : ∀ i, π ^ N ∣ (f - f').coeff i)
    (hvis : Visible π φ f N) : NeedsDescent π φ f ↔ NeedsDescent π φ f' := by
  have hvis' : Visible π φ f' N := (visible_congr hπ hφ.monic hφ.pos hff').1 hvis
  exact ⟨needsDescent_imp hπ hφ.monic hφ.pos hff' hvis hvis',
    needsDescent_imp hπ hφ.monic hφ.pos (coeff_sub_symm hff') hvis' hvis⟩

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.needsDescent_congr
end AxCheck
