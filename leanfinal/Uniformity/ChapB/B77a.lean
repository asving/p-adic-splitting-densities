/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B14
import Uniformity.ChapB.B16
import Uniformity.ChapB.B76

/-!
# Uniformity.ChapB.B77a — level stability, the polygon half

**Chapter B, NODE B.77** (`blueprint/CHAP-B_leaf_layer.md` §9), ENV-A′, **part (a) of the
mandated 2-way split** (steps 1–4 of the node's proof; `B77b.lean` carries step 5,
`resPoly_congr`).  Two signed declarations:

* `suppVal_congr` — the cleared support value `suppVal φ f u ℓ` is a function of the level-`N`
  congruence class of `f`, for **all** `u ℓ : ℕ` (no positivity, no coprimality), provided the
  polygon's abscissa-`0` height is inside the window (`hvis : Visible π φ f N`);
* `sideSet_congr` — the on-side abscissae `sideSet φ f u ℓ` likewise.  Since `sideMin`,
  `sideMax`, `sideDeg` (B.20) and `IsPure` (B.34) are built from `sideSet` and `OnSide`, they
  transport by rewriting along this equality; that is step 4, and it is recorded here rather
  than as separate contract declarations (B77b performs the `sideMin`/`sideDeg` rewrites it
  needs).

## Why `hvis` is not removable

Without a window hypothesis the statement is **false**: `f` and `f'` congruent mod `π ^ N` can
have wildly different polygons above height `N` (B.76's module note gives R8-1's family
`A₀ = 5 ^ M`, `M` unbounded).  `hvis` says the polygon's height at abscissa `0` is `< N`, which
pins the whole `inf` below `ℓ·N`: every abscissa whose height reaches the cap contributes a term
`≥ ℓ·N`, strictly above the value being computed, so it cannot participate in either `inf` — and
the abscissae below the cap have *equal* heights on both sides (B.76(i) read below `N`).  That
two-branch split is the whole proof, and it is `EFF.HE3.67`'s R8-1 clause 2 verbatim.

## The two readings of B.76(i)

`npHgt_min_congr` is a `min`-truncated equality; both of its readings are needed and both are
private helpers here:

* below the cap — `eq_of_min_eq_of_lt` : `min a N = min b N` and `a < N` force `b = a`;
* at or above it — `le_of_min_eq_of_le` : `min a N = min b N` and `N ≤ a` force `N ≤ b`.

Packaged as `npHgt_dichotomy`: for every abscissa `j`, either the two heights are *equal*, or
*both* reach the cap.

DEPENDS: B.02 (`dev`) · B.07/B.08 (`gaussVal`) · B.10 (`dev_congr`, through B.76) · B.11
(`npHgt`) · B.14 (`suppVal`) · B.16 (`OnSide`, `sideSet`) · B.75 (`Visible`) · B.76
(`npHgt_min_congr`, `visible_iff_npHgt_lt`) · mathlib `Finset.exists_mem_eq_inf`,
`Finset.inf_le`, `Finset.le_inf`, `nsmul_le_nsmul_right`, `ENat.ne_top_iff_exists`.

**PROOF.**

1. **Setup.**  `hvis` gives `npHgt φ f 0 = (H : ℕ∞)` with `H < N` (B.76(ii) plus
   `ENat.ne_top_iff_exists`).  The `inf` against the abscissa `0` then bounds the support value:
   `suppVal φ f u ℓ ≤ ℓ·H < ℓ·N` for `0 < ℓ` (`suppVal_lt_of_visible`).  The two `inf` ranges
   agree by `hdeg`.
2. **`suppVal`.**  `ℓ = 0` is degenerate: `0 • x = 0` makes both summand families literally the
   function `j ↦ u·j`, and `hdeg` equates the ranges — no hypothesis is used.  For `0 < ℓ`,
   `≤` and `≥` are proved separately.  `suppVal φ f u ℓ ≤ suppVal φ f' u ℓ` is pointwise
   (`Finset.le_inf`): at an abscissa in the equal-height branch the `f'`-term *is* an `f`-term,
   and at one in the capped branch the `f'`-term is `≥ ℓ·N >` the `f`-side value.  The reverse
   needs the `f`-side `inf` to be **attained** (`Finset.exists_mem_eq_inf`) at some `j₀`: the
   attained value is `< ℓ·N`, so `j₀` is in the equal-height branch, and the `f'`-term at `j₀`
   equals it.
3. **`sideSet`.**  Same dichotomy at the level of the defining equation: in the equal-height
   branch `OnSide φ f' u ℓ j` and `OnSide φ f u ℓ j` have identical left-hand sides and (by
   step 2) identical right-hand sides; in the capped branch both are false, each left-hand side
   being `≥ ℓ·N` and each right-hand side `< ℓ·N`.  `Finset.ext` plus `Finset.mem_filter`, with
   `hdeg` matching the filtered ranges.
4. **Step 4 of the node** (`sideMin`/`sideMax`/`sideDeg`/`IsPure`) is rewriting along step 3;
   no declaration of its own.

**SOURCE.** `EFF.W12.27` verbatim ("All data the read consumes sit at heights `≤ N−1`, so every
lift of the window class shares them"); `EFF.HE3.67` (R8-1 clause 2 — the two transport branches:
"read exactly below `c_ν`" is the equal-height branch, "known only to be `≥ c_ν` but
`c_ν > b_{ν,j}`" is the capped branch, where both terms leave the `inf`); `EFF.W12.84` step 2;
`spec/EFF-HE3.md` XREF `GENHN-3(a)` (consumed through B.76).

**TEETH.** `HE-T-CAP` (`EFF.HE3.54`, 17 + 43 members) → Lean theorem (this node, with B77b);
`HE-BND` (`EFF.HE3.55`, RE-SCOPED by R8-1) → executable regression, scored on aligned rows only.

**The signed hypothesis `hd : 0 < φ.natDegree` is not used** and is retained because the
signature is frozen against the gate-verified stubs (`leanspec/Leanspec/ChapB.lean`, **B.77a**,
**B.77b**): `φ` enters only through B.76, whose own proof needs `hφ : φ.Monic` alone (B.76's
module note records the same fact).  Only `linter.unusedVariables` is silenced.

ENVIRONMENT: ENV-A′ (ENV-A, with `hπ : Irreducible π` carried explicitly).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### Reading B.76(i) on each side of the cap -/

/-- Below the cap the truncated congruence is an honest equality: if `min a N = min b N` and
`a < N` then `b = a`. -/
private theorem eq_of_min_eq_of_lt {a b : ℕ∞} {N : ℕ} (h : min a (N : ℕ∞) = min b (N : ℕ∞))
    (ha : a < (N : ℕ∞)) : b = a := by
  rw [min_eq_left ha.le] at h
  rcases min_cases b (N : ℕ∞) with ⟨hb, _⟩ | ⟨hb, _⟩
  · rw [hb] at h; exact h.symm
  · rw [hb] at h; exact absurd ha (by simp [h])

/-- At or above the cap the truncated congruence transports the bound: if `min a N = min b N`
and `N ≤ a` then `N ≤ b`. -/
private theorem le_of_min_eq_of_le {a b : ℕ∞} {N : ℕ} (h : min a (N : ℕ∞) = min b (N : ℕ∞))
    (ha : (N : ℕ∞) ≤ a) : (N : ℕ∞) ≤ b := by
  rw [min_eq_right ha] at h
  exact h.trans_le (min_le_left b (N : ℕ∞))

/-- **The transport dichotomy.**  At every abscissa, a level-`N` congruence either leaves the
Newton-polygon height *unchanged*, or leaves it *at or above the cap* on both sides. -/
private theorem npHgt_dichotomy (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (j : ℕ) :
    npHgt φ f' j = npHgt φ f j ∨
      ((N : ℕ∞) ≤ npHgt φ f j ∧ (N : ℕ∞) ≤ npHgt φ f' j) := by
  have hmin := npHgt_min_congr hπ hφ hd hff' j
  rcases lt_or_ge (npHgt φ f j) (N : ℕ∞) with hlt | hge
  · exact Or.inl (eq_of_min_eq_of_lt hmin hlt)
  · exact Or.inr ⟨hge, le_of_min_eq_of_le hmin hge⟩

/-- Every capped abscissa contributes a support term at least `ℓ·N`. -/
private theorem cast_mul_le_term {ℓ N c : ℕ} {x : ℕ∞} (hx : (N : ℕ∞) ≤ x) :
    ((ℓ * N : ℕ) : ℕ∞) ≤ ℓ • x + (c : ℕ∞) :=
  calc ((ℓ * N : ℕ) : ℕ∞) = ℓ • (N : ℕ∞) := by rw [nsmul_eq_mul, Nat.cast_mul]
    _ ≤ ℓ • x := nsmul_le_nsmul_right hx ℓ
    _ ≤ ℓ • x + (c : ℕ∞) := le_self_add

/-- **The window bound.**  If the polygon's abscissa-`0` height is inside the window then the
whole cleared support value is strictly below `ℓ·N`. -/
private theorem suppVal_lt_of_visible (hπ : Irreducible π) {φ : Polynomial O} {N : ℕ}
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

/-! ### (a) the cleared support value transports -/

-- `hd : 0 < φ.natDegree` is part of the frozen signature and is not used; see the docstring.
set_option linter.unusedVariables false in
/-- **B.77, clause `suppVal`.**  The cleared support value of the `(u,ℓ)`-side depends only on
the level-`N` congruence class of `f`, once the window sees the polygon (`hvis`).  No positivity
and no coprimality is assumed of `(u, ℓ)`. -/
theorem suppVal_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hdeg : f'.natDegree = f.natDegree)
    (hvis : Visible π φ f N) (u ℓ : ℕ) :
    suppVal φ f' u ℓ = suppVal φ f u ℓ := by
  classical
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp only [suppVal, hdeg, zero_nsmul, zero_add]
  have hSlt : suppVal φ f u ℓ < ((ℓ * N : ℕ) : ℕ∞) := suppVal_lt_of_visible hπ hvis hℓ u
  have hmem0 : 0 ∈ Finset.range (f.natDegree + 1) := Finset.mem_range.2 (Nat.succ_pos _)
  refine le_antisymm ?_ ?_
  · -- the `f`-side `inf` is attained below the cap, and the `f'`-term there is the same
    obtain ⟨j₀, hj₀mem, hj₀⟩ := Finset.exists_mem_eq_inf (Finset.range (f.natDegree + 1))
      ⟨0, hmem0⟩ (fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞))
    have hval : suppVal φ f u ℓ = ℓ • npHgt φ f j₀ + ((u * j₀ : ℕ) : ℕ∞) := hj₀
    have hlow : npHgt φ f j₀ < (N : ℕ∞) := by
      by_contra hcon
      have hcon' : (N : ℕ∞) ≤ npHgt φ f j₀ := not_lt.1 hcon
      have hbig : ((ℓ * N : ℕ) : ℕ∞) ≤ suppVal φ f u ℓ :=
        (cast_mul_le_term hcon').trans_eq hval.symm
      exact absurd hbig (not_le.2 hSlt)
    have heq : npHgt φ f' j₀ = npHgt φ f j₀ := by
      rcases npHgt_dichotomy hπ hφ hd hff' j₀ with h1 | ⟨h2, _⟩
      · exact h1
      · exact absurd h2 (not_le.2 hlow)
    have hmem' : j₀ ∈ Finset.range (f'.natDegree + 1) := by rw [hdeg]; exact hj₀mem
    calc suppVal φ f' u ℓ
        ≤ ℓ • npHgt φ f' j₀ + ((u * j₀ : ℕ) : ℕ∞) :=
          Finset.inf_le (f := fun j => ℓ • npHgt φ f' j + ((u * j : ℕ) : ℕ∞)) hmem'
      _ = suppVal φ f u ℓ := by rw [heq]; exact hval.symm
  · -- pointwise: every `f'`-term is either an `f`-term or above the cap
    change suppVal φ f u ℓ
      ≤ (Finset.range (f'.natDegree + 1)).inf (fun j => ℓ • npHgt φ f' j + ((u * j : ℕ) : ℕ∞))
    refine Finset.le_inf fun j hj => ?_
    have hjmem : j ∈ Finset.range (f.natDegree + 1) := by rw [← hdeg]; exact hj
    rcases npHgt_dichotomy hπ hφ hd hff' j with h1 | ⟨_, h2⟩
    · rw [h1]
      exact Finset.inf_le (f := fun j => ℓ • npHgt φ f j + ((u * j : ℕ) : ℕ∞)) hjmem
    · exact hSlt.le.trans (cast_mul_le_term h2)

/-! ### (b) the on-side abscissae transport -/

-- `hd : 0 < φ.natDegree` is part of the frozen signature and is not used; see the docstring.
set_option linter.unusedVariables false in
/-- **B.77, clause `sideSet`.**  The on-side abscissae of the `(u,ℓ)`-side depend only on the
level-`N` congruence class of `f`.  Consequently `sideMin`, `sideMax`, `sideDeg` (B.20) and
`IsPure` (B.34), which are built from `sideSet` and `OnSide`, transport by rewriting. -/
theorem sideSet_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (hdeg : f'.natDegree = f.natDegree)
    (hvis : Visible π φ f N) (u ℓ : ℕ) :
    sideSet φ f' u ℓ = sideSet φ f u ℓ := by
  classical
  have hsupp : suppVal φ f' u ℓ = suppVal φ f u ℓ :=
    suppVal_congr hπ hφ hd hff' hdeg hvis u ℓ
  have hOn : ∀ j, OnSide φ f' u ℓ j ↔ OnSide φ f u ℓ j := by
    intro j
    rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
    · simp only [OnSide, zero_nsmul, zero_add, hsupp]
    have hSlt : suppVal φ f u ℓ < ((ℓ * N : ℕ) : ℕ∞) := suppVal_lt_of_visible hπ hvis hℓ u
    rcases npHgt_dichotomy hπ hφ hd hff' j with h1 | ⟨h2, h2'⟩
    · rw [OnSide, OnSide, h1, hsupp]
    · constructor
      · intro hon
        refine absurd ?_ (not_le.2 hSlt)
        have : ((ℓ * N : ℕ) : ℕ∞) ≤ suppVal φ f' u ℓ :=
          (cast_mul_le_term h2').trans_eq hon
        exact this.trans_eq hsupp
      · intro hon
        exact absurd ((cast_mul_le_term h2).trans_eq hon) (not_le.2 hSlt)
  ext j
  simp only [sideSet, Finset.mem_filter, Finset.mem_range, hdeg, hOn j]

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.suppVal_congr
#print axioms Uniformity.Density.Leaf.sideSet_congr
end AxCheck
