/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B10
import Uniformity.ChapB.B11
import Uniformity.ChapB.B75

/-!
# Uniformity.ChapB.B76 — the visibility calculus

**Chapter B, NODE B.76** (`blueprint/CHAP-B_leaf_layer.md` §9), ENV-A′.  Five public
declarations, one object: the calculus of B.75's `Visible π φ f N` and its transport engine.

* `npHgt_min_congr` — **the truncation congruence**, `GENHN-3(a)` at `e₁ = 1`.  If `π ^ N`
  divides every coefficient of `f - f'`, then for every abscissa `j`

  ```
  min (npHgt φ f j) N  =  min (npHgt φ f' j) N        (in ℕ∞).
  ```

* `visible_iff_npHgt_lt` — the digit form of `Visible` equals the valuation form
  `npHgt φ f 0 < N`.
* `visible_mono` — `Visible` is monotone in the level `N`.
* `visible_congr` — `Visible` is invariant under `π ^ N`-congruence of `f`.
* `exists_visible` — some level sees `f` exactly when `dev φ f 0 ≠ 0`.

## Why clause (i) is `min`-truncated

The naive statement `npHgt φ f' j = npHgt φ f j` is **false** at heights `≥ N`: a level-`N`
congruence class contains lifts of every deeper height (R8-1's counterexample `A₀ = 5 ^ M` with
`M` unbounded lives exactly there).  The honest content is the pair "heights `< N` transport
exactly" + "heights `≥ N` transport as the bound `≥ N`", and the `min`-truncation is both of
those at once, in one rewritable equality — the form R8-1 consumes.

DEPENDS: B.02 (`dev`) · B.07 (`gaussVal`) · B.08 (`le_gaussVal_iff`, `gaussVal_eq_top_iff`) ·
B.10 (`dev_congr`) · B.11 (`npHgt`) · B.75 (`Visible`) · mathlib `ENat.ne_top_iff_exists`,
`min_lt_iff`, `pow_dvd_pow`.

**PROOF.**

1. (i) rests on the private one-sided lemma `min_gaussVal_le`: if `π ^ N` divides every
   coefficient of `a - b` then `min (gaussVal a) N ≤ min (gaussVal b) N`.  Its proof avoids any
   ultrametric API.  `min (gaussVal a) N ≤ N ≠ ⊤`, so `min (gaussVal a) N = (k : ℕ∞)` for a
   natural `k ≤ N`; then `π ^ k` divides every coefficient of `a` (B.08's `le_gaussVal_iff`, from
   `k ≤ gaussVal a`) and `π ^ k ∣ π ^ N` divides every coefficient of `a - b`, so `π ^ k` divides
   every coefficient of `b = a - (a - b)`, i.e. `k ≤ gaussVal b` — which with `k ≤ N` is
   `min (gaussVal a) N ≤ min (gaussVal b) N`.  Antisymmetry, with B.10's `dev_congr` in both
   directions, is (i).
2. (ii) `Visible` unfolds to `¬ ∀ i, π ^ N ∣ (dev φ f 0).coeff i` (`not_forall`), which is
   `¬ ((N : ℕ∞) ≤ gaussVal (dev φ f 0))` by B.08's `le_gaussVal_iff`, i.e. `npHgt φ f 0 < N`.
3. (iii) `π ^ M ∣ x → π ^ N ∣ x` for `N ≤ M` (`pow_dvd_pow`, `dvd_trans`); contrapose the witness.
4. (iv) `a < N ↔ min a N < N` (`min_lt_iff`), so (i) at `j = 0` transports the strict inequality;
   then (ii) twice.  *(This is where `hφ` enters, via B.10.)*
5. (v) `dev φ f 0 ≠ 0` gives `gaussVal (dev φ f 0) ≠ ⊤` (B.08's `gaussVal_eq_top_iff`), hence
   `= (H : ℕ∞)`; take `N := H + 1` and apply (ii).

**One signed hypothesis is not used by the proofs and is retained because the signature is
frozen** against the gate-verified stub (`leanspec/Leanspec/ChapB.lean`, **B.76a**/**B.76d**):
`hd : 0 < φ.natDegree`, in both `npHgt_min_congr` and `visible_congr` — the only place `φ` enters
either proof is B.10's `dev_congr`, which needs `hφ : φ.Monic` alone.  Likewise `visible_mono`
carries the auto-included `[IsDomain O]`, `[IsDiscreteValuationRing O]` that its statement does
not consume (`Visible` needs only `[CommRing O]`); they are kept, not `omit`ted, so the binder
list still matches the stub's, and only `linter.unusedSectionVars` is silenced.

**SOURCE.** `EFF.HE3.67` (R8-1 cites "LEMMA HE3-2(b) plus GENHN-3(a)"; this node is the
`GENHN-3(a)` half at `e₁ = 1`, with `dv = addVal` and cap `= N`); `spec/EFF-HE3.md` XREF ledger
(`GENHN-3(a)`, count 11); `EFF.W12.23` ("in-window, no truncation error").  The citation is
**through HE3's ledger, not through an EFF-GENHN unit**: chapter B's cut excludes GENHN, and the
proof above is self-contained, so nothing is consumed from GENHN beyond the name.

**TEETH.** `HE-T-CAP` (`EFF.HE3.54`, Q5: the reader variant that dropped out-of-window digits
disagrees with the sound reader on 17 (`p = 5`) + 43 (`p = 7`) members) → executable regression
retained: a live check that exactly the `min`-truncation, and nothing finer, survives the window.

ENVIRONMENT: ENV-A′ (ENV-A, with `hπ : Irreducible π` carried explicitly by the nodes that
need it).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The one-sided truncation bound -/

/-- **The engine of B.76(i), one-sided.**  If `π ^ N` divides every coefficient of `a - b`, then
`gaussVal a` and `gaussVal b` agree below the cap `N` — here, the `≤` half.

The proof uses no ultrametric API: `min (gaussVal a) N` is finite (it is `≤ N`), say `(k : ℕ∞)`
with `k ≤ N`, and then `π ^ k` divides every coefficient of `a` and of `a - b`, hence of `b`. -/
private theorem min_gaussVal_le (hπ : Irreducible π) {N : ℕ} {a b : Polynomial O}
    (h : ∀ i, π ^ N ∣ (a - b).coeff i) :
    min (gaussVal a) (N : ℕ∞) ≤ min (gaussVal b) (N : ℕ∞) := by
  refine le_min ?_ (min_le_right _ _)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℕ∞) = min (gaussVal a) (N : ℕ∞) :=
    ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.coe_ne_top N) (min_le_right _ _))
  have hkN : k ≤ N := by
    have : (k : ℕ∞) ≤ (N : ℕ∞) := by rw [hk]; exact min_le_right _ _
    exact_mod_cast this
  have hka : (k : ℕ∞) ≤ gaussVal a := by rw [hk]; exact min_le_left _ _
  rw [← hk]
  refine (le_gaussVal_iff hπ).2 fun i => ?_
  have h1 : π ^ k ∣ a.coeff i := (le_gaussVal_iff hπ).1 hka i
  have h2 : π ^ k ∣ (a - b).coeff i := dvd_trans (pow_dvd_pow π hkN) (h i)
  have hb : b.coeff i = a.coeff i - (a - b).coeff i := by
    rw [Polynomial.coeff_sub]; ring
  rw [hb]
  exact dvd_sub h1 h2

/-! ### (i) the truncation congruence -/

-- `hd : 0 < φ.natDegree` is part of the frozen signature and is not used; see the docstring.
set_option linter.unusedVariables false in
/-- **B.76(i) — the truncation congruence.**  A `π ^ N`-congruence of `f` moves no Newton-polygon
height below the cap `N`, and moves no height at or above `N` below it:

`min (npHgt φ f j) N = min (npHgt φ f' j) N` for every abscissa `j`.

Heights `< N` therefore transport *exactly*, and heights `≥ N` transport as the bound `≥ N`. -/
theorem npHgt_min_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) (j : ℕ) :
    min (npHgt φ f j) (N : ℕ∞) = min (npHgt φ f' j) (N : ℕ∞) := by
  have hsym : ∀ i, π ^ N ∣ (f' - f).coeff i := by
    intro i
    have h := hff' i
    rw [Polynomial.coeff_sub] at h ⊢
    exact (dvd_sub_comm).1 h
  exact le_antisymm (min_gaussVal_le hπ (dev_congr hπ hφ hff' j))
    (min_gaussVal_le hπ (dev_congr hπ hφ hsym j))

/-! ### (ii) the digit form and the valuation form agree -/

/-- **B.76(ii).**  B.75's digit definition of `Visible` is the valuation statement
`npHgt φ f 0 < N`. -/
theorem visible_iff_npHgt_lt (hπ : Irreducible π) {φ f : Polynomial O} {N : ℕ} :
    Visible π φ f N ↔ npHgt φ f 0 < (N : ℕ∞) := by
  rw [← not_le]
  change (∃ i, ¬ π ^ N ∣ (dev φ f 0).coeff i) ↔ ¬ ((N : ℕ∞) ≤ gaussVal (dev φ f 0))
  rw [le_gaussVal_iff hπ, not_forall]

/-! ### (iii) monotonicity in the level -/

-- `[IsDomain O]`, `[IsDiscreteValuationRing O]` are auto-included section variables that this
-- statement does not consume (`Visible` needs only `[CommRing O]`).  They are KEPT, so that the
-- binder list matches the frozen stub (`leanspec/Leanspec/ChapB.lean`, **B.76c**, whose `axiom`
-- includes them by the same rule); only the linter is silenced.
set_option linter.unusedSectionVars false in
/-- **B.76(iii).**  A wider window sees at least as much: `Visible` is monotone in `N`. -/
theorem visible_mono {φ f : Polynomial O} {N M : ℕ} (hNM : N ≤ M) :
    Visible π φ f N → Visible π φ f M := by
  rintro ⟨i, hi⟩
  exact ⟨i, fun hdvd => hi (dvd_trans (pow_dvd_pow π hNM) hdvd)⟩

/-! ### (iv) invariance under a level-`N` congruence -/

-- `hd : 0 < φ.natDegree` is part of the frozen signature and is not used; see the docstring.
set_option linter.unusedVariables false in
/-- **B.76(iv).**  Visibility at level `N` is a property of the level-`N` congruence class of
`f`: it is exactly the truncated height read of (i), below the cap. -/
theorem visible_congr (hπ : Irreducible π) {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) {N : ℕ} {f f' : Polynomial O}
    (hff' : ∀ i, π ^ N ∣ (f - f').coeff i) :
    Visible π φ f N ↔ Visible π φ f' N := by
  have key : ∀ x : ℕ∞, (x < (N : ℕ∞)) ↔ (min x (N : ℕ∞) < (N : ℕ∞)) := by
    intro x; simp
  rw [visible_iff_npHgt_lt hπ, visible_iff_npHgt_lt hπ, key (npHgt φ f 0), key (npHgt φ f' 0),
    npHgt_min_congr hπ hφ hd hff' 0]

/-! ### (v) some level is visible exactly when the constant development coefficient is nonzero -/

/-- **B.76(v).**  A nonzero constant development coefficient is seen by some window — and then by
every window deeper than its height. -/
theorem exists_visible (hπ : Irreducible π) {φ f : Polynomial O} (h0 : dev φ f 0 ≠ 0) :
    ∃ N : ℕ, Visible π φ f N := by
  obtain ⟨H, hH⟩ : ∃ H : ℕ, (H : ℕ∞) = gaussVal (dev φ f 0) :=
    ENat.ne_top_iff_exists.1 fun h => h0 (gaussVal_eq_top_iff.1 h)
  refine ⟨H + 1, (visible_iff_npHgt_lt hπ).2 ?_⟩
  change gaussVal (dev φ f 0) < ((H + 1 : ℕ) : ℕ∞)
  rw [← hH]
  exact_mod_cast Nat.lt_succ_self H

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.npHgt_min_congr
#print axioms Uniformity.Density.Leaf.visible_iff_npHgt_lt
#print axioms Uniformity.Density.Leaf.visible_mono
#print axioms Uniformity.Density.Leaf.visible_congr
#print axioms Uniformity.Density.Leaf.exists_visible
end AxCheck
