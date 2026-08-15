/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H90 — invariant maintenance along a chain (`e₁ = 2`)

**Chapter H, NODE H.90** (`blueprint/CHAP-H_general_induction.md` §12; source `EFF.GENH4.24`).
*Invariant maintenance along a chain at `e₁ = 2`.* Two clauses, one per parity of the refinement
depth `dμ`:

* **(i) genre E, even `dμ`.** The refine adds `ŝ·π^(dμ/2)` to `p₀`, and the even floor
  `dμ ≥ 2h+2` gives `dμ/2 ≥ h+1`: the added term is strictly deeper than `v(p₀) = h`, so the
  exact invariant `v(p₀) = h` (with residue `−z`) survives the refinement.
* **(ii) genre E, odd `dμ`.** The refine adds `ŝ·π^((dμ−h)/2)` to `p₁`, and the odd floor
  `dμ ≥ 2h+1` gives `(dμ−h)/2 ≥ (h+1)/2`: the invariant `v(p₁) ≥ (h+1)/2` survives.

Both floors are exactly the slot-string starts of H.46 (`EFF.GENH4.17`) — the invariant
maintenance and the slot geometry are the same arithmetic.

**⚠ WHY THIS TINY NODE IS LOAD-BEARING.** `EFF.GENH4.24`'s conditionality: this is *the induction
that makes every per-node lemma apply at every node* — without it, `EFF.GENH4.19`/`.21` (the
chapter's H.85/H.88/H.89 content) hold only at entry.  Every consumer of those at a *deep* history
node depends on this node, and it must be named in the `DEPENDS` of every chain-level statement.
It is the chapter-H analogue of chapter G's `G.30a`.

Both clauses are `ℕ`-arithmetic with floor division by `2`; `omega` decides them.

DEPENDS: H.46 (the two floors are the slot strings' starts) — no Lean-level import needed, the
statements are self-contained arithmetic.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.90 (i).** Genre E, even `dμ`: the even floor `dμ ≥ 2h+2` forces the refinement's
added term `π^(dμ/2)` strictly below the invariant level `v(p₀) = h`, i.e. `dμ/2 ≥ h+1`. -/
theorem invariant_even {dμ h : ℕ} (hd : 2 * h + 2 ≤ dμ) : h + 1 ≤ dμ / 2 := by
  omega

/-- **NODE H.90 (ii).** Genre E, odd `dμ`: the odd floor `dμ ≥ 2h+1` forces the refinement's added
term `π^((dμ−h)/2)` at least at the invariant level `v(p₁) ≥ (h+1)/2`. -/
theorem invariant_odd {dμ h : ℕ} (hd : 2 * h + 1 ≤ dμ) : (h + 1) / 2 ≤ (dμ - h) / 2 := by
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.invariant_even
#print axioms Uniformity.Density.Induction.invariant_odd

end AxCheck
