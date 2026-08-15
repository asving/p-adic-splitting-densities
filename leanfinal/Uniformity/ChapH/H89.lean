/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Uniformity.ChapH.H89 — the consulted heights sit strictly inside the window (`(OB-a)` at `e₁ = 2`)

**Chapter H, NODE H.89** (`blueprint/CHAP-H_general_induction.md` §12; source `EFF.GENH4.21`,
`LEMMA GENH4-3`'s consulted-digit clause). *Every digit CONSULTED by any event sits strictly
inside its coordinate's window, at BOTH parities.* For `h ≥ 1`, `N ≥ 1`:

* **(i)** a RAM read at odd `u ≤ 2N−1` consults position `(u−h)/2 ≤ N−1`;
* **(ii)** a 2SIDED read at even `w ≤ 2N−2` consults position `w/2 ≤ N−1`;
* **(iii)** a SPLITEQ/INERT/REFINE read at `2dμ ≤ 2N−2` consults positions `dμ ≤ N−1` (in `S₁`)
  and `2dμ/2 ≤ N−1` (in `S₀`).

Consequently no read consults a height in the ragged band `[2N, 2N−2+h]`: the consulted ceiling
(the cap `2N`) lands below BOTH parities' window ends, which is the H-2(i) inequality re-run on
the ragged window of H.46.

**⚠ THIS IS `(OB-a)`'s DISCHARGE AT `e₁ = 2` AND ONLY THERE.** `EFF.GENIND.72` (`OB-a`) is the
chain-level window coherence in `dv`-units at *general* stages; `EFF.GENH4.21` discharges it at
the two quartic genres only.  The general case is `GENHN-CAP-GEN` (`EFF.GENHN.79`), whose Lean
form would need the reader formalized — it is not, so `CAP-GEN` has no node and its content sits
in `StageInterface`'s `hwin`.  **The `(OB-a)` disclosure at general stages is carried unchanged.**

**REPAIR RECORD [A-H.1/D8].** `band_not_consulted` as first committed carried no `1 ≤ N` guard
and was **machine-refuted at the stage-0e gate** at `(N, m) = (0, 0)`: the antecedent `2*0 ≤ 0`
holds while the conclusion `¬ (0 ≤ 2*0 − 1)` is `¬ (0 ≤ 0)` by `ℕ`-truncation, i.e. `False`.  The
`(hN : 1 ≤ N)` guard restored below is the one this node's own statement prose ("For `h ≥ 1`,
`N ≥ 1`") and all three sibling lemmas already carry (`consulted_ram` takes it explicitly), so the
omission was a transcription slip; the guarded form is verified on a 40 × 20 grid at the gate.

All four statements are `ℕ`-arithmetic with floor division by `2`; `omega` decides them.

DEPENDS: H.46 (the ragged band's definition and cardinality) — no Lean-level import needed, the
statements are self-contained arithmetic.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace Uniformity.Density.Induction

/-- **NODE H.89 (i).** A RAM read at odd height `u ≤ 2N−1` (with slot depth `h ≥ 1` and a
nonempty window `N ≥ 1`) consults the position `(u−h)/2`, which is at most the window end `N−1`. -/
theorem consulted_ram {u h N : ℕ} (hh : 1 ≤ h) (hu : u ≤ 2 * N - 1) (hN : 1 ≤ N) :
    (u - h) / 2 ≤ N - 1 := by
  omega

/-- **NODE H.89 (ii).** A 2SIDED read at even height `w ≤ 2N−2` consults the position `w/2`,
which is at most the window end `N−1`. -/
theorem consulted_twoSided {w N : ℕ} (hw : w ≤ 2 * N - 2) : w / 2 ≤ N - 1 := by
  omega

/-- **NODE H.89 (iii).** A SPLITEQ/INERT/REFINE read at height `2dμ ≤ 2N−2` consults `S₁` at
position `dμ`, which is at most the window end `N−1` (the `S₀` position `2dμ/2` is the same
number). -/
theorem consulted_refine {dμ N : ℕ} (hd : 2 * dμ ≤ 2 * N - 2) : dμ ≤ N - 1 := by
  omega

/-- **NODE H.89, the ledger.** No height in the ragged band `[2N, 2N−2+h]` is readable: a height
`m ≥ 2N` is never `≤ 2N−1`, the odd window end.  [repaired: A-H.1/D8 — the `1 ≤ N` guard is
load-bearing, `(N, m) = (0, 0)` refutes the unguarded form.] -/
theorem band_not_consulted {m N h : ℕ} (hN : 1 ≤ N) (hband : 2 * N ≤ m) : ¬ (m ≤ 2 * N - 1) := by
  omega

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.consulted_ram
#print axioms Uniformity.Density.Induction.consulted_twoSided
#print axioms Uniformity.Density.Induction.consulted_refine
#print axioms Uniformity.Density.Induction.band_not_consulted

end AxCheck
