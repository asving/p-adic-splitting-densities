/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H13

/-!
# Uniformity.ChapH.H15 — `alphaExp`, the α-locus exponent in transported coordinates

**Chapter H, NODE H.15** (`blueprint/CHAP-H_general_induction.md` §4). Defines the α(k)-locus's
free-digit exponent `alphaExp m W k = m * W + k * clusterC m`, where `W` is the **reduced window
minus one**, i.e. `W = N − 1 − m*k` for the α(k)-transport out of window `N`.

Definitional, no proof obligation. DEPENDS: H.13.

**⚠ COORDINATE CHOICE, AND WHY (the subtraction-free discipline)** (blueprint): the corpus's
displayed exponent is `m(N−1) − k·m(m+1)/2`, which carries two `ℕ`-subtractions (`N−1`, and the
whole exponent) that truncate silently below the admissibility bound `mk ≤ N−1`. Writing the
exponent in `W` makes every chapter-H α statement subtraction-free and makes the transport
identity H.17 **definitional**. The re-derivation is one line: with `N−1 = W+mk`, the `j`-th
summand of the corpus's slot count is `N−1−(m−j)k = W + jk`, so
`Σ_{j<m}(W+jk) = mW + k·Σ_{j<m}j = mW + k·c(m)`. H.16 lands both that slot count and the
reconciliation with the displayed form; chapter G used the same discipline (its `G23R*` route is
"subtraction-free" by design).

SOURCE: `EFF.GENIND.17` (the α-locus law `(Q−1)·Q^{m(N−1) − k·m(m+1)/2}` and its derivation as the
S2.2 slot count `Q^{Σ_j (N−1−(m−j)k)}`); `EFF.GENIND.21` (the ghost-fibre count
`Σ_{j<m} jk = k·m(m−1)/2 = k·c(m)` and the transported menu `(Q−1)·Q^{k·c(m)} ×` the window-`(N−mk)`
menu).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The α(k)-locus's free-digit exponent, written in the TRANSPORTED coordinate `W = N − 1 − mk`:
`alphaExp m W k = m·W + k·c(m)` — the reduced-window exponent plus the ghost exponent.  H.16
identifies it with `GENIND`'s displayed `m(N−1) − k·m(m+1)/2`. -/
def alphaExp (m W k : ℕ) : ℕ := m * W + k * clusterC m

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.alphaExp

end AxCheck
