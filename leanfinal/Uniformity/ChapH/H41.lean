/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H38
import Uniformity.ChapH.H40

/-!
# Uniformity.ChapH.H41 — the quartic law audit

**Chapter H, NODE H.41** (`blueprint/CHAP-H_general_induction.md` §7). Turns `EFF.GENIND.99`'s
preregistered spot values for the two quartic laws — `lawE` (H.38, the e-first genre
`(q−1)q^{4N−5h−3}`) and `lawF` (H.40, the f-first genre `(q(q−1)/2)·q^{4N−10k−4}`) — into a single
machine-checked conjunction:

`lawE 2 6 1 = 65536`, `lawE 3 4 1 = 13122`, `lawE 5 3 1 = 2500`, `lawF 2 6 1 = 1024`,
`lawF 2 5 1 = 64`, and the row total `lawE 2 6 1 + lawF 2 6 1 = 66560`.

DEPENDS: H.38 (`lawE`), H.40 (`lawF`).

**⚠ WHY THE ROW TOTAL IS A CONJUNCT** (blueprint): `EFF.GENIND.99`'s audit closes with *"all
twenty-one preregistered spot values and all four tooth counts are re-derivable from the displayed
laws"*, and the row total `66,560` is the one figure **three** instruments agree on (P-3's tally,
the cost probe, and the sum of the two laws). Landing the sum as its own conjunct means a future
edit to either law breaks the audit loudly rather than silently rebalancing.

Recomputed fresh: `lawE 2 6 1 = 1·2^(24−5−3) = 2^16 = 65536`;
`lawE 3 4 1 = 2·3^(16−5−3) = 2·3^8 = 13122`; `lawE 5 3 1 = 4·5^(12−5−3) = 4·5^4 = 2500`;
`lawF 2 6 1 = 1·2^(24−10−4) = 2^10 = 1024`; `lawF 2 5 1 = 1·2^(20−10−4) = 2^6 = 64`;
`65536 + 1024 = 66560`. Each of the five spots sits **above** its genre's visibility floor
(H.38's `2h + 1 ≤ N`: `3 ≤ 6`, `3 ≤ 4`, `3 ≤ 3`; H.40's `4k + 1 ≤ N`: `5 ≤ 6`, `5 ≤ 5`), so no
`ℕ`-subtraction truncates and the audited values are the honest loci.

SOURCE: `EFF.GENIND.99` (`E4(1) = 65,536`, `F4(1) = 1,024`, CS total `66,560` at `(·,2,6,n4)`;
`E4(1) = 13,122` at `(·,3,4,n4)`; `E4(1) = 2,500` at `(·,5,3,n4)`); `EFF.GENIND.163`/`R4.2`
(`lawF 2 5 1 = 64`).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.41.** The quartic law audit: `EFF.GENIND.99`'s preregistered spot values for the two
quartic laws, plus the `(·,2,6,n4)` row total that three independent instruments agree on. -/
theorem quartic_law_audit :
    lawE 2 6 1 = 65536 ∧ lawE 3 4 1 = 13122 ∧ lawE 5 3 1 = 2500 ∧
    lawF 2 6 1 = 1024 ∧ lawF 2 5 1 = 64 ∧ lawE 2 6 1 + lawF 2 6 1 = 66560 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.quartic_law_audit

end AxCheck
