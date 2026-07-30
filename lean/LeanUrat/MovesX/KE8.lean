/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.MovesX.Defs

/-! # KE8 — [ATTEMPT] ALIGN-inc: `X1aAlignP ⟨true, false⟩` from the GMN order accounting

BRIDGE CAMPAIGN unit **KE8** (area BP4, cluster c3; blueprint
`lean/notes/BRIDGE_BP4_KERNELS_2026-07-30.md` §3.E (E-vii) + §4 KE8).
E-PHASE STATEMENT MODULE — statement with `sorry` body.

THE KERNEL: `X1aAlignP n X ⟨true, false⟩` (MovesX/Defs.lean) — the (ALIGN-inc)
discharge state: `d_cert(H) ≤ ind(f)` on every stratum off `discZero`, with
`d_cert` counting ONLY the inc-certified T1/T2 nodes (reading A/(CD) pinning,
task-58 adjudication: row-0 = no bound certified — the pinning is BUILT INTO
`dCert ⟨true, false⟩`, so every consumer here is (CD)-compliant by type).

THE PAPER MECHANISM (MOVES_2026-07-24.md:11138-11151, the X.1a assembly):
certified nodes occupy DISTINCT ORDERS `r₁ < r₂ < …` (ALIGN places them), each
order contributing `ind_r(f) ≥ ind_t(f) ≥ f₀⋯f_{r−1} ≥ 1`; GMN Thm 4.18(1)
sums over ALL orders, so `ind(f) ≥ d_cert(H)` per branch (lower bounds are
F1-safe — other branches only help).

RECORDED RESOLUTIONS:
1. ⚑ `GmnOrderAccounting` is the NAMED CARRIER (Q4 shape) refining the frozen
   `GMNIndex` surface (which has only `ind`/`inStratum`/`p2`) with exactly the
   two consumed GMN facts: the FINITE-SUM face of Thm 4.18(1)/Cor 4.19
   (`finsum_le` — every finite set of per-order contributions is dominated by
   `ind f`; finite form avoids summability) and the ALIGN-inc PLACEMENT duty
   (`place`/`place_inj`/`place_charged` — the certified nodes injectively
   occupy orders of contribution ≥ 1; this is the D.0-to-Def-2.5 normalization
   crossing, the sub-clause (ALIGN-inc) names as its duty). Inhabiting the
   carrier at the real engine consumes the DECLARED GMN cite
   (`OM/Classifier` Cor 4.19 CITE axioms — allowed, already trusted) — that
   instance leg is instantiation-area work, not this unit's.
2. The unit's own Lean content is the "general assembly is D.12-transport
   BOOKKEEPING" leg: `dCert st H = card (Fin (dCert st H)) ≤
   Σ_{r ∈ image place} orderInd f r ≤ ind f` (injectivity converts the count
   to a finite sum over the placed orders; `finsum_le` closes).

deps: KE13 (CM gate — the ALIGN transport row-check probe runs FIRST; a
violating T0-T5 row pins the failing transport row before any prover runs);
X1a table units (MovesX XA/XB, built) for the eventual instance leg. Fallback:
the per-row obstruction record (which table row's transport fails). Consumers:
`X3aRouteP`'s right disjunct via KD5, XG3's route hypothesis.
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

/-- **KE8 named carrier (⚑ ratification)** — the D.12-transported GMN order
accounting over one prime's `GMNIndex`:
* `orderInd f r` — the order-`r` index contribution `ind_r(f)` (normalized
  coordinates, Thm 4.18's own bookkeeping);
* `finsum_le` — Thm 4.18(1)'s lower-bound face: any FINITE set of orders'
  contributions is dominated by `ind f` (off `discZero`);
* `place`/`place_inj`/`place_charged` — the (ALIGN-inc) duty: on any stratum
  history, the inc-certified nodes (the `dCert ⟨true, false⟩` population)
  injectively occupy orders each contributing ≥ 1.
Instance leg = the declared GMN cite + the ALIGN-inc normalization crossing;
owner: the instantiation area (OM engine side). -/
structure GmnOrderAccounting (n p : ℕ) [Fact p.Prime] (G : GMNIndex n p) where
  orderInd : MonicBox n p → ℕ → ℕ
  finsum_le : ∀ f : MonicBox n p, f ∉ discZero n p →
    ∀ R : Finset ℕ, ∑ r ∈ R, orderInd f r ≤ G.ind f
  place : ∀ (f : MonicBox n p) (H : XHistory n),
    Fin (dCert ⟨true, false⟩ H) → ℕ
  place_inj : ∀ (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → G.inStratum f H → Function.Injective (place f H)
  place_charged : ∀ (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → G.inStratum f H →
      ∀ j, 1 ≤ orderInd f (place f H j)

/-- **KE8 [ATTEMPT]** — the (ALIGN-inc) discharge: `X1aAlignP n X ⟨true, false⟩`
from an order accounting at every prime. Sketch (resolution 2): the injective
placement turns `dCert ⟨true, false⟩ H` into a sum of per-order charges ≥ 1
over the image finset; `finsum_le` dominates that sum by `ind f`.
deps: KE13 (gate — runs FIRST), `GmnOrderAccounting` (⚑). -/
theorem x1aAlignInc_of_orderAccounting {n : ℕ} (X : XFamily n)
    (hacc : ∀ (p : ℕ) [Fact p.Prime],
      Nonempty (GmnOrderAccounting n p (X.gmn p))) :
    X1aAlignP n X ⟨true, false⟩ := by
  sorry

end LeanUrat.MovesX
