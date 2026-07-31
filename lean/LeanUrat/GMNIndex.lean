/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesX.KE8

/-! # GMNIndex — the AX-GMN-INDEX statement DRAFT (M15 dual-LITERATURE)

**STATUS: NOT-YET-DECLARED. This file contains NO axiom.** It is the drafted
statement SHAPE of the pending literature axiom **AX-GMN-INDEX**
(faithfulness entry: `docs/AXIOM_FAITHFULNESS.md` §AX-GMN-INDEX, DRAFT
2026-07-31, PENDING guardian audit), plus the machine-checked consumption
seam showing the shape covers EXACTLY the `finsum_le` field of the KE8
carrier `GmnOrderAccounting` and NOTHING else.

## The citation (pinned by both twins)

Guàrdia–Montes–Nart, *Newton polygons of higher order in algebraic number
theory*, Trans. Amer. Math. Soc. 364 (2012), no. 1, 361–416
(arXiv:0807.2620v2): **Theorem 4.18(1)** ("theorem of the index",
ind(f) ≥ ind₁(f) + ⋯ + ind_r(f) for monic separable f over O) with
**Definitions 4.11** (ind(f)), **4.12** (ind of a side/polygon), **4.15**
(higher-order ind_t/ind_r, keyed to a "universally fixed family" of
representatives — the §4.2 standing convention) and **Remark 4.14**
(nonnegativity: ind is a lattice-point count).  Sources: the Fable twin
`lean/notes/openmath/M15-x1a-align-gmn_fable.md` (incl. the 1548-case
`ind2` = 2·ind(S) dictionary check N1) and the Codex twin
(`/tmp/openmath/M15-x1a-align-gmn_codex.jsonl`, VERDICT LITERATURE).

## Why the `axiom` keyword is withheld (the honest deferral)

The intended declaration (displayed below) is about two engine-side
definitions that DO NOT EXIST YET:

* `gmnInd p f : ℕ` — Def 4.11 at O = ℤ_p (the v-index of f);
* `gmnOrderInd p f r : ℕ` — Def 4.15's ind_r(f) at the ENGINE'S pinned
  representative family (value 0 at r = 0); per Def 4.15's explicit warning,
  ind_t(f) depends on the choice of representatives, so the constant is
  well-defined ONLY relative to that pinned family.

Declaring the axiom today would mean declaring those constants `opaque`,
and an axiom over opaque constants is NOT a faithful transcription of
Thm 4.18(1): it is satisfied by the all-zero functions
(`face_zero_witness` below, machine-checked) and so imports either nothing
or — once the constants are later given bodies — an UNAUDITED bridge from
the bodies to the paper.  Per the task instruction ("if any doubt, leave it
as a displayed def + TODO and say so"): there is doubt, so this file ships
the SHAPE as a `def` and the declaration text as a display.

## The pending declaration (text on record; DO NOT DECLARE without the gates)

Once `gmnInd`/`gmnOrderInd` are BUILT (real definitions, not opaque), the
declaration is, verbatim:

```
-- [CITE] GMN TAMS 364 (2012) 361–416 (arXiv:0807.2620v2) Thm 4.18(1)
-- + Def 4.15 (nonnegativity, per-order ind_r) + Def 4.11 (ind), keyed to
-- the engine's pinned representative family (§4.2 "universally fixed").
axiom AX_GMN_index_finsum (n p : ℕ) [Fact p.Prime] (f : MonicBox n p)
    (hdz : f ∉ discZero n p) (R : Finset ℕ) :
    ∑ r ∈ R, gmnOrderInd p f r ≤ gmnInd p f
```

GATES before the declaration (in order):
1. `gmnInd`/`gmnOrderInd` built as real definitions, with the engine's
   representative family pinned (residual item OL-3 of the faithfulness
   entry);
2. guardian audit of AX-GMN-INDEX passes (`docs/AXIOM_FAITHFULNESS.md`
   entry is DRAFT — the audit is the declared gate, run separately);
3. Asvin sign-off (axiom policy: citation + faithfulness entry + audit).

## The over-scoping trap (both twins, independently)

Do NOT declare `∀ p, Nonempty (GmnOrderAccounting n p (X.gmn p))` as the
axiom.  The carrier's `place`/`place_inj`/`place_charged` fields are the
ALIGN-inc placement duty — engine-side facts the paper never asserts
(residual items OL-1/OL-2/OL-4 = the Codex twin's "Open Lemma L").  The
seam theorems below make the split machine-checked: the literature face
discharges `finsum_le` ONLY; every other field enters as an explicit
hypothesis.
-/

namespace LeanUrat.GMNIndexAxiom

open LeanUrat.MovesX

set_option linter.style.longLine false
-- The `place` hypotheses below keep the binder spelling of the KE8 carrier
-- fields VERBATIM (including the unused `f` binder), per the statement-fence
-- discipline; KE8 silences the same lint for the same reason.
set_option linter.unusedVariables false

/-- **AX-GMN-INDEX statement shape (NOT-YET-DECLARED).**  The finite-sum face
of GMN Thm 4.18(1) + Def 4.15, parameterized over the not-yet-built
engine-side definitions `gmnInd` (Def 4.11) and `gmnOrderInd` (Def 4.15 at
the engine's pinned representative family): for every prime, every monic
degree-`n` `f` over `ℤ_[p]` off the discriminant-zero locus, and every
FINITE set `R` of orders, `∑_{r ∈ R} ind_r(f) ≤ ind(f)`.  (Finite-sum form:
`ind_r(f) ≥ 0` for all `r` by Remark 4.14/Def 4.15, so Thm 4.18(1) at
`r = max R` dominates any finite subfamily — and summability is never
needed.)  The pending axiom asserts exactly `GmnIndexFinsumFace n gmnInd
gmnOrderInd` for the REAL `gmnInd`/`gmnOrderInd`; see the file header for
the gates. -/
def GmnIndexFinsumFace (n : ℕ)
    (gmnInd : ∀ (p : ℕ) [Fact p.Prime], MonicBox n p → ℕ)
    (gmnOrderInd : ∀ (p : ℕ) [Fact p.Prime], MonicBox n p → ℕ → ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p), f ∉ discZero n p →
    ∀ R : Finset ℕ, ∑ r ∈ R, gmnOrderInd p f r ≤ gmnInd p f

/-- **The vacuity witness (why the `axiom` keyword is deferred).**  The shape
is satisfied by the all-zero functions: an axiom of this shape over OPAQUE
constants would therefore import no content — the content lives entirely in
the DEFINITIONS of `gmnInd`/`gmnOrderInd`, which must be built and audited
BEFORE the declaration (gate 1 of the file header). -/
theorem face_zero_witness (n : ℕ) :
    GmnIndexFinsumFace n (fun _ _ _ => 0) (fun _ _ _ _ => 0) := by
  intro p _ f _ R
  simp

/-- **Consumption seam, per-prime leg.**  The literature face (`hface` — the
pending axiom's statement at one prime) + the `ind` instance pin (`hpin` —
the non-axiom engine identification `(X.gmn p).ind = gmnInd p`) + the THREE
placement duties (`place`/`place_inj`/`place_charged` — the residual
OL-1/OL-2/OL-4, engine-side, NOT covered by the citation) inhabit the KE8
carrier `GmnOrderAccounting`.  Machine-checks the AX-GMN-INDEX scoping: the
axiom face discharges `finsum_le` alone; all else stays a proof
obligation. -/
theorem orderAccounting_of_face (n p : ℕ) [Fact p.Prime] (G : GMNIndex n p)
    (gmnInd : MonicBox n p → ℕ) (gmnOrderInd : MonicBox n p → ℕ → ℕ)
    (hpin : ∀ f, G.ind f = gmnInd f)
    (hface : ∀ f : MonicBox n p, f ∉ discZero n p →
      ∀ R : Finset ℕ, ∑ r ∈ R, gmnOrderInd f r ≤ gmnInd f)
    (place : ∀ (f : MonicBox n p) (H : XHistory n),
      Fin (dCert ⟨true, false⟩ H) → ℕ)
    (place_inj : ∀ (f : MonicBox n p) (H : XHistory n), f ∉ discZero n p →
      G.inStratum f H → Function.Injective (place f H))
    (place_charged : ∀ (f : MonicBox n p) (H : XHistory n), f ∉ discZero n p →
      G.inStratum f H → ∀ j, 1 ≤ gmnOrderInd f (place f H j)) :
    Nonempty (GmnOrderAccounting n p G) :=
  ⟨{ orderInd := fun f => gmnOrderInd f
     finsum_le := fun f hdz R => (hface f hdz R).trans_eq (hpin f).symm
     place := place
     place_inj := place_inj
     place_charged := place_charged }⟩

/-- **Consumption seam, end-to-end.**  With the face at every prime plus the
placement duties at every prime, the target row `KT.cl15_align` — i.e.
`X1aAlignP n X ⟨true, false⟩` — follows through the PROVED KE8 reduction
`x1aAlignInc_of_orderAccounting`.  This displays the exact residual of the
M15 unit: everything in this theorem's hypothesis list EXCEPT `hface` is
engine-side work the citation does not cover (see the AX-GMN-INDEX entry's
residual reconciliation, items OL-1–OL-4). -/
theorem x1aAlignInc_of_face {n : ℕ} (X : XFamily n)
    (gmnInd : ∀ (p : ℕ) [Fact p.Prime], MonicBox n p → ℕ)
    (gmnOrderInd : ∀ (p : ℕ) [Fact p.Prime], MonicBox n p → ℕ → ℕ)
    (hpin : ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p),
      (X.gmn p).ind f = gmnInd p f)
    (hface : GmnIndexFinsumFace n gmnInd gmnOrderInd)
    (place : ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
      Fin (dCert ⟨true, false⟩ H) → ℕ)
    (place_inj : ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
      f ∉ discZero n p → (X.gmn p).inStratum f H →
        Function.Injective (place p f H))
    (place_charged : ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
      f ∉ discZero n p → (X.gmn p).inStratum f H →
        ∀ j, 1 ≤ gmnOrderInd p f (place p f H j)) :
    X1aAlignP n X ⟨true, false⟩ := by
  refine x1aAlignInc_of_orderAccounting X ?_
  intro p hp
  exact orderAccounting_of_face n p (X.gmn p) (gmnInd p) (gmnOrderInd p)
    (hpin p) (hface p) (place p) (place_inj p) (place_charged p)

end LeanUrat.GMNIndexAxiom
