/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT

/-!
# Moves/L1_baseWeight_R3 — the base valuation is multiplicative (§B2-DEF D.2, base stage)

**Round-3 audit repair** of `L1.baseWeight`.  Introduces the base valuation

  `baseWeight φ e h f := min_i (e·v(aᵢ) + i·h)`

over the φ-adic development `f = Σ aᵢ·φⁱ` (`v = gaussVal`, the Gauss/content valuation from
`L1_gaussVal`), and states its multiplicativity on nonzero polynomials.  The `i`-th φ-adic
coefficient of `f` is extracted canonically as `(f /ₘ φⁱ) %ₘ φ` (monic `φ`), so no development
choice is needed and the definition elaborates without `Fact A`/`Fact B`.

## Faithfulness (trust boundary)

The definition is the sInf min-formula of §A.1 B1.1 (MOVES ~1995-1999): the set of slot weights
`{e·v(aᵢ) + i·h : aᵢ ≠ 0}` is nonempty and bounded below by `0` for `f ≠ 0` (each `v ≥ 0`,
`i·h ≥ 0`), so its `sInf` is attained.

## Honest gap (why the theorem body is `sorry`)

Multiplicativity `w(fg) = w(f) + w(g)` is the MacLane-augmentation valuation theorem: the
associated graded ring `gr = F_Q[π, y]` (deg π = e, deg y = h) is a polynomial ring over the
field `F_Q = 𝔽_{p^{deg φ}}` — a domain **exactly because** `φ̄` is irreducible (`hirred`), giving
`gcd(e,h)=1`, `hmon`, `hd`.  The `≥` direction is the ultrametric bound on the development of the
product; the `≤` direction is that the product of initial forms is nonzero in the domain `gr`.
Formalizing `gr` as a domain (the added hypotheses are exactly what makes it one) is the
outstanding work; the statement is TRUE under these hypotheses.  `sorry` is the honest placeholder
keeping the byte-identical MANIFEST_R3 statement — no new axioms, no statement weakening.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 400000

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-- The **Gauss valuation** `v(f) = min_i v_p(f.coeff i)` (inlined from `L1.gaussVal`, whose olean is
not yet on disk in this fan-out; identical definition). -/
private noncomputable def gaussVal {p : ℕ} [Fact p.Prime] (f : Polynomial ℤ_[p]) : ℤ :=
  if h : f.support.Nonempty then f.support.inf' h (fun i => (f.coeff i).valuation) else 0

/-- The base valuation `w(f) = min_i (e·v(aᵢ) + i·h)` over the φ-adic development `f = Σ aᵢ·φⁱ`
(D.2 base stage; `v = gaussVal`).  The `i`-th φ-adic coefficient is `(f /ₘ φⁱ) %ₘ φ`; the `sInf`
of the (nonempty, `0`-bounded-below) slot-weight set is the attained minimum. -/
noncomputable def baseWeight {p : ℕ} [Fact p.Prime] (φ : Polynomial ℤ_[p]) (e h : ℕ)
    (f : Polynomial ℤ_[p]) : ℤ :=
  sInf { m : ℤ | ∃ i : ℕ, ((f /ₘ φ ^ i) %ₘ φ) ≠ 0 ∧
            m = (e : ℤ) * gaussVal ((f /ₘ φ ^ i) %ₘ φ) + (i : ℤ) * (h : ℤ) }

theorem L1_baseWeight_valuation {p : ℕ} [Fact p.Prime] (φ : Polynomial ℤ_[p]) (e h : ℕ) (hmon : φ.Monic) (hd : 1 ≤ φ.natDegree) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.gcd e h = 1) (hirred : Irreducible (φ.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p))) (f g : Polynomial ℤ_[p]) (hf : f ≠ 0) (hg : g ≠ 0) : baseWeight φ e h (f * g) = baseWeight φ e h f + baseWeight φ e h g := by
  sorry

end LeanUrat.Moves
