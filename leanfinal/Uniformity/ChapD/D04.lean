/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D01

/-!
# Uniformity.ChapD.D04 — `varthetaEl`/`thetaEl`, the two telescope orientations at group level

**Chapter D, NODE D.04** [def] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern — this node's signature is unamended).
ENV-D2. Two public declarations, both definitional (the node's STATEMENT signs both
orientations as one node, because the pair is what the orientation discipline is about).

*The two telescope orientations, at the group level.* For a normalizer section `N` (D.01), a
ladder step `q : ℤ` and `s : ℕ`:

* `varthetaEl N q s := (n q)^s · (n (s·q))⁻¹` — **T1's orientation** (`(C2-vartheta)`,
  `EFF.T1.09`: numerator the TOP-STEP power `n̂(u)^s`, denominator the slot-height normalizer
  `n̂(su)`);
* `thetaEl N q s := n (s·q) · ((n q)^s)⁻¹` — **the B-law (inverse) orientation**
  (`(C3-Theta)`/`(T1-THETA)`: `Θ = ϑ⁻¹`).

The suffix `El` marks the group ELEMENT; the `K`-valued residues are D.08's `vartheta`/`theta`,
which apply D.07's `res` to these elements' value-zero membership witnesses. Nothing here is
`K`-valued and nothing here needs an arena: `EFF.T1.09`'s `K_iˣ` membership fence (proved only
at `i ∈ {1,2}`, `(H-VARTHETA-RES)_i` at `i ≥ 3`) does not bite on a group element, which is
exactly why the two definitions are split off into ENV-D2 and proved about once.

## ORIENTATION

**T1 two-index convention for `varthetaEl`; `thetaEl` is its inverse — rows 1–2 of D.06**
(anchor `D-THETA-TABLE`, the GC-14 canonical copy; this file states its convention and does not
restate the table). Two consequences a consumer must not lose:

* *the mutual inversion is a THEOREM, not a definitional identity.* `thetaEl q s ·
  varthetaEl q s = 1` is node D.06's `thetaEl_mul_varthetaEl`. This file defines the two
  elements independently, each as its source display spells it, so that D.06's inversion has
  content to check.
* *the slot reindexing is a CONSUMER's job.* `s = f_{i+1} − t` (T3's `Θ_i(t) := Θ_N(f_{i+1}−t;
  u_{i+1})`, `EFF.T3.04`) is applied at D.33/D.58 and never baked into these definitions. A
  reader who silently reads the argument `s` as a slot index `t` gets D.06 row 2 backwards —
  that is append #54's trap.

## Faithfulness

**⚠ Trust-boundary transcription.** Three points, flagged for the chapter cross-read:

* *`s : ℕ`, `q : ℤ`.* The source displays quantify `s ≥ 0` (`EFF.T3.03`: "For `s ≥ 0`") while
  the ladder step `q = u_{i+1}` and every height are integers (`EFF.T1.02`'s integrality
  clause, carried by D.01's `n : ℤ → G`). Typing `s` as `ℕ` is that quantifier, not a
  restriction: `(N.n q) ^ s` is the monoid power and `↑s * q` the integer height, so `N.n (s*q)`
  is evaluated at a genuine `ℤ` and the coercion is the only cast in the file.
* *the numerator/denominator assignment is the whole content.* `varthetaEl` puts the TOP-STEP
  power `n̂(u)^s` on top and the slot-height normalizer `n̂(su)` underneath — `EFF.T1.09`'s
  boxed fraction `n̂_i(u_{i+1})^s / n̂_i(su_{i+1})` — and `thetaEl` is the literal swap,
  `EFF.T3.04`'s `res(N(sq)/N(q)^s)`. Swapping either is undetectable by types and is precisely
  what D.06's executed involution and D.67's numeric leg exist to catch.
* *no residue, no `res`, no unit-group claim.* These are group elements of `G`, not `Kˣ`
  elements. Every membership/residue statement about them is D.07/D.08's
  (`varthetaEl_mem_ker`, `thetaEl_mem_ker`, `vartheta`, `theta`).

DEPENDS: D.01 (`NormSection`, landed at `Uniformity.ChapD.D01`). Nothing else — neither
definition consumes `n_zero`, and neither mentions D.02's `tau` (the recursion that ties them
together is D.05).

**PROOF.** Definitional. Both bodies are the gate-verified `leanspec/Leanspec/ChapD.lean` stub
bodies verbatim, with the blueprint's `namespace Uniformity.Density.Gauge` header restored (the
leanspec wrapper `LeanspecD` is a stub-side artifact; the landed namespace assignment is
`Uniformity.Density.Gauge`, GC-6.2).

SOURCE: `EFF.T1.09` (the boxed `(C2-vartheta)` — the fraction `n̂_i(u_{i+1})^s /
n̂_i(su_{i+1})`); `EFF.T3.03` (`ϑ_N(s;q) := res(N(q)^s / N(sq))`, "Fix a ladder step
`q = u_{i+1}`. For `s ≥ 0`…"); `EFF.T3.04` (`Θ_N(s;q) := ϑ_N(s;q)⁻¹ = res(N(sq)/N(q)^s)`, the
`(T1-THETA)` display, plus the slot substitution `s = f_{i+1} − t`); `EFF.T1.14`
(`(C3-Theta)`).

**TEETH.** T1's "inverse-orientation tooth" (`EFF.T1.11/.14/.15` TEETH) → Lean theorem at D.10
+ gate D.67; the group-level involution → D.06. Nothing to score at this node (two
definitions), and that is the point: the definitions are what the batteries score AGAINST.

ENVIRONMENT: ENV-D2 (`{G : Type*} [CommGroup G]`, written inline per the B.42 binder rule —
this file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- T1's telescope orientation: the group element under `ϑ_{i,s} = res(n̂(u)^s / n̂(su))`
(`EFF.T1.09` `(C2-vartheta)`).
ORIENTATION: T1 two-index; see D.06 (`D-THETA-TABLE`). -/
def NormSection.varthetaEl {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) (s : ℕ) : G :=
  (N.n q) ^ s * (N.n (s * q))⁻¹

/-- The B-law orientation `Θ_N(s;q) = ϑ_N(s;q)⁻¹` (`EFF.T3.04` `(T1-THETA)`, `EFF.T1.14`
`(C3-Theta)`). ORIENTATION: inverse of `varthetaEl`; see D.06. -/
def NormSection.thetaEl {G : Type*} [CommGroup G] (N : NormSection G) (q : ℤ) (s : ℕ) : G :=
  N.n (s * q) * ((N.n q) ^ s)⁻¹

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.NormSection.varthetaEl
#print axioms Uniformity.Density.Gauge.NormSection.thetaEl

end AxCheck
