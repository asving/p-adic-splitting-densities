/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Group.Int

/-!
# Uniformity.ChapE.E10 — `SlotCarrier`, T2's slot layer S1.2–S1.4 as fields

**Chapter E, NODE E.10** (`blueprint/CHAP-E_sigma_ladder.md` §4). Over the standing bundle `O`
and a label field `K`, a **σ-ladder slot carrier** packages T2's slot layer as hypothesis
fields — the architecture `EFF.T2.39` itself prescribes ("The theorem assumes the explicit
quantitative consequences … These are source obligations, not conclusions obtained merely by
naming a carrier"):

* the key degree `D` with `hD : 0 < D`, and `(DEG-EF)` `D = e_𝒞 f_𝒞` as a FIELD
  (`EFF.T2.04` — explicitly not inferred from monicity);
* the height `hgt : Polynomial O → WithTop ℤ` and digit `dig : Polynomial O → K`, the
  ξ-independent data of `(SLOT-V)`/`(SLOT-R)` (`EFF.T2.05`), with `hgt 0 = ⊤`, `dig 0 = 0`, and
  finiteness/nonvanishing on nonzero sub-`D` polynomials;
* the ultrametric laws for `hgt` (`EFF.T2.04`, r12's valuation disclosure);
* digit additivity at a shared height (`EFF.HE7.96`(c)'s mechanism);
* the full-height predicate `Full : ℤ → Prop` and the lift law `(LIFT)`/`(OCC)` (`EFF.T2.09`) —
  lifts exist AT FULL HEIGHTS ONLY. There is no all-height lift hypothesis, and against this
  interface an all-height lift is not even expressible (this is the structural form of the S7
  sub-threshold / pass-2 refusal, which attacks exactly that).

DECISION D-E1 (blueprint): carrier heights are `WithTop ℤ`. `EFF.T2.05` declares `h(A) ∈ 𝐙` with
`h(0) = +∞`, and negative heights are real at raw normalizers (`EFF.HE7.05`'s `ϖ = x^{i₀}π^{a₀}`
with possibly `a₀ < 0`). This does not touch GC-2's `ℕ∞` ruling for chapter C's level-`r`
polygon heights; the reconciliation with B's `npHgt` is chapter C's, consumed as
`EFF.HE6R1.18 [supplied-by: chapter C]`.

NO-IRR fence (`EFF.T2.43`/`.44`, binding on every §4 signature): "Any later HE7 formalization
that requires irreducibility of the current key is not a formalization of this theorem." Nothing
here carries an irreducibility hypothesis.

FAITHFULNESS (the ξ-quantifier is deliberately absent — blueprint flag, standing for the codex
cross-read). `EFF.T2.05` states `(SLOT-V)`/`(SLOT-R)` as evaluation laws at every `ξ ∈ Pt ⊆ K̄₀`.
No algebraic closure exists in `leanfinal` (GC-7), so E's schema carries the ξ-INDEPENDENT
height/digit pair — exactly what the laws assert exists — and pushes every root-side consequence
into E.12's five clause-family fields, where the corpus itself carries them as source
obligations. At instances, `hgt`/`dig` are B's `digAt`-layer reads (B.21) on the `e₁ = 1` slice
and chapter C's normalizer reads above. The evaluation laws themselves are INSTANCE obligations,
exactly as in the corpus, and are never stated E-side.

Definitional, no proof obligation. Body reused verbatim from the gate-verified leanspec stub
(`leanspec/Leanspec/ChapE.lean`, the first of §12(a)'s FRAGILE signatures). The blueprint's
SPLIT CANDIDATE (peel the ultrametric-law pair into a mixin `HgtLaws` in `E10a`) was NOT taken:
elaboration is cheap here, and the split would fragment one corpus obligation suite.

DEPENDS: none (landed `Polynomial` API only). `[Finite K]` is deliberately OUT of the structure
(minimal binding, GC-6.4): only §7's dictionary counts need it.

SOURCE: `EFF.T2.04` (`(FINITE-RES)`, `(DEG-EF)`, the r12 valuation disclosure); `EFF.T2.05`
(`(SLOT-V)`/`(SLOT-R)`, `h(0) = +∞`, `dig(0) = 0`); `EFF.T2.09` (`(LIFT)`/`(OCC)`); `EFF.T2.10`
(fullness criteria — instances of `Full`, not fields).

ENVIRONMENT: ENV-E2 + `{K : Type*} [Field K]`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

/-- A **σ-ladder slot carrier** (T2 S1.2–S1.4, `EFF.T2.04`–`.10`): the ξ-independent
height/digit data with the ultrametric, lift, and additivity laws as fields. -/
structure SlotCarrier (O : Type*) [CommRing O] (K : Type*) [Field K] where
  /-- The current key degree `D > 0`. -/
  D : ℕ
  hD : 0 < D
  /-- Carrier invariants with `(DEG-EF)`: `D = e_𝒞 f_𝒞` (a hypothesis, never inferred). -/
  eC : ℕ
  fC : ℕ
  hef : D = eC * fC
  heC : 1 ≤ eC
  hfC : 1 ≤ fC
  /-- `h(A)`: the exact slot height (`SLOT-V`'s ξ-independent value); `h(0) = ⊤`. -/
  hgt : Polynomial O → WithTop ℤ
  /-- `dig(A)`: the exact slot digit (`SLOT-R`'s ξ-independent value); `dig 0 = 0`. -/
  dig : Polynomial O → K
  hgt_zero : hgt 0 = ⊤
  dig_zero : dig 0 = 0
  /-- nonzero sub-`D` polynomials have finite height and nonzero digit (`EFF.T2.05`). -/
  hgt_ne_top : ∀ A : Polynomial O, A ≠ 0 → A.natDegree < D → hgt A ≠ ⊤
  dig_ne_zero : ∀ A : Polynomial O, A ≠ 0 → A.natDegree < D → dig A ≠ 0
  /-- the ultrametric laws (`EFF.T2.04`, r12's valuation disclosure). -/
  hgt_add_ge : ∀ A B, min (hgt A) (hgt B) ≤ hgt (A + B)
  hgt_add_eq : ∀ A B, hgt A ≠ hgt B → hgt (A + B) = min (hgt A) (hgt B)
  /-- digit additivity at a shared height (residues at a fixed height are additive —
  `EFF.HE7.96`(c)'s mechanism). -/
  dig_add : ∀ A B : Polynomial O, ∀ k : ℤ,
      hgt A = (k : WithTop ℤ) → hgt B = (k : WithTop ℤ) → dig A + dig B ≠ 0 →
      hgt (A + B) = (k : WithTop ℤ) ∧ dig (A + B) = dig A + dig B
  /-- the full heights (`OCC`'s finite-domain obligation is the instances'). -/
  Full : ℤ → Prop
  /-- `(LIFT)`: at a full height every nonzero digit is realised (`EFF.T2.09`). -/
  hlift : ∀ k : ℤ, Full k → ∀ c : K, c ≠ 0 →
      ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < D ∧
        hgt A = (k : WithTop ℤ) ∧ dig A = c

end Uniformity.Density.Ladder

/-! ## Axiom footprint

The type former alone asserts nothing about the fields (every structure former ends in some
`Sort`), so the fragile fields are printed too: the two ultrametric laws, the additivity law and
the `Full`-gated lift. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.SlotCarrier
#print axioms Uniformity.Density.Ladder.SlotCarrier.mk
#print axioms Uniformity.Density.Ladder.SlotCarrier.hgt_add_ge
#print axioms Uniformity.Density.Ladder.SlotCarrier.hgt_add_eq
#print axioms Uniformity.Density.Ladder.SlotCarrier.dig_add
#print axioms Uniformity.Density.Ladder.SlotCarrier.hlift

end AxCheck
