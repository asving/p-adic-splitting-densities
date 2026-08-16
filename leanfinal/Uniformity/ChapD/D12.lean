/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D02

/-!
# Uniformity.ChapD.D12 — `NormSection.chi`, the section ratio and the coboundary `(T3-COB)`

**Chapter D, NODE D.12** [def+lemma] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, the abstract
cocycle arena; amendments A-1, A-D.1, A-D.2 govern — none of them re-signs this node, so the
SIGNATURE below is the one signed at composition and re-stubbed at stage 0e in
`leanspec/Leanspec/ChapD.lean`, whose `chi` body is reused here byte-for-byte). ENV-D2. Two
public declarations (the definition and its one lemma).

*The section ratio `χ` and the coboundary `(T3-COB)`.* For TWO normalizer sections
`N N̂ : NormSection G` on the same group and the same height set (`EFF.T3.12`'s "two normalized
exact-height sections on the same set of heights"):

  `χ(k) := n̂(k)·(n(k))⁻¹`,   `χ(a)·χ(b)·χ(a+b)⁻¹ = τ_{N̂}(a,b)·τ_N(a,b)⁻¹`.

The second display is `EFF.T3.16`'s boxed `(T3-COB)`: the failure of `χ` to be a character is
EXACTLY the ratio of the two cocycles, coboundary for coboundary.

## ⚠ The non-claim: NO character law for `χ` is assumed

`EFF.T3.16` states it and this node keeps it: "no character law for χ is assumed. It is a
character exactly when the two imported cocycles have equal residue." Nothing below asserts
`χ(a+b) = χ(a)χ(b)`, and no consumer may quietly use it. The fence is not editorial — the T3
battery exhibits an actual failure (`χ(1)·χ(1) = 1 ≠ 2 = χ(2)` at FRAME-C, gate D.67 leg 2), and
the same failure is EXECUTED at the bottom of this file as a two-line group-level witness, so
that the non-claim is machine-scored at its source and not merely written down. (The FRAME-C
instance itself — `χ(k) = 2^{⌊k/2⌋}` over `𝔽₅`, read through D.17's arena — is still owed by
D.67; this file's witness is its ENV-D2 shadow, in the exponent group, and does not discharge
it.)

## The naming fence (`chi` vs `tau`)

T3 renamed HETOW's one-argument `τ` to `χ` precisely to keep it apart from the two-argument
cocycle (`EFF.T3.12`), and D.02's faithfulness note records the obligation from the other side:
every two-argument cocycle in the chapter is `NormSection.tau`, and the ONE-argument pointwise
ratio is `NormSection.chi`. The two Lean names are distinct and neither aliases the other
(blueprint §0.3(ii)). Downstream, D.39's `GaugeArena.chiK` is the `K`-valued residue of THIS
`chi`, not a second definition of it.

## Faithfulness

**⚠ Trust-boundary definition.** `chi` is the pointwise quotient `n̂(k)/n(k)`, written `·⁻¹` in
the commutative group `G` — `EFF.T3.12`'s display verbatim. Three points for the cross-read:

* *argument order.* `chi Nhat N k` puts the HATTED section first, so `chi Nhat N = n̂/n`. The
  blueprint's SIGNATURE fixes this order (`(Nhat N : NormSection G)`), and D.39's `chiK` consumes
  it in that order. A swap inverts every downstream comparison.
* *no hypothesis relating the two sections.* Neither `chi` nor `chi_coboundary` assumes that `N`
  and `N̂` have equal heights: at ENV-D2 there are no heights at all. The "same set of heights"
  clause of `EFF.T3.12` is discharged by TYPING (both are `ℤ → G`), and the exact-height
  agreement enters only where it is needed — D.39's `hNhat`, which is what buys the
  kernel-membership for the residue.
* *`n_zero` unused.* The coboundary law is an identity of quotients and consumes neither
  section's normalization. It therefore holds for the raw maps; it is stated for `NormSection`
  because that is the carrier every consumer already has.

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

DEPENDS: D.01 (`NormSection`), D.02 (`NormSection.tau`) — both landed at
`Uniformity.ChapD.D01`/`D02`; mathlib `mul_inv`, `inv_inv` and the `ac_rfl` normalizer, all
name-verified at the v4.31.0 pin.

**PROOF.** The blueprint's, executed. Unfold `chi` and `tau`; `mul_inv`/`inv_inv` push every
inverse onto an atom, after which the two sides are the same six-atom product
(`n̂a, n̂b, n̂(a+b)⁻¹, na⁻¹, nb⁻¹, n(a+b)`) in different associations, closed by `ac_rfl`. The
corpus derivation is the displayed two-line residue computation (`EFF.T3.16`) — here at group
level; the residue image follows through D.07's `res` at consumers.

SOURCE: `EFF.T3.12` (`χ`'s definition and the renaming note), `EFF.T3.16` (the boxed `(T3-COB)`
plus "no character law for χ is assumed. It is a character exactly when the two imported cocycles
have equal residue").

**TEETH.** T3 §8.4(1), the "character mutant" → THIS Lean theorem (a mutant that replaces the
right-hand side by `1` is refuted by the executed witness below) + gate D.67's `χ(1)² ≠ χ(2)`
numeric leg over `𝔽₅`.

ENVIRONMENT: ENV-D2 (`{G : Type*} [CommGroup G]`, written inline per the B.42 binder rule — this
file has no `variable` block).

## Status

Sorry-free, axiom-free (Lean core only): `chi_coboundary` is a PROVED theorem here, not the
leanspec `axiom` stub.
-/

namespace Uniformity.Density.Gauge

/-- **D.12 (def) — the pointwise section ratio** (`EFF.T3.12`).  T3's `χ`, renamed from HETOW's
`τ` to avoid collision with the two-argument cocycle `NormSection.tau` — the spec's own renaming.
The HATTED section comes first: `chi Nhat N k = n̂(k)/n(k)`. -/
def NormSection.chi {G : Type*} [CommGroup G] (Nhat N : NormSection G) (k : ℤ) : G :=
  Nhat.n k * (N.n k)⁻¹

/-- **D.12 (lemma) — `(T3-COB)`, the coboundary law** (`EFF.T3.16`).  The failure of `χ` to be a
character is exactly the ratio of the two cocycles.  ⚠ NO character law for `χ` is asserted
anywhere: `χ` is a character precisely when the two cocycles agree, and the executed witness at
the foot of this file exhibits a pair where they do not. -/
theorem NormSection.chi_coboundary {G : Type*} [CommGroup G]
    (Nhat N : NormSection G) (a b : ℤ) :
    NormSection.chi Nhat N a * NormSection.chi Nhat N b * (NormSection.chi Nhat N (a + b))⁻¹
      = Nhat.tau a b * (N.tau a b)⁻¹ := by
  simp only [NormSection.chi, NormSection.tau, mul_inv, inv_inv]
  ac_rfl

end Uniformity.Density.Gauge

/-! ## The executed non-character witness (the ⚠ fence of `EFF.T3.16`, scored at its source)

The ENV-D2 shadow of FRAME-C's `χ(k) = 2^{⌊k/2⌋}` (gate D.67 leg 2, which runs the same numbers
over `𝔽₅` through D.17's arena): in the exponent group `Multiplicative ℤ`, take `N` trivial and
`n̂(k) := ofAdd ⌊k/2⌋`.  Then `χ(k) = ofAdd ⌊k/2⌋`, so `χ(1)·χ(1) = ofAdd 0 = 1` while
`χ(2) = ofAdd 1 ≠ 1` — the character law FAILS, by machine.  This is why `chi_coboundary` is
stated with a right-hand side and not with `1`.  The two sections are `private`: they are gate
data, not chapter API (the H.112/H.113 root-namespace-hygiene precedent). -/

section NonCharacterWitness

open Uniformity.Density.Gauge

/-- Gate data: the trivial section on the exponent group. -/
private def chiFenceBase : NormSection (Multiplicative ℤ) where
  n := fun _ => 1
  n_zero := rfl

/-- Gate data: the `⌊k/2⌋` section — the exponent shadow of FRAME-C's `n̂(k) = 2^{⌊k/2⌋}`. -/
private def chiFenceHat : NormSection (Multiplicative ℤ) where
  n := fun k => Multiplicative.ofAdd (k / 2)
  n_zero := rfl

/-- EXECUTED: `χ(1)·χ(1) ≠ χ(2)`.  `χ` is NOT a character (`EFF.T3.16`'s fence). -/
example :
    NormSection.chi chiFenceHat chiFenceBase 1 * NormSection.chi chiFenceHat chiFenceBase 1
      ≠ NormSection.chi chiFenceHat chiFenceBase 2 := by
  simp only [NormSection.chi, chiFenceHat, chiFenceBase, inv_one, mul_one]
  decide

/-- EXECUTED: the same pair satisfies `(T3-COB)` at `a = b = 1` with a NON-trivial right-hand
side — the two cocycles genuinely differ there, which is the whole content of the fence. -/
example :
    NormSection.chi chiFenceHat chiFenceBase 1 * NormSection.chi chiFenceHat chiFenceBase 1
        * (NormSection.chi chiFenceHat chiFenceBase (1 + 1))⁻¹
      = chiFenceHat.tau 1 1 * (chiFenceBase.tau 1 1)⁻¹ :=
  NormSection.chi_coboundary chiFenceHat chiFenceBase 1 1

end NonCharacterWitness

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.NormSection.chi
#print axioms Uniformity.Density.Gauge.NormSection.chi_coboundary

end AxCheck
