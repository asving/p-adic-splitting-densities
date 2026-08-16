/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B30
import Uniformity.ChapB.B61

/-!
# Uniformity.ChapB.BBox1CiteStatement — the signable gate-(b) statement for `B-BOX-1`

**OM-5 (2026-08-16).** This file declares **NO axiom and NO `sorry`**. It lands two things:

1. `BBox1CiteStatement` — the closed `Prop` that the OM-5 unit proposes as the gate-(b)
   literature cite discharging `B-BOX-1` (CHAP-B B.61's carried hypothesis `hBOX`) at the
   irreducible-residual leaf, in landed vocabulary, **byte-exact as the signable artifact**
   (the CHAP-I dated addendum of 2026-08-16 carries the faithfulness draft; the sources are
   [FGMN] Thm 6.6 + [GN15] Thm 2.3 & eq. (2.1) — the leaf dichotomy, NS-2's COVERS-ALL-O
   verdict — plus the two classical-valuation-theory glue legs named there). Elaborating this
   file machine-checks that the proposed statement TYPES against the landed layer; nothing
   here asserts it.

2. `typeOf_leaf_of_cite` — the machine-checked WIRING: `BBox1CiteStatement` really does
   discharge B.61's `hBOX`, i.e. under B.61's hypotheses plus the residual-irreducibility
   clause (`hirr`, deliberately absent from B.61's frozen signature — its own docstring says
   "the irreducibility of `ψ` is how a *caller* is expected to know `hBOX`"), the leaf
   theorem's conclusion follows from the cite statement. Until the owner signs the cite as an
   `axiom`, every consumer takes `BBox1CiteStatement` as an explicit hypothesis — exactly the
   same honesty shape as `hBOX` today, one composition higher.

## ⚠ Status of the box: UNCHANGED until signature

`B-BOX-1` remains an explicit hypothesis everywhere. This file adds no proving power; it
pins the statement the owner would sign and proves the wiring is sound. A future
`axiom bBox1_cite : BBox1CiteStatement` (post-signature, with the faithfulness entry in
`docs/AXIOM_FAITHFULNESS.md`) makes `typeOf_leaf_of_cite` fire unconditionally, with the
axiom name visible in every downstream `#print axioms` — the H-14 inheritance pattern.

## Certification

`verification/om5_bbox1_cert.gp` (128 checks, 0 failures): the leaf `(e,f) = (ℓ, m·d)` and
the order-level gcd `inertiaDegOf = m·d` at `d ≥ 2`, both primes `{2,3}`, both
characteristics, including the A-F.7-widened `ℓ = 1, m ≥ 2, d ≥ 2` region and the wild
`p ∣ ℓ` rows; the multiplicity-`≥ 2` defeat certifying that `hirr` is a NECESSARY hypothesis
of this statement (`(x²−p)²`: factor-level gcd `1`, `m·d = 2 ∤ 1`); the non-coprime defeat;
and route 1's (LEMMA HE3-4U) base-change mechanism executed at an `m ≥ 2` equal-char
instance.

## Status

Sorry-free, axiom-free (Lean core only). The `Prop` is *stated*, not asserted.
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

/-- **The `B-BOX-1` gate-(b) cite statement** (OM-5 draft, 2026-08-16; owner signature
pending). At an irreducible-residual leaf — `g` monic `(u,ℓ)`-pure at an order-1 key `φ`,
`0 < u`, `0 < ℓ`, `Nat.Coprime u ℓ`, `sideDeg = d > 0`, reduction `φ̄ ^ (ℓd)`, and residual
polynomial **irreducible** (the multiplicity-1 clause; necessary per the CERT-C(i) defeat) —
every monic irreducible factor `g'` of `g` satisfies the residue-degree lower bound
`m·d ∣ inertiaDegOf g'`, i.e. exactly B.61's `hBOX`.

Classical content: the leaf dichotomy ([FGMN] Thm 6.6, [GN15] Thm 2.3 + eq. (2.1); GMN
Thm 1.19 + Cor 1.20 at ℚ_p scope) gives `g` irreducible with `f(L/K) = m·d`; the maximal
order `O_L` of `L = K[x]/(g)` is a DVR finite over the complete `O` with residue degree
`m·d`; and `v(N(x)) = f·w(x)` turns that into the divisibility of every order-level
norm-valuation — the gcd semantics of `inertiaDegOf`. See the CHAP-I 2026-08-16 OM-5
addendum for the full faithfulness draft. -/
def BBox1CiteStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (π : O), Irreducible π → ∀ (φ : Polynomial O), IsKey φ →
    ∀ (u ℓ : ℕ), 0 < u → 0 < ℓ → Nat.Coprime u ℓ →
    ∀ (g : Polynomial O), g.Monic → IsPure φ g u ℓ →
    ∀ (hne : (sideSet φ g u ℓ).Nonempty), 0 < sideDeg φ g u ℓ hne →
    g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne) →
    ∀ (H₀ : ℕ), npHgt φ g (sideMin φ g u ℓ hne) = (H₀ : ℕ∞) →
    Irreducible (resPoly π φ g u ℓ hne H₀) →
    ∀ g' ∈ monicFactors g,
      φ.natDegree * sideDeg φ g u ℓ hne ∣ inertiaDegOf g'

section ENVC

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The wiring, machine-checked.** The cite statement discharges B.61's `hBOX`: under
B.61's hypotheses plus the `H₀` pin and the residual irreducibility `hirr`, the leaf theorem
`typeOf g = ⟨{(ℓ, m·d)}⟩` follows from `BBox1CiteStatement`. This is `B-BOX-1`'s discharge
at the irreducible-residual scope, conditional on the (unsigned) cite and on nothing else. -/
theorem typeOf_leaf_of_cite (hcite : BBox1CiteStatement)
    (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {u ℓ : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ) {g : Polynomial O}
    (hg : g.Monic) (hpure : IsPure φ g u ℓ) (hne : (sideSet φ g u ℓ).Nonempty)
    (hd : 0 < sideDeg φ g u ℓ hne)
    (hres : g.map (IsLocalRing.residue O)
      = (φ.map (IsLocalRing.residue O)) ^ (ℓ * sideDeg φ g u ℓ hne))
    {H₀ : ℕ} (hH₀ : npHgt φ g (sideMin φ g u ℓ hne) = (H₀ : ℕ∞))
    (hirr : Irreducible (resPoly π φ g u ℓ hne H₀)) :
    typeOf g = ⟨{(ℓ, φ.natDegree * sideDeg φ g u ℓ hne)}⟩ :=
  typeOf_leaf_of_resDeg_lower_bound hπ hφ hu hℓ hcop hg hpure hne hd hres
    (hcite O π hπ φ hφ u ℓ hu hℓ hcop g hg hpure hne hd hres H₀ hH₀ hirr)

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint (both must be Lean-core only; the `Prop` is stated, not asserted) -/

section AxCheck
#print axioms Uniformity.Density.Leaf.BBox1CiteStatement
#print axioms Uniformity.Density.Leaf.typeOf_leaf_of_cite
end AxCheck
