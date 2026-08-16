/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B66a
import Uniformity.Density.LocalData

/-!
# Uniformity.ChapB.B66 — `order1Type`, the order-1 datum as a `FactorizationType`

**Chapter B, NODE B.66** [def] [fresh] (`blueprint/CHAP-B_leaf_layer.md` §9), ENV-C in the
blueprint, **ENV-A as elaborated** (the body consults neither completeness nor residue
finiteness). One signed declaration, `order1Type`, plus the GC-4 degree-conservation lemma its
dictionary status makes mandatory and two read-off lemmas.

*The order-1 type datum.* For `φ` an order-1 key and `f` monic with `f̄ = φ̄^μ`, the **order-1
datum** of `f` is the multiset of pairs `(ℓ_S, m · ψ.natDegree)` over all
(slope `S`, monic irreducible residual factor `ψ`) — B.66a's two canonical index `Finset`s —
packaged as a `Uniformity.FactorizationType`.

**SIGNATURE.** Verbatim from the frozen stub (`leanspec/Leanspec/ChapB.lean`, **B.66**): binder
names, order, implicitness, the `open Classical in`, and the `Multiset.bind` body unchanged.

## What the suppliers now are (this changed under this node's feet, in its favour)

B.66's own SIGNATURE note said the two `Finset`s were "private helpers of this node"; the
RE-PLAN booking (B.79's ⚠, A-§9.5) promoted them to **B.66a**, and A-F.3 item **B-D4** signed
them as opaque `axiom`-typed constants. They did not land that way: B.66a landed them as REAL
definitions (`Set.Finite.toFinset` of the sets its membership lemmas describe), so `order1Type`
is a genuine, axiom-free definition and **this file's footprint is Lean core** — the 2026-08-16
B.42 literature cite is neither imported nor consumed anywhere on this path.

## GC-4 compliance (`blueprint/CONVENTIONS_2026-08-15.md` GC-4)

GC-4 requires every σ-valued dictionary function to ship a degree-conservation lemma. The one
this node can honestly ship is the **structural** identity `order1Type_degree`:

```
(order1Type π φ f).degree = ∑_{p ∈ slopeFinset π φ f} ∑_{ψ ∈ resFactorFinset π φ f p}
                              p.2 * (φ.natDegree * ψ.natDegree)
```

i.e. `Σ ℓ_S · (m · deg ψ)` over the polygon-and-residual index, which is exactly GC-4's
`(dict …).degree = <block degree>` with the block degree read off the dictionary's own index.

**The arithmetic form `(order1Type π φ f).degree = f.natDegree` is NOT provable at this node and
is not stated here.** It is a theorem about `f`, not about the datum: it needs B.42's dissection
(`Σ_S deg F_S = deg f`) welded to B.45's residual degree law (`deg F_S = ℓ_S · m · Σ_ψ deg ψ`
on a separable side), which is precisely the content the blueprint routes through B.63 and the
B.79a tie (§14 item 12). Claiming it here would be claiming those. What *is* discharged here is
the bookkeeping half — the multiset really is the double sum, with no term lost in the `bind`.

## Faithfulness

`EFF.W12.62` item 2 verbatim: "THEOREM W-12.A is the transcription spec for order-1 menu entries
AT EVERY DEGREE (`typeOf`-keyed by `(C, P_i, λ_{i,S})`)" — this node is the last two components
(per-branch polygon `P_i`, per-side residual type `λ_{i,S}`) at a single branch; the level-0
component `C` is B.67. `EFF.HE3.15`'s stage type `τ_stage(ℓ) := {(e_s, f_s)}` and `EFF.HE3.16`'s
transport `(e,f) ↦ (e₁e, f₁f)` at `e₁ = 1, f₁ = m` give `(e,f) ↦ (e, m·f)`, which is this
definition's second component `φ.natDegree * ψ.natDegree`. **Flagged for human review**
(definition faithfulness; parent CLAUDE.md trust boundary).

**One comment in the signed docstring is NOT a theorem about this body, and is not relied on
anywhere below.** The stub's "`0` (the empty type) when the data are not separable — the junk
branch is never read" describes an intent, not the term: the body reads B.66a's suppliers
unconditionally, and a non-separable residual polynomial still has monic irreducible divisors,
so the value off the separable regime is a well-defined multiset that simply carries no
warranty. The one junk value that IS pinned is at the degenerate input `f = 0`, where both
suppliers are empty and the datum is the empty type — `order1Type_zero`, proved below as this
node's sanity gate.

DEPENDS: B.20 (`sideSet`, `sideMin` — through B.66a) · B.66a (`slopeFinset`, `resFactorFinset`,
`mem_slopeFinset_imp`) · landed `Uniformity.FactorizationType` and
`FactorizationType.degree` (`Density/LocalData.lean:43`, `:49`) · mathlib `Multiset.map_bind`,
`Multiset.sum_bind`, `Finset.sum_eq_multiset_sum`.

The blueprint's DEPENDS lists B.42 and B.45; they are the *sources* of the two index sets'
faithfulness (B.66a's header records the clause-by-clause reading), not Lean dependencies of
this definition.

**SIZE.** blueprint 16 lines; landed 4 declarations.

**TEETH.** `HM3`-side menu rows are chapter G's; here **signed non-applicability** (a
definition), with `order1Type_degree` and `order1Type_zero` as the node's own regression.

SOURCE: `EFF.W12.62`; `EFF.HE3.15`; `EFF.HE3.16`.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

-- ENV-A (blueprint §0.1): the polynomial arena. The blueprint tags B.66 ENV-C; the definition
-- consults neither completeness nor residue finiteness, so — exactly as in the stub, whose
-- section variables are usage-included — the elaborated type carries ENV-A only.
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **B.66 — the order-1 datum.** `order1Type π φ f` : the `FactorizationType` predicted by
`f`'s order-1 polygon-and-residual data — the multiset of pairs `(ℓ_S, m · deg ψ)` over B.66a's
canonical slope and residual-factor `Finset`s. -/
noncomputable def order1Type (π : O) (φ f : Polynomial O) : FactorizationType :=
  open Classical in
  ⟨(slopeFinset π φ f).val.bind (fun p =>
      (resFactorFinset π φ f p).val.map (fun ψ => (p.2, φ.natDegree * ψ.natDegree)))⟩

/-- The datum's underlying multiset, by definition. -/
theorem order1Type_data (π : O) (φ f : Polynomial O) :
    (order1Type π φ f).data = (slopeFinset π φ f).val.bind (fun p =>
      (resFactorFinset π φ f p).val.map (fun ψ => (p.2, φ.natDegree * ψ.natDegree))) := rfl

/-- The `(e,f)` pairs of the order-1 datum, read off the two index `Finset`s: every entry comes
from a slope of the polygon and a monic irreducible factor of that side's residual polynomial,
with `e` the slope's denominator and `f` the product `m · deg ψ`. -/
theorem mem_order1Type_data {π : O} {φ f : Polynomial O} {q : ℕ × ℕ} :
    q ∈ (order1Type π φ f).data ↔
      ∃ p ∈ slopeFinset π φ f, ∃ ψ ∈ resFactorFinset π φ f p,
        q = (p.2, φ.natDegree * ψ.natDegree) := by
  rw [order1Type_data]
  simp only [Multiset.mem_bind, Multiset.mem_map, Finset.mem_val]
  constructor
  · rintro ⟨p, hp, ψ, hψ, rfl⟩
    exact ⟨p, hp, ψ, hψ, rfl⟩
  · rintro ⟨p, hp, ψ, hψ, rfl⟩
    exact ⟨p, hp, ψ, hψ, rfl⟩

/-- **GC-4's mandatory degree-conservation lemma for this dictionary.** The datum's degree is the
double sum `Σ_S Σ_ψ ℓ_S · (m · deg ψ)` over the polygon-and-residual index — nothing is lost or
double-counted in the `Multiset.bind`. (The arithmetic form `= f.natDegree` belongs to B.63 /
the B.79a tie; see the module docstring.) -/
theorem order1Type_degree (π : O) (φ f : Polynomial O) :
    (order1Type π φ f).degree
      = ∑ p ∈ slopeFinset π φ f, ∑ ψ ∈ resFactorFinset π φ f p,
          p.2 * (φ.natDegree * ψ.natDegree) := by
  classical
  rw [FactorizationType.degree, order1Type_data, Multiset.map_bind, Multiset.sum_bind]
  simp only [Finset.sum_eq_multiset_sum, Multiset.map_map, Function.comp_def]

/-- **Sanity gate — the pinned junk value.** At `f = 0` the polygon has a single abscissa, so no
slope carries a two-point side, so the slope supplier is empty and the datum is the empty type.
(This is the only junk value the signed body pins; see the module docstring on the stub
docstring's separability comment.) -/
theorem order1Type_zero (π : O) (φ : Polynomial O) :
    order1Type π φ (0 : Polynomial O) = ⟨0⟩ := by
  classical
  have hempty : slopeFinset π φ (0 : Polynomial O) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
    have hcard := (mem_slopeFinset_imp hp).2.2
    have hsub : sideSet φ (0 : Polynomial O) p.1 p.2 ⊆
        Finset.range ((0 : Polynomial O).natDegree + 1) := by
      intro j hj
      have hj' : j ∈ Finset.filter (OnSide φ (0 : Polynomial O) p.1 p.2)
          (Finset.range ((0 : Polynomial O).natDegree + 1)) := hj
      exact (Finset.mem_filter.mp hj').1
    have hle : (sideSet φ (0 : Polynomial O) p.1 p.2).card ≤ 1 := by
      have := Finset.card_le_card hsub
      simpa using this
    omega
  apply FactorizationType.ext
  rw [order1Type_data, hempty]
  simp

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.order1Type
#print axioms Uniformity.Density.Leaf.order1Type_data
#print axioms Uniformity.Density.Leaf.mem_order1Type_data
#print axioms Uniformity.Density.Leaf.order1Type_degree
#print axioms Uniformity.Density.Leaf.order1Type_zero
end AxCheck
