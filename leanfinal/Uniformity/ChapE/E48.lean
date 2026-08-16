/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.Density.TypeOfAlgebra

/-!
# Uniformity.ChapE.E48 — `typeOf_list_prod`: the rung σ-transport law

**Chapter E, NODE E.48** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §7 — the σ dictionary and
the transport laws, the chapter's TERMINAL SUPPLY), **as REPAIRED by amendment A-E.1/E-D9**.
ENVIRONMENT ENV-E2 (+ the landed kernel's instances).

σ is multiplicative over the block split: for a list of monic polynomials over a DVR base `O`,
the factorization type of the product is the SUM of the factors' types — the
`(SIDE-PROD)`/`(LABEL-PROD)`/`(BOUNDARY-PROD)` situations of `EFF.T2.17`, where every emitted
label block is read from its own development and the blocks are multiplied back together. It is
the σ-half of HE7.A clauses 4/6 and of T2.KEY-BOUNDARY, and the transport law that the drainage
recursions and chapter H's §11 `composedSigma` consume from chapter E.

The proof is the landed product law `Uniformity.Density.typeOf_mul` iterated along the list, with
the empty product `1` as base case (its monic factorization is the empty multiset, so its type is
`⟨0⟩`).

## Namespace (GC-6.2)

This is the chapter's ONE theorem about landed objects, so it lives in the owning namespace
`Uniformity.Density` — not in `Uniformity.Density.Ladder` where chapter E's own definitions sit.

## The A-E.1/E-D9 repair (statement-level; the blueprint is authority)

The committed signature was

    theorem typeOf_list_prod ... (hm : ...) (hcond : True) : typeOf l.prod = (l.map typeOf).sum

and it **does not elaborate**: `(l.map typeOf).sum` needs `Add FactorizationType`, which does not
exist and whose absence is deliberate — the landed module states the peel law *"on `.data`, not on
any addition structure for `FactorizationType`, so it survives verbatim if such structure is later
added"* (`Uniformity/Density/TypeOfAlgebra.lean`, whose spec entry REJECTS the algebraic
structure, R14). A fleet agent must NOT introduce `Add FactorizationType` to restore the committed
shape. The conclusion is therefore signed on `.data`, where the landed law lives, and the sum is
the ordinary `List.sum` of `Multiset (ℕ × ℕ)`.

The blueprint's `hcond : True` slot was reserved for whatever side conditions the landed
`typeOf_mul` turned out to need. §12(a)7's type diff was executed and answered it: the landed

    theorem typeOf_mul {f g : Polynomial O} (hf : f.Monic) (hg : g.Monic) :
        (typeOf (f * g)).data = (typeOf f).data + (typeOf g).data

(`Uniformity/Density/TypeOfAlgebra.lean:60`) takes **monicity only** — no coprimality, no
root-set disjointness. So `hcond` stands for nothing and is DROPPED rather than filled; §14 item 9
("can the ladder's blocks supply them?") is answered — there is nothing to supply, and E.23 routes
no side condition for this node.

## Degree bookkeeping (GC-4)

E.48 emits a `.data` (a `Multiset (ℕ × ℕ)`), not a σ-value, so its degree conservation is not a
fresh lemma: it travels through the landed `Uniformity.FactorizationType.degree_mk_add`
(`(⟨σ.data + τ.data⟩).degree = σ.degree + τ.degree`, CN-23) together with the landed
`Uniformity.Density.typeOf_degree` (`(typeOf f).degree = f.natDegree` for monic `f`). Both are
cited, neither is restated here. GC-4's mandatory σ-output lemma for chapter E's own dictionary is
`ladderSigma_degree`, NODE E.46 — a different node and file.

DEPENDS: landed `Uniformity.Density.typeOf_mul`, `monicFactors_mul`, `monicFactors_eq`,
`typeOf_data` · E.45 (the dictionary this feeds).

SOURCE: `EFF.T2.17` (`(SIDE-PROD)`/`(LABEL-PROD)`: *"Every emitted label block is read from its own
development"*); `EFF.T2.32` (T2.KEY-BOUNDARY: *"Multiplying the resulting identities proves the
assertion"*); `EFF.T2.31` clause 6 (*"their product is F"*).

TEETH: Q1's member-by-member σ against PARI — each member's σ is assembled by exactly this sum —
→ **Lean theorem** at the landed side-conditions (monicity only).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density

/-- **NODE E.48.** *The rung σ-transport law* — σ is multiplicative over the block split: the
factorization type of a product of monic polynomials is the sum of the factors' types, read on
`.data` (defect A-E.1/E-D9: `FactorizationType` deliberately carries no `Add`, so the sum is the
`List.sum` of the underlying `Multiset (ℕ × ℕ)`s). The only side condition is MONICITY, exactly as
in the landed two-factor law `typeOf_mul`. -/
theorem typeOf_list_prod {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (l : List (Polynomial O))
    (hm : ∀ g ∈ l, Polynomial.Monic g) :
    (typeOf l.prod).data = (l.map fun g => (typeOf g).data).sum := by
  -- A list of monics has a monic product (needed to feed `typeOf_mul` at each cons).
  have hmonic : ∀ m : List (Polynomial O), (∀ g ∈ m, Polynomial.Monic g) → m.prod.Monic := by
    intro m
    induction m with
    | nil => intro _; simp
    | cons b s ihs =>
      intro hbs
      rw [List.prod_cons]
      exact (hbs b (by simp)).mul (ihs fun g hg => hbs g (by simp [hg]))
  induction l with
  | nil =>
    -- `[].prod = 1`, whose monic factorization is the empty multiset, so `(typeOf 1).data = 0`.
    have hF : IsMonicFactorization (1 : Polynomial O) 0 :=
      ⟨fun p hp => absurd hp (Multiset.notMem_zero p), Multiset.prod_zero⟩
    simp [typeOf_data, monicFactors_eq hF]
  | cons a t ih =>
    have ha : a.Monic := hm a (by simp)
    have ht : ∀ g ∈ t, Polynomial.Monic g := fun g hg => hm g (by simp [hg])
    rw [List.prod_cons, typeOf_mul ha (hmonic t ht), ih ht, List.map_cons, List.sum_cons]

end Uniformity.Density

/-! ## Consistency gate — the list law specializes to the landed two-factor law

Not a new declaration: an `example` that re-derives `Uniformity.Density.typeOf_mul`'s conclusion
from `typeOf_list_prod` at the two-element list, checking that the `.data`/`List.sum` shape of the
signed conclusion really is the landed law's `Multiset` addition. -/

section ConsistencyGate

open Uniformity.Density

example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (f g : Polynomial O) (hf : f.Monic) (hg : g.Monic) :
    (typeOf (f * g)).data = (typeOf f).data + (typeOf g).data := by
  have h := typeOf_list_prod [f, g] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    exacts [hf, hg])
  simpa using h

end ConsistencyGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.typeOf_list_prod

end AxCheck
