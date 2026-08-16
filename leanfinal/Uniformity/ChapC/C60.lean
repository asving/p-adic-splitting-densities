/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C09
import Uniformity.Density.TypeOf

/-!
# Uniformity.ChapC.C60 — `C-BOX-1`: the level-2 residue-leg hypothesis, named and fenced

**Chapter C, NODE C.60** [def+lemma] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §7, the Tier-1
`(e, f)` layer; the A-C.1 amendment set governs). **ENV-C3** nominally — see the environment note
below. Two signed declarations.

## What `C-BOX-1` is, and why it is a hypothesis rather than a theorem

`CBox1Side L g : Prop := (F.f₁ * L.r.natDegree) ∣ inertiaDegOf g` — the **residue-direction
divisibility** the Tier-1 sandwich needs: the composed residual degree `f₁·d_r` divides the
residue degree of `K[x]/(g)`.

This is **the exact analogue of CHAP-B's `B-BOX-1` one level up**. The corpus proves it by
realizing the residual root in the leaf's residue field (`EFF.HE6.29`'s root label) — a
**`K̄₀`-side statement with no closure-free proof in this chapter**, so under DECISION C-D1 it is
carried as an explicit hypothesis rather than transcribed with a fake proof.

**The fence (the whole point of the node).** No node assumes `CBox1Side` silently: it is an
explicit hypothesis on C.61/C.62/C.63/C.69 and on §5's C.40, **and nowhere else**. A fleet agent
that needs it discharged at `f₁·d_r ≥ 2` returns
`BLOCKED: C-BOX-1 (B-BOX-1 analogue; repair route B.56/B.62)` — it does not invent a proof, and
per GC-5's RE-PLAN discipline a genre schema that wants this as a *field* triggers C-D1's
FALSIFIER protocol, not a silent add.

## The three lemma clauses, and which of them is Lean

The blueprint node lists three clauses; only (i) is a signed declaration, and the stub declares
only (i). (ii) and (iii) are **records/companions**, transcribed here as documentation:

* **(i) the vacuity perimeter — LANDED as `cbox1_of_deg_one`.** `CBox1Side L g` holds
  unconditionally when `F.f₁ * L.r.natDegree = 1`, by `one_dvd`. This is the perimeter inside
  which every Tier-1 consumer is *unconditional*: the frame-residual-degree-1 regime. It is also
  the honest measure of how much the hypothesis costs — nothing at `f₁ d_r = 1`, everything
  above it.
* **(ii) the UPPER bound is unconditional (companion, NOT landed here).** Bounds of the shape
  `inertiaDegOf g ∣ F.f₁ * L.r.natDegree * (…)` come free from the degree identity together with
  C.59, mirroring B.54's upper half. C.59 is not yet landed, and the blueprint records this as a
  companion rather than a clause of this node, so nothing is declared for it — the asymmetry
  (upper free, lower carried) is exactly `B-BOX-1`'s.
* **(iii) the repair route (record, NOT landed).** Inherited from `B-BOX-1`: B.56/B.62's
  spectral-norm layer (multiplicative, ℝ-valued — **the same named RISK**), applied at the
  iterated leaf.

## Environment note

The node names **ENV-C3** (= ENV-C1 + `[IsAdicComplete (maximalIdeal O) O]` +
`[Finite (ResidueField O)]`), which is the environment its *consumers* and its intended
discharge live in. **Neither signed declaration consumes those instances**: `inertiaDegOf` is
defined engine-free over any DVR (`Uniformity/Density/TypeOf.lean` — the gcd of the norm
valuations), and clause (i) is `one_dvd`. The stub carries no instance binders, and adding unused
ones would change the signature, so the declarations land instance-free (GC-6.4's minimal
binding). The completeness/finiteness content enters only where `inertiaDegOf` is *identified*
with the classical residue degree, which is `Uniformity/Density/TypeOfFaithful.lean`'s business,
not this node's.

## ⚠ FAITHFULNESS (trust boundary, flagged for human review)

`inertiaDegOf g` is this development's **gcd-of-norm-valuations** surrogate for the residue
degree `f` of `K[x]/(g)` — engine-free by construction, provably equal to the classical `f` for
monic irreducible `g` over a complete `O` (`inertiaDegOf_eq_inertiaDeg'`), and *only* then.
`CBox1Side` is therefore a statement about that surrogate; the corpus's `EFF.HE6.29` root label
is **not** transcribed and must not be assumed. Reading `CBox1Side` as "the residual root lives
in the leaf's residue field" is the closure-side gloss, not the Lean content.

**DEPENDS.** C.09 (`LevelDatum`, its `r`) · landed `inertiaDegOf` (`Uniformity.Density.TypeOf`) ·
B.55/B.56/B.62 (the level-1 box + its repair route, cited as the inheritance, not imported) — by
committed node ID (GC-13(b)). The two imports are `Uniformity.ChapC.C09` (pulling C.03, C.01) and
`Uniformity.Density.TypeOf`.

**PROOF.** (i) `h1 ▸ one_dvd _`. (ii)/(iii) are records + companions, not declarations.

SOURCE: CHAP-B H-7 (`B-BOX-1`, verbatim shape: "stated as an explicit hypothesis on B.55/B.58 and
not assumed anywhere else"); `EFF.HE6.29` (`HE6-ROOT-LABEL` — the corpus's closure-side supplier,
**NOT transcribed**, per C-D1); GC-5's RE-PLAN discipline.

**TEETH.** Signed **non-applicability** (a named hypothesis); its DISCHARGE evidence is the
batteries' PARI σ agreement, retained as regressions at §13.

ENVIRONMENT: ENV-C3 (nominal; see the environment note).

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ### The signed declarations -/

/-- `C-BOX-1`: the level-2 residue-degree lower bound, carried as an explicit hypothesis
(DECISION C-D1; the `B-BOX-1` analogue — CHAP-B H-7's shape one level up). -/
def CBox1Side {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) : Prop :=
  (F.f₁ * L.r.natDegree) ∣ inertiaDegOf g

/-- **C.60 (i) — the vacuity perimeter.** At `f₁·d_r = 1` the hypothesis is free (`one_dvd`), so
every Tier-1 consumer carrying `CBox1Side` is unconditional in that regime. -/
theorem cbox1_of_deg_one {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (g : Polynomial O) (h1 : F.f₁ * L.r.natDegree = 1) : CBox1Side L g := by
  rw [CBox1Side, h1]
  exact one_dvd _

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.CBox1Side
#print axioms Uniformity.Density.Tower.cbox1_of_deg_one

end AxCheck
