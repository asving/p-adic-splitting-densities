/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C03

/-!
# Uniformity.ChapC.C09 — `LevelDatum`, `keyDeg₂`, `seam`: the level-2 dictionary

**Chapter C, NODE C.09** [def] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §3, the level frame
and the level dictionary; the A-C.1 amendment set governs). ENV-C1. Three signed declarations,
all definitional. **This is a TERMINAL SUPPLY node**: chapter D's telescope and chapter E's ladder
consume the level-2 dictionary from here, so its field list is an external interface, not a local
convenience.

*The level datum and the level-2 dictionary numerals.* A **level datum** over a frame `F` (C.01)
with a correct pin `H₀` (C.03) is a side together with a residual factor:

* `u`, `ℓ` with `0 < ℓ` and `Nat.Coprime u ℓ` — the level slope `λ = u/ℓ` in lowest terms;
* `hκ : ℓ * (F.e₁ * F.f₁) * F.h < u` — the standing hypothesis `κ > D′h` of `EFF.HE6.14`,
  cleared of the denominator `ℓ` (multiply `u/ℓ > D′h` through by `ℓ > 0`);
* `r : Polynomial (F.stageField H₀ hpin)` monic irreducible with `r.coeff 0 ≠ 0` and
  `0 < r.natDegree` — the residual factor, over the stage field `K` of C.03.

The derived numerals of `EFF.HE6R1.18`'s dictionary are

* `L.keyDeg₂ = (F.e₁ * F.f₁) * L.ℓ * L.r.natDegree` — the level-2 key degree `D″ = D′ℓd_r`;
* `L.seam = L.r.natDegree * L.u` — the seam `T₂ = ℓd_rλ`, cleared at `λ = u/ℓ` to the integer
  `d_r·u`.

Their regroupings and the jump-frame floor `4 ≤ keyDeg₂` are C.10's business, not this node's.

## ⚠ Faithfulness

**Mandatory, trust-boundary definition** (three definitions, no proof obligation; parent
CLAUDE.md trust boundary). Four recasts against `EFF.HE6.14`'s DEFINITION HE6-1, each flagged for
the chapter cross-read (blueprint §16):

* **`r` lives over the CONCRETE stage field**, C.03's `AdjoinRoot` iterate — not over an abstract
  `Field` parameter. This is forced by GC-7's abstract/concrete split: level data must transport
  back to `typeOf` definitionally, so the concrete carrier is mandatory here, and ENV-C4's
  abstract statements are instantiated AT this carrier rather than the other way round.
* **`hκ` is the cleared `κ > D′h`.** `κ = u/ℓ` is a rational and the structure carries no
  rationals; `ℓ * (e₁ * f₁) * h < u` is its `ℕ`-form, faithful because `ℓ > 0`. Note the
  association: `D′ = e₁f₁` is grouped, so the product is `ℓ·(e₁f₁)·h`, and `<` is strict, as the
  corpus's `>` is.
* **`hcop` is a STRUCTURE FIELD, not a per-lemma hypothesis.** Coprimality of `(u, ℓ)` is
  load-bearing and its load-bearing status is machine-certified in the corpus: tooth
  `HE6-T-BADKEY` exhibits a `κ = 6/2` key — same rational slope, not in lowest terms — whose
  associated object has two `p`-adic factors, which is `EFF.HE6.14`'s CONDITIONALITY. Carrying it
  in the structure makes every consumer inherit it and makes the tooth a typing obstruction rather
  than a forgotten side condition.
* **`hrdeg : 0 < r.natDegree` is carried even though `hrirr` nearly gives it.** Irreducibility
  over a field rules out units, hence `r.natDegree = 0` is impossible for monic `r` — but only
  once `K` is known to be a field, which is NOT in scope at these binders (the `Field` instance
  needs `Fact (Irreducible (frameRes …))` plus the D9 base-field fact; see C.04). The field is
  independent as written and is what `EFF.HE6.14`'s `d_r ≥ 1` says.

**Flagged for human review** (definition faithfulness; parent CLAUDE.md trust boundary).

## D13 — the multiplicity is deliberately NOT a field

Recorded by the stub gate (`leanspec/Leanspec/ChapC.lean`, defect **D13**) as a design finding,
not a typing failure: `LevelDatum` has no field for the multiplicity `m`. C.29's `HasLabel`
existentially quantifies its own `m` with `dvResPoly … = L.r ^ m`, and C.35's `mult₂` computes a
different one as `(blockFactor …).natDegree / L.keyDeg₂`. Nothing in the chapter ties the two, and
C.40 is the node where they must agree. That obligation is downstream of this node and is NOT
discharged by adding a field here — adding one would silently pick a winner between two
definitions the chapter has not yet reconciled. The datum is left as the corpus writes it.

## The `noncomputable` on the two numerals (D18)

`keyDeg₂` and `seam` both read `L.r.natDegree`, and `L.r`'s coefficient ring is
`F.stageField H₀ hpin = AdjoinRoot (frameRes …)`, whose ring structure comes from the quotient
instance `AdjoinRoot.instCommRing` and is noncomputable. Both numerals are therefore
`noncomputable def`. Defect **D18** of the stub gate is the record that the pre-amendment
blueprint signed plain `def`s here (as it did at C.03's `stageCard`) and that they do not
elaborate; the A-C.1 text and the gate-verified twin both carry the cure, and it is transcribed
from them.

**DEPENDS.** C.01 (`KeyFrame`) · C.03 (`stageField`, and `frameRes` inside it) — all by committed
node ID (GC-13(b)). The import is `Uniformity.ChapC.C03`.

**PROOF.** Definitional. The bodies are the gate-verified `leanspec/Leanspec/ChapC.lean` stub
bodies (the §3 A-C.1 layer) verbatim, including the D18 cure.

SOURCE: `EFF.HE6.14` (DEFINITION HE6-1's data: `κ = u/ℓ` in lowest terms, `κ > D′h`, `r` monic
irreducible, `r(0) ≠ 0`); `EFF.HE6R1.18` (the dictionary `D″ = D′ℓd_r = 2·1·2 = 4`,
`T₂ = ℓd_rλ = 2λ`, `K₂ = K(β)`, `μ₂ = deg f_S/D″`).

**TEETH.** `EFF.HE6R1.18`'s frame audit ("Every frame parameter is forced and every one checks")
→ **Lean theorem** at C.10 + **executable regression** at blueprint §13 (the
`(e₁,f₁,h) = (2,1,1)`, `Φ′ = x²−π`, `D″ = 4`, `T₂ = 2λ`, `μ₂ = 2` instance re-fired at `q = 3`
AND at the `q = 2` analogue). `HE6-T-BADKEY` guards `hcop`, as above.

ENVIRONMENT: ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- A level-2 label `(λ = u/ℓ, r)` over the frame `F`, with the dictionary numerals
`D″ = D′ℓd_r` and `T₂ = ℓd_rλ` (cleared: `T₂ = d_r·u`).  `EFF.HE6R1.18`. -/
structure LevelDatum (F : KeyFrame O π) (H₀ : ℕ)
    (hpin : npHgt Polynomial.X F.key (sideMin Polynomial.X F.key F.h F.e₁ F.hne) = (H₀ : ℕ∞))
    where
  /-- The slope numerator of `λ = u/ℓ`. -/
  u : ℕ
  /-- The slope denominator of `λ = u/ℓ`; positive, and coprime to `u`. -/
  ℓ : ℕ
  /-- The residual factor over the stage field `K` (C.03's concrete `AdjoinRoot` iterate). -/
  r : Polynomial (F.stageField H₀ hpin)
  hℓ : 0 < ℓ
  hcop : Nat.Coprime u ℓ
  /-- `κ > D′h`, cleared of the denominator `ℓ`. -/
  hκ : ℓ * (F.e₁ * F.f₁) * F.h < u
  hrmonic : r.Monic
  hrirr : Irreducible r
  hr0 : r.coeff 0 ≠ 0
  hrdeg : 0 < r.natDegree

/-- `D″ = D′·ℓ·deg r`.  **D18 (cured):** `noncomputable` — `L.r.natDegree` goes through
`AdjoinRoot.instCommRing`. -/
noncomputable def LevelDatum.keyDeg₂ {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : ℕ :=
  (F.e₁ * F.f₁) * L.ℓ * L.r.natDegree

/-- `T₂ = ℓ·d_r·λ`, cleared to the integer `d_r·u`.  **D18 (cured):** `noncomputable`. -/
noncomputable def LevelDatum.seam {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) : ℕ :=
  L.r.natDegree * L.u

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.LevelDatum
#print axioms Uniformity.Density.Tower.LevelDatum.mk
#print axioms Uniformity.Density.Tower.LevelDatum.keyDeg₂
#print axioms Uniformity.Density.Tower.LevelDatum.seam

end AxCheck
