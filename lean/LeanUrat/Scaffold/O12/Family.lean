/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.Scaffold.O12.Core

/-!
# Scaffold/O12/Family — GramOver, the 𝔅_n row families, Theorem 2 [BP_II units II-R1..R14]

Movement II row-family layer (blueprint `lean/blueprints/BP_II.md` §1.3; source of
mathematical truth: the verified leaf `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§2.3, §5).

This file carries **unit II-R1**: the `GramOver` inductive (the grammar 𝒢 with leaves,
mirroring the landed `Gram` of `MovesU/O12PoleFree.lean`) plus the two induction walks
`GramOver.mono` and `Gram.gramOver`. Units II-R2..R14 extend this module.
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU (MemRcyc Gram cycS DefinedAt AbsSolveTable detO1 detO2 detO3)

/-- The grammar 𝒢 with LEAVES: generated from a set S by (g1)–(g6) (brief §2.3).
Mirrors the landed `Gram` (O12PoleFree.lean) plus a leaf constructor — the leaves are
the lower blocks' solved entries in Theorem 2's induction. -/
inductive GramOver (S : Set Qq) : Qq → Prop
  | leaf {f : Qq} (h : f ∈ S) : GramOver S f
  | poly (P : Polynomial ℚ) : GramOver S (algebraMap (Polynomial ℚ) Qq P)
  | invS {s : Polynomial ℚ} (hs : s ∈ cycS) : GramOver S (algebraMap (Polynomial ℚ) Qq s)⁻¹
  | add {f g} : GramOver S f → GramOver S g → GramOver S (f + g)
  | mul {f g} : GramOver S f → GramOver S g → GramOver S (f * g)
  | neg {f} : GramOver S f → GramOver S (-f)
  | subst {f} (δ : ℕ+) : GramOver S f → GramOver S (MovesS.powSubst δ f)

/-- Leafless generation is generation over any leaf set: the landed grammar `Gram`
embeds into `GramOver S` constructor-for-constructor (induction walk, unit II-R1). -/
theorem Gram.gramOver {S : Set Qq} {f : Qq} (h : Gram f) : GramOver S f := by
  induction h with
  | poly P => exact GramOver.poly P
  | invS hs => exact GramOver.invS hs
  | add _ _ ha hb => exact ha.add hb
  | mul _ _ ha hb => exact ha.mul hb
  | neg _ ha => exact ha.neg
  | subst δ _ ha => exact ha.subst δ

/-- Monotonicity in the leaf set (induction walk, unit II-R1): enlarging S only
enlarges what 𝒢 generates. -/
theorem GramOver.mono {S T : Set Qq} (hST : S ⊆ T) {f} : GramOver S f → GramOver T f := by
  intro h
  induction h with
  | leaf hf => exact GramOver.leaf (hST hf)
  | poly P => exact GramOver.poly P
  | invS hs => exact GramOver.invS hs
  | add _ _ ha hb => exact ha.add hb
  | mul _ _ ha hb => exact ha.mul hb
  | neg _ ha => exact ha.neg
  | subst δ _ ha => exact ha.subst δ

end LeanUrat.Scaffold
