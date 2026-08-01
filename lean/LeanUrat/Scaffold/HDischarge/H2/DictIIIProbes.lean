/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps

/-!
# Scaffold/HDischarge/H2/DictIIIProbes — the two adjudication probes
  [HDISCHARGE_H2 unit H2-U7; wave 1, MED, dep DictIII.Hyps]

Transcription of `lean/blueprints/HDISCHARGE_H2.md` §6 unit H2-U7, theorem
statements VERBATIM.

* PROBE F-1 (`dictFresh_junctionPin_trivial`): the `junctionPin` clause of the
  landed `DictIII.FRESH` row is TRIVIAL — its conclusion follows from its own
  guard `i + 1 < H.nodes.length` with no (FRESH) content at all.
* PROBE F-2 (`probe_not_FRESH`): a compiled negation witness — the
  duplicate-node history `nodes = [ν, ν]` (with `base := ⊤`, `psi0 := X`,
  `psihat i := X + 1`, over `F = ZMod 2`) satisfies every `EHist` carrier law
  but refutes the `parentSeparated` clause, so the landed `DictIII.FRESH` row
  is FALSE at an intended-instance class (the carrier laws do NOT obstruct
  duplicate nodes: no `EHist` law mentions `nodes` beyond its type).

Output feeds the §2.3 sign-off-gated adjudication; per the unit charge, NO
restatement of `DictIII.FRESH` is made in this file — the probes only consume
the landed row.  Witness names (`probeNode`, `duplicateEHist`) are this unit's
construction freedom (blueprint: "construction is the unit's work").
-/

namespace LeanUrat.Scaffold.HDischarge.H2

/- The proof below is the blueprint-supplied one, kept verbatim; in this pin
`simp`'s default set already carries the `isSome`/`getElem?` reduction
(`List.isSome_getElem?`), so the listed argument is redundant and only the
`unusedSimpArgs` linter (not the proof) needs quieting. -/
set_option linter.unusedSimpArgs false in
/-- PROBE F-1 (PROVED at blueprint probe): DictIII.FRESH.junctionPin is trivial. -/
theorem dictFresh_junctionPin_trivial {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] (H : DictIII.EHist p F) (i : ℕ)
    (h : i + 1 < H.nodes.length) : (H.nodes[i]?).isSome := by
  simp [List.getElem?_eq_some_iff]; omega

/-- The duplicated node ν of the PROBE F-2 witness: e = h = ℓ = 1, s = u = 0,
    terminal (`sel = none`), `inc = false`.  Every `ENodeData` carrier law
    holds (`hsel` is vacuous at `sel = none`). -/
def probeNode : DictIII.ENodeData where
  e := 1
  h := 1
  ℓ := 1
  s := 0
  u := 0
  sel := none
  inc := false
  he := le_rfl
  hh := le_rfl
  hcop := by decide
  hl := le_rfl
  hsel := by simp

/-- The witness dressing laws: `X + 1` over `↥(⊤ : Subfield (ZMod 2))` is
    monic, irreducible, and ≠ `X` (helper for `duplicateEHist.hpsihat`). -/
theorem probePsihat_laws :
    (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))).Monic ∧
      Irreducible (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))) ∧
      (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))) ≠
        Polynomial.X := by
  have hm : (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))).Monic := by
    simpa using Polynomial.monic_X_add_C (1 : ↥(⊤ : Subfield (ZMod 2)))
  have hd : (Polynomial.X + 1 : Polynomial ↥(⊤ : Subfield (ZMod 2))).degree = 1 := by
    simpa using Polynomial.degree_X_add_C (1 : ↥(⊤ : Subfield (ZMod 2)))
  refine ⟨hm, hm.irreducible_of_degree_eq_one hd, ?_⟩
  · intro hXC
    have h10 := congrArg (fun q => Polynomial.coeff q 0) hXC
    simp at h10

/-- The PROBE F-2 duplicate-node witness history over `F = ZMod 2`:
    `nodes = [ν, ν]` with ν = `probeNode`, `base := ⊤`, `psi0 := X`,
    `psihat i := X + 1` — every `EHist` carrier law holds (no law constrains
    `nodes`), yet `nodes[0]? = nodes[1]?`. -/
noncomputable def duplicateEHist : DictIII.EHist 2 (ZMod 2) where
  base := ⊤
  psi0 := Polynomial.X
  hpsi0 := ⟨Polynomial.monic_X, Polynomial.irreducible_X⟩
  a0 := 1
  ha0 := le_rfl
  nodes := [probeNode, probeNode]
  fld := fun _ => ⊤
  psihat := fun _ => Polynomial.X + 1
  hpsihat := fun _ => probePsihat_laws

/-- The witness node list, read back (definitional). -/
theorem duplicateEHist_nodes :
    duplicateEHist.nodes = [probeNode, probeNode] := rfl

/-- PROBE F-2: compiled negation witness — duplicate-node history refutes
    DictIII.FRESH.parentSeparated at an intended-instance class. -/
theorem probe_not_FRESH : ∃ (p : ℕ) (_ : Fact p.Prime),
    ¬ (DictIII.FRESH p (ZMod 2)) := by
  refine ⟨2, inferInstance, fun hF => ?_⟩
  exact hF.parentSeparated (H := duplicateEHist) (i := 0) (j := 1)
    (by simp [duplicateEHist_nodes]) (by simp [duplicateEHist_nodes])
    (by omega) rfl

end LeanUrat.Scaffold.HDischarge.H2

-- Footprint audit (unit H2-U7 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.HDischarge.H2.dictFresh_junctionPin_trivial
#print axioms LeanUrat.Scaffold.HDischarge.H2.probe_not_FRESH
