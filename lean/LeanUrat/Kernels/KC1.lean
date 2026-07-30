/-
Kernels/KC1 — BP4-c5 E-phase skeleton for unit KC1: the HMC direction census
at the toy (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.C + §4 KC1;
adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

THE KERNEL (MovesV/Defs.lean:1180): HMC TE D ↔ ∀ m γ h₁ h₂,
(D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂) ↔ (D.dom (.last m)).Mem h₁ ∧
(D.dom γ).Mem h₂.  Machine fact on record: ¬HMC at the census-coupled toy
(`hmc_false_witness`, MovesV/V4_hmc.lean:369).  KC1 sharpens that record into
a DIRECTION census: WHICH direction of the iff fails where at `HmcToy`.
NOTHING here asserts HMC (risk R9); the file's four statements are instance
checks at the toy only.

FILE PLACEMENT (recorded resolution): the blueprint assigns all KC units to
Kernels/HmcReduction.lean; that file exists (sibling cluster BP4-c2, units
KC2a/KC3/KC4) and may not be modified, and its own file-scope note directs
the remaining KC units into sibling files.  Hence <UnitId>.lean naming.

RECORDED RESOLUTION of the blueprint's either/or ("prove the OTHER direction
HOLDS toy-wide (or refute)"): the census resolves to a THREE-part record —
 (i) the ⊇/compose direction (factors ⟹ composite) FAILS at (0,0), depth 2
     (`hmcToy_compose_dir_fails_at_zero`) — the blueprint's sealed leg;
 (ii) the ⊆/projection direction HOLDS toy-wide at every DEPTH-2 template
     (one-step tails, both genres): both factor domains are `fullPart`, so
     the conjunction is unconditionally true;
 (iii) the ⊆/projection direction FAILS toy-wide at deep tails (depth ≥ 3):
     witness γ = .cons mv (.last mv), h₁ = (fun _ => 1), h₂ = (fun _ => 0) —
     the composite domain `nzPart 3` contains the append (first coordinate
     1 ≠ 0) while the TAIL factor domain `nzPart 2` misses h₂ = 0.  So the
     blueprint's parenthetical refute branch is the true one beyond depth 2;
     "the coupling kills ⊇ only" survives exactly ON the depth-2 perimeter
     where `hmc_false_witness` lives.  NOTE for the sibling KC2a prover
     (Kernels/HmcReduction.lean): leg (iii) shows the DomProj countermodel
     ∃-statement is already realizable AT HmcToy ITSELF — no new instance
     construction is needed.

deps: MovesV.V4_hmc vocabulary (HmcToy.S/TE/XD/c0/mv, fullPart, nzPart).
difficulty: routine-opus (decide-adjacent; the memberships are
fullPart_mem/nzPart_mem/nzPart_not_mem computations).

Build: cd lean && lake build LeanUrat.Kernels.KC1
-/
import LeanUrat.MovesV.V4_hmc

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open LeanUrat.MovesV

/-- KC1 leg (i) — the ⊇/compose direction fails at the census point (0,0):
¬(Mem (h₁ ++ h₂) ← factors) at h₁ = h₂ = 0, m = mv, γ = .last mv (the
blueprint's displayed form).  This is the SAME coupled point as
`hmc_false_witness`: both one-step domains are `fullPart 1` (contain the
zero height) while the composite domain is `nzPart 2` (misses it).
Sketch: intro; apply the implication to ⟨fullPart_mem, fullPart_mem⟩;
refute with nzPart_not_mem + simp [Hpt.append, Fin.append, Fin.addCases]. -/
theorem hmcToy_compose_dir_fails_at_zero :
    ¬ (((HmcToy.XD.dom (.last HmcToy.mv)).Mem (fun _ => 0) ∧
        (HmcToy.XD.dom (.last HmcToy.mv)).Mem (fun _ => 0)) →
       (HmcToy.XD.dom (.cons HmcToy.mv (.last HmcToy.mv))).Mem
          (Hpt.append (fun _ => 0) (fun _ => 0))) := by
  sorry

/-- KC1 leg (ii), `.last`-tail genre — the ⊆/projection direction HOLDS
toy-wide at depth-2 templates with a `.last` tail: both factor domains are
`fullPart 1`, so the conclusion is unconditionally true (the membership
hypothesis is not even needed).  Sketch: exact fullPart_mem twice. -/
theorem hmcToy_proj_dir_holds_lastTail
    {α β β' : HmcToy.S.Cell} (m : HmcToy.S.Move α β) (m₂ : HmcToy.S.Move β β')
    (h₁ : Hpt (HmcToy.S.dim m)) (h₂ : Hpt (HmcToy.S.dim m₂))
    (hmem : (HmcToy.XD.dom (.cons m (.last m₂))).Mem (Hpt.append h₁ h₂)) :
    (HmcToy.XD.dom (.last m)).Mem h₁ ∧ (HmcToy.XD.dom (.last m₂)).Mem h₂ := by
  sorry

/-- KC1 leg (ii), `.lastT`-tail genre — same census, terminal-move tail:
both factor domains are `fullPart 1`; unconditionally true. -/
theorem hmcToy_proj_dir_holds_lastTTail
    {α β : HmcToy.S.Cell} {v : VLabel 1} (m : HmcToy.S.Move α β)
    (mT : HmcToy.S.MoveT β v)
    (h₁ : Hpt (HmcToy.S.dim m)) (h₂ : Hpt (HmcToy.S.dimT mT))
    (hmem : (HmcToy.XD.dom (.cons m (.lastT mT))).Mem (Hpt.append h₁ h₂)) :
    (HmcToy.XD.dom (.last m)).Mem h₁ ∧ (HmcToy.XD.dom (.lastT mT)).Mem h₂ := by
  sorry

/-- KC1 leg (iii) — the refute branch of the blueprint's either/or: the
⊆/projection direction FAILS toy-wide once the tail is itself composite
(depth ≥ 3).  Witness (recorded, the sorry body is its verification):
γ = .cons mv (.last mv) (so the tail domain is `nzPart 2`), h₁ = (fun _ => 1),
h₂ = (fun _ => 0): the composite append has first coordinate 1 ≠ 0, hence
lies in `nzPart 3` (nzPart_mem), while the tail factor membership fails at
the zero height (nzPart_not_mem).  Consequence recorded for the sibling
gate KC2a: `DomProj` (KC2b's named law, Kernels/KC2b.lean) is violated at
HmcToy itself. -/
theorem hmcToy_proj_dir_fails_deep :
    ∃ (γ : Template 1 HmcToy.S HmcToy.c0) (h₁ : Hpt (HmcToy.S.dim HmcToy.mv))
      (h₂ : Hpt γ.D),
      (HmcToy.XD.dom (.cons HmcToy.mv γ)).Mem (Hpt.append h₁ h₂) ∧
      ¬ ((HmcToy.XD.dom (.last HmcToy.mv)).Mem h₁ ∧
         (HmcToy.XD.dom γ).Mem h₂) := by
  sorry

end LeanUrat.Kernels
