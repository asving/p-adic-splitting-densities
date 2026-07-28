/-
Unit U15.present_exist_of_seeds  (HC-2 campaign, E-phase — blueprint §5 Layer C: the
PRESENT-EXIST discharge)
moves_ref: MovesD §2 PRESENT-EXIST row ("∀ N ≥ P.NP pol, Nonempty (Presented …) —
presentability at every level of L12's exact range (§C C.2)").
deps: U13, U14 (reprOf i ∈ PrefSet gives hcoh/hreal/hbox), U17/U18 (hnorm — or carried).
difficulty: easy-medium.
hypothesis_fields: **hseed = SEED-EXIST (HC-1; the rev-2 reprOf + KeysLawful form — the
ONLY display, stated here verbatim per audit GAP-5)**; hnorm (dischargeable by U17c's
`presentNorm_polOM`, which itself carries `StageTransHyp` + `OmUniqHyp`); hd4 (N-5);
hunp (K2).
N-QUEUE RESTATEMENT (2026-07-28, sign-off round): gains
  `hd4  : ∀ i, RootD4 (reprOf i)` (N-5 — the HC-1-seam-adjacent addition placed where
   the content lives: HC-1's seed constructions sit over the decided cluster strata,
   where §B2-DEF D.4's root clause is the note's own standing hypothesis), and
  `hunp : ∀ i N keys S vOf, SeedFreshUnpinned (reprOf i) n N S vOf` (K2 — the per-step
   "fresh supports unpinned" condition, ∀-seed form because U15's seed is
   choice-extracted from `hseed`'s ∃; its eventual discharge is U10's (ZC)+DOM geometry
   over PrefSet members, at which point this binder retires).
SEED-EXIST itself is byte-UNCHANGED (the HC-1 seam display stays frozen); the additions
are separate named binders. The wave-4 negotiation decides whether they fold into the
SEED-EXIST conclusion.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U13_assembly

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- PRESENT-EXIST = SEED-EXIST + assembly: the reduction is the deliverable, the seed is
the honest residue (blueprint §2 Wall B). -/
theorem present_exist_of_seeds {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n}
    (hseed : ∀ (i : PrefIdx n (polOM p F) P) (N : ℕ), P.NP (polOM p F) ≤ N →
       ∃ keys : ℕ → Polynomial ℤ_[p], KeysLawful (reprOf i) keys ∧
         Nonempty (PresentSeed p F (reprOf i) n N keys))
    (hnorm : PresentNorm n (polOM p F) P)
    (hd4 : ∀ i : PrefIdx n (polOM p F) P, RootD4 (reprOf i))
    (hunp : ∀ (i : PrefIdx n (polOM p F) P) (N : ℕ) (keys : ℕ → Polynomial ℤ_[p])
       (S : PresentSeed p F (reprOf i) n N keys) (vOf : VOf p (n * N)),
       SeedFreshUnpinned (reprOf i) n N S vOf) :
    ∀ N : ℕ, P.NP (polOM p F) ≤ N →
      Nonempty (Presented p F n N (n * N) (polOM p F) P) := by
  intro N hN
  -- `N ≥ 1` from `N ≥ P.NP`: both branches of the piecewise `Shape.NP` are `≥ 1`
  -- (`NPband = 1 + …`; else-branch `= 1`).
  have hNP1 : 1 ≤ P.NP (polOM p F) := by
    unfold Shape.NP
    split_ifs with h
    · unfold ShapePrefix.NPband; omega
    · exact le_refl 1
  have h1N : 1 ≤ N := le_trans hNP1 hN
  -- assemble the presented family: `jet i` = U13's `jetSetup_of_seed` fired on the seed
  -- SEED-EXIST hands us at level `N` (its `keys`, lawfulness, and a `PresentSeed`), plus the
  -- coherence/realizability/box data carried by `reprOf i ∈ PrefSet`; `hnorm` verbatim.
  refine ⟨⟨fun i => ?_, hnorm⟩⟩
  -- SEED-EXIST at this class and level
  obtain ⟨hkeys, hSne⟩ := (hseed i N hN).choose_spec
  -- `reprOf i` is the chosen PrefSet representative of the η-class `i`
  have hmem : reprOf i ∈ PrefSet n (polOM p F) P := i.2.choose_spec.1
  obtain ⟨-, hcoh, hreal, hbox, -⟩ := hmem
  exact (jetSetup_of_seed hkeys hSne.some h1N hcoh hreal hbox (hd4 i)
    (fun _ _ _ _ => 0) (hunp i N _ hSne.some _)).some

end LeanUrat.MovesJ
