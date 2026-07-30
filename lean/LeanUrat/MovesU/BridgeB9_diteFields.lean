/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.DefsLedger

/-!
# IB-B9 — the two dite fields of the tautological roster (bridge campaign BP1)

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.3 (the
`bsplit`/`betaLeg` lines of the `bridgeRegData` display + the post-Codex
ASSEMBLY ORDER note: "a structure literal cannot postpone required fields —
the two dite fields are STANDALONE defs … which now runs BEFORE the record
unit IB-B8") / §4 group B (IB-B9).

UNIT: `bridgeBsplit`/`bridgeBetaLeg` — the split-exit and β-leg entry families
of the tautological roster, dite-guarded on the p-independent symbolic
determinant hypothesis `MovesS.DetHyp` (and on `0 < δ` for the leg depth),
junk `0` off the guard — plus the well-definedness lemmas: the value is
independent of WHICH `DetHyp` proof is supplied (proof irrelevance is
definitional for Prop binders; each lemma is `dif_pos` rewriting).  These are
EXACTLY the shapes `RegPin.bsplit_pin`/`RegPin.betaLeg_pin`
(DefsLedger.lean:495/505) demand at the tautological roster, so IB-B13's pin
lemmas are these laws read at `bridgeRegData`.

DEPS: none (LegRoster/legTarget from DefsLedger; bSplit/blockSolve/
blockSolveLt/powSubst from the MovesS solve corpus, already in DefsLedger's
import cone).  CONSUMERS: IB-B8 (`bsplit := bridgeBsplit`,
`betaLeg := bridgeBetaLeg`), IB-B13, IB-B15b.

PROOF SKETCH (R, ~15): both lemmas are `dif_pos` (for `bridgeBetaLeg` at the
conjunction witness `⟨hδ, hdet⟩`) + proof irrelevance of the `DetHyp`/`0 < δ`
components (`Subsingleton.elim` on Props, definitional).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

open scoped Classical in
/-- IB-B9 (def): the tautological roster's split-exit entry at (block e, state
    i) — under `DetHyp`, the real `MovesS.bSplit` with the real `blockSolveLt`
    legs, assembled over the chain's exact σ-index `Sigmas` (the
    `RegPin.bsplit_pin` RHS, verbatim); junk `0` without it. -/
noncomputable def bridgeBsplit {n : ℕ} (C : UCarriers n)
    (e : {e : ℕ // e ∈ Finset.Icc 1 n}) (i : C.T.State e.1) : RatFunc ℚ :=
  if hdet : MovesS.DetHyp C.T C.RB C.hK then
    ∑ σ' ∈ C.chain.Sigmas,
      MovesS.bSplit C.T C.RB C.hdc e.1 e.2
        (MovesS.blockSolveLt C.RB C.hdc C.hK hdet e.1) σ' i
  else 0

open scoped Classical in
/-- IB-B9 (def): the tautological roster's β-leg entry at (block e, leg l,
    depth δ) — under `0 < δ ∧ DetHyp`, `powSubst δ` of the real `blockSolve`
    at the leg's real `legTarget` (block, state), summed over `Sigmas` (the
    `RegPin.betaLeg_pin` RHS, verbatim); junk `0` off the guard. -/
noncomputable def bridgeBetaLeg {n : ℕ} (C : UCarriers n)
    (e : {e : ℕ // e ∈ Finset.Icc 1 n}) (l : LegRoster C.T e.1) (δ : ℕ) :
    RatFunc ℚ :=
  if h : 0 < δ ∧ MovesS.DetHyp C.T C.RB C.hK then
    MovesS.powSubst ⟨δ, h.1⟩
      (∑ σ' ∈ C.chain.Sigmas,
        MovesS.blockSolve C.T C.RB C.hdc C.hK h.2
          (legTarget C e.1 e.2 l).1.1 (legTarget C e.1 e.2 l).1.2
          (legTarget C e.1 e.2 l).2 σ')
  else 0

/-- IB-B9 (well-definedness): `bridgeBsplit`'s value at ANY supplied `DetHyp`
    proof — the `dif_pos` unfolding law IB-B13 reads at `bridgeRegData`. -/
theorem bridgeBsplit_eq_of_detHyp {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK)
    (e : {e : ℕ // e ∈ Finset.Icc 1 n}) (i : C.T.State e.1) :
    bridgeBsplit C e i
      = ∑ σ' ∈ C.chain.Sigmas,
          MovesS.bSplit C.T C.RB C.hdc e.1 e.2
            (MovesS.blockSolveLt C.RB C.hdc C.hK hdet e.1) σ' i := by
  unfold bridgeBsplit
  exact dif_pos hdet

/-- IB-B9 (well-definedness): `bridgeBetaLeg`'s value at ANY supplied `0 < δ`
    and `DetHyp` witnesses — the `dif_pos` unfolding law IB-B13 reads at
    `bridgeRegData`. -/
theorem bridgeBetaLeg_eq_of_pos {n : ℕ} (C : UCarriers n)
    (hdet : MovesS.DetHyp C.T C.RB C.hK)
    (e : {e : ℕ // e ∈ Finset.Icc 1 n}) (l : LegRoster C.T e.1)
    (δ : ℕ) (hδ : 0 < δ) :
    bridgeBetaLeg C e l δ
      = MovesS.powSubst ⟨δ, hδ⟩
          (∑ σ' ∈ C.chain.Sigmas,
            MovesS.blockSolve C.T C.RB C.hdc C.hK hdet
              (legTarget C e.1 e.2 l).1.1 (legTarget C e.1 e.2 l).1.2
              (legTarget C e.1 e.2 l).2 σ') := by
  unfold bridgeBetaLeg
  exact dif_pos ⟨hδ, hdet⟩

end LeanUrat.MovesU
