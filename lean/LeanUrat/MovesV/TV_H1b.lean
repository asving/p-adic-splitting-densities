/-  TV-H1b (BRIDGE BP3, cluster c2; E-phase skeleton) — [GATE, countermodel-
    first, risk R2] COUNTERMODEL ASSEMBLY for the banked W17ii clause (ii):
    the §3.G infinite-shDom RS4Chain over TV-H1a's carriers; deliverable =
    compiled `W17iiNeg.w17ii_false` OR the exact blocking law recorded.
    Blueprint: lean/notes/BRIDGE_BP3_TV_2026-07-30.md §3.G + §4 (TV-H1b).
    deps: TV-H1a.

    SEALED PREDICTION: `negChain` below is constructible with shDom Ŝ
    infinite and shWeightH ≡ 1 (pins stated); then `wsh17_pin`'s clause (ii)
    demands HasSum of the constant 1 over an infinite domain — false at every
    value — so `w17ii_false` compiles.  BLOCKER INVENTORY to clear or record
    (each may return "blocked by law L" with L named):
    - RS1Bundle's fields (βmeas ≡ 0; every guarded law empty-indexed at the
      TV-H1a carrier; nsNull := True per the A10 disclosure pattern);
    - pools_e0 / legs_reg: RegP at EVERY prime (PrimePools is FORCED total by
      prime_base) — empty-Act PoolHyps; the EscapeE0 Tendsto is over the
      empty-indexed vector space (subsingleton — constant tendsto);
    - rsh_interp: NOT hdet-vacuous (TV-H1a's negDetHyp check) — the Rsh
      evaluation identity must be discharged for real at every prime and the
      forced singleton Sigmas (n = 1: Σ vdeg = 1 admits exactly the one-verdict
      multiset); Rval ≡ 1 / decidedTotal ≡ 1 satisfy x3_total + rs1_equates;
      THE recorded plausible blocker, with legs_reg;
    - sh_realized at allActivePools = M.Pools (header resolution of TV_H1a):
      met by shEvt = univ (nonempty by boxpos), NOT by vacuity;
    - wshval_card then forces WshVal ≡ 1; wsh_ok/wsh_interp at the trivial
      pack WshP with val = 1.

    COEXISTENCE RULE (soundness — the M1 lesson; BINDING at prover phase):
    the sorried universal `w17ii_wave4` applies to EVERY RS4Chain, so a
    COMPILED `w17ii_false` + that sorried claim in one environment derives
    False.  Therefore: this module must NEVER import (or be imported
    alongside) LeanUrat.MovesV.V7_w17ii once `w17ii_false` is compiled —
    the filled file lands in quarantine (not reachable from the build root)
    OR in the SAME COMMIT as TV-H3's adjudicated repair of the clause (the
    H-cluster sequencing enforces the second).  At E-phase every piece here
    is sorried, so no negation is compiled and coexistence is safe.

    ================= EXECUTION RECORD (gate prover, 2026-07-30) ============
    VERDICT: COUNTERMODEL-COMPILED.  Every piece below was FILLED and the
    module built GREEN per-module (`lake build LeanUrat.MovesV.TV_H1b`,
    8571 jobs; import closure = MovesS.Interfaces + TV_H1a only — V7_w17ii
    NOT in the closure, so no environment ever contained both the sorried
    universal and the compiled negation).  Axiom census on the deliverables
    (`#print axioms`): w17ii_false / negChain_shDom_infinite /
    negChain_weight_one / negShapeFam_ne all EXACTLY
    [propext, Classical.choice, Quot.sound] — zero sorryAx.
    THE FILLED, GREEN-BUILT TEXT IS ARCHIVED AT
      lean/quarantine/TV_H1b_w17iiNeg_2026-07-30.lean.txt
    per the coexistence rule above (V7_w17ii's banked clause is still
    un-repaired in-tree, and TV-H3's repair is not in this commit); this
    in-tree module is RESTORED to the E-phase skeleton until the TV-H3
    repair commit re-lands the fill.  Blocker inventory outcome — ALL
    CLEARED, none blocked: RS1Bundle empty-indexed; pools_e0/legs_reg via a
    uniform empty-Act PoolHyp (EscapeE0's Tendsto = the constant map in the
    empty-indexed subsingleton Pi, `tendsto_const_nhds`); legs_read VACUOUS
    (allActivePools = M.Pools at the empty-state carrier, so its
    non-all-active premise is absurd); rsh_interp discharged FOR REAL — at
    the k = 0 singleton shape with σ0 = {(1,1)}, shConv's decomposition
    subtype is Unique and its leg product is empty, so
    Rsh = (WshP Ŝ₀).val · 1 = 1, evaluating to Rval ≡ 1 at every prime.
    The refutation: clause (ii) at (Ŝ₀, q₀ = 2) demands HasSum of the
    constant 1 over ↥(Set.univ : Set ℕ); summability would force 1 → 0
    along the cofinite filter (NeBot at the infinite index), against
    `tendsto_const_nhds` — contradiction via `tendsto_nhds_unique`.
    CONSEQUENCE for the pending adjudication (TV-H2 / ESCALATION E-1, Q4):
    the "PLAUSIBLE countermodel does not suffice" proviso of the Q4 ruling
    is MOOT — the countermodel is COMPILED, so `w17ii_wave4` clause (ii) is
    FALSE AS STATED and the statement change (the census-field repair menu
    (a′)/(b′) of §3.G REV 2) is now evidence-backed per the /goal decision
    rule.  TV-H3 must land the adjudicated repair in the SAME commit that
    re-lands this fill.
    ========================================================================= -/
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesV.TV_H1a

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV.W17iiNeg

/-- TV-H1b piece 1: the shape family — a singleton k = 0 shape (empty block
states admit no deeper τOf), σ0 := the forced verdict multiset.
[E-PHASE SKELETON RESTORED — the compiled fill is quarantined; see the
EXECUTION RECORD in the file header.] -/
noncomputable def negShapeFam : MovesS.ShapeFam negTable :=
  sorry

/-- TV-H1b pin: the family is nonempty (required — W17ii is vacuously TRUE
over an empty family, and the refutation instantiates at a member). -/
theorem negShapeFam_ne : negShapeFam.Sh.Nonempty := by
  sorry

/-- TV-H1b piece 2: THE COUNTERMODEL CHAIN — the ~30-field RS4Chain build
over TV-H1a's carriers per the blocker inventory in the file header; shallow
carriers per the sealed prediction: shDom := Set.univ (Hgt = ℕ, infinite),
shWeightH ≡ 1, shEvtH := univ, visH := a singleton, shEvt = univ. -/
noncomputable def negChain :
    MovesS.RS4Chain negTable negMS negRB negDegCons negKmatHyp negShapeFam :=
  sorry

/-- TV-H1b pin: the countermodel's shDom is INFINITE at every family member
(the clause-(ii) refutation's first leg). -/
theorem negChain_shDom_infinite :
    ∀ Ŝ ∈ negShapeFam.Sh, (negChain.shDom Ŝ).Infinite := by
  sorry

/-- TV-H1b pin: the countermodel's shallow weight is CONSTANT 1 (the
clause-(ii) refutation's second leg: constant 1 over an infinite domain has
no HasSum at any value). -/
theorem negChain_weight_one :
    ∀ (Ŝ : MovesS.Shape negTable) (h : negMS.Hgt) (q₀ : ℚ),
      negChain.shWeightH Ŝ h q₀ = 1 := by
  sorry

/-- TV-H1b DELIVERABLE (the sealed prediction): clause (ii) of the banked
W17ii FAILS at the countermodel chain — `¬ negChain.wsh17_pin`.  Proof
sketch: pick Ŝ (negShapeFam_ne) and a pool q₀ (pools_infinite ⟹ nonempty);
the pin's second conjunct is HasSum (fun _ : shDom Ŝ => 1) (WshVal Ŝ q₀) by
negChain_weight_one, impossible over the infinite index negChain_shDom_infinite
(a constant nonzero function on an infinite type is not summable).
QUARANTINE RULE binding at fill time — see the file header.  [EXECUTED: the
compiled proof lives in the quarantined fill; this skeleton sorry is NOT a
banked duty — it is the soundness-mandated placeholder until TV-H3.] -/
theorem w17ii_false : ¬ negChain.wsh17_pin := by
  sorry

end LeanUrat.MovesV.W17iiNeg
