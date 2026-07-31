/-
Unit U10d-NEG — the COMPILED NEGATION WITNESS for `zc_step_confine` (U10d; queue item 17
evidence; PROBE-C round, 2026-07-31; the U1-NEG / U27_OBSTRUCTION durability pattern).

WHAT IS REFUTED.  `LeanUrat/HC2/U10_zcStep.lean:897–902` states (sorried;
BLOCKED-SUSPECT-FALSE record of 2026-07-31 at its sorry):

  theorem zc_step_confine ... :
    ∀ j : Fin (n * N), (mkSigma H n N S vOf (i+2)).pinned j = true →
      (boxChart n N j).2 < H.prevRim n (i + 1)

— the rim-confinement bound quantified over ALL pins of the new state Σ_{i+2}.  The §C
rim rule confines only FRESH cuts (U3 `mkFresh_band`, PROVED); the ∀-pins rendering is an
E-phase over-quantification.  This file compiles the record's exact mechanism:

* `mkSigma_pinned_succ` / `mkSigma_pinned_mono` — pins PERSIST down the whole chain
  (spec clause (2) `Or.inl` on the witness branch; the fallback branches keep the state
  verbatim — machine-checked from the `pinTransportSystem` dite alone).
* `mkSigma_one_pinned_of_strip` — the ROOT read pins every coordinate of its strip
  roster: existence of the spec system at read 0 is FREE (`freshAttach_exists` at the
  unpinned `Σ₀ = topLocus`, exactly U7's `mkSigma_recursion_zero` route), and spec
  clause (2) `Or.inr` fires on the strip clause through the coordinate.
* `prevRim_le_root` — THE RIM CHAIN: `prevRim n (i+1) = μ_i·cW_i ≤ μ₀·cW₀` (per step:
  `C3_widthConfine` + coherence window containment `s0'+w' ≤ μ` + width chain
  `D' = cW`).
* `confine_bound_fails` — THE REFUTATION KERNEL: on ANY legal configuration with
  `s0₀ = 0`, `0 < ustar₀`, `wSide₀ < n` (InBox only demands `s0₀ + wSide₀ ≤ n`), the
  coordinate `(0, wSide₀)` is a STRIP cut of read 0 (height `0 < ustar₀ = line₀.at
  wSide₀` by `hLineU` at `s0₀ = 0`, `Dwidth₀ = 1` — in-band non-value), hence pinned in
  EVERY `Σ_{i+2}`; yet `prevRim n (i+1) ≤ μ₀·cW₀ ≤ wSide₀·Dwidth₀ = wSide₀`
  (`C3_widthConfine` at the root's coherence-forced `Dwidth₀ = deg Φ₀ = 1` + the rim
  chain) — the claimed bound FAILS at that pin, at EVERY i.
* `zcStepConfineStmt_false_of_config` — the ∀-sentence (`ZcStepConfineStmt`, the LOCAL
  byte-identical statement copy) is FALSE at `(p, F)` GIVEN any such configuration.

M1 COEXISTENCE DISCIPLINE.  This file does NOT import `U10_zcStep` (the module holding
the sorried universal it refutes).  The refuted statement's shape is restated below as
the LOCAL byte-identical copy `ZcStepConfineStmt` (provenance: `U10_zcStep.lean:897–902`,
HEAD 2026-07-31 — binders and conclusion verbatim, wrapped as a named ∀-Prop).  All other
vocabulary (`mkSigma`, `pinTransportSystem`, `IsFreshAttach`, `PresentSeed`, `VOf`,
`boxChart`, `stripSet`, `inFreshBand`, `IsValueCoord`, `History.prevRim`,
`HistoryCoherent`, `Realizable`, `InBox`) is imported from its home Defs modules
(`HC2/Defs`, `MovesC/Defs`, `MovesD/Defs` — definitions-only, grep-verified sorry-free
2026-07-31) and the sorry-free proved units `HC2/SharedZC`, `HC2/U7_sigmaRec`
(`clause_assign`/`mkFresh_codim`/`freshAttach_exists`), `MovesC/C3_widthConfine` — NOT
copied and NOT co-resident with any sorried statement of the U10 module.

HONESTY PERIMETER (the U1-NEG pattern — recorded, not hidden).  The refutation is
unconditional over its hypothesis class; the INHABITATION of that class (a concrete
2-node coherent+realizable history with a lawful `PresentSeed`) is NOT compiled here:
any 2-node `HistoryCoherent` history requires `TransitionCoreL` at the root read — the
constructed child stage that is exactly the HK-15/HK-18 Block-G frontier (sorried
skeletons at HEAD; HK-37's header records "NO CONCRETE 2-NODE GATE EXISTS ON DISK YET")
— the standing task-#44 / 2-node-gate blocker.  When the 2-node gate lands, instantiate
`zcStepConfineStmt_false_of_config` with it (its root read must satisfy the recipe's
`s0₀ = 0 < ustar₀`, `wSide₀ < n` — U27/U31-gate-shaped roots do) to close the last leg.

deps: HC2.Defs, HC2.SharedZC, HC2.U7_sigmaRec, MovesC.C3_widthConfine (all sorry-free).
axioms: Lean core only (verified by the #print axioms at EOF).

M1 DATED NOTE (2026-07-31, queue item 17 EXECUTED — Asvin sign-off on the consolidated
queue): this leaf refutes the OLD ∀-pins form of `zc_step_confine` ONLY — the byte copy
`ZcStepConfineStmt` below (provenance `U10_zcStep.lean:897–902` at the PRE-repair HEAD).
At the repaired HEAD, `zc_step_confine` is RESTATED to the adjudicated fresh-cut
restriction (∀ j, (∃ cl ∈ mkFresh(i+1).clauses, j ∈ cl.support) → j's base < prevRim n
(i+1)) and PROVED from U3's `mkFresh_band`; the refutation mechanism here (old pins
persisting beyond the shrinking rim) does not touch the repaired form, whose quantifier
never sees old pins. The leaf stays intact as the durable evidence for the fence event;
no sorried copy of the OLD form remains anywhere in-tree (M1 coexistence rule satisfied
in the strongest sense: the refuted statement now exists ONLY inside this negation
witness).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.SharedZC
import LeanUrat.HC2.U7_sigmaRec
import LeanUrat.MovesC.C3_widthConfine

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD SharedZC

namespace U10dNeg

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- LOCAL BYTE-IDENTICAL STATEMENT COPY (provenance: `LeanUrat/HC2/U10_zcStep.lean:897–902`,
`zc_step_confine`, HEAD 2026-07-31): the sorried universal this unit refutes, wrapped as a
named ∀-Prop at fixed `(p, F)` — binders `{n N} {H} {keys} (S) (vOf) (hcoh) (hreal) (hbox)
(hN) (i) (hi1)` and the conclusion `∀ j, pinned j = true → (boxChart n N j).2 < prevRim n
(i+1)` verbatim.  NEVER prove this Prop; it exists so the refutation below can name its
target without importing the module that holds the sorried original (M1 rule). -/
def ZcStepConfineStmt (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop :=
  ∀ {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)),
    HistoryCoherent H → Realizable H → InBox n H → 1 ≤ N →
    ∀ (i : ℕ) (hi1 : i + 1 < H.nodes.length),
    ∀ j : Fin (n * N), (mkSigma H n N S vOf (i+2)).pinned j = true →
      (boxChart n N j).2 < H.prevRim n (i + 1)

/-- PIN PERSISTENCE, one step: every pin of `Σ_m` is a pin of `Σ_{m+1}`.  On the witness
branch this is spec clause (2) `Or.inl`; on both fallback branches (`m ≥ len`, or no spec
witness) the state's pins are kept verbatim.  No hypotheses beyond the pin itself. -/
lemma mkSigma_pinned_succ {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)) (m : ℕ) (c : Fin (n * N))
    (hc : (mkSigma H n N S vOf m).pinned c = true) :
    (mkSigma H n N S vOf (m + 1)).pinned c = true := by
  by_cases hm : m < H.nodes.length
  · have hstep : mkSigma H n N S vOf (m + 1)
        = pinTransportSystem (mkSigma H n N S vOf m) (S.Theta m)
            (mkFresh H n N S vOf m hm) := by
      show (if hi' : m < H.nodes.length then
          pinTransportSystem (mkSigma H n N S vOf m) (S.Theta m) (mkFresh H n N S vOf m hi')
        else mkSigma H n N S vOf m) = _
      rw [dif_pos hm]
    rw [hstep]
    by_cases hEx : ∃ D' : Locus p (n * N),
        IsFreshAttach (mkSigma H n N S vOf m) (S.Theta m) (mkFresh H n N S vOf m hm) D'
    · exact ((pinTransportSystem_spec (mkSigma H n N S vOf m) (S.Theta m)
        (mkFresh H n N S vOf m hm) hEx).2.1 c).mpr (Or.inl hc)
    · unfold pinTransportSystem
      rw [dif_neg hEx]
      exact hc
  · have hstep : mkSigma H n N S vOf (m + 1) = mkSigma H n N S vOf m := by
      show (if hi' : m < H.nodes.length then
          pinTransportSystem (mkSigma H n N S vOf m) (S.Theta m) (mkFresh H n N S vOf m hi')
        else mkSigma H n N S vOf m) = _
      rw [dif_neg hm]
    rw [hstep]
    exact hc

/-- PIN PERSISTENCE, transitive: pins of `Σ_m` survive into every later `Σ_{m'}`. -/
lemma mkSigma_pinned_mono {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)) (m m' : ℕ) (hmm : m ≤ m')
    (c : Fin (n * N)) (hc : (mkSigma H n N S vOf m).pinned c = true) :
    (mkSigma H n N S vOf m').pinned c = true := by
  induction m', hmm using Nat.le_induction with
  | base => exact hc
  | succ k hk ih => exact mkSigma_pinned_succ S vOf k c ih

/-- THE ROOT READ PINS ITS STRIP ROSTER: every coordinate of `stripSet` at read 0 is
pinned in `Σ₁`.  Existence of the spec system at read 0 is free (nothing is pinned on
`Σ₀ = topLocus` — U7's `mkSigma_recursion_zero` route: `clause_assign` + `mkFresh_codim`
+ `freshAttach_exists`), and spec clause (2) `Or.inr` fires on the strip clause through
the coordinate (support `{c}`, `C1_stripClause`'s chosen witness). -/
lemma mkSigma_one_pinned_of_strip {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)) (h0 : 0 < H.nodes.length)
    (c : Fin (n * N)) (hc : c ∈ stripSet H n N 0 (H.nodes[0]'h0)) :
    (mkSigma H n N S vOf 1).pinned c = true := by
  classical
  have hasg : ∀ cl ∈ (mkFresh H n N S vOf 0 h0).clauses, ∃ u : Fin (n * N) → ZMod p,
      ∀ x, cl.sat x ↔ ∀ c' ∈ cl.support, x c' = u c' :=
    fun cl hcl => clause_assign cl (mkFresh_codim S vOf 0 h0 cl hcl)
  have hunp : ∀ c' : Fin (n * N), (mkSigma H n N S vOf 0).pinned c' = true →
      ¬ ∃ cl ∈ (mkFresh H n N S vOf 0 h0).clauses, c' ∈ cl.support := by
    intro c' hc'
    rw [show (mkSigma H n N S vOf 0).pinned c' = false from rfl] at hc'
    exact Bool.noConfusion hc'
  have hEx : ∃ D' : Locus p (n * N),
      IsFreshAttach (mkSigma H n N S vOf 0) (S.Theta 0) (mkFresh H n N S vOf 0 h0) D' :=
    freshAttach_exists (mkSigma H n N S vOf 0) (S.Theta_uni 0) (mkFresh H n N S vOf 0 h0)
      hasg hunp
  have hspec := pinTransportSystem_spec (mkSigma H n N S vOf 0) (S.Theta 0)
    (mkFresh H n N S vOf 0 h0) hEx
  have hstep : mkSigma H n N S vOf 1
      = pinTransportSystem (mkSigma H n N S vOf 0) (S.Theta 0)
          (mkFresh H n N S vOf 0 h0) := by
    show (if hi' : 0 < H.nodes.length then
        pinTransportSystem (mkSigma H n N S vOf 0) (S.Theta 0) (mkFresh H n N S vOf 0 hi')
      else mkSigma H n N S vOf 0) = _
    rw [dif_pos h0]
  rw [hstep]
  refine ((hspec.2.1 c).mpr (Or.inr ⟨(C1_stripClause (p := p) c).choose, ?_, ?_⟩))
  · show (C1_stripClause (p := p) c).choose ∈ mkFreshClauses H n N S vOf 0 h0
    unfold mkFreshClauses
    exact List.mem_append_left _
      (List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hc, rfl⟩)
  · rw [(C1_stripClause (p := p) c).choose_spec.1]
    exact Finset.mem_singleton_self c

/-- THE RIM CHAIN: `prevRim n (i+1) = μ_i·cW_i ≤ μ₀·cW₀` along any coherent history —
per step `μ_{k+1}·cW_{k+1} ≤ wSide_{k+1}·Dwidth_{k+1}` (`C3_widthConfine`)
`= wSide_{k+1}·cW_k` (coherence width chain) `≤ μ_k·cW_k` (coherence window containment
`s0' + w' ≤ μ`). -/
lemma prevRim_le_root {n : ℕ} {H : History p F} (hcoh : HistoryCoherent H)
    (h0 : 0 < H.nodes.length) :
    ∀ i : ℕ, i < H.nodes.length →
      H.prevRim n (i + 1) ≤ (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth := by
  intro i
  induction i with
  | zero =>
      intro _
      have hone : H.prevRim n 1 = (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth := by
        show (H.nodes[0]?).elim n (fun ν => ν.μ * ν.childWidth) = _
        rw [List.getElem?_eq_getElem h0]
        rfl
      exact le_of_eq hone
  | succ k ih =>
      intro hk1
      have hk : k < H.nodes.length := by omega
      obtain ⟨-, -, -, -, hwin, hDw, -⟩ := hcoh.2.2.2 k hk1
      have hstep : H.prevRim n (k + 2)
          = (H.nodes[k+1]'hk1).μ * (H.nodes[k+1]'hk1).childWidth := by
        show (H.nodes[k+1]?).elim n (fun ν => ν.μ * ν.childWidth) = _
        rw [List.getElem?_eq_getElem hk1]
        rfl
      have hprev : H.prevRim n (k + 1)
          = (H.nodes[k]'hk).μ * (H.nodes[k]'hk).childWidth := by
        show (H.nodes[k]?).elim n (fun ν => ν.μ * ν.childWidth) = _
        rw [List.getElem?_eq_getElem hk]
        rfl
      have hchain : (H.nodes[k+1]'hk1).μ * (H.nodes[k+1]'hk1).childWidth
          ≤ (H.nodes[k]'hk).μ * (H.nodes[k]'hk).childWidth := by
        calc (H.nodes[k+1]'hk1).μ * (H.nodes[k+1]'hk1).childWidth
            ≤ (H.nodes[k+1]'hk1).wSide * (H.nodes[k+1]'hk1).Dwidth :=
              C3_widthConfine (H.nodes[k+1]'hk1)
          _ = (H.nodes[k+1]'hk1).wSide * (H.nodes[k]'hk).childWidth := by rw [hDw]
          _ ≤ (H.nodes[k]'hk).μ * (H.nodes[k]'hk).childWidth :=
              Nat.mul_le_mul (le_trans (Nat.le_add_left _ _) hwin) le_rfl
      rw [hstep]
      exact le_trans hchain (by rw [← hprev]; exact ih hk)

/-- THE REFUTATION KERNEL (the in-file record's exact recipe, U10_zcStep.lean:909–925):
on ANY configuration satisfying `zc_step_confine`'s own hypothesis class (coherent; `N ≥ 1`;
`i + 1 < len`) whose ROOT read has `s0₀ = 0`, `0 < ustar₀`, `wSide₀ < n`, the coordinate
`(0, wSide₀)` — box index `n − 1 − wSide₀` — is a STRIP cut of read 0, hence pinned in
`Σ_{i+2}` (pin persistence), yet sits at-or-beyond the rim `prevRim n (i+1)`: the claimed
confinement bound FAILS at it.  (`hreal`/`hbox` are not consumed: the violation needs
none of realizability/box placement — strictly stronger than refuting inside the class.) -/
theorem confine_bound_fails {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hN : 1 ≤ N)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length) (h0 : 0 < H.nodes.length)
    (hs0 : (H.nodes[0]'h0).s0 = 0)
    (hu : 0 < (H.nodes[0]'h0).ustar)
    (hw : (H.nodes[0]'h0).wSide < n) :
    ∃ j : Fin (n * N), (mkSigma H n N S vOf (i+2)).pinned j = true ∧
      ¬ ((boxChart n N j).2 < H.prevRim n (i + 1)) := by
  classical
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hw
  -- the root frame's key has degree 1 (coherence clause 1), so Dwidth₀ = 1
  have hD1 : (H.nodes[0]'h0).Dwidth = 1 := by
    rw [(H.nodes[0]'h0).hDwidth]
    exact hcoh.1 h0
  -- the witness box index: level 0, base index wSide₀ (chart is base-DESCENDING)
  have hjlt : n - 1 - (H.nodes[0]'h0).wSide < n * N := by
    calc n - 1 - (H.nodes[0]'h0).wSide < n := by omega
      _ = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * N := Nat.mul_le_mul_left n hN
  have hbc1 : (boxChart n N ⟨n - 1 - (H.nodes[0]'h0).wSide, hjlt⟩).1 = 0 := by
    show (n - 1 - (H.nodes[0]'h0).wSide) / n = 0
    exact Nat.div_eq_of_lt (by omega)
  have hbc2 : (boxChart n N ⟨n - 1 - (H.nodes[0]'h0).wSide, hjlt⟩).2
      = (H.nodes[0]'h0).wSide := by
    show n - 1 - (n - 1 - (H.nodes[0]'h0).wSide) % n = (H.nodes[0]'h0).wSide
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  -- read-0 height and floor at the witness coordinate
  have hht0 : H.htH 0 (boxChart n N ⟨n - 1 - (H.nodes[0]'h0).wSide, hjlt⟩) = 0 := by
    unfold History.htH
    rw [hbc1]
    simp
  have hfl : H.floorH 0 (boxChart n N ⟨n - 1 - (H.nodes[0]'h0).wSide, hjlt⟩).2 = ⊥ := rfl
  -- root fine slot and slot valuation at base wSide₀ (`Dwidth₀ = 1`, `s0₀ = 0`, `hLineU`)
  have hfs : (H.nodes[0]'h0).fineSlot (H.nodes[0]'h0).wSide = (H.nodes[0]'h0).wSide := by
    unfold Node.fineSlot
    rw [hD1, Nat.div_one]
  have hsv : (H.nodes[0]'h0).slotVal (H.nodes[0]'h0).wSide = (H.nodes[0]'h0).ustar := by
    unfold Node.slotVal
    rw [hD1, Nat.mul_one]
    have hLU := (H.nodes[0]'h0).hLineU
    rw [hs0, hD1, Nat.zero_add, Nat.mul_one] at hLU
    exact hLU
  -- the witness is a read-0 STRIP cut: in-band (height 0 ∈ (⊥, ustar₀]), non-value (0 ≠ ustar₀)
  have hband : inFreshBand H n (boxChart n N) 0 (H.nodes[0]'h0)
      ⟨n - 1 - (H.nodes[0]'h0).wSide, hjlt⟩ := by
    unfold inFreshBand
    refine ⟨?_, ?_, ?_⟩
    · rw [hbc2]
      show (H.nodes[0]'h0).wSide < n
      exact hw
    · rw [hfl, hht0]
      exact WithBot.bot_lt_coe 0
    · rw [hht0, hbc2, hfs, hsv]
      exact le_of_lt hu
  have hnotval : ¬ IsValueCoord H (boxChart n N) 0 (H.nodes[0]'h0)
      ⟨n - 1 - (H.nodes[0]'h0).wSide, hjlt⟩ := by
    unfold IsValueCoord
    rintro ⟨-, hht⟩
    rw [hht0, hbc2, hfs, hsv] at hht
    exact (ne_of_lt hu) hht
  have hstrip : (⟨n - 1 - (H.nodes[0]'h0).wSide, hjlt⟩ : Fin (n * N))
      ∈ stripSet H n N 0 (H.nodes[0]'h0) := by
    unfold stripSet
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hband, hnotval⟩
  -- the pin, persisted down the chain to Σ_{i+2}
  have hpin : (mkSigma H n N S vOf (i + 2)).pinned
      ⟨n - 1 - (H.nodes[0]'h0).wSide, hjlt⟩ = true :=
    mkSigma_pinned_mono S vOf 1 (i + 2) (by omega) _
      (mkSigma_one_pinned_of_strip S vOf h0 _ hstrip)
  -- the bound violation: prevRim n (i+1) ≤ μ₀·cW₀ ≤ wSide₀·Dwidth₀ = wSide₀
  have hrim : H.prevRim n (i + 1) ≤ (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth :=
    prevRim_le_root hcoh h0 i (by omega)
  have hroot : (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth
      ≤ (H.nodes[0]'h0).wSide := by
    have h := C3_widthConfine (H.nodes[0]'h0)
    rw [hD1, Nat.mul_one] at h
    exact h
  refine ⟨⟨n - 1 - (H.nodes[0]'h0).wSide, hjlt⟩, hpin, ?_⟩
  rw [hbc2]
  exact Nat.not_lt.mpr (le_trans hrim hroot)

/-- THE NEGATION WITNESS: the ∀-sentence `ZcStepConfineStmt` (the byte-identical local
copy of `zc_step_confine`'s statement) is FALSE at `(p, F)` GIVEN any legal configuration
whose root read satisfies the recipe (`s0₀ = 0`, `0 < ustar₀`, `wSide₀ < n`).  The
inhabitation of the configuration class is the standing 2-node-gate blocker — see the
module header's honesty perimeter. -/
theorem zcStepConfineStmt_false_of_config
    (hwit : ∃ (n N : ℕ) (H : History p F) (keys : ℕ → Polynomial ℤ_[p])
      (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)),
      HistoryCoherent H ∧ Realizable H ∧ InBox n H ∧ 1 ≤ N ∧
      ∃ (i : ℕ) (hi1 : i + 1 < H.nodes.length) (h0 : 0 < H.nodes.length),
        (H.nodes[0]'h0).s0 = 0 ∧ 0 < (H.nodes[0]'h0).ustar ∧
        (H.nodes[0]'h0).wSide < n) :
    ¬ ZcStepConfineStmt p F := by
  intro hstmt
  obtain ⟨n, N, H, keys, S, vOf, hcoh, hreal, hbox, hN, i, hi1, h0, hs0, hu, hw⟩ := hwit
  obtain ⟨j, hpin, hviol⟩ := confine_bound_fails S vOf hcoh hN i hi1 h0 hs0 hu hw
  exact hviol (hstmt S vOf hcoh hreal hbox hN i hi1 j hpin)

end U10dNeg

-- Axiom audit: Lean core only ({propext, Classical.choice, Quot.sound}); in particular
-- NO sorryAx — the witness never touches the sorried U10 module (M1 coexistence rule).
#print axioms U10dNeg.mkSigma_pinned_mono
#print axioms U10dNeg.mkSigma_one_pinned_of_strip
#print axioms U10dNeg.prevRim_le_root
#print axioms U10dNeg.confine_bound_fails
#print axioms U10dNeg.zcStepConfineStmt_false_of_config

end LeanUrat.MovesJ
