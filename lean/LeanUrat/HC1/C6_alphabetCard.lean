/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.ScratchC6
import LeanUrat.HC1.CL04_addrDichotomy
import LeanUrat.Moves.L5_realCofin_R3
import LeanUrat.Moves.L5_realDomination_R3

/-!
# HC1.C6_alphabetCard — the alphabet cardinality + the fullness DICHOTOMY (G-4)

moves_ref: MOVES 2160–2165 "= [F_{k+1} : F_p] … EXACTLY WHEN every height in γ's
slot tree is attainable … and STRICTLY SMALLER at shallow heights". deps: T7, T8;
ScratchC6 (the 2026-07-28 certificates), CL04 (the address vocabulary); Moves
`L5_realCofin_R3`, `L5_realDomination_R3` (clean). BOTH directions (audit G-4):
fullness ⟺ every slot height is attainable, and STRICTLY SMALLER on the failing
side. Still no unconditional fullness claim (the rev-D¹¹c fix stands).
difficulty: medium. hyp: `cleanThreshold` on conjunct 2 (below).

## ITEM-18 EXECUTION RECORD (statement repair, Asvin sign-off 2026-07-31)

**Pre-repair statement REFUTED-AS-STATED.** The ScratchC6 certificates
(2026-07-28, all Lean-core) show conjunct 2's RHS is a THEOREM
(`C6_conjunct2_rhs_always`: level-set membership forces attainability — the D-10
typing quantified the note's condition over the WRONG index set), so the fenced
iff asserted UNCONDITIONAL fullness (`C6_forces_unconditional_fullness`) —
refuted at shallow heights by the COMPILED countermodel `Tshallow` (CL-01a/b/c;
`CL01c_shallowTower.lean`: singleton level set at (0,0), card 𝔸 ≤ 3 < 4 = card F₄).
Per the BP5 §3.1 LANDING GATE the compiled negation
(`C6_pre_repair_refuted_at_Tshallow`) lands ATOMICALLY with this repair,
retargeted at the frozen `C6_stmt_pre_repair` copy (both in CL01c's file).

**The repair (ratified: the "independence/clean-threshold hypothesis on
conjunct 2").** Conjunct 2 gains the named hypothesis `Tower.cleanThreshold b γ`
(below): every ℤ-ALIGNED ADDRESS of block b is attainable at γ — the note's own
fullness condition (MOVES 2160–2165), typed over addresses per ScratchC6's D-10
diagnosis, in CL-04's display-(3) vocabulary. WEAKEST-FORM rationale: by the
CL-04 probe record (PROBE REPORT, outcome (b)) fullness is believed EQUIVALENT
to this condition (the CI-1 equidistribution theorem + CI-2/CI-3 line fullness/
independence + CI-4 card bridge), so no strictly weaker non-trivial hypothesis
can restore the iff; the D.9(b) clean-threshold regime (each stage's slot
heights clear its D.9(b) bound) is the displayed sufficient INSTANCE, hence the
hypothesis name. Conjuncts 1 and 3 are unconditional and remain unguarded.

**Proof status.** Conjunct 1 PROVED (T7, via `C6_conjunct1_closable`).
Conjunct 2 → PROVED (`C6_conjunct2_rhs_always`). Conjunct 3 PROVED
(`C6_conjunct3_hyp_false`: the hypothesis is refutable, ex falso). Conjunct 2 ⟸
(cleanThreshold → fullness) is THE remaining honest sorry — exactly CL-05's
specified obligation (CL04 PROBE REPORT: CI-1 slot-class equidistribution,
CI-2 digit-line structure, CI-3 slot-min orthogonality/joint independence,
CI-4 `card F_{K+1} = |F_Q|^{∏g}`); real new mathematics, NOT in the corpus at
HEAD. The statement is now believed TRUE (probe-backed); the pre-repair FALSE
form survives only as the frozen copy + compiled negation in CL01c.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- **The card-K bridge (F-2, sign-off event 2026-07-28, blueprint §9.2):** every
stage residue field of a tower has p-power cardinality, `Nat.card ↥K = p^d` with
`d = [K : F_p] ≥ 1` — the bridge C6's conjuncts 2–3 consume. Underivable before the
F-2 char pin `Tower.hcharF : CharP F p` (round-2 fleet kernel: `Stage p F` carries
no characteristic tie, so `Nat.card K` was a power of char F, junk off char p); the
pin records the note's own setting (F_{k+1}/F_p extensions, MOVES 2148–2165). -/
theorem C6_cardK_bridge {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (k : Fin (T.K + 1)) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card ↥(T.stg k).K = p ^ d := by
  haveI : CharP F p := T.hcharF
  haveI : Fintype ↥(T.stg k).K := Fintype.ofFinite _
  haveI : CharP ↥(T.stg k).K p :=
    RingHom.charP (T.stg k).K.subtype (T.stg k).K.subtype.injective p
  obtain ⟨n, -, hn⟩ := FiniteField.card ↥(T.stg k).K p
  exact ⟨(n : ℕ), n.2, by rw [Nat.card_eq_fintype_card, hn]⟩

/-- **The clean-threshold (full-attainability) hypothesis** (item-18 repair,
2026-07-31): every ℤ-aligned address of block `b` is attainable at height `γ` —
the note's fullness condition (MOVES 2160–2165 "EXACTLY WHEN every height in γ's
slot tree is attainable"), typed over ADDRESSES per the D-10 correction, in
CL-04's display-(3) vocabulary. The D.9(b) clean-threshold regime is the
displayed sufficient instance; per the CL-04 probe record, fullness is believed
EQUIVALENT to this condition, making it the weakest truth-restoring hypothesis
for conjunct 2. -/
def Tower.cleanThreshold {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) : Prop :=
  ∀ s : T.Addr b, T.aligned γ s → T.attainable γ s

/-- Unit C6 (REPAIRED at item 18, 2026-07-31 — the pre-repair form is frozen as
`C6_stmt_pre_repair` with its compiled `Tshallow` negation in CL01c's file):
`#𝔸 = p^aDim`; on nonempty level sets, UNDER THE CLEAN-THRESHOLD HYPOTHESIS
(every aligned address attainable), fullness (𝔸 = the full value field
F_{K+1} = the top stage's K, in cardinality) holds exactly when every level-set
slot is attainable; and unconditionally, an unattainable level-set slot forces
`aDim < log_p card F_{K+1}`. -/
theorem C6_alphabetCard {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (hne : (T.levelSet b γ).Nonempty) :
    Nat.card ↥(T.alphabet b γ) = p ^ T.aDim b γ ∧
    (T.cleanThreshold b γ →
      (Nat.card ↥(T.alphabet b γ) = Nat.card ↥(T.stg (Fin.last T.K)).K ↔
        ∀ c : ↥(T.levelSet b γ), ∃ y : ↥(T.stg 0).FQ,
          T.typComposite b γ (Pi.single c y) ≠ 0)) ∧
    ((∃ c : ↥(T.levelSet b γ), ∀ y : ↥(T.stg 0).FQ,
        T.typComposite b γ (Pi.single c y) = 0) →
      T.aDim b γ < Nat.log p (Nat.card ↥(T.stg (Fin.last T.K)).K)) := by
  refine ⟨C6_conjunct1_closable T b γ, ?_, ?_⟩
  · intro hclean
    constructor
    · -- → : the RHS is a theorem (attainability is automatic on the level set)
      intro _
      exact C6_conjunct2_rhs_always T b γ
    · -- ⟸ : fullness from the clean threshold — THE OPEN CL-05 OBLIGATION
      -- (CL04 PROBE REPORT spec: CI-1 equidistribution `#aligned = ∏g per achieved
      -- class`, CI-2 digit-line card = |F_Q|, CI-3 joint independence
      -- `aDim = N·[F_Q:F_p]`, CI-4 `card F_{K+1} = |F_Q|^{∏g}`; assembly:
      -- hclean ⟹ N = ∏g ⟹ card 𝔸 = |F_Q|^{∏g} = card F_{K+1}). Real new
      -- mathematics, not in the corpus at HEAD — the honest sorry (item-18
      -- record in the module docstring).
      intro _
      sorry
  · -- conjunct 3: its hypothesis is refutable outright (ScratchC6 certificate)
    intro hex
    exact absurd hex (C6_conjunct3_hyp_false T b γ)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C6_cardK_bridge
#print axioms LeanUrat.HC1.C6_alphabetCard
