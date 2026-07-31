/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.CL01b_shallowMove
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.T7_alphabetSpan
import LeanUrat.HC1.ScratchC6

/-!
# HC1.CL01c_shallowTower — Tshallow assembly + the card certificate (BP5 CL-01c)

**Unit CL-01c** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4 CL-01, split
per REVISION 2 finding 11). AS-BUILT (SIDE BRANCH, 2026-07-30): all bodies PROVED,
Lean-core axioms only. The card certificate takes the ≤ 3 route: the level set is the
SINGLE coordinate c0 (κ₀ = 1 kills l and slot 0; the block pin kills the top slot), so
by T7's span identity the alphabet is covered by ONE F_Q-digit line ∪ {0} with
F_Q ⊆ ⊥ ⊆ {0,1}, giving card 𝔸 ≤ 3 < 4 = card F₄ = card K_top — no exact card 𝔸 = 2
needed for the ≠.

**Informal statement.** Assemble ScratchC6's shallow instance
`Tshallow : Tower 2 (GaloisField 2 2)` — K = 1, stg = [TshallowBase, TshallowChild],
the one CL-01b increment — and certify the shallow-height deficiency at
(b, γ) = (0, 0): the level set is nonempty (the single coordinate l = 0, slots ≡ 0)
yet `card 𝔸(0,0) ≠ card F_{K+1}` (𝔸 is one base-digit line over F_Q = F₂:
card ≤ 2 < 4 = card F₄ — ScratchC6 header, MOVES 2160–2165's "STRICTLY SMALLER at
shallow heights").

**Deps.** CL-01a, CL-01b, DefsCar (`levelSet`/`alphabet`), T7_alphabetSpan (the card
toolkit for the ≤ 2 bound). CL-01c is the last of the CL-01 portfolio.

**Proof sketch.** Nonemptiness: exhibit `⟨0, fun _ => if top then 0 else 0, …⟩` — the
coordinate l = 0, slot ≡ 0 (top slot 0 = b); `ht = 0 + 0 = 0`, `blk = 0`. Uniqueness
at (0,0) (not stated, but drives the card bound): κ₀ = h₀/(e₀·STR₀) = 1 and κ₁ =
h′/(e′·STR₁) > 0 force l = 0, slots ≡ 0. Card: by the singleton level set, `alphabet
0 0` is the closure of ONE digit-line image `y ↦ typComposite (single c₀ y)` over
F_Q = F₂ (2 digits), so `card 𝔸 ≤ 2` (additive image of a 2-element digit group;
T7's span toolkit), while `card F_{K+1} = card ↥(⊤ : Subfield F₄) = 4` via
`TshallowChild_pins.1` + `C6_cardK_bridge`-style counting. 2 ≠ 4 closes.

**E-phase resolutions recorded.**
* The blueprint's "card F₄" is rendered as `Nat.card ↥(Tshallow.stg (Fin.last
  Tshallow.K)).K` — the exact right-hand side of the fenced C6 fullness clause, so the
  certificate composes (at CL-02's fence transition ONLY) with the live
  `C6_forces_unconditional_fullness` + `Tshallow_levelSet_nonempty` into the negation
  of pre-repair C6 at `Tshallow`.
* The nonemptiness certificate is split out (`Tshallow_levelSet_nonempty`): the fenced
  C6 carries an `hne` hypothesis, so the composition needs it as a separate piece.

**LANDING GATE (§3.1, BINDING — this is the unit the gate is FOR).** While
`C6_alphabetCard`'s sorry is live, NO negation-shaped compiled artifact lands in the
live tree, and conservatively (escalation E-2) the gate also holds back the
one-composition-away pieces: a PROVED `Tshallow` + `Tshallow_alphabet_deficient`.
THIS COMPILED FILE THEREFORE LIVES ON THE SIDE BRANCH ONLY (the live tree keeps the
sorried skeleton). It does NOT import `C6_alphabetCard` and compiles no negation:
the composition against the live `C6_forces_unconditional_fullness` lands ATOMICALLY
with CL-02's fence transition, retargeted at the frozen `C6_stmt_pre_repair` copy of
the pre-repair statement (the R-7 kernel-freezing pattern). difficulty: hard-fable (portfolio cap shared with
CL-01a/b). PERMITTED OUTCOME: BLOCKED + the exact missing-constructor list (feeds
Q-2: the adjudication may rest on the Lean-core ScratchC6 certificates + the
math-level record if the compiled tower is insanely costly). hyp: none.

**GATE OPENED — LANDED 2026-07-31 (item 18, Asvin sign-off; the CL-02 fence
transition).** This change-set repairs `C6_alphabetCard` (the clean-threshold
hypothesis on conjunct 2 — see that file's execution record), so the pre-repair
sorried universal no longer exists in the live tree; per the gate mechanism this
file lands from the side branch (commit de42a7e) WITH the frozen
`C6_stmt_pre_repair` copy and the compiled negation
(`C6_pre_repair_refuted_at_Tshallow`, `C6_pre_repair_theorem_refuted`) appended
at the end — atomically in the same commit. M1 no-coexistence: satisfied (the
negation targets ONLY the frozen copy).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- **The shallow tower** (CL-01c assembly): one base read + one g = 2 increment.
The `base` and `move` fields are the unit's remaining construction slots
(`TshallowBase_isBase` and `TshallowMove` respectively); `K`, `stg`, `hcharF` are
fixed here so the projection pins below are definitional. -/
noncomputable def Tshallow : Tower 2 (GaloisField 2 2) where
  K := 1
  stg := ![TshallowBase, TshallowChild]
  base := TshallowBase_isBase
  move := fun k =>
    match k with
    | ⟨0, _⟩ => TshallowMove
    | ⟨n + 1, h⟩ => absurd h (by omega)
  hcharF := inferInstance

/-- Tshallow has exactly one move. -/
theorem Tshallow_K : Tshallow.K = 1 := rfl

/-- Stage 0 of Tshallow is CL-01a's base stage. -/
theorem Tshallow_stg_zero : Tshallow.stg 0 = TshallowBase := rfl

/-- The top stage of Tshallow is CL-01b's child stage. -/
theorem Tshallow_stg_last : Tshallow.stg (Fin.last Tshallow.K) = TshallowChild := rfl

/-! ### Counting toolkit: the two-element subfield {0, 1} and card F₄ = 4 -/

private lemma two_eq_zero' : (1 : GaloisField 2 2) + 1 = 0 := by
  have h : ((2 : ℕ) : GaloisField 2 2) = 0 := CharP.cast_eq_zero _ 2
  rw [Nat.cast_ofNat] at h
  linear_combination h

/-- The prime subfield {0, 1} of F₄, as an explicit subfield (char 2 closes it under
all operations); it receives ⊥ via `bot_le`, giving the ≤ 2 bound on F_Q. -/
private def S01 : Subfield (GaloisField 2 2) where
  carrier := {0, 1}
  zero_mem' := Or.inl rfl
  one_mem' := Or.inr rfl
  add_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (add_zero 0)
    · exact Or.inr (zero_add 1)
    · exact Or.inr (add_zero 1)
    · exact Or.inl two_eq_zero'
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (mul_zero 0)
    · exact Or.inl (zero_mul 1)
    · exact Or.inl (mul_zero 1)
    · exact Or.inr (mul_one 1)
  neg_mem' := by
    rintro x (rfl | rfl)
    · exact Or.inl neg_zero
    · exact Or.inr (show (-1 : GaloisField 2 2) = 1 by linear_combination -two_eq_zero')
  inv_mem' := by
    rintro x (rfl | rfl)
    · exact Or.inl inv_zero
    · exact Or.inr inv_one

private lemma F4card : Nat.card (GaloisField 2 2) = 4 := by
  have h := GaloisField.card 2 2 (by norm_num)
  rw [h]; norm_num

/-! ### The unique shallow coordinate (l = 0, slots ≡ 0) and the height computation -/

/-- Coordinate extensionality (the T7 `levelSet_finite'` destructuring, as a lemma). -/
private lemma coord_ext {c c' : Tshallow.Coord} (hl : c.l = c'.l)
    (hs : c.slot = c'.slot) : c = c' := by
  obtain ⟨l₁, s₁, h₁⟩ := c
  obtain ⟨l₂, s₂, h₂⟩ := c'
  dsimp only at hl hs
  subst hl; subst hs
  rfl

/-- The single shallow coordinate: p-adic level 0, all slots 0. -/
private def c0 : Tshallow.Coord where
  l := 0
  slot := fun _ => 0
  slot_lt := by
    intro r
    obtain ⟨rv, hrv⟩ := r
    have h1 : rv < 1 := by
      have hK : Tshallow.K = 1 := rfl
      rw [← hK]; exact hrv
    have h2 : rv = 0 := by omega
    subst h2
    show 0 < TshallowChild.Φ.natDegree / TshallowBase.Φ.natDegree
    rw [TshallowChild_pins.2.2, TshallowBase_pins.1, Polynomial.natDegree_X]
    norm_num

private lemma hc0_mem : c0 ∈ Tshallow.levelSet 0 0 := by
  constructor
  · rfl
  · show ((0 : ℕ) : ℚ) + ∑ r, ((0 : ℕ) : ℚ) * Tshallow.kappa r = 0
    simp

/-- κ₀ = h₀/(e₀·STR₀) = 1/(1·1) = 1 (the pins + STR₀ = 1). -/
private lemma kappa0 : Tshallow.kappa 0 = 1 := by
  show (TshallowBase.h : ℚ) / ((TshallowBase.e : ℚ) * ((Tshallow.str 0 : ℕ) : ℚ)) = 1
  have hstr : Tshallow.str 0 = 1 := rfl
  rw [TshallowBase_pins.2.2.1, TshallowBase_pins.2.1, hstr]
  norm_num

/-- STR₁ = STR₀·e₀ = 1 (the exclusive stretch at the top read). -/
private lemma str1 : Tshallow.str 1 = 1 := by
  have h : Tshallow.str 1
      = Tshallow.strAux 0 * (if h : 0 < Tshallow.K + 1 then (Tshallow.stg ⟨0, h⟩).e else 1) :=
    rfl
  rw [h, dif_pos (Nat.succ_pos _)]
  show 1 * TshallowBase.e = 1
  rw [one_mul, TshallowBase_pins.2.1]

/-- κ₁ = h′/(e′·STR₁) = h′ (e′ = 1, STR₁ = 1). -/
private lemma kappa1 : Tshallow.kappa 1 = (TshallowChild.h : ℚ) := by
  show (TshallowChild.h : ℚ) / ((TshallowChild.e : ℚ) * ((Tshallow.str 1 : ℕ) : ℚ)) =
    (TshallowChild.h : ℚ)
  rw [TshallowChild_pins.2.1, str1]
  norm_num

/-- **Uniqueness at (0,0)**: κ₀ = 1 > 0 and the block pin force l = 0, slots ≡ 0 —
the level set is the single coordinate `c0` (ScratchC6's math-level analysis,
compiled). -/
private lemma levelSet_eq_c0 (c : Tshallow.Coord) (hc : c ∈ Tshallow.levelSet 0 0) :
    c = c0 := by
  obtain ⟨hblk, hht⟩ := hc
  have hs1 : c.slot 1 = 0 := hblk
  have h0 : (c.l : ℚ) + ∑ r, (c.slot r : ℚ) * Tshallow.kappa r = 0 := hht
  have hsum : ∑ r, (c.slot r : ℚ) * Tshallow.kappa r
      = (c.slot 0 : ℚ) * Tshallow.kappa 0 + (c.slot 1 : ℚ) * Tshallow.kappa 1 :=
    Fin.sum_univ_two _
  rw [hsum, kappa0, kappa1, hs1] at h0
  have hq : (c.l : ℚ) + (c.slot 0 : ℚ) = 0 := by push_cast at h0; linarith
  have hnat : c.l + c.slot 0 = 0 := by exact_mod_cast hq
  have hl : c.l = 0 := by omega
  have hs0 : c.slot 0 = 0 := by omega
  refine coord_ext hl ?_
  funext r
  match r with
  | ⟨0, _⟩ => exact hs0
  | ⟨1, _⟩ => exact hs1
  | ⟨n + 2, h⟩ =>
    exact absurd h (by have hK : Tshallow.K = 1 := rfl; omega)

/-- CL-01c certificate 1: the shallow level set at (b, γ) = (0, 0) is NONEMPTY (the
coordinate l = 0, slots ≡ 0) — the `hne` piece of the eventual composition against
the fenced C6. -/
theorem Tshallow_levelSet_nonempty : (Tshallow.levelSet 0 0).Nonempty :=
  ⟨c0, hc0_mem⟩

/-- The one base-digit line of the shallow alphabet: `y ↦ typComposite(single c0 y)`
over F_Q = F₂. -/
private noncomputable def digLine (y : ↥(Tshallow.stg 0).FQ) : Tshallow.grQ 0 :=
  Tshallow.typComposite 0 0 (Pi.single (⟨c0, hc0_mem⟩ : ↥(Tshallow.levelSet 0 0)) y)

/-- CL-01c certificate 2 (THE card certificate): at the shallow height the alphabet is
strictly deficient — `card 𝔸(0,0) ≠ card F_{K+1}` (2-element digit line vs the
4-element top residue field). Together with `Tshallow_levelSet_nonempty` and the live
`C6_forces_unconditional_fullness`, this refutes pre-repair `C6_alphabetCard` at
`Tshallow` — that composition is GATE-HELD (see the module docstring) and is NOT
compiled by this unit. -/
theorem Tshallow_alphabet_deficient :
    Nat.card ↥(Tshallow.alphabet 0 0)
      ≠ Nat.card ↥(Tshallow.stg (Fin.last Tshallow.K)).K := by
  classical
  obtain ⟨hset, -, -⟩ := T7_alphabetSpan Tshallow 0 0
  haveI hss : Subsingleton ↥(Tshallow.levelSet 0 0) :=
    ⟨fun a b => Subtype.ext ((levelSet_eq_c0 a.1 a.2).trans (levelSet_eq_c0 b.1 b.2).symm)⟩
  -- Step 1: the alphabet is covered by the single digit line (plus 0)
  have hcover : (Tshallow.alphabet 0 0 : Set (Tshallow.grQ 0))
      ⊆ Set.range digLine ∪ {0} := by
    intro x hx
    rw [hset] at hx
    obtain ⟨s, dig, rfl⟩ := hx
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
    · rw [Finset.sum_empty]; exact Or.inr rfl
    · left
      have hs : s = {(⟨c0, hc0_mem⟩ : ↥(Tshallow.levelSet 0 0))} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨?_, fun b _ => Subsingleton.elim b _⟩
        rwa [Subsingleton.elim (⟨c0, hc0_mem⟩ : ↥(Tshallow.levelSet 0 0)) a]
      rw [hs, Finset.sum_singleton]
      exact ⟨dig _, rfl⟩
  -- Step 2: the digit line's domain F_Q ⊆ K = ⊥ ⊆ {0, 1} has ≤ 2 elements
  have hFQ2 : Nat.card ↥(Tshallow.stg 0).FQ ≤ 2 := by
    have hsub : ((Tshallow.stg 0).FQ : Set (GaloisField 2 2))
        ⊆ ({0, 1} : Set (GaloisField 2 2)) := by
      intro x hx
      have hx1 : x ∈ TshallowBase.K := TshallowBase.hFQ_le hx
      rw [TshallowBase_pins.2.2.2] at hx1
      exact (bot_le : (⊥ : Subfield (GaloisField 2 2)) ≤ S01) hx1
    calc Nat.card ↥(Tshallow.stg 0).FQ
        = ((Tshallow.stg 0).FQ : Set (GaloisField 2 2)).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ ({0, 1} : Set (GaloisField 2 2)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_pair zero_ne_one).le
  -- Step 3: card 𝔸 ≤ 3 < 4 = card F₄ = card K_top
  have hle : Nat.card ↥(Tshallow.alphabet 0 0) ≤ 3 := by
    have e1 : Nat.card ↥(Tshallow.alphabet 0 0)
        = (Tshallow.alphabet 0 0 : Set (Tshallow.grQ 0)).ncard :=
      Nat.card_coe_set_eq _
    have e2 : (Tshallow.alphabet 0 0 : Set (Tshallow.grQ 0)).ncard
        ≤ (Set.range digLine ∪ {0} : Set (Tshallow.grQ 0)).ncard :=
      Set.ncard_le_ncard hcover ((Set.finite_range digLine).union (Set.finite_singleton 0))
    have e3 : (Set.range digLine ∪ {0} : Set (Tshallow.grQ 0)).ncard
        ≤ (Set.range digLine).ncard + 1 := by
      rw [Set.union_singleton]
      exact Set.ncard_insert_le _ _
    have e4 : (Set.range digLine).ncard ≤ Nat.card ↥(Tshallow.stg 0).FQ := by
      rw [← Set.ncard_univ, ← Set.image_univ]
      exact Set.ncard_image_le Set.finite_univ
    omega
  have hRHS : Nat.card ↥(Tshallow.stg (Fin.last Tshallow.K)).K = 4 := by
    have hK : (Tshallow.stg (Fin.last Tshallow.K)).K = (⊤ : Subfield (GaloisField 2 2)) :=
      TshallowChild_pins.1
    rw [hK, Nat.card_congr (Equiv.subtypeUnivEquiv fun x => Subfield.mem_top x),
      F4card]
  omega

/-! ## The fence transition (item 18, 2026-07-31): frozen pre-repair copy + the
compiled negation

Per the BP5 §3.1 LANDING GATE, the pieces below land ATOMICALLY with the
`C6_alphabetCard` statement repair (the clean-threshold hypothesis on conjunct 2)
in the same change-set: the sorried pre-repair universal no longer exists in the
live tree, so the M1 no-coexistence rule is satisfied. The negation targets the
FROZEN copy `C6_stmt_pre_repair` (R-7 kernel-freezing pattern), never the
repaired live statement. -/

/-- **The frozen pre-repair C6 conclusion** (VERBATIM pre-repair statement text of
`C6_alphabetCard` at (T, b, γ), frozen 2026-07-31 at the item-18 fence transition):
conjunct 2's iff carries NO clean-threshold hypothesis — the form refuted below. -/
def C6_stmt_pre_repair {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) : Prop :=
  Nat.card ↥(T.alphabet b γ) = p ^ T.aDim b γ ∧
  (Nat.card ↥(T.alphabet b γ) = Nat.card ↥(T.stg (Fin.last T.K)).K ↔
    ∀ c : ↥(T.levelSet b γ), ∃ y : ↥(T.stg 0).FQ,
      T.typComposite b γ (Pi.single c y) ≠ 0) ∧
  ((∃ c : ↥(T.levelSet b γ), ∀ y : ↥(T.stg 0).FQ,
      T.typComposite b γ (Pi.single c y) = 0) →
    T.aDim b γ < Nat.log p (Nat.card ↥(T.stg (Fin.last T.K)).K))

/-- **THE COMPILED COUNTERMODEL** (CL-01 deliverable, landed at the fence
transition): the pre-repair C6 conclusion is FALSE at `Tshallow`, (b, γ) = (0, 0)
— it forces unconditional fullness (`C6_forces_unconditional_fullness`, the
ScratchC6 certificate), refuted by the card certificate
`Tshallow_alphabet_deficient` (card 𝔸 ≤ 3 < 4 = card F₄). -/
theorem C6_pre_repair_refuted_at_Tshallow : ¬ C6_stmt_pre_repair Tshallow 0 0 :=
  fun h => Tshallow_alphabet_deficient (C6_forces_unconditional_fullness Tshallow 0 0 h)

/-- The ∀-form refutation at the gate ambient: no theorem can prove the pre-repair
C6 conclusion on every nonempty level set — the level set at (0,0) is nonempty
(`Tshallow_levelSet_nonempty`) and the conclusion fails there. -/
theorem C6_pre_repair_theorem_refuted :
    ¬ ∀ (T : Tower 2 (GaloisField 2 2)) (b : ℕ) (γ : ℚ),
        (T.levelSet b γ).Nonempty → C6_stmt_pre_repair T b γ :=
  fun h => C6_pre_repair_refuted_at_Tshallow (h Tshallow 0 0 Tshallow_levelSet_nonempty)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.Tshallow_levelSet_nonempty
#print axioms LeanUrat.HC1.Tshallow_alphabet_deficient
#print axioms LeanUrat.HC1.C6_pre_repair_refuted_at_Tshallow
#print axioms LeanUrat.HC1.C6_pre_repair_theorem_refuted
