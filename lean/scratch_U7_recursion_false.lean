/-
U7 ESCALATION REFUTATION (2026-07-28, Fable escalation round).

CLAIM REFUTED: `mkSigma_recursion` (U7_sigmaRec.lean) IS FALSE AS STATED — not merely
unprovable-by-the-blueprint-route. The first prover's stop showed only that the
∃-obligation of `pinTransportSystem_spec` fails for SOME (D, Θ, fd); this file closes the
remaining gap: the failure is REACHABLE FROM A GENUINE `PresentSeed`, so the theorem's
∀-S statement itself is false.

THE COUNTERMODEL: U27's concrete inert gate seed (`U27.seed`, root-only history
`U31.H₀`, n = 2, N = 1, keys = fq) perturbed by the constant unitriangular shift
σ x c = x c + 1 (corr ≡ 1): `badSeed` has pres 0 = the literal baseDigit chart,
pres (i+1) x f := presF (σ x) f, Theta i = σ. Every `PresentSeed` field is discharged
(pres_theta is then definitional; pres_block reduces to U27's via add_right_cancel;
zcSeed laws only see pres 0, unchanged). At read 0 the box is ALL strip coordinates
(U27's band_all/not_value) and `valueSlots = ∅`, so `mkFresh` = two LITERAL-ZERO strip
clauses. Post-DC-2 `IsFreshAttach` then demands, of any D':
  clause (1): D'.IsSolution x ↔ fd.sat (σ x)   (D = topLocus at i = 0)
  clause (2): pinned at the strip coordinate c₀
  clause (3): D'.solve c₀ ≡ 0 (LITERAL zero — untransported)
For x₀ = all-ones: σ x₀ = 0 satisfies fd, so clause (1) forces D'.IsSolution x₀, whose
pinned equation at c₀ forces x₀ c₀ = 0 — but x₀ c₀ = 1. NO D' EXISTS (`no_attach`).
Hence `mkSigma badSeed 1` = the junk default `topLocus`, whose solution set is the FULL
box, while the recursion RHS at x₁ = 0 demands fd.sat (σ 0) = fd.sat(all-ones) = FALSE.
The iff fails at x₁ = 0 (`mkSigma_recursion_FALSE`).

ROOT CAUSE (the exact obstruction, for the designer round): DC-2 transported
`IsFreshAttach`'s solution-set clause through Θ (fd.sat (Θ x)) but left clauses (3)/(4)
as LITERAL-zero solves in the NEW (post-Θ) coordinates. On the solution set, the strip
coordinate solves to x c = −corr_c(x_<c), not 0; nothing in `PresentSeed` (only
`Theta_uni`) forbids corr ≠ 0 on a strip coordinate, and this file exhibits a lawful
seed realizing it. Consistency of the spec needs ONE of:
  (i) clause (3)/(4) transported: D'.solve c g = the unique value making (Θ x)_c = 0,
      i.e. −corr_c (and clause (4) likewise composed with Θ); or
  (ii) a NEW SEED LAW (D5-fence event) that Θ's corrections vanish at fresh strip
      coordinates ON the transported locus — the C.1.5(2) "carries vanish below the
      floor" content, currently nowhere in `PresentSeed`; or
  (iii) re-reading (ZC-a)'s "normalized re-presentation" so that literal-zero solves are
      asserted only where the correction is proved zero (U9c/U10c's consumers re-keyed).
Blueprint statement (the U7 display) is NOT itself refuted — the display is about the
JetSetup.recursion field type; what is refuted is the E-phase D7 spec (post-DC-2
`IsFreshAttach` clauses (1)+(3) jointly) as the carrier of that display.

Machine-checked: `lake env lean` green, zero sorry, zero axioms declared here.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U27_gateInert

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace U7Refute

/-! ### §1 — concrete history facts (copies of U27's private lemmas) -/

private lemma htH0_eq (H : History 2 F4) (x : Coord) : H.htH 0 x = (x.1 : ℚ) := by
  rw [History.htH]
  simp

private lemma fineSlot_eq (b : ℕ) : U31.ν₀.fineSlot b = b := by
  rw [Node.fineSlot, show U31.ν₀.Dwidth = 1 from rfl, Nat.div_one]

private lemma slotVal_eq (j : ℕ) : U31.ν₀.slotVal j = 2 - (j : ℚ) := by
  rw [Node.slotVal, show U31.ν₀.Dwidth = 1 from rfl, Nat.mul_one]
  show (2 : ℚ) - 1 * (j : ℚ) = 2 - (j : ℚ)
  ring

/-- Box arithmetic at the floor box: level `= 0`, base `= 1 − c`. -/
private lemma base_lvl (c : Fin (2 * 1)) :
    (boxChart 2 1 c).1 = 0 ∧ (boxChart 2 1 c).2 = 1 - (c : ℕ) := by
  have h := c.isLt
  show (c : ℕ) / 2 = 0 ∧ 2 - 1 - (c : ℕ) % 2 = 1 - (c : ℕ)
  omega

/-- The FULL floor box is the fresh band at read 0 (U27's `band_all`, copied). -/
private lemma band_all (hj : 0 < U31.H₀.nodes.length) (c : Fin (2 * 1)) :
    inFreshBand U31.H₀ 2 (boxChart 2 1) 0 (U31.H₀.nodes[0]'hj) c := by
  obtain ⟨hℓ, hb⟩ := boxChart_lt 2 1 c
  rw [inFreshBand]
  refine ⟨hb, ?_, ?_⟩
  · show (⊥ : WithBot ℚ) < _
    exact WithBot.bot_lt_coe _
  · rw [htH0_eq]
    show _ ≤ U31.ν₀.slotVal (U31.ν₀.fineSlot (boxChart 2 1 c).2)
    rw [fineSlot_eq, slotVal_eq, (base_lvl c).1]
    have h2 : ((boxChart 2 1 c).2 : ℚ) ≤ 1 := by
      exact_mod_cast (by omega : (boxChart 2 1 c).2 ≤ 1)
    push_cast
    linarith

/-- No floor-box coordinate is a value position (U27's `not_value`, copied). -/
private lemma not_value (hj : 0 < U31.H₀.nodes.length) (c : Fin (2 * 1)) :
    ¬ IsValueCoord U31.H₀ (boxChart 2 1) 0 (U31.H₀.nodes[0]'hj) c := by
  rintro ⟨-, hht⟩
  rw [htH0_eq, (base_lvl c).1] at hht
  rw [show (U31.H₀.nodes[0]'hj) = U31.ν₀ from rfl, fineSlot_eq, slotVal_eq] at hht
  have h2 : ((boxChart 2 1 c).2 : ℚ) ≤ 1 := by
    exact_mod_cast (by have := (boxChart_lt 2 1 c).2; omega : (boxChart 2 1 c).2 ≤ 1)
  push_cast at hht
  linarith

lemma h0len : 0 < U31.H₀.nodes.length := Nat.one_pos

/-! ### §2 — the perturbed seed: the constant unitriangular shift σ -/

/-- The constant shift `σ x c = x c + 1` — unitriangular with correction ≡ 1. -/
def σs : (Fin (2 * 1) → ZMod 2) → (Fin (2 * 1) → ZMod 2) := fun x c => x c + 1

lemma σs_invol (x : Fin (2 * 1) → ZMod 2) : σs (σs x) = x := by
  funext c
  show x c + 1 + 1 = x c
  rw [add_assoc, show (1 + 1 : ZMod 2) = 0 from by decide, add_zero]

/-- The perturbed presentation spine: the literal chart at frame 0; the σ-precomposed
chart at every later frame (so `pres_theta` with `Theta = σ` is definitional). -/
noncomputable def presB : ℕ → (Fin (2 * 1) → ZMod 2) → Polynomial ℤ_[2] → Prop
  | 0 => U27.presF 0
  | (i + 1) => fun x f => U27.presF (i + 1) (σs x) f

/-- THE BAD SEED: U27's concrete inert gate seed with `Theta i = σ` (constant correction
1 at every coordinate — in particular at both strip coordinates of read 0). Every
`PresentSeed` obligation is discharged; `Theta_uni` is the ONLY law `PresentSeed` imposes
on Θ, and it does not see the correction's value. -/
noncomputable def badSeed : PresentSeed 2 F4 U31.H₀ 2 1 U27.keys₀ where
  pres := presB
  pres_zero := fun _ _ => Iff.rfl
  pres_total := by
    intro i _ f _ _
    match i with
    | 0 =>
      exact ⟨fun j => baseDigit 2 (boxChart 2 1 j).1 (f.coeff (boxChart 2 1 j).2),
        fun _ => rfl⟩
    | (k + 1) =>
      refine ⟨σs (fun j => baseDigit 2 (boxChart 2 1 j).1 (f.coeff (boxChart 2 1 j).2)), ?_⟩
      show U27.presF (k + 1)
        (σs (σs (fun j => baseDigit 2 (boxChart 2 1 j).1 (f.coeff (boxChart 2 1 j).2)))) f
      rw [σs_invol]
      exact fun _ => rfl
  Theta := fun _ => σs
  Theta_uni := fun _ i => ⟨fun _ => 1, fun _ => rfl⟩
  pres_theta := by
    intro i hi x f h
    have hlen : U31.H₀.nodes.length = 1 := rfl
    have hi0 : i = 0 := by rw [hlen] at hi; omega
    subst hi0
    exact h
  pres_block := by
    intro i hi f f' x x' hx hx' B B' Nd Nd' hB hB' c hc
    have hlen : U31.H₀.nodes.length = 1 := rfl
    have hi0 : i = 0 := by rw [hlen] at hi; omega
    subst hi0
    have h := U27.seed.pres_block 0 hi f f' (σs x) (σs x') hx hx' B B' Nd Nd' hB hB' c hc
    exact add_right_cancel (h : x c + 1 = x' c + 1)
  typObj := U27.seed.typObj
  zcSeed := by
    constructor
    · intro i hi x f B Nd hpres hdev j β hguard
      have hlen : U31.H₀.nodes.length = 1 := rfl
      have hi0 : i = 0 := by rw [hlen] at hi; omega
      subst hi0
      exact U27.seed.zcSeed.downsets_literal 0 hi x f B Nd hpres hdev j β hguard
    · intro i hi S hS x f hpres d
      have hlen : U31.H₀.nodes.length = 1 := rfl
      have hi0 : i = 0 := by rw [hlen] at hi; omega
      subst hi0
      exact U27.seed.zcSeed.pres_attain 0 hi S hS x f hpres d

/-- Any emitted-value family (irrelevant: read 0 has no value clauses). -/
noncomputable def vOf₀ : VOf 2 (2 * 1) := fun _ _ _ _ => 0

/-! ### §3 — read 0's fresh data: two literal-zero strips, no value clauses -/

def c₀ : Fin (2 * 1) := ⟨0, by omega⟩

lemma c₀_strip : c₀ ∈ stripSet U31.H₀ 2 1 0 (U31.H₀.nodes[0]'h0len) := by
  classical
  unfold stripSet
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, band_all h0len c₀, not_value h0len c₀⟩

lemma valueSlots_empty :
    valueSlots U31.H₀ 2 1 0 (U31.H₀.nodes[0]'h0len) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  unfold valueSlots at hj
  rw [Finset.mem_filter] at hj
  obtain ⟨-, -, ⟨c, hc⟩, -⟩ := hj
  unfold levelSet at hc
  rw [Finset.mem_filter] at hc
  obtain ⟨-, hfs, hht⟩ := hc
  rw [htH0_eq, (base_lvl c).1] at hht
  rw [show (U31.H₀.nodes[0]'h0len) = U31.ν₀ from rfl] at hfs hht
  rw [fineSlot_eq] at hfs
  rw [slotVal_eq] at hht
  have h2 : (boxChart 2 1 c).2 ≤ 1 := by have := (boxChart_lt 2 1 c).2; omega
  have h3 : (j : ℚ) = 2 := by push_cast at hht; linarith
  have h4 : j = 2 := by exact_mod_cast h3
  omega

lemma clauses_eq : (mkFresh U31.H₀ 2 1 badSeed vOf₀ 0 h0len).clauses
    = (stripSet U31.H₀ 2 1 0 (U31.H₀.nodes[0]'h0len)).toList.map
        (fun c => (C1_stripClause (p := 2) c).choose) := by
  show mkFreshClauses U31.H₀ 2 1 badSeed vOf₀ 0 h0len = _
  unfold mkFreshClauses
  have hnil : ((valueSlots U31.H₀ 2 1 0 (U31.H₀.nodes[0]'h0len)).attach.toList) = [] :=
    Finset.toList_eq_nil.mpr (Finset.attach_eq_empty_iff.mpr valueSlots_empty)
  rw [hnil]
  simp

lemma strip_mem : (C1_stripClause (p := 2) c₀).choose
    ∈ (mkFresh U31.H₀ 2 1 badSeed vOf₀ 0 h0len).clauses := by
  rw [clauses_eq]
  exact List.mem_map.mpr ⟨c₀, Finset.mem_toList.mpr c₀_strip, rfl⟩

/-- Read 0's fresh content, solved: `fd.sat y ↔ y ≡ 0 on the strip roster`. -/
lemma fd_sat_iff (y : Fin (2 * 1) → ZMod 2) :
    (mkFresh U31.H₀ 2 1 badSeed vOf₀ 0 h0len).sat y ↔
      ∀ c ∈ stripSet U31.H₀ 2 1 0 (U31.H₀.nodes[0]'h0len), y c = 0 := by
  unfold FreshData.sat
  rw [clauses_eq]
  constructor
  · intro h c hc
    have hm := h _ (List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hc, rfl⟩)
    exact ((C1_stripClause (p := 2) c).choose_spec.2.2 y).mp hm
  · intro h cl hcl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcl
    exact ((C1_stripClause (p := 2) c).choose_spec.2.2 y).mpr (h c (Finset.mem_toList.mp hc))

/-! ### §4 — the spec has NO witness at read 0 (clauses (1)+(2)+(3) jointly inconsistent) -/

/-- Post-DC-2 `IsFreshAttach` is UNSATISFIABLE at the bad seed's read 0: clause (1)
(solution set = `fd.sat ∘ Θ`) forces the all-ones point IN (its σ-image is 0), while
clauses (2)+(3) (literal-zero solve at the pinned strip coordinate) force it OUT. -/
lemma no_attach :
    ¬ ∃ D' : Locus 2 (2 * 1),
        IsFreshAttach (topLocus 2 (2 * 1)) (badSeed.Theta 0)
          (mkFresh U31.H₀ 2 1 badSeed vOf₀ 0 h0len) D' := by
  rintro ⟨D', h1, h2, h3, -⟩
  have hspec := (C1_stripClause (p := 2) c₀).choose_spec
  -- clause (3): the strip coordinate solves to LITERAL zero
  have hsolve : ∀ g, D'.solve c₀ g = 0 :=
    h3 c₀ ⟨_, strip_mem, hspec.1, hspec.2.2⟩
  -- clause (2): the strip coordinate is pinned
  have hpin : D'.pinned c₀ = true :=
    (h2 c₀).mpr (Or.inr ⟨_, strip_mem, by rw [hspec.1]; exact Finset.mem_singleton_self c₀⟩)
  -- the all-ones point: its σ-image is all-zeros, satisfying every strip clause
  have hsat : (mkFresh U31.H₀ 2 1 badSeed vOf₀ 0 h0len).sat
      (badSeed.Theta 0 (fun _ => 1)) := by
    rw [fd_sat_iff]
    intro c _
    show ((1 : ZMod 2) + 1 = 0)
    decide
  have htop : (topLocus 2 (2 * 1)).IsSolution (badSeed.Theta 0 (fun _ => 1)) :=
    fun _ h => Bool.noConfusion h
  -- clause (1) forces the all-ones point to solve D'
  have hsol : D'.IsSolution (fun _ => 1) := (h1 (fun _ => 1)).mpr ⟨htop, hsat⟩
  have hx := hsol c₀ hpin
  rw [hsolve] at hx
  exact absurd (hx : (1 : ZMod 2) = 0) (by decide)

/-- Hence the state chain takes the JUNK branch: `mkSigma badSeed 1` = the full box. -/
lemma sigma1_top :
    mkSigma U31.H₀ 2 1 badSeed vOf₀ (0 + 1) = topLocus 2 (2 * 1) := by
  rw [show mkSigma U31.H₀ 2 1 badSeed vOf₀ (0 + 1)
        = if hi : 0 < U31.H₀.nodes.length then
            pinTransportSystem (mkSigma U31.H₀ 2 1 badSeed vOf₀ 0) (badSeed.Theta 0)
              (mkFresh U31.H₀ 2 1 badSeed vOf₀ 0 hi)
          else mkSigma U31.H₀ 2 1 badSeed vOf₀ 0 from rfl,
    dif_pos h0len,
    show mkSigma U31.H₀ 2 1 badSeed vOf₀ 0 = topLocus 2 (2 * 1) from rfl]
  unfold pinTransportSystem
  rw [dif_neg no_attach]

/-! ### §5 — THE REFUTATION -/

set_option linter.unusedVariables false in
/-- **U7's `mkSigma_recursion` is FALSE AS STATED** (binders verbatim from
`U7_sigmaRec.lean`): at the bad seed, read 0, and the all-zeros point, the LHS is the
junk-branch full box (always solves) while the RHS demands the σ-image (all-ones) to
satisfy the literal-zero strip clause. (`F : Type` — the countermodel's universe;
refuting the universe-0 instance refutes the polymorphic statement a fortiori.) -/
theorem mkSigma_recursion_FALSE :
    ¬ (∀ {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
        (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
        (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
        (i : ℕ) (hi : i < H.nodes.length),
        ∀ x : Fin (n * N) → ZMod p,
          (mkSigma H n N S vOf (i+1)).IsSolution x ↔
            ((mkSigma H n N S vOf i).IsSolution (S.Theta i x) ∧
              mkStratum H n N S vOf i (S.Theta i x))) := by
  intro hall
  have h := hall (p := 2) (F := F4) U31.H₀ 2 1 badSeed vOf₀ 0 h0len (fun _ => 0)
  -- LHS holds: the junk branch is the full box
  have hLHS : (mkSigma U31.H₀ 2 1 badSeed vOf₀ (0 + 1)).IsSolution (fun _ => 0) := by
    rw [sigma1_top]
    exact fun _ hpin => Bool.noConfusion hpin
  obtain ⟨-, hstr⟩ := h.mp hLHS
  -- but the RHS stratum membership fails at the σ-image of 0 (= all-ones)
  have hsat : (mkFresh U31.H₀ 2 1 badSeed vOf₀ 0 h0len).sat
      (badSeed.Theta 0 (fun _ => 0)) := hstr h0len
  have hzero := (fd_sat_iff _).mp hsat c₀ c₀_strip
  exact absurd (hzero : (0 : ZMod 2) + 1 = 0) (by decide)

-- Axiom audit: Lean core only (`propext`, `Classical.choice`, `Quot.sound`).
#print axioms mkSigma_recursion_FALSE

end U7Refute
end LeanUrat.MovesJ
