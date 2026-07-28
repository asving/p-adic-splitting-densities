/-
Unit U27.gate_order0_inert  (HC-2 campaign, E/P-phase — blueprint §5 Layer E; runs in the
FIRST E/P block per §7.1: the realF2 lesson)
moves_ref: the root-only n = 2 inert history at p = 2; MovesC `C6.thmC_b`; the
INDEPENDENTLY RECORDED value: realM2's decided count for the inert shape at n = 2 — the
1/4 density anchor of `gate_v2_countingDensity_inert2` (OM/RealInstanceV2Gates). The 1/4
tie is the second equation below (mass · 2² = 2^{2·1}); with the thmC_b instance it forces
totalPins = 2 (recorded as the first equation — the census stop-the-line number).
deps: U31 (the concrete inert history H₀/ν₀, the landing-key witness inside
`sideReads_ν₀`, and the base-stage valuation facts), Defs (D1/D5–D7).
difficulty: medium.
hypothesis_fields: none — THIS UNIT IS AXIOM- AND SEED-HYPOTHESIS-FREE (the seed AND the
jet setup are constructed concretely; that is the point).

RESTATED-AT-COVERAGE-FLOOR (2026-07-28, adjudicated; supersedes the RESTATED-POST-DEFS-
REPAIR sorried form). The pre-restatement unit quantified `∀ N ≥ 1`; that sentence was
MACHINE-REFUTED at N = 2 (`lean/U27_OBSTRUCTION_negation.lean`: `root_height` forces
`line ≥ 1` at both bases, coherence forces `Dwidth = 1`, and `inFreshBand`'s inclusive
upper edge then swallows the level-1 coordinates whenever they exist — `totalPins` is
FORCED to 4 at N = 2, and ≥ 4 at every N ≥ 2, never the recorded 2). The refutation is
the box-size half of the DC-1 lesson (blueprint §2.2): the note's own proviso, quoted at
`ZCSeedLaws.downsets_literal`'s CHART-COVERAGE GUARD, is (ZC-c) "for every
N ≥ 1 + the largest constrained level" = §C C.2's `N(H,Z)` box-size rule — and the
RECORDED gate values (totalPins = 2, the 1/4 tie) are the values AT THE FLOOR BOX
`N₀(H₀,⊤) = 1 + 0 = 1` (every constrained level of the decided order-0 inert stratum is
level 0: the two cluster-zero strips; the pin/mass equations are box-size-dependent, so
the gate pins the floor box exactly). THIS RESTATEMENT: `N := 1`, every other conjunct
byte-identical. The old refutation does not touch the restated form (at N = 1 its own
band count is 2 = the recorded value — no contradiction derives; the constructive proof
below settles it by Lean's consistency).

PROVED (2026-07-28, same round): H₀/keys are U31's concrete history and landing key
`fq = X² + 2X + 4`; the seed is the literal `baseDigit` chart at every frame (Θ = id is
lawful at the root-only history; `downsets_literal`'s guard DERIVES `j < 2 ∧ β ≤ 1` at
positive thresholds, where the law reads "slot divisibility ↔ the level-0 digit
vanishes"); the jet setup is U28's gate pattern ported to p = 2 (state chain
`topLocus → zeroSys`, fresh data = the two level-0 cluster-zero strips, band = the FULL
N = 1 box). Zero sorries, zero axioms beyond Lean core.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U31_gateReadsOf

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace U27

/-! ### §1 — concrete node/history facts (the U31 instance, re-read) -/

private lemma htH0_eq (H : History 2 F4) (x : Coord) : H.htH 0 x = (x.1 : ℚ) := by
  rw [History.htH]
  simp

private lemma strFrame0 : U31.H₀.strFrame 0 = 1 := rfl

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

private lemma htH1_eq (cc : Coord) :
    U31.H₀.htH 1 cc = (cc.1 : ℚ) + ((cc.2 % 2 : ℕ) : ℚ) := by
  rw [History.htH, Finset.sum_range_one]
  congr 1
  rw [show U31.H₀.innerslotH 0 cc.2 = cc.2 % 2 from by
        show (cc.2 % U31.ν₀.childWidth) / U31.ν₀.Dwidth = cc.2 % 2
        rw [show U31.ν₀.childWidth = 2 from rfl, show U31.ν₀.Dwidth = 1 from rfl,
          Nat.div_one],
    show U31.H₀.kappaH 0 = 1 from by
        show ((1 : ℕ) : ℚ) / (((1 : ℕ) : ℚ) * ((U31.H₀.strFrame 0 : ℕ) : ℚ)) = 1
        rw [strFrame0]
        norm_num]
  ring

private lemma floorH1_eq (b : ℕ) (hb : b < 2) :
    U31.H₀.floorH 1 b = ((2 : ℚ) : WithBot ℚ) := by
  rw [History.floorH]
  show (List.map (fun ν => ν.staircase b) (List.take 1 [U31.ν₀])).foldr max ⊥ = _
  rw [show List.take 1 [U31.ν₀] = [U31.ν₀] from rfl, List.map_cons, List.map_nil,
    List.foldr_cons, List.foldr_nil, Node.staircase,
    if_pos (show b < U31.ν₀.μ * U31.ν₀.childWidth from by
      rw [show U31.ν₀.μ * U31.ν₀.childWidth = 2 from rfl]; exact hb),
    show (b / U31.ν₀.childWidth) * U31.ν₀.childWidth = 0 from by
      rw [show U31.ν₀.childWidth = 2 from rfl]; omega]
  rw [max_eq_left bot_le]
  show ((((2 : ℚ) - 1 * ((0 : ℕ) : ℚ)) : ℚ) : WithBot ℚ) = _
  norm_num

/-- The FULL floor box is the fresh band: at N = 1 only level 0 exists, strictly above
the empty floor and (weakly) below both slot valuations 2, 1. -/
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

/-- No floor-box coordinate is a value position (heights are 0; slot valuations are ≥ 1). -/
private lemma not_value (hj : 0 < U31.H₀.nodes.length) (c : Fin (2 * 1)) :
    ¬ IsValueCoord U31.H₀ (boxChart 2 1) 0 (U31.H₀.nodes[0]'hj) c := by
  rintro ⟨-, hht⟩
  rw [htH0_eq, (base_lvl c).1] at hht
  rw [show (U31.H₀.nodes[0]'hj) = U31.ν₀ from rfl, fineSlot_eq, slotVal_eq] at hht
  have h2 : ((boxChart 2 1 c).2 : ℚ) ≤ 1 := by
    exact_mod_cast (by have := (boxChart_lt 2 1 c).2; omega : (boxChart 2 1 c).2 ≤ 1)
  push_cast at hht
  linarith

/-- The (ZC-a) downset check at the post-read state: every floor-box height (0 or 1) is
at most the landed floor 2. -/
private lemma zc_floor (_hj : 0 < U31.H₀.nodes.length) (j : Fin (2 * 1)) :
    ((U31.H₀.htH 1 (boxChart 2 1 j) : ℚ) : WithBot ℚ)
      ≤ U31.H₀.floorH 1 (boxChart 2 1 j).2 := by
  rw [htH1_eq, floorH1_eq _ (boxChart_lt 2 1 j).2, WithBot.coe_le_coe, (base_lvl j).1]
  have h2 : (((boxChart 2 1 j).2 % 2 : ℕ) : ℚ) ≤ 1 := by
    exact_mod_cast (by omega : (boxChart 2 1 j).2 % 2 ≤ 1)
  push_cast
  linarith

/-! ### §2 — the key tower: U31's landing key `fq` at every index -/

/-- The key tower: the recorded landing key `fq = X² + 2X + 4` at every index. -/
noncomputable def keys₀ : ℕ → Polynomial ℤ_[2] := fun _ => U31.fq

private lemma landing_ν₀ : LandingKey U31.ν₀ U31.fq := U31.landingKey_ν₀

lemma keysLawful₀ : KeysLawful U31.H₀ keys₀ := by
  constructor
  · intro i hi
    exact absurd (show i + 1 < 1 from hi) (by omega)
  · intro i hi
    have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
    subst hi0
    exact landing_ν₀

/-! ### §3 — block-locality of `fq` and `baseDigit` at level 0 (the U28 pattern at p = 2) -/

private lemma fq_degree : U31.fq.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree U31.fq_monic.ne_zero, U31.fq_natDegree]
  rfl

/-- BLOCK-LOCALITY OF THE INERT LANDING KEY: `fq ≡ X² (mod 2)`, so any `fq`-development
determines every coefficient of `f` mod 2 from its own block slot alone. -/
private lemma fq_block {f : Polynomial ℤ_[2]} {B : ℕ → Polynomial ℤ_[2]} {Nd : ℕ}
    (hdev : IsDevelopment U31.fq f B Nd) (i : ℕ) :
    (2 : ℤ_[2]) ∣ f.coeff i - (B (i / 2)).coeff (i % 2) := by
  obtain ⟨hdeg, hbeyond, hsum⟩ := hdev
  have hqle : 2 * (i / 2) ≤ i := by omega
  have hgcoeff : (∑ j ∈ Finset.range Nd, B j * Polynomial.X ^ (2 * j)).coeff i
      = (B (i / 2)).coeff (i % 2) := by
    rw [Polynomial.finset_sum_coeff]
    have hterm : ∀ j, (B j * Polynomial.X ^ (2 * j)).coeff i
        = if 2 * j ≤ i then (B j).coeff (i - 2 * j) else 0 := fun j =>
      Polynomial.coeff_mul_X_pow' (B j) (2 * j) i
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    rw [Finset.sum_eq_single (i / 2)]
    · rw [if_pos hqle]
      congr 1
      omega
    · intro j _ hj
      by_cases hin : 2 * j ≤ i
      · rw [if_pos hin]
        have hjle : j ≤ i / 2 :=
          (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hin)
        have hjlt : j < i / 2 := lt_of_le_of_ne hjle hj
        have hstep : 2 * (j + 1) ≤ 2 * (i / 2) := Nat.mul_le_mul_left 2 hjlt
        rw [Nat.mul_succ] at hstep
        refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hdeg j) ?_)
        rw [fq_degree]
        exact_mod_cast (by omega : 2 ≤ i - 2 * j)
      · rw [if_neg hin]
    · intro hni
      rw [Finset.mem_range, not_lt] at hni
      rw [if_pos hqle, hbeyond _ (by omega), Polynomial.coeff_zero]
  have h1 : U31.fq - Polynomial.X ^ 2 ∣
      f - ∑ j ∈ Finset.range Nd, B j * Polynomial.X ^ (2 * j) := by
    rw [hsum, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j _ => ?_
    rw [← mul_sub]
    refine Dvd.dvd.mul_left ?_ (B j)
    rw [show Polynomial.X ^ (2 * j) = (Polynomial.X ^ 2) ^ j by rw [← pow_mul]]
    exact sub_dvd_pow_sub_pow _ _ j
  have h2 : Polynomial.C (2 : ℤ_[2]) ∣ U31.fq - Polynomial.X ^ 2 := by
    refine ⟨Polynomial.X + Polynomial.C 2, ?_⟩
    rw [U31.fq,
      show Polynomial.C (4 : ℤ_[2]) = Polynomial.C (2 : ℤ_[2]) * Polynomial.C (2 : ℤ_[2])
        from by rw [← Polynomial.C_mul]; norm_num]
    ring
  have hcd := (Polynomial.C_dvd_iff_dvd_coeff (2 : ℤ_[2]) (f - ∑ j ∈ Finset.range Nd,
    B j * Polynomial.X ^ (2 * j))).mp (dvd_trans h2 h1) i
  rwa [Polynomial.coeff_sub, hgcoeff] at hcd

/-- `baseDigit` congruence at level 0: the digit only sees the class mod 2. -/
private lemma baseDigit_congr0 {a a' : ℤ_[2]} (h : (2 : ℤ_[2]) ∣ a - a') :
    baseDigit 2 0 a = baseDigit 2 0 a' := by
  have hmap : PadicInt.toZModPow 1 a = PadicInt.toZModPow 1 a' := by
    have hker : a - a' ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := by
      rw [PadicInt.ker_toZModPow]
      refine Ideal.mem_span_singleton.mpr ?_
      rw [show (((2 : ℕ)) : ℤ_[2]) ^ 1 = (2 : ℤ_[2]) by norm_num]
      exact h
    rwa [RingHom.sub_mem_ker_iff] at hker
  rw [baseDigit, baseDigit, hmap]

/-- The level-0 digit vanishes iff the coefficient is even. -/
private lemma baseDigit_zero_iff (a : ℤ_[2]) :
    baseDigit 2 0 a = 0 ↔ (2 : ℤ_[2]) ∣ a := by
  haveI : NeZero ((2 : ℕ) ^ 1) := ⟨by norm_num⟩
  have hbd : baseDigit 2 0 a = (((PadicInt.toZModPow 1 a).val : ℕ) : ZMod 2) := by
    rw [baseDigit]
    norm_num
  have hker : PadicInt.toZModPow (p := 2) 1 a = 0 ↔ (2 : ℤ_[2]) ∣ a := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton,
      show (((2 : ℕ)) : ℤ_[2]) ^ 1 = (2 : ℤ_[2]) by norm_num]
  rw [hbd, ← hker]
  have hvlt : (PadicInt.toZModPow (p := 2) 1 a).val < 2 ^ 1 :=
    ZMod.val_lt (PadicInt.toZModPow 1 a)
  constructor
  · intro h
    have h2 : (2 : ℕ) ∣ (PadicInt.toZModPow (p := 2) 1 a).val :=
      (ZMod.natCast_eq_zero_iff _ 2).mp h
    have hv0 : (PadicInt.toZModPow (p := 2) 1 a).val = 0 := by omega
    exact (ZMod.val_eq_zero _).mp hv0
  · intro h
    rw [h, ZMod.val_zero]
    simp

/-! ### §4 — the concrete presentation spine and the graded seed -/

/-- The concrete presentation spine: the literal frame-0 `baseDigit` chart AT EVERY frame
(lawful at the root-only history with `Θ = id`). -/
noncomputable def presF : ℕ → (Fin (2 * 1) → ZMod 2) → Polynomial ℤ_[2] → Prop :=
  fun _ x f => ∀ j : Fin (2 * 1),
    x j = baseDigit 2 (boxChart 2 1 j).1 (f.coeff (boxChart 2 1 j).2)

/-- The shared block-locality law (consumed verbatim by BOTH the seed and the jet setup):
frame-1 presentations only read the `fq`-development block. -/
private lemma block_law : ∀ i : ℕ, i < U31.H₀.nodes.length →
    ∀ (f f' : Polynomial ℤ_[2]) (x x' : Fin (2 * 1) → ZMod 2),
      presF (i + 1) x f → presF (i + 1) x' f' →
    ∀ (B B' : ℕ → Polynomial ℤ_[2]) (Nd Nd' : ℕ),
      IsDevelopment (keys₀ i) f B Nd → IsDevelopment (keys₀ i) f' B' Nd' →
      ∀ c : Fin (2 * 1),
        B ((boxChart 2 1 c).2 / (keys₀ i).natDegree)
          = B' ((boxChart 2 1 c).2 / (keys₀ i).natDegree) →
        x c = x' c := by
  intro i hi f f' x x' hx hx' B B' Nd Nd' hB hB' c hc
  rw [hx c, hx' c]
  have hdeg : (keys₀ i).natDegree = 2 := U31.fq_natDegree
  rw [hdeg] at hc
  have h1 := fq_block hB (boxChart 2 1 c).2
  have h2 := fq_block hB' (boxChart 2 1 c).2
  rw [(base_lvl c).1]
  refine baseDigit_congr0 ?_
  have h3 := dvd_sub h1 h2
  have h4 : f.coeff (boxChart 2 1 c).2 - (B ((boxChart 2 1 c).2 / 2)).coeff ((boxChart 2 1 c).2 % 2)
      - (f'.coeff (boxChart 2 1 c).2 - (B' ((boxChart 2 1 c).2 / 2)).coeff ((boxChart 2 1 c).2 % 2))
      = f.coeff (boxChart 2 1 c).2 - f'.coeff (boxChart 2 1 c).2
      + ((B' ((boxChart 2 1 c).2 / 2)).coeff ((boxChart 2 1 c).2 % 2)
          - (B ((boxChart 2 1 c).2 / 2)).coeff ((boxChart 2 1 c).2 % 2)) := by ring
  rw [h4, hc, sub_self, add_zero] at h3
  exact h3

/-- Every legal value support at the floor box is EMPTY (no coordinate sits at a slot's
exact valuation: heights are 0, slot valuations are 2 − j ≥ 1 on the window). -/
private lemma valueSupport_empty (i : ℕ) (hi : i < U31.H₀.nodes.length)
    (S : Finset (Fin (2 * 1)))
    (hS : IsValueSupport U31.H₀ (boxChart 2 1) i (U31.H₀.nodes[i]'hi) S) : S = ∅ := by
  have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
  subst hi0
  obtain ⟨jj, hspan, hmem⟩ := hS
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c hc
  obtain ⟨hfs, hht⟩ := (hmem c).mp hc
  rw [htH0_eq, (base_lvl c).1] at hht
  rw [show (U31.H₀.nodes[0]'hi) = U31.ν₀ from rfl] at hfs hht
  rw [fineSlot_eq] at hfs
  rw [slotVal_eq] at hht
  have h2 : (boxChart 2 1 c).2 ≤ 1 := by have := (boxChart_lt 2 1 c).2; omega
  have h3 : (jj : ℚ) = 2 := by push_cast at hht; linarith
  have h4 : jj = 2 := by exact_mod_cast h3
  omega

/-- THE CONCRETE GRADED SEED at the coverage floor — the inhabitation smoke test the
DC-1 Defs repair deferred: `pres` = the literal chart, `Θ = id`, TypObjects trivial on
the (empty) value supports, and the GUARDED `downsets_literal` proved outright (the
guard derives `j < 2 ∧ β ≤ 1` at positive thresholds; the law then reads "slot
divisibility ↔ the level-0 digit vanishes", which is exactly `baseDigit_zero_iff` +
the base-stage normal form). -/
noncomputable def seed : PresentSeed 2 F4 U31.H₀ 2 1 keys₀ where
  pres := presF
  pres_zero := fun x f => Iff.rfl
  pres_total := fun i _ f _ _ =>
    ⟨fun j => baseDigit 2 (boxChart 2 1 j).1 (f.coeff (boxChart 2 1 j).2), fun j => rfl⟩
  Theta := fun _ => id
  Theta_uni := fun _ i => ⟨fun _ => 0, fun x => (add_zero _).symm⟩
  pres_theta := fun i _ x f h => h
  pres_block := block_law
  typObj := fun i hi S hS => by
    have hcard : S.card = 0 := by rw [valueSupport_empty i hi S hS]; rfl
    haveI : Subsingleton (Fin S.card → ZMod 2) := by
      rw [hcard]
      infer_instance
    exact { φ := 0, dep := fun x y _ => rfl, surj := fun y => ⟨0, Subsingleton.elim _ _⟩ }
  zcSeed := by
    constructor
    · -- downsets_literal, guarded (DC-1)
      intro i hi x f B Nd hpres hdev j β hguard
      have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
      subst hi0
      have hdevX : IsDevelopment (Polynomial.X : Polynomial ℤ_[2]) f B Nd := hdev
      have hstr : ((U31.H₀.strFrame 0 : ℕ) : ℚ) = 1 := by rw [strFrame0]; norm_num
      have hfj := U31.dev_coeff hdevX
      have hBj_const : B j = Polynomial.C ((B j).coeff 0) := U31.is_const (hdevX.1 j)
      have hfj0 : B j = 0 → f.coeff j = 0 := by
        intro hB0
        rw [hfj j]
        split_ifs with h
        · rw [hB0, Polynomial.coeff_zero]
        · rfl
      have hne_data : B j ≠ 0 → f.coeff j = (B j).coeff 0 := by
        intro hne
        by_cases h : j < Nd
        · rw [hfj j, if_pos h]
        · exact absurd (hdevX.2.1 j (by omega)) hne
      by_cases hβ : 0 < β
      · -- positive threshold: the guard pins j < 2 and β ≤ 1
        have hj2 : j < 2 := by
          obtain ⟨c, hc⟩ := hguard (0, j)
            (by show U31.ν₀.fineSlot j = j; exact fineSlot_eq j)
            (by rw [htH0_eq]; exact_mod_cast hβ)
          have hlt := (boxChart_lt 2 1 c).2
          rw [hc] at hlt
          exact hlt
        have hβ1 : β ≤ 1 := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨c, hc⟩ := hguard (1, j)
            (by show U31.ν₀.fineSlot j = j; exact fineSlot_eq j)
            (by rw [htH0_eq]; exact_mod_cast hcon)
          have h1 := congrArg Prod.fst hc
          have h2 := (base_lvl c).1
          rw [h2] at h1
          exact absurd h1.symm (by norm_num)
        -- the unique box coordinate at fine slot j
        have hcjlt : 1 - j < 2 * 1 := by omega
        set cj : Fin (2 * 1) := ⟨1 - j, hcjlt⟩ with hcjdef
        have hbase_cj : (boxChart 2 1 cj).2 = j := by
          rw [(base_lvl cj).2]
          show 1 - (1 - j) = j
          omega
        have hRHS : (∀ c : Fin (2 * 1),
            (U31.H₀.nodes[0]'hi).fineSlot (boxChart 2 1 c).2 = j →
              U31.H₀.htH 0 (boxChart 2 1 c) < β → x c = 0) ↔ x cj = 0 := by
          constructor
          · intro h
            refine h cj ?_ ?_
            · show U31.ν₀.fineSlot (boxChart 2 1 cj).2 = j
              rw [fineSlot_eq, hbase_cj]
            · rw [htH0_eq, (base_lvl cj).1]
              exact_mod_cast hβ
          · intro h c hfs hht
            have hbc : (boxChart 2 1 c).2 = j := by
              have h1 : U31.ν₀.fineSlot (boxChart 2 1 c).2 = j := hfs
              rwa [fineSlot_eq] at h1
            have hc_eq : c = cj := by
              have h2 := (base_lvl c).2
              have h3 := c.isLt
              refine Fin.ext ?_
              show (c : ℕ) = 1 - j
              omega
            rwa [hc_eq]
        have hxcj : x cj = baseDigit 2 0 (f.coeff j) := by
          rw [hpres cj, (base_lvl cj).1, hbase_cj]
        have hLHS : (B j = 0 ∨
            β ≤ (((U31.H₀.nodes[0]'hi).σ.w (B j) : ℚ)) / ((U31.H₀.strFrame 0 : ℚ)))
            ↔ (2 : ℤ_[2]) ∣ f.coeff j := by
          constructor
          · rintro (hB0 | hwle)
            · rw [hfj0 hB0]
              exact dvd_zero _
            · by_cases hB0 : B j = 0
              · rw [hfj0 hB0]
                exact dvd_zero _
              · have hbne : (B j).coeff 0 ≠ 0 := fun h0 =>
                  hB0 (by rw [hBj_const, h0, map_zero])
                obtain ⟨mv, u, hNF, hu⟩ := U31.NF_const hbne
                have hNFθ : U31.NF (U31.θ (B j)) mv (Polynomial.C u) := by
                  rw [hBj_const, U31.θ_C]
                  exact hNF
                have hbw : U31.bw (B j) = mv := U31.bw_eq hNFθ
                have hwval : ((U31.H₀.nodes[0]'hi).σ.w (B j)) = U31.bw (B j) := rfl
                rw [hwval, hbw, hstr, div_one] at hwle
                have hmvpos : (0 : ℚ) < ((mv : ℤ) : ℚ) := lt_of_lt_of_le hβ hwle
                have hmv1 : 1 ≤ mv := by
                  have h0 : 0 < mv := by exact_mod_cast hmvpos
                  omega
                have hbu : (B j).coeff 0 = 2 ^ mv * u := by
                  have hcc := congrArg (fun q => Polynomial.coeff q 0) hNF.1
                  simp only [← Polynomial.C_pow, ← Polynomial.C_mul,
                    Polynomial.coeff_C_zero] at hcc
                  exact hcc
                rw [hne_data hB0, hbu]
                exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) u
          · intro hdvd
            by_cases hB0 : B j = 0
            · exact Or.inl hB0
            · right
              have hbne : (B j).coeff 0 ≠ 0 := fun h0 =>
                hB0 (by rw [hBj_const, h0, map_zero])
              obtain ⟨mv, u, hNF, hu⟩ := U31.NF_const hbne
              have hNFθ : U31.NF (U31.θ (B j)) mv (Polynomial.C u) := by
                rw [hBj_const, U31.θ_C]
                exact hNF
              have hbw : U31.bw (B j) = mv := U31.bw_eq hNFθ
              have hbu : (B j).coeff 0 = 2 ^ mv * u := by
                have hcc := congrArg (fun q => Polynomial.coeff q 0) hNF.1
                simp only [← Polynomial.C_pow, ← Polynomial.C_mul,
                  Polynomial.coeff_C_zero] at hcc
                exact hcc
              have hmv1 : 1 ≤ mv := by
                by_contra h0
                push_neg at h0
                have hmv0 : mv = 0 := by omega
                rw [hmv0, pow_zero, one_mul] at hbu
                rw [hne_data hB0, hbu] at hdvd
                exact hu ((U31.ρ_eq_zero_iff u).mpr hdvd)
              have hwval : ((U31.H₀.nodes[0]'hi).σ.w (B j)) = U31.bw (B j) := rfl
              rw [hwval, hbw, hstr, div_one]
              calc β ≤ 1 := hβ1
              _ ≤ ((mv : ℤ) : ℚ) := by exact_mod_cast hmv1
        rw [hLHS, hRHS, hxcj, baseDigit_zero_iff]
      · -- nonpositive threshold: both sides hold outright
        push_neg at hβ
        have hL : B j = 0 ∨
            β ≤ (((U31.H₀.nodes[0]'hi).σ.w (B j) : ℚ)) / ((U31.H₀.strFrame 0 : ℚ)) := by
          by_cases hB0 : B j = 0
          · exact Or.inl hB0
          · right
            have hbne : (B j).coeff 0 ≠ 0 := fun h0 =>
              hB0 (by rw [hBj_const, h0, map_zero])
            have h0le : (0 : ℤ) ≤ U31.bw (Polynomial.C ((B j).coeff 0)) :=
              U31.bw_const_nonneg hbne
            have hwval : ((U31.H₀.nodes[0]'hi).σ.w (B j)) = U31.bw (B j) := rfl
            rw [hwval, hstr, div_one]
            calc β ≤ 0 := hβ
            _ ≤ ((U31.bw (B j) : ℤ) : ℚ) := by
                rw [show U31.bw (B j) = U31.bw (Polynomial.C ((B j).coeff 0)) from by
                  rw [← hBj_const]]
                exact_mod_cast h0le
        have hR : ∀ c : Fin (2 * 1),
            (U31.H₀.nodes[0]'hi).fineSlot (boxChart 2 1 c).2 = j →
              U31.H₀.htH 0 (boxChart 2 1 c) < β → x c = 0 := by
          intro c _ hht
          rw [htH0_eq, (base_lvl c).1] at hht
          exact absurd hht (by push_cast; linarith)
        exact iff_of_true hL hR
    · -- pres_attain: value supports are empty, nothing to attain
      intro i hi S hS x f hpres d
      exact ⟨x, f, hpres, fun c _ => rfl,
        fun c hc => absurd (valueSupport_empty i hi S hS ▸ hc) (Finset.notMem_empty c)⟩
    · -- theta_norm (D5-fence law, 2026-07-28): the gate's Θ is the identity — no
      -- corrections anywhere, the law is definitional.
      intro i hi c hdown x
      rfl
    · -- root_shape (D5-fence law, 2026-07-28): the gate's box carries NO value
      -- coordinate at all (heights 0, slot valuations 2 − j ≥ 1 on the window) — the
      -- `valueSupport_empty` arithmetic, run at a single coordinate.
      intro h0 c hint hvc
      obtain ⟨-, hht⟩ := hvc
      rw [htH0_eq, (base_lvl c).1] at hht
      rw [show (U31.H₀.nodes[0]'h0) = U31.ν₀ from rfl] at hht
      rw [fineSlot_eq, slotVal_eq] at hht
      have h2 : (boxChart 2 1 c).2 ≤ 1 := by have := (boxChart_lt 2 1 c).2; omega
      have h3 : ((boxChart 2 1 c).2 : ℚ) = 2 := by push_cast at hht ⊢; linarith
      have h4 : (boxChart 2 1 c).2 = 2 := by exact_mod_cast h3
      omega

/-! ### §5 — the gate jet setup (U28's p = 3 pattern, ported to p = 2) -/

/-- The literal-zero clause at coordinate `c` (support `{c}`, codim 1, `sat x ↔ x c = 0`). -/
private noncomputable def zeroClause {m : ℕ} (c : Fin m) : LevelClause 2 m where
  support := {c}
  codim := 1
  sat := fun x => x c = 0
  dep := fun x y h => by rw [h c (Finset.mem_singleton_self c)]
  count := by
    have h1 : Nat.card {y : Fin m → ZMod 2 // y c = 0 ∧
        ∀ c' ∉ ({c} : Finset (Fin m)), y c' = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      constructor
      · refine ⟨fun a b => ?_⟩
        refine Subtype.ext (funext fun c' => ?_)
        by_cases hc' : c' = c
        · subst hc'
          rw [a.prop.1, b.prop.1]
        · rw [a.prop.2 c' (by simp [hc']), b.prop.2 c' (by simp [hc'])]
      · exact ⟨⟨fun _ => 0, rfl, fun _ _ => rfl⟩⟩
    rw [h1, Finset.card_singleton]
    norm_num

/-- The all-zeros digit system pinned exactly on `D`. -/
private noncomputable def zeroSys {m : ℕ} (D : Finset (Fin m)) : Locus 2 m where
  pinned := fun c => decide (c ∈ D)
  solve := fun _ _ => 0

private lemma zeroSys_isSolution {m : ℕ} (D : Finset (Fin m)) (x : Fin m → ZMod 2) :
    (zeroSys D).IsSolution x ↔ ∀ c ∈ D, x c = 0 := by
  constructor
  · intro h c hc
    exact h c (by simp [zeroSys, hc])
  · intro h c hc
    have : c ∈ D := by simpa [zeroSys] using hc
    exact h c this

/-- The gate fresh data: one literal-zero clause per coordinate of `D`. -/
private noncomputable def gateFresh (m : ℕ) (D : Finset (Fin m)) : FreshData 2 m :=
  ⟨D.toList.map zeroClause, by
    rw [List.pairwise_map]
    refine (Finset.nodup_toList D).imp ?_
    intro a b hab
    show Disjoint ({a} : Finset (Fin m)) ({b} : Finset (Fin m))
    exact Finset.disjoint_singleton.mpr hab⟩

private noncomputable def gateFreshFn (m : ℕ) (D : Finset (Fin m)) : ℕ → FreshData 2 m :=
  fun i => if i = 0 then gateFresh m D else ⟨[], List.Pairwise.nil⟩

private lemma gateFresh_sat_iff (m : ℕ) (D : Finset (Fin m)) (x : Fin m → ZMod 2) :
    (gateFresh m D).sat x ↔ ∀ c ∈ D, x c = 0 := by
  constructor
  · intro h c hc
    exact h (zeroClause c) (List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hc, rfl⟩)
  · intro h cl hcl
    obtain ⟨c, hcD, rfl⟩ := List.mem_map.mp hcl
    exact h c (Finset.mem_toList.mp hcD)

private lemma mstar_card :
    (gateFresh (2 * 1) (Finset.univ : Finset (Fin (2 * 1)))).mstar
      = (Finset.univ : Finset (Fin (2 * 1))).card := by
  rw [FreshData.mstar]
  have hrep : ((gateFresh (2 * 1) (Finset.univ : Finset (Fin (2 * 1)))).clauses.map
      LevelClause.codim)
      = List.replicate (Finset.univ : Finset (Fin (2 * 1))).toList.length 1 := by
    rw [List.eq_replicate_iff]
    constructor
    · simp [gateFresh]
    · intro b hb
      rw [gateFresh, List.map_map] at hb
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
      rfl
  rw [hrep, List.sum_replicate, smul_eq_mul, mul_one, Finset.length_toList]

/-- THE CONCRETE JET SETUP at the coverage floor: state chain `topLocus → zeroSys univ`,
fresh data = the two level-0 cluster-zero strips (the FULL floor box is the band),
`Θ = id`, keys ≡ `fq`. -/
noncomputable def gateJ : JetSetup U31.H₀ 2 1 (2 * 1) where
  hm := rfl
  hN := le_rfl
  coordOf := boxChart 2 1
  coordOf_sorted := boxChart_sorted 2 1
  coordOf_lt := boxChart_lt 2 1
  coherent := U31.coherent_H₀
  realizable := fun i hi => absurd (show i + 1 < 1 from hi) (by omega)
  root_height := by
    intro hj b hb
    have hb2 : b < 2 := by
      have h1 : b < U31.ν₀.μ * U31.ν₀.childWidth := hb
      rwa [show U31.ν₀.μ * U31.ν₀.childWidth = 2 from rfl] at h1
    show (1 : ℚ) ≤ U31.ν₀.line.at b
    show (1 : ℚ) ≤ (2 : ℚ) - 1 * (b : ℚ)
    have h2 : (b : ℚ) ≤ 1 := by exact_mod_cast (by omega : b ≤ 1)
    linarith
  Sigma := fun k =>
    if k = 0 then topLocus 2 (2 * 1) else zeroSys (Finset.univ : Finset (Fin (2 * 1)))
  init := fun c => rfl
  fresh := gateFreshFn (2 * 1) Finset.univ
  Theta := fun _ => id
  Theta_uni := fun _ i => ⟨fun _ => 0, fun x => (add_zero _).symm⟩
  keys := keys₀
  keys_mid := fun i hi => absurd (show i + 1 < 1 from hi) (by omega)
  landing := by
    intro i hi
    have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
    subst hi0
    exact landing_ν₀
  pres := presF
  pres_zero := fun x f => Iff.rfl
  pres_total := fun i _ f _ _ =>
    ⟨fun j => baseDigit 2 (boxChart 2 1 j).1 (f.coeff (boxChart 2 1 j).2), fun j => rfl⟩
  pres_theta := fun i _ x f h => h
  pres_block := block_law
  stratum := fun i y => (gateFreshFn (2 * 1) Finset.univ i).sat y
  recursion := by
    intro i hi x
    have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
    subst hi0
    show (zeroSys (Finset.univ : Finset (Fin (2 * 1)))).IsSolution x ↔
      (topLocus 2 (2 * 1)).IsSolution x ∧ (gateFresh (2 * 1) Finset.univ).sat x
    rw [zeroSys_isSolution, gateFresh_sat_iff]
    constructor
    · intro h
      exact ⟨fun c hc => by simp [topLocus] at hc, h⟩
    · rintro ⟨-, h⟩
      exact h
  inh_implied := fun i _ y _ => Iff.rfl
  zc := by
    intro i hi
    have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
    subst hi0
    refine ⟨?_, ?_⟩
    · intro j hj
      show (decide (j ∈ (Finset.univ : Finset (Fin (2 * 1)))) = true) ↔ _
      rw [decide_eq_true_eq]
      exact iff_of_true (Finset.mem_univ j) (zc_floor hi j)
    · intro j _ _ f
      rfl
  fresh_band := by
    intro i hi cl hcl c hc
    have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
    subst hi0
    exact band_all hi c
  fresh_cover := by
    intro i hi c hcband
    have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
    subst hi0
    refine ⟨zeroClause c, ?_, Finset.mem_singleton_self c⟩
    show zeroClause c ∈ (gateFreshFn (2 * 1) Finset.univ 0).clauses
    simp only [gateFreshFn, gateFresh]
    exact List.mem_map.mpr ⟨c, Finset.mem_toList.mpr (Finset.mem_univ c), rfl⟩
  fresh_assembled := by
    intro i hi cl hcl
    have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
    subst hi0
    have hcl' : ∃ a ∈ (Finset.univ : Finset (Fin (2 * 1))), zeroClause a = cl := by
      simpa [gateFreshFn, gateFresh] using hcl
    obtain ⟨c₀, -, rfl⟩ := hcl'
    left
    exact ⟨c₀, rfl, rfl, fun x => Iff.rfl, not_value hi c₀⟩
  mstar_eq := by
    intro i hi
    have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
    subst hi0
    have hL : (gateFreshFn (2 * 1) Finset.univ 0).mstar
        = (Finset.univ : Finset (Fin (2 * 1))).card := by
      show (gateFresh (2 * 1) Finset.univ).mstar = _
      exact mstar_card
    have hR : Nat.card {c : Fin (2 * 1) //
        inFreshBand U31.H₀ 2 (boxChart 2 1) 0 (U31.H₀.nodes[0]'hi) c}
        = (Finset.univ : Finset (Fin (2 * 1))).card := by
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (band_all hi)),
        Nat.card_eq_fintype_card, Fintype.card_fin, Finset.card_univ, Fintype.card_fin]
    rw [hL, hR]

/-- The SHZ locus of the gate setup is the all-zero cylinder. -/
private lemma gateJ_SHZ :
    gateJ.SHZ (topLocus 2 (2 * 1))
      = {x : Fin (2 * 1) → ZMod 2 | ∀ c ∈ (Finset.univ : Finset (Fin (2 * 1))), x c = 0} := by
  ext x
  simp only [JetSetup.SHZ, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, hy0, hchain, hsat, -⟩
    intro c hc
    have h1 := hsat 0 (show 0 < U31.H₀.nodes.length from Nat.one_pos)
    rw [show y 0 = x from hy0] at h1
    exact (gateFresh_sat_iff (2 * 1) Finset.univ x).mp h1 c hc
  · intro h
    refine ⟨fun _ => x, rfl, fun i _ => rfl, fun i hi => ?_,
      fun c hc => by simp [topLocus] at hc⟩
    have hi0 : i = 0 := by have h1 : i < 1 := hi; omega
    subst hi0
    exact (gateFresh_sat_iff (2 * 1) Finset.univ x).mpr h

/-- The zero-cylinder count. -/
private lemma card_zero_cylinder (m : ℕ) (D : Finset (Fin m)) :
    Nat.card ↥{x : Fin m → ZMod 2 | ∀ c ∈ D, x c = 0} = 2 ^ (m - D.card) := by
  have e : ↥{x : Fin m → ZMod 2 | ∀ c ∈ D, x c = 0} ≃ ({c : Fin m // c ∉ D} → ZMod 2) :=
  { toFun := fun x c => x.1 c.1
    invFun := fun g => ⟨fun c => if hc : c ∈ D then 0 else g ⟨c, hc⟩, fun c hc => dif_pos hc⟩
    left_inv := fun x => Subtype.ext (funext fun c => by
      show (if hc : c ∈ D then 0 else x.1 c) = x.1 c
      by_cases hc : c ∈ D
      · rw [dif_pos hc, x.2 c hc]
      · rw [dif_neg hc])
    right_inv := fun g => funext fun c => by
      show (if hc : c.1 ∈ D then 0 else g ⟨c.1, hc⟩) = g c
      rw [dif_neg c.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  exact Fintype.card_coe D

end U27

/-- ORDER-0 GATE (inert, p = 2, n = 2), AT THE COVERAGE FLOOR `N := 1`: a concrete
root-only inert history with a CONCRETE seed and a CONCRETE jet setup realizes the
recorded stratum data — `totalPins = 2` and the 1/4 mass tie `mass · 2² = 2^{2·1}`.

THE COVERAGE FLOOR (DC-1 / the (ZC-c) proviso, quoted): the note's "Downsets are
literal" law carries the side condition "**for every N ≥ 1 + the largest constrained
level**" (§C (ZC-c); = §C C.2's `N(H,Z)` box-size rule), implemented in
`ZCSeedLaws.downsets_literal` as the CHART-COVERAGE GUARD. For the order-0 inert F4
history every constrained level of the decided stratum `T(H₀,⊤)` is level 0 (the two
cluster-zero strips), so the floor is `N₀ = 1 + 0 = 1` — and the RECORDED equations
(`totalPins = 2`, the quarter tie) are the floor-box values: they are box-size-dependent
and FALSE at every `N ≥ 2` (`root_height` + the band's inclusive upper edge force
`totalPins ≥ 4` there — machine-refuted for the old `∀ N ≥ 1` form at N = 2 in
`lean/U27_OBSTRUCTION_negation.lean`). Hence the gate is stated AT `N = 1` exactly. -/
theorem gate_order0_inert :
    ∃ (H₀ : History 2 F4) (keys : ℕ → Polynomial ℤ_[2]),
      KeysLawful H₀ keys ∧
      H₀.nodes.length = 1 ∧
      (∀ h0 : 0 < H₀.nodes.length,
        (H₀.nodes[0]'h0).species = ReadSpecies.root ∧
        (H₀.nodes[0]'h0).g = 2 ∧ (H₀.nodes[0]'h0).μ = 1) ∧
      ∃ (S : PresentSeed 2 F4 H₀ 2 1 keys) (J : JetSetup H₀ 2 1 (2 * 1)),
        totalPins J (topLocus 2 (2 * 1)) = 2 ∧
        Nat.card (J.SHZ (topLocus 2 (2 * 1))) * 2 ^ 2 = 2 ^ (2 * 1) := by
  refine ⟨U31.H₀, U27.keys₀, U27.keysLawful₀, rfl, fun h0 => ⟨rfl, rfl, rfl⟩,
    U27.seed, U27.gateJ, ?_, ?_⟩
  · -- totalPins = 2
    rw [totalPins]
    have hnp : (topLocus 2 (2 * 1)).numPinned = 0 := by
      unfold DigitSystem.numPinned
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _
      simp [topLocus]
    rw [hnp, Nat.add_zero]
    show (Finset.range U31.H₀.nodes.length).sum (fun i => (U27.gateJ.fresh i).mstar) = 2
    rw [show U31.H₀.nodes.length = 1 from rfl, Finset.sum_range_one]
    show (U27.gateFresh (2 * 1) Finset.univ).mstar = 2
    rw [U27.mstar_card, Finset.card_univ, Fintype.card_fin]
  · -- the 1/4 mass tie
    rw [U27.gateJ_SHZ, U27.card_zero_cylinder, Finset.card_univ, Fintype.card_fin]
    norm_num

end LeanUrat.MovesJ
