import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.L0_FactB_unique
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.ResVal

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Polynomial LeanUrat.Moves

namespace LeanUrat.Moves

/-! # L5.landTransport (MANIFEST_CORE) — corrected R4 statement (Φ̂ tied to σ)

TRANSPORT determinacy at the STANDARD LIFT `Φ̂`: matching slot residuals (`hslotR`) and
slot weights (`hslotw`) determine `R f`. See `L5_landTransport_R3.lean` for the
machine-checked refutation of the untied R3 statement.

**Proof architecture (sorry-free).** The D.3(d) no-cancellation of the minimal block is
already encoded in the hypothesis `hK1 : K1At σ.w Φhat (σ.w Φhat)` — K1 holds for EVERY
`Φ̂`-development, in particular for every SUB-development `Σ_{j∈T} B_j Φ̂^j` (T a slot subset):
its weight is the ATTAINED slot minimum, so the minimal block keeps weight `m` exactly and
never cancels (Fact B gives nonvanishing). `hRadd` then chains residual additivity across the
minimal block (all partial sums sit at weight `m`), `hRlt` drops the non-minimal rest, and
`R f = Σ_min R(B_j)·R(Φ̂)^j` — a function of the shared slot data only. -/

open Classical in
/-- The minimizing-slot reading of a residual at the standard lift `Φ̂`: `R f = Σ_{minimizing j}
R(B_j)·R(Φ̂)^j`. A function ONLY of the slot data `(R(B_j))_j`, `(w(B_j))_j`, `w Φ̂`, `w f`,
`R Φ̂`, and `M`. (Classical filter over the minimizing set.) -/
noncomputable def readOff {K : Type*} [Field K] (M : ℕ) (rC : ℕ → LaurentPolynomial K)
    (wC : ℕ → ℤ) (kw wg : ℤ) (rΦ : LaurentPolynomial K) : LaurentPolynomial K :=
  ∑ j ∈ (Finset.range M).filter (fun j => rC j ≠ 0 ∧ wC j + (j : ℤ) * kw = wg), rC j * rΦ ^ j

/-- The attained slot-minimum is unique: two attained minima over the SAME slot-weight and
nonzero-slot data agree. -/
private lemma smin_unique {N : ℕ} {sw sw' : ℕ → ℤ} {nz nz' : ℕ → Prop} {m m' : ℤ}
    (h : SlotMinAttained m N sw nz) (h' : SlotMinAttained m' N sw' nz')
    (hsw : ∀ j, sw j = sw' j) (hnz : ∀ j, nz j ↔ nz' j) : m = m' := by
  obtain ⟨hlb, j, hj, hnzj, hm⟩ := h
  obtain ⟨hlb', j', hj', hnzj', hm'⟩ := h'
  have h1 : m' ≤ sw' j := hlb' j hj ((hnz j).1 hnzj)
  have h2 : m ≤ sw j' := hlb j' hj' ((hnz j').2 hnzj')
  have e1 : m = sw' j := by rw [hm, hsw j]
  have e2 : m' = sw j' := by rw [hm', ← hsw j']
  omega

section TransportHelpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/- [SYN2-S1 SWEEP-1, 2026-07-31] The four private Stage-engine micro-copies
(w_one, w_pow, R_one, R_pow) are DELETED — single proof source is the ResVal
Stage-keyed engine (`Moves/ResVal.lean`, statements α-identical); uses re-pointed
to `ResVal.w_one`/`ResVal.w_pow`/`ResVal.R_pow`. -/

open Classical in
/-- A slot subset `T ⊆ range M` of a family of coefficients yields a `Φ̂`-development of its
own partial sum (slots outside `T` zeroed). -/
private lemma subdev (Φhat : Polynomial ℤ_[p]) {C : ℕ → Polynomial ℤ_[p]} {M : ℕ}
    (hdeg : ∀ j, (C j).degree < Φhat.degree) (T : Finset ℕ) (hT : T ⊆ Finset.range M) :
    IsDevelopment Φhat (∑ j ∈ T, C j * Φhat ^ j) (fun j => if j ∈ T then C j else 0) M := by
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · by_cases hjT : j ∈ T
    · simpa [hjT] using hdeg j
    · simp only [hjT, if_false, degree_zero]
      exact lt_of_le_of_lt bot_le (hdeg 0)
  · have hjT : j ∉ T := fun hjT => absurd (Finset.mem_range.mp (hT hjT)) (not_lt.mpr hj)
    simp [hjT]
  · have hcongr : ∀ j ∈ Finset.range M,
        (if j ∈ T then C j else 0) * Φhat ^ j = if j ∈ T then C j * Φhat ^ j else 0 := by
      intro j _
      by_cases hjT : j ∈ T <;> simp [hjT]
    calc ∑ j ∈ T, C j * Φhat ^ j
        = ∑ j ∈ Finset.range M ∩ T, C j * Φhat ^ j := by
          rw [Finset.inter_eq_right.mpr hT]
      _ = ∑ j ∈ Finset.range M, (if j ∈ T then C j * Φhat ^ j else 0) :=
          (Finset.sum_ite_mem _ _ _).symm
      _ = ∑ j ∈ Finset.range M, (if j ∈ T then C j else 0) * Φhat ^ j :=
          (Finset.sum_congr rfl hcongr).symm

/-- **Fact B, applied to a slot subset**: a partial sum over a subset with a genuinely nonzero
slot is nonzero (else the uniqueness of `Φ̂`-developments would force all its slots to vanish). -/
private lemma subdev_ne {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic)
    {C : ℕ → Polynomial ℤ_[p]} {M : ℕ} (hdeg : ∀ j, (C j).degree < Φhat.degree)
    {T : Finset ℕ} (hT : T ⊆ Finset.range M) {a : ℕ} (haT : a ∈ T) (haC : C a ≠ 0) :
    (∑ j ∈ T, C j * Φhat ^ j) ≠ 0 := by
  classical
  intro h0
  have hdevT := subdev Φhat hdeg T hT
  rw [h0] at hdevT
  have hzero : IsDevelopment Φhat (0 : Polynomial ℤ_[p]) (fun _ => 0) 0 := by
    refine ⟨fun j => ?_, fun j _ => rfl, by simp⟩
    simpa using lt_of_le_of_lt bot_le (hdeg 0)
  have hall := L0_FactB_unique Φhat hmon 0 hdevT hzero a
  simp only [haT, if_true] at hall
  exact haC hall

/-- **K1 on a slot subset**: the weight of a nonzero partial sum is an attained slot weight of
one of its own nonzero slots. This is exactly the D.3(d) no-cancellation as `hK1` delivers it. -/
private lemma subdev_weight (σ : Stage p F) {Φhat : Polynomial ℤ_[p]}
    (hK1 : K1At σ.w Φhat (σ.w Φhat)) {C : ℕ → Polynomial ℤ_[p]} {M : ℕ}
    (hdeg : ∀ j, (C j).degree < Φhat.degree) {T : Finset ℕ} (hT : T ⊆ Finset.range M)
    (hne : (∑ j ∈ T, C j * Φhat ^ j) ≠ 0) :
    ∃ j ∈ T, C j ≠ 0 ∧
      σ.w (∑ i ∈ T, C i * Φhat ^ i) = σ.w (C j) + (j : ℤ) * σ.w Φhat := by
  classical
  obtain ⟨-, j, hjM, hjnz, hjeq⟩ := hK1 _ _ M hne (subdev Φhat hdeg T hT)
  by_cases hjT : j ∈ T
  · refine ⟨j, hjT, ?_, ?_⟩
    · simpa [hjT] using hjnz
    · simpa [hjT] using hjeq
  · exact absurd (by simp [hjT]) hjnz

/-- **Residual additivity across an equal-weight block** (the D.3(d) reading): if every slot of
`T` is nonzero with slot weight exactly `m`, then `R(Σ_T B_j Φ̂^j) = Σ_T R(B_j)·R(Φ̂)^j`.
Induction over `T`; every partial sum keeps weight `m` (by `subdev_weight`, i.e. K1 on the
subset) and is nonzero (`subdev_ne`, Fact B), so `hRadd` applies at each step. -/
private lemma block_R (σ : Stage p F) {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic)
    (hK1 : K1At σ.w Φhat (σ.w Φhat)) {C : ℕ → Polynomial ℤ_[p]} {M : ℕ}
    (hdeg : ∀ j, (C j).degree < Φhat.degree) (m : ℤ) :
    ∀ T : Finset ℕ, T.Nonempty → T ⊆ Finset.range M →
      (∀ j ∈ T, C j ≠ 0 ∧ σ.w (C j) + (j : ℤ) * σ.w Φhat = m) →
      σ.R (∑ j ∈ T, C j * Φhat ^ j) = ∑ j ∈ T, σ.R (C j) * σ.R Φhat ^ j := by
  intro T hTne
  induction hTne using Finset.Nonempty.cons_induction with
  | singleton a =>
    intro _ hTS
    rw [Finset.sum_singleton, Finset.sum_singleton,
        σ.hRmul _ _ (hTS a (Finset.mem_singleton_self a)).1 (pow_ne_zero _ hmon.ne_zero),
        ResVal.R_pow σ Φhat hmon.ne_zero a]
  | cons a s ha hs ih =>
    intro hT hTS
    have haS := hTS a (Finset.mem_cons_self a s)
    have hsT : s ⊆ Finset.range M := fun x hx => hT (Finset.mem_cons.2 (Or.inr hx))
    have hsS : ∀ j ∈ s, C j ≠ 0 ∧ σ.w (C j) + (j : ℤ) * σ.w Φhat = m :=
      fun j hj => hTS j (Finset.mem_cons.2 (Or.inr hj))
    obtain ⟨b, hb⟩ := hs
    have hxne : C a * Φhat ^ a ≠ 0 := mul_ne_zero haS.1 (pow_ne_zero _ hmon.ne_zero)
    have hyne : (∑ j ∈ s, C j * Φhat ^ j) ≠ 0 := subdev_ne hmon hdeg hsT hb (hsS b hb).1
    have hwx : σ.w (C a * Φhat ^ a) = m := by
      rw [σ.hwmul _ _ haS.1 (pow_ne_zero _ hmon.ne_zero), ResVal.w_pow σ Φhat hmon.ne_zero a]
      exact haS.2
    have hwy : σ.w (∑ j ∈ s, C j * Φhat ^ j) = m := by
      obtain ⟨j, hjs, hjC, hjeq⟩ := subdev_weight σ hK1 hdeg hsT hyne
      rw [hjeq]
      exact (hsS j hjs).2
    have hconsne : (∑ j ∈ Finset.cons a s ha, C j * Φhat ^ j) ≠ 0 :=
      subdev_ne hmon hdeg hT (Finset.mem_cons_self a s) haS.1
    have hwcons : σ.w (∑ j ∈ Finset.cons a s ha, C j * Φhat ^ j) = m := by
      obtain ⟨j, hjs, hjC, hjeq⟩ := subdev_weight σ hK1 hdeg hT hconsne
      rw [hjeq]
      exact (hTS j hjs).2
    rw [Finset.sum_cons] at hconsne hwcons ⊢
    rw [Finset.sum_cons,
        σ.hRadd _ _ hxne hyne hconsne (hwx.trans hwy.symm) (hwcons.trans hwx.symm),
        ih hsT hsS,
        σ.hRmul _ _ haS.1 (pow_ne_zero _ hmon.ne_zero), ResVal.R_pow σ Φhat hmon.ne_zero a]

open Classical in
/-- **The minimizing-slot reading at the standard lift** (D.3(d)/D.8, formerly the honest gap):
`R g₀ = readOff M (R∘C) (w∘C) (w Φ̂) (w g₀) (R Φ̂)`. Split the development into the minimizing
block and the rest; K1 on subsets (`subdev_weight`) pins the block at weight `w g₀` and the rest
strictly above, `hRlt` drops the rest, `block_R` reads the block termwise. -/
private lemma readAtLift (σ : Stage p F) {Φhat : Polynomial ℤ_[p]} (hmon : Φhat.Monic)
    (hK1 : K1At σ.w Φhat (σ.w Φhat)) (g₀ : Polynomial ℤ_[p]) (hg₀ : g₀ ≠ 0)
    (C : ℕ → Polynomial ℤ_[p]) (M : ℕ) (hdev : IsDevelopment Φhat g₀ C M) :
    σ.R g₀ = readOff M (fun j => σ.R (C j)) (fun j => σ.w (C j)) (σ.w Φhat) (σ.w g₀) (σ.R Φhat) := by
  obtain ⟨hdegC, hCz, hsum⟩ := hdev
  obtain ⟨hlb, j₀, hj₀M, hj₀C, hj₀eq⟩ := hK1 g₀ C M hg₀ ⟨hdegC, hCz, hsum⟩
  have hRC : ∀ j, σ.R (C j) ≠ 0 ↔ C j ≠ 0 := by
    intro j
    constructor
    · intro h hj0
      rw [hj0, σ.hR0] at h
      exact h rfl
    · exact σ.hRne (C j)
  set S : Finset ℕ := (Finset.range M).filter
      (fun j => σ.R (C j) ≠ 0 ∧ σ.w (C j) + (j : ℤ) * σ.w Φhat = σ.w g₀) with hSdef
  set Sc : Finset ℕ := (Finset.range M).filter
      (fun j => ¬ (σ.R (C j) ≠ 0 ∧ σ.w (C j) + (j : ℤ) * σ.w Φhat = σ.w g₀)) with hScdef
  have hSsub : S ⊆ Finset.range M := Finset.filter_subset _ _
  have hScsub : Sc ⊆ Finset.range M := Finset.filter_subset _ _
  have hSmem : ∀ j ∈ S, C j ≠ 0 ∧ σ.w (C j) + (j : ℤ) * σ.w Φhat = σ.w g₀ := by
    intro j hj
    rw [hSdef, Finset.mem_filter] at hj
    exact ⟨(hRC j).1 hj.2.1, hj.2.2⟩
  have hj₀S : j₀ ∈ S := by
    rw [hSdef, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hj₀M, (hRC j₀).2 hj₀C, hj₀eq.symm⟩
  have hsplit : g₀ = (∑ j ∈ S, C j * Φhat ^ j) + ∑ j ∈ Sc, C j * Φhat ^ j := by
    rw [hsum, hSdef, hScdef]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range M) _ _).symm
  have hRmin : σ.R (∑ j ∈ S, C j * Φhat ^ j) = ∑ j ∈ S, σ.R (C j) * σ.R Φhat ^ j :=
    block_R σ hmon hK1 hdegC (σ.w g₀) S ⟨j₀, hj₀S⟩ hSsub hSmem
  have hgoal : σ.R g₀ = ∑ j ∈ S, σ.R (C j) * σ.R Φhat ^ j := by
    by_cases hrest : (∑ j ∈ Sc, C j * Φhat ^ j) = 0
    · rw [hsplit, hrest, add_zero, hRmin]
    · have hfminne : (∑ j ∈ S, C j * Φhat ^ j) ≠ 0 :=
        subdev_ne hmon hdegC hSsub hj₀S (hSmem j₀ hj₀S).1
      have hwmin : σ.w (∑ j ∈ S, C j * Φhat ^ j) = σ.w g₀ := by
        obtain ⟨j, hjS, hjC, hjeq⟩ := subdev_weight σ hK1 hdegC hSsub hfminne
        rw [hjeq]
        exact (hSmem j hjS).2
      have hwrest : σ.w g₀ < σ.w (∑ j ∈ Sc, C j * Φhat ^ j) := by
        obtain ⟨j, hjSc, hjC, hjeq⟩ := subdev_weight σ hK1 hdegC hScsub hrest
        rw [hjeq]
        rw [hScdef, Finset.mem_filter] at hjSc
        have hle : σ.w g₀ ≤ σ.w (C j) + (j : ℤ) * σ.w Φhat :=
          hlb j (Finset.mem_range.mp hjSc.1) hjC
        have hneq : σ.w (C j) + (j : ℤ) * σ.w Φhat ≠ σ.w g₀ :=
          fun he => hjSc.2 ⟨(hRC j).2 hjC, he⟩
        omega
      have hsumne : (∑ j ∈ S, C j * Φhat ^ j) + (∑ j ∈ Sc, C j * Φhat ^ j) ≠ 0 :=
        hsplit ▸ hg₀
      have hwlt : σ.w (∑ j ∈ S, C j * Φhat ^ j) < σ.w (∑ j ∈ Sc, C j * Φhat ^ j) := by
        rw [hwmin]
        exact hwrest
      rw [hsplit, σ.hRlt _ _ hfminne hrest hsumne hwlt, hRmin]
  rw [hgoal, hSdef]
  simp only [readOff]

end TransportHelpers

theorem L5_landTransport {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] (σ : Stage p F) (hcore : StageCore σ) (ψ : Polynomial ↥σ.K) (g : ℕ) (hg : ψ.natDegree = g) (hgpos : 1 ≤ g) (hmon : ψ.Monic) (hψ : Irreducible ψ) (hψz : ψ ≠ Polynomial.X) (Φhat : Polynomial ℤ_[p]) (hlift : IsStandardLift σ ψ g Φhat) (hK1 : K1At σ.w Φhat (σ.w Φhat)) (f f' : Polynomial ℤ_[p]) (hf : f ≠ 0) (hf' : f' ≠ 0) (B B' : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hd : IsDevelopment Φhat f B N) (hd' : IsDevelopment Φhat f' B' N) (hslotR : ∀ j, j < N → σ.R (B j) = σ.R (B' j)) (hslotw : ∀ j, j < N → σ.w (B j) = σ.w (B' j)) : σ.R f = σ.R f' := by
  classical
  have hmonΦ : Φhat.Monic := (L3_liftMonic σ ψ g hgpos Φhat hlift).1
  have hwj : ∀ j, σ.w (B j) = σ.w (B' j) := by
    intro j
    rcases Nat.lt_or_ge j N with h | h
    · exact hslotw j h
    · rw [hd.2.1 j h, hd'.2.1 j h]
  have hRj : ∀ j, σ.R (B j) = σ.R (B' j) := by
    intro j
    rcases Nat.lt_or_ge j N with h | h
    · exact hslotR j h
    · rw [hd.2.1 j h, hd'.2.1 j h]
  have hnz : ∀ j, (B j ≠ 0) ↔ (B' j ≠ 0) := by
    intro j
    constructor
    · intro hb hb'
      exact σ.hRne (B j) hb (by rw [hRj j, hb', σ.hR0])
    · intro hb' hb
      exact σ.hRne (B' j) hb' (by rw [← hRj j, hb, σ.hR0])
  have hsw : ∀ j, σ.w (B j) + (j : ℤ) * σ.w Φhat = σ.w (B' j) + (j : ℤ) * σ.w Φhat := by
    intro j
    rw [hwj j]
  have hwff' : σ.w f = σ.w f' :=
    smin_unique (hK1 f B N hf hd) (hK1 f' B' N hf' hd') hsw hnz
  have hRfun : (fun j => σ.R (B j)) = (fun j => σ.R (B' j)) := funext hRj
  have hwfun : (fun j => σ.w (B j)) = (fun j => σ.w (B' j)) := funext hwj
  rw [readAtLift σ hmonΦ hK1 f hf B N hd,
      readAtLift σ hmonΦ hK1 f' hf' B' N hd',
      hRfun, hwfun, hwff']

end LeanUrat.Moves
