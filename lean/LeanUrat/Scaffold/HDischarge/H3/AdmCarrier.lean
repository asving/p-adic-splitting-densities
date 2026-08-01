/-
HDISCHARGE_H3 §1.4 — unit ADM-U1 (wave 0): the (ADM) per-class carrier layer.
Defs `classCount` / `maxClassWeight` transcribed VERBATIM from the blueprint
(compile-probed there), plus the two non-vacuity lemmas assigned to this unit
by ADM-U2's duties (v1)/(v2): `classFilter_nonempty_of_mem_onLineSlots` and
`d_pos`, and mod-period simp lemmas.  Consumers: ADM-U2
(`admFull_iff_maxClassWeight`), ADM-U3, ADM-U4.

Unit ADM-U3 (wave 1): `classCount_eq_d_of_r_le_one` — (CLASS-d) unconditional
at r ≤ 1 (statement VERBATIM from the blueprint), transcribing O-9 §2's
`j₁ = j₁* + t·e₁` class enumeration; counting kernels reused from
`ValueSide/Census.lean`'s `C2R1Salvage` layer (hence the extra import).
-/
import Mathlib
import LeanUrat.Scaffold.ValueSide.CensusCore
import LeanUrat.Scaffold.ValueSide.Census

/-!
# (ADM) per-class carrier defs [HDISCHARGE_H3 unit ADM-U1]

**PROVENANCE.**

* Blueprint: `lean/blueprints/HDISCHARGE_H3.md` §1.4 (ADM-U1: the two defs
  verbatim; the two non-vacuity lemmas named in ADM-U2's duties (v1)/(v2),
  Codex pass-1 finding 11, landed here so U2's proof consumes them).
* Math source of record: O-9 rev5 §2 (the class ledger; (CLASS-d)) — see
  HDISCHARGE_H3 §1.3.  NOTE (F-ADM-2): (CLASS-d) itself is NOT a carrier
  theorem at r ≥ 2; nothing here claims it.
* Carrier: `LeanUrat.Scaffold.CensusData` (BP_IV §1.2, `CensusCore.lean`).
-/

namespace LeanUrat.Scaffold.HD3

/-- unit ADM-U1 (blueprint-verbatim) — the per-class ledger count: the number
    of φ-monomial slots `j ∈ J` whose weight lies in the residue class
    `c (mod e)` (O-9 §2's `#{𝐣 : wt(𝐣) ≡ c}`; (CLASS-d) asserts this `= d`,
    supplied as a HYPOTHESIS at general order per F-ADM-2). -/
noncomputable def classCount (D : CensusData) (c : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : D.J => D.wt j % D.period = c % D.period)).card

/-- unit ADM-U1 (blueprint-verbatim) — the maximum ledger weight in the
    residue class of `β (mod e)` (O-9 §2's `max{wt(𝐣) : wt(𝐣) ≡ β}`; a
    genuine max whenever the class is nonempty — see
    `classFilter_nonempty_of_mem_onLineSlots`). -/
noncomputable def maxClassWeight (D : CensusData) (β : ℕ) : ℕ :=
  ((Finset.univ.filter
      (fun j : D.J => D.wt j % D.period = β % D.period)) : Finset D.J).sup D.wt

/-- `classCount` depends on `c` only through `c % period`. -/
@[simp] theorem classCount_mod_period (D : CensusData) (c : ℕ) :
    classCount D (c % D.period) = classCount D c := by
  have h : c % D.period % D.period = c % D.period := Nat.mod_mod_of_dvd c dvd_rfl
  simp only [classCount, h]

/-- `maxClassWeight` depends on `β` only through `β % period`. -/
@[simp] theorem maxClassWeight_mod_period (D : CensusData) (β : ℕ) :
    maxClassWeight D (β % D.period) = maxClassWeight D β := by
  have h : β % D.period % D.period = β % D.period := Nat.mod_mod_of_dvd β dvd_rfl
  simp only [maxClassWeight, h]

/-- Any slot in the class of `β` weighs at most `maxClassWeight D β`
    (the `Finset.sup` upper-bound law, packaged for ADM-U2). -/
theorem wt_le_maxClassWeight (D : CensusData) {β : ℕ} {j : D.J}
    (hj : D.wt j % D.period = β % D.period) :
    D.wt j ≤ maxClassWeight D β :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

/-- ADM-U2 non-vacuity duty (v1) — for `β ∈ onLineSlots` the filtered class
    is NONEMPTY: `β = wt 𝐣` for some `𝐣` (the def of `onLineSlots`), and `𝐣`
    lies in its own class.  So `maxClassWeight`'s `Finset.sup` is a genuine
    max, never the empty-sup default `0`. -/
theorem classFilter_nonempty_of_mem_onLineSlots (D : CensusData) {β : ℕ}
    (hβ : β ∈ D.onLineSlots) :
    (Finset.univ.filter
      (fun j : D.J => D.wt j % D.period = β % D.period)).Nonempty := by
  simp only [CensusData.onLineSlots, Finset.mem_image] at hβ
  obtain ⟨j, -, hj⟩ := hβ
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, by rw [hj]⟩⟩

/-- ADM-U2 non-vacuity duty (v2) — `d ≥ 1` is a carrier fact: `d = ∏ f_i`
    with every `f_i ≥ 1` (the `hf` bounds).  Used where (CLASS-d) as a
    hypothesis forces class nonemptiness at arbitrary `c`. -/
theorem d_pos (D : CensusData) : 0 < D.d :=
  Finset.prod_pos fun i _ => D.hf i

/-- unit ADM-U2 (blueprint-verbatim statement) — the deep-stratum reading of
    (ADM)-FULL, with (CLASS-d) as the NAMED hypothesis `hclass` (F-ADM-2: at
    r ≥ 2 (CLASS-d) is NOT a carrier theorem — r = 2 countermodels on file —
    so it enters as a hypothesis, never hypothesis-free).  Route (LED(iii)
    monotonicity, Finset counting): `attainDim β` counts the residue class of
    `β` truncated at `wt ≤ β`; under `hclass` the full class has exactly `d`
    members, so full attainment at `β` ⟺ the truncation is the whole class
    ⟺ every class weight is ≤ β ⟺ `maxClassWeight β ≤ β`.  Non-vacuity
    duties (v1)/(v2) are the ADM-U1 records
    (`classFilter_nonempty_of_mem_onLineSlots`, `d_pos`): on every on-line
    slot the class is nonempty, so the `Finset.sup` in `maxClassWeight` is a
    genuinely attained max; the counting proof below is additionally immune
    to the empty-sup default. -/
theorem admFull_iff_maxClassWeight (D : CensusData)
    (hclass : ∀ c, classCount D c = D.d) :
    ADMFull D ↔ ∀ β ∈ D.onLineSlots, maxClassWeight D β ≤ β := by
  constructor
  · rintro ⟨hfull⟩ β hβ
    -- the truncated class `Gset β` fills the WHOLE class, by cardinality:
    -- both have `d` elements (`hfull` at β, `hclass` at β) and one contains
    -- the other.
    have hsub : D.Gset β ⊆
        Finset.univ.filter (fun j : D.J => D.wt j % D.period = β % D.period) :=
      fun j hj => by
        have hj' := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hj'.1, hj'.2.1⟩
    have hcard : (Finset.univ.filter
        (fun j : D.J => D.wt j % D.period = β % D.period)).card
          ≤ (D.Gset β).card := by
      have h1 := hclass β
      have h2 := hfull β hβ
      simp only [classCount] at h1
      simp only [CensusData.attainDim] at h2
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    unfold maxClassWeight
    refine Finset.sup_le fun j hj => ?_
    have hjG : j ∈ D.Gset β := by rw [heq]; exact hj
    exact (Finset.mem_filter.mp hjG).2.2
  · intro hle
    refine ⟨fun β hβ => ?_⟩
    -- every class member's weight clears β (via `wt_le_maxClassWeight` and
    -- the cleared sup), so the truncation IS the whole class …
    have heq : D.Gset β =
        Finset.univ.filter (fun j : D.J => D.wt j % D.period = β % D.period) := by
      ext j
      simp only [CensusData.Gset, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      exact (wt_le_maxClassWeight D h).trans (hle β hβ)
    -- … whose card is `d` by `hclass`.
    have hc := hclass β
    simp only [classCount] at hc
    simpa [CensusData.attainDim, heq] using hc

/-!
## Unit ADM-U3 — (CLASS-d) unconditional at r ≤ 1

**PROVENANCE.**

* Blueprint: `lean/blueprints/HDISCHARGE_H3.md` §1.4 (ADM-U3; statement
  VERBATIM).  Math source of record: O-9 rev5 §2, the (CLASS-d) r ≤ 1 proof —
  the class enumeration `j₁ = j₁* + t·e₁, 0 ≤ t < f₁`: the mod-e₁ congruence
  pins the stage-1 class digit `j₁*` uniquely (`h₁` a unit mod `e₁` by
  `h_coprime`), the `t`-window contributes `f₁`, and the weight-0 stage-0
  digit contributes `f₀`; per-class total `f₀·f₁ = d`.  At r = 0 the period
  is 1: the single class carries all `f₀ = d` monomials.
* NOTE (F-ADM-2): r ≤ 1 is exactly the UNCONDITIONAL range; at r ≥ 2
  (CLASS-d) is NOT a carrier theorem (compiled countermodels on the probe
  grid — it is (GR-B)-supplied and consumed as ADM-U2's `hclass` hypothesis).
* Non-vacuity (the ADM-U0 record, `CensusCore.lean`): with `triangular`
  dropped, ramified r = 1 data (e₁ > 1) are expressible, so the theorem
  genuinely quantifies over the full coprime (e₁, h₁) range.
* Counting kernels reused from unit C2's salvage layer
  (`C2R1Salvage.card_filter_pi_two` / `weight_mod_iff` /
  `card_filter_prod_fst_eq`, `ValueSide/Census.lean`).
-/

/-- unit ADM-U3 (blueprint-verbatim) — **(CLASS-d) unconditional at r ≤ 1**:
    every weight class mod the period carries exactly `d = ∏ fᵢ` ledger
    slots.  O-9 §2's enumeration: at r = 1 the class of `c` is
    `{(j₀, j₁* + t·e₁) : j₀ < f₀, t < f₁}` with `j₁* = (h₁⁻¹c) mod e₁`. -/
theorem classCount_eq_d_of_r_le_one (D : CensusData) (hr : D.r ≤ 1) (c : ℕ) :
    classCount D c = D.d := by
  obtain ⟨r, e, h, f, he, hf, hcop⟩ := D
  dsimp only at hr
  rcases (show r = 0 ∨ r = 1 by omega) with hr0 | hr1
  · -- r = 0: period 1, a single class carrying all f₀ = d monomials
    subst hr0
    set D0 : CensusData := ⟨0, e, h, f, he, hf, hcop⟩ with hD0
    have hperiod : D0.period = 1 :=
      (Fin.prod_univ_one D0.ledgerE).trans D0.ledgerE_zero
    have htrue : ∀ j : D0.J, D0.wt j % D0.period = c % D0.period := by
      intro j
      rw [hperiod, Nat.mod_one, Nat.mod_one]
    have hcard : Fintype.card D0.J = f 0 := by
      have hJ : Fintype.card D0.J = Fintype.card (Fin 1 × Fin (f 0)) :=
        Fintype.card_congr
          (Equiv.piUnique fun i : Fin 1 => Fin (D0.ledgerE i) × Fin (f i))
      rw [hJ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, one_mul]
    unfold classCount
    rw [Finset.filter_true_of_mem (fun j _ => htrue j), Finset.card_univ,
      hcard]
    exact (Fin.prod_univ_one f).symm
  · -- r = 1: the O-9 §2 enumeration j₁ = j₁* + t·e₁
    subst hr1
    set Dm : CensusData := ⟨1, e, h, f, he, hf, hcop⟩ with hDm
    haveI : NeZero (e 1) := ⟨by have := he 1; omega⟩
    -- the pinned class digit j₁* = (h₁⁻¹·c) mod e₁
    set A : ℕ := (((ZMod.unitOfCoprime (h 1) (hcop 1))⁻¹ : (ZMod (e 1))ˣ)
        * (c : ZMod (e 1)) : ZMod (e 1)).val with hA
    have hAlt : A < e 1 := by
      rw [hA]
      exact ZMod.val_lt _
    -- carrier data at the concrete stages (definitional)
    have hd : Dm.d = f 0 * f 1 := Fin.prod_univ_two f
    have hperiod : Dm.period = e 1 :=
      (Fin.prod_univ_two Dm.ledgerE).trans (one_mul _)
    have hwphi0 : Dm.wphi 0 = 0 := rfl
    have hwphi1 : Dm.wphi 1 = h 1 := by
      have h2 : Dm.wphi 1 = e 1 * 0 + h 1 := rfl
      omega
    have hwt : ∀ j : Dm.J, Dm.wt j = ((j 1).1.1 + e 1 * (j 1).2.1) * h 1 := by
      intro j
      have h2 : Dm.wt j
          = ((j 0).1.1 + Dm.ledgerE 0 * (j 0).2.1) * Dm.wphi 0
            + ((j 1).1.1 + e 1 * (j 1).2.1) * Dm.wphi 1 :=
        Fin.sum_univ_two _
      rw [h2, hwphi0, hwphi1, mul_zero, zero_add]
    -- the class count in stage-1 coordinates
    have hcc : classCount Dm c
        = (Finset.univ.filter (fun j : Dm.J =>
            (((j 1).1.1 + e 1 * (j 1).2.1) * h 1) % e 1 = c % e 1)).card := by
      unfold classCount
      congr 1
      refine Finset.filter_congr ?_
      intro j _
      rw [hwt j, hperiod]
    -- stage 0 rides at weight 0: the factor f₀ (counting kernel, helper 1)
    have hstep : (Finset.univ.filter (fun j : Dm.J =>
          (((j 1).1.1 + e 1 * (j 1).2.1) * h 1) % e 1 = c % e 1)).card
        = Fintype.card (Fin 1 × Fin (f 0))
          * (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
              ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = c % e 1)).card :=
      C2R1Salvage.card_filter_pi_two
        (G := fun i => Fin (Dm.ledgerE i) × Fin (f i))
        (fun y => ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = c % e 1)
    -- the congruence pins the class digit to j₁* = A (helper 4), pinning
    -- costs nothing (helper 2), and the t-window counts f₁ in full
    have hpin : (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
          ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = c % e 1)).card = f 1 := by
      have hQiff : ∀ y : Fin (e 1) × Fin (f 1),
          (((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = c % e 1
            ↔ (y.1 = (⟨A, hAlt⟩ : Fin (e 1)) ∧ True)) := by
        intro y
        constructor
        · intro hcmod
          have h1y : y.1.1 = A := by
            rw [hA]
            exact (C2R1Salvage.weight_mod_iff (hcop 1) c y.1.1 y.2.1
              y.1.2).mp hcmod
          exact ⟨Fin.ext h1y, trivial⟩
        · rintro ⟨hfst, -⟩
          have h1y : y.1.1 = A := by rw [hfst]
          exact (C2R1Salvage.weight_mod_iff (hcop 1) c y.1.1 y.2.1
            y.1.2).mpr (by rw [h1y, hA])
      calc (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
              ((y.1.1 + e 1 * y.2.1) * h 1) % e 1 = c % e 1)).card
          = (Finset.univ.filter (fun y : Fin (e 1) × Fin (f 1) =>
              y.1 = (⟨A, hAlt⟩ : Fin (e 1)) ∧ True)).card :=
            congrArg Finset.card (Finset.filter_congr fun y _ => hQiff y)
        _ = (Finset.univ.filter (fun _ : Fin (f 1) => True)).card :=
            C2R1Salvage.card_filter_prod_fst_eq (⟨A, hAlt⟩ : Fin (e 1))
              (fun _ : Fin (f 1) => True)
        _ = f 1 := by simp
    rw [hcc, hstep, hpin, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, one_mul, hd]

end LeanUrat.Scaffold.HD3
