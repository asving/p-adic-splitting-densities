/-
HDISCHARGE_H3 §1.4 — unit ADM-U4 (wave 1): compiled countermodel + control
gates for (ADM)-FULL.  Three legs per the blueprint row (K6/K7/K7⁺):

* K7 leg     — `k7_not_admFull : ¬ ADMFull k7Datum` (the O-9 pass-3
  countermodel type T2) — THE unit gate ("compiled ¬ADMFull").
* K7⁺ leg    — `k7Pos_admFull : ADMFull k7PosDatum` (the d ≥ 2 positive
  control, carrier-transcribed; see the k7PosDatum docstring).
* K6 leg     — ADJUDICATED AT LANDING (full record on `k6Datum`): the
  blueprint's prose form `¬ ADMFull k6Datum` is REFUTED at the carrier's
  C0d slot reading (`k6_admFull` below is the compiled counter-proof);
  the operative K6 gate per the Census.lean ADM-U0 satisfiability record
  is `k6_attainDim_one : k6Datum.attainDim 1 = 0` at `period = 3` (the
  padding-clause LIVEness witness).  No statement was weakened: the prose
  leg is not landed as a `sorry`, it is landed as its machine adjudication.
-/
import Mathlib
import LeanUrat.Scaffold.ValueSide.Census
import LeanUrat.Scaffold.HDischarge.H3.AdmCarrier

/-!
# (ADM)-FULL machine gates [HDISCHARGE_H3 unit ADM-U4]

**PROVENANCE.**

* Blueprint: `lean/blueprints/HDISCHARGE_H3.md` §1.4 (ADM-U4) and §1.1–1.3
  (the K6/K7 countermodel data; findings F-ADM-1/F-ADM-2).
* Math source of record: O-9 rev5 §§1–2 (warning display 1 = K6; the pass-3
  countermodel type T2 = K7) and the falsifier script
  `verification/openmath/o9_rev4_fulladm_check.py` (CH1–CH5).
* Carrier: `LeanUrat.Scaffold.CensusData` at the post-ADM-U0 head
  (`triangular` DROPPED — the K6/K7⁺ shapes are expressible at all only
  since that repair; see the `CensusData` docstring repair record).
* Deps consumed: ADM-U1 (`HD3.classCount`/`HD3.maxClassWeight` — the
  deep-stratum display rows below) · unit C3 (the `Decidable (ADMFull D)`
  instance, `ValueSide/Census.lean` — the `by decide` cross-check rows).
* Proof style: explicit `Finset`/slot computations for the gate mechanisms
  (C4c/C5CtorGate precedent), `decide` only at literal-value leaves
  (`d`/`period`/`Fintype.card`/`attainDim` at fixed β) and as independent
  one-line cross-checks through the C3 instance.
-/

namespace LeanUrat.Scaffold.HD3

/-! ## Shared slot helpers -/

/-- The all-zero φ-monomial index of any census datum (every digit 0). -/
def j0 (D : CensusData) : D.J := fun i => (⟨0, D.ledgerE_pos i⟩, ⟨0, D.hf i⟩)

/-- The all-zero index has slot weight 0 (every digit contributes 0). -/
theorem wt_j0 (D : CensusData) : D.wt (j0 D) = 0 := by
  unfold CensusData.wt
  exact Finset.sum_eq_zero fun i _ => by simp [j0]

/-- The base slot β = 0 is on-line at EVERY census datum (witness `j0`) —
    the non-vacuity anchor for all three gates below. -/
theorem zero_mem_onLineSlots (D : CensusData) : 0 ∈ D.onLineSlots :=
  Finset.mem_image.mpr ⟨j0 D, Finset.mem_univ _, wt_j0 D⟩

/-! ## K7 — the (ADM)-FULL countermodel gate (the unit's charge)

O-9 pass-3 countermodel type T2 (r = 1, f₀ = 1, e₁ = 1, f₁ = 2, h₁ = 2):
m = d = 2, ledger period e = 1, ledger weights {0, 2} (w(φ₁) = e₁V₁ + h₁ = 2).
The base on-line slot β = 0 is value-attained but only PARTIALLY:
attainDim 0 = 1 < 2 = d — rev 3's VALUE (ADM) admits the datum, rev 4's
FULL (ADM) refuses it (the (q+1)/q census overcount mechanism, CH2). -/

/-- The K7 countermodel datum (O-9 pass-3 type T2): r = 1, e ≡ 1, h ≡ 2,
    f = (1, 2).  Stage-0 h₀ = 2 is lattice-inert (wphi 0 = 0); the ledger
    data is exactly O-9's (e₁, h₁, f₀, f₁) = (1, 2, 1, 2), d = 2. -/
def k7Datum : CensusData where
  r := 1
  e := fun _ => 1
  h := fun _ => 2
  f := fun i => if i.1 = 0 then 1 else 2
  he := fun _ => le_refl 1
  hf := fun i => by split <;> omega
  h_coprime := fun _ => Nat.coprime_one_right 2

/-- The weight-2 K7 slot: stage-1 t-digit 1 (the φ₁ monomial). -/
def k7j1 : k7Datum.J :=
  Fin.cases (motive := fun i => Fin (k7Datum.ledgerE i) × Fin (k7Datum.f i))
    ((0, 0) : Fin 1 × Fin 1) (fun _ => ((0 : Fin 1), (1 : Fin 2)))

theorem k7_wt_j1 : k7Datum.wt k7j1 = 2 := by decide

/-- **THE ADM-U4 GATE (K7 leg): compiled ¬ADMFull.**  Mechanism on display:
    if every on-line slot were FULLY attained then at β = 0 the graded piece
    `Gset 0` would have card d = 2 = |J|, forcing `Gset 0 = univ` — but the
    φ₁ slot `k7j1` has weight 2 > 0, so it cannot lie in `Gset 0`. -/
theorem k7_not_admFull : ¬ ADMFull k7Datum := by
  intro h
  have hfull := h.full_attained 0 (zero_mem_onLineSlots _)
  unfold CensusData.attainDim at hfull
  rw [show k7Datum.d = 2 by decide] at hfull
  have huniv : k7Datum.Gset 0 = Finset.univ :=
    Finset.eq_univ_of_card _
      (by rw [hfull, show Fintype.card k7Datum.J = 2 by decide])
  have hmem : k7j1 ∈ k7Datum.Gset 0 := huniv ▸ Finset.mem_univ _
  have hle : k7Datum.wt k7j1 ≤ 0 := by
    simpa [CensusData.Gset] using (Finset.mem_filter.mp hmem).2.2
  rw [k7_wt_j1] at hle
  omega

/-- Cross-check through the C3 `Decidable (ADMFull D)` instance. -/
example : ¬ ADMFull k7Datum := by decide

/-- K7 partial-slot profile: the base slot is value-attained (dim 1 ≥ 1)
    but not FULL (dim 1 < d = 2) — the exact CH1 dichotomy row. -/
example : k7Datum.attainDim 0 = 1 ∧ k7Datum.d = 2 := by decide

/-- ADM-U1 tie (the deep-stratum reading of HDISCHARGE_H3 §1.1): K7
    violates "every on-line β ≥ max class weight" at β = 0 — the single
    class (period 1) has max ledger weight 2 > 0.  (CLASS-d) itself HOLDS
    at K7 (r = 1; classCount = 2 = d), so the failure is genuinely the
    FULL-attainment clause, not the class ledger. -/
example : maxClassWeight k7Datum 0 = 2 ∧ classCount k7Datum 0 = 2 := by
  decide

/-! ## K7⁺ — the d ≥ 2 positive control

**Carrier transcription record.**  O-9's K7 positive control (CH3's D2,
census q¹⁴(q²−1)² exact at p ∈ {2,3}) is the SAME type T2 under a TALLER
polygon (vertices (0,7)→(1,6), N = 8, on-line slots {7, 2} both FULL).  The
census carrier holds no polygon datum (C0d): its canonical slot layer is the
ledger image wt(J), and at that layer EVERY T2-shaped datum with h₁ ≥ 1
fails FULL at the base slot (the K7 gate above is exactly this fact) — D2
is therefore INEXPRESSIBLE here, precisely as K6's polygon slot is (see the
K6 record below).  The carrier-honest K7⁺ control is the blueprint's
operative content — `ADMFull` is SATISFIABLE at d ≥ 2, r = 1 — witnessed on
a RAMIFIED datum (e₁ = 2 > 1: expressible only post-ADM-U0, so this gate
also exercises the dropped-`triangular` freedom; C5CtorGate's existing
positive instance is unramified with all weights 0 and period 1). -/

/-- The K7⁺ positive-control datum: r = 1, e = (1, 2), h ≡ 1, f = (2, 1) —
    d = 2, period = 2, ledger weights {0, 1} (w(φ₁) = h₁ = 1), each of the
    two classes fully attained by its f₀ = 2 stage-0 monomials. -/
def k7PosDatum : CensusData where
  r := 1
  e := fun i => if i.1 = 0 then 1 else 2
  h := fun _ => 1
  f := fun i => if i.1 = 0 then 2 else 1
  he := fun i => by split <;> omega
  hf := fun i => by split <;> omega
  h_coprime := fun _ => Nat.coprime_one_left _

/-- K7⁺ slot-weight law: wt(j) = a₁ (the stage-1 class digit; stage 0 rides
    at weight 0, the t₁-digit is `Fin 1`-forced, w(φ₁) = 1).  Evaluated over
    the 4-element index Fintype. -/
theorem k7Pos_wt : ∀ j : k7PosDatum.J, k7PosDatum.wt j = ((j 1).1 : ℕ) := by
  decide

/-- **ADM-U4 gate (K7⁺ leg): compiled ADMFull at d ≥ 2.**  Mechanism on
    display: every on-line slot is some a₁ < 2, and `attainDim a₁ = 2 = d`
    at both classes (evaluated leaves). -/
theorem k7Pos_admFull : ADMFull k7PosDatum := by
  constructor
  intro β hβ
  simp only [CensusData.onLineSlots, Finset.mem_image] at hβ
  obtain ⟨j, -, rfl⟩ := hβ
  rw [k7Pos_wt j]
  have hlt : ((j 1).1 : ℕ) < 2 := (j 1).1.isLt
  have h01 : ((j 1).1 : ℕ) = 0 ∨ ((j 1).1 : ℕ) = 1 := by omega
  rcases h01 with h | h <;> rw [h] <;> decide

/-- Cross-check through the C3 instance, plus the control profile. -/
example : ADMFull k7PosDatum := by decide
example : k7PosDatum.d = 2 ∧ k7PosDatum.period = 2 := by decide

/-! ## K6 — the padding-clause liveness gate, and the leg's adjudication

**ADJUDICATION RECORD (the blueprint's `¬ ADMFull` prose leg).**  The
blueprint row (written pre-ADM-U0) lists "K6 datum (`¬ ADMFull`)
[BLOCKED-BY ADM-U0 — inexpressible at head]".  ADM-U0 has LANDED, so K6
(O-9 warning display 1: e₁ = 3, h₁ = 2, f₀ = f₁ = 1) is now expressible —
but its countermodel content lives at the POLYGON slot β = 1 (on the O-9
line, value-UNATTAINED: ledger weights are {0, 2, 4}), and the carrier
holds no polygon datum: C0d's canonical slot layer `onLineSlots = wt(J)`
does not contain 1.  On the slots the carrier CAN see, every class is a
d = 1 singleton attained at its own weight, so `ADMFull k6Datum` is TRUE —
`k6_admFull` below is the compiled counter-proof to the prose leg
(machine adjudication, not a weakening; nothing is `sorry`d).  The
operative K6 machine gate at the carrier — specified by the ADM-U0
satisfiability record in `ValueSide/Census.lean` ("warning display 1 …
gives `attainDim 1 = 0` at period 3, and the clause is LIVE") — is the
padding-hypothesis liveness pair `k6_attainDim_one` + `k6_period`:
the hypothesis of `not_admFull_of_unattained_onLineSlot` /
`stratumR_count_eq_zero_of_unattained_vertex` (`attainDim β = 0`) was
UNSATISFIABLE pre-repair and is now witnessed. -/

/-- The K6 datum (O-9 rev5 warning display 1): r = 1, e = (1, 3), h ≡ 2,
    f ≡ 1 — d = 1, period = 3, ledger weights {0, 2, 4} (w(φ₁) = h₁ = 2,
    gcd(2, 3) = 1: a RAMIFIED stage-1 type, expressible only post-ADM-U0). -/
def k6Datum : CensusData where
  r := 1
  e := fun i => if i.1 = 0 then 1 else 3
  h := fun _ => 2
  f := fun _ => 1
  he := fun i => by split <;> omega
  hf := fun _ => le_refl 1
  h_coprime := fun i => by
    show Nat.Coprime 2 (if i.1 = 0 then 1 else 3)
    split <;> decide

/-- K6 slot-weight law: wt(j) = 2·a₁ (stage 0 rides at weight 0, both
    t-digits are `Fin 1`-forced, w(φ₁) = 2).  Evaluated over the 3-element
    index Fintype. -/
theorem k6_wt : ∀ j : k6Datum.J, k6Datum.wt j = 2 * ((j 1).1 : ℕ) := by
  decide

/-- **ADM-U4 gate (K6 leg, operative form): the padding clause is LIVE.**
    β = 1 sits in an attained class residue?  No — 1 % 3 misses every
    ledger weight ≤ 1 (only weight 0, class 0): `Gset 1 = ∅`.  Mechanism
    explicit: 2a₁ ≤ 1 forces a₁ = 0, whose class 0 ≠ 1 (mod 3). -/
theorem k6_attainDim_one : k6Datum.attainDim 1 = 0 := by
  unfold CensusData.attainDim
  rw [Finset.card_eq_zero]
  unfold CensusData.Gset
  rw [Finset.filter_eq_empty_iff]
  rintro j - ⟨hmod, hle⟩
  rw [k6_wt j] at hmod hle
  rw [show k6Datum.period = 3 by decide] at hmod
  omega

theorem k6_period : k6Datum.period = 3 := by decide

/-- The compiled adjudication of the prose K6 leg: at C0d's slot layer the
    K6 datum SATISFIES (ADM)-FULL — every carrier-visible slot {0, 2, 4} is
    its d = 1 class's own attained weight.  (The O-9 K6 countermodel is a
    statement about the polygon slot β = 1, invisible to this carrier.) -/
theorem k6_admFull : ADMFull k6Datum := by
  constructor
  intro β hβ
  simp only [CensusData.onLineSlots, Finset.mem_image] at hβ
  obtain ⟨j, -, rfl⟩ := hβ
  rw [k6_wt j]
  have hlt : ((j 1).1 : ℕ) < 3 := (j 1).1.isLt
  have h012 : ((j 1).1 : ℕ) = 0 ∨ ((j 1).1 : ℕ) = 1 ∨ ((j 1).1 : ℕ) = 2 := by
    omega
  rcases h012 with h | h | h <;> rw [h] <;> decide

/-- Cross-checks through the C3 instance + the K6 lattice profile
    (weights {0,2,4}: dims 1 at each attained slot, 0 at the polygon slot
    β = 1 — the CH4 regression row's carrier shadow). -/
example : ADMFull k6Datum := by decide
example : k6Datum.d = 1 ∧ k6Datum.attainDim 0 = 1 ∧ k6Datum.attainDim 2 = 1
    ∧ k6Datum.attainDim 4 = 1 := by decide

end LeanUrat.Scaffold.HD3
