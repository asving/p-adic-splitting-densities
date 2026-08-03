/-
BP_IV §1.2 — the order-r census carrier root (`CensusCore.lean`).
Units in this file: C0a (`CensusData`) · C0b (`d/period/J`) · C0c
(`wt/Gset/attainDim/s`) · C0d (`onLineSlots`) · H1 (`ADMFull`, statement
verbatim — landed by unit C3 as prerequisite; declared immediately after the
derived definitions, per BP_IV §1.0).
This module imports no value-side module (import graph: CensusCore → Hyps →
Census, never a cycle).
-/
import Mathlib

/-!
# The order-r census carriers [wave IV-0a]

**PROVENANCE (unit C0a; BP_IV §1.2).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.2 (statement verbatim) and §1.0
  (module/namespace placement).
* Math source of record: `O9_phaseB_verifybrief_rev5.md` (§§1, 5.1, the r4
  FULL-attainment form) and M08 (`M08-cl6-general_fable.md` §2, Theorem 2).
* Imports: `Mathlib` only.
-/

namespace LeanUrat.Scaffold

/-- The order-r census datum: the ledger of stage triples (e_i, h_i, f_i),
    i = 0..r, with e_i, f_i ≥ 1.  Derived: d = ∏ f_i (census field degree —
    O-9's DELTA-3 index fix: d = f₀⋯f_r, NOT f₀⋯f_{r−1}), the period
    e = ∏ e_i, the slot-weight function wt on the mixed-radix φ-monomial index
    set J (a Fintype), the graded pieces G_β, and s(β) = #{j | wt j ≤ β}.

    **ADM-U0 REPAIR RECORD (HDISCHARGE_H3 §1.3(b) (F-ADM-1), definition-change
    authority).**  The BP_IV §1.2 display carried a fourth axiom row
    `triangular : ∀ i, i.1 ≠ 0 → e i ∣ h i`, which JOINTLY with `h_coprime`
    forces e_i = 1 at every stage i ≥ 1 (e_i ∣ h_i ∧ gcd(h_i, e_i) = 1 ⟹
    e_i = 1 — the compiled degeneracy witnesses, git history at the pre-repair
    `Census.lean`), so the landed carrier could express NO ramified stage-≥1
    type (the K6 datum e₁ = 3, h₁ = 2 fails 3 ∣ 2).  Adjudicated against the
    math source of record, O-9 rev5 §1 (the pinned data sheet): the type data
    is `λ_i = −h_i/e_i in lowest terms` — COPRIMALITY ONLY, e_i > 1 explicitly
    live at stages ≥ 1 (warning display 1).  The row was a transcription
    defect of the blueprint display (the C1/C2 `ledgerE` precedent, REVISION 3)
    and is DROPPED; `he/hf/h_coprime` are the complete axiom set. -/
structure CensusData where
  r : ℕ
  e : Fin (r + 1) → ℕ
  h : Fin (r + 1) → ℕ
  f : Fin (r + 1) → ℕ
  he : ∀ i, 1 ≤ e i
  hf : ∀ i, 1 ≤ f i
  h_coprime : ∀ i, Nat.Coprime (h i) (e i)

/-!
**PROVENANCE (unit F-ADM-3 kernel; `lean/notes/openmath/FADM3_REKEY_2026-08-08.md`;
math source: ADMREAL_2026-08-08.md §5, Lemma CLASS-LAT).**  The abstract
mixed-radix class-equidistribution kernel behind `CensusData.classCard_eq_d`:
in a triangular weight system `w i = u i · ∏_{j > i} m j` with
`gcd(u i, m i) = 1`, the digit-sum map `a ↦ Σ aᵢ·wᵢ` on the digit box
`Π i, Fin (m i)` is INJECTIVE modulo the radix product `∏ m i` — CLASS-LAT's
triangular-system argument in head-peeling form (mod the tail product the
head term dies; cancel the tail product from the modulus, then the unit).
Pure `Nat.ModEq` arithmetic; no census dependence.
-/

namespace ClassLat

/-- The stage weight of the abstract triangular system: `u i` times the
    product of the LATER radices (the O-9 §4 top-normalized shape
    `w_i = E_i·u_i`, `E_i = m_{i+1}⋯m_n`). -/
def wsys {n : ℕ} (m u : Fin n → ℕ) (i : Fin n) : ℕ :=
  u i * ∏ j ∈ Finset.Ioi i, m j

theorem wsys_succ {n : ℕ} (m u : Fin (n + 1) → ℕ) (i : Fin n) :
    wsys m u i.succ = wsys (fun j => m j.succ) (fun j => u j.succ) i := by
  unfold wsys
  rw [Fin.prod_Ioi_succ]

theorem wsys_zero {n : ℕ} (m u : Fin (n + 1) → ℕ) :
    wsys m u 0 = u 0 * ∏ j : Fin n, m j.succ := by
  unfold wsys
  rw [Fin.prod_Ioi_zero]

/-- CLASS-LAT injectivity kernel: the triangular digit sum is injective on
    the digit box modulo the radix product. -/
theorem digitSum_inj {n : ℕ} (m u : Fin n → ℕ) (hm : ∀ i, 1 ≤ m i)
    (hcop : ∀ i, Nat.Coprime (u i) (m i)) (a a' : ∀ i, Fin (m i))
    (h : (∑ i, ((a i : ℕ) * wsys m u i))
        ≡ (∑ i, ((a' i : ℕ) * wsys m u i)) [MOD ∏ i, m i]) :
    a = a' := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ n ih =>
    -- the sum splits as head + reindexed tail (the tail weights are EXACTLY
    -- the truncated system's weights — CLASS-LAT's (F3))
    have hsplit : ∀ b : ∀ i : Fin (n + 1), Fin (m i),
        (∑ i, ((b i : ℕ) * wsys m u i))
          = ((b 0 : ℕ) * u 0) * (∏ j : Fin n, m j.succ)
            + ∑ i : Fin n, ((b i.succ : ℕ)
                * wsys (fun j => m j.succ) (fun j => u j.succ) i) := by
      intro b
      rw [Fin.sum_univ_succ]
      congr 1
      · rw [wsys_zero, mul_assoc]
      · exact Finset.sum_congr rfl fun i _ => by rw [wsys_succ]
    have hM : (∏ i : Fin (n + 1), m i) = m 0 * ∏ j : Fin n, m j.succ :=
      Fin.prod_univ_succ m
    have hP : 0 < ∏ j : Fin n, m j.succ :=
      Finset.prod_pos fun j _ => hm j.succ
    -- (1) tail congruence mod the tail product: the head terms die
    have htail : (∑ i : Fin n, ((a i.succ : ℕ)
          * wsys (fun j => m j.succ) (fun j => u j.succ) i))
        ≡ (∑ i : Fin n, ((a' i.succ : ℕ)
          * wsys (fun j => m j.succ) (fun j => u j.succ) i))
          [MOD ∏ j : Fin n, m j.succ] := by
      have h1 := Nat.ModEq.of_mul_left (m 0) (hM ▸ h)
      rw [hsplit a, hsplit a'] at h1
      have hka : ((a 0 : ℕ) * u 0) * (∏ j : Fin n, m j.succ)
          ≡ 0 [MOD ∏ j : Fin n, m j.succ] :=
        (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_left _ _)
      have hka' : ((a' 0 : ℕ) * u 0) * (∏ j : Fin n, m j.succ)
          ≡ 0 [MOD ∏ j : Fin n, m j.succ] :=
        (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_left _ _)
      have h2 := (hka.add_right _).symm.trans h1
      have h3 := h2.trans (hka'.add_right _)
      rwa [zero_add, zero_add] at h3
    -- (2) inductive hypothesis on the truncated system
    have hEq : (fun i : Fin n => a i.succ) = (fun i : Fin n => a' i.succ) :=
      ih (fun j => m j.succ) (fun j => u j.succ) (fun i => hm i.succ)
        (fun i => hcop i.succ) _ _ htail
    -- (3) head digit: cancel the (now equal) tails, then the tail product
    -- from the modulus, then the unit u 0
    have htails_eq : (∑ i : Fin n, ((a i.succ : ℕ)
          * wsys (fun j => m j.succ) (fun j => u j.succ) i))
        = (∑ i : Fin n, ((a' i.succ : ℕ)
          * wsys (fun j => m j.succ) (fun j => u j.succ) i)) :=
      Finset.sum_congr rfl fun i _ => by rw [congrFun hEq i]
    have hhead : ((a 0 : ℕ) * u 0) * (∏ j : Fin n, m j.succ)
        ≡ ((a' 0 : ℕ) * u 0) * (∏ j : Fin n, m j.succ)
          [MOD m 0 * ∏ j : Fin n, m j.succ] := by
      have h2 := hM ▸ h
      rw [hsplit a, hsplit a', htails_eq] at h2
      exact Nat.ModEq.add_right_cancel' _ h2
    have h4 : (a 0 : ℕ) * u 0 ≡ (a' 0 : ℕ) * u 0 [MOD m 0] :=
      Nat.ModEq.mul_right_cancel' hP.ne' hhead
    have h5 : (a 0 : ℕ) ≡ (a' 0 : ℕ) [MOD m 0] :=
      Nat.ModEq.cancel_right_of_coprime (hcop 0).symm h4
    have h6 : (a 0 : ℕ) = (a' 0 : ℕ) := by
      have h7 : (a 0 : ℕ) % m 0 = (a' 0 : ℕ) % m 0 := h5
      rwa [Nat.mod_eq_of_lt (a 0).isLt, Nat.mod_eq_of_lt (a' 0).isLt] at h7
    funext i
    refine Fin.cases ?_ ?_ i
    · exact Fin.ext h6
    · exact fun j => congrFun hEq j

/-- CLASS-LAT class-count kernel: EVERY residue class mod the radix product
    is hit by EXACTLY ONE digit-box point (any constant offset `off`) — the
    digit sum is injective (`digitSum_inj`), the box and `ℤ/∏mᵢ` have equal
    cardinality, so the class map is a bijection. -/
theorem card_digitBox_class {n : ℕ} (m u : Fin n → ℕ) (hm : ∀ i, 1 ≤ m i)
    (hcop : ∀ i, Nat.Coprime (u i) (m i)) (off c : ℕ) :
    (Finset.univ.filter (fun a : ∀ i, Fin (m i) =>
        ((∑ i, ((a i : ℕ) * wsys m u i)) + off) % (∏ i, m i)
          = c % (∏ i, m i))).card = 1 := by
  have hMpos : 0 < ∏ i, m i := Finset.prod_pos fun i _ => hm i
  set Φ : (∀ i, Fin (m i)) → ℕ :=
    fun a => ((∑ i, ((a i : ℕ) * wsys m u i)) + off) % (∏ i, m i) with hΦ
  have hinj : Function.Injective Φ := by
    intro a a' hh
    exact digitSum_inj m u hm hcop a a' (Nat.ModEq.add_right_cancel' off hh)
  have hcardPi : Fintype.card (∀ i, Fin (m i)) = ∏ i, m i := by
    simp [Fintype.card_pi]
  have himg : Finset.univ.image Φ = Finset.range (∏ i, m i) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (Nat.mod_lt _ hMpos)
    · rw [Finset.card_range, Finset.card_image_of_injective _ hinj,
        Finset.card_univ, hcardPi]
  have hc : c % (∏ i, m i) ∈ Finset.univ.image Φ := by
    rw [himg]
    exact Finset.mem_range.mpr (Nat.mod_lt _ hMpos)
  obtain ⟨a0, -, ha0⟩ := Finset.mem_image.mp hc
  rw [Finset.card_eq_one]
  refine ⟨a0, ?_⟩
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro ha
    exact hinj (ha.trans ha0.symm)
  · rintro rfl
    exact ha0

end ClassLat

/-!
**PROVENANCE (unit C0b; BP_IV §1.2, wave IV-0b; REVISED at BP_IV REVISION 3,
mop-up adjudication).**  Derived defs: `d` = ∏ f_i (the census field degree,
O-9's DELTA-3 index fix: d = f₀⋯f_r, NOT f₀⋯f_{r−1}), the LEDGER period, and
the mixed-radix φ-monomial index set `J` (a Fintype — instance supplied
immediately after the def).

**THE REVISION-3 CARRIER FIX (the C1/C2 adjudication; warrant: the compiled
countermodels `C1Refutation.not_admFull_cmC1` / `C2Refutation.*` of the
pre-revision `Census.lean`, retired with this fix — see git history at
33656d2 and BP_IV REVISION 3).**  The §1.2 display gave stage 0 a full
`Fin (e 0) × Fin (f 0)` pair in `J` and an `e 0` factor in `period`; the O9
ledger (rev5 §§1–2, the math source of record) has stage 0 contributing the
`f₀` monomials `x^{j₀}` ONLY (φ₀ = x, weight 0 — "m = f₀ = d at r = 0") and
the period `e = e₁⋯e_r` (NO e₀ factor; "the O9 convention is e₀ = 1").
Against the display, the O9-scoped laws C1 (r = 0 automaticity — a ROOT (ADM)
row clause) and C2 (the r = 1 criterion) are FALSE (countermodels at e₀ = 2);
the carrier transcription, not the laws, was wrong.  The fix: the LEDGER
stage multiplicity `ledgerE` (:= 1 at stage 0, e_i at stages i ≥ 1) replaces
`e i` in the DERIVED defs `J`/`period`/`wt`-radix.  The stage-0 FIELDS
`e 0`/`h 0` remain carrier data (consumed by C4c's canonical level-1 polygon,
which is untouched by this fix).
-/

namespace CensusData

def d (D : CensusData) : ℕ := ∏ i, D.f i

/-- The LEDGER stage multiplicity (REVISION 3): stage 0 rides at multiplicity
    1 (φ₀ = x contributes the `f₀` monomials only — O9 rev5 §2), stages i ≥ 1
    at their ramification `e i`. -/
def ledgerE (D : CensusData) (i : Fin (D.r + 1)) : ℕ :=
  if i.1 = 0 then 1 else D.e i

@[simp] theorem ledgerE_zero (D : CensusData) : D.ledgerE 0 = 1 := by
  simp [ledgerE]

theorem ledgerE_of_ne_zero (D : CensusData) {i : Fin (D.r + 1)} (hi : i.1 ≠ 0) :
    D.ledgerE i = D.e i := by
  simp [ledgerE, hi]

theorem ledgerE_pos (D : CensusData) (i : Fin (D.r + 1)) : 1 ≤ D.ledgerE i := by
  unfold ledgerE
  split_ifs
  · exact le_rfl
  · exact D.he i

/-- The LEDGER period `e = e₁⋯e_r` (REVISION 3: no `e 0` factor — O9 rev5 §1,
    "e = 1 at r = 0"). -/
def period (D : CensusData) : ℕ := ∏ i, D.ledgerE i

def J (D : CensusData) : Type :=
  (i : Fin (D.r + 1)) → Fin (D.ledgerE i) × Fin (D.f i)

/-- `J` is a Fintype (the blueprint carrier docstring: "the mixed-radix
    φ-monomial index set J (a Fintype)"). -/
instance instFintypeJ (D : CensusData) : Fintype D.J :=
  inferInstanceAs
    (Fintype ((i : Fin (D.r + 1)) → Fin (D.ledgerE i) × Fin (D.f i)))

instance instDecidableEqJ (D : CensusData) : DecidableEq D.J :=
  inferInstanceAs
    (DecidableEq ((i : Fin (D.r + 1)) → Fin (D.ledgerE i) × Fin (D.f i)))

/-!
**PROVENANCE (unit C0c; BP_IV §1.2, wave IV-0c).**  The derived slot-weight
layer: `wt` (signature verbatim from the blueprint; body = the mixed-radix
φ-monomial weight of the O9 ledger, per the C0 unit-table row "wt = the
mixed-radix φ-monomial weight (O9 ledger LED)"), then `Gset`, `attainDim`, `s`
(all three verbatim from the blueprint, `-- unit C0c` annotations).

The `wt` body transcribes `O9_phaseB_verifybrief_rev5.md` §4 (the slot ledger,
Lemma LED's weight data) into the census-datum coordinates:

* ledger weights: `wt(𝐣) = Σ_i j_i · w(φ_i)`, where stage 0 contributes weight
  0 — §2's r = 0/r = 1 automaticity discussion: the `f₀` choices of `j₀` ride
  "at weight contribution 0" (φ₀ = x);
* stage weights: the TOP-NORMALIZED `w(φ_i) = E_i·(e_i·V_i + h_i)`,
  `E_i = e_{i+1}⋯e_r` (O-9 §4's ledger, `w = v_{r+1}`), with the birth values
  `e_i·V_i + h_i` by the pinned (P3) V-recursion (GMN Prop 2.7(4) + Thm 2.11):
  `V₁ = 0` and `V_{i+1} = e_i·f_i·(e_i·V_i + h_i)` — §2's worked data:
  `w(φ₁) = e₁V₁ + h₁, V₁ = 0` (E₁ = 1 at r = 1); `V̂ = e₁f₁·w(φ₁)`.
  **F-ADM-3 re-key record: the pre-re-key transcription read the BIRTH values
  as the weights (no `E_i`) — see the `wphi` docstring;**
* the per-stage mixed-radix split of the blueprint's `Fin (e i) × Fin (f i)`
  pair: `j_i = a_i + e_i·b_i` (`a_i` the mod-`e_i` class digit, `b_i` the
  `t < f_i` digit) — §2's class decomposition `j₁ = j₁* + t·e₁, 0 ≤ t < f₁`.
-/

/-- The (P3) V-recursion ladder (GMN Prop 2.7(4) + Thm 2.11), ℕ-indexed for
    structural recursion: `V₀ := 0` (stage-0 slot, never consumed — stage 0
    carries weight 0), `V₁ := 0`, and `V_{i+2} = e_{i+1}·f_{i+1}·(e_{i+1}·
    V_{i+1} + h_{i+1})` for in-range stages (out-of-range indices return 0;
    `wt` only reads stages `i ≤ r`). -/
def Vrec (D : CensusData) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | (i + 2) =>
    if hi : i + 1 < D.r + 1 then
      let k : Fin (D.r + 1) := ⟨i + 1, hi⟩
      D.e k * D.f k * (D.e k * Vrec D (i + 1) + D.h k)
    else 0

/-- **F-ADM-3 RE-KEY layer (definition-change unit of record; standing
    definition-change authority; `lean/notes/openmath/FADM3_REKEY_2026-08-08.md`;
    ADMREAL_2026-08-08.md §5b finding F-ADM-3 + §8 repair design;
    SYNTHESIS_PASS7_2026-08-08.md queue #4).**  The top-normalization
    multiplier `E_i = e_{i+1}⋯e_r` of the O-9 §4 ledger, read through
    `ledgerE` (every stage `j > i` has `j ≥ 1`, where `ledgerE j = e j`). -/
def Emul (D : CensusData) (i : Fin (D.r + 1)) : ℕ :=
  ∏ j ∈ Finset.Ioi i, D.ledgerE j

theorem Emul_pos (D : CensusData) (i : Fin (D.r + 1)) : 1 ≤ D.Emul i := by
  unfold Emul
  have h : 0 < ∏ j ∈ Finset.Ioi i, D.ledgerE j :=
    Finset.prod_pos fun j _ => D.ledgerE_pos j
  omega

/-- At the TOP stage the multiplier is the empty product: `E_r = 1` — so the
    re-keyed and birth weights agree there (the r ≤ 1 agreement recorded in
    F-ADM-3's consumer audit). -/
theorem Emul_last (D : CensusData) : D.Emul (Fin.last D.r) = 1 := by
  unfold Emul
  rw [Finset.Ioi_eq_empty.mpr fun b _ => Fin.le_last b, Finset.prod_empty]

/-- The BIRTH-normalized stage value `v_{i+1}(φ_i) = e_i·V_i + h_i` (0 at
    stage 0) — the PRE-F-ADM-3 `wphi` body, kept on record as the carrier's
    birth ledger.  F-ADM-3: at r ≥ 2 stages with some later `e_j > 1` this is
    NOT the weight the O-9 §4 census ledger reads. -/
def wbirth (D : CensusData) (i : Fin (D.r + 1)) : ℕ :=
  if i.1 = 0 then 0 else D.e i * D.Vrec i.1 + D.h i

/-- The birth value is a UNIT against its own stage multiplicity:
    `gcd(e_i·V_i + h_i, e_i) = gcd(h_i, e_i) = 1` (`h_coprime`); at stage 0,
    `gcd(0, 1) = 1`.  CLASS-LAT's fact (F2). -/
theorem wbirth_coprime_ledgerE (D : CensusData) (i : Fin (D.r + 1)) :
    Nat.Coprime (D.wbirth i) (D.ledgerE i) := by
  unfold wbirth ledgerE
  split_ifs with h0
  · exact Nat.coprime_one_right 0
  · rw [add_comm]
    exact (Nat.coprime_add_mul_left_left (D.h i) (D.e i)
      (D.Vrec i.1)).mpr (D.h_coprime i)

/-- The stage weight `w(φ_i)` of the O-9 §4 TOP-NORMALIZED ledger: 0 at stage
    0 (φ₀ = x — O9 §2: the `j₀` digit rides at weight contribution 0), and
    `E_i·(e_i·V_i + h_i)` at stages `i ≥ 1` — `w = v_{r+1}`, the weight `wt`
    sums (O-9 §4 Lemma LED; ADMREAL §2: TRI itself forces the top
    normalization).

    **F-ADM-3 RE-KEY RECORD (definition change of record, executed under the
    standing definition-change authority; ADMREAL_2026-08-08.md §5b + §8;
    SYNTHESIS_PASS7_2026-08-08.md queue #4; unit note
    `lean/notes/openmath/FADM3_REKEY_2026-08-08.md`).**  The PRE-RE-KEY body
    was `if i.1 = 0 then 0 else D.e i * D.Vrec i.1 + D.h i` — the BIRTH value
    `v_{i+1}(φ_i)` (kept above as `wbirth`), which lacks the
    `E_i = e_{i+1}⋯e_r` rescale and is at variance with O-9 §4's ledger at
    every r ≥ 2 stage with some later `e_j > 1` (machine evidence: the
    F-ADM-2 88-type r = 2 grid failure reproduction,
    `verification/openmath/admreal_check.py` leg R3′; the two conventions
    agree at r ≤ 1 and wherever all later `e_j = 1`).  Consequence of the
    re-key: (CLASS-d) is a carrier THEOREM at every order
    (`classCard_eq_d` below = ADMREAL Lemma CLASS-LAT), no longer an r ≥ 2
    hypothesis. -/
def wphi (D : CensusData) (i : Fin (D.r + 1)) : ℕ :=
  if i.1 = 0 then 0 else D.Emul i * (D.e i * D.Vrec i.1 + D.h i)

/-- The re-keyed stage weight in kernel shape: `wphi_i = wbirth_i · E_i`
    (true at stage 0 too: `0 = 0·E₀`).  Note `Emul` is definitionally
    `ClassLat`'s tail product, so `wphi = ClassLat.wsys ledgerE wbirth`. -/
theorem wphi_eq_wbirth_mul_Emul (D : CensusData) (i : Fin (D.r + 1)) :
    D.wphi i = D.wbirth i * D.Emul i := by
  unfold wphi wbirth
  split_ifs with h0
  · rw [zero_mul]
  · rw [mul_comm]

/-- Top-stage evaluation: at `i = last r` (with `r ≥ 1` so the stage is not
    stage 0) the multiplier is 1 and the re-keyed weight IS the birth value —
    the evaluation the r ≤ 1 consumer proofs read. -/
theorem wphi_last (D : CensusData) (h0 : (Fin.last D.r).1 ≠ 0) :
    D.wphi (Fin.last D.r)
      = D.e (Fin.last D.r) * D.Vrec D.r + D.h (Fin.last D.r) := by
  unfold wphi
  rw [if_neg h0, Emul_last, one_mul, Fin.val_last]

/-- unit C0c — the mixed-radix φ-monomial slot weight (O9 ledger LED):
    `wt 𝐣 = Σ_i j_i · w(φ_i)` with the per-stage digit `j_i = a_i + e_i·b_i`
    read off the `Fin (ledgerE i) × Fin (f i)` pair (REVISION 3: the ledger
    radix — at stage 0 the class digit collapses, `j₀ = b₀ < f₀`; at stages
    i ≥ 1 `ledgerE i = e i` and the digit is unchanged) and
    `w(φ_i) = wphi i`. -/
noncomputable def wt (D : CensusData) : D.J → ℕ :=
  fun j => ∑ i, ((j i).1.1 + D.ledgerE i * (j i).2.1) * D.wphi i

noncomputable def Gset (D : CensusData) (β : ℕ) : Finset D.J :=
  Finset.univ.filter
    (fun j => D.wt j % D.period = β % D.period ∧ D.wt j ≤ β)         -- unit C0c

noncomputable def attainDim (D : CensusData) (β : ℕ) : ℕ := (D.Gset β).card

noncomputable def s (D : CensusData) (β : ℕ) : ℕ :=
  (Finset.univ.filter fun j : D.J => D.wt j ≤ β).card                -- unit C0c

/-!
**PROVENANCE (unit C0d; BP_IV §1.2, wave IV-0b).**  Signature verbatim from the
blueprint (`-- unit C0d`); the body is DERIVED (the blueprint displays no body)
and is hereby flagged for division-lead/Codex ratification per the trust
boundary (definitions are where errors hide):

* O9 §2 (the TRI bullet): the w-values attained on `{deg < m} \ {0}` are
  exactly `{e·v + wt(𝐣) : v ≥ 0, 𝐣 a ledger index}` — the ON-LINE lattice
  values.  The census carrier holds no polygon datum (no face endpoints, no
  `U₀/ℓ/K_D`), so the carrier's canonical finite slot set is the `v = 0`
  fundamental layer: the ledger's own attained weights, `wt(J)` as a Finset.
* Fit with the unit table: C1's sketch "at r = 0 … count the f₀ on-line j
  directly" reads off exactly this image (at r = 0 the slots collapse to the
  weights of the single-digit ledger); C3 gets `Finset.decidableBAll` over
  this Finset; H1's `ADMFull` quantifies `∀ β ∈ D.onLineSlots`.
* NOT chosen (recorded to prevent re-attempts): all on-line lattice points
  `≤ max wt` in attained classes — refuted against C1 (at r = 0 it contains
  class points below the class weight, where `attainDim = 0 ≠ d`, breaking
  the blueprint's r = 0 automaticity row).
-/

/-- unit C0d — the on-line lattice slots of the census datum: the Finset of
    ledger-attained slot weights `{wt 𝐣 : 𝐣 ∈ J}` (O9 §2 TRI bullet's `v = 0`
    fundamental layer of the on-line lattice `{e·v + wt(𝐣)}`).  Consumed by
    `ADMFull` (unit H1: every on-line slot FULLY attained) and the C1–C3
    layer. -/
noncomputable def onLineSlots (D : CensusData) : Finset ℕ :=
  Finset.image D.wt Finset.univ

/-!
**PROVENANCE (unit F-ADM-3; ADMREAL_2026-08-08.md §5, Lemma CLASS-LAT, on the
re-keyed carrier).**  The class-count law at EVERY order.  Proof shape: split
each slot digit `j_i = a_i + e_i·b_i` (class digit `a_i`, `t`-digit `b_i`);
for FIXED `b` the `a`-sum is a translate of the triangular digit sum, which
hits every class mod `e` exactly once (`ClassLat.card_digitBox_class`, with
`m = ledgerE`, `u = wbirth`, offset = the `b`-part of the weight — legal
because `wphi = wsys ledgerE wbirth`, i.e. the re-keyed weights carry the
`E_i` factor); summing over the `∏ f_i = d` choices of `b` gives `d` per
class.  Inputs: the carrier axioms only (`h_coprime` via
`wbirth_coprime_ledgerE`).  This is the statement the F-ADM-2 scan REFUTED on
the pre-re-key coded lattice (88 r = 2 grid types, all with some `E_i > 1`)
— falsifier legs: `verification/openmath/admreal_check.py` R3″/R7.
-/

/-- **CLASS-LAT on the carrier (every order):** each residue class mod the
    ledger period carries EXACTLY `d = ∏ f_i` slots. -/
theorem classCard_eq_d (D : CensusData) (c : ℕ) :
    (Finset.univ.filter
      (fun j : D.J => D.wt j % D.period = c % D.period)).card = D.d := by
  -- (1) the weight splits: class-digit part (in kernel shape) + f-digit part
  have hwt : ∀ j : D.J, D.wt j
      = (∑ i, ((j i).1.1 * ClassLat.wsys D.ledgerE D.wbirth i))
        + ∑ i, D.ledgerE i * (j i).2.1 * D.wphi i := by
    intro j
    unfold wt
    have hterm : ∀ i : Fin (D.r + 1),
        ((j i).1.1 + D.ledgerE i * (j i).2.1) * D.wphi i
          = (j i).1.1 * ClassLat.wsys D.ledgerE D.wbirth i
            + D.ledgerE i * (j i).2.1 * D.wphi i := by
      intro i
      rw [add_mul]
      congr 1
      rw [wphi_eq_wbirth_mul_Emul]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
  -- (2) count fiberwise over the f-digit vector b
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun j : D.J => (fun i => (j i).2 : ∀ i, Fin (D.f i)))
    (t := Finset.univ) (fun j _ => Finset.mem_univ _)]
  -- (3) each fiber counts exactly 1 (the CLASS-LAT kernel)
  have hone : ∀ b : ∀ i, Fin (D.f i),
      ((Finset.univ.filter
          (fun j : D.J => D.wt j % D.period = c % D.period)).filter
        (fun j => (fun i => (j i).2) = b)).card = 1 := by
    intro b
    rw [Finset.filter_filter]
    have hbij : (Finset.univ.filter (fun j : D.J =>
          D.wt j % D.period = c % D.period ∧ (fun i => (j i).2) = b)).card
        = (Finset.univ.filter (fun a : ∀ i, Fin (D.ledgerE i) =>
            ((∑ i, ((a i : ℕ) * ClassLat.wsys D.ledgerE D.wbirth i))
                + ∑ i, D.ledgerE i * (b i).1 * D.wphi i)
              % (∏ i, D.ledgerE i)
              = c % (∏ i, D.ledgerE i))).card := by
      refine Finset.card_bij' (fun j _ => fun i => (j i).1)
        (fun a _ => fun i => (a i, b i)) ?_ ?_ ?_ ?_
      · intro j hj
        obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hsub : (∑ i, ((j i).1.1 * ClassLat.wsys D.ledgerE D.wbirth i))
            + ∑ i, D.ledgerE i * (b i).1 * D.wphi i = D.wt j := by
          rw [hwt j]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [← congrFun h2 i]
        rw [hsub]
        exact h1
      · intro a ha
        have h1 := (Finset.mem_filter.mp ha).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, rfl⟩
        rw [hwt _]
        exact h1
      · intro j hj
        obtain ⟨-, -, h2⟩ := Finset.mem_filter.mp hj
        funext i
        exact Prod.ext rfl (congrFun h2 i).symm
      · intro a _
        rfl
    rw [hbij]
    exact ClassLat.card_digitBox_class D.ledgerE D.wbirth D.ledgerE_pos
      D.wbirth_coprime_ledgerE _ c
  rw [Finset.sum_congr rfl fun b _ => hone b]
  -- (4) total: the f-digit box has ∏ f_i = d points
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ]
  unfold d
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ => Fintype.card_fin _

end CensusData

/-!
**PROVENANCE (unit H1; BP_IV §1.0).**  Statement transcribed VERBATIM from the
blueprint ("In `CensusCore.lean`, immediately after `CensusData` and its
derived definitions").  Landed by unit C3 as its compile-time prerequisite
(H1 had not landed when C3 ran, 2026-08-01); H1's owner should verify verbatim
transcription rather than re-declare.  Math source of record: ROOT §3.1 (ADM).
-/

/-- **(ADM)-FULL** (ROOT §3.1 (ADM), the single operative O-9 r4 form; unit of
record 35faac7): every on-line lattice slot's β_k is FULLY attained by the
ledger — `attainDim β_k = d`, equivalently
`#{j : wt j ≡ β_k (mod e), wt j ≤ β_k} = d`.  p-free, per-datum decidable
(unit C3).  Automatic at r = 0 ONLY (unit C1); NOT automatic at r ≥ 1 (two
countermodels on file, O-9 pass-2/pass-3 records). -/
structure ADMFull (D : CensusData) : Prop where
  full_attained : ∀ β ∈ D.onLineSlots, D.attainDim β = D.d

end LeanUrat.Scaffold
