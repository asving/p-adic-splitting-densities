/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GRDefs
import LeanUrat.B2D.GR0b_suppliers
import LeanUrat.Scaffold.HDischarge.H1.Order1

/-!
# B2D/GR3_keyResidual — the summed key residual  [B2DEF_LEAN unit GR-3; wave 2a]

Blueprint §5 GR-3. moves_ref: §B2-DEF D.5 RESIDUAL sum + D.1(b) no-cancellation
(MOVES :2270–2277), D.8 m̂ = −t·h·g. deps: GR-1, GR-2. difficulty: medium-hard.
REUSE: `Node.mhat` (the existing m̂ — cite, don't rebuild), the LANDED
`H1.nodeLift_key_res` proof architecture (its `hRadd` recomposition induction,
adapted with the sharp scalar-1 assembly).

## ROUTE-(a) EXECUTION (2026-08-08, GR34_DISPOSITION; supersedes the wave-2a STOP
## below for the STATEMENTS): `ReadHyps` gained the frame pins `hσs`/`hσt`
## (fence-(vii) statement change, campaign-owner adjudication under standing
## authority), so `GR3_keyResidual_pinned`/`GR3_keyResidual` are now PROVED —
## one-liners from `GR3_keyResidual_level` at `R.hσs`/`R.hσt`. The abstract-frame
## (σ.e ≥ 2) scope is RETIRED as believed-false-and-unconsumed (the countermodel
## record below stands as the reason; zero consumers ever bound that face).

## WAVE-2a ADJUDICATION (2026-08-02): the frozen forms STOP — THE FRAME-SIDE PINS
## ARE A GENUINE RESIDUE; the supplier-level forms are PROVED below

**The obstruction, exactly** (N-GR1 check N5, run 2026-08-02, numeric shadow in
`verification/openmath/ngr1_slotpos_trace.py`; the Lean-side suppliers in
`GR0b_suppliers.lean`): the summed positions are
`pos(κ) = −σ.t·σ.wPrev(t_κ) + e·κ·σ.s` with `σ.e·wPrev(t_κ) = w(t_κ) = ν.h(g−κ)`
(`Stage.hStretch`), so over ℤ: `σ.e·pos(κ) = κ·ν.e − σ.t·ν.h·g` (via `hscale` +
the FRAME's `hbez`). `ReadHyps` forces `ν.e = 1`, `ν.t = 0`, `m̂ = 0`
(`readHyps_e_eq_one` etc.) — but pins NOTHING about the FRAME's `(σ.e, σ.s, σ.t)`.
At an abstract frame with `σ.e ≥ 2` the position lattice COMPRESSES by `σ.e`:
integrality forces the present slots onto `κ ≡ g (mod σ.e)` (so `ψ = φ(z^{σ.e})`,
a gap polynomial — irreducible examples exist whenever `p ∤ σ.e`, e.g. `z² + 1`
over `F₃`), and the sum becomes `T^c·toLaurent φ` with `deg φ = g/σ.e < g` —
NEITHER the pinned form NOR the ∃-form can hold (`toLaurent` is injective and
`T`-shifts preserve support gaps). Designed genuine-stage configuration: `p = 3`,
frame = the MacLane stage `[v₃; w(X) = 1/2]` (normalized `w = min(2v₃ + i)`,
`(e,h,s,t) = (2,1,0,1)`), fake node `(ν.e, ν.h) = (1,1)`, `ψ = z²+1`, realizer
`t₀ = 3`, `Φ′ = X² + 3`: every `ReadHyps` field checks, `R(Φ′) = C(1)·T⁻¹ + 1` —
adjacent support vs the gap-2 target. VERDICT: the frozen statements are FALSE at
the abstract `Node` carrier (mathematical countermodel; NOT compilable over the
corpus ambient `F4` — a gap-ψ over a char-2 field is a Frobenius power, never
irreducible — so a compiled countermodel is priced at a `p ≠ 2` stage forge, one
full unit). Per the frozen-interface discipline the E-phase sorries STAND
byte-unchanged; per the "new supplier lemmas" allowance the PROVED route is:

* `GR3_keyResidual_level` (+ `'` ∃-form): the frozen conclusion WITH the two frame
  pins `ν.σ.s = 1`, `ν.σ.t = 0` — exactly what `GR0b.frame_level_of_history`
  supplies at interior coherent reads (where `child_e` + `he1t` + `hbez` force
  them). On the recorded perimeter this loses nothing: recorded frames of level
  reads ARE level (`σ.e = ν.e = 1`). GR-4's history-level discharger consumes it.

**Why the configuration is invisible to the recorded tower**: `HistoryCoherent`'s
`child_e` ties every non-root frame's `σ.e` to the node's own `ν.e`, which
`ReadHyps` forces to 1 — the countermodel frame (`σ.e = 2` hosting a `ν.e = 1`
read) is UNRECORDABLE. The residue is an abstract-carrier artifact, but the frozen
statement quantifies over the abstract carrier, so it stands OPEN-OBSTRUCTED, not
proved. Re-adjudication of the §4 interface (adding the frame pins to `ReadHyps`
or re-keying `graded_read` to the history carrier) is a statement-change decision
for the campaign owner, not this unit (fence (vii)).

STATEMENT FLAG (N-GR1 gate): RUN 2026-08-02 GREEN (blueprint §7 run record) — the
pinned display's arithmetic (`m̂ = −t·h·g`, unit stride) verified exactly at every
probed genuine read; the N5 leg exhibits the frame-side compression above.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.Scaffold.HDischarge.H1

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **GR-3, SUPPLIER-LEVEL, PROVED**: the pinned conclusion under the two frame
pins `ν.σ.s = 1`, `ν.σ.t = 0` (supplied at interior coherent reads by
`GR0b.frame_level_of_history`). `ReadHyps` itself forces the read-side pins
(`ν.e = 1`, `ν.h = ν.σ.h`, `ν.t = 0`, hence `m̂ = 0`), and the D.5 sum argument is
then the landed `nodeLift_key_res` recomposition with the sharp scalar-1/`T^0`
assembly kept (the ∃-form there hides `c = 1, k = 0`; the graded_read consumer
needs them pinned). -/
theorem GR3_keyResidual_level (ν : Node p F) (Φhat : Polynomial ℤ_[p])
    (hlift : IsNodeLift ν Φhat) (R : ReadHyps ν)
    (hσs : ν.σ.s = 1) (hσt : ν.σ.t = 0) :
    ν.σ.R Φhat = LaurentPolynomial.T ν.mhat * Polynomial.toLaurent ν.ψ := by
  classical
  have hνe : ν.e = 1 := readHyps_e_eq_one ν R
  have hlevel : ν.h = ν.σ.h := readHyps_h_eq ν R
  rw [readHyps_mhat_eq_zero ν R, LaurentPolynomial.T_zero, one_mul]
  -- the landed `nodeLift_key_res` recomposition, sharp assembly kept:
  obtain ⟨tt, h0, hcl, heq⟩ := hlift
  set g := ν.g with hg
  set σ := ν.σ with hσ
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  set BB : ℕ → Polynomial ℤ_[p] :=
    fun k => if k < g then tt k else if k = g then 1 else 0 with hBB
  have hkey : Φhat = ∑ k ∈ Finset.range (g + 1), BB k * σ.Φ ^ k := by
    rw [Finset.sum_range_succ]
    have h1 : ∑ k ∈ Finset.range g, BB k * σ.Φ ^ k =
        ∑ k ∈ Finset.range g, tt k * σ.Φ ^ k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hBB]
      simp [Finset.mem_range.mp hk]
    have h2 : BB g = 1 := by rw [hBB]; simp
    rw [h1, h2, one_mul, heq, hνe]
    simp only [one_mul]
    exact add_comm _ _
  have hψg : ν.ψ.coeff g = 1 := by
    have := ν.hψmonic.coeff_natDegree
    rwa [ν.hψdeg] at this
  have hslotR : ∀ k ≤ g, BB k ≠ 0 →
      σ.R (BB k * σ.Φ ^ k) =
        LaurentPolynomial.C (ν.ψ.coeff k) * LaurentPolynomial.T (k : ℤ) := by
    intro k hk hBk
    rcases lt_or_eq_of_le hk with hklt | hkeq
    · have httk : tt k ≠ 0 := by
        intro h
        apply hBk
        rw [hBB]
        simp [hklt, h]
      have hψk : ν.ψ.coeff k ≠ 0 := fun h => httk (h0 k h)
      obtain ⟨_, _, _, hR⟩ := hcl k hklt hψk
      have hBBk : BB k = tt k := by rw [hBB]; simp [hklt]
      rw [hBBk, σ.hRmul (tt k) (σ.Φ ^ k) httk (pow_ne_zero k hΦne),
        stage_R_pow σ σ.Φ hΦne k, σ.hRΦ, hR, hσt, LaurentPolynomial.T_pow, hσs]
      simp [LaurentPolynomial.T_zero]
    · have hBBk : BB k = 1 := by rw [hBB]; simp [hkeq]
      rw [hBBk, one_mul, stage_R_pow σ σ.Φ hΦne k, σ.hRΦ,
        LaurentPolynomial.T_pow, hσs, hkeq, hψg]
      simp
  have hslotW : ∀ k ≤ g, BB k ≠ 0 →
      σ.w (BB k) + (k : ℤ) * σ.w σ.Φ = (g : ℤ) * (σ.h : ℤ) := by
    intro k hk hBk
    rcases lt_or_eq_of_le hk with hklt | hkeq
    · have httk : tt k ≠ 0 := by
        intro h
        apply hBk
        rw [hBB]
        simp [hklt, h]
      have hψk : ν.ψ.coeff k ≠ 0 := fun h => httk (h0 k h)
      obtain ⟨_, _, hw, _⟩ := hcl k hklt hψk
      have hBBk : BB k = tt k := by rw [hBB]; simp [hklt]
      rw [hBBk, hw, σ.hwΦ, hlevel]
      ring
    · have hBBk : BB k = 1 := by rw [hBB]; simp [hkeq]
      have hw1 : σ.w 1 = 0 := by
        have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
        rw [mul_one] at h
        omega
      rw [hBBk, hw1, σ.hwΦ, hkeq]
      ring
  have hdegBB : ∀ k, (BB k).degree < σ.Φ.degree := by
    intro k
    have hΦdeg : (0 : WithBot ℕ) < σ.Φ.degree := stage_degree_pos σ
    rw [hBB]
    by_cases hklt : k < g
    · simp only [if_pos hklt]
      by_cases httk : tt k = 0
      · rw [httk]; simpa using lt_of_le_of_lt bot_le hΦdeg
      · have hψk : ν.ψ.coeff k ≠ 0 := fun h => httk (h0 k h)
        obtain ⟨_, hin, _, _⟩ := hcl k hklt hψk
        exact hin
    · simp only [if_neg hklt]
      by_cases hkeq : k = g
      · simpa [hkeq, Polynomial.degree_one] using hΦdeg
      · simpa [hkeq] using lt_of_le_of_lt bot_le hΦdeg
  have main : ∀ m, m ≤ g + 1 →
      σ.R (∑ k ∈ Finset.range m, BB k * σ.Φ ^ k) =
        ∑ k ∈ Finset.range m, LaurentPolynomial.C (ν.ψ.coeff k) *
          LaurentPolynomial.T (k : ℤ) ∧
      ((∑ k ∈ Finset.range m, BB k * σ.Φ ^ k) ≠ 0 →
        σ.w (∑ k ∈ Finset.range m, BB k * σ.Φ ^ k) = (g : ℤ) * (σ.h : ℤ)) := by
    intro m
    induction m with
    | zero => intro _; simp [σ.hR0]
    | succ m ih =>
      intro hm1
      have hm : m ≤ g + 1 := by omega
      have hmg : m ≤ g := by omega
      obtain ⟨ihR, ihW⟩ := ih hm
      set Sm := ∑ k ∈ Finset.range m, BB k * σ.Φ ^ k with hSm
      have hdev : ∀ (mm : ℕ), mm ≤ g + 1 →
          Moves.IsDevelopment σ.Φ (∑ k ∈ Finset.range mm, BB k * σ.Φ ^ k)
            (fun k => if k < mm then BB k else 0) mm := by
        intro mm _
        refine ⟨fun j => ?_, fun j hj => by simp [Nat.not_lt.mpr hj], ?_⟩
        · by_cases hjm : j < mm
          · simpa [hjm] using hdegBB j
          · simpa [hjm] using lt_of_le_of_lt bot_le (stage_degree_pos σ)
        · refine Finset.sum_congr rfl fun k hk => ?_
          simp [Finset.mem_range.mp hk]
      have hWof : ∀ (mm : ℕ), mm ≤ g + 1 →
          (∑ k ∈ Finset.range mm, BB k * σ.Φ ^ k) ≠ 0 →
          σ.w (∑ k ∈ Finset.range mm, BB k * σ.Φ ^ k) = (g : ℤ) * (σ.h : ℤ) := by
        intro mm hmm hne
        obtain ⟨_, ⟨j, hjmm, hjnz, hjeq⟩⟩ :=
          σ.hK1 _ _ mm hne (hdev mm hmm)
        simp only [] at hjnz hjeq
        have hjnz' : BB j ≠ 0 := by
          intro h
          apply hjnz
          simp [hjmm, h]
        have hjeq' : σ.w (∑ k ∈ Finset.range mm, BB k * σ.Φ ^ k) =
            σ.w (BB j) + (j : ℤ) * σ.w σ.Φ := by
          simpa [hjmm] using hjeq
        rw [hjeq']
        exact hslotW j (by omega) hjnz'
      have hzero_digits : Sm = 0 → ∀ k, k < m → ν.ψ.coeff k = 0 := by
        intro hS0 k hk
        have huniq := LeanUrat.Scaffold.DictIII.devCoeff_eq_of_isDevelopment
          σ.hmonic m Sm (fun k => if k < m then BB k else 0) (hdev m hm) k
        rw [hS0] at huniq
        simp only [LeanUrat.Scaffold.DictIII.devCoeff_zero_left] at huniq
        have hBk0 : BB k = 0 := by
          have := huniq
          simpa [hk] using this
        by_contra hψk
        rcases lt_or_eq_of_le (le_of_lt (lt_of_lt_of_le hk hmg)) with hklt | hkeq
        · obtain ⟨htt, _, _, _⟩ := hcl k hklt hψk
          apply htt
          have : BB k = tt k := by rw [hBB]; simp [hklt]
          rwa [this] at hBk0
        · have : BB k = 1 := by rw [hBB]; simp [hkeq]
          rw [this] at hBk0
          exact one_ne_zero hBk0
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← hSm]
      by_cases hBm : BB m = 0
      · have hψm : ν.ψ.coeff m = 0 := by
          by_contra hψm
          rcases lt_or_eq_of_le hmg with hmlt | hmeq
          · obtain ⟨htt, _, _, _⟩ := hcl m hmlt hψm
            apply htt
            have : BB m = tt m := by rw [hBB]; simp [hmlt]
            rwa [this] at hBm
          · have : BB m = 1 := by rw [hBB]; simp [hmeq]
            rw [this] at hBm
            exact one_ne_zero hBm
        constructor
        · rw [hBm, zero_mul, add_zero, hψm, map_zero, zero_mul, add_zero]
          exact ihR
        · intro hne
          rw [hBm, zero_mul, add_zero] at hne ⊢
          exact ihW hne
      · have hFm : BB m * σ.Φ ^ m ≠ 0 := mul_ne_zero hBm (pow_ne_zero m hΦne)
        have hFmR : σ.R (BB m * σ.Φ ^ m) =
            LaurentPolynomial.C (ν.ψ.coeff m) * LaurentPolynomial.T (m : ℤ) :=
          hslotR m hmg hBm
        have hFmW : σ.w (BB m * σ.Φ ^ m) = (g : ℤ) * (σ.h : ℤ) := by
          rw [σ.hwmul (BB m) (σ.Φ ^ m) hBm (pow_ne_zero m hΦne),
            stage_w_pow σ σ.Φ hΦne m]
          exact hslotW m hmg hBm
        by_cases hS0 : Sm = 0
        · rw [hS0, zero_add]
          constructor
          · rw [hFmR]
            have : ∑ k ∈ Finset.range m, LaurentPolynomial.C (ν.ψ.coeff k) *
                LaurentPolynomial.T (k : ℤ) = 0 := by
              refine Finset.sum_eq_zero fun k hk => ?_
              rw [hzero_digits hS0 k (Finset.mem_range.mp hk), map_zero, zero_mul]
            rw [this, zero_add]
          · intro _; exact hFmW
        · have hsum_ne : Sm + BB m * σ.Φ ^ m ≠ 0 := by
            intro habs
            have hdevs := hdev (m + 1) hm1
            rw [Finset.sum_range_succ] at hdevs
            have := LeanUrat.Scaffold.DictIII.devCoeff_eq_of_isDevelopment
              σ.hmonic (m + 1) (Sm + BB m * σ.Φ ^ m)
              (fun k => if k < m + 1 then BB k else 0) hdevs m
            rw [habs] at this
            simp only [LeanUrat.Scaffold.DictIII.devCoeff_zero_left] at this
            apply hBm
            simpa [Nat.lt_succ_self] using this
          have hWm1 : σ.w (Sm + BB m * σ.Φ ^ m) = (g : ℤ) * (σ.h : ℤ) := by
            have := hWof (m + 1) hm1 (by rwa [Finset.sum_range_succ])
            rwa [Finset.sum_range_succ] at this
          have hradd := σ.hRadd Sm (BB m * σ.Φ ^ m) hS0 hFm hsum_ne
            (by rw [ihW hS0, hFmW]) (by rw [hWm1, ihW hS0])
          constructor
          · rw [hradd, ihR, hFmR]
          · intro _; exact hWm1
  have hfin := (main (g + 1) le_rfl).1
  rw [← hkey] at hfin
  have hψsum : Polynomial.toLaurent ν.ψ =
      ∑ k ∈ Finset.range (g + 1), LaurentPolynomial.C (ν.ψ.coeff k) *
        LaurentPolynomial.T (k : ℤ) := by
    conv_lhs => rw [ν.ψ.as_sum_range' (g + 1) (by rw [ν.hψdeg]; omega)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => Polynomial.toLaurent_C_mul_T k _
  rw [hfin]
  exact hψsum.symm

/-- **GR-3, SUPPLIER-LEVEL ∃-form** (the `graded_read` clause-2 shape at the frame
pins; scalar 1 as `GrBKeyLaws.key_res` needs). -/
theorem GR3_keyResidual_level' (ν : Node p F) (Φhat : Polynomial ℤ_[p])
    (hlift : IsNodeLift ν Φhat) (R : ReadHyps ν)
    (hσs : ν.σ.s = 1) (hσt : ν.σ.t = 0) :
    ∃ mh : ℤ, ν.σ.R Φhat = LaurentPolynomial.T mh * Polynomial.toLaurent ν.ψ :=
  ⟨ν.mhat, GR3_keyResidual_level ν Φhat hlift R hσs hσt⟩

/-- **GR-3, pinned form**: distinct slot positions (GR-2's strictly monotone
`readPos`) mean no cancellation (D.1(b)), and the slot sum recomposes to
`σ.R Φ′ = T^{m̂}·toLaurent ψ` at the D.8 normalization `m̂ = Node.mhat = −t·h·g`.
N-GR1-gated display (module docstring). **ROUTE-(a) STATUS (2026-08-08): PROVED
at the ReadHyps-pinned face** — the frame pins `(σ.s, σ.t) = (1, 0)` are now
`ReadHyps` fields (`R.hσs`/`R.hσt`; GR34_DISPOSITION route (a)), so this is the
supplier-level `GR3_keyResidual_level` fired at the pack's own pins. -/
theorem GR3_keyResidual_pinned (ν : Node p F) (Φ' : Polynomial ℤ_[p])
    (hlift : IsNodeLift ν Φ') (R : ReadHyps ν) :
    ν.σ.R Φ' = LaurentPolynomial.T ν.mhat * Polynomial.toLaurent ν.ψ :=
  GR3_keyResidual_level ν Φ' hlift R R.hσs R.hσt

/-- **GR-3, the ∃-form** (§4's frozen `graded_read` clause 2; fills
`GrBKeyLaws.key_res` with `c = 1`). **ROUTE-(a) STATUS (2026-08-08): PROVED at
the ReadHyps-pinned face** (frame pins now pack fields; GR34_DISPOSITION). -/
theorem GR3_keyResidual (ν : Node p F) (Φ' : Polynomial ℤ_[p])
    (hlift : IsNodeLift ν Φ') (R : ReadHyps ν) :
    ∃ mh : ℤ, ν.σ.R Φ' = LaurentPolynomial.T mh * Polynomial.toLaurent ν.ψ :=
  ⟨ν.mhat, GR3_keyResidual_pinned ν Φ' hlift R⟩

end LeanUrat.B2D

#print axioms LeanUrat.B2D.GR3_keyResidual_pinned
#print axioms LeanUrat.B2D.GR3_keyResidual
#print axioms LeanUrat.B2D.GR3_keyResidual_level
#print axioms LeanUrat.B2D.GR3_keyResidual_level'
