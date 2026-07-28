/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsV
import LeanUrat.HC1.S2_childW
import LeanUrat.HC1.V4_readLanding
import LeanUrat.HC2.Defs

/-!
# HC1.V10_transportWindow — §B2-DEF D.8-(TRANSPORT), UPWARD leg, the FORCED-WINDOW
# clause, transcribed at the ReadFrame (blueprint §10 REV, V10; V4's follow-on)

**THE CHARGED DISPLAY** (MOVES_2026-07-24.md lines 2520–2528, quoted VERBATIM — the
one display the R3b adjudication (REV-3 block of `V9_K1nonrec.lean`) found blueprint
§10.1 had WRONGLY fenced out of V4):

> UPWARD (uniqueness only — retyped at rev D‴, pass-11 finding 3; the return
> carries verified at rev D¹¹, F4): given (a, μ, (C_j)_j), recover the slot data
> by strong induction on j: carry_j is a function of d_μ, …, d_{j−1} ALONE
> (display above), hence already recovered; then d_j ≡ C_j − carry_j mod ψ, and
> d_j = z^{q_j}·(a polynomial of degree < g) with the window base q_j forced by
> the stride/width data (slot j's S5 position, plus jm̂ − a); z^{q}·{deg <
> g} is a full system of representatives mod ψ for every q (z a unit mod ψ), so
> the congruence class plus the forced window determine d_j uniquely: the
> recursion inverts UNIQUELY wherever both sides are actual data.

At the REGRADED frame the clause reads: each minimizing slot term of the
Φ̂-development carries its residual in the (S5′)-forced window — at the vertex
slot this IS the bottom-window law, R3b's exact residue
(`V9_wvEqStretch_of_bottomSlot`'s hypothesis).

## ⚠⚠ THE TRANSCRIPTION FINDING (V10 round, 2026-07-28) — READ BEFORE CONSUMING ⚠⚠

Transcribing the clause "wherever both sides are actual data" forces one to ask what
Lean data render *actual*.  The R3b countermodel (`verification/r3b_countermodel_check.py`,
REV-3 block) proves the ReadFrame + V4-landing data alone do NOT: on those data the
window law is FALSE (deficit 1 at the vertex).  The faithful *actual-data* carrier in
the recorded semantics is the RECORDED TRANSITION — the child stage σ′ with
`TransitionData` keyed at the read pair (HistoryCoherent's non-recentering leg) — and
transcribing the forced window against IT yields the following, PROVED below:

1. **`V10_forcedKeyWeight`** — the child-stage laws FORCE the read pair: at any
   recorded steep read-lift transition with `e★·g ≥ 2`,
   `h★ = e★²·g·σ.h` (the parent-key power `Φ^{e★g} = Φ̂ − τ` is weighed once by
   `σ′.hwmul + σ′.hStretch` as `e★g·e★σ.h` and once by `child_slotmin` as
   `min(e★·σ.w τ, h★)`; steepness kills the τ-slot).  Corollaries: `e★ = 1`
   (coprimality), `t★ = 0` (the P2 pin), `s★ = 1` (Bézout), `h★ = g·σ.h`.

2. **`V10_readTransition_incompatible`** — with the recorded Bézout ties
   `σ′.s = s★, σ′.t = t★` the recorded transition is CONTRADICTORY outright at
   `e★·g ≥ 2`: `σ′.R Φ̂ = T s★ = T 1` (hRΦ + the tie) while
   `σ′.R Φ̂ = σ′.R(Φ)^g = C(c^g)·T 0` (hRlt through the deep τ-slot + hS5′ at the
   forced position `−t★·σ.w Φ = 0`) — a Laurent monomial at position 1 equal to one
   at position 0.  **The non-corner perimeter of the recorded read-transition
   semantics is EMPTY**: `HistoryCoherent`'s round-3 choice to key `TransitionCoreL`
   at the READ pair `(ν.e, ν.h)` on the READ lift is UNSATISFIABLE together with the
   child's own Stage laws whenever `ν.e·ν.g ≥ 2` and a successor node is recorded.
   (S9's genuine transitions are untouched: their lift is the FRAME-pair standard
   lift, equal-weight in the frame grading, and the same computation is consistent.
   The faithful child of a READ lift weighs `Φ̂ ↦ e★·(e★h★g)` — the regraded side
   value — not `h★`; re-keying `TransitionCoreL`/`TransitionData` there is a NAMED
   SIGN-OFF ITEM, not silently changed here.)

3. **`V10_transportWindow`** — the charged unit: the forced-window/bottom-slot law at
   the vertex coefficient, stated over the proved `V2_readFrame` carrier with V4's
   landing data + the recorded transition, on the non-corner perimeter `e★·g ≥ 2`.
   PROVED — but **VACUOUSLY, through finding 2**: the stated hypotheses are
   contradictory.  This is disclosed here and in every consumer record; the honest
   mathematical transport (the display's genuine content) awaits the child-keying
   repair above and is NOT claimed as machine-checked mathematics.

**The recorded boundary caveats, handled explicitly per the display** (REV-3 record:
"the BOUNDARY t★ = 1 ∧ h★ − e★σ.h = 1 is NOT decided by the window equation alone —
the transcriber must take the display's full strength there"): at recorded
transitions the boundary is EMPTY — finding 1 forces `t★ = 0`, so the parameter
region `t★ = 1` (and with it the undecided boundary `t★ = 1 ∧ h★ − e★σ.h = 1`) is
unreachable; likewise `t★·(h★ − e★σ.h) ≥ 2`.  The only surviving corner of the
window equation `l₋ = t★·deficit` is `t★ = 0` — where it degenerates to `l₋ = 0`,
the bottom-window law itself — at the `e★·g = 1` corner (R3c), which this unit does
NOT cover (records consistent there; see the V9 REV-4 record).

**Countermodel disposition (the charged confirmation).** The r3b countermodel
(p = 2, (1,1)-Gauss σ at X, read pair (e★,h★) = (1,2), t★ = 0, g = 2,
Φ̂ = X²+4X+16) — SATISFIES finding 1's forced equation (`2 = 1²·2·1`), and DIES at
finding 2: `s★ = 1 ≠ 0 = g·(−t★·σ.h)` — no lawful σ′ exists over its data, so it
cannot be extended to the `ReadsOf` instances the V10-completed chain consumes.
The route consumes NO `SideReads` clause — in particular NOT clause (iii)'s `σ.R f`
rendering (the ⚠-fenced U31 seam): the fence is respected.  Numeric mirror:
`verification/v10_transition_check.py`.

moves_ref: §B2-DEF D.8 (TRANSPORT) UPWARD (MOVES 2520–2528, quoted above); D.2 (S5)
positions (MOVES 1960–1963); D.7 head (child valuation display).
deps: V0 (DefsV), S2 (childW), V4 (statement shape), HC2.Defs (IsReadLift).
ZERO axioms; zero sorry; `#print axioms` tail below.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves LeanUrat.MovesJ

section V10Helpers

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `w 1 = 0` (the V9 helper pattern). -/
private lemma v10_w_one (σ : Stage p F) : σ.w 1 = 0 := by
  have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h; omega

/-- `w (-x) = w x` (the V9 helper pattern). -/
private lemma v10_w_neg (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    σ.w (-x) = σ.w x := by
  have hn1 : σ.w (-1) = 0 := by
    have h := σ.hwmul (-1) (-1) (by norm_num) (by norm_num)
    rw [neg_mul_neg, one_mul, v10_w_one σ] at h; omega
  have h := σ.hwmul (-1) x (by norm_num) hx
  rw [neg_one_mul] at h
  rw [h, hn1, zero_add]

/-- `w (x^n) = n·w x` (the V9 helper pattern). -/
private lemma v10_w_pow (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    σ.w (x ^ n) = (n : ℤ) * σ.w x := by
  induction n with
  | zero => rw [pow_zero, v10_w_one σ]; push_cast; ring
  | succ k ih =>
      rw [pow_succ, σ.hwmul _ _ (pow_ne_zero k hx) hx, ih]
      push_cast; ring

/-- Finite-sum ultrametric lower bound (the V9 helper pattern). -/
private lemma v10_w_sum_ge (σ : Stage p F) (S : Finset ℕ) (f : ℕ → Polynomial ℤ_[p])
    (c : ℤ) :
    (∀ k ∈ S, f k ≠ 0 → c ≤ σ.w (f k)) → (∑ k ∈ S, f k) ≠ 0 →
    c ≤ σ.w (∑ k ∈ S, f k) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro _ hne; simp at hne
  | @insert a S' ha ih =>
      intro hterm hne
      rw [Finset.sum_insert ha] at hne ⊢
      by_cases hfa : f a = 0
      · rw [hfa, zero_add] at hne ⊢
        exact ih (fun k hk hk0 => hterm k (Finset.mem_insert_of_mem hk) hk0) hne
      · by_cases hS' : (∑ k ∈ S', f k) = 0
        · rw [hS', add_zero]
          exact hterm a (Finset.mem_insert_self a S') hfa
        · have h1 := hterm a (Finset.mem_insert_self a S') hfa
          have h2 := ih (fun k hk hk0 => hterm k (Finset.mem_insert_of_mem hk) hk0) hS'
          have h3 := σ.hwult (f a) (∑ k ∈ S', f k) hfa hS' hne
          omega

/-- `R (x^n) = (R x)^n` for `n ≥ 1` (iterated `hRmul`; pure `Stage` fact). -/
private lemma v10_R_pow (σ : Stage p F) (x : Polynomial ℤ_[p]) (hx : x ≠ 0) :
    ∀ n : ℕ, 1 ≤ n → σ.R (x ^ n) = (σ.R x) ^ n := by
  intro n
  induction n with
  | zero => omega
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · subst hk0; simp
      · rw [pow_succ, σ.hRmul _ _ (pow_ne_zero k hx) hx, ih hk1, pow_succ]

end V10Helpers

/-- **V10 finding 1 — the FORCED KEY-WEIGHT law** (the first stage of the (TRANSPORT)
transcription against the recorded transition): at a recorded steep read-lift
transition with `e★·g ≥ 2`, the child-stage laws force `h★ = e★²·g·σ.h`.

Mechanism: `Φ^{e★g} = Φ̂ − τ` is a 2-slot `Φ̂`-development, so `child_slotmin` pins
`σ′.w(Φ^{e★g}) = min(e★·σ.w τ, h★)` (attained), while `σ′.hwmul` + `σ′.hStretch`
(through `child_e`/`child_wPrev`) pin it to `e★g·e★σ.h`.  The read lift's slot
weights `σ.w(t_k) = h★(g−k)` make `e★·σ.w τ ≥ e★h★ + e★²(g−1)σ.h`, which strictly
exceeds `e★²gσ.h` under steepness — so the minimum is the key slot: `h★ = e★²gσ.h`. -/
theorem V10_forcedKeyWeight {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ σ' : Stage p F) (estar hstar : ℕ) (g : ℕ)
    (ψ : Polynomial ↥σ.K) (Φhat : Polynomial ℤ_[p])
    (hsteep : (estar : ℤ) * (σ.h : ℤ) < (hstar : ℤ))
    (hEG : 2 ≤ estar * g)
    (hlift : IsReadLift σ ψ g estar hstar Φhat)
    (hkey : σ'.Φ = Φhat) (hce : σ'.e = estar) (hcw : ∀ x, σ'.wPrev x = σ.w x)
    (hslot : IsSlotMinWeight σ'.w Φhat estar hstar σ.w) :
    (hstar : ℤ) = (estar : ℤ) * (estar : ℤ) * (g : ℤ) * (σ.h : ℤ) := by
  classical
  obtain ⟨tt, htt0, httk, hPhi⟩ := hlift
  set E : ℕ := estar with hE
  set G : ℕ := g with hG
  have hE1 : 1 ≤ E := by
    rcases Nat.eq_zero_or_pos E with h0 | h1
    · rw [h0] at hEG; omega
    · exact h1
  have hG1 : 1 ≤ G := by
    rcases Nat.eq_zero_or_pos G with h0 | h1
    · rw [h0] at hEG; omega
    · exact h1
  have hΦmon := σ.hmonic
  have hΦne : σ.Φ ≠ 0 := hΦmon.ne_zero
  have hD1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
  set D : ℕ := σ.Φ.natDegree with hD
  set τ : Polynomial ℤ_[p] := ∑ k ∈ Finset.range G, tt k * σ.Φ ^ (E * k) with hτdef
  -- degree bookkeeping (the V9_transSteepness block, transplanted)
  have hpowne : σ.Φ ^ (E * G) ≠ 0 := pow_ne_zero _ hΦne
  have hdegpow : (σ.Φ ^ (E * G)).degree = ((E * G * D : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hpowne, Polynomial.natDegree_pow]
  have hτdeg : τ.degree < ((E * G * D : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro k hk
    by_cases htk : tt k = 0
    · rw [htk, zero_mul, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · have hkG : k < G := Finset.mem_range.mp hk
      have hψk : ψ.coeff k ≠ 0 := fun h0 => htk (htt0 k h0)
      obtain ⟨-, htkC, -, -⟩ := httk k hkG hψk
      have htermne : tt k * σ.Φ ^ (E * k) ≠ 0 := mul_ne_zero htk (pow_ne_zero _ hΦne)
      refine (Polynomial.natDegree_lt_iff_degree_lt htermne).mp ?_
      rw [Polynomial.natDegree_mul htk (pow_ne_zero _ hΦne), Polynomial.natDegree_pow]
      have httdeg : (tt k).natDegree < D := Polynomial.natDegree_lt_natDegree htk htkC
      have h1 : E * k + 1 ≤ E * G := by
        have hEk : E * k + 1 ≤ E * (k + 1) := by
          rw [Nat.mul_succ]
          exact Nat.add_le_add_left hE1 (E * k)
        exact le_trans hEk (Nat.mul_le_mul_left E hkG)
      have hb : D + E * k * D ≤ E * G * D := by
        have h2 : (E * k + 1) * D ≤ (E * G) * D := Nat.mul_le_mul_right D h1
        calc D + E * k * D = (E * k + 1) * D := by ring
          _ ≤ E * G * D := h2
      exact lt_of_lt_of_le (Nat.add_lt_add_right httdeg _) hb
  have hΦhatdeg : Φhat.degree = ((E * G * D : ℕ) : WithBot ℕ) := by
    rw [hPhi,
      Polynomial.degree_add_eq_left_of_degree_lt (by rw [hdegpow]; exact hτdeg), hdegpow]
  -- `Φ ∈ C_{Φ̂}` (non-corner: `E·G ≥ 2`)
  have hinC : inC σ'.Φ σ.Φ := by
    show σ.Φ.degree < σ'.Φ.degree
    rw [hkey, hΦhatdeg, Polynomial.degree_eq_natDegree hΦne, ← hD]
    have hlt : D < E * G * D := by
      have h2 : 2 * D ≤ E * G * D := Nat.mul_le_mul_right D hEG
      omega
    exact_mod_cast hlt
  -- (1) the hwmul + hStretch value of `Φ^{E·G}` at σ′
  have hwPhi' : σ'.w σ.Φ = (E : ℤ) * (σ.h : ℤ) := by
    rw [σ'.hStretch σ.Φ hΦne hinC, hcw, σ.hwΦ, hce]
  have hwpowval : σ'.w (σ.Φ ^ (E * G)) = ((E * G : ℕ) : ℤ) * ((E : ℤ) * (σ.h : ℤ)) := by
    rw [v10_w_pow σ' σ.Φ hΦne (E * G), hwPhi']
  -- (2) the child_slotmin value of `Φ^{E·G}` through the 2-slot development `Φ̂ − τ`
  set B2 : ℕ → Polynomial ℤ_[p] := fun j => if j = 0 then -τ else if j = 1 then 1 else 0
    with hB2
  have hB20 : B2 0 = -τ := by simp [hB2]
  have hB21 : B2 1 = 1 := by simp [hB2]
  have hdev2 : IsDevelopment Φhat (σ.Φ ^ (E * G)) B2 2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simp only [hB2]
      split_ifs with h1 h2
      · rw [Polynomial.degree_neg, hΦhatdeg]
        exact hτdeg
      · rw [Polynomial.degree_one, hΦhatdeg]
        have : (0 : ℕ) < E * G * D := by positivity
        exact_mod_cast this
      · rw [Polynomial.degree_zero, hΦhatdeg]
        exact WithBot.bot_lt_coe _
    · intro j hj
      have hj0 : j ≠ 0 := by omega
      have hj1 : j ≠ 1 := by omega
      simp only [hB2, if_neg hj0, if_neg hj1]
    · rw [Finset.sum_range_succ, Finset.sum_range_one, hB20, hB21, hPhi]
      ring
  obtain ⟨hlow2, j₀, hj₀2, hj₀ne, hj₀eq⟩ := hslot (σ.Φ ^ (E * G)) B2 2 hpowne hdev2
  -- the τ-slot weight bound: `σ.w τ ≥ h★ + E(G−1)σ.h` (read-lift weights + steepness)
  have hτbound : τ ≠ 0 → (hstar : ℤ) + (E : ℤ) * ((G : ℤ) - 1) * (σ.h : ℤ) ≤ σ.w τ := by
    intro hτne
    refine v10_w_sum_ge σ (Finset.range G) _ _ ?_ (by rw [← hτdef]; exact hτne)
    intro k hk htkne
    have hkG : k < G := Finset.mem_range.mp hk
    have htk : tt k ≠ 0 := fun h0 => htkne (by rw [h0, zero_mul])
    have hψk : ψ.coeff k ≠ 0 := fun h0 => htk (htt0 k h0)
    obtain ⟨-, -, htkw, -⟩ := httk k hkG hψk
    rw [σ.hwmul _ _ htk (pow_ne_zero _ hΦne), htkw, v10_w_pow σ σ.Φ hΦne (E * k), σ.hwΦ]
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    have hkg1 : (k : ℤ) ≤ (G : ℤ) - 1 := by
      have : (k : ℤ) < (G : ℤ) := by exact_mod_cast hkG
      omega
    -- `h★(G−k) + Ek·σ.h ≥ h★ + E(G−1)σ.h  ⟺  (G−1−k)(h★ − Eσ.h) ≥ 0`
    have hfac : (0 : ℤ) ≤ ((G : ℤ) - 1 - (k : ℤ)) * ((hstar : ℤ) - (E : ℤ) * (σ.h : ℤ)) := by
      apply mul_nonneg <;> [omega; linarith [hsteep]]
    push_cast
    nlinarith [hfac]
  -- resolve the attained slot
  interval_cases j₀
  · -- attained at the τ-slot: contradiction with steepness
    exfalso
    have hτne : τ ≠ 0 := by
      intro h0
      apply hj₀ne
      rw [hB20, h0, neg_zero]
    have hval : σ'.w (σ.Φ ^ (E * G)) = (E : ℤ) * σ.w τ := by
      have hthis : σ'.w (σ.Φ ^ (E * G))
          = (E : ℤ) * σ.w (B2 0) + ((0 : ℕ) : ℤ) * (hstar : ℤ) := hj₀eq
      rw [hB20, v10_w_neg σ τ hτne] at hthis
      rw [hthis]
      push_cast; ring
    rw [hwpowval] at hval
    have hb := hτbound hτne
    have hE0 : (0 : ℤ) < (E : ℤ) := by exact_mod_cast hE1
    have hG0 : (1 : ℤ) ≤ (G : ℤ) := by exact_mod_cast hG1
    -- `E·G·E·σ.h = E·σ.w τ ≥ E·h★ + E²(G−1)σ.h  ⟹  E·σ.h ≥ h★` — against steepness
    have hscaled : (E : ℤ) * ((hstar : ℤ) + (E : ℤ) * ((G : ℤ) - 1) * (σ.h : ℤ))
        ≤ (E : ℤ) * σ.w τ := by
      exact mul_le_mul_of_nonneg_left hb (le_of_lt hE0)
    push_cast at hval
    nlinarith [hval, hscaled, hsteep, hE0, hG0]
  · -- attained at the key slot: `E·G·E·σ.h = h★` — the forced key weight
    have hval : σ'.w (σ.Φ ^ (E * G)) = (E : ℤ) * σ.w 1 + (1 : ℤ) * (hstar : ℤ) := by
      have hthis : σ'.w (σ.Φ ^ (E * G))
          = (E : ℤ) * σ.w (B2 1) + ((1 : ℕ) : ℤ) * (hstar : ℤ) := hj₀eq
      rw [hB21] at hthis
      rw [hthis]
      push_cast; ring
    rw [hwpowval, v10_w_one σ] at hval
    push_cast at hval ⊢
    linarith [hval]

/-- **V10 finding 2 — the recorded read-transition is INCOMPATIBLE at `e★·g ≥ 2`**:
adding the recorded Bézout ties (`σ′.s = s★`, `σ′.t = t★`, HistoryCoherent's clauses)
to finding 1's data yields `False`.

Mechanism: finding 1 forces `e★ = 1` (coprimality), `t★ = 0` (the P2 pin),
`s★ = 1` (Bézout), `h★ = g·σ.h`, `g ≥ 2`.  Then `σ′.R Φ̂ = T(σ′.s) = T 1` (hRΦ)
while `Φ̂ = Φ^g + τ` with `σ′.w(Φ^g) = g·σ.h = h★ < σ′.w τ`, so `hRlt` + `hRmul` +
`hS5′` (position `−t★·σ.w Φ = 0`) give `σ′.R Φ̂ = C(c^g)·T 0` — a monomial at
position 0.  `T 1 ≠ C(c^g)` in `↥σ′.K[z^{±1}]`. -/
theorem V10_readTransition_incompatible {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] (σ σ' : Stage p F) (estar hstar : ℕ) (sstar tstar : ℤ) (g : ℕ)
    (ψ : Polynomial ↥σ.K) (Φhat : Polynomial ℤ_[p])
    (hsteep : (estar : ℤ) * (σ.h : ℤ) < (hstar : ℤ))
    (hEG : 2 ≤ estar * g)
    (hcop : Nat.gcd estar hstar = 1)
    (hbez : (estar : ℤ) * sstar + (hstar : ℤ) * tstar = 1)
    (he1t : estar = 1 → tstar = 0)
    (hψ0 : ψ.coeff 0 ≠ 0)
    (hlift : IsReadLift σ ψ g estar hstar Φhat)
    (hkey : σ'.Φ = Φhat) (hce : σ'.e = estar) (hcw : ∀ x, σ'.wPrev x = σ.w x)
    (hslot : IsSlotMinWeight σ'.w Φhat estar hstar σ.w)
    (hs_tie : σ'.s = sstar) (ht_tie : σ'.t = tstar) : False := by
  classical
  -- finding 1
  have hkw := V10_forcedKeyWeight σ σ' estar hstar g ψ Φhat hsteep hEG hlift hkey hce hcw hslot
  -- `e★ = 1` from coprimality
  have hE1 : estar = 1 := by
    have hdvd : (estar : ℤ) ∣ (hstar : ℤ) := ⟨(estar : ℤ) * (g : ℤ) * (σ.h : ℤ), by linarith [hkw]⟩
    have hdvdN : estar ∣ hstar := Int.ofNat_dvd.mp (by exact_mod_cast hdvd)
    have : estar ∣ Nat.gcd estar hstar := Nat.dvd_gcd dvd_rfl hdvdN
    rw [hcop] at this
    exact Nat.dvd_one.mp this
  have hT0 : tstar = 0 := he1t hE1
  have hS1 : sstar = 1 := by
    rw [hE1, hT0] at hbez; push_cast at hbez; linarith
  have hG2 : 2 ≤ g := by rw [hE1, one_mul] at hEG; exact hEG
  -- `h★ = g·σ.h` (ℤ)
  have hkw1 : (hstar : ℤ) = (g : ℤ) * (σ.h : ℤ) := by
    rw [hE1] at hkw; push_cast at hkw; linarith
  -- unpack the lift
  obtain ⟨tt, htt0, httk, hPhi⟩ := hlift
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hD1 : 1 ≤ σ.Φ.natDegree := σ.hdeg
  set τ : Polynomial ℤ_[p] := ∑ k ∈ Finset.range g, tt k * σ.Φ ^ (estar * k) with hτdef
  -- degrees (re-derived; the finding-1 block is private to its proof)
  have hg1 : 1 ≤ g := by omega
  have hpowne : σ.Φ ^ (estar * g) ≠ 0 := pow_ne_zero _ hΦne
  have hdegpow : (σ.Φ ^ (estar * g)).degree
      = ((estar * g * σ.Φ.natDegree : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hpowne, Polynomial.natDegree_pow]
  have hτdeg : τ.degree < ((estar * g * σ.Φ.natDegree : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro k hk
    by_cases htk : tt k = 0
    · rw [htk, zero_mul, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · have hkG : k < g := Finset.mem_range.mp hk
      have hψk : ψ.coeff k ≠ 0 := fun h0 => htk (htt0 k h0)
      obtain ⟨-, htkC, -, -⟩ := httk k hkG hψk
      have htermne : tt k * σ.Φ ^ (estar * k) ≠ 0 := mul_ne_zero htk (pow_ne_zero _ hΦne)
      refine (Polynomial.natDegree_lt_iff_degree_lt htermne).mp ?_
      rw [Polynomial.natDegree_mul htk (pow_ne_zero _ hΦne), Polynomial.natDegree_pow]
      have httdeg : (tt k).natDegree < σ.Φ.natDegree :=
        Polynomial.natDegree_lt_natDegree htk htkC
      have h1 : estar * k + 1 ≤ estar * g := by
        have hEk : estar * k + 1 ≤ estar * (k + 1) := by
          rw [Nat.mul_succ]
          have hE1' : 1 ≤ estar := by rw [hE1]
          exact Nat.add_le_add_left hE1' (estar * k)
        exact le_trans hEk (Nat.mul_le_mul_left estar hkG)
      have hb : σ.Φ.natDegree + estar * k * σ.Φ.natDegree
          ≤ estar * g * σ.Φ.natDegree := by
        have h2 : (estar * k + 1) * σ.Φ.natDegree ≤ (estar * g) * σ.Φ.natDegree :=
          Nat.mul_le_mul_right σ.Φ.natDegree h1
        calc σ.Φ.natDegree + estar * k * σ.Φ.natDegree
            = (estar * k + 1) * σ.Φ.natDegree := by ring
          _ ≤ estar * g * σ.Φ.natDegree := h2
      exact lt_of_lt_of_le (Nat.add_lt_add_right httdeg _) hb
  have hΦhatdeg : Φhat.degree = ((estar * g * σ.Φ.natDegree : ℕ) : WithBot ℕ) := by
    rw [hPhi,
      Polynomial.degree_add_eq_left_of_degree_lt (by rw [hdegpow]; exact hτdeg), hdegpow]
  have hinCΦ : inC σ'.Φ σ.Φ := by
    show σ.Φ.degree < σ'.Φ.degree
    rw [hkey, hΦhatdeg, Polynomial.degree_eq_natDegree hΦne]
    have hlt : σ.Φ.natDegree < estar * g * σ.Φ.natDegree := by
      have h2 : 2 * σ.Φ.natDegree ≤ estar * g * σ.Φ.natDegree :=
        Nat.mul_le_mul_right σ.Φ.natDegree hEG
      omega
    exact_mod_cast hlt
  -- σ′-weights: `σ′.w(Φ^g) = g·σ.h = h★`
  have hwPhi' : σ'.w σ.Φ = (σ.h : ℤ) := by
    rw [σ'.hStretch σ.Φ hΦne hinCΦ, hcw, σ.hwΦ, hce, hE1]; push_cast; ring
  have hwpowg : σ'.w (σ.Φ ^ (estar * g)) = (g : ℤ) * (σ.h : ℤ) := by
    rw [v10_w_pow σ' σ.Φ hΦne (estar * g), hwPhi', hE1]; push_cast; ring
  -- the S5′ digit of `Φ` at the forced position `−t★·σ.w Φ = 0`
  obtain ⟨cΦ, hcΦ⟩ := σ'.hS5 σ.Φ hΦne hinCΦ
  have hRΦ0 : σ'.R σ.Φ = LaurentPolynomial.C (cΦ : ↥σ'.K) := by
    rw [hcΦ, ht_tie, hT0]
    simp
  -- `σ′.R (Φ^{e★g}) = C(cΦ^{e★g})`
  have hRpow : σ'.R (σ.Φ ^ (estar * g))
      = LaurentPolynomial.C ((cΦ : ↥σ'.K) ^ (estar * g)) := by
    rw [v10_R_pow σ' σ.Φ hΦne (estar * g) (by omega), hRΦ0, ← map_pow]
  -- `σ′.R Φ̂ = C(cΦ^{e★g})`, by `hRlt` through the deep τ-slot (or directly at τ = 0)
  have hRhat : σ'.R Φhat = LaurentPolynomial.C ((cΦ : ↥σ'.K) ^ (estar * g)) := by
    by_cases hτ0 : τ = 0
    · rw [hPhi, hτ0, add_zero]
      exact hRpow
    · have hinCτ : inC σ'.Φ τ := by
        show τ.degree < σ'.Φ.degree
        rw [hkey, hΦhatdeg]; exact hτdeg
      have hwτ : σ'.w τ = σ.w τ := by
        rw [σ'.hStretch τ hτ0 hinCτ, hcw, hce, hE1]; push_cast; ring
      -- the τ weight bound at `e★ = 1`: `σ.w τ ≥ h★ + (g−1)σ.h > h★`
      have hτbound : (hstar : ℤ) + ((g : ℤ) - 1) * (σ.h : ℤ) ≤ σ.w τ := by
        refine v10_w_sum_ge σ (Finset.range g) _ _ ?_ (by rw [← hτdef]; exact hτ0)
        intro k hk htkne
        have hkG : k < g := Finset.mem_range.mp hk
        have htk : tt k ≠ 0 := fun h0 => htkne (by rw [h0, zero_mul])
        have hψk : ψ.coeff k ≠ 0 := fun h0 => htk (htt0 k h0)
        obtain ⟨-, -, htkw, -⟩ := httk k hkG hψk
        rw [σ.hwmul _ _ htk (pow_ne_zero _ hΦne), htkw,
          v10_w_pow σ σ.Φ hΦne (estar * k), σ.hwΦ, hE1]
        have hkg1 : (k : ℤ) ≤ (g : ℤ) - 1 := by
          have : (k : ℤ) < (g : ℤ) := by exact_mod_cast hkG
          omega
        have hfac : (0 : ℤ)
            ≤ ((g : ℤ) - 1 - (k : ℤ)) * ((hstar : ℤ) - (σ.h : ℤ)) := by
          apply mul_nonneg
          · omega
          · rw [hE1] at hsteep; push_cast at hsteep; linarith
        push_cast
        nlinarith [hfac]
      have hlt : σ'.w (σ.Φ ^ (estar * g)) < σ'.w τ := by
        rw [hwpowg, hwτ]
        have hσh1 : (1 : ℤ) ≤ (σ.h : ℤ) := by exact_mod_cast σ.hh
        have hg2 : (2 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hG2
        nlinarith [hτbound, hkw1]
      have hne' : σ.Φ ^ (estar * g) + τ ≠ 0 := by
        rw [← hPhi, ← hkey]
        exact σ'.hmonic.ne_zero
      have := σ'.hRlt (σ.Φ ^ (estar * g)) τ hpowne hτ0 hne' hlt
      rw [hPhi, this]
      exact hRpow
  -- the clash: `T 1 = C (cΦ^{e★g})`
  have hRhat' : σ'.R σ'.Φ = LaurentPolynomial.T (1 : ℤ) := by
    rw [σ'.hRΦ, hs_tie, hS1]
  rw [hkey, hRhat] at hRhat'
  -- coefficient extraction at position 1
  have h1 : (LaurentPolynomial.C ((cΦ : ↥σ'.K) ^ (estar * g)) : LaurentPolynomial ↥σ'.K)
      = LaurentPolynomial.C ((cΦ : ↥σ'.K) ^ (estar * g)) * LaurentPolynomial.T (0 : ℤ) := by
    simp
  have h2 : (LaurentPolynomial.T (1 : ℤ) : LaurentPolynomial ↥σ'.K)
      = LaurentPolynomial.C (1 : ↥σ'.K) * LaurentPolynomial.T (1 : ℤ) := by
    rw [map_one, one_mul]
  rw [h1, h2, ← LaurentPolynomial.single_eq_C_mul_T,
    ← LaurentPolynomial.single_eq_C_mul_T] at hRhat'
  have h' : (Finsupp.single (0 : ℤ) ((cΦ : ↥σ'.K) ^ (estar * g)))
      = Finsupp.single (1 : ℤ) (1 : ↥σ'.K) := hRhat'
  have hc := DFunLike.congr_fun h' 1
  rw [Finsupp.single_apply, Finsupp.single_apply, if_pos rfl,
    if_neg (by norm_num : ¬ (0 : ℤ) = 1)] at hc
  exact one_ne_zero hc.symm

/-- **Unit V10 — the (TRANSPORT)-upward FORCED-WINDOW clause at the ReadFrame**
(the charged statement, over the proved `V2_readFrame` carrier with V4's landing
data + the recorded transition, on the non-corner perimeter `e★·g ≥ 2`): the vertex
coefficient is nonzero and its regrade weight equals its stretched frame weight —
`wV(B μ) = e★·σ.w(B μ)`, the bottom-window law, R3b's exact residue
(`V9_wvEqStretch_of_bottomSlot`'s hypothesis, `V9_bottomSlot_of_wvEqStretch`'s
conclusion).

⚠ **PROVED VACUOUSLY** — via `V10_readTransition_incompatible`: the recorded
transition hypotheses are contradictory on this perimeter (the header's finding 2).
Never cite this theorem as machine-checked transport mathematics; its content is
the INCONSISTENCY FINDING, and the honest transport awaits the child-keying repair
(named sign-off item; header).  The boundary caveats `t★ = 1` and
`h★ − e★σ.h = 1` are handled by emptiness: finding 1 forces `t★ = 0` here. -/
theorem V10_transportWindow {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (hσ : StageCoreL σ)
    (estar hstar : ℕ) (sstar tstar : ℤ)
    (hrp : ReadPair σ estar hstar sstar tstar)
    (V : ReadFrame σ estar hstar sstar tstar)
    (ψ : Polynomial ↥σ.K) (g : ℕ) (hdeg : ψ.natDegree = g) (hmon : ψ.Monic)
    (hirr : Irreducible ψ) (hne : ψ ≠ Polynomial.X)
    (Φhat : Polynomial ℤ_[p]) (hlift : IsReadLift σ ψ g estar hstar Φhat)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ)
    (Ranch : Polynomial ↥σ.K)
    (hanch : HasAnchorK (V.D.Rv f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N)
    (hNμ : μ < N)
    -- THE RECORDED TRANSITION (the (TRANSPORT)-upward actual-data carrier;
    -- supplied at V9 from `HistoryCoherent`'s non-recentering leg)
    (σ' : Stage p F)
    (hkey : σ'.Φ = Φhat) (hce : σ'.e = estar) (hcw : ∀ x, σ'.wPrev x = σ.w x)
    (hslot : IsSlotMinWeight σ'.w Φhat estar hstar σ.w)
    (hs_tie : σ'.s = sstar) (ht_tie : σ'.t = tstar)
    -- the NON-CORNER perimeter (`e★·g = 1` is the R3c corner, not covered)
    (hEG : 2 ≤ estar * g) :
    B μ ≠ 0 ∧ childW σ σ.Φ estar hstar (B μ) = (estar : ℤ) * σ.w (B μ) := by
  obtain ⟨he1, hh1, hcop, hbez, he1t, hsteep⟩ := hrp
  -- `ψ.coeff 0 ≠ 0` from irreducibility + `ψ ≠ X`
  have hψ0 : ψ.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := Polynomial.X_dvd_iff.mpr h0
    rcases hirr.isUnit_or_isUnit hu with hX | hUnit
    · exact Polynomial.not_isUnit_X hX
    · obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.mp hUnit
      apply hne
      have hψX : ψ = Polynomial.C c * Polynomial.X := by rw [hu, ← hc.2]; ring
      have hlc : c = 1 := by
        have := hmon
        rw [hψX] at this
        have hlead : (Polynomial.C c * Polynomial.X).leadingCoeff = c := by
          rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
            Polynomial.leadingCoeff_X, mul_one]
        rw [Polynomial.Monic, hlead] at this
        exact this
      rw [hψX, hlc, map_one, one_mul]
  exact (V10_readTransition_incompatible σ σ' estar hstar sstar tstar g ψ Φhat
    hsteep hEG hcop hbez he1t hψ0 hlift hkey hce hcw hslot hs_tie ht_tie).elim

end LeanUrat.HC1

#print axioms LeanUrat.HC1.V10_forcedKeyWeight
#print axioms LeanUrat.HC1.V10_readTransition_incompatible
#print axioms LeanUrat.HC1.V10_transportWindow
