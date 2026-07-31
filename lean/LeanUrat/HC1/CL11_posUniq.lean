/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# HC1.CL11_posUniq — 𝔽_p[x] positional uniqueness (BP5 CL-11, REVISION-2 statement)

**Unit CL-11** (blueprint `lean/notes/BRIDGE_BP5_CLEANUP_2026-07-30.md` §4;
REVISION 2 finding 1 — degeneracy hypotheses ADDED; risks R-1/R-2). **GATED on
CL-10's clean outcome** (countermodel-first: the NCL probe must complete before any
prover works this unit).

**Informal statement (over any field `K₀`, applied at `K₀ = 𝔽_p` by CL-12).** For a
NONEMPTY finite set of DISTINCT slot vectors `s : Fin (K+1) → ℕ`, bounded by
`slotBound` at inner levels and CONSTANT (`= b`) at the top, monic `Φ̄_r` with
`0 < deg Φ̄₀` and the exact key-degree ratio law
`deg Φ̄_{r+1} = slotBound r · deg Φ̄_r`, and nonzero digits `d̄_s` with
`deg d̄_s < deg Φ̄₀`:  `Σ_s d̄_s · ∏_r Φ̄_r^{s r} ≠ 0`.

**DEGENERACY RECORD (the REVISION-2 repair, verbatim from the blueprint).** As
previously sketched the EMPTY slot-vector set satisfied every hypothesis and gave
`Σ = 0` — the statement was FALSE. NONEMPTY is the load-bearing addition;
`0 < deg Φ̄₀` is then derivable (a nonzero digit with `deg d̄ < deg Φ̄₀` forces
`deg Φ̄₀ ≥ 1`) but is stated explicitly because the div/mod induction consumes it
directly — this writer keeps it as a hypothesis (the permitted downgrade to a
derived `have` is left to the prover, WITH a note; the nonemptiness may NEVER be
dropped). Both discharge for free at the CL-12 site: survivor set nonempty (`y ≠ 0`,
`l_min` attained) and `(T.stg 0).hdeg : 1 ≤ Φ.natDegree` + monic-map degree
preservation (CL-27(b) `red_monic_deg`).

**Proof sketch.** Strong induction on the highest inner level where the slot
vectors differ; Euclidean uniqueness of div/mod by `Φ̄_r^{(min slot at level r)}`
with the degree bound `Σ_{r'<r} slotBound·deg < deg Φ̄_r` (the mixed-radix carry
bound — T9(b)'s numeric kernel shape re-used, here in degree form:
`CL11a_prefix_degree_lt` below); base case: no inner level left, one term (the slot
vectors were distinct), `d̄ ≠ 0` times a monic power ≠ 0. The top slot is CONSTANT
`b`, so `Φ̄_K^b` factors out (monic over a field, ≠ 0) — the induction runs on inner
levels only.

**E-phase resolutions recorded.**
* "finite set of DISTINCT slot vectors ... digits d̄_s" is transcribed as a
  `Finset (Fin (K+1) → ℕ)` (distinctness = Finset elementhood) with a digit
  function `d` read on `S`; all hypotheses quantify over `s ∈ S`.
* Degree forms: `degree` (WithBot) for the digit bound — matching CL-27(b)'s
  `red_digLift_deg`, the discharging lemma — and `natDegree` for the ratio law and
  `0 < deg Φ̄₀`, matching `red_ratio_law`/`red_monic_deg`. **R-2 fence: the digit
  bound has NO lower-degree companion and must never gain one** (reduced digits may
  drop degree).
* SPLIT RULE (CL-11a/b, exercised): the div/mod DEGREE sublemma is emitted here as
  the standalone `CL11a_prefix_degree_lt` (the carry bound: any digit-cleared prefix
  stays strictly below the next place-value degree); the main statement is
  `CL11_posUniq`.

**PROVER NOTES (as-built, 2026-07-30).**
* CL-10 gate: COMPLETED first (BLOCKED as sealed-predicted; mechanism survey in
  `CL10_nclProbe.lean`).
* `CL11_posUniq` is proved by DEGREE SEPARATION rather than the sketched explicit
  div/mod peeling — same mathematics, shorter formal path: each term
  `d̄_s·∏Φ̄^{s r}` lies in the x-degree window `[V(s), V(s) + deg Φ̄₀)` where
  `V(s) = Σ_r s_r·deg Φ̄_r`; the exact ratio law makes `deg Φ̄₀ ∣ V(s)` and the
  mixed-radix kernel (T9(b)'s `mr_inj_top` shape, copied private below) makes
  `V` injective on bounded slot vectors, so the windows are pairwise disjoint and
  the maximal-degree term's leading coefficient survives in the sum. This is
  exactly the Euclidean div/mod uniqueness read off at the leading coefficient —
  the carry bound `CL11a_prefix_degree_lt` (fenced) is proved standalone and is
  the same telescope in prefix form.
* `hdeg0` is consumed by the radix-positivity leg (`1 ≤ D_r` for every place);
  `hSne` by the max-term extraction AND radix positivity (`slotBound r ≥ 1` is
  read off any member's bound row). The nonemptiness is load-bearing exactly as
  the degeneracy record demands.

**Deps.** CL-10 (gate; must complete first). Tower-independent — imports Mathlib
only. difficulty: hard-fable. Size: ~150. hyp: none.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial

/-! ## Private ℕ-extended plumbing (T9(b)'s kernel shape, tower-free) -/

/-- The ℕ-extended place values `deg Φ̄_m` (junk 1 beyond K). -/
private noncomputable def cl11_DD {K₀ : Type*} [Field K₀] (K : ℕ)
    (Φ : Fin (K + 1) → Polynomial K₀) : ℕ → ℕ :=
  fun m => if hm : m < K + 1 then (Φ ⟨m, hm⟩).natDegree else 1

/-- The ℕ-extended digit radices (junk 1 beyond K). -/
private def cl11_cb (K : ℕ) (slotBound : Fin K → ℕ) : ℕ → ℕ :=
  fun m => if hm : m < K then slotBound ⟨m, hm⟩ else 1

/-- The ℕ-extension of a slot vector (junk 0 beyond K). -/
private def cl11_ext (K : ℕ) (z : Fin (K + 1) → ℕ) : ℕ → ℕ :=
  fun m => if hm : m < K + 1 then z ⟨m, hm⟩ else 0

private lemma cl11_DD_zero {K₀ : Type*} [Field K₀] (K : ℕ)
    (Φ : Fin (K + 1) → Polynomial K₀) : cl11_DD K Φ 0 = (Φ 0).natDegree := by
  rw [cl11_DD, dif_pos (Nat.succ_pos K)]
  rw [show (⟨0, Nat.succ_pos K⟩ : Fin (K + 1)) = 0 from Fin.ext (by simp)]

private lemma cl11_DD_succ {K₀ : Type*} [Field K₀] (K : ℕ)
    (slotBound : Fin K → ℕ) (Φ : Fin (K + 1) → Polynomial K₀)
    (hratio : ∀ r : Fin K, (Φ r.succ).natDegree = slotBound r * (Φ r.castSucc).natDegree)
    (m : ℕ) (hm : m < K) :
    cl11_DD K Φ (m + 1) = slotBound ⟨m, hm⟩ * cl11_DD K Φ m := by
  have hm1 : m < K + 1 := Nat.lt_succ_of_lt hm
  have hm2 : m + 1 < K + 1 := by omega
  rw [cl11_DD, cl11_DD, dif_pos hm1, dif_pos hm2]
  have hsc : (⟨m, hm⟩ : Fin K).succ = (⟨m + 1, hm2⟩ : Fin (K + 1)) := Fin.ext rfl
  have hcs : (⟨m, hm⟩ : Fin K).castSucc = (⟨m, hm1⟩ : Fin (K + 1)) := Fin.ext rfl
  have := hratio ⟨m, hm⟩
  rw [hsc, hcs] at this
  exact this

private lemma cl11_DD_pos {K₀ : Type*} [Field K₀] (K : ℕ)
    (slotBound : Fin K → ℕ) (Φ : Fin (K + 1) → Polynomial K₀)
    (hdeg0 : 0 < (Φ 0).natDegree)
    (hratio : ∀ r : Fin K, (Φ r.succ).natDegree = slotBound r * (Φ r.castSucc).natDegree)
    (hcb : ∀ r : Fin K, 1 ≤ slotBound r) :
    ∀ m, 1 ≤ cl11_DD K Φ m := by
  intro m
  induction m with
  | zero => rw [cl11_DD_zero]; omega
  | succ m ih =>
    by_cases hm : m < K
    · rw [cl11_DD_succ K slotBound Φ hratio m hm]
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by have := hcb ⟨m, hm⟩; omega) (by omega))
    · by_cases hm1 : m + 1 < K + 1
      · omega
      · rw [cl11_DD, dif_neg hm1]

private lemma cl11_step {K₀ : Type*} [Field K₀] (K : ℕ)
    (slotBound : Fin K → ℕ) (Φ : Fin (K + 1) → Polynomial K₀)
    (hratio : ∀ r : Fin K, (Φ r.succ).natDegree = slotBound r * (Φ r.castSucc).natDegree) :
    ∀ m, m < K → cl11_cb K slotBound m * cl11_DD K Φ m ≤ cl11_DD K Φ (m + 1) := by
  intro m hm
  rw [cl11_cb, dif_pos hm, cl11_DD_succ K slotBound Φ hratio m hm]

/-- The degree-place divisibility chain: `deg Φ̄₀ ∣ deg Φ̄_m` (from the exact ratio law). -/
private lemma cl11_DD_dvd {K₀ : Type*} [Field K₀] (K : ℕ)
    (slotBound : Fin K → ℕ) (Φ : Fin (K + 1) → Polynomial K₀)
    (hratio : ∀ r : Fin K, (Φ r.succ).natDegree = slotBound r * (Φ r.castSucc).natDegree) :
    ∀ m, m < K + 1 → cl11_DD K Φ 0 ∣ cl11_DD K Φ m := by
  intro m
  induction m with
  | zero => intro _; exact dvd_refl _
  | succ m ih =>
    intro hm1
    have hm : m < K := by omega
    rw [cl11_DD_succ K slotBound Φ hratio m hm]
    exact (ih (by omega)).mul_left _

/-- Fin-sum to ℕ-range-sum conversion for the mixed-radix value. -/
private lemma cl11_conv {K₀ : Type*} [Field K₀] (K : ℕ)
    (Φ : Fin (K + 1) → Polynomial K₀) (z : Fin (K + 1) → ℕ) :
    (∑ r, z r * (Φ r).natDegree)
      = ∑ m ∈ Finset.range (K + 1), cl11_ext K z m * cl11_DD K Φ m := by
  rw [← Fin.sum_univ_eq_sum_range (fun m => cl11_ext K z m * cl11_DD K Φ m) (K + 1)]
  apply Finset.sum_congr rfl
  intro i _
  rw [cl11_ext, cl11_DD]
  simp only [dif_pos i.isLt, Fin.eta]

/-- Prefix-restricted conversion (the CL-11a filter shape). -/
private lemma cl11_conv_lt {K₀ : Type*} [Field K₀] (K : ℕ)
    (Φ : Fin (K + 1) → Polynomial K₀) (z : Fin (K + 1) → ℕ) (n : Fin (K + 1)) :
    (∑ r ∈ Finset.univ.filter (fun r : Fin (K + 1) => (r : ℕ) < (n : ℕ)),
        z r * (Φ r).natDegree)
      = ∑ m ∈ Finset.range (n : ℕ), cl11_ext K z m * cl11_DD K Φ m := by
  have h2 : ∑ m ∈ Finset.range (n : ℕ), cl11_ext K z m * cl11_DD K Φ m
      = ∑ m ∈ Finset.range (K + 1),
          (if m < (n : ℕ) then cl11_ext K z m * cl11_DD K Φ m else 0) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun m _ => rfl)
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; have := n.isLt; exact ⟨by omega, h⟩
    · rintro ⟨-, h⟩; exact h
  rw [Finset.sum_filter, h2,
    ← Fin.sum_univ_eq_sum_range
      (fun m => if m < (n : ℕ) then cl11_ext K z m * cl11_DD K Φ m else 0) (K + 1)]
  apply Finset.sum_congr rfl
  intro r _
  simp only [cl11_ext, cl11_DD, dif_pos r.isLt, Fin.eta]

/-- The e-augmented prefix bound: `e + Σ_{r<m} a_r·D_r < D_m` for `e < D_0`,
digits below the radices, and the step law (the mixed-radix carry telescope). -/
private lemma cl11_prefix_bound (D c a : ℕ → ℕ) (e : ℕ) (he : e < D 0) :
    ∀ m, (∀ r, r < m → a r < c r) → (∀ r, r < m → c r * D r ≤ D (r + 1)) →
      e + ∑ r ∈ Finset.range m, a r * D r < D m := by
  intro m
  induction m with
  | zero =>
      intro _ _
      simpa using he
  | succ m ih =>
      intro hb hstep
      rw [Finset.sum_range_succ, ← add_assoc]
      have hpre : e + ∑ r ∈ Finset.range m, a r * D r < D m :=
        ih (fun r hr => hb r (Nat.lt_succ_of_lt hr)) (fun r hr => hstep r (Nat.lt_succ_of_lt hr))
      have ham : a m + 1 ≤ c m := hb m (Nat.lt_succ_self m)
      calc e + ∑ r ∈ Finset.range m, a r * D r + a m * D m
          < D m + a m * D m := by omega
        _ = (a m + 1) * D m := by ring
        _ ≤ c m * D m := by gcongr
        _ ≤ D (m + 1) := hstep m (Nat.lt_succ_self m)

/-- Prefix bound (T9(b)'s private `mr_prefix_lt`, copied — the `e = 0` telescope). -/
private lemma cl11_mr_prefix_lt (D c a : ℕ → ℕ) (hD : ∀ r, 1 ≤ D r) :
    ∀ n, (∀ r, r < n → a r < c r) → (∀ r, r < n → c r * D r ≤ D (r + 1)) →
      ∑ r ∈ Finset.range n, a r * D r < D n := by
  intro n hb hstep
  have := cl11_prefix_bound D c a 0 (hD 0) n hb hstep
  omega

/-- Injectivity on a fully-bounded prefix (T9(b)'s private `mr_inj_prefix`, copied). -/
private lemma cl11_mr_inj_prefix (D c a b : ℕ → ℕ) (hD : ∀ r, 1 ≤ D r) :
    ∀ n, (∀ r, r < n → a r < c r) → (∀ r, r < n → b r < c r) →
      (∀ r, r < n → c r * D r ≤ D (r + 1)) →
      ∑ r ∈ Finset.range n, a r * D r = ∑ r ∈ Finset.range n, b r * D r →
      ∀ r, r < n → a r = b r := by
  intro n
  induction n with
  | zero => intro _ _ _ _ r hr; exact absurd hr (Nat.not_lt_zero r)
  | succ m ih =>
      intro ha hb hstep hsum r hr
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
      have hpa : ∑ r ∈ Finset.range m, a r * D r < D m :=
        cl11_mr_prefix_lt D c a hD m (fun r hr => ha r (Nat.lt_succ_of_lt hr))
          (fun r hr => hstep r (Nat.lt_succ_of_lt hr))
      have hpb : ∑ r ∈ Finset.range m, b r * D r < D m :=
        cl11_mr_prefix_lt D c b hD m (fun r hr => hb r (Nat.lt_succ_of_lt hr))
          (fun r hr => hstep r (Nat.lt_succ_of_lt hr))
      set Pa := ∑ r ∈ Finset.range m, a r * D r with hPadef
      set Pb := ∑ r ∈ Finset.range m, b r * D r with hPbdef
      have hDm : 0 < D m := hD m
      have hPaeq : (Pa + a m * D m) % D m = Pa := by
        rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpa
      have hPbeq : (Pb + b m * D m) % D m = Pb := by
        rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpb
      have hmod : Pa = Pb := by rw [← hPaeq, ← hPbeq, hsum]
      have hamm : a m * D m = b m * D m := by omega
      have ham : a m = b m := Nat.eq_of_mul_eq_mul_right hDm hamm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
      · exact ih (fun r hr => ha r (Nat.lt_succ_of_lt hr))
              (fun r hr => hb r (Nat.lt_succ_of_lt hr))
              (fun r hr => hstep r (Nat.lt_succ_of_lt hr)) hmod r hlt
      · subst heq; exact ham

/-- Top-peel injectivity (T9(b)'s private `mr_inj_top`, copied): positions `0..n-1`
bounded, position `n` free; equal base-`D` value forces agreement on all of `0..n`. -/
private lemma cl11_mr_inj_top (D c a b : ℕ → ℕ) (hD : ∀ r, 1 ≤ D r) (n : ℕ)
    (ha : ∀ r, r < n → a r < c r) (hb : ∀ r, r < n → b r < c r)
    (hstep : ∀ r, r < n → c r * D r ≤ D (r + 1))
    (hsum : ∑ r ∈ Finset.range (n + 1), a r * D r = ∑ r ∈ Finset.range (n + 1), b r * D r) :
    ∀ r, r ≤ n → a r = b r := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
  have hpa : ∑ r ∈ Finset.range n, a r * D r < D n := cl11_mr_prefix_lt D c a hD n ha hstep
  have hpb : ∑ r ∈ Finset.range n, b r * D r < D n := cl11_mr_prefix_lt D c b hD n hb hstep
  set Pa := ∑ r ∈ Finset.range n, a r * D r with hPadef
  set Pb := ∑ r ∈ Finset.range n, b r * D r with hPbdef
  have hDn : 0 < D n := hD n
  have hPaeq : (Pa + a n * D n) % D n = Pa := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpa
  have hPbeq : (Pb + b n * D n) % D n = Pb := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hpb
  have hmod : Pa = Pb := by rw [← hPaeq, ← hPbeq, hsum]
  have hamm : a n * D n = b n * D n := by omega
  have han : a n = b n := Nat.eq_of_mul_eq_mul_right hDn hamm
  intro r hr
  rcases hr.lt_or_eq with hlt | heq
  · exact cl11_mr_inj_prefix D c a b hD n ha hb hstep hmod r hlt
  · subst heq; exact han

/-- **CL-11a** (the div/mod degree sublemma — the mixed-radix carry bound in degree
form): a digit-cleared prefix `d · ∏_{r < n} Φ̄_r^{s r}` (digit degree below
`deg Φ̄₀`, inner slots below their bounds) has degree strictly below `deg Φ̄_n`.
Junk-true at `d = 0` (`degree ⊥`). Telescopes on the exact ratio law:
`deg Φ̄₀ + Σ_{r<n} (slotBound r − 1)·deg Φ̄_r = deg Φ̄_n`. -/
theorem CL11a_prefix_degree_lt {K₀ : Type*} [Field K₀] (K : ℕ)
    (slotBound : Fin K → ℕ) (Φ : Fin (K + 1) → Polynomial K₀)
    (hmonic : ∀ r, (Φ r).Monic)
    (hdeg0 : 0 < (Φ 0).natDegree)
    (hratio : ∀ r : Fin K, (Φ r.succ).natDegree = slotBound r * (Φ r.castSucc).natDegree)
    (s : Fin (K + 1) → ℕ) (n : Fin (K + 1))
    (hbound : ∀ r : Fin K, (r : ℕ) < (n : ℕ) → s r.castSucc < slotBound r)
    (d : Polynomial K₀) (hddeg : d.degree < (Φ 0).degree) :
    (d * ∏ r ∈ Finset.univ.filter (fun r : Fin (K + 1) => (r : ℕ) < (n : ℕ)),
        (Φ r) ^ (s r)).degree < (Φ n).degree := by
  classical
  by_cases hd0 : d = 0
  · rw [hd0, zero_mul, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr fun h => (hmonic n).ne_zero (Polynomial.degree_eq_bot.mp h)
  · have hPmonic : (∏ r ∈ Finset.univ.filter (fun r : Fin (K + 1) => (r : ℕ) < (n : ℕ)),
        (Φ r) ^ (s r)).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun r _ => (hmonic r).pow _)
    have hPne : (∏ r ∈ Finset.univ.filter (fun r : Fin (K + 1) => (r : ℕ) < (n : ℕ)),
        (Φ r) ^ (s r)) ≠ 0 := hPmonic.ne_zero
    have hdlt : d.natDegree < (Φ 0).natDegree := Polynomial.natDegree_lt_natDegree hd0 hddeg
    -- the ℕ-level degree computation
    have hPdeg : (∏ r ∈ Finset.univ.filter (fun r : Fin (K + 1) => (r : ℕ) < (n : ℕ)),
          (Φ r) ^ (s r)).natDegree
        = ∑ r ∈ Finset.univ.filter (fun r : Fin (K + 1) => (r : ℕ) < (n : ℕ)),
            s r * (Φ r).natDegree := by
      rw [Polynomial.natDegree_prod _ _ (fun r _ => pow_ne_zero _ (hmonic r).ne_zero)]
      apply Finset.sum_congr rfl
      intro r _
      rw [Polynomial.natDegree_pow, mul_comm]
    -- the ℕ-level carry bound
    have hkey : d.natDegree
        + ∑ r ∈ Finset.univ.filter (fun r : Fin (K + 1) => (r : ℕ) < (n : ℕ)),
            s r * (Φ r).natDegree
        < (Φ n).natDegree := by
      rw [cl11_conv_lt K Φ s n]
      have hbnd : ∀ r, r < (n : ℕ) → cl11_ext K s r < cl11_cb K slotBound r := by
        intro r hr
        have hrK : r < K := lt_of_lt_of_le hr (Nat.lt_succ_iff.mp n.isLt)
        have hr1 : r < K + 1 := by omega
        rw [cl11_ext, cl11_cb, dif_pos hr1, dif_pos hrK]
        have hcs : (⟨r, hrK⟩ : Fin K).castSucc = (⟨r, hr1⟩ : Fin (K + 1)) := Fin.ext rfl
        have := hbound ⟨r, hrK⟩ hr
        rwa [hcs] at this
      have hstp : ∀ r, r < (n : ℕ) → cl11_cb K slotBound r * cl11_DD K Φ r ≤ cl11_DD K Φ (r + 1) := by
        intro r hr
        exact cl11_step K slotBound Φ hratio r (lt_of_lt_of_le hr (Nat.lt_succ_iff.mp n.isLt))
      have he0 : d.natDegree < cl11_DD K Φ 0 := by rw [cl11_DD_zero]; exact hdlt
      have hDn : cl11_DD K Φ (n : ℕ) = (Φ n).natDegree := by
        rw [cl11_DD, dif_pos n.isLt]
      rw [← hDn]
      exact cl11_prefix_bound (cl11_DD K Φ) (cl11_cb K slotBound) (cl11_ext K s)
        d.natDegree he0 (n : ℕ) hbnd hstp
    -- assemble in WithBot
    rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hd0,
        Polynomial.degree_eq_natDegree hPne, Polynomial.degree_eq_natDegree (hmonic n).ne_zero,
        hPdeg, ← Nat.cast_add]
    exact_mod_cast hkey

/-- **CL-11 (REVISION-2 statement)**: positional uniqueness of the mixed-radix
Φ̄-development with bounded nonzero digits, over any field. NONEMPTY + `0 < deg Φ̄₀`
are the REVISION-2 degeneracy hypotheses (see the file header; nonemptiness may
never be dropped). Applied by CL-12 at `K₀ = 𝔽_p` with `Φ̄ = red ∘ Φ`,
`slotBound = T.slotBound`, `d̄ = red ∘ digLift`, hypotheses discharged by CL-27(b). -/
theorem CL11_posUniq {K₀ : Type*} [Field K₀] (K : ℕ)
    (slotBound : Fin K → ℕ) (Φ : Fin (K + 1) → Polynomial K₀) (b : ℕ)
    (hmonic : ∀ r, (Φ r).Monic)
    (hdeg0 : 0 < (Φ 0).natDegree)
    (hratio : ∀ r : Fin K, (Φ r.succ).natDegree = slotBound r * (Φ r.castSucc).natDegree)
    (S : Finset (Fin (K + 1) → ℕ)) (hSne : S.Nonempty)
    (hbound : ∀ s ∈ S, ∀ r : Fin K, s r.castSucc < slotBound r)
    (htop : ∀ s ∈ S, s (Fin.last K) = b)
    (d : (Fin (K + 1) → ℕ) → Polynomial K₀)
    (hd : ∀ s ∈ S, d s ≠ 0)
    (hddeg : ∀ s ∈ S, (d s).degree < (Φ 0).degree) :
    ∑ s ∈ S, d s * ∏ r, (Φ r) ^ (s r) ≠ 0 := by
  classical
  -- radix positivity from any member's bound row (the nonemptiness is load-bearing)
  obtain ⟨s₁, hs₁⟩ := id hSne
  have hcb : ∀ r : Fin K, 1 ≤ slotBound r := by
    intro r
    have := hbound s₁ hs₁ r
    omega
  have hD1 : ∀ m, 1 ≤ cl11_DD K Φ m := cl11_DD_pos K slotBound Φ hdeg0 hratio hcb
  have hstepD : ∀ m, m < K → cl11_cb K slotBound m * cl11_DD K Φ m ≤ cl11_DD K Φ (m + 1) :=
    cl11_step K slotBound Φ hratio
  -- per-term facts
  have hProdMonic : ∀ s : Fin (K + 1) → ℕ, (∏ r, (Φ r) ^ (s r)).Monic := by
    intro s
    exact Polynomial.monic_prod_of_monic _ _ (fun r _ => (hmonic r).pow _)
  have htne : ∀ s ∈ S, d s * ∏ r, (Φ r) ^ (s r) ≠ 0 := by
    intro s hs
    exact mul_ne_zero (hd s hs) (hProdMonic s).ne_zero
  have htdeg : ∀ s ∈ S, (d s * ∏ r, (Φ r) ^ (s r)).natDegree
      = (d s).natDegree + ∑ r, s r * (Φ r).natDegree := by
    intro s hs
    rw [Polynomial.natDegree_mul (hd s hs) (hProdMonic s).ne_zero,
        Polynomial.natDegree_prod _ _ (fun r _ => pow_ne_zero _ (hmonic r).ne_zero)]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [Polynomial.natDegree_pow, mul_comm]
  -- mixed-radix injectivity of the window base V(s) = Σ s_r·deg Φ̄_r on S
  have hVinj : ∀ s ∈ S, ∀ s' ∈ S,
      (∑ r, s r * (Φ r).natDegree) = (∑ r, s' r * (Φ r).natDegree) → s = s' := by
    intro s hs s' hs' hsum
    rw [cl11_conv K Φ s, cl11_conv K Φ s'] at hsum
    have hb1 : ∀ m, m < K → cl11_ext K s m < cl11_cb K slotBound m := by
      intro m hm
      have hm1 : m < K + 1 := by omega
      rw [cl11_ext, cl11_cb, dif_pos hm1, dif_pos hm]
      have hcs : (⟨m, hm⟩ : Fin K).castSucc = (⟨m, hm1⟩ : Fin (K + 1)) := Fin.ext rfl
      have := hbound s hs ⟨m, hm⟩
      rwa [hcs] at this
    have hb2 : ∀ m, m < K → cl11_ext K s' m < cl11_cb K slotBound m := by
      intro m hm
      have hm1 : m < K + 1 := by omega
      rw [cl11_ext, cl11_cb, dif_pos hm1, dif_pos hm]
      have hcs : (⟨m, hm⟩ : Fin K).castSucc = (⟨m, hm1⟩ : Fin (K + 1)) := Fin.ext rfl
      have := hbound s' hs' ⟨m, hm⟩
      rwa [hcs] at this
    have hall := cl11_mr_inj_top (cl11_DD K Φ) (cl11_cb K slotBound)
      (cl11_ext K s) (cl11_ext K s') hD1 K hb1 hb2 hstepD hsum
    funext i
    have hi := hall i.val (Nat.lt_succ_iff.mp i.isLt)
    rw [cl11_ext, cl11_ext, dif_pos i.isLt, dif_pos i.isLt] at hi
    simpa [Fin.eta] using hi
  -- window disjointness: distinct members have distinct TERM degrees
  have hD0dvd : ∀ z : Fin (K + 1) → ℕ, cl11_DD K Φ 0 ∣ (∑ r, z r * (Φ r).natDegree) := by
    intro z
    rw [cl11_conv K Φ z]
    apply Finset.dvd_sum
    intro m hm
    exact ((cl11_DD_dvd K slotBound Φ hratio m (Finset.mem_range.mp hm)).mul_left _)
  have hdeginj : ∀ s ∈ S, ∀ s' ∈ S,
      (d s * ∏ r, (Φ r) ^ (s r)).natDegree = (d s' * ∏ r, (Φ r) ^ (s' r)).natDegree → s = s' := by
    intro s hs s' hs' he
    rw [htdeg s hs, htdeg s' hs'] at he
    obtain ⟨a, ha⟩ := hD0dvd s
    obtain ⟨a', ha'⟩ := hD0dvd s'
    have hds : (d s).natDegree < cl11_DD K Φ 0 := by
      rw [cl11_DD_zero]
      exact Polynomial.natDegree_lt_natDegree (hd s hs) (hddeg s hs)
    have hds' : (d s').natDegree < cl11_DD K Φ 0 := by
      rw [cl11_DD_zero]
      exact Polynomial.natDegree_lt_natDegree (hd s' hs') (hddeg s' hs')
    rw [ha, ha'] at he
    -- Euclidean uniqueness at radix `deg Φ̄₀`
    have h1 : ((d s).natDegree + cl11_DD K Φ 0 * a) % cl11_DD K Φ 0 = (d s).natDegree := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hds
    have h2 : ((d s').natDegree + cl11_DD K Φ 0 * a') % cl11_DD K Φ 0 = (d s').natDegree := by
      rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hds'
    have hmod : (d s).natDegree = (d s').natDegree := by rw [← h1, ← h2, he]
    have hVeq : (∑ r, s r * (Φ r).natDegree) = (∑ r, s' r * (Φ r).natDegree) := by
      rw [ha, ha']
      omega
    exact hVinj s hs s' hs' hVeq
  -- extract the maximal-degree term; its leading coefficient survives the sum
  obtain ⟨s₀, hs₀, hmax⟩ := S.exists_max_image (fun s => (d s * ∏ r, (Φ r) ^ (s r)).natDegree) hSne
  intro h0
  have hco : (∑ s ∈ S, d s * ∏ r, (Φ r) ^ (s r)).coeff
      ((d s₀ * ∏ r, (Φ r) ^ (s₀ r)).natDegree)
      = (d s₀ * ∏ r, (Φ r) ^ (s₀ r)).leadingCoeff := by
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single s₀]
    · rfl
    · intro s hs hne
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hle := hmax s hs
      have hnee : (d s * ∏ r, (Φ r) ^ (s r)).natDegree
          ≠ (d s₀ * ∏ r, (Φ r) ^ (s₀ r)).natDegree :=
        fun h => hne (hdeginj s hs s₀ hs₀ h)
      omega
    · intro h; exact absurd hs₀ h
  rw [h0, Polynomial.coeff_zero] at hco
  exact (Polynomial.leadingCoeff_ne_zero.mpr (htne s₀ hs₀)) hco.symm

end LeanUrat.HC1

#print axioms LeanUrat.HC1.CL11a_prefix_degree_lt
#print axioms LeanUrat.HC1.CL11_posUniq
