/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsCar
import LeanUrat.HC1.ScratchC6
import LeanUrat.HC1.CL04_addrDichotomy
import LeanUrat.HC1.CL13_lvlDet
import LeanUrat.HC1.T11_attainDichotomy
import LeanUrat.HC1.C2_TYPa
import LeanUrat.Moves.L3_liftMonic
import LeanUrat.Moves.L5_realCofin_R3
import LeanUrat.Moves.L5_realDomination_R3

/-!
# HC1.C6_alphabetCard — the alphabet cardinality + the fullness DICHOTOMY (G-4)

moves_ref: MOVES 2160–2165 "= [F_{k+1} : F_p] … EXACTLY WHEN every height in γ's
slot tree is attainable … and STRICTLY SMALLER at shallow heights". deps: T7, T8;
ScratchC6 (the 2026-07-28 certificates), CL04 (the address vocabulary); Moves
`L5_realCofin_R3`, `L5_realDomination_R3` (clean). BOTH directions (audit G-4):
fullness ⟺ every slot height is attainable, and STRICTLY SMALLER on the failing
side. Still no unconditional fullness claim (the rev-D¹¹c fix stands).
difficulty: medium. hyp: `cleanThreshold` on conjunct 2 (below).

## ITEM-18 EXECUTION RECORD (statement repair, Asvin sign-off 2026-07-31)

**Pre-repair statement REFUTED-AS-STATED.** The ScratchC6 certificates
(2026-07-28, all Lean-core) show conjunct 2's RHS is a THEOREM
(`C6_conjunct2_rhs_always`: level-set membership forces attainability — the D-10
typing quantified the note's condition over the WRONG index set), so the fenced
iff asserted UNCONDITIONAL fullness (`C6_forces_unconditional_fullness`) —
refuted at shallow heights by the COMPILED countermodel `Tshallow` (CL-01a/b/c;
`CL01c_shallowTower.lean`: singleton level set at (0,0), card 𝔸 ≤ 3 < 4 = card F₄).
Per the BP5 §3.1 LANDING GATE the compiled negation
(`C6_pre_repair_refuted_at_Tshallow`) lands ATOMICALLY with this repair,
retargeted at the frozen `C6_stmt_pre_repair` copy (both in CL01c's file).

**The repair (ratified: the "independence/clean-threshold hypothesis on
conjunct 2").** Conjunct 2 gains the named hypothesis `Tower.cleanThreshold b γ`
(below): every ℤ-ALIGNED ADDRESS of block b is attainable at γ — the note's own
fullness condition (MOVES 2160–2165), typed over addresses per ScratchC6's D-10
diagnosis, in CL-04's display-(3) vocabulary. WEAKEST-FORM rationale: by the
CL-04 probe record (PROBE REPORT, outcome (b)) fullness is believed EQUIVALENT
to this condition (the CI-1 equidistribution theorem + CI-2/CI-3 line fullness/
independence + CI-4 card bridge), so no strictly weaker non-trivial hypothesis
can restore the iff; the D.9(b) clean-threshold regime (each stage's slot
heights clear its D.9(b) bound) is the displayed sufficient INSTANCE, hence the
hypothesis name. Conjuncts 1 and 3 are unconditional and remain unguarded.

**Proof status.** Conjunct 1 PROVED (T7, via `C6_conjunct1_closable`).
Conjunct 2 → PROVED (`C6_conjunct2_rhs_always`). Conjunct 3 PROVED
(`C6_conjunct3_hyp_false`: the hypothesis is refutable, ex falso). Conjunct 2 ⟸
(cleanThreshold → fullness) was THE remaining honest sorry — exactly CL-05's
specified obligation (CL04 PROBE REPORT: CI-1 slot-class equidistribution,
CI-2 digit-line structure, CI-3 slot-min orthogonality/joint independence,
CI-4 `card F_{K+1} = |F_Q|^{∏g}`); the pre-repair FALSE form survives as the
frozen copy + compiled negation in CL01c.

## CL-05 EXECUTION RECORD (B2D hard-hole unit, 2026-08-02) — SORRY CLOSED

**Numerics first** (`verification/cl05_fullness_probe.py`, sealed predictions in
header before first run, exit 0): P1 the fiber-count kernel at 2000 on-lattice
targets incl. recentering rows and gcd-defect strata (`h_r` sharing factors with
earlier `e_j`); P2 152 deep assemblies `N = ∏g ∧ |FQ|^N = card K_top`; P3 163
shallow instances where hclean FAILS and the count drops — the guard is
non-vacuous.

**The proof, per the CI-1..CI-4 spec** (private `cl05_*` apparatus below):
* CI-1 = `cl05_walk_inj` + `cl05_walk_fiber` (the genuinely new counting: the
  unit walk `u ↦ Σ u_r·h_r·∏_{j>r}e_j` is a COMPLETE residue system mod
  `D₀ = ∏ e_r` — triangular peel on `gcd(e_r,h_r) = 1` only — so every fiber of
  the box walk is a free `v`-shift of size exactly `∏ G_r`), instantiated at the
  tower by `cl05_slotBound_eq` (`slotBound r = e_r·G_r`; at recenterings BOTH
  sides collapse via `IsRecentering`'s `σ.e = 1` — the parent-`e ≥ 2` recentering
  that would break the count is ILLEGAL, which is exactly why the identity holds)
  + `cl05_kappa_c`/`cl05_strAux_Iio` (the `D₀·κ_r = h_r·∏_{j>r}e_j` denominator
  clearing) + `cl05_aligned_card`.
* CI-2+CI-3 = `cl05_alphabet_card_pow`: the composite is an injective additive
  hom (injectivity = the PROVED `CL13_lvlDet`, LVL-DET) onto the alphabet
  (surjectivity = `T11_attainDichotomy`), so `card 𝔸 = |FQ|^N` — no separate
  line/independence legs needed.
* CI-4 = `cl05_cardK_step`/`cl05_cardK_chain` (`child_field` + the CU1
  `card_adjoin_root` argument, replicated verbatim as `cl05_card_adjoin_root`;
  recenterings keep `K`).
* Assembly: `cl05_levelSet_card` (level set ≃ aligned addresses; hclean
  discharges attainability) + base pin `K₀ = FQ`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves
open scoped Classical

/-- **The card-K bridge (F-2, sign-off event 2026-07-28, blueprint §9.2):** every
stage residue field of a tower has p-power cardinality, `Nat.card ↥K = p^d` with
`d = [K : F_p] ≥ 1` — the bridge C6's conjuncts 2–3 consume. Underivable before the
F-2 char pin `Tower.hcharF : CharP F p` (round-2 fleet kernel: `Stage p F` carries
no characteristic tie, so `Nat.card K` was a power of char F, junk off char p); the
pin records the note's own setting (F_{k+1}/F_p extensions, MOVES 2148–2165). -/
theorem C6_cardK_bridge {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (k : Fin (T.K + 1)) :
    ∃ d : ℕ, 1 ≤ d ∧ Nat.card ↥(T.stg k).K = p ^ d := by
  haveI : CharP F p := T.hcharF
  haveI : Fintype ↥(T.stg k).K := Fintype.ofFinite _
  haveI : CharP ↥(T.stg k).K p :=
    RingHom.charP (T.stg k).K.subtype (T.stg k).K.subtype.injective p
  obtain ⟨n, -, hn⟩ := FiniteField.card ↥(T.stg k).K p
  exact ⟨(n : ℕ), n.2, by rw [Nat.card_eq_fintype_card, hn]⟩

/-- **The clean-threshold (full-attainability) hypothesis** (item-18 repair,
2026-07-31): every ℤ-aligned address of block `b` is attainable at height `γ` —
the note's fullness condition (MOVES 2160–2165 "EXACTLY WHEN every height in γ's
slot tree is attainable"), typed over ADDRESSES per the D-10 correction, in
CL-04's display-(3) vocabulary. The D.9(b) clean-threshold regime is the
displayed sufficient instance; per the CL-04 probe record, fullness is believed
EQUIVALENT to this condition, making it the weakest truth-restoring hypothesis
for conjunct 2. -/
def Tower.cleanThreshold {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) : Prop :=
  ∀ s : T.Addr b, T.aligned γ s → T.attainable γ s

/-! ## The CL-05 apparatus (execution record in the module docstring; all private)

Part 1 — the counting core (CI-1's kernel): the walk `s ↦ Σ_r s_r·c_r` over the
box `∏_r [0, e_r·G_r)`, with suffix coefficients `c_r = h_r·∏_{j>r} e_j` and
`gcd(e_r, h_r) = 1`, has ALL fibers mod `D = ∏ e_r` of size exactly `∏_r G_r`. -/

/-- Injectivity of the unit walk: two sub-`e` tuples with `D`-congruent walks are
equal (top-down peel; only `gcd(e_r, h_r) = 1` is consumed). -/
private lemma cl05_walk_inj (K : ℕ) : ∀ (e h : Fin K → ℕ),
    (∀ r, 1 ≤ e r) → (∀ r, Nat.gcd (e r) (h r) = 1) →
    ∀ u u' : Fin K → ℕ, (∀ r, u r < e r) → (∀ r, u' r < e r) →
    ((∏ r, (e r : ℤ)) ∣
      ∑ r, ((u r : ℤ) - (u' r : ℤ)) * ((h r : ℤ) * ∏ j ∈ Finset.Ioi r, (e j : ℤ))) →
    u = u' := by
  induction K with
  | zero =>
    intro e h _ _ u u' _ _ _
    funext r
    exact r.elim0
  | succ K ih =>
    intro e h he hcop u u' hu hu' hdvd
    have hprod : (∏ r : Fin (K + 1), (e r : ℤ)) = (e 0 : ℤ) * ∏ i : Fin K, (e i.succ : ℤ) :=
      Fin.prod_univ_succ _
    have hsum : (∑ r : Fin (K + 1), ((u r : ℤ) - (u' r : ℤ)) *
          ((h r : ℤ) * ∏ j ∈ Finset.Ioi r, (e j : ℤ)))
        = ((u 0 : ℤ) - (u' 0 : ℤ)) * ((h 0 : ℤ) * ∏ i : Fin K, (e i.succ : ℤ))
          + ∑ i : Fin K, ((u i.succ : ℤ) - (u' i.succ : ℤ)) *
              ((h i.succ : ℤ) * ∏ j ∈ Finset.Ioi i, (e j.succ : ℤ)) := by
      rw [Fin.sum_univ_succ, Fin.prod_Ioi_zero]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.prod_Ioi_succ]
    rw [hsum, hprod] at hdvd
    have hD'pos : (0 : ℤ) < ∏ i : Fin K, (e i.succ : ℤ) :=
      Finset.prod_pos fun i _ => by exact_mod_cast he i.succ
    have htail_dvd : (∏ i : Fin K, (e i.succ : ℤ)) ∣
        ∑ i : Fin K, ((u i.succ : ℤ) - (u' i.succ : ℤ)) *
          ((h i.succ : ℤ) * ∏ j ∈ Finset.Ioi i, (e j.succ : ℤ)) := by
      have h1 : (∏ i : Fin K, (e i.succ : ℤ)) ∣
          ((u 0 : ℤ) - (u' 0 : ℤ)) * ((h 0 : ℤ) * ∏ i : Fin K, (e i.succ : ℤ)) :=
        ⟨((u 0 : ℤ) - (u' 0 : ℤ)) * (h 0 : ℤ), by ring⟩
      have h2 : (∏ i : Fin K, (e i.succ : ℤ)) ∣ (e 0 : ℤ) * ∏ i : Fin K, (e i.succ : ℤ) :=
        ⟨(e 0 : ℤ), mul_comm _ _⟩
      exact (dvd_add_right h1).mp (dvd_trans h2 hdvd)
    have htail : (fun i : Fin K => u i.succ) = fun i : Fin K => u' i.succ :=
      ih (fun i => e i.succ) (fun i => h i.succ) (fun i => he i.succ) (fun i => hcop i.succ)
        _ _ (fun i => hu i.succ) (fun i => hu' i.succ) htail_dvd
    have hzero : (∑ i : Fin K, ((u i.succ : ℤ) - (u' i.succ : ℤ)) *
        ((h i.succ : ℤ) * ∏ j ∈ Finset.Ioi i, (e j.succ : ℤ))) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi : u i.succ = u' i.succ := congrFun htail i
      rw [hi, sub_self, zero_mul]
    rw [hzero, add_zero] at hdvd
    have hcancel : (e 0 : ℤ) ∣ ((u 0 : ℤ) - (u' 0 : ℤ)) * (h 0 : ℤ) := by
      have h3 : ((u 0 : ℤ) - (u' 0 : ℤ)) * ((h 0 : ℤ) * ∏ i : Fin K, (e i.succ : ℤ))
          = (((u 0 : ℤ) - (u' 0 : ℤ)) * (h 0 : ℤ)) * ∏ i : Fin K, (e i.succ : ℤ) := by ring
      rw [h3] at hdvd
      exact (mul_dvd_mul_iff_right hD'pos.ne').mp hdvd
    have hcp : IsCoprime ((e 0 : ℕ) : ℤ) ((h 0 : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact hcop 0
    have hdvd0 : (e 0 : ℤ) ∣ ((u 0 : ℤ) - (u' 0 : ℤ)) := hcp.dvd_of_dvd_mul_right hcancel
    have h0 : u 0 = u' 0 := by
      obtain ⟨k, hk⟩ := hdvd0
      have hb1 : ((u 0 : ℕ) : ℤ) < e 0 := by exact_mod_cast hu 0
      have hb2 : ((u' 0 : ℕ) : ℤ) < e 0 := by exact_mod_cast hu' 0
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have h1 : (e 0 : ℤ) * k ≤ (e 0 : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        omega
      · rw [hk0, mul_zero] at hk
        omega
      · have h1 : (e 0 : ℤ) * 1 ≤ (e 0 : ℤ) * k :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        omega
    funext r
    rcases Fin.eq_zero_or_eq_succ r with rfl | ⟨i, rfl⟩
    · exact h0
    · exact congrFun htail i

/-- **The CL-05 fiber count** (CI-1's kernel; sealed numerically by
`verification/cl05_fullness_probe.py` P1): over a box with bounds
`B r = e r * G r`, EVERY fiber of the walk mod `D = ∏ e` has exactly `∏ G`
elements — the unit part walks a complete residue system (`cl05_walk_inj` +
cardinality), the quotient part is a free shift. -/
private lemma cl05_walk_fiber (K : ℕ) (e h G B : Fin K → ℕ)
    (he : ∀ r, 1 ≤ e r) (hcop : ∀ r, Nat.gcd (e r) (h r) = 1)
    (hB : ∀ r, B r = e r * G r) (M : ℤ) :
    Nat.card {t : (r : Fin K) → Fin (B r) //
      ((∏ r, e r : ℕ) : ℤ) ∣
        M - ∑ r, ((t r : ℕ) : ℤ) * ((h r : ℤ) * ∏ j ∈ Finset.Ioi r, (e j : ℤ))} = ∏ r, G r := by
  classical
  set c : Fin K → ℤ := fun r => (h r : ℤ) * ∏ j ∈ Finset.Ioi r, (e j : ℤ) with hc
  set D : ℕ := ∏ r, e r with hD
  have hDpos : 0 < D := Finset.prod_pos fun r _ => he r
  haveI : NeZero D := ⟨hDpos.ne'⟩
  set U : ((r : Fin K) → Fin (e r)) → ZMod D :=
    fun u => ((∑ r, ((u r : ℕ) : ℤ) * c r : ℤ) : ZMod D) with hU
  have hUinj : Function.Injective U := by
    intro u u' huu
    simp only [hU] at huu
    have hmod : ((∑ r, ((u r : ℕ) : ℤ) * c r) : ℤ) ≡ (∑ r, ((u' r : ℕ) : ℤ) * c r) [ZMOD (D : ℕ)] :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mp huu
    have hdvd : ((D : ℕ) : ℤ) ∣
        (∑ r, ((u' r : ℕ) : ℤ) * c r) - ∑ r, ((u r : ℕ) : ℤ) * c r := hmod.dvd
    have hsub : ((∑ r, ((u' r : ℕ) : ℤ) * c r) - ∑ r, ((u r : ℕ) : ℤ) * c r)
        = ∑ r, (((u' r : ℕ) : ℤ) - ((u r : ℕ) : ℤ)) * c r := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hsub] at hdvd
    have hDD : ((D : ℕ) : ℤ) = ∏ r, (e r : ℤ) := by rw [hD]; push_cast; rfl
    rw [hDD] at hdvd
    have heq : (fun r => ((u' r : Fin (e r)) : ℕ)) = fun r => ((u r : Fin (e r)) : ℕ) :=
      cl05_walk_inj K e h he hcop _ _ (fun r => (u' r).2) (fun r => (u r).2) hdvd
    funext r
    exact Fin.ext (congrFun heq r).symm
  have hUbij : Function.Bijective U := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hUinj, ?_⟩
    rw [Fintype.card_pi, ZMod.card]
    simp only [Fintype.card_fin]
    exact hD.symm
  set Ueq : ((r : Fin K) → Fin (e r)) ≃ ZMod D := Equiv.ofBijective U hUbij with hUeq
  set J : ((r : Fin K) → Fin (G r)) → ZMod D :=
    fun v => ((∑ r, ((v r : ℕ) : ℤ) * ((e r : ℤ) * c r) : ℤ) : ZMod D) with hJ
  set m : ZMod D := ((M : ℤ) : ZMod D) with hm
  have hdivlt : ∀ (t : (r : Fin K) → Fin (B r)) (r : Fin K), (t r : ℕ) / e r < G r := by
    intro t r
    have h1 : (t r : ℕ) < e r * G r := hB r ▸ (t r).2
    rw [Nat.div_lt_iff_lt_mul (he r)]
    rwa [mul_comm] at h1
  have hkey2 : ∀ (u : (r : Fin K) → Fin (e r)) (v : (r : Fin K) → Fin (G r)),
      (((∑ r, (((u r : ℕ) + e r * (v r : ℕ) : ℕ) : ℤ) * c r : ℤ) : ZMod D)) = U u + J v := by
    intro u v
    have hsp : (∑ r, (((u r : ℕ) + e r * (v r : ℕ) : ℕ) : ℤ) * c r)
        = (∑ r, ((u r : ℕ) : ℤ) * c r) + ∑ r, ((v r : ℕ) : ℤ) * ((e r : ℤ) * c r) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      push_cast
      ring
    rw [hsp, Int.cast_add]
  have hkey : ∀ t : (r : Fin K) → Fin (B r),
      (((∑ r, ((t r : ℕ) : ℤ) * c r : ℤ) : ZMod D))
        = U (fun r => ⟨(t r : ℕ) % e r, Nat.mod_lt _ (he r)⟩)
          + J (fun r => ⟨(t r : ℕ) / e r, hdivlt t r⟩) := by
    intro t
    have hsp : (∑ r, ((t r : ℕ) : ℤ) * c r)
        = ∑ r, ((((t r : ℕ) % e r) + e r * ((t r : ℕ) / e r) : ℕ) : ℤ) * c r := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Nat.mod_add_div]
    rw [hsp]
    exact hkey2 (fun r => ⟨(t r : ℕ) % e r, Nat.mod_lt _ (he r)⟩)
      (fun r => ⟨(t r : ℕ) / e r, hdivlt t r⟩)
  have hEquiv : {t : (r : Fin K) → Fin (B r) //
      ((D : ℕ) : ℤ) ∣ M - ∑ r, ((t r : ℕ) : ℤ) * c r} ≃ ((r : Fin K) → Fin (G r)) := by
    refine ⟨fun s => fun r => ⟨(s.1 r : ℕ) / e r, hdivlt s.1 r⟩, fun v => ⟨fun r =>
      ⟨((Ueq.symm (m - J v)) r : ℕ) + e r * (v r : ℕ), ?_⟩, ?_⟩, ?_, ?_⟩
    · have h1 : ((Ueq.symm (m - J v)) r : ℕ) < e r := ((Ueq.symm (m - J v)) r).2
      calc ((Ueq.symm (m - J v)) r : ℕ) + e r * (v r : ℕ)
          < e r + e r * (v r : ℕ) := by omega
        _ = e r * ((v r : ℕ) + 1) := by ring
        _ ≤ e r * G r := Nat.mul_le_mul_left _ (v r).2
        _ = B r := (hB r).symm
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
      have hUv : U (Ueq.symm (m - J v)) = m - J v := Ueq.apply_symm_apply (m - J v)
      have hthis := hkey2 (Ueq.symm (m - J v)) v
      rw [hUv] at hthis
      rw [hthis, ← hm]
      ring
    · rintro ⟨t, hcond⟩
      apply Subtype.ext
      funext r
      apply Fin.ext
      show ((Ueq.symm (m - J _)) r : ℕ) + e r * ((t r : ℕ) / e r) = (t r : ℕ)
      have hcast : (((M - ∑ r, ((t r : ℕ) : ℤ) * c r : ℤ)) : ZMod D) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hcond
      rw [Int.cast_sub] at hcast
      have hsolve : (((∑ r, ((t r : ℕ) : ℤ) * c r : ℤ)) : ZMod D) = m :=
        (sub_eq_zero.mp hcast).symm
      have hk := hkey t
      rw [hsolve] at hk
      have hUsymm : Ueq.symm (m - J (fun r => ⟨(t r : ℕ) / e r, hdivlt t r⟩))
          = fun r => ⟨(t r : ℕ) % e r, Nat.mod_lt _ (he r)⟩ := by
        rw [Equiv.symm_apply_eq]
        have happ : Ueq (fun r => (⟨(t r : ℕ) % e r, Nat.mod_lt _ (he r)⟩ : Fin (e r)))
            = U (fun r => ⟨(t r : ℕ) % e r, Nat.mod_lt _ (he r)⟩) := rfl
        rw [happ, sub_eq_iff_eq_add]
        exact hk
      rw [hUsymm]
      exact Nat.mod_add_div _ _
    · intro v
      funext r
      apply Fin.ext
      show (((Ueq.symm (m - J v)) r : ℕ) + e r * (v r : ℕ)) / e r = (v r : ℕ)
      rw [Nat.add_mul_div_left _ _ (he r), Nat.div_eq_of_lt ((Ueq.symm (m - J v)) r).2, zero_add]
  calc Nat.card {t : (r : Fin K) → Fin (B r) //
      ((D : ℕ) : ℤ) ∣ M - ∑ r, ((t r : ℕ) : ℤ) * c r}
      = Nat.card ((r : Fin K) → Fin (G r)) := Nat.card_congr hEquiv
    _ = ∏ r, G r := by
        rw [Nat.card_pi]
        exact Finset.prod_congr rfl fun r _ => Nat.card_eq_fintype_card.trans (Fintype.card_fin _)

/-! Part 2 — tower data: per-move residue degree, the slot-bound law, the
residue-card chain (CI-4). -/

/-- The residue degree of one move: the increment's `g`, or 1 at a recentering. -/
private def cl05_moveDeg {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (r : Fin T.K) : ℕ :=
  match T.move r with
  | MoveWitness.inc _ g _ _ _ _ _ _ _ => g
  | MoveWitness.recenter _ _ _ _ => 1

section CL05

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

private lemma cl05_moveDeg_inc (T : Tower p F) (r : Fin T.K) {ψ g Φhat e' h' zbar hyp core core'}
    (hmv : T.move r = MoveWitness.inc ψ g Φhat e' h' zbar hyp core core') :
    cl05_moveDeg T r = g := by
  unfold cl05_moveDeg
  rw [hmv]

private lemma cl05_moveDeg_rec (T : Tower p F) (r : Fin T.K) {cc tt core core'}
    (hmv : T.move r = MoveWitness.recenter cc tt core core') :
    cl05_moveDeg T r = 1 := by
  unfold cl05_moveDeg
  rw [hmv]

/-- The slot-bound law `slotBound r = e_r · G_r` (increments: `child_key` degree;
recenterings: degree unchanged AND the parent `e = 1` — `IsRecentering.1`, which
is exactly what protects the fiber count from a dead slot eating a live `e`). -/
private lemma cl05_slotBound_eq (T : Tower p F) (r : Fin T.K) :
    T.slotBound r = (T.stg r.castSucc).e * cl05_moveDeg T r := by
  have hdpos : 0 < (T.stg r.castSucc).Φ.natDegree := (T.stg r.castSucc).hdeg
  cases hmv : T.move r with
  | inc ψ g Φhat e' h' zbar hyp core core' =>
    rw [cl05_moveDeg_inc T r hmv]
    have hkey := core.base.child_key
    have hdeg := (L3_liftMonic (T.stg r.castSucc) ψ g hyp.hg Φhat hyp.hlift).2
    rw [Tower.slotBound, hkey, hdeg, Nat.mul_div_cancel _ hdpos]
  | recenter cc tt core core' =>
    rw [cl05_moveDeg_rec T r hmv]
    obtain ⟨he1, _, _, htt, _, _, _, hΦ', _, _, _, _, _, _⟩ := core.base
    have hnd : (T.stg r.succ).Φ.natDegree = (T.stg r.castSucc).Φ.natDegree := by
      rw [hΦ']
      have hne1 : (T.stg r.castSucc).Φ - tt ≠ 0 := by
        rw [← hΦ']; exact (T.stg r.succ).hmonic.ne_zero
      have hne2 : (T.stg r.castSucc).Φ ≠ 0 := (T.stg r.castSucc).hmonic.ne_zero
      have hdegeq : ((T.stg r.castSucc).Φ - tt).degree = (T.stg r.castSucc).Φ.degree :=
        Polynomial.degree_sub_eq_left_of_degree_lt htt
      rw [Polynomial.degree_eq_natDegree hne1, Polynomial.degree_eq_natDegree hne2] at hdegeq
      exact_mod_cast hdegeq
    rw [Tower.slotBound, hnd, Nat.div_self hdpos, he1]

/-- Residue-field cardinality growth at one adjoined root (verbatim replication of
the PROVED `Scaffold/DictIII/CU1.card_adjoin_root`, private there — CI-4's kernel). -/
private theorem cl05_card_adjoin_root {K : Subfield F} {ψ : Polynomial ↥K}
    (hmon : ψ.Monic) (hirr : Irreducible ψ) {z : F}
    (hz : Polynomial.eval₂ K.subtype z ψ = 0) :
    Nat.card ↥(Subfield.closure (↑K ∪ {z})) = Nat.card ↥K ^ ψ.natDegree := by
  have haev : (Polynomial.aeval z) ψ = 0 := by
    rwa [Polynomial.aeval_def]
  have hint : IsIntegral ↥K z := ⟨ψ, hmon, haev⟩
  have hmin : minpoly ↥K z = ψ :=
    (minpoly.eq_of_irreducible_of_monic hirr haev hmon).symm
  have hfin : Module.finrank ↥K ↥(IntermediateField.adjoin ↥K {z})
      = ψ.natDegree := by
    rw [← hmin]
    exact IntermediateField.adjoin.finrank hint
  have hcard : Nat.card ↥(IntermediateField.adjoin ↥K {z})
      = Nat.card ↥K ^ ψ.natDegree := by
    rw [← hfin]
    exact Module.natCard_eq_pow_finrank
  have hrange : Set.range ⇑(algebraMap ↥K F) = (↑K : Set F) := Subtype.range_coe
  rw [← hcard]
  refine Nat.card_congr (Equiv.setCongr ?_)
  rw [← IntermediateField.coe_toSubfield, IntermediateField.adjoin_toSubfield, hrange]

/-- One-move residue-card law: `|K_{r+1}| = |K_r|^{G_r}` (D.6 growth at increments
via `child_field`; `K` unchanged at recenterings). -/
private lemma cl05_cardK_step (T : Tower p F) (r : Fin T.K) :
    Nat.card ↥(T.stg r.succ).K = Nat.card ↥(T.stg r.castSucc).K ^ cl05_moveDeg T r := by
  cases hmv : T.move r with
  | inc ψ g Φhat e' h' zbar hyp core core' =>
    rw [cl05_moveDeg_inc T r hmv]
    have hK : (T.stg r.succ).K = (T.stg r.castSucc).nextField zbar := core.base.child_field
    have hz : Polynomial.eval₂ (T.stg r.castSucc).K.subtype (zbar : F) ψ = 0 := by
      have h1 := hyp.hroot
      rw [Polynomial.aeval_def, Polynomial.eval₂_map] at h1
      rwa [show (algebraMap F F).comp (T.stg r.castSucc).K.subtype
          = (T.stg r.castSucc).K.subtype from RingHom.ext fun x => rfl] at h1
    rw [hK]
    have hcard := cl05_card_adjoin_root hyp.hmonic hyp.hirr hz
    rw [hyp.hdeg] at hcard
    exact hcard
  | recenter cc tt core core' =>
    rw [cl05_moveDeg_rec T r hmv, pow_one]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hK, _, _, _⟩ := core.base
    rw [hK]

/-- CI-4, the chain: `|K_top| = |K_0|^{∏ G_r}`. -/
private lemma cl05_cardK_chain (T : Tower p F) :
    Nat.card ↥(T.stg (Fin.last T.K)).K
      = Nat.card ↥(T.stg 0).K ^ ∏ r : Fin T.K, cl05_moveDeg T r := by
  have haux : ∀ m (hm : m < T.K + 1),
      Nat.card ↥(T.stg ⟨m, hm⟩).K
        = Nat.card ↥(T.stg 0).K ^ ∏ j ∈ Finset.range m,
            (if h : j < T.K then cl05_moveDeg T ⟨j, h⟩ else 1) := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [Finset.range_zero, Finset.prod_empty, pow_one]
      rfl
    | succ n ihn =>
      intro hm
      have hnK : n < T.K := by omega
      have hn1 : n < T.K + 1 := by omega
      have hstep := cl05_cardK_step T ⟨n, hnK⟩
      rw [Finset.prod_range_succ, dif_pos hnK, pow_mul, ← ihn hn1]
      exact hstep
  have hconv : (∏ r : Fin T.K, cl05_moveDeg T r)
      = ∏ j ∈ Finset.range T.K, (if h : j < T.K then cl05_moveDeg T ⟨j, h⟩ else 1) := by
    rw [← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_congr rfl fun r _ => by rw [dif_pos r.isLt]
  rw [hconv]
  exact haux T.K (Nat.lt_succ_self _)

/-! Part 3 — the height-lattice bookkeeping: strAux as an Iio-product, the
product split, and the `D₀·κ_r = c_r` identity. -/

private lemma cl05_strAux_Iio (T : Tower p F) : ∀ (v : ℕ) (hv : v < T.K),
    T.strAux v = ∏ j ∈ Finset.Iio (⟨v, hv⟩ : Fin T.K), (T.stg j.castSucc).e := by
  intro v
  induction v with
  | zero =>
    intro hv
    have hIio : Finset.Iio (⟨0, hv⟩ : Fin T.K) = ∅ := by
      ext j
      simp [Fin.lt_def]
    rw [hIio, Finset.prod_empty]
    rfl
  | succ n ihn =>
    intro hv
    have hn : n < T.K := by omega
    have hins : Finset.Iio (⟨n + 1, hv⟩ : Fin T.K)
        = insert (⟨n, hn⟩ : Fin T.K) (Finset.Iio (⟨n, hn⟩ : Fin T.K)) := by
      ext j
      simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def]
      constructor
      · intro hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
        · exact Or.inr hj'
        · exact Or.inl (Fin.ext hj')
      · rintro (rfl | hj)
        · exact Nat.lt_succ_self n
        · exact Nat.lt_succ_of_lt hj
    have hnotmem : (⟨n, hn⟩ : Fin T.K) ∉ Finset.Iio (⟨n, hn⟩ : Fin T.K) := by simp
    rw [hins, Finset.prod_insert hnotmem, ← ihn hn]
    have hn1 : n < T.K + 1 := by omega
    have hstep : T.strAux (n + 1) = T.strAux n * (T.stg ⟨n, hn1⟩).e := by
      have hh : T.strAux (n + 1)
          = T.strAux n * (if h : n < T.K + 1 then (T.stg ⟨n, h⟩).e else 1) := rfl
      rw [hh, dif_pos hn1]
    rw [hstep, mul_comm]
    rfl

private lemma cl05_prod_split {n : ℕ} (f : Fin n → ℕ) (r : Fin n) :
    (∏ j, f j) = (∏ j ∈ Finset.Iio r, f j) * f r * ∏ j ∈ Finset.Ioi r, f j := by
  have hnotmem : r ∉ Finset.Iio r ∪ Finset.Ioi r := by simp
  have hdisj : Disjoint (Finset.Iio r) (Finset.Ioi r) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_Iio] at ha
    rw [Finset.mem_Ioi] at ha'
    exact absurd (ha.trans ha') (lt_irrefl _)
  have huniv : (Finset.univ : Finset (Fin n)) = insert r (Finset.Iio r ∪ Finset.Ioi r) := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi, true_iff]
    rcases lt_trichotomy j r with hj | hj | hj
    · exact Or.inr (Or.inl hj)
    · exact Or.inl hj
    · exact Or.inr (Or.inr hj)
  rw [huniv, Finset.prod_insert hnotmem, Finset.prod_union hdisj]
  ring

/-- The `D₀·κ = c` identity: clearing the exclusive-STR denominator of `κ_r`
against the full inner product leaves the suffix coefficient `h_r·∏_{j>r} e_j`. -/
private lemma cl05_kappa_c (T : Tower p F) (r : Fin T.K) :
    ((∏ j : Fin T.K, (T.stg j.castSucc).e : ℕ) : ℚ) * T.kappa r.castSucc
      = ((T.stg r.castSucc).h : ℚ) * ∏ j ∈ Finset.Ioi r, ((T.stg j.castSucc).e : ℚ) := by
  have hIio := cl05_strAux_Iio T r.val r.isLt
  have hstr : T.str r.castSucc = T.strAux r.val := rfl
  have hepos : (0 : ℚ) < ((T.stg r.castSucc).e : ℚ) := by
    exact_mod_cast (T.stg r.castSucc).he
  have hIiopos : (0 : ℚ) < ∏ j ∈ Finset.Iio r, ((T.stg j.castSucc).e : ℚ) :=
    Finset.prod_pos fun j _ => by exact_mod_cast (T.stg j.castSucc).he
  have hD : ((∏ j : Fin T.K, (T.stg j.castSucc).e : ℕ) : ℚ)
      = ((T.stg r.castSucc).e : ℚ) * (T.strAux r.val : ℚ)
        * ∏ j ∈ Finset.Ioi r, ((T.stg j.castSucc).e : ℚ) := by
    have hsplit := cl05_prod_split (fun j => (T.stg j.castSucc).e) r
    have hcast : ((∏ j : Fin T.K, (T.stg j.castSucc).e : ℕ) : ℚ)
        = ((∏ j ∈ Finset.Iio r, (T.stg j.castSucc).e : ℕ) : ℚ)
          * ((T.stg r.castSucc).e : ℚ)
          * ((∏ j ∈ Finset.Ioi r, (T.stg j.castSucc).e : ℕ) : ℚ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) hsplit
    rw [hcast, hIio]
    push_cast
    ring
  rw [Tower.kappa, hstr, hD]
  have hstrpos : (0 : ℚ) < (T.strAux r.val : ℚ) := by
    rw [hIio]
    push_cast
    exact hIiopos
  field_simp

/-! Part 4 — the aligned-address count (CI-1 at the tower). -/

/-- CI-1 instantiated: on a nonempty level set, the number of ℤ-aligned addresses
of block `b` at height `γ` is exactly `∏ G_r` (recenterings contribute 1). -/
private lemma cl05_aligned_card (T : Tower p F) (b : ℕ) (γ : ℚ)
    (hne : (T.levelSet b γ).Nonempty) :
    Nat.card {s : T.Addr b // T.aligned γ s} = ∏ r : Fin T.K, cl05_moveDeg T r := by
  classical
  obtain ⟨c₀, hc₀b, hc₀h⟩ := hne
  set eF : Fin T.K → ℕ := fun r => (T.stg r.castSucc).e with heF
  set hF : Fin T.K → ℕ := fun r => (T.stg r.castSucc).h with hhF
  set cZ : Fin T.K → ℤ := fun r => (hF r : ℤ) * ∏ j ∈ Finset.Ioi r, (eF j : ℤ) with hcZ
  set D₀ : ℕ := ∏ r, eF r with hD₀
  have hD₀pos : 0 < D₀ := Finset.prod_pos fun r _ => (T.stg r.castSucc).he
  have hD₀Q : ((D₀ : ℕ) : ℚ) ≠ 0 := by positivity
  -- the D₀·κ = c identity, cast-packaged per slot vector
  have hmulc : ∀ v : Fin T.K → ℕ,
      ((D₀ : ℕ) : ℚ) * (∑ r, (v r : ℚ) * T.kappa r.castSucc)
        = ((∑ r, (v r : ℤ) * cZ r : ℤ) : ℚ) := by
    intro v
    rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    have hkc := cl05_kappa_c T r
    calc ((D₀ : ℕ) : ℚ) * ((v r : ℚ) * T.kappa r.castSucc)
        = (v r : ℚ) * (((D₀ : ℕ) : ℚ) * T.kappa r.castSucc) := by ring
      _ = (v r : ℚ) * (((T.stg r.castSucc).h : ℚ)
            * ∏ j ∈ Finset.Ioi r, ((T.stg j.castSucc).e : ℚ)) := by rw [hkc]
      _ = (v r : ℚ) * ((cZ r : ℤ) : ℚ) := by
          simp only [hcZ, hhF, heF]
          push_cast
          ring
  -- the height decomposition of γ at the witness coordinate
  have hslotlast : c₀.slot (Fin.last T.K) = b := hc₀b
  have hγeq : γ = (c₀.l : ℚ)
      + ((∑ r : Fin T.K, (c₀.slot r.castSucc : ℚ) * T.kappa r.castSucc)
        + (b : ℚ) * T.kappa (Fin.last T.K)) := by
    have h1 : T.ht c₀ = γ := hc₀h
    rw [Tower.ht] at h1
    rw [← h1, Fin.sum_univ_castSucc, hslotlast]
  -- the integer target
  set M : ℤ := (D₀ : ℤ) * (c₀.l : ℤ) + ∑ r, (c₀.slot r.castSucc : ℤ) * cZ r with hM
  have hM_cast : ((M : ℤ) : ℚ) = ((D₀ : ℕ) : ℚ)
      * ((c₀.l : ℚ) + ∑ r : Fin T.K, ((c₀.slot r.castSucc : ℕ) : ℚ) * T.kappa r.castSucc) := by
    have h2 := hmulc (fun r => c₀.slot r.castSucc)
    rw [hM, Int.cast_add, mul_add, h2]
    congr 1
    push_cast
    ring
  -- the alignment ⟺ divisibility bridge for block-b slot vectors
  have hbridge : ∀ sf : Fin (T.K + 1) → ℕ, sf (Fin.last T.K) = b →
      ((∃ n : ℤ, γ - ∑ r, (sf r : ℚ) * T.kappa r = (n : ℚ))
        ↔ ((D₀ : ℕ) : ℤ) ∣ M - ∑ r : Fin T.K, ((sf r.castSucc : ℕ) : ℤ) * cZ r) := by
    intro sf hsftop
    have hsum_split : (∑ r : Fin (T.K + 1), (sf r : ℚ) * T.kappa r)
        = (∑ r : Fin T.K, (sf r.castSucc : ℚ) * T.kappa r.castSucc)
          + (b : ℚ) * T.kappa (Fin.last T.K) := by
      rw [Fin.sum_univ_castSucc, hsftop]
    have hDX : ((M - ∑ r : Fin T.K, ((sf r.castSucc : ℕ) : ℤ) * cZ r : ℤ) : ℚ)
        = ((D₀ : ℕ) : ℚ) * (γ - ∑ r : Fin (T.K + 1), (sf r : ℚ) * T.kappa r) := by
      have h2 := hmulc (fun r => sf r.castSucc)
      rw [Int.cast_sub, hM_cast, ← h2, hsum_split, hγeq]
      ring
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have h1 : ((M - ∑ r : Fin T.K, ((sf r.castSucc : ℕ) : ℤ) * cZ r : ℤ) : ℚ)
          = (((D₀ : ℕ) : ℤ) * n : ℤ) := by
        rw [hDX, hn]
        push_cast
        ring
      exact_mod_cast h1
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h1 : ((D₀ : ℕ) : ℚ) * (γ - ∑ r : Fin (T.K + 1), (sf r : ℚ) * T.kappa r)
          = ((D₀ : ℕ) : ℚ) * (k : ℚ) := by
        rw [← hDX, hk]
        push_cast
        ring
      exact mul_left_cancel₀ hD₀Q h1
  -- the equiv onto the abstract fiber
  have hEquiv : {s : T.Addr b // T.aligned γ s}
      ≃ {t : (r : Fin T.K) → Fin (T.slotBound r) //
          ((D₀ : ℕ) : ℤ) ∣ M - ∑ r, ((t r : ℕ) : ℤ) * cZ r} := by
    refine ⟨fun s => ⟨fun r => ⟨s.1.1 r.castSucc, s.1.2.1 r⟩, ?_⟩, fun t =>
      ⟨⟨Fin.snoc (fun r => (t.1 r : ℕ)) b, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · -- forward condition (defeq through the mk-projection)
      exact (hbridge s.1.1 s.1.2.2).mp s.2
    · -- inner bounds of the reconstructed address
      intro r
      simp only [Fin.snoc_castSucc]
      exact (t.1 r).2
    · -- top pin
      simp only [Fin.snoc_last]
    · -- alignment of the reconstructed address
      have hdvd' : ((D₀ : ℕ) : ℤ) ∣ M - ∑ r : Fin T.K,
          ((Fin.snoc (α := fun _ => ℕ) (fun r => (t.1 r : ℕ)) b r.castSucc : ℕ) : ℤ) * cZ r := by
        have hconv : (∑ r : Fin T.K,
            ((Fin.snoc (α := fun _ => ℕ) (fun r => (t.1 r : ℕ)) b r.castSucc : ℕ) : ℤ) * cZ r)
            = ∑ r : Fin T.K, ((t.1 r : ℕ) : ℤ) * cZ r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [Fin.snoc_castSucc]
        rw [hconv]
        exact t.2
      exact (hbridge (Fin.snoc (fun r => (t.1 r : ℕ)) b)
        (by simp only [Fin.snoc_last])).mpr hdvd'
    · -- left inverse
      rintro ⟨⟨sf, hbounds, htop⟩, hal⟩
      apply Subtype.ext
      apply Subtype.ext
      funext i
      refine Fin.lastCases ?_ (fun r => ?_) i
      · simp only [Fin.snoc_last]
        exact htop.symm
      · simp only [Fin.snoc_castSucc]
    · -- right inverse
      rintro ⟨t, hcond⟩
      apply Subtype.ext
      funext r
      apply Fin.ext
      show (Fin.snoc (α := fun _ => ℕ) (fun r => (t r : ℕ)) b r.castSucc : ℕ) = (t r : ℕ)
      simp only [Fin.snoc_castSucc]
  rw [Nat.card_congr hEquiv]
  exact cl05_walk_fiber T.K eF hF (cl05_moveDeg T) T.slotBound
    (fun r => (T.stg r.castSucc).he) (fun r => (T.stg r.castSucc).hcop)
    (fun r => cl05_slotBound_eq T r) M

/-! Part 5 — level set ≃ aligned addresses (hclean discharges attainability). -/

private lemma cl05_levelSet_card (T : Tower p F) (b : ℕ) (γ : ℚ)
    (hclean : T.cleanThreshold b γ) :
    Nat.card ↥(T.levelSet b γ) = Nat.card {s : T.Addr b // T.aligned γ s} := by
  classical
  -- the forward computation: a level-set coordinate's alignment defect is its p-adic level
  have hfwd : ∀ cc : T.Coord, cc ∈ T.levelSet b γ →
      γ - ∑ r, ((cc.slot r : ℕ) : ℚ) * T.kappa r = (cc.l : ℚ) := by
    intro cc hcc
    have hht : T.ht cc = γ := hcc.2
    rw [← hht, Tower.ht]
    ring
  have halig : ∀ c : ↥(T.levelSet b γ),
      T.aligned γ (⟨c.1.slot, c.1.slot_lt, c.2.1⟩ : T.Addr b) := by
    intro c
    refine ⟨(c.1.l : ℤ), ?_⟩
    show γ - ∑ r, ((c.1.slot r : ℕ) : ℚ) * T.kappa r = ((c.1.l : ℤ) : ℚ)
    rw [hfwd c.1 c.2]
    norm_cast
  set fwd : ↥(T.levelSet b γ) → {s : T.Addr b // T.aligned γ s} :=
    fun c => ⟨⟨c.1.slot, c.1.slot_lt, c.2.1⟩, halig c⟩ with hfwddef
  have hbij : Function.Bijective fwd := by
    constructor
    · rintro ⟨c, hc⟩ ⟨c', hc'⟩ hcc
      have hslot : c.slot = c'.slot := by
        have := congrArg (fun x => x.1.1) hcc
        exact this
      have hl : c.l = c'.l := by
        have h1 : T.ht c = γ := hc.2
        have h2 : T.ht c' = γ := hc'.2
        have key : T.ht c = T.ht c' := h1.trans h2.symm
        rw [Tower.ht, Tower.ht, hslot] at key
        exact_mod_cast add_right_cancel key
      apply Subtype.ext
      obtain ⟨l1, s1, p1⟩ := c
      obtain ⟨l2, s2, p2⟩ := c'
      dsimp only at hl hslot
      subst hl
      subst hslot
      rfl
    · rintro ⟨⟨sf, hbounds, htop⟩, hal⟩
      have hal' : ∃ n : ℤ, γ - ∑ r, ((sf r : ℕ) : ℚ) * T.kappa r = (n : ℚ) := hal
      obtain ⟨n, hn⟩ := hal'
      have hatt : T.attainable γ (⟨sf, hbounds, htop⟩ : T.Addr b) :=
        hclean ⟨sf, hbounds, htop⟩ hal
      have hatt' : (0 : ℚ) ≤ γ - ∑ r, ((sf r : ℕ) : ℚ) * T.kappa r := hatt
      have hn0 : (0 : ℤ) ≤ n := by
        have h1 : (0 : ℚ) ≤ (n : ℚ) := by
          rw [← hn]
          exact hatt'
        exact_mod_cast h1
      have hht : T.ht (⟨n.toNat, sf, hbounds⟩ : T.Coord) = γ := by
        show ((n.toNat : ℕ) : ℚ) + ∑ r, ((sf r : ℕ) : ℚ) * T.kappa r = γ
        have htn : ((n.toNat : ℕ) : ℚ) = (n : ℚ) := by
          have h2 := Int.toNat_of_nonneg hn0
          exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h2
        rw [htn]
        linarith [hn]
      refine ⟨⟨⟨n.toNat, sf, hbounds⟩, htop, hht⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl
  exact Nat.card_congr (Equiv.ofBijective fwd hbij)

/-! Part 6 — the alphabet card as a power of the digit field (CI-2 + CI-3: the
composite is an injective additive bijection onto the alphabet — injectivity is
the PROVED CL-13 LVL-DET, surjectivity is T11). -/

private lemma cl05_alphabet_card_pow (T : Tower p F) (b : ℕ) (γ : ℚ) :
    Nat.card ↥(T.alphabet b γ)
      = Nat.card ↥(T.stg 0).FQ ^ Nat.card ↥(T.levelSet b γ) := by
  classical
  haveI hfin : Finite ↥(T.levelSet b γ) := (levelSet_finite T b γ).to_subtype
  set φ : (↥(T.levelSet b γ) → ↥(T.stg 0).FQ) →+ T.grQ γ :=
    AddMonoidHom.mk' (T.typComposite b γ) (C2_TYPa T b γ).2 with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    have hyc : ∃ csub : ↥(T.levelSet b γ), y csub ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hy0 (funext fun c => hall c)
    obtain ⟨csub, hcsub⟩ := hyc
    have hne' : ∃ c : T.Coord,
        (fun c => if h : c ∈ T.levelSet b γ then y ⟨c, h⟩ else 0) c ≠ 0 := by
      refine ⟨csub.1, ?_⟩
      show (if h : (csub : T.Coord) ∈ T.levelSet b γ
          then y ⟨(csub : T.Coord), h⟩ else 0) ≠ 0
      rw [dif_pos csub.2]
      simpa using hcsub
    have hsupp' : ∀ c : T.Coord,
        (fun c => if h : c ∈ T.levelSet b γ then y ⟨c, h⟩ else 0) c ≠ 0 →
          c ∈ T.levelSet b γ := by
      intro c hc
      by_contra hnc
      apply hc
      show (if h : c ∈ T.levelSet b γ then y ⟨c, h⟩ else 0) = 0
      rw [dif_neg hnc]
    have happ : T.typComposite b γ y ≠ 0 := CL13_lvlDet T b γ _ hne' hsupp'
    exact happ hy
  have hbij : Function.Bijective (fun y => (⟨φ y,
      (T11_attainDichotomy T b γ (φ y)).1.mp ⟨y, rfl⟩⟩ : ↥(T.alphabet b γ))) := by
    constructor
    · intro y y' hyy
      exact hinj (congrArg Subtype.val hyy)
    · rintro ⟨X, hX⟩
      obtain ⟨y, hy⟩ := (T11_attainDichotomy T b γ X).1.mpr hX
      exact ⟨y, Subtype.ext hy⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  rw [Nat.card_fun]

end CL05

/-- Unit C6 (REPAIRED at item 18, 2026-07-31 — the pre-repair form is frozen as
`C6_stmt_pre_repair` with its compiled `Tshallow` negation in CL01c's file):
`#𝔸 = p^aDim`; on nonempty level sets, UNDER THE CLEAN-THRESHOLD HYPOTHESIS
(every aligned address attainable), fullness (𝔸 = the full value field
F_{K+1} = the top stage's K, in cardinality) holds exactly when every level-set
slot is attainable; and unconditionally, an unattainable level-set slot forces
`aDim < log_p card F_{K+1}`. -/
theorem C6_alphabetCard {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (T : Tower p F) (b : ℕ) (γ : ℚ) (hne : (T.levelSet b γ).Nonempty) :
    Nat.card ↥(T.alphabet b γ) = p ^ T.aDim b γ ∧
    (T.cleanThreshold b γ →
      (Nat.card ↥(T.alphabet b γ) = Nat.card ↥(T.stg (Fin.last T.K)).K ↔
        ∀ c : ↥(T.levelSet b γ), ∃ y : ↥(T.stg 0).FQ,
          T.typComposite b γ (Pi.single c y) ≠ 0)) ∧
    ((∃ c : ↥(T.levelSet b γ), ∀ y : ↥(T.stg 0).FQ,
        T.typComposite b γ (Pi.single c y) = 0) →
      T.aDim b γ < Nat.log p (Nat.card ↥(T.stg (Fin.last T.K)).K)) := by
  refine ⟨C6_conjunct1_closable T b γ, ?_, ?_⟩
  · intro hclean
    constructor
    · -- → : the RHS is a theorem (attainability is automatic on the level set)
      intro _
      exact C6_conjunct2_rhs_always T b γ
    · -- ⟸ : fullness from the clean threshold — CL-05, CLOSED 2026-08-02
      -- (execution record in the module docstring; the cl05_* apparatus above:
      -- card 𝔸 = |FQ|^N (CL13-injectivity + T11-surjectivity), N = #aligned
      -- (hclean drops attainability), #aligned = ∏G (the fiber-count kernel),
      -- card K_top = |K₀|^{∏G} = |FQ|^{∏G} (child_field chain + base pin)).
      intro _
      rw [cl05_alphabet_card_pow T b γ, cl05_levelSet_card T b γ hclean,
        cl05_aligned_card T b γ hne, cl05_cardK_chain T]
      have hbase : (T.stg 0).K = (T.stg 0).FQ := T.base.1.2.2
      rw [hbase]
  · -- conjunct 3: its hypothesis is refutable outright (ScratchC6 certificate)
    intro hex
    exact absurd hex (C6_conjunct3_hyp_false T b γ)

end LeanUrat.HC1

#print axioms LeanUrat.HC1.C6_cardK_bridge
#print axioms LeanUrat.HC1.C6_alphabetCard
