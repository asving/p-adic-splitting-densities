/-
FORGE junc_bundle STAGE 2 — `H1/JuncForge.lean`: the row-A/ℤ₂ junction ADJUDICATED
(charter: `lean/notes/openmath/JUNCFORGE_S1_2026-08-08.md` §S5; unit note
`lean/notes/openmath/JUNCFORGE_S2_2026-08-08.md`; ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`).

## WHAT THE UNIT WAS CHARTERED TO DO vs WHAT IT PROVED

The §S5 spec ordered the first compiled e ≥ 2 junction: row A over ℤ₂ —
Φ₀ = X, Φ₁ = X + 2, Φ₂ = X² + 4X + 12, classificand f = X² + 4X + 28
(dev f = 24 + Φ₁² at the deep read, side pair (2,3), γ = 6, pattern ψ₁ = 1 + z,
μ = 1, a = −3) — with `junc_bundle` discharged clause-by-clause at a junction
stage graded at the read pair.  Executing the spec against the LEAN `SideReads`
transcription instead PROVED THE BUNDLE INSTANCE-FALSE — at every stage, for
every recorded node:

* **THE PARITY WALL (`juncforge_no_e2_junction`).**  An e = 2 recording forces,
  through clause (ii)'s two functional equalities at the stride slots {0, 2},
  `ν.h = σ.w(24)` with `gcd(2, ν.h) = 1` — so the in-carrier slot weight is ODD
  while the key-power slot weight `σ.w(Φ₁²) = 2·σ.h` is EVEN.  The two slots can
  never tie, `hRlt` collapses `σ.R f` to a SINGLE monomial, and clause (iii)'s
  anchored pattern `Ranch = pat₀ + pat₁·z` (two nonzero digits, `hpat0`/`hpatTop`)
  is unsatisfiable.  The e₁ = 2 ramification itself (w₁(24) = 3 odd vs the even
  augmented diagonal) is the obstruction: NO ℤ-valued stage scale can host both
  the clause-(ii) window functional and the clause-(iii) graded residual at a
  genuinely ramified deep read.  So every `SideReads` at this read has ν.e = 1.
* **THE LANDING WALL (`juncforge_deep_wall`, char-2 ambient).**  With ν.e = 1
  forced, the designated Φ₂-landing dies in every species/degree case:
  the recentering face by degree (Φ₂ has degree 2, Φ₁ − lift degree 1); the
  g = 1 lift face by degree (Φ₁ + t₀ degree 1); the g = 2 lift face because
  clause (ii) forces pat₁ = 0 (the middle slot B₁ = 0 by Fact-B uniqueness),
  whence ψ ∣ Ranch pins ψ = z² + c₀ — a SQUARE over a finite char-2 residue
  field (Frobenius surjectivity), contradicting `hψirr`.
* **`juncforge_junc_bundle_false`** — the packaged form: for ANY continuation
  history H₂ whose base frame is keyed at Φ₁ and whose interior pin lands Φ₂,
  the `GlueJunction.junc_bundle` existential (dev + pin + SideReads) is FALSE.
* **THE D0 ADJUDICATION (`juncforge_D0_instanceFalse`)** — the stage-1 §S2(c)
  flag DECIDED: `gate_glue_junction`'s `hbundle` hypothesis (f = fq = σ₁rec.Φ,
  the degenerate f-equals-key stratum) is INSTANCE-FALSE — the unique fq-adic
  development of fq (Fact B, `L0_FactB_unique`, the priced support kernel:
  ALREADY PROVED on file) has B₀ = 0 while clause (ii) at `hpat0` demands
  B₀ ≠ 0.  `gate_glue_conditional` is therefore VACUOUS at its compiled
  instance.  DISPOSITION of the gate's display text is an orchestrator/ROOT
  matter — nothing in `GlueRun.lean` is edited; this file only displays.
* **THE POSITIVE FRAGMENT (`juncforge_clauseIII_derivable`)** — the §S5 central
  pin holds EXACTLY as specified at the level of clause (iii) alone: at any
  stage carrying the read-pair pins (Φ = Φ₁, h = 3, (s,t) = (−1,1),
  wPrev(24) = 3, w(24) = 6 — the (2,3)-graded scale), the interface DERIVES
  `σ.R f = R(24)·T⁻³ + T⁻² = T⁻³·(c + z)` at consecutive positions −3, −2 with
  anchor −3 and ord_{z+c}(c + z) = 1 — the harness-measured shape, from
  hS5 + hRΦ + hRmul + hRadd + hK1 alone.  The stage-1 two-scale law survives;
  what fails is CO-HABITATION with clause (ii)'s window functional in one node.

## WHAT THIS MEANS FOR THE E-PHASE FLAG AND THE NAMED OPEN

The HC2/Defs clause-(iii) E-PHASE FLAG ("the σ.R f rendering may
over-strengthen") is CONFIRMED AND SHARPENED: at deep genuinely-ramified reads
the `SideReads` transcription is contradictory between clauses (ii) and (iii),
not merely strong.  The C-e escapee (GlueRun header: "no compiled e ≥ 2
instance exists on file to feed it") is now EXPLAINED: none CAN exist as the
definition stands.  `DIterJunctionSupplier` is NOT refuted (its Φnext is
existential; refinement-shaped e = 1 recordings are not excluded by this file),
but any discharge landing the genuine OM continuation key at a ramified
junction is.  No existing statement is modified; all declarations here are new.

## WHAT IS NOT CLAIMED

No claim at towers other than row A/ℤ₂; no claim about odd-residue-char
pathological stages for the g = 2 leg (the wall's Frobenius leg is proved at
the faithful char-2 ambient, hypothesis `(2 : F) = 0` — satisfied by F4); no
edit or disposition of `gate_glue_junction`/`gate_glue_conditional`; no claim
that `SideReads`/`junc_bundle` should be repaired in any particular way (that
is a ROOT/statement-authority matter).  Numerics were falsifiers only; every
verdict here is kernel-checked.
-/
import LeanUrat.Scaffold.HDischarge.H1.GlueRun
import LeanUrat.Moves.L0_FactB_unique

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

universe u

namespace LeanUrat.Scaffold.HDischarge.H1

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesJ

namespace JuncForge

/-! ### §1 — the row-A compiled data (harness-exact: JUNCFORGE_S1 §S5) -/

/-- Row A classificand `f = X² + 4X + 28` (deg f = 2 > deg Φ₁ = 1: a genuine deep read). -/
noncomputable def fA : Polynomial ℤ_[2] := X ^ 2 + C 4 * X + C 28

/-- Row A level-1 key `Φ₁ = X + 2`. -/
noncomputable def Φ1A : Polynomial ℤ_[2] := X + C 2

/-- Row A level-2 key `Φ₂ = X² + 4X + 12`. -/
noncomputable def Φ2A : Polynomial ℤ_[2] := X ^ 2 + C 4 * X + C 12

/-- The (unique) Φ₁-adic development of f: `f = 24 + Φ₁²` — slots (24, 0, 1). -/
noncomputable def BA : ℕ → Polynomial ℤ_[2] :=
  fun j => if j = 0 then C 24 else if j = 2 then 1 else 0

lemma fA_monic : fA.Monic := by unfold fA; monicity!

lemma fA_ne : fA ≠ 0 := fA_monic.ne_zero

lemma Φ1A_monic : Φ1A.Monic := monic_X_add_C 2

lemma Φ1A_deg : Φ1A.degree = 1 := degree_X_add_C 2

lemma Φ2A_natDegree : Φ2A.natDegree = 2 := by unfold Φ2A; compute_degree!

/-- The row-A deep development identity `f = 24 + Φ₁²`. -/
lemma fA_eq : fA = C 24 + Φ1A ^ 2 := by
  unfold fA Φ1A
  have hexp : (X + C (2 : ℤ_[2])) ^ 2 = X ^ 2 + (C 2 + C 2) * X + C 2 * C 2 := by
    ring
  have h4 : (C (2 : ℤ_[2]) + C 2) = C 4 := by rw [← C_add]; norm_num
  have h4' : (C (2 : ℤ_[2]) * C 2) = C 4 := by rw [← C_mul]; norm_num
  have h28 : (C (28 : ℤ_[2])) = C 24 + C 4 := by rw [← C_add]; norm_num
  rw [hexp, h4, h4', h28]
  ring

/-- The development witness at the compiled slots. -/
lemma BA_dev : IsDevelopment Φ1A fA BA 3 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    unfold BA
    rw [Φ1A_deg]
    split_ifs
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
    · exact lt_of_le_of_lt degree_one_le (by norm_num)
    · rw [degree_zero]; decide
  · intro j hj
    unfold BA
    rw [if_neg (by omega), if_neg (by omega)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : BA 0 = C 24 := rfl
    have h1 : BA 1 = 0 := rfl
    have h2 : BA 2 = 1 := rfl
    rw [h0, h1, h2, fA_eq]
    ring

/-! ### §2 — the Laurent support helper: a monomial is never a two-digit anchored pattern -/

/-- A Laurent MONOMIAL `C c · T m` (c ≠ 0) can never equal an anchored pattern
`T a · toLaurent Ranch` whose `Ranch` carries TWO nonzero coefficients (at 0 and at
some i ≠ 0) — the kernel of the clause-(ii)⊥(iii) wall. -/
private lemma monomial_ne_anchor {K : Type*} [Field K] {c : K} (hc : c ≠ 0)
    {m a : ℤ} {Ranch : Polynomial K} {i : ℕ} (hi : i ≠ 0)
    (h0 : Ranch.coeff 0 ≠ 0) (hiC : Ranch.coeff i ≠ 0) :
    LaurentPolynomial.C c * LaurentPolynomial.T m
      ≠ LaurentPolynomial.T a * Ranch.toLaurent := by
  intro heq
  -- normalize: toLaurent Ranch = C c * T (m - a)
  have h1 : Ranch.toLaurent = LaurentPolynomial.C c * LaurentPolynomial.T (m - a) := by
    have h2 : LaurentPolynomial.T (-a) * (LaurentPolynomial.C c * LaurentPolynomial.T m)
        = LaurentPolynomial.T (-a) * (LaurentPolynomial.T a * Ranch.toLaurent) :=
      congrArg (fun x => LaurentPolynomial.T (-a) * x) heq
    calc Ranch.toLaurent
        = (LaurentPolynomial.T (-a) * LaurentPolynomial.T a) * Ranch.toLaurent := by
          rw [← LaurentPolynomial.T_add]; norm_num
      _ = LaurentPolynomial.T (-a) * (LaurentPolynomial.C c * LaurentPolynomial.T m) := by
          rw [mul_assoc]; exact h2.symm
      _ = LaurentPolynomial.C c * (LaurentPolynomial.T (-a) * LaurentPolynomial.T m) := by
          ring
      _ = LaurentPolynomial.C c * LaurentPolynomial.T (m - a) := by
          rw [← LaurentPolynomial.T_add]; ring_nf
  by_cases hk : 0 ≤ m - a
  · -- nonnegative shift: Ranch = C c * X^d, a single monomial — kills one of the two digits
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (m - a) = (d : ℤ) := ⟨(m - a).toNat, (Int.toNat_of_nonneg hk).symm⟩
    have h3 : Ranch.toLaurent = (Polynomial.C c * Polynomial.X ^ d).toLaurent := by
      rw [h1, hd, map_mul, Polynomial.toLaurent_C, map_pow, Polynomial.toLaurent_X,
        LaurentPolynomial.T_pow, mul_one]
    have h4 : Ranch = Polynomial.C c * Polynomial.X ^ d := Polynomial.toLaurent_injective h3
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      rw [h4] at hiC
      simp only [pow_zero, mul_one, Polynomial.coeff_C, if_neg hi] at hiC
      exact hiC rfl
    · rw [h4] at h0
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega : ¬ (0:ℕ) = d),
        mul_zero] at h0
      exact h0 rfl
  · -- negative shift: Ranch * X^d = C c with d ≥ 1 — coefficient 0 kills it
    push_neg at hk
    obtain ⟨d, hd, hd1⟩ : ∃ d : ℕ, (a - m) = (d : ℤ) ∧ 1 ≤ d := by
      refine ⟨(a - m).toNat, (Int.toNat_of_nonneg (by omega)).symm, ?_⟩
      omega
    have h3 : (Ranch * Polynomial.X ^ d).toLaurent = (Polynomial.C c).toLaurent := by
      rw [map_mul, map_pow, Polynomial.toLaurent_X, LaurentPolynomial.T_pow, mul_one,
        Polynomial.toLaurent_C, h1]
      rw [mul_assoc, ← LaurentPolynomial.T_add]
      rw [show m - a + (d : ℤ) = 0 by omega, LaurentPolynomial.T_zero, mul_one]
    have h4 : Ranch * Polynomial.X ^ d = Polynomial.C c := Polynomial.toLaurent_injective h3
    have h5 := congrArg (fun q => Polynomial.coeff q 0) h4
    simp only [Polynomial.coeff_C_zero] at h5
    rw [Polynomial.coeff_mul_X_pow' Ranch d 0, if_neg (by omega)] at h5
    exact hc h5.symm

/-! ### §3 — the frame forcing: what any `SideReads` at the row-A deep read must record -/

/-- Development pinning (Fact B, the priced §S5 support kernel — PROVED on file as
`Moves.L0_FactB_unique`): any development of f at the Φ₁-keyed frame agrees slotwise
with the compiled (24, 0, 1). -/
private lemma dev_pin {F : Type u} [Field F] [Finite F] (ν : Node 2 F)
    (hσΦ : ν.σ.Φ = Φ1A) {B : ℕ → Polynomial ℤ_[2]} {Nd : ℕ}
    (hdev : IsDevelopment ν.σ.Φ fA B Nd) : ∀ j, B j = BA j := by
  rw [hσΦ] at hdev
  exact L0_FactB_unique Φ1A Φ1A_monic fA hdev BA_dev

/-- **The window forcing**: clause (ii) at the two endpoint digits (`hpat0`/`hpatTop`)
plus `hOrd` force the recorded side onto the development support — `s0 = 0`, `wSide = 2`. -/
private lemma support_frame {F : Type u} [Field F] [Finite F] (ν : Node 2 F)
    (hσΦ : ν.σ.Φ = Φ1A) {B : ℕ → Polynomial ℤ_[2]} {Nd : ℕ} {Φnext : Polynomial ℤ_[2]}
    (hdev : IsDevelopment ν.σ.Φ fA B Nd) (hside : SideReads ν B Nd Φnext) :
    ν.s0 = 0 ∧ ν.wSide = 2 := by
  obtain ⟨-, hii, -, -, -, -⟩ := hside
  have huniq := dev_pin ν hσΦ hdev
  have hsupp : ∀ j, B j ≠ 0 → j = 0 ∨ j = 2 := by
    intro j hj
    by_contra hcon
    push_neg at hcon
    apply hj
    rw [huniq j]
    unfold BA
    rw [if_neg hcon.1, if_neg hcon.2]
  -- s0 lands on the support
  obtain ⟨hB0ne, -, -⟩ := hii 0 (Nat.zero_le _) ν.hpat0
  rw [Nat.mul_zero, Nat.add_zero] at hB0ne
  have hs0 := hsupp _ hB0ne
  -- s0 + wSide lands on the support
  obtain ⟨hBtne, -, -⟩ := hii (ν.wSide / ν.e) (le_refl _) ν.hpatTop
  rw [Nat.mul_div_cancel' ν.hEdvd] at hBtne
  have hst := hsupp _ hBtne
  -- wSide = 0 is impossible: the pattern would be a nonzero constant divisible by ψ
  have hws_ne : ν.wSide ≠ 0 := by
    intro h0
    have hR : ν.Ranch = Polynomial.C (ν.pat 0) := by
      rw [ν.hRanch, h0, Nat.zero_div]
      rw [Finset.sum_range_one]
      simp
    have hdvd : ν.ψ ∣ ν.Ranch :=
      dvd_trans (dvd_pow_self _ (by have := ν.hμ; omega : ν.μ ≠ 0)) ν.hOrd.1
    rw [hR] at hdvd
    have hCne : Polynomial.C (ν.pat 0) ≠ 0 := Polynomial.C_ne_zero.mpr ν.hpat0
    have hle := Polynomial.natDegree_le_of_dvd hdvd hCne
    rw [Polynomial.natDegree_C, ν.hψdeg] at hle
    have := ν.hg
    omega
  constructor
  · rcases hs0 with h | h
    · exact h
    · exfalso; rcases hst with h' | h' <;> omega
  · rcases hs0 with h | h
    · rcases hst with h' | h' <;> omega
    · exfalso; rcases hst with h' | h' <;> omega

/-! ### §4 — THE PARITY WALL: no e ≥ 2 junction recording exists at the row-A deep read -/

/-- **THE PARITY WALL (`ν.e = 1` forced — the C-e escapee explained).**  Any `SideReads`
recording of the row-A deep read (f = X² + 4X + 28 against a Φ₁ = X + 2-keyed frame,
ANY stage, ANY designated landing) has read stride 1.  At ν.e = 2, clause (ii)'s two
stride equalities force `σ.w(24) = ν.h` odd (coprimality) while the key-power slot
carries `σ.w(Φ₁²) = 2·σ.h` even; the slots cannot tie, `hRlt` makes `σ.R f` a single
monomial, and clause (iii)'s two-digit anchored pattern is impossible
(`monomial_ne_anchor`).  This is the e₁ = 2 ramification parity itself — no ℤ-valued
stage hosts both scales.  Char-free; Φnext-free. -/
theorem juncforge_no_e2_junction {F : Type u} [Field F] [Finite F] (ν : Node 2 F)
    (hσΦ : ν.σ.Φ = Φ1A) {B : ℕ → Polynomial ℤ_[2]} {Nd : ℕ} {Φnext : Polynomial ℤ_[2]}
    (hdev : IsDevelopment ν.σ.Φ fA B Nd) (hside : SideReads ν B Nd Φnext) :
    ν.e = 1 := by
  obtain ⟨hs00, hwS2⟩ := support_frame ν hσΦ hdev hside
  have huniq := dev_pin ν hσΦ hdev
  obtain ⟨-, hii, ⟨hiiiA, -⟩, -, -, -⟩ := hside
  -- e divides wSide = 2
  have he12 : ν.e = 1 ∨ ν.e = 2 := by
    have hdvd2 : ν.e ∣ ν.wSide := ν.hEdvd
    rw [hwS2] at hdvd2
    exact Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ hdvd2
  rcases he12 with h | he2
  · exact h
  exfalso
  -- stride 2: pattern width 1, digits at slots 0 and 2
  have hdiv : ν.wSide / ν.e = 1 := by rw [hwS2, he2]
  -- clause (ii) equality at k = 0 (slot 0, digit of 24)
  obtain ⟨-, hE0, -⟩ := hii 0 (Nat.zero_le _) ν.hpat0
  rw [Nat.mul_zero, Nat.add_zero, hs00] at hE0
  rw [huniq 0] at hE0
  -- clause (ii) equality at k = 1 (slot 2, the key-power digit)
  have hpat1 : ν.pat 1 ≠ 0 := by rw [← hdiv]; exact ν.hpatTop
  obtain ⟨-, hE1, -⟩ := hii 1 (by rw [hdiv]) hpat1
  rw [Nat.mul_one, hs00, he2] at hE1
  rw [huniq (0 + 2)] at hE1
  have hBA0 : BA 0 = C 24 := rfl
  have hBA2 : BA (0 + 2) = 1 := rfl
  rw [hBA0] at hE0
  rw [hBA2] at hE1
  -- σ.w 1 = 0
  have hw1 : ν.σ.w 1 = 0 := by
    have h := ν.σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    omega
  rw [hw1] at hE1
  -- the two equalities: 2·σ.w(24) = gam = 2·ν.h, so σ.w(24) = ν.h
  have hW0 : ν.σ.w (C 24) = (ν.h : ℤ) := by
    rw [he2] at hE0
    push_cast at hE0 hE1
    omega
  -- coprimality: ν.h is odd
  have hodd : ¬ (2 ∣ ν.h) := by
    intro hdvd
    have hcop2 : Nat.gcd ν.e ν.h = 1 := ν.hcop
    rw [he2] at hcop2
    have h1 : (2 : ℕ) ∣ Nat.gcd 2 ν.h := Nat.dvd_gcd dvd_rfl hdvd
    rw [hcop2] at h1
    omega
  -- the key-power slot weight is even
  have hΦne : ν.σ.Φ ≠ 0 := ν.σ.hmonic.ne_zero
  have hW2 : ν.σ.w (ν.σ.Φ ^ 2) = 2 * (ν.σ.h : ℤ) := by
    rw [pow_two, ν.σ.hwmul _ _ hΦne hΦne, ν.σ.hwΦ]
    ring
  have hne : ν.σ.w (C 24) ≠ ν.σ.w (ν.σ.Φ ^ 2) := by
    rw [hW0, hW2]
    obtain ⟨m, hm⟩ := Nat.even_or_odd' ν.h
    rcases hm with hm | hm
    · exact absurd ⟨m, by omega⟩ hodd
    · intro hcon
      omega
  -- the split f = 24 + Φ² and the single-monomial residual
  have hfA_split : fA = C 24 + ν.σ.Φ ^ 2 := by rw [hσΦ]; exact fA_eq
  have hC24ne : (C (24 : ℤ_[2])) ≠ 0 := C_ne_zero.mpr (by norm_num)
  have hΦ2ne : ν.σ.Φ ^ 2 ≠ 0 := pow_ne_zero _ hΦne
  have hsumne : C (24 : ℤ_[2]) + ν.σ.Φ ^ 2 ≠ 0 := by rw [← hfA_split]; exact fA_ne
  have hinC24 : inC ν.σ.Φ (C (24 : ℤ_[2])) := by
    show (C (24 : ℤ_[2])).degree < ν.σ.Φ.degree
    rw [hσΦ, Φ1A_deg]
    exact lt_of_le_of_lt degree_C_le (by norm_num)
  have hmono : ∃ c : ↥ν.σ.K, c ≠ 0 ∧ ∃ m : ℤ,
      ν.σ.R fA = LaurentPolynomial.C c * LaurentPolynomial.T m := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- in-carrier slot strictly lighter: R f = R(24), an hS5 monomial
      have hR := ν.σ.hRlt (C 24) (ν.σ.Φ ^ 2) hC24ne hΦ2ne hsumne hlt
      obtain ⟨c, hc⟩ := ν.σ.hS5 (C 24) hC24ne hinC24
      exact ⟨(c : ↥ν.σ.K), Units.ne_zero c, _, by rw [hfA_split, hR, hc]⟩
    · -- key-power slot strictly lighter: R f = T^{2s}
      have hcomm : C (24 : ℤ_[2]) + ν.σ.Φ ^ 2 = ν.σ.Φ ^ 2 + C 24 := by ring
      have hsumne' : ν.σ.Φ ^ 2 + C (24 : ℤ_[2]) ≠ 0 := by rw [← hcomm]; exact hsumne
      have hR := ν.σ.hRlt (ν.σ.Φ ^ 2) (C 24) hΦ2ne hC24ne hsumne' hgt
      refine ⟨1, one_ne_zero, ν.σ.s + ν.σ.s, ?_⟩
      rw [hfA_split, hcomm, hR, pow_two, ν.σ.hRmul _ _ hΦne hΦne, ν.σ.hRΦ,
        ← LaurentPolynomial.T_add, map_one, one_mul]
  -- clause (iii): the anchored two-digit pattern
  have hsum : (∑ j ∈ Finset.range Nd, B j * ν.σ.Φ ^ j) = fA := hdev.2.2.symm
  rw [hsum] at hiiiA
  obtain ⟨hRc0, hReq⟩ := hiiiA
  -- Ranch = C(pat 0) + C(pat 1)·X: two nonzero coefficients
  have hRanch2 : ν.Ranch = Polynomial.C (ν.pat 0) + Polynomial.C (ν.pat 1) * Polynomial.X := by
    rw [ν.hRanch, hdiv]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp
  have hcoeff1 : ν.Ranch.coeff 1 = ν.pat 1 := by
    rw [hRanch2]
    simp
  obtain ⟨c, hcne, m, hRm⟩ := hmono
  rw [hRm] at hReq
  exact monomial_ne_anchor hcne (i := 1) one_ne_zero hRc0 (hcoeff1 ▸ hpat1) hReq

/-! ### §5 — THE LANDING WALL: the Φ₂-landing junction bundle is instance-false -/

/-- **THE LANDING WALL.**  At the faithful char-2 ambient, NO node over ANY stage
keyed at Φ₁ = X + 2 hosts a `SideReads` of f = X² + 4X + 28 with designated landing
Φ₂ = X² + 4X + 12: e = 2 dies by the parity wall; at e = 1 the recentering face and
the g = 1 lift face die by degree (Φ₂ has degree 2), and the g = 2 lift face forces
ψ = z² + c₀ with pat₁ = 0 — a Frobenius square over the finite char-2 residue field,
contradicting `hψirr`.  The §S5-chartered clause-by-clause discharge is therefore
IMPOSSIBLE as `SideReads` stands: `junc_bundle` at row A is instance-false. -/
theorem juncforge_deep_wall {F : Type u} [Field F] [Finite F] (h2F : (2 : F) = 0)
    (ν : Node 2 F) (hσΦ : ν.σ.Φ = Φ1A) {B : ℕ → Polynomial ℤ_[2]} {Nd : ℕ}
    (hdev : IsDevelopment ν.σ.Φ fA B Nd) :
    ¬ SideReads ν B Nd Φ2A := by
  intro hside
  have he1 : ν.e = 1 := juncforge_no_e2_junction ν hσΦ hdev hside
  obtain ⟨hs00, hwS2⟩ := support_frame ν hσΦ hdev hside
  have huniq := dev_pin ν hσΦ hdev
  obtain ⟨-, hii, ⟨-, -⟩, hiv, -, -⟩ := hside
  have hΦ1deg : ν.σ.Φ.degree = 1 := by rw [hσΦ]; exact Φ1A_deg
  by_cases hsp : ν.species = ReadSpecies.recentering
  · -- recentering face: Φ₂ = Φ₁ − lift has degree 1 ≠ 2
    obtain ⟨hinC, -, -, -, hΦn⟩ := hiv.1 hsp
    have hdeg : (ν.σ.Φ - ν.lift).degree = 1 := by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt
        (show ν.lift.degree < ν.σ.Φ.degree from hinC)]
      exact hΦ1deg
    have h1 : Φ2A.natDegree = 1 := by
      rw [hΦn]
      exact Polynomial.natDegree_eq_of_degree_eq_some hdeg
    rw [Φ2A_natDegree] at h1
    omega
  · -- lift face
    obtain ⟨tt, htt0, httk, hΦeq⟩ := hiv.2 hsp
    -- the middle digit is dead: pat 1 = 0 (B 1 = 0 by Fact B)
    have hdiv1 : ν.wSide / ν.e = 2 := by rw [hwS2, he1]
    have hpat1 : ν.pat 1 = 0 := by
      by_contra hne
      obtain ⟨hBne, -, -⟩ := hii 1 (by rw [hdiv1]; omega) hne
      apply hBne
      rw [Nat.mul_one, hs00, he1, huniq (0 + 1)]
      rfl
    -- Ranch = C(pat 0) + C(pat 2)·X², nonzero, natDegree ≤ 2
    have hRanch3 : ν.Ranch
        = Polynomial.C (ν.pat 0) + Polynomial.C (ν.pat 2) * Polynomial.X ^ 2 := by
      rw [ν.hRanch, hdiv1]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hpat1]
      simp
    have hRne : ν.Ranch ≠ 0 := by
      intro h0
      apply ν.hpat0
      have := congrArg (fun q => Polynomial.coeff q 0) h0
      rw [hRanch3] at this
      simpa using this
    have hRdeg : ν.Ranch.natDegree ≤ 2 := by
      rw [hRanch3]
      refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      simp only [Polynomial.natDegree_C, max_le_iff]
      refine ⟨by omega, le_trans (Polynomial.natDegree_mul_le) ?_⟩
      simp [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
    have hdvdψ : ν.ψ ∣ ν.Ranch :=
      dvd_trans (dvd_pow_self _ (by have := ν.hμ; omega : ν.μ ≠ 0)) ν.hOrd.1
    have hgle : ν.g ≤ 2 := by
      have h := Polynomial.natDegree_le_of_dvd hdvdψ hRne
      rw [ν.hψdeg] at h
      omega
    have hg1 := ν.hg
    have hgcases : ν.g = 1 ∨ ν.g = 2 := by omega
    rcases hgcases with hg | hg
    · -- g = 1: the lift key Φ₁ + t₀ has degree 1 ≠ 2
      rw [he1, hg] at hΦeq
      rw [Finset.sum_range_one] at hΦeq
      simp only [Nat.mul_one, Nat.mul_zero, pow_one, pow_zero, mul_one] at hΦeq
      have htt0deg : (tt 0).degree < 1 := by
        by_cases h0 : ν.ψ.coeff 0 = 0
        · rw [htt0 0 h0, degree_zero]; decide
        · obtain ⟨-, hinC0, -, -⟩ := httk 0 (by omega) h0
          rw [← hΦ1deg]
          exact hinC0
      have hdeg : (ν.σ.Φ + tt 0).degree = 1 := by
        rw [Polynomial.degree_add_eq_left_of_degree_lt (by rw [hΦ1deg]; exact htt0deg)]
        exact hΦ1deg
      have h1 : Φ2A.natDegree = 1 := by
        rw [hΦeq]
        exact Polynomial.natDegree_eq_of_degree_eq_some hdeg
      rw [Φ2A_natDegree] at h1
      omega
    · -- g = 2: ψ = X² + C c₀ is a Frobenius square over the char-2 residue field
      -- (a) ψ.coeff 1 = 0 via ψ ∣ Ranch at equal degree
      have hψne : ν.ψ ≠ 0 := ν.hψmonic.ne_zero
      obtain ⟨q, hq⟩ := hdvdψ
      have hqne : q ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hq
        exact hRne hq
      have hψnd : ν.ψ.natDegree = 2 := by rw [ν.hψdeg, hg]
      have hqdeg : q.natDegree = 0 := by
        have h := congrArg Polynomial.natDegree hq
        rw [Polynomial.natDegree_mul hψne hqne, hψnd] at h
        omega
      obtain ⟨u, hu⟩ := Polynomial.natDegree_eq_zero.mp hqdeg
      have hune : u ≠ 0 := by
        rintro rfl
        rw [map_zero] at hu
        exact hqne hu.symm
      have hRcoeff1 : ν.Ranch.coeff 1 = 0 := by
        rw [hRanch3]
        simp
      have hψc1 : ν.ψ.coeff 1 = 0 := by
        have h := congrArg (fun r => Polynomial.coeff r 1) hq
        rw [hRcoeff1, ← hu, Polynomial.coeff_mul_C] at h
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact h'
        · exact absurd h' hune
      -- (b) reconstruct ψ = X² + C(ψ.coeff 0)
      have hψ2 : ν.ψ = Polynomial.X ^ 2 + Polynomial.C (ν.ψ.coeff 0) := by
        have hlead : ν.ψ.coeff 2 = 1 := by
          have := ν.hψmonic.coeff_natDegree
          rwa [hψnd] at this
        ext n
        match n with
        | 0 => simp [Polynomial.coeff_X_pow]
        | 1 => simp [hψc1, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        | 2 => simp [hlead, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        | (n + 3) =>
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hψnd]; omega)]
          rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
            if_neg (show ¬ (n + 3 = 2) by omega), if_neg (show ¬ (n + 3 = 0) by omega)]
          norm_num
      -- (c) char 2 in the residue field, squaring is surjective
      have h2K : (2 : ↥ν.σ.K) = 0 := by
        apply ν.σ.K.subtype.injective
        rw [map_ofNat, map_zero]
        exact h2F
      have hsq : ∀ d : ↥ν.σ.K, ∃ dd, dd ^ 2 = d := by
        have hinj : Function.Injective (fun x : ↥ν.σ.K => x ^ 2) := by
          intro x y hxy
          simp only at hxy
          have h1 : (x - y) ^ 2 = 0 := by
            linear_combination hxy + (y * y - x * y) * h2K
          have := pow_eq_zero_iff (n := 2) (by omega) |>.mp h1
          exact sub_eq_zero.mp this
        intro d
        exact Finite.injective_iff_surjective.mp hinj d
      obtain ⟨dd, hdd⟩ := hsq (ν.ψ.coeff 0)
      -- (d) ψ = (X + C dd)² contradicts irreducibility
      have h2P : (2 : Polynomial ↥ν.σ.K) = 0 := by
        rw [← map_ofNat (Polynomial.C : ↥ν.σ.K →+* Polynomial ↥ν.σ.K) 2, h2K, map_zero]
      have hψsq : ν.ψ = (Polynomial.X + Polynomial.C dd) * (Polynomial.X + Polynomial.C dd) := by
        rw [hψ2, ← hdd]
        have hexp : (Polynomial.X + Polynomial.C dd) * (Polynomial.X + Polynomial.C dd)
            = Polynomial.X ^ 2 + 2 * (Polynomial.C dd * Polynomial.X)
              + Polynomial.C dd * Polynomial.C dd := by ring
        rw [hexp, h2P, zero_mul, add_zero, ← Polynomial.C_mul, ← pow_two]
      have hXdd_notunit : ¬ IsUnit (Polynomial.X + Polynomial.C dd) := by
        apply Polynomial.not_isUnit_of_natDegree_pos
        rw [Polynomial.natDegree_X_add_C]
        omega
      rcases ν.hψirr.isUnit_or_isUnit hψsq with h | h
      · exact hXdd_notunit h
      · exact hXdd_notunit h

/-- The corpus ambient field F4 satisfies the wall's char-2 hypothesis. -/
lemma F4_char2 : (2 : F4) = 0 := by
  have h := CharP.cast_eq_zero F4 2
  simpa using h

/-- The landing wall AT THE CORPUS FIELD (display instantiation: the hypothesis class
is inhabited exactly where the compiled corpus lives). -/
theorem juncforge_deep_wall_F4 (ν : Node 2 F4) (hσΦ : ν.σ.Φ = Φ1A)
    {B : ℕ → Polynomial ℤ_[2]} {Nd : ℕ} (hdev : IsDevelopment ν.σ.Φ fA B Nd) :
    ¬ SideReads ν B Nd Φ2A :=
  juncforge_deep_wall F4_char2 ν hσΦ hdev

/-- **The packaged junction-bundle verdict**: for any continuation history H₂ whose
base frame is keyed at Φ₁ and whose interior pin (1 < |H₂|) lands Φ₂, the
`GlueJunction.junc_bundle` core existential — development + interior pin + full
`SideReads` at the promoted base read — is FALSE.  (Negating the first three
conjuncts negates the full four-clause bundle a fortiori.) -/
theorem juncforge_junc_bundle_false {F : Type u} [Field F] [Finite F] (h2F : (2 : F) = 0)
    (H₂ : History 2 F) (hΦ : H₂.headNode.σ.Φ = Φ1A) (hlen : 1 < H₂.nodes.length)
    (hkey : (H₂.nodes[1]'hlen).σ.Φ = Φ2A) :
    ¬ ∃ (B : ℕ → Polynomial ℤ_[2]) (Nd : ℕ) (Φnext : Polynomial ℤ_[2]),
        IsDevelopment H₂.headNode.σ.Φ fA B Nd ∧
        (∀ h1 : 1 < H₂.nodes.length, Φnext = (H₂.nodes[1]'h1).σ.Φ) ∧
        SideReads H₂.headNode B Nd Φnext := by
  rintro ⟨B, Nd, Φnext, hdev, hpin, hside⟩
  have hΦn : Φnext = Φ2A := by rw [hpin hlen, hkey]
  rw [hΦn] at hside
  exact juncforge_deep_wall h2F H₂.headNode hΦ hdev hside

/-! ### §6 — THE POSITIVE FRAGMENT: clause (iii) IS derivable at the read-pair scale -/

/-- **The §S5 central pin, at its true strength**: at any stage carrying the
(2,3)-read-pair pins — key Φ₁, `h = 3`, Bézout `(s, t) = (−1, 1)`, parent weight
`wPrev(24) = 3`, graded weight `w(24) = 6` — the interface DERIVES the harness-exact
clause-(iii) shape: `σ.R f = R(24)·T⁻³ + T⁻² = T⁻³·(c + z)` (consecutive positions
−3, −2), anchor a = −3, `Ranch = c + z` with `ord_{z+c} = μ = 1`, purely from
hS5 + hRΦ + hRmul + hRadd + hK1.  The two-scale law of stage 1 (§S2(a)) is thus
Lean-derivable; what `juncforge_no_e2_junction` kills is only its CO-HABITATION with
clause (ii)'s window functional inside one recorded node.  The existence of a stage
with these pins is the (open, separately priced) junction-stage construction — this
theorem carries them as hypotheses and is a derivation, not an instance. -/
theorem juncforge_clauseIII_derivable {F : Type u} [Field F] [Finite F]
    (σ : Stage 2 F) (hΦ : σ.Φ = Φ1A) (hh : σ.h = 3) (hs : σ.s = -1) (ht : σ.t = 1)
    (hwP : σ.wPrev (C 24) = 3) (hw24 : σ.w (C 24) = 6) :
    ∃ c : (↥σ.K)ˣ,
      HasAnchorK (σ.R fA) (-3) (Polynomial.C ((c : ↥σ.K)) + Polynomial.X) ∧
      OrdPsiPoly (Polynomial.X + Polynomial.C ((c : ↥σ.K)))
        (Polynomial.C ((c : ↥σ.K)) + Polynomial.X) 1 := by
  have hΦne : σ.Φ ≠ 0 := σ.hmonic.ne_zero
  have hC24ne : (C (24 : ℤ_[2])) ≠ 0 := C_ne_zero.mpr (by norm_num)
  have hΦ2ne : σ.Φ ^ 2 ≠ 0 := pow_ne_zero _ hΦne
  have hfA_split : fA = C 24 + σ.Φ ^ 2 := by rw [hΦ]; exact fA_eq
  have hsumne : C (24 : ℤ_[2]) + σ.Φ ^ 2 ≠ 0 := by rw [← hfA_split]; exact fA_ne
  have hinC24 : inC σ.Φ (C (24 : ℤ_[2])) := by
    show (C (24 : ℤ_[2])).degree < σ.Φ.degree
    rw [hΦ, Φ1A_deg]
    exact lt_of_le_of_lt degree_C_le (by norm_num)
  -- the tie: both slots at graded weight 6
  have hW2 : σ.w (σ.Φ ^ 2) = 6 := by
    rw [pow_two, σ.hwmul _ _ hΦne hΦne, σ.hwΦ, hh]
    norm_num
  have hw1 : σ.w 1 = 0 := by
    have h := σ.hwmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at h
    omega
  -- K1: w(f) attains the slot minimum 6
  have hwfA : σ.w fA = 6 := by
    have hdev : IsDevelopment σ.Φ fA BA 3 := by rw [hΦ]; exact BA_dev
    obtain ⟨hle, j, hjlt, hjne, hjeq⟩ := σ.hK1 fA BA 3 fA_ne hdev
    have hjeq' : σ.w fA = σ.w (BA j) + (j : ℤ) * σ.w σ.Φ := hjeq
    interval_cases j
    · rw [show BA 0 = C 24 from rfl] at hjeq'
      rw [hjeq', hw24]
      push_cast
      ring
    · exact (hjne rfl).elim
    · rw [show BA 2 = 1 from rfl] at hjeq'
      rw [hjeq', hw1, σ.hwΦ, hh]
      push_cast
  -- the derivable sum: R f = R(24) + T^{2s}
  obtain ⟨c, hc⟩ := σ.hS5 (C 24) hC24ne hinC24
  have hRadd := σ.hRadd (C 24) (σ.Φ ^ 2) hC24ne hΦ2ne hsumne
    (by rw [hw24, hW2]) (by rw [← hfA_split, hwfA, hw24])
  have hRΦ2 : σ.R (σ.Φ ^ 2) = LaurentPolynomial.T (-2) := by
    rw [pow_two, σ.hRmul _ _ hΦne hΦne, σ.hRΦ, ← LaurentPolynomial.T_add, hs]
    norm_num
  have hRfA : σ.R fA
      = LaurentPolynomial.C ((c : ↥σ.K)) * LaurentPolynomial.T (-3)
        + LaurentPolynomial.T (-2) := by
    rw [hfA_split, hRadd, hc, hRΦ2, ht, hwP]
    norm_num
  refine ⟨c, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- anchored: Ranch(0) = c ≠ 0
    simp [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_zero]
  · -- σ.R f = T⁻³ · toLaurent (C c + X): positions −3, −2
    rw [hRfA, map_add, Polynomial.toLaurent_C, Polynomial.toLaurent_X, mul_add,
      mul_comm (LaurentPolynomial.T (-3 : ℤ)) (LaurentPolynomial.C ((c : ↥σ.K))),
      ← LaurentPolynomial.T_add]
    norm_num
  · -- (z + c)¹ ∣ (c + z)
    rw [pow_one]
    exact dvd_of_eq (add_comm _ _)
  · -- ¬ (z + c)² ∣ (c + z): degree
    intro hdvd
    have hne : (Polynomial.C ((c : ↥σ.K)) + Polynomial.X) ≠ 0 := by
      have hmon : (Polynomial.X + Polynomial.C ((c : ↥σ.K))).Monic := monic_X_add_C _
      rw [add_comm]
      exact hmon.ne_zero
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C] at hle
    have : (Polynomial.C ((c : ↥σ.K)) + Polynomial.X).natDegree = 1 := by
      rw [add_comm]
      exact Polynomial.natDegree_X_add_C _
    omega

/-! ### §7 — THE D0 ADJUDICATION: `gate_glue_junction`'s hbundle is instance-false -/

/-- The self-development of fq at the key fq: `fq = 0 + 1·fq` (slots (0, 1)). -/
private noncomputable def BselfJ : ℕ → Polynomial ℤ_[2] := fun j => if j = 1 then 1 else 0

private lemma fq_deg' : U31.fq.degree = 2 := by
  rw [Polynomial.degree_eq_natDegree U31.fq_monic.ne_zero, U31.fq_natDegree]
  rfl

private lemma BselfJ_dev : IsDevelopment U31.fq U31.fq BselfJ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    unfold BselfJ
    rw [fq_deg']
    split_ifs
    · exact lt_of_le_of_lt degree_one_le (by norm_num)
    · rw [degree_zero]; decide
  · intro j hj
    unfold BselfJ
    rw [if_neg (by omega)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one]
    unfold BselfJ
    norm_num

/-- **THE D0 VERDICT — `hbundle` is INSTANCE-FALSE (the stage-1 §S2(c) flag CONFIRMED
in Lean).**  The negated proposition is BYTE-IDENTICAL to the `hbundle` hypothesis of
`gate_glue_junction`/`gate_glue_conditional` (`H1/GlueRun.lean`): at the compiled
seam the junction read's frame key IS the classificand (f = fq = σ₁rec.Φ — the
degenerate D0 stratum), so the unique development (Fact B) has B₀ = 0, while
`SideReads` clause (ii) at the recorded `hpat0` (pat 0 = −rcCenter ≠ 0,
`RCWitness.lean`) demands B₀ ≠ 0.  Hence `gate_glue_conditional` is VACUOUS at its
compiled instance: the D-1 wall at this seam is the degenerate stratum, not an
opacity wall.  The gates themselves are NOT edited — display only; disposition is an
orchestrator/ROOT matter. -/
theorem juncforge_D0_instanceFalse :
    ¬ ∃ (B : ℕ → Polynomial ℤ_[2]) (Nd : ℕ) (Φnext : Polynomial ℤ_[2]),
        IsDevelopment H₂rc.headNode.σ.Φ U31.fq B Nd ∧
        (∀ h1 : 1 < H₂rc.nodes.length, Φnext = (H₂rc.nodes[1]'h1).σ.Φ) ∧
        SideReads H₂rc.headNode B Nd Φnext ∧
        (ReadSpecies.recentering = ReadSpecies.recentering →
          inC H₂rc.headNode.σ.Φ H₂rc.headNode.lift ∧ H₂rc.headNode.lift ≠ 0 ∧
          H₂rc.headNode.σ.w H₂rc.headNode.lift = H₂rc.headNode.σ.w H₂rc.headNode.σ.Φ ∧
          H₂rc.headNode.σ.R H₂rc.headNode.lift
            = LaurentPolynomial.C H₂rc.headNode.center * LaurentPolynomial.T 0 ∧
          Φnext = H₂rc.headNode.σ.Φ - H₂rc.headNode.lift) := by
  rintro ⟨B, Nd, Φnext, hdev, -, hside, -⟩
  -- the head node's frame key is fq itself: the D0 stratum
  have hkey : H₂rc.headNode.σ.Φ = U31.fq := HK25.σ₁rec_Φ
  rw [hkey] at hdev
  -- Fact B: the unique development has B 0 = 0
  have huniq := L0_FactB_unique U31.fq U31.fq_monic U31.fq hdev BselfJ_dev
  have hB0 : B 0 = 0 := by
    rw [huniq 0]
    rfl
  -- clause (ii) at k = 0 with the recorded hpat0 demands B 0 ≠ 0
  obtain ⟨-, hii, -, -, -, -⟩ := hside
  obtain ⟨hBne, -, -⟩ := hii 0 (Nat.zero_le _) H₂rc.headNode.hpat0
  apply hBne
  show B (ν₁rcRoot.s0 + ν₁rcRoot.e * 0) = 0
  rw [Nat.mul_zero, Nat.add_zero]
  exact hB0

/-! ### §8 — REVISION 1 (2026-08-08, JFS2-AUDIT fix): the D0 ↔ gate binder tie, kernel-checked

The faithfulness audit (`lean/notes/openmath/JUNCFORGE_S2_audit_report.md`) found the
"BYTE-IDENTICAL to hbundle" claim of §7 uncertifiable from its packet, and found the
§S1/§S5 prose overrunning the proved scope (the walls bind the row-A fiber
`(fA, Φ1A)` via `hσΦ`/`hdev`; the file-header glosses "at every stage, for every
recorded node" and "none CAN exist as the definition stands" are rescoped by
`JUNCFORGE_S2_2026-08-08.md` REVISION 1 — read them as row-A-fiber claims).  The two
declarations below discharge the byte-identity gap INSIDE the kernel, by two
decorrelated legs (one textual, one structural — no shared extraction):

* `juncforge_gate_hbundle_false` — the statement is `gate_glue_junction`'s `hbundle`
  binder copied verbatim (modulo leading indentation) and negated; the proof term is
  `juncforge_D0_instanceFalse` applied DIRECTLY, no massaging.  If the copy drifted
  from the D0 proposition, elaboration would fail.
* `juncforge_gluePacket_false` — the NON-TEXTUAL leg: for EVERY base history H₁, the
  full `GlueJunction U31.fq H₁ H₂rc ReadSpecies.recentering` packet is uninhabited,
  proved by projecting the structure's own `junc_bundle` FIELD (the gate's compiled
  binder type, not a copy) into `juncforge_D0_instanceFalse`.  This certifies in the
  kernel that the proposition the D0 verdict negates IS the gate's bundle clause, and
  makes "`gate_glue_conditional` is vacuous at its compiled instance" a theorem: its
  conclusion route can never be fed. -/

/-- **REVISION 1 TIE, textual leg (JFS2-AUDIT gap 3).**  `gate_glue_junction`'s
`hbundle` binder (`H1/GlueRun.lean`), verbatim modulo indentation, negated; proof =
`juncforge_D0_instanceFalse` unchanged.  Kernel-certified identity of the two texts. -/
theorem juncforge_gate_hbundle_false :
    ¬ ∃ (B : ℕ → Polynomial ℤ_[2]) (Nd : ℕ) (Φnext : Polynomial ℤ_[2]),
      IsDevelopment H₂rc.headNode.σ.Φ U31.fq B Nd ∧
      (∀ h1 : 1 < H₂rc.nodes.length, Φnext = (H₂rc.nodes[1]'h1).σ.Φ) ∧
      SideReads H₂rc.headNode B Nd Φnext ∧
      (ReadSpecies.recentering = ReadSpecies.recentering →
        inC H₂rc.headNode.σ.Φ H₂rc.headNode.lift ∧ H₂rc.headNode.lift ≠ 0 ∧
        H₂rc.headNode.σ.w H₂rc.headNode.lift = H₂rc.headNode.σ.w H₂rc.headNode.σ.Φ ∧
        H₂rc.headNode.σ.R H₂rc.headNode.lift
          = LaurentPolynomial.C H₂rc.headNode.center * LaurentPolynomial.T 0 ∧
        Φnext = H₂rc.headNode.σ.Φ - H₂rc.headNode.lift) :=
  juncforge_D0_instanceFalse

/-- **REVISION 1 TIE, structural leg (the non-textual check).**  The full
`GlueJunction` packet at the compiled seam data — U31's classificand fq, the RCW
continuation H₂rc, the recentering species, ANY base history H₁ — is uninhabited:
its own `junc_bundle` field is exactly the proposition `juncforge_D0_instanceFalse`
negates (`sp' := ReadSpecies.recentering` substituted).  Hence
`gate_glue_conditional` is VACUOUS at its compiled instance as a THEOREM, not a
prose gloss.  The gates themselves remain unedited (display only). -/
theorem juncforge_gluePacket_false (H₁ : History 2 F4) :
    ¬ GlueJunction U31.fq H₁ H₂rc ReadSpecies.recentering :=
  fun J => juncforge_D0_instanceFalse J.junc_bundle

end JuncForge

end LeanUrat.Scaffold.HDischarge.H1

#print axioms LeanUrat.Scaffold.HDischarge.H1.JuncForge.juncforge_no_e2_junction
#print axioms LeanUrat.Scaffold.HDischarge.H1.JuncForge.juncforge_deep_wall
#print axioms LeanUrat.Scaffold.HDischarge.H1.JuncForge.juncforge_deep_wall_F4
#print axioms LeanUrat.Scaffold.HDischarge.H1.JuncForge.juncforge_junc_bundle_false
#print axioms LeanUrat.Scaffold.HDischarge.H1.JuncForge.juncforge_clauseIII_derivable
#print axioms LeanUrat.Scaffold.HDischarge.H1.JuncForge.juncforge_D0_instanceFalse
#print axioms LeanUrat.Scaffold.HDischarge.H1.JuncForge.juncforge_gate_hbundle_false
#print axioms LeanUrat.Scaffold.HDischarge.H1.JuncForge.juncforge_gluePacket_false
