/-
HDISCHARGE_H3 §2.2 — unit D12R-U2a/b/c: the (HEN-LIFT) Lean formalization.
U2a `henLift_padic` (existence; statement transcribed VERBATIM from the blueprint's
compile-probed display) · U2b `henLift_padic_unique` (uniqueness; statement designed
here at E-phase per the blueprint's charge: same hypotheses, two monic lift pairs
with equal reductions are equal) · U2c the read-off (`henLift_padic_irreducible` +
the unramified/(E,F) clause in the blueprint-sanctioned residue-degree-only
numerical form; packaged in `henLift_padic_readoff`).
-/
import Mathlib

/-!
# (HEN-LIFT): coprime-factor Hensel lifting over ℤ_[p] [HDISCHARGE_H3 unit D12R-U2a/b/c]

**PROVENANCE.**

* Blueprint: `lean/blueprints/HDISCHARGE_H3.md` §2.2 (unit D12R-U2a/b/c, the D-12r
  optional Lean upgrade).  The `henLift_padic` statement is the blueprint's
  compile-probed display, transcribed verbatim.  U2b/U2c statements are adjudicated
  here at E-phase, as the blueprint directs ("statement to be compile-probed at
  E-phase" / "E-phase probe owed").
* Math source of record: the (HEN-LIFT) faithfulness brief (HL-a/b/c), i.e. Hensel's
  lemma for coprime factorizations — Neukirch, *Algebraic Number Theory* II §4 region
  / Serre, *Local Fields* alternates (LIT-3 pins, tracked on the D-12r row).
* Mathlib probe (blueprint §2.2, re-confirmed here): `HenselianLocalRing` and
  `hensels_lemma` are ROOT-lifting only; no coprime-FACTOR lifting exists in the pin
  (`UniversalCoprimeFactorizationRing` lifts only into an étale extension), so this
  file is a genuine formalization, not a cite.  Route: successive approximation mod
  p^(n+1) with Bézout correction, limits via `IsAdicComplete (maximalIdeal ℤ_[p])`.

**U2c vocabulary adjudication** (blueprint: "residue-degree-only numerical form
acceptable at first landing; full IsUnramified form as the stretch goal"):

* irreducibility clause: `henLift_padic_irreducible` (via
  `Polynomial.Monic.irreducible_of_irreducible_map`);
* (E,F) clause, numerical form: `henLift_padic_residue_equiv` — the residue ring
  ℤ_[p][X]/(p, g) of the g-order is isomorphic to `AdjoinRoot ψ` = 𝔽_p[X]/(ψ); for ψ
  irreducible that quotient is a FIELD (`henLift_padic_residue_isField`), i.e. p alone
  already cuts out the maximal ideal above (p): the E = 1 witness; and
  `henLift_padic_residue_finrank`: dim_{𝔽_p} AdjoinRoot ψ = deg ψ: the F = deg ψ
  witness.  The full `IsUnramified`-vocabulary form is the recorded stretch goal and
  is NOT claimed here.

Everything below is `sorry`-free and Lean-core (gate: `lake env lean` + AxChk).
-/

namespace LeanUrat.Scaffold.HD3

namespace HenLift

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## §0 Residue and adic-completeness helpers -/

/-- Reduction mod p detects divisibility by `p` (kernel of `PadicInt.toZMod`). -/
lemma toZMod_eq_zero_iff_dvd (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

/-- Polynomial-level version: reduction mod p kills `F` iff `C p` divides `F`. -/
lemma map_toZMod_eq_zero_iff (F : Polynomial ℤ_[p]) :
    F.map PadicInt.toZMod = 0 ↔ Polynomial.C (p : ℤ_[p]) ∣ F := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro h0 i
    rw [← toZMod_eq_zero_iff_dvd, ← Polynomial.coeff_map, h0, Polynomial.coeff_zero]
  · intro hdvd
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, toZMod_eq_zero_iff_dvd]
    exact hdvd i

/-- Every mod-p polynomial lifts with the same degree (`toZMod` is surjective). -/
lemma exists_map_toZMod_eq (φ : Polynomial (ZMod p)) :
    ∃ Q : Polynomial ℤ_[p], Q.map PadicInt.toZMod = φ ∧ Q.degree = φ.degree :=
  Polynomial.exists_degree_eq_of_mem_lifts
    (Polynomial.mem_lifts_of_surjective (ZMod.ringHom_surjective PadicInt.toZMod) φ)

/-- Every monic mod-p polynomial lifts monically with the same degree. -/
lemma exists_monic_lift {φ : Polynomial (ZMod p)} (hφ : φ.Monic) :
    ∃ Q : Polynomial ℤ_[p], Q.map PadicInt.toZMod = φ ∧ Q.degree = φ.degree ∧ Q.Monic :=
  Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (ZMod.ringHom_surjective PadicInt.toZMod) φ) hφ

lemma toZMod_natCast_p : (PadicInt.toZMod ((p : ℤ_[p])) : ZMod p) = 0 := by
  rw [map_natCast, ZMod.natCast_self]

lemma cast_p_ne_zero : ((p : ℤ_[p])) ≠ 0 :=
  Nat.cast_ne_zero.mpr hp.out.ne_zero

/-- Constant-multiplication preserves degree over the domain ℤ_[p]. -/
lemma degree_C_mul' {c : ℤ_[p]} (hc : c ≠ 0) (F : Polynomial ℤ_[p]) :
    (Polynomial.C c * F).degree = F.degree := by
  rw [Polynomial.degree_mul, Polynomial.degree_C hc, zero_add]

/-- Hausdorff separation in ℤ_[p]: divisible by every power of p ⟹ zero. -/
lemma eq_zero_of_forall_pow_dvd (x : ℤ_[p]) (hx : ∀ n : ℕ, (p : ℤ_[p]) ^ n ∣ x) :
    x = 0 := by
  have hh : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] := inferInstance
  refine hh.haus x fun n => ?_
  simp only [SModEq.sub_mem, sub_zero, ← Ideal.one_eq_top, smul_eq_mul, mul_one,
    PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact hx n

/-- Polynomial-level Hausdorff separation. -/
lemma poly_eq_zero_of_forall_pow_dvd (F : Polynomial ℤ_[p])
    (hF : ∀ n : ℕ, Polynomial.C ((p : ℤ_[p]) ^ n) ∣ F) : F = 0 := by
  ext i
  rw [Polynomial.coeff_zero]
  exact eq_zero_of_forall_pow_dvd _ fun n =>
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mp (hF n) i

/-- Completeness of ℤ_[p], packaged for coefficient sequences: a p-adically
    Cauchy sequence (successive gaps divisible by p^(n+1)) has a limit to which
    every stage is congruent mod p^n. -/
lemma exists_pow_dvd_limit (c : ℕ → ℤ_[p])
    (hc : ∀ n : ℕ, (p : ℤ_[p]) ^ (n + 1) ∣ c (n + 1) - c n) :
    ∃ L : ℤ_[p], ∀ n : ℕ, (p : ℤ_[p]) ^ n ∣ L - c n := by
  have tel : ∀ m n : ℕ, m ≤ n → (p : ℤ_[p]) ^ m ∣ c n - c m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : (p : ℤ_[p]) ^ m ∣ c (n + 1) - c n :=
        dvd_trans (pow_dvd_pow _ (by omega)) (hc n)
      have h2 := dvd_add h1 ih
      rwa [sub_add_sub_cancel] at h2
  have hpc : IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[p]) ℤ_[p] := inferInstance
  obtain ⟨L, hL⟩ := hpc.prec (f := c) (by
      intro m n hmn
      simp only [SModEq.sub_mem, ← Ideal.one_eq_top, smul_eq_mul, mul_one,
        PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact dvd_sub_comm.mp (tel m n hmn))
  refine ⟨L, fun n => ?_⟩
  have h3 := hL n
  simp only [SModEq.sub_mem, ← Ideal.one_eq_top, smul_eq_mul, mul_one,
    PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3
  exact dvd_sub_comm.mp h3

/-- Polynomial limits: a degree-bounded, p-adically Cauchy sequence of polynomials
    has a degree-bounded limit polynomial, coefficientwise. -/
lemma exists_poly_limit (d : ℕ) (P : ℕ → Polynomial ℤ_[p])
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcong : ∀ n, Polynomial.C ((p : ℤ_[p]) ^ (n + 1)) ∣ P (n + 1) - P n) :
    ∃ Q : Polynomial ℤ_[p], Q.natDegree ≤ d ∧
      ∀ n, Polynomial.C ((p : ℤ_[p]) ^ n) ∣ Q - P n := by
  have key : ∀ i : ℕ, ∃ L : ℤ_[p], ∀ n, (p : ℤ_[p]) ^ n ∣ L - (P n).coeff i := by
    intro i
    refine exists_pow_dvd_limit (fun n => (P n).coeff i) fun n => ?_
    have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp (hcong n) i
    rwa [Polynomial.coeff_sub] at h1
  choose L hL using key
  refine ⟨∑ i ∈ Finset.range (d + 1), Polynomial.monomial i (L i), ?_, ?_⟩
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
      le_trans (Polynomial.natDegree_monomial_le _)
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  · intro n
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hQc : (∑ j ∈ Finset.range (d + 1), Polynomial.monomial j (L j)).coeff i
        = if i ≤ d then L i else 0 := by
      rw [Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial]
      rw [Finset.sum_ite_eq' (Finset.range (d + 1)) i L]
      simp
    rw [Polynomial.coeff_sub, hQc]
    by_cases hid : i ≤ d
    · rw [if_pos hid]
      exact hL i n
    · rw [if_neg hid,
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg n) (by omega))]
      simp

/-! ## §1 The approximation invariant, base and inductive step -/

/-- Stage-`n` approximation data for the Hensel factor lift: monic factors reducing
    to ψ, h whose product matches `f` mod p^(n+1). -/
structure LiftState (f : Polynomial ℤ_[p]) (ψ h : Polynomial (ZMod p)) (n : ℕ)
    (g k : Polynomial ℤ_[p]) : Prop where
  gMonic : g.Monic
  kMonic : k.Monic
  gMap : g.map PadicInt.toZMod = ψ
  kMap : k.map PadicInt.toZMod = h
  dvdSub : Polynomial.C ((p : ℤ_[p]) ^ (n + 1)) ∣ f - g * k

lemma LiftState.degree_g {f : Polynomial ℤ_[p]} {ψ h : Polynomial (ZMod p)}
    {n : ℕ} {g k : Polynomial ℤ_[p]} (st : LiftState f ψ h n g k) :
    g.degree = ψ.degree := by
  rw [← st.gMap]
  exact (st.gMonic.degree_map _).symm

lemma LiftState.degree_k {f : Polynomial ℤ_[p]} {ψ h : Polynomial (ZMod p)}
    {n : ℕ} {g k : Polynomial ℤ_[p]} (st : LiftState f ψ h n g k) :
    k.degree = h.degree := by
  rw [← st.kMap]
  exact (st.kMonic.degree_map _).symm

lemma LiftState.natDegree_g {f : Polynomial ℤ_[p]} {ψ h : Polynomial (ZMod p)}
    {n : ℕ} {g k : Polynomial ℤ_[p]} (st : LiftState f ψ h n g k) :
    g.natDegree = ψ.natDegree := by
  rw [← st.gMap]
  exact (st.gMonic.natDegree_map _).symm

lemma LiftState.natDegree_k {f : Polynomial ℤ_[p]} {ψ h : Polynomial (ZMod p)}
    {n : ℕ} {g k : Polynomial ℤ_[p]} (st : LiftState f ψ h n g k) :
    k.natDegree = h.natDegree := by
  rw [← st.kMap]
  exact (st.kMonic.natDegree_map _).symm

/-- Base of the induction: monic same-degree lifts of ψ and h multiply to f mod p. -/
lemma exists_base (f : Polynomial ℤ_[p]) (ψ h : Polynomial (ZMod p))
    (hψm : ψ.Monic) (hhm : h.Monic)
    (hfact : f.map PadicInt.toZMod = ψ * h) :
    ∃ gk : Polynomial ℤ_[p] × Polynomial ℤ_[p], LiftState f ψ h 0 gk.1 gk.2 := by
  obtain ⟨g, hgmap, hgdeg, hgm⟩ := exists_monic_lift (p := p) hψm
  obtain ⟨k, hkmap, hkdeg, hkm⟩ := exists_monic_lift (p := p) hhm
  refine ⟨(g, k), ⟨hgm, hkm, hgmap, hkmap, ?_⟩⟩
  have h0 : (f - g * k).map PadicInt.toZMod = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, hfact, hgmap, hkmap, sub_self]
  simpa using (map_toZMod_eq_zero_iff _).mp h0

/-- The inductive step: correct a stage-`n` approximation by a Bézout-controlled
    multiple of p^(n+1), improving the congruence to p^(n+2) while moving each
    factor only by a multiple of p^(n+1). -/
lemma exists_step (f : Polynomial ℤ_[p]) (ψ h : Polynomial (ZMod p))
    (hfm : f.Monic) (hψm : ψ.Monic) (hhm : h.Monic)
    (hcop : IsCoprime ψ h) (hfact : f.map PadicInt.toZMod = ψ * h)
    {n : ℕ} {g k : Polynomial ℤ_[p]} (st : LiftState f ψ h n g k) :
    ∃ gk' : Polynomial ℤ_[p] × Polynomial ℤ_[p],
      LiftState f ψ h (n + 1) gk'.1 gk'.2 ∧
      Polynomial.C ((p : ℤ_[p]) ^ (n + 1)) ∣ gk'.1 - g ∧
      Polynomial.C ((p : ℤ_[p]) ^ (n + 1)) ∣ gk'.2 - k := by
  classical
  obtain ⟨w, hw⟩ := st.dvdSub
  have hψ0 : ψ ≠ 0 := hψm.ne_zero
  have hh0 : h ≠ 0 := hhm.ne_zero
  have hgdeg : g.degree = ψ.degree := st.degree_g
  have hkdeg : k.degree = h.degree := st.degree_k
  have hfdeg : f.degree = ψ.degree + h.degree := by
    rw [← hfm.degree_map PadicInt.toZMod, hfact, Polynomial.degree_mul]
  have hCp : ((p : ℤ_[p]) ^ (n + 1)) ≠ 0 := pow_ne_zero _ cast_p_ne_zero
  -- degree of the defect
  have hwdeg : w.degree < f.degree := by
    rcases eq_or_ne w 0 with rfl | hw0
    · rw [Polynomial.degree_zero]
      exact Ne.bot_lt fun hbot => hfm.ne_zero (Polynomial.degree_eq_bot.mp hbot)
    · calc w.degree = (f - g * k).degree := by rw [hw, degree_C_mul' hCp]
        _ < f.degree := Polynomial.degree_sub_lt
            (by rw [hfdeg, Polynomial.degree_mul, hgdeg, hkdeg]) hfm.ne_zero
            (by rw [hfm.leadingCoeff, (st.gMonic.mul st.kMonic).leadingCoeff])
  -- Bézout correction
  obtain ⟨a, b, hab⟩ := hcop
  set wbar := w.map PadicInt.toZMod with hwbar_def
  have hwbar_deg : wbar.degree < ψ.degree + h.degree :=
    lt_of_le_of_lt Polynomial.degree_map_le (hfdeg ▸ hwdeg)
  set u := (wbar * b) %ₘ ψ with hu_def
  set v := wbar * a + ((wbar * b) /ₘ ψ) * h with hv_def
  have hdiv : u + ψ * ((wbar * b) /ₘ ψ) = wbar * b := by
    rw [hu_def]; exact Polynomial.modByMonic_add_div (wbar * b) ψ
  have hkey : u * h + v * ψ = wbar := by
    rw [hv_def]
    linear_combination h * hdiv + wbar * hab
  have hudeg : u.degree < ψ.degree := Polynomial.degree_modByMonic_lt _ hψm
  have hvdeg : v.degree < h.degree := by
    have hvψ : v * ψ = wbar - u * h := by linear_combination hkey
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0, Polynomial.degree_zero]
      exact Ne.bot_lt fun hbot => hh0 (Polynomial.degree_eq_bot.mp hbot)
    · have hψbot : ψ.degree ≠ ⊥ := fun hbot => hψ0 (Polynomial.degree_eq_bot.mp hbot)
      have hhbot : h.degree ≠ ⊥ := fun hbot => hh0 (Polynomial.degree_eq_bot.mp hbot)
      have h2 : v.degree + ψ.degree < h.degree + ψ.degree := by
        rw [← Polynomial.degree_mul, hvψ]
        refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
        · exact lt_of_lt_of_le hwbar_deg (le_of_eq (add_comm _ _))
        · rw [Polynomial.degree_mul, add_comm h.degree ψ.degree]
          exact (WithBot.add_lt_add_iff_right hhbot).mpr hudeg
      exact (WithBot.add_lt_add_iff_right hψbot).mp h2
  -- lift the corrections
  obtain ⟨U, hUmap, hUdeg⟩ := exists_map_toZMod_eq (p := p) u
  obtain ⟨V, hVmap, hVdeg⟩ := exists_map_toZMod_eq (p := p) v
  set c : Polynomial ℤ_[p] := Polynomial.C ((p : ℤ_[p]) ^ (n + 1)) with hc_def
  have hcmap : c.map PadicInt.toZMod = 0 := by
    rw [hc_def, Polynomial.map_C, map_pow, toZMod_natCast_p,
      zero_pow (Nat.succ_ne_zero n), Polynomial.C_0]
  refine ⟨(g + c * U, k + c * V), ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨U, by ring⟩, ⟨V, by ring⟩⟩
  · -- monic
    refine st.gMonic.add_of_left ?_
    have hcU : (c * U).degree = U.degree := by rw [hc_def, degree_C_mul' hCp]
    rw [hcU, hUdeg, hgdeg]
    exact hudeg
  · refine st.kMonic.add_of_left ?_
    have hcV : (c * V).degree = V.degree := by rw [hc_def, degree_C_mul' hCp]
    rw [hcV, hVdeg, hkdeg]
    exact hvdeg
  · -- reduction unchanged
    rw [Polynomial.map_add, Polynomial.map_mul, hcmap, zero_mul, add_zero, st.gMap]
  · rw [Polynomial.map_add, Polynomial.map_mul, hcmap, zero_mul, add_zero, st.kMap]
  · -- improved congruence
    have hgoal : f - (g + c * U) * (k + c * V)
        = c * (w - (U * k + V * g)) - (c * c) * (U * V) := by
      linear_combination hw
    rw [hgoal]
    refine dvd_sub ?_ ?_
    · -- the linear term: its residue vanishes by the Bézout identity
      have hmapz : (w - (U * k + V * g)).map PadicInt.toZMod = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
          hUmap, hVmap, st.kMap, st.gMap, hkey, hwbar_def, sub_self]
      obtain ⟨t, ht⟩ := (map_toZMod_eq_zero_iff _).mp hmapz
      refine ⟨t, ?_⟩
      have hCC : c * Polynomial.C (p : ℤ_[p]) = Polynomial.C ((p : ℤ_[p]) ^ (n + 1 + 1)) := by
        rw [hc_def, ← Polynomial.C_mul, ← pow_succ]
      rw [ht, ← mul_assoc, hCC]
    · -- the quadratic term carries p^(2n+2)
      have hexp : (n + 1) + (n + 1) = (n + 1 + 1) + n := by omega
      have hcc : c * c
          = Polynomial.C ((p : ℤ_[p]) ^ (n + 1 + 1)) * Polynomial.C ((p : ℤ_[p]) ^ n) := by
        rw [hc_def, ← Polynomial.C_mul, ← Polynomial.C_mul, ← pow_add, ← pow_add, hexp]
      exact dvd_mul_of_dvd_left ⟨_, hcc⟩ _

/-! ## §2 The approximation sequence, its limit, and U2a -/

/-- The full approximation tower, built by recursion with choice from
    `exists_base` and `exists_step`. -/
noncomputable def liftSeq (f : Polynomial ℤ_[p]) (ψ h : Polynomial (ZMod p))
    (hfm : f.Monic) (hψm : ψ.Monic) (hhm : h.Monic)
    (hcop : IsCoprime ψ h) (hfact : f.map PadicInt.toZMod = ψ * h) :
    (n : ℕ) → {gk : Polynomial ℤ_[p] × Polynomial ℤ_[p] // LiftState f ψ h n gk.1 gk.2}
  | 0 => ⟨(exists_base f ψ h hψm hhm hfact).choose,
      (exists_base f ψ h hψm hhm hfact).choose_spec⟩
  | n + 1 =>
    ⟨(exists_step f ψ h hfm hψm hhm hcop hfact
        (liftSeq f ψ h hfm hψm hhm hcop hfact n).2).choose,
      (exists_step f ψ h hfm hψm hhm hcop hfact
        (liftSeq f ψ h hfm hψm hhm hcop hfact n).2).choose_spec.1⟩

/-- Consecutive stages of the tower are congruent mod p^(n+1). -/
lemma liftSeq_succ_dvd (f : Polynomial ℤ_[p]) (ψ h : Polynomial (ZMod p))
    (hfm : f.Monic) (hψm : ψ.Monic) (hhm : h.Monic)
    (hcop : IsCoprime ψ h) (hfact : f.map PadicInt.toZMod = ψ * h) (n : ℕ) :
    Polynomial.C ((p : ℤ_[p]) ^ (n + 1)) ∣
      (liftSeq f ψ h hfm hψm hhm hcop hfact (n + 1)).1.1
        - (liftSeq f ψ h hfm hψm hhm hcop hfact n).1.1 ∧
    Polynomial.C ((p : ℤ_[p]) ^ (n + 1)) ∣
      (liftSeq f ψ h hfm hψm hhm hcop hfact (n + 1)).1.2
        - (liftSeq f ψ h hfm hψm hhm hcop hfact n).1.2 :=
  (exists_step f ψ h hfm hψm hhm hcop hfact
    (liftSeq f ψ h hfm hψm hhm hcop hfact n).2).choose_spec.2

end HenLift

open HenLift in
open Polynomial in
/-- **D12R-U2a (HEN-LIFT existence; HL-a).** Statement VERBATIM from
    HDISCHARGE_H3 §2.2.  A coprime monic factorization of the reduction of a monic
    f ∈ ℤ_[p][X] lifts to a monic factorization of f itself. -/
theorem henLift_padic (p : ℕ) [hp : Fact p.Prime] (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (ψ h : Polynomial (ZMod p)) (hψm : ψ.Monic) (hhm : h.Monic)
    (hcop : IsCoprime ψ h)
    (hfact : f.map (PadicInt.toZMod) = ψ * h) :
    ∃ g k : Polynomial ℤ_[p], g.Monic ∧ k.Monic ∧ f = g * k ∧
      g.map PadicInt.toZMod = ψ ∧ k.map PadicInt.toZMod = h := by
  classical
  set S := liftSeq f ψ h hf hψm hhm hcop hfact with hS_def
  -- limit of the g-column
  obtain ⟨G, hGdeg, hG⟩ := exists_poly_limit ψ.natDegree (fun n => (S n).1.1)
    (fun n => le_of_eq (S n).2.natDegree_g)
    (fun n => (liftSeq_succ_dvd f ψ h hf hψm hhm hcop hfact n).1)
  -- limit of the k-column
  obtain ⟨K, hKdeg, hK⟩ := exists_poly_limit h.natDegree (fun n => (S n).1.2)
    (fun n => le_of_eq (S n).2.natDegree_k)
    (fun n => (liftSeq_succ_dvd f ψ h hf hψm hhm hcop hfact n).2)
  -- reductions of the limits
  have hGmap : G.map PadicInt.toZMod = ψ := by
    have h1 : Polynomial.C (p : ℤ_[p]) ∣ G - (S 1).1.1 := by simpa using hG 1
    have h2 := (map_toZMod_eq_zero_iff _).mpr h1
    rw [Polynomial.map_sub, sub_eq_zero] at h2
    rw [h2, (S 1).2.gMap]
  have hKmap : K.map PadicInt.toZMod = h := by
    have h1 : Polynomial.C (p : ℤ_[p]) ∣ K - (S 1).1.2 := by simpa using hK 1
    have h2 := (map_toZMod_eq_zero_iff _).mpr h1
    rw [Polynomial.map_sub, sub_eq_zero] at h2
    rw [h2, (S 1).2.kMap]
  -- the limits are monic
  have hGmonic : G.Monic := by
    have hcoeff : G.coeff ψ.natDegree = 1 := by
      have hx : ∀ n : ℕ, (p : ℤ_[p]) ^ n ∣ G.coeff ψ.natDegree - 1 := by
        intro n
        have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp (hG n) ψ.natDegree
        have hlead : ((S n).1.1).coeff ψ.natDegree = 1 := by
          rw [← (S n).2.natDegree_g]
          exact (S n).2.gMonic.coeff_natDegree
        rwa [Polynomial.coeff_sub, hlead] at h1
      exact sub_eq_zero.mp (eq_zero_of_forall_pow_dvd _ hx)
    exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hGdeg hcoeff
  have hKmonic : K.Monic := by
    have hcoeff : K.coeff h.natDegree = 1 := by
      have hx : ∀ n : ℕ, (p : ℤ_[p]) ^ n ∣ K.coeff h.natDegree - 1 := by
        intro n
        have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp (hK n) h.natDegree
        have hlead : ((S n).1.2).coeff h.natDegree = 1 := by
          rw [← (S n).2.natDegree_k]
          exact (S n).2.kMonic.coeff_natDegree
        rwa [Polynomial.coeff_sub, hlead] at h1
      exact sub_eq_zero.mp (eq_zero_of_forall_pow_dvd _ hx)
    exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hKdeg hcoeff
  -- the limits multiply to f
  have hprod : f = G * K := by
    have hFz : f - G * K = 0 := by
      refine poly_eq_zero_of_forall_pow_dvd _ fun n => ?_
      have d1 : Polynomial.C ((p : ℤ_[p]) ^ n) ∣ f - (S n).1.1 * (S n).1.2 :=
        dvd_trans (map_dvd Polynomial.C (pow_dvd_pow _ (Nat.le_succ n))) (S n).2.dvdSub
      have d2 : Polynomial.C ((p : ℤ_[p]) ^ n) ∣ (S n).1.1 * (S n).1.2 - G * K := by
        have e : (S n).1.1 * (S n).1.2 - G * K
            = (S n).1.1 * ((S n).1.2 - K) + ((S n).1.1 - G) * K := by ring
        rw [e]
        exact dvd_add ((dvd_sub_comm.mp (hK n)).mul_left _)
          ((dvd_sub_comm.mp (hG n)).mul_right _)
      have h3 := dvd_add d1 d2
      rwa [sub_add_sub_cancel] at h3
    exact (sub_eq_zero.mp hFz)
  exact ⟨G, K, hGmonic, hKmonic, hprod, hGmap, hKmap⟩

open HenLift in
open Polynomial in
set_option linter.unusedVariables false in
/-- **D12R-U2b (HEN-LIFT uniqueness; HL-b).**  Statement adjudicated at E-phase per
    the blueprint charge: same hypotheses as `henLift_padic`; two monic lift pairs
    with equal reductions are equal.  (The hypothesis row mirrors U2a verbatim, so
    some rows are unused by the proof; the linter is silenced rather than the
    statement thinned.) -/
theorem henLift_padic_unique (p : ℕ) [hp : Fact p.Prime] (f : Polynomial ℤ_[p])
    (hf : f.Monic) (ψ h : Polynomial (ZMod p)) (hψm : ψ.Monic) (hhm : h.Monic)
    (hcop : IsCoprime ψ h)
    (g k g' k' : Polynomial ℤ_[p])
    (hg : g.Monic) (hk : k.Monic) (hg' : g'.Monic) (hk' : k'.Monic)
    (hfgk : f = g * k) (hfgk' : f = g' * k')
    (hgψ : g.map PadicInt.toZMod = ψ) (hkh : k.map PadicInt.toZMod = h)
    (hgψ' : g'.map PadicInt.toZMod = ψ) (hkh' : k'.map PadicInt.toZMod = h) :
    g = g' ∧ k = k' := by
  classical
  have main : ∀ n : ℕ, Polynomial.C ((p : ℤ_[p]) ^ n) ∣ g - g' ∧
      Polynomial.C ((p : ℤ_[p]) ^ n) ∣ k - k' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩ := ih
      have hzero : g * k - g' * k' = 0 := by rw [← hfgk, ← hfgk', sub_self]
      have hfactored : Polynomial.C ((p : ℤ_[p]) ^ n) * (g * β + α * k') = 0 := by
        linear_combination hzero - g * hβ - k' * hα
      have hsum : g * β + α * k' = 0 := by
        rcases mul_eq_zero.mp hfactored with hC | hok
        · exact absurd (Polynomial.C_eq_zero.mp hC) (pow_ne_zero _ cast_p_ne_zero)
        · exact hok
      have hred : ψ * (β.map PadicInt.toZMod) + (α.map PadicInt.toZMod) * h = 0 := by
        have h1 := congrArg (Polynomial.map PadicInt.toZMod) hsum
        simpa [Polynomial.map_add, Polynomial.map_mul, hgψ, hkh'] using h1
      have hψα : ψ ∣ (α.map PadicInt.toZMod) * h :=
        ⟨-(β.map PadicInt.toZMod), by linear_combination hred⟩
      have hψdvd : ψ ∣ α.map PadicInt.toZMod := hcop.dvd_of_dvd_mul_right hψα
      have hαdeg : (α.map PadicInt.toZMod).degree < ψ.degree := by
        rcases eq_or_ne α 0 with rfl | hα0
        · rw [Polynomial.map_zero, Polynomial.degree_zero]
          exact Ne.bot_lt fun hbot => hψm.ne_zero (Polynomial.degree_eq_bot.mp hbot)
        · refine lt_of_le_of_lt Polynomial.degree_map_le ?_
          have hdeg_g : g.degree = ψ.degree := by
            rw [← hgψ]; exact (hg.degree_map _).symm
          have hdeg_g' : g'.degree = ψ.degree := by
            rw [← hgψ']; exact (hg'.degree_map _).symm
          have hgg' : (g - g').degree < ψ.degree := by
            calc (g - g').degree < g.degree :=
                  Polynomial.degree_sub_lt (hdeg_g.trans hdeg_g'.symm) hg.ne_zero
                    (by rw [hg.leadingCoeff, hg'.leadingCoeff])
              _ = ψ.degree := hdeg_g
          have hαd : (g - g').degree = α.degree := by
            rw [hα, degree_C_mul' (pow_ne_zero _ cast_p_ne_zero)]
          rw [← hαd]
          exact hgg'
      have hα0 : α.map PadicInt.toZMod = 0 :=
        Polynomial.eq_zero_of_dvd_of_degree_lt hψdvd hαdeg
      have hβ0 : β.map PadicInt.toZMod = 0 := by
        have h1 : ψ * (β.map PadicInt.toZMod) = 0 := by
          rw [hα0] at hred
          simpa using hred
        rcases mul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 hψm.ne_zero
        · exact h2
      obtain ⟨α', hα'⟩ := (map_toZMod_eq_zero_iff _).mp hα0
      obtain ⟨β', hβ'⟩ := (map_toZMod_eq_zero_iff _).mp hβ0
      constructor
      · exact ⟨α', by rw [hα, hα', pow_succ, Polynomial.C_mul]; ring⟩
      · exact ⟨β', by rw [hβ, hβ', pow_succ, Polynomial.C_mul]; ring⟩
  exact ⟨sub_eq_zero.mp (poly_eq_zero_of_forall_pow_dvd _ fun n => (main n).1),
    sub_eq_zero.mp (poly_eq_zero_of_forall_pow_dvd _ fun n => (main n).2)⟩

open Polynomial in
/-- **D12R-U2c, irreducibility clause.**  A monic lift of an irreducible reduction
    is irreducible. -/
theorem henLift_padic_irreducible (p : ℕ) [hp : Fact p.Prime]
    (g : Polynomial ℤ_[p]) (hg : g.Monic) (ψ : Polynomial (ZMod p))
    (hmap : g.map PadicInt.toZMod = ψ) (hψ : Irreducible ψ) :
    Irreducible g :=
  Polynomial.Monic.irreducible_of_irreducible_map PadicInt.toZMod g hg
    (by rw [hmap]; exact hψ)

open HenLift in
open Polynomial in
/-- **D12R-U2c, (E,F) clause, residue-ring identification.**  The residue ring
    ℤ_[p][X]/(p, g) of the g-order is the mod-p root ring 𝔽_p[X]/(ψ); with ψ
    irreducible the latter is a field (see `henLift_padic_residue_isField`), so p
    alone generates the maximal ideal above (p) in the order: the E = 1 witness of
    the unramified read-off, in the blueprint-sanctioned numerical form. -/
theorem henLift_padic_residue_equiv (p : ℕ) [hp : Fact p.Prime]
    (g : Polynomial ℤ_[p]) (hg : g.Monic) (ψ : Polynomial (ZMod p))
    (hmap : g.map PadicInt.toZMod = ψ) :
    Nonempty ((Polynomial ℤ_[p] ⧸
        (Ideal.span {Polynomial.C (p : ℤ_[p]), g} : Ideal (Polynomial ℤ_[p])))
      ≃+* AdjoinRoot ψ) := by
  classical
  set Φ : Polynomial ℤ_[p] →+* AdjoinRoot ψ :=
    (AdjoinRoot.mk ψ).comp (Polynomial.mapRingHom PadicInt.toZMod) with hΦ_def
  have hsurj : Function.Surjective Φ := by
    rw [hΦ_def, RingHom.coe_comp]
    exact AdjoinRoot.mk_surjective.comp
      (Polynomial.map_surjective _ (ZMod.ringHom_surjective PadicInt.toZMod))
  have hker : RingHom.ker Φ = Ideal.span {Polynomial.C (p : ℤ_[p]), g} := by
    apply le_antisymm
    · intro F hF
      rw [RingHom.mem_ker, hΦ_def, RingHom.comp_apply, Polynomial.coe_mapRingHom,
        AdjoinRoot.mk_eq_zero] at hF
      obtain ⟨tbar, htbar⟩ := hF
      obtain ⟨T, hTmap, -⟩ := exists_map_toZMod_eq (p := p) tbar
      have hz : (F - g * T).map PadicInt.toZMod = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hmap, hTmap, htbar, sub_self]
      obtain ⟨s, hs⟩ := (map_toZMod_eq_zero_iff _).mp hz
      rw [Ideal.mem_span_pair]
      exact ⟨s, T, by linear_combination -hs⟩
    · rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [SetLike.mem_coe, RingHom.mem_ker, hΦ_def, RingHom.comp_apply,
          Polynomial.coe_mapRingHom, Polynomial.map_C, toZMod_natCast_p, Polynomial.C_0,
          map_zero]
      · rw [SetLike.mem_coe, RingHom.mem_ker, hΦ_def, RingHom.comp_apply,
          Polynomial.coe_mapRingHom, hmap, AdjoinRoot.mk_self]
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)⟩

open Polynomial in
/-- **D12R-U2c, (E,F) clause, field witness.**  For ψ irreducible the residue ring
    is a field — combined with `henLift_padic_residue_equiv` this is the E = 1
    numerical witness. -/
theorem henLift_padic_residue_isField (p : ℕ) [hp : Fact p.Prime]
    (ψ : Polynomial (ZMod p)) (hψ : Irreducible ψ) :
    IsField (AdjoinRoot ψ) := by
  have : Fact (Irreducible ψ) := ⟨hψ⟩
  exact Field.toIsField (AdjoinRoot ψ)

open Polynomial in
/-- **D12R-U2c, (E,F) clause, residue-degree witness.**  The residue field has
    𝔽_p-dimension deg ψ: the F = deg ψ numerical witness. -/
theorem henLift_padic_residue_finrank (p : ℕ) [hp : Fact p.Prime]
    (ψ : Polynomial (ZMod p)) (hψ : Irreducible ψ) :
    Module.finrank (ZMod p) (AdjoinRoot ψ) = ψ.natDegree := by
  have h1 := (AdjoinRoot.powerBasis (f := ψ) hψ.ne_zero).finrank
  rwa [AdjoinRoot.powerBasis_dim] at h1

open Polynomial in
/-- **D12R-U2c, packaged read-off.**  Irreducibility of the lifted factor plus the
    unramified/(E,F) clause in residue-degree-only numerical form: the g-order's
    residue ring ℤ_[p][X]/(p, g) is the field 𝔽_p[X]/(ψ) (E = 1: p generates the
    maximal ideal there) of 𝔽_p-dimension deg ψ (F = deg ψ).  The
    `IsUnramified`-vocabulary upgrade is the recorded stretch goal, NOT claimed. -/
theorem henLift_padic_readoff (p : ℕ) [hp : Fact p.Prime]
    (g : Polynomial ℤ_[p]) (hg : g.Monic) (ψ : Polynomial (ZMod p))
    (hmap : g.map PadicInt.toZMod = ψ) (hψ : Irreducible ψ) :
    Irreducible g ∧
    Nonempty ((Polynomial ℤ_[p] ⧸
        (Ideal.span {Polynomial.C (p : ℤ_[p]), g} : Ideal (Polynomial ℤ_[p])))
      ≃+* AdjoinRoot ψ) ∧
    IsField (AdjoinRoot ψ) ∧
    Module.finrank (ZMod p) (AdjoinRoot ψ) = ψ.natDegree :=
  ⟨henLift_padic_irreducible p g hg ψ hmap hψ,
    henLift_padic_residue_equiv p g hg ψ hmap,
    henLift_padic_residue_isField p ψ hψ,
    henLift_padic_residue_finrank p ψ hψ⟩

end LeanUrat.Scaffold.HD3

