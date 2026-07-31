/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC1.DefsSpine
import LeanUrat.Moves.L5_landVertexDigit
import LeanUrat.Moves.ResVal

/-!
# HC1.K1_vertexPin — the read-indexed D.8 vertex pin and the twist-class bridge

K1 KERNEL bridge (2026-07-28; ADDITIVE unit — no existing statement or Defs change).

**The twist class** (S7 leg (c), S8's `TvecUnitLaw` leg, S11 Part 1's residual set) is
blocked by ONE interface under-recording, certified on both sides (S8's in-file dual-audited
twist symmetry; the S7 escalation scratch's (⋆)): `TransitionCoreL.child_dig_frame` supplies
its frame-unit exponent `mfun : ℤ → ℤ` EXISTENTIALLY, so the child residual normalization is
free to twist by `z̄^{λ·e'·w}` — while the note pins it (D.7(vi), MOVES 2395–2418:
`V′ := Π in_{w′}(ũ_i)^{s·b_i}·in_{w′}(Φ)^{t} … u₀ := V′^{−h′} (explicit, no choice);
z′ := u₀·Y′^{e′}`; D.8's (VERTEX) carries the explicit unit `z̄^{−μm̂}`).

**This file** records the pin as a NAMED Prop (`VertexPin` — `child_dig_frame` with the
D.7(vi) NORMALIZED exponent, `mfun ≡ 0`: the child digit of a parent-frame coefficient IS
its parent ψ-digit) and PROVES the twist-class bridges from it:

* `K1_tvecUnitLaw_of_pin` — StageCoreL σ + TransitionCoreL + pin ⟹ `TvecUnitLaw σ'`:
  EXACTLY the S8 conjunct the twist symmetry proved underivable from the recorded class;
  with the pin, the S8 kernel's `E` vanishes and the product law closes. S9d discharges
  S8's homed conjunct by verifying the pin on the constructed child and consuming this.
* `K1_coeffLocC_of_pin` — same hypotheses ⟹ CoeffLocLaw conjunct (c) (the z′-pin
  `z′ = V′^{−h′}·Y′^{e′}`): EXACTLY the S7 scratch's (⋆) residual; the witness vector is
  `−h′·(transported parent T-vector)` and the pin kills its scalar `z̄^{h′·E}`.
  With the scratch's PROVED legs (a)/(b) this completes `CoeffLocLaw σ'` — S7's wall.
* `K1_frameVertexDigit` — the PROVED D.8 assets, re-keyed to HC-1's own interface: what
  `L5_landVertexDigit` pins, AT THE PAIR HC-1 RECORDS (`TransHyp.hlift : IsStandardLift` —
  the FRAME pair; contrast HC-2's run-level `IsNodeLift` read pair, whose vertex law is
  the HC2/K1_vertexPin kernel). One-line wrapper: gives every HC-1 unit the vertex digit
  with its explicit normalization unit `z̄^{μ·t·h·g}` without re-deriving the hzbar form.

FAITHFULNESS FLAG (semantic guardian): `VertexPin` is a NAMED HYPOTHESIS Prop (never an
axiom), the K1 rendering of the D.7(vi) pinned normalization. Its non-vacuity obligation
sits with S9d (the constructed child realizes it by construction — blueprint §9.5); if
S9's construction realizes a different explicit exponent, the bridges re-instantiate at
the corrected pin (the proofs consume the pin only through `pinDigit`).
S11a NOTE: {TvecUnitLaw, CoeffLocLaw} is precisely the S11 kernel's twist-class residual
that F-5's `MoveWitness` enrichment carries; these bridges let the enriched witness be
BUILT (S9d) rather than assumed, shrinking the S11a certificate's independent content to
the non-twist legs (the escalation's verified transport).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.HC1

open Polynomial LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## The pin -/

/-- **THE READ-INDEXED D.8 VERTEX PIN** (D.7(vi)'s pinned normalization, as an interface
record): the child residual of every parent-frame coefficient is the monomial unit at the
forced position whose scalar IS the parent ψ-digit — `child_dig_frame` with the frame-unit
exponent pinned to the normalized value (`mfun ≡ 0`). The S8/S7(c)/S11 twist symmetry
(`mfun ↦ mfun + λe′·id`) moves this Prop, so recording it kills the twist class — the
bridges below. Realized BY CONSTRUCTION on S9d's child (the `V′`-normalized residual). -/
def VertexPin (σ σ' : Stage p F) (Φhat : Polynomial ℤ_[p]) (zbar : Fˣ) : Prop :=
  ∀ B : Polynomial ℤ_[p], B ≠ 0 → inC Φhat B →
    ∃ c' : (↥σ'.K)ˣ,
      σ'.R B = LaurentPolynomial.C ((c' : ↥σ'.K)) *
          LaurentPolynomial.T (- σ'.t * σ.w B) ∧
      ((c' : ↥σ'.K) : F) = σ.digPrime zbar B

/-- The pin refines the recorded transition data: it IS `child_dig_frame`'s clause with
`mfun := 0` (so a pinned transition satisfies the recorded interface verbatim). -/
lemma VertexPin.to_child_dig_frame {σ σ' : Stage p F} {Φhat : Polynomial ℤ_[p]}
    {zbar : Fˣ} (pin : VertexPin σ σ' Φhat zbar) :
    ∃ mfun : ℤ → ℤ, ∀ B, B ≠ 0 → inC Φhat B →
      ∃ c' : (↥σ'.K)ˣ,
        σ'.R B = LaurentPolynomial.C (c' : ↥σ'.K) *
            LaurentPolynomial.T (- σ'.t * σ.w B) ∧
        ((c' : ↥σ'.K) : F) = σ.digPrime zbar B * ((zbar ^ ((0 : ℤ → ℤ) (σ.w B)) : Fˣ) : F) := by
  refine ⟨0, fun B hB0 hBC => ?_⟩
  obtain ⟨c', hc', hval⟩ := pin B hB0 hBC
  exact ⟨c', hc', by simpa using hval⟩

/-! ## The proved frame-pair D.8 asset, re-keyed to HC-1's interface -/

/-- What the proved D.8 assets pin, at the pair HC-1 records: the VERTEX digit with its
EXPLICIT normalization unit, keyed to `TransHyp` (whose `hlift` is the FRAME-pair
`IsStandardLift` — D.5's displayed lift). `σ.R f = ψ^μ·q`, `ψ ∤ q`, and
`dig′(B_μ) = z̄^{μ·t·h·g}·q(z̄)` — §B2-DEF D.8 (VERTEX), pass-10 finding 2's unit intact. -/
theorem K1_frameVertexDigit (σ : Stage p F) {ψ : Polynomial ↥σ.K} {g : ℕ}
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (th : TransHyp σ ψ g Φhat e' h' zbar)
    (f : Polynomial ℤ_[p]) (hf : f ≠ 0) (μ : ℕ) (a : ℤ) (Ranch : Polynomial ↥σ.K)
    (hanch : HasAnchorK (σ.R f) a Ranch) (hord : OrdPsiPoly ψ Ranch μ)
    (B : ℕ → Polynomial ℤ_[p]) (N : ℕ) (hdev : IsDevelopment Φhat f B N) :
    ∃ q : LaurentPolynomial ↥σ.K,
      σ.R f = (Polynomial.toLaurent ψ) ^ μ * q ∧ ¬ (Polynomial.toLaurent ψ ∣ q) ∧
      σ.digPrime zbar (B μ) =
        ((zbar ^ ((μ : ℤ) * σ.t * (σ.h : ℤ) * (g : ℤ)) : Fˣ) : F) *
          LaurentPolynomial.eval₂ σ.K.subtype zbar q := by
  have hzbar : Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0 := by
    have h := th.hroot
    rwa [Polynomial.aeval_def, Polynomial.eval₂_map, Algebra.algebraMap_self,
      RingHom.id_comp] at h
  exact L5_landVertexDigit σ ψ g th.hdeg th.hmonic th.hirr th.hne_z Φhat th.hlift
    zbar hzbar f hf μ a Ranch hanch hord B N hdev

/-! ## Units-of-Laurent arithmetic (tUnit calculus + the two-variable monomial unit) -/

private lemma tUnit_val' (R : Type*) [CommRing R] (a : ℤ) :
    ((tUnit R a : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = LaurentPolynomial.T a := rfl

private lemma tUnit_mul' (R : Type*) [CommRing R] (a b : ℤ) :
    tUnit R a * tUnit R b = tUnit R (a + b) := by
  apply Units.ext
  show LaurentPolynomial.T a * LaurentPolynomial.T b = LaurentPolynomial.T (a + b)
  rw [LaurentPolynomial.T_add]

private lemma tUnit_zero' (R : Type*) [CommRing R] : tUnit R 0 = 1 := by
  apply Units.ext
  show LaurentPolynomial.T 0 = 1
  rw [LaurentPolynomial.T_zero]

private lemma tUnit_inv' (R : Type*) [CommRing R] (a : ℤ) :
    (tUnit R a)⁻¹ = tUnit R (-a) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [tUnit_mul', add_neg_cancel, tUnit_zero']

/-- The two-variable monomial unit of `LTwo K`: value `C (C c · T k) · T w` (inner
position `k`, outer weight `w`, scalar the unit `c`) — the normal form of every
`grRes`-unit this file manipulates. -/
private noncomputable def mUnit (K : Type*) [Field K] (c : Kˣ) (k w : ℤ) : (LTwo K)ˣ :=
  (Units.map (LaurentPolynomial.C : LaurentPolynomial K →+* LTwo K).toMonoidHom
      ((Units.map (LaurentPolynomial.C : K →+* LaurentPolynomial K).toMonoidHom c)
        * tUnit K k))
    * tUnit (LaurentPolynomial K) w

private lemma mUnit_val (K : Type*) [Field K] (c : Kˣ) (k w : ℤ) :
    ((mUnit K c k w : (LTwo K)ˣ) : LTwo K)
      = LaurentPolynomial.C (LaurentPolynomial.C (c : K) * LaurentPolynomial.T k) *
          LaurentPolynomial.T w := rfl

private lemma mUnit_one (K : Type*) [Field K] : mUnit K 1 0 0 = 1 := by
  apply Units.ext
  rw [mUnit_val]
  simp

private lemma mUnit_mul (K : Type*) [Field K] (c c' : Kˣ) (k k' w w' : ℤ) :
    mUnit K c k w * mUnit K c' k' w' = mUnit K (c * c') (k + k') (w + w') := by
  apply Units.ext
  rw [Units.val_mul, mUnit_val, mUnit_val, mUnit_val, mul_mul_mul_comm, ← map_mul,
    ← LaurentPolynomial.T_add]
  congr 2
  rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add, Units.val_mul]

private lemma mUnit_inv (K : Type*) [Field K] (c : Kˣ) (k w : ℤ) :
    (mUnit K c k w)⁻¹ = mUnit K c⁻¹ (-k) (-w) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [mUnit_mul, mul_inv_cancel, add_neg_cancel, add_neg_cancel, mUnit_one]

private lemma mUnit_pow (K : Type*) [Field K] (c : Kˣ) (k w : ℤ) (n : ℕ) :
    mUnit K c k w ^ n = mUnit K (c ^ n) (k * n) (w * n) := by
  induction n with
  | zero => simp [mUnit_one]
  | succ m ih =>
      rw [pow_succ, ih, mUnit_mul, ← pow_succ]
      congr 1 <;> push_cast <;> ring

private lemma mUnit_zpow (K : Type*) [Field K] (c : Kˣ) (k w : ℤ) (n : ℤ) :
    mUnit K c k w ^ n = mUnit K (c ^ n) (k * n) (w * n) := by
  cases n with
  | ofNat m =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, mUnit_pow]
  | negSucc m =>
      have hk : k * Int.negSucc m = -(k * ((m : ℤ) + 1)) := by
        rw [Int.negSucc_eq]; ring
      have hw : w * Int.negSucc m = -(w * ((m : ℤ) + 1)) := by
        rw [Int.negSucc_eq]; ring
      have hm : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [zpow_negSucc, zpow_negSucc, mUnit_pow, mUnit_inv, hk, hw, hm]

private lemma prod_mUnit_zpow {K : Type*} [Field K] {ι : Type*} (s : Finset ι)
    (c : ι → Kˣ) (k w a : ι → ℤ) :
    (∏ i ∈ s, mUnit K (c i) (k i) (w i) ^ (a i))
      = mUnit K (∏ i ∈ s, c i ^ a i) (∑ i ∈ s, k i * a i) (∑ i ∈ s, w i * a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [mUnit_one]
  | insert i s his ih =>
      rw [Finset.prod_insert his, ih, mUnit_zpow, mUnit_mul, Finset.prod_insert his,
        Finset.sum_insert his, Finset.sum_insert his]

/-- `locT` in monomial-unit normal form. -/
private lemma mUnit_locT (K : Type*) [Field K] : mUnit K 1 0 1 = locT K := by
  apply Units.ext
  rw [mUnit_val]
  show _ = LaurentPolynomial.T 1
  simp

/-- `C zvar` (the inner variable, the z′-pin's target value) in normal form. -/
private lemma mUnit_zvar (K : Type*) [Field K] :
    ((mUnit K 1 1 0 : (LTwo K)ˣ) : LTwo K) = LaurentPolynomial.C (zvar K) := by
  rw [mUnit_val]
  simp [zvar]

/-! ## Fin-indexed products over lists -/

private lemma fin_prod_get {M : Type*} [CommMonoid M] {α : Type*} (l : List α) (g : α → M) :
    ∏ i : Fin l.length, g (l.get i) = (l.map g).prod := by
  conv_rhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

private lemma fin_sum_get {M : Type*} [AddCommMonoid M] {α : Type*} (l : List α) (g : α → M) :
    ∑ i : Fin l.length, g (l.get i) = (l.map g).sum := by
  conv_rhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

/-! ## Stage valuation/residual basics -/

/- [SYN2-S1 SWEEP-1, 2026-07-31] ResVal.w_one/ResVal.w_pow/ResVal.R_one/ResVal.R_pow DELETED — single proof
source `Moves/ResVal.lean` (α-identical); uses re-pointed. -/

private lemma list_prod_ne_zero' (l : List (Polynomial ℤ_[p])) (hl : ∀ x ∈ l, x ≠ 0) :
    l.prod ≠ 0 :=
  List.prod_ne_zero (fun h0 => (hl 0 h0) rfl)

private lemma w_list_prod (σ : Stage p F) (l : List (Polynomial ℤ_[p]))
    (hl : ∀ x ∈ l, x ≠ 0) : σ.w l.prod = (l.map σ.w).sum := by
  induction l with
  | nil => simpa using ResVal.w_one σ
  | cons x xs ih =>
      rw [List.prod_cons, List.map_cons, List.sum_cons,
        σ.hwmul x xs.prod (hl x (by simp))
          (list_prod_ne_zero' xs (fun y hy => hl y (by simp [hy]))),
        ih (fun y hy => hl y (by simp [hy]))]

private lemma R_list_prod (σ : Stage p F) (l : List (Polynomial ℤ_[p]))
    (hl : ∀ x ∈ l, x ≠ 0) : σ.R l.prod = (l.map σ.R).prod := by
  induction l with
  | nil => simpa using ResVal.R_one σ
  | cons x xs ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons,
        σ.hRmul x xs.prod (hl x (by simp))
          (list_prod_ne_zero' xs (fun y hy => hl y (by simp [hy]))),
        ih (fun y hy => hl y (by simp [hy]))]

/-! ## Laurent monomial calculus (positions/scalars of `C·T` normal forms) -/

private lemma CT_pow' {K : Type*} [Field K] (c : K) (k : ℤ) (n : ℕ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T k) ^ n
      = LaurentPolynomial.C (c ^ n) * LaurentPolynomial.T ((n : ℤ) * k) := by
  rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow]

private lemma CT_list_prod {K : Type*} [Field K] {α : Type*} (l : List α)
    (c : α → K) (k : α → ℤ) :
    (l.map fun x => LaurentPolynomial.C (c x) * LaurentPolynomial.T (k x)).prod
      = LaurentPolynomial.C ((l.map c).prod) * LaurentPolynomial.T ((l.map k).sum) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons,
        List.map_cons, List.sum_cons, map_mul, LaurentPolynomial.T_add]
      ring

private lemma CT_apply' {K : Type*} [Field K] (c : K) (n q : ℤ) :
    (LaurentPolynomial.C c * LaurentPolynomial.T n : LaurentPolynomial K) q
      = if n = q then c else 0 := by
  have h1 : LaurentPolynomial.C c * LaurentPolynomial.T n
      = (Finsupp.single n c : LaurentPolynomial K) :=
    (LaurentPolynomial.single_eq_C_mul_T c n).symm
  have h0 := congrArg (fun t : ℤ →₀ K => t q) h1
  exact h0.trans Finsupp.single_apply

/-- Monomial equality extraction: equal `C·T` monomials with nonzero left scalar have
equal scalars and equal positions. -/
private lemma CT_eq_extract {K : Type*} [Field K] {c c' : K} {n n' : ℤ} (hc : c ≠ 0)
    (h : LaurentPolynomial.C c * LaurentPolynomial.T n
       = LaurentPolynomial.C c' * LaurentPolynomial.T n') : c = c' ∧ n = n' := by
  have h1 := congrArg (fun t : ℤ →₀ K => t n) h
  rw [CT_apply', CT_apply', if_pos rfl] at h1
  by_cases hnn : n' = n
  · subst hnn
    rw [if_pos rfl] at h1
    exact ⟨h1, rfl⟩
  · rw [if_neg hnn] at h1
    exact absurd h1 hc

/-! ## Integer-exponent list calculus -/

private lemma list_sum_toNat_sub {α : Type*} (l : List α) (e v : α → ℤ) :
    (l.map fun x => ((e x).toNat : ℤ) * v x).sum
      - (l.map fun x => (((-(e x)).toNat : ℤ)) * v x).sum
      = (l.map fun x => e x * v x).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have hx2 : ((e x).toNat : ℤ) * v x - (((-(e x)).toNat : ℤ)) * v x = e x * v x := by
        rw [← sub_mul, Int.toNat_sub_toNat_neg]
      linarith

private lemma list_prod_zpow_split {G : Type*} [CommGroup G] {α : Type*} (l : List α)
    (dd : α → G) (e : α → ℤ) :
    (l.map fun x => dd x ^ e x).prod
      = (l.map fun x => dd x ^ (e x).toNat).prod *
        ((l.map fun x => dd x ^ (-(e x)).toNat).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.prod_cons]
      have hx : dd x ^ e x = dd x ^ (e x).toNat * (dd x ^ (-(e x)).toNat)⁻¹ := by
        rw [← zpow_natCast (dd x) (e x).toNat, ← zpow_natCast (dd x) (-(e x)).toNat,
          ← zpow_neg, ← zpow_add]
        congr 1
        omega
      rw [hx, ih, mul_inv]
      exact mul_mul_mul_comm _ _ _ _

private lemma list_prod_zpow_out {G : Type*} [CommGroup G] {α : Type*} (l : List α)
    (f : α → G) (lam : ℤ) :
    (l.map fun x => f x ^ lam).prod = ((l.map f).prod) ^ lam := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.prod_cons, ih, mul_zpow]

private lemma list_prod_zpow_sum {G : Type*} [CommGroup G] {α : Type*} (l : List α)
    (m : α → ℤ) (g : G) :
    (l.map fun x => g ^ m x).prod = g ^ ((l.map m).sum) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, zpow_add]

/-! ## The parent T-vector identities (extracted from `StageCoreL.core.tvec`) -/

open Classical in
/-- The parent (S5) digit of a coefficient, as a total function (choice; junk 1). -/
private noncomputable def dS5 (σ : Stage p F) (x : Polynomial ℤ_[p]) : (↥σ.K)ˣ :=
  if h : x ≠ 0 ∧ inC σ.Φ x then (σ.hS5 x h.1 h.2).choose else 1

private lemma dOf_spec (σ : Stage p F) {x : Polynomial ℤ_[p]} (hx : x ≠ 0)
    (hC : inC σ.Φ x) :
    σ.R x = LaurentPolynomial.C ((dS5 σ x : ↥σ.K)) *
      LaurentPolynomial.T (- σ.t * σ.wPrev x) := by
  rw [dS5, dif_pos ⟨hx, hC⟩]
  exact (σ.hS5 x hx hC).choose_spec

private lemma tvec_entry_facts (σ : Stage p F) {q : Polynomial ℤ_[p] × ℤ}
    (hq : q ∈ σ.Tvec) : q.1 ≠ 0 ∧ inC σ.Φ q.1 :=
  σ.hreps q.1 (by rw [← σ.hTvec]; exact List.mem_map_of_mem hq)

/-- Weight of one side (num or den) of the parent T-vector product. -/
private lemma tvec_side_w (σ : Stage p F) (eF : ℤ → ℕ) :
    σ.w ((σ.Tvec.map fun q => q.1 ^ eF q.2).prod * σ.Φ ^ eF σ.t)
      = (σ.Tvec.map fun q => (eF q.2 : ℤ) * σ.w q.1).sum + (eF σ.t : ℤ) * σ.h := by
  have hentne : ∀ x ∈ σ.Tvec.map (fun q => q.1 ^ eF q.2), x ≠ 0 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact pow_ne_zero _ ((tvec_entry_facts σ hq).1)
  rw [σ.hwmul _ _ (list_prod_ne_zero' _ hentne) (pow_ne_zero _ σ.hmonic.ne_zero),
    w_list_prod σ _ hentne, ResVal.w_pow σ σ.Φ σ.hmonic.ne_zero, σ.hwΦ, List.map_map]
  congr 2
  refine List.map_congr_left ?_
  intro q hq
  show σ.w (q.1 ^ eF q.2) = _
  rw [ResVal.w_pow σ q.1 ((tvec_entry_facts σ hq).1)]

/-- Residual of one side of the parent T-vector product, in monomial normal form. -/
private lemma tvec_side_R (σ : Stage p F) (eF : ℤ → ℕ) :
    σ.R ((σ.Tvec.map fun q => q.1 ^ eF q.2).prod * σ.Φ ^ eF σ.t)
      = LaurentPolynomial.C
          ((σ.Tvec.map fun q => ((dS5 σ q.1 : (↥σ.K)ˣ) : ↥σ.K) ^ eF q.2).prod)
        * LaurentPolynomial.T
            ((σ.Tvec.map fun q => (eF q.2 : ℤ) * (- σ.t * σ.wPrev q.1)).sum
              + (eF σ.t : ℤ) * σ.s) := by
  have hentne : ∀ x ∈ σ.Tvec.map (fun q => q.1 ^ eF q.2), x ≠ 0 := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact pow_ne_zero _ ((tvec_entry_facts σ hq).1)
  rw [σ.hRmul _ _ (list_prod_ne_zero' _ hentne) (pow_ne_zero _ σ.hmonic.ne_zero),
    R_list_prod σ _ hentne, ResVal.R_pow σ σ.Φ σ.hmonic.ne_zero, σ.hRΦ,
    LaurentPolynomial.T_pow, List.map_map]
  have hmap : σ.Tvec.map (σ.R ∘ fun q => q.1 ^ eF q.2)
      = σ.Tvec.map (fun q =>
          LaurentPolynomial.C (((dS5 σ q.1 : (↥σ.K)ˣ) : ↥σ.K) ^ eF q.2) *
            LaurentPolynomial.T ((eF q.2 : ℤ) * (- σ.t * σ.wPrev q.1))) := by
    refine List.map_congr_left ?_
    intro q hq
    obtain ⟨hq0, hqC⟩ := tvec_entry_facts σ hq
    show σ.R (q.1 ^ eF q.2) = _
    rw [ResVal.R_pow σ q.1 hq0, dOf_spec σ hq0 hqC, CT_pow']
  rw [hmap, CT_list_prod, mul_assoc, ← LaurentPolynomial.T_add]

/-- The three parent identities the twist-class bridges consume, extracted from the
parent T-vector product law (`TvecLaw σ`, supplied by `StageCoreL σ`):
(C) the weight identity `Σ b·w(ũ) + t·h = 1` (T has degree 1);
(A) the scalar identity `Π d^{b} = 1` (T's digit scalars cancel);
(B′) the position identity `−t·Σ b·w̃(ũ) + t·s = 0` (T's z-position vanishes). -/
private lemma parent_tvec_identities (σ : Stage p F) (hσ : StageCoreL σ) :
    ((σ.Tvec.map fun q => q.2 * σ.w q.1).sum + σ.t * (σ.h : ℤ) = 1) ∧
    ((σ.Tvec.map fun q => dS5 σ q.1 ^ q.2).prod = 1) ∧
    (- σ.t * ((σ.Tvec.map fun q => q.2 * σ.wPrev q.1).sum) + σ.t * σ.s = 0) := by
  obtain ⟨hwEq, hREq⟩ := hσ.core.tvec
  rw [Stage.tvecNum, Stage.tvecDen] at hwEq hREq
  -- weight sides
  have hwN := tvec_side_w σ Int.toNat
  have hwD := tvec_side_w σ (fun z => (-z).toNat)
  rw [hwN, hwD] at hwEq
  -- (C)
  have hsubW := list_sum_toNat_sub σ.Tvec (fun q => q.2) (fun q => σ.w q.1)
  have h5 : ((σ.t.toNat : ℤ)) * σ.h - (((-σ.t).toNat : ℤ)) * σ.h = σ.t * σ.h := by
    rw [← sub_mul, Int.toNat_sub_toNat_neg]
  have hC : (σ.Tvec.map fun q => q.2 * σ.w q.1).sum + σ.t * (σ.h : ℤ) = 1 := by
    linarith
  -- residual sides
  have hRN := tvec_side_R σ Int.toNat
  have hRD := tvec_side_R σ (fun z => (-z).toNat)
  rw [hRN, hRD] at hREq
  -- unit-valued scalars are nonzero
  have hval : ∀ eF : ℤ → ℕ,
      (σ.Tvec.map fun q => ((dS5 σ q.1 : (↥σ.K)ˣ) : ↥σ.K) ^ eF q.2).prod
        = (((σ.Tvec.map fun q => dS5 σ q.1 ^ eF q.2).prod : (↥σ.K)ˣ) : ↥σ.K) := by
    intro eF
    induction σ.Tvec with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.prod_cons, Units.val_mul,
          Units.val_pow_eq_pow_val, ih]
  have hPne : (σ.Tvec.map fun q => ((dS5 σ q.1 : (↥σ.K)ˣ) : ↥σ.K) ^ Int.toNat q.2).prod
      ≠ 0 := by
    rw [hval Int.toNat]
    exact Units.ne_zero _
  obtain ⟨hPP, hpos⟩ := CT_eq_extract hPne hREq
  -- (A)
  have hUU : (σ.Tvec.map fun q => dS5 σ q.1 ^ Int.toNat q.2).prod
      = (σ.Tvec.map fun q => dS5 σ q.1 ^ (-q.2).toNat).prod := by
    apply Units.ext
    rw [← hval Int.toNat, ← hval (fun z => (-z).toNat)]
    exact hPP
  have hA : (σ.Tvec.map fun q => dS5 σ q.1 ^ q.2).prod = 1 := by
    rw [list_prod_zpow_split σ.Tvec (fun q => dS5 σ q.1) (fun q => q.2), hUU,
      mul_inv_cancel]
  -- (B′)
  have hsubP := list_sum_toNat_sub σ.Tvec (fun q => q.2)
    (fun q => - σ.t * σ.wPrev q.1)
  have h6 : ((σ.t.toNat : ℤ)) * σ.s - (((-σ.t).toNat : ℤ)) * σ.s = σ.t * σ.s := by
    rw [← sub_mul, Int.toNat_sub_toNat_neg]
  have hSS : (σ.Tvec.map fun q => q.2 * (- σ.t * σ.wPrev q.1)).sum + σ.t * σ.s = 0 := by
    linarith
  have hfac : (σ.Tvec.map fun q => q.2 * (- σ.t * σ.wPrev q.1)).sum
      = - σ.t * ((σ.Tvec.map fun q => q.2 * σ.wPrev q.1).sum) := by
    induction σ.Tvec with
    | nil => simp
    | cons x xs ih =>
        simp only [List.map_cons, List.sum_cons, ih]
        ring
  exact ⟨hC, hA, by linarith [hfac ▸ hSS]⟩

/-! ## The pinned child digit, its F-images, and the shared scalar kernel K1d -/

open Classical in
/-- The pinned child digit of a coefficient (choice over the pin; junk 1). -/
private noncomputable def cOf (σ σ' : Stage p F) {Φhat : Polynomial ℤ_[p]} {zbar : Fˣ}
    (pin : VertexPin σ σ' Φhat zbar) (x : Polynomial ℤ_[p]) : (↥σ'.K)ˣ :=
  if h : x ≠ 0 ∧ inC Φhat x then (pin x h.1 h.2).choose else 1

private lemma cOf_spec (σ σ' : Stage p F) {Φhat : Polynomial ℤ_[p]} {zbar : Fˣ}
    (pin : VertexPin σ σ' Φhat zbar) {x : Polynomial ℤ_[p]}
    (hx : x ≠ 0) (hC : inC Φhat x) :
    σ'.R x = LaurentPolynomial.C ((cOf σ σ' pin x : ↥σ'.K)) *
        LaurentPolynomial.T (- σ'.t * σ.w x) ∧
    ((cOf σ σ' pin x : ↥σ'.K) : F) = σ.digPrime zbar x := by
  rw [cOf, dif_pos ⟨hx, hC⟩]
  exact (pin x hx hC).choose_spec

/-- The pinned child digit of a PARENT coefficient, in `Fˣ`: parent (S5) digit times the
forced parent-frame `z̄`-power — the pin's whole content, unit-valued. -/
private lemma cOf_F_coeff (σ σ' : Stage p F) {Φhat : Polynomial ℤ_[p]} {zbar : Fˣ}
    (pin : VertexPin σ σ' Φhat zbar) {x : Polynomial ℤ_[p]}
    (hx : x ≠ 0) (hxσ : inC σ.Φ x) (hxΦ : inC Φhat x) :
    Units.map (σ'.K.subtype).toMonoidHom (cOf σ σ' pin x)
      = Units.map (σ.K.subtype).toMonoidHom (dS5 σ x) * zbar ^ (- σ.t * σ.wPrev x) := by
  apply Units.ext
  have h1 : ((cOf σ σ' pin x : ↥σ'.K) : F) = σ.digPrime zbar x :=
    (cOf_spec σ σ' pin hx hxΦ).2
  have h2 : σ.digPrime zbar x
      = σ.K.subtype ((dS5 σ x : ↥σ.K)) * ((zbar ^ (- σ.t * σ.wPrev x) : Fˣ) : F) := by
    simp only [Stage.digPrime]
    rw [dOf_spec σ hx hxσ, LaurentPolynomial.eval₂_C_mul_T]
  rw [Units.val_mul, Units.coe_map, Units.coe_map]
  exact h1.trans h2

/-- The pinned child digit of the OUTGOING KEY, in `Fˣ`: `z̄^{s}` (the parent key residual
`R Φ = z^s` evaluated at the root). -/
private lemma cOf_F_key (σ σ' : Stage p F) {Φhat : Polynomial ℤ_[p]} {zbar : Fˣ}
    (pin : VertexPin σ σ' Φhat zbar) (hΦin : inC Φhat σ.Φ) :
    Units.map (σ'.K.subtype).toMonoidHom (cOf σ σ' pin σ.Φ) = zbar ^ σ.s := by
  apply Units.ext
  have h1 : ((cOf σ σ' pin σ.Φ : ↥σ'.K) : F) = σ.digPrime zbar σ.Φ :=
    (cOf_spec σ σ' pin σ.hmonic.ne_zero hΦin).2
  have h2 : σ.digPrime zbar σ.Φ = ((zbar ^ σ.s : Fˣ) : F) := by
    simp only [Stage.digPrime]
    rw [σ.hRΦ, LaurentPolynomial.eval₂_T]
  rw [Units.coe_map]
  exact h1.trans h2

/-- MonoidHom push through a zpow-weighted list product (groups). -/
private lemma map_list_prod_zpow {G H : Type*} [CommGroup G] [CommGroup H] (φ : G →* H)
    {α : Type*} (l : List α) (f : α → G) (e : α → ℤ) :
    φ ((l.map fun x => f x ^ e x).prod) = (l.map fun x => φ (f x) ^ e x).prod := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.prod_cons, map_mul, map_zpow, ih]

/-- The bilinear list-sum reshaping used by the component identities. -/
private lemma list_sum_shape {α : Type*} (l : List (α × ℤ)) (a s : ℤ) (w : α × ℤ → ℤ) :
    (l.map fun q => (a * w q) * (s * q.2)).sum
      = a * s * ((l.map fun q => q.2 * w q).sum) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- **The K1 scalar kernel**: under the pin, the child digits of the parent T-vector
entries multiply to 1 at EVERY integer power of the transported exponents — the single
identity behind both twist-class scalar legs (S8's `TvecUnitLaw` at `lam = σ'.s`; S7's
z′-pin at `lam = −σ'.h`). The parent scalar law (A) and position law (B′) enter through
the `Fˣ`-images; the frame twist `z̄^{lam·E}` is exactly what the pin kills. -/
private lemma K1d (σ σ' : Stage p F) (hσ : StageCoreL σ) {Φhat : Polynomial ℤ_[p]}
    {zbar : Fˣ} (pin : VertexPin σ σ' Φhat zbar) (hΦin : inC Φhat σ.Φ) (lam : ℤ) :
    (σ.Tvec.map fun q => cOf σ σ' pin q.1 ^ (lam * q.2)).prod
      * cOf σ σ' pin σ.Φ ^ (lam * σ.t) = 1 := by
  obtain ⟨hC, hA, hB⟩ := parent_tvec_identities σ hσ
  have hGinj : Function.Injective
      (Units.map (σ'.K.subtype).toMonoidHom : (↥σ'.K)ˣ →* Fˣ) :=
    Units.map_injective σ'.K.subtype.injective
  apply hGinj
  rw [map_mul, map_one, map_zpow,
    map_list_prod_zpow (Units.map (σ'.K.subtype).toMonoidHom) σ.Tvec
      (fun q => cOf σ σ' pin q.1) (fun q => lam * q.2)]
  -- per-entry normal form: (DU·ZU^k)^(lam·b) = (DU^b)^lam · ZU^(k·(lam·b))
  have hmap1 : (σ.Tvec.map fun q =>
        (Units.map (σ'.K.subtype).toMonoidHom) (cOf σ σ' pin q.1) ^ (lam * q.2))
      = σ.Tvec.map fun q =>
          ((Units.map (σ.K.subtype).toMonoidHom) (dS5 σ q.1) ^ q.2) ^ lam
            * zbar ^ ((- σ.t * σ.wPrev q.1) * (lam * q.2)) := by
    refine List.map_congr_left fun q hq => ?_
    obtain ⟨hq0, hqσ⟩ := tvec_entry_facts σ hq
    have hqΦ : inC Φhat q.1 :=
      lt_trans (show q.1.degree < σ.Φ.degree from hqσ)
        (show σ.Φ.degree < Φhat.degree from hΦin)
    rw [cOf_F_coeff σ σ' pin hq0 hqσ hqΦ, mul_zpow, ← zpow_mul, ← zpow_mul,
      mul_comm lam q.2, zpow_mul]
  rw [hmap1, List.prod_map_mul, list_prod_zpow_out, list_prod_zpow_sum,
    cOf_F_key σ σ' pin hΦin]
  -- (A) in Fˣ
  have hAF : (σ.Tvec.map fun q =>
      (Units.map (σ.K.subtype).toMonoidHom) (dS5 σ q.1) ^ q.2).prod = 1 := by
    have h := congrArg (Units.map (σ.K.subtype).toMonoidHom) hA
    rwa [map_list_prod_zpow (Units.map (σ.K.subtype).toMonoidHom) σ.Tvec
      (fun q => dS5 σ q.1) (fun q => q.2), map_one] at h
  rw [hAF, one_zpow, one_mul, ← zpow_mul, ← zpow_add]
  -- the exponent vanishes by (B′)
  have hexp : (σ.Tvec.map fun q => (- σ.t * σ.wPrev q.1) * (lam * q.2)).sum
      + σ.s * (lam * σ.t) = 0 := by
    rw [list_sum_shape σ.Tvec (- σ.t) lam (fun q => σ.wPrev q.1)]
    linear_combination lam * hB
  rw [hexp, zpow_zero]

/-! ## Bridge 1 — S8's blocked leg: the child T-vector product law from the pin -/

/-- **The twist-class bridge, T-law leg** (S8's `TvecUnitLaw σ'` conjunct — the one the
dual-audited twist symmetry proved underivable from the RECORDED hypothesis class): with
the D.7(vi) pin recorded, the child T-vector product law holds. Outer/inner exponents
collapse through the parent weight identity (C) + the child Bézout; the residue leg is
`K1d` at `lam = σ'.s`. Consumed by S9d (which proves the pin on the constructed child)
and thence by S8's homed conjunct and S11's twist-class residual. -/
theorem K1_tvecUnitLaw_of_pin (σ σ' : Stage p F) (hσ : StageCoreL σ)
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar)
    (pin : VertexPin σ σ' Φhat zbar) (hΦin : inC Φhat σ.Φ) :
    TvecUnitLaw σ' := by
  classical
  obtain ⟨hC, _, _⟩ := parent_tvec_identities σ hσ
  -- entry facts for the child T-vector
  have hmem' : ∀ x ∈ σ'.Tvec, x.1 ≠ 0 ∧ inC Φhat x.1 := by
    intro x hx
    obtain ⟨h0, hCx⟩ := tvec_entry_facts σ' hx
    exact ⟨h0, by rwa [tc.base.child_key] at hCx⟩
  -- the three component identities
  have hsc : (∏ i : Fin σ'.Tvec.length,
      cOf σ σ' pin ((σ'.Tvec.get i).1) ^ ((σ'.Tvec.get i).2)) = 1 := by
    rw [fin_prod_get σ'.Tvec (fun x => cOf σ σ' pin x.1 ^ x.2), tc.child_Tvec,
      List.map_append, List.prod_append, List.map_map]
    simp only [Function.comp_def, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    exact K1d σ σ' hσ pin hΦin σ'.s
  have hin : (∑ i : Fin σ'.Tvec.length,
      (- σ'.t * σ.w ((σ'.Tvec.get i).1)) * ((σ'.Tvec.get i).2)) + σ'.s * σ'.t = 0 := by
    rw [fin_sum_get σ'.Tvec (fun x => (- σ'.t * σ.w x.1) * x.2), tc.child_Tvec,
      List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [list_sum_shape σ.Tvec (- σ'.t) σ'.s (fun q => σ.w q.1), σ.hwΦ]
    linear_combination (- σ'.t * σ'.s) * hC
  have hout : (∑ i : Fin σ'.Tvec.length,
      σ'.w ((σ'.Tvec.get i).1) * ((σ'.Tvec.get i).2)) + σ'.h * σ'.t = 1 := by
    rw [fin_sum_get σ'.Tvec (fun x => σ'.w x.1 * x.2)]
    have hstretch : σ'.Tvec.map (fun x => σ'.w x.1 * x.2)
        = σ'.Tvec.map (fun x => (σ'.e * σ.w x.1) * x.2) := by
      refine List.map_congr_left fun x hx => ?_
      obtain ⟨h0, hCx⟩ := tvec_entry_facts σ' hx
      rw [σ'.hStretch x.1 h0 hCx, tc.base.child_wPrev]
    rw [hstretch, tc.child_Tvec, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [list_sum_shape σ.Tvec (σ'.e : ℤ) σ'.s (fun q => σ.w q.1), σ.hwΦ]
    have hbez' : (σ'.e : ℤ) * σ'.s + (σ'.h : ℤ) * σ'.t = 1 := σ'.hbez
    linear_combination (σ'.e : ℤ) * σ'.s * hC + hbez'
  -- assemble the units
  refine ⟨mUnit ↥σ'.K 1 σ'.s σ'.h,
    fun i => mUnit ↥σ'.K (cOf σ σ' pin ((σ'.Tvec.get i).1))
      (- σ'.t * σ.w ((σ'.Tvec.get i).1)) (σ'.w ((σ'.Tvec.get i).1)), ?_, ?_, ?_⟩
  · show ((mUnit ↥σ'.K 1 σ'.s σ'.h : (LTwo ↥σ'.K)ˣ) : LTwo ↥σ'.K) = σ'.grRes σ'.Φ
    rw [mUnit_val, Stage.grRes, σ'.hRΦ, σ'.hwΦ]
    simp
  · intro i
    obtain ⟨h0, hCx⟩ := hmem' (σ'.Tvec.get i) (σ'.Tvec.get_mem i)
    show ((mUnit ↥σ'.K _ _ _ : (LTwo ↥σ'.K)ˣ) : LTwo ↥σ'.K) = σ'.grRes ((σ'.Tvec.get i).1)
    rw [mUnit_val, Stage.grRes, (cOf_spec σ σ' pin h0 hCx).1]
  · rw [prod_mUnit_zpow Finset.univ
      (fun i => cOf σ σ' pin ((σ'.Tvec.get i).1))
      (fun i => - σ'.t * σ.w ((σ'.Tvec.get i).1))
      (fun i => σ'.w ((σ'.Tvec.get i).1))
      (fun i => (σ'.Tvec.get i).2), mUnit_zpow, one_zpow, mUnit_mul, mul_one,
      hsc, hin, hout, mUnit_locT]

/-! ## Bridge 2 — S7's blocked leg (c): the z′-pin from the pin

The witness is the note's own `z′ = V′^{−h′}·Y′^{e′}` (D.7(vi)): the exponent vector is
`−h′ ×` the TRANSPORTED PARENT T-vector, read over `σ'.reps = σ.reps ++ [σ.Φ]`
(`child_reps`), whose alignment with the parent `σ.Tvec` is positional (`hTvec`). -/

/-- Index-aligned product over the child representative list: a product over
`σ'.reps = σ.reps ++ [σ.Φ]` against parent-Tvec-aligned exponents splits as the parent
list product times the outgoing-key term. -/
private lemma prod_over_child_reps {M : Type*} [CommMonoid M] (σ σ' : Stage p F)
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar)
    (hlen' : σ.Tvec.length + 1 = σ'.reps.length)
    (G : Polynomial ℤ_[p] → ℤ → M) (bv : Fin σ'.reps.length → ℤ)
    (hbvL : ∀ (i : Fin σ'.reps.length) (h : (i : ℕ) < σ.Tvec.length),
      bv i = (σ.Tvec.get ⟨(i : ℕ), h⟩).2)
    (hbvR : ∀ i : Fin σ'.reps.length, ¬ ((i : ℕ) < σ.Tvec.length) → bv i = σ.t) :
    (∏ i, G (σ'.reps.get i) (bv i))
      = (σ.Tvec.map fun q => G q.1 q.2).prod * G σ.Φ σ.t := by
  classical
  have hlenT : σ.Tvec.length = σ.reps.length := by
    have h := congrArg List.length σ.hTvec
    rwa [List.length_map] at h
  -- the two get-computations on the appended list
  have hgetL : ∀ (v : ℕ) (hv : v < σ'.reps.length) (hvT : v < σ.Tvec.length),
      σ'.reps.get ⟨v, hv⟩ = (σ.Tvec.get ⟨v, hvT⟩).1 := by
    intro v hv hvT
    have hvr : v < σ.reps.length := by omega
    have h2 : σ'.reps[v] = σ.reps[v]'hvr := by
      simp only [tc.base.child_reps]
      exact List.getElem_append_left hvr
    have h3 : σ.reps[v]'hvr = (σ.Tvec[v]'hvT).1 := by
      have h4 : σ.reps = σ.Tvec.map Prod.fst := σ.hTvec.symm
      simp only [h4]
      exact List.getElem_map _
    simp only [List.get_eq_getElem]
    rw [h2, h3]
  have hgetR : ∀ (v : ℕ) (hv : v < σ'.reps.length), ¬ (v < σ.Tvec.length) →
      σ'.reps.get ⟨v, hv⟩ = σ.Φ := by
    intro v hv hnv
    have hveq : v = σ.reps.length := by omega
    subst hveq
    simp only [List.get_eq_getElem, tc.base.child_reps]
    rw [List.getElem_append_right (le_refl _)]
    simp
  -- reindex to `Fin (T + 1)` and split off the last factor
  rw [← Fin.prod_congr' (fun i => G (σ'.reps.get i) (bv i)) hlen', Fin.prod_univ_castSucc]
  congr 1
  · -- the interior product is the parent list product
    rw [← fin_prod_get σ.Tvec (fun q => G q.1 q.2)]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hjT : ((j.castSucc.cast hlen' : Fin σ'.reps.length) : ℕ) < σ.Tvec.length := by
      simp only [Fin.val_cast, Fin.val_castSucc]
      exact j.isLt
    rw [hgetL _ _ hjT, hbvL _ hjT]
    have hA : (⟨((Fin.cast hlen' j.castSucc : Fin σ'.reps.length) : ℕ), hjT⟩
        : Fin σ.Tvec.length) = j := Fin.ext rfl
    rw [hA]
  · -- the last factor is the outgoing-key term
    have hnT : ¬ (((Fin.last σ.Tvec.length).cast hlen' : Fin σ'.reps.length) : ℕ)
        < σ.Tvec.length := by simp
    rw [hgetR _ _ hnT, hbvR _ hnT]

/-- Additive twin of `prod_over_child_reps`. -/
private lemma sum_over_child_reps (σ σ' : Stage p F)
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar)
    (hlen' : σ.Tvec.length + 1 = σ'.reps.length)
    (G : Polynomial ℤ_[p] → ℤ → ℤ) (bv : Fin σ'.reps.length → ℤ)
    (hbvL : ∀ (i : Fin σ'.reps.length) (h : (i : ℕ) < σ.Tvec.length),
      bv i = (σ.Tvec.get ⟨(i : ℕ), h⟩).2)
    (hbvR : ∀ i : Fin σ'.reps.length, ¬ ((i : ℕ) < σ.Tvec.length) → bv i = σ.t) :
    (∑ i, G (σ'.reps.get i) (bv i))
      = (σ.Tvec.map fun q => G q.1 q.2).sum + G σ.Φ σ.t :=
  prod_over_child_reps (M := Multiplicative ℤ) σ σ' tc hlen' G bv hbvL hbvR

/-- **The twist-class bridge, z′-pin leg** (S7's CoeffLocLaw conjunct (c) — the scratch's
(⋆) residual): with the pin, `z′` is EXACTLY (scalar 1) the value of the degree-0 formal
`U ∪ {Y}`-monomial vector `−h′·(transported parent T-vector) + e′·Y′` — the note's
`z′ = V′^{−h′}·Y′^{e′}` (D.7(vi)). The weight leg is the parent identity (C); the scalar
leg is `K1d` at `lam = −σ'.h` (the pin kills the scratch's `z̄^{h′·E}`). Together with the
scratch's PROVED legs (a)/(b) this completes `CoeffLocLaw σ'`. -/
theorem K1_coeffLocC_of_pin (σ σ' : Stage p F) (hσ : StageCoreL σ)
    {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (tc : TransitionCoreL σ σ' Φhat e' h' zbar)
    (pin : VertexPin σ σ' Φhat zbar) (hΦin : inC Φhat σ.Φ) :
    ∃ (zv : LVec σ') (u : (LTwo ↥σ'.K)ˣ),
      σ'.lvecWeight zv = 0 ∧ IsLVecVal σ' zv u ∧
      (u : LTwo ↥σ'.K) = LaurentPolynomial.C (zvar ↥σ'.K) := by
  classical
  obtain ⟨hC, _, _⟩ := parent_tvec_identities σ hσ
  have hlenT : σ.Tvec.length = σ.reps.length := by
    have h := congrArg List.length σ.hTvec
    rwa [List.length_map] at h
  have hlen' : σ.Tvec.length + 1 = σ'.reps.length := by
    rw [tc.base.child_reps, List.length_append, List.length_singleton, hlenT]
  -- the aligned parent exponent vector
  set bv : Fin σ'.reps.length → ℤ :=
    fun i => if h : (i : ℕ) < σ.Tvec.length then (σ.Tvec.get ⟨(i : ℕ), h⟩).2 else σ.t
    with hbv
  have hbvL : ∀ (i : Fin σ'.reps.length) (h : (i : ℕ) < σ.Tvec.length),
      bv i = (σ.Tvec.get ⟨(i : ℕ), h⟩).2 := fun i h => by rw [hbv]; exact dif_pos h
  have hbvR : ∀ i : Fin σ'.reps.length, ¬ ((i : ℕ) < σ.Tvec.length) → bv i = σ.t :=
    fun i h => by rw [hbv]; exact dif_neg h
  -- entry facts on the child representative list
  have hrepfacts : ∀ i : Fin σ'.reps.length,
      σ'.reps.get i ≠ 0 ∧ inC Φhat (σ'.reps.get i) := by
    intro i
    obtain ⟨h0, hCx⟩ := σ'.hreps (σ'.reps.get i) (σ'.reps.get_mem i)
    exact ⟨h0, by rwa [tc.base.child_key] at hCx⟩
  -- the three component identities
  have hsc : (∏ i : Fin σ'.reps.length,
      cOf σ σ' pin (σ'.reps.get i) ^ (-(σ'.h : ℤ) * bv i)) = 1 := by
    rw [prod_over_child_reps σ σ' tc hlen'
      (fun x b => cOf σ σ' pin x ^ (-(σ'.h : ℤ) * b)) bv hbvL hbvR]
    exact K1d σ σ' hσ pin hΦin (-(σ'.h : ℤ))
  have hin : (∑ i : Fin σ'.reps.length,
      (- σ'.t * σ.w (σ'.reps.get i)) * (-(σ'.h : ℤ) * bv i)) + σ'.s * σ'.e = 1 := by
    rw [sum_over_child_reps σ σ' tc hlen'
      (fun x b => (- σ'.t * σ.w x) * (-(σ'.h : ℤ) * b)) bv hbvL hbvR,
      list_sum_shape σ.Tvec (- σ'.t) (-(σ'.h : ℤ)) (fun q => σ.w q.1), σ.hwΦ]
    have hbez' : (σ'.e : ℤ) * σ'.s + (σ'.h : ℤ) * σ'.t = 1 := σ'.hbez
    linear_combination (σ'.t * σ'.h) * hC + hbez'
  have hout : (∑ i : Fin σ'.reps.length,
      σ'.w (σ'.reps.get i) * (-(σ'.h : ℤ) * bv i)) + σ'.h * σ'.e = 0 := by
    have hstretch : (∑ i : Fin σ'.reps.length,
        σ'.w (σ'.reps.get i) * (-(σ'.h : ℤ) * bv i))
        = ∑ i : Fin σ'.reps.length,
            ((σ'.e : ℤ) * σ.w (σ'.reps.get i)) * (-(σ'.h : ℤ) * bv i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      obtain ⟨h0, hCx⟩ := σ'.hreps (σ'.reps.get i) (σ'.reps.get_mem i)
      rw [σ'.hStretch _ h0 hCx, tc.base.child_wPrev]
    rw [hstretch, sum_over_child_reps σ σ' tc hlen'
      (fun x b => ((σ'.e : ℤ) * σ.w x) * (-(σ'.h : ℤ) * b)) bv hbvL hbvR,
      list_sum_shape σ.Tvec (σ'.e : ℤ) (-(σ'.h : ℤ)) (fun q => σ.w q.1), σ.hwΦ]
    linear_combination (- (σ'.e : ℤ) * σ'.h) * hC
  -- assemble
  refine ⟨⟨fun i => -(σ'.h : ℤ) * bv i, (σ'.e : ℤ)⟩,
    (∏ i, (mUnit ↥σ'.K (cOf σ σ' pin (σ'.reps.get i))
        (- σ'.t * σ.w (σ'.reps.get i)) (σ'.w (σ'.reps.get i))) ^ (-(σ'.h : ℤ) * bv i))
      * (mUnit ↥σ'.K 1 σ'.s σ'.h) ^ (σ'.e : ℤ), ?_, ?_, ?_⟩
  · -- lvecWeight = 0
    show (∑ i, (-(σ'.h : ℤ) * bv i) * σ'.w (σ'.reps.get i)) + (σ'.e : ℤ) * σ'.h = 0
    have hcomm : (∑ i, (-(σ'.h : ℤ) * bv i) * σ'.w (σ'.reps.get i))
        = ∑ i : Fin σ'.reps.length, σ'.w (σ'.reps.get i) * (-(σ'.h : ℤ) * bv i) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hcomm]
    linarith [hout]
  · -- IsLVecVal
    refine ⟨fun i => mUnit ↥σ'.K (cOf σ σ' pin (σ'.reps.get i))
        (- σ'.t * σ.w (σ'.reps.get i)) (σ'.w (σ'.reps.get i)),
      mUnit ↥σ'.K 1 σ'.s σ'.h, ?_, ?_, rfl⟩
    · intro i
      obtain ⟨h0, hCx⟩ := hrepfacts i
      show ((mUnit ↥σ'.K _ _ _ : (LTwo ↥σ'.K)ˣ) : LTwo ↥σ'.K) = σ'.grRes (σ'.reps.get i)
      rw [mUnit_val, Stage.grRes, (cOf_spec σ σ' pin h0 hCx).1]
    · show ((mUnit ↥σ'.K 1 σ'.s σ'.h : (LTwo ↥σ'.K)ˣ) : LTwo ↥σ'.K) = σ'.grRes σ'.Φ
      rw [mUnit_val, Stage.grRes, σ'.hRΦ, σ'.hwΦ]
      simp
  · -- the value is C zvar
    rw [prod_mUnit_zpow Finset.univ
      (fun i => cOf σ σ' pin (σ'.reps.get i))
      (fun i => - σ'.t * σ.w (σ'.reps.get i))
      (fun i => σ'.w (σ'.reps.get i))
      (fun i => -(σ'.h : ℤ) * bv i), mUnit_zpow, one_zpow, mUnit_mul, mul_one,
      hsc, hin, hout]
    exact mUnit_zvar ↥σ'.K

end LeanUrat.HC1
