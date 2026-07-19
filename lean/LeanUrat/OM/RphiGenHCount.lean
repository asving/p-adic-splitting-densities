import Mathlib
import LeanUrat.OM.RphiRing
import LeanUrat.OM.RphiRingGenH

/-!
# B-RING, wave W6a-residual: the per-digit product count for the gapped general-`h` ring

Completes wave W6a (`LeanUrat.OM.RphiRingGenH`). Blueprint:
`uniform-rationality/notes/GENERAL_RESTART_BLUEPRINT.md` §1 + §6 (W6a-residual bullet) and §5
(clamping caveats). Gate ground truth: `/workspace-vast/asving/tmp/phaseb_w6a/gate_w6a.py`
(0-mismatch) and `/workspace-vast/asving/tmp/phaseb_w6h/`.

This module is **purely additive**: it imports `RphiRing` and `RphiRingGenH` and edits neither.
It supplies the two facts W6a deferred to a named residual:

## Deliverables (BANKED, core-only footprint `[propext, Classical.choice, Quot.sound]`)

* **Reverse valuation anchors (exact, general `e`, general `h`)**:
  `vL_theta_eq` (`vL θ = h`) and `vL_natCast_p_eq` (`vL p = e`). W6a banked only the `≤`
  membership bounds; here the `≥` is upgraded to `=` via the digit structure:
  `θ ∉ filtIdeal (h+1)` (its digit-`1` coordinate is a unit) and `p ∉ filtIdeal (e+1)`
  (its digit-`0` coordinate is `p`, and `p² ∤ p`).

* **The per-digit product count (general `e`, general `h`)**:
  `card_filtIdeal : Nat.card (filtIdeal w) = ∏_{i<e} p^(N − min N ⌈(w−ih)/e⌉⁺)`.
  The `⁺` clamp is Nat truncated subtraction (`dexp`); the `min N` clamp is handled explicitly
  by `ball_count_clamped` (blueprint §5 caveats 1,2). Proven via `filtIdeal_eq_phiIdeal`:
  the filtration ideal equals the digit-ball ideal `phiIdeal w = {x : ∀ i, p^(dexp w i) ∣ aᵢ}`.
  The **⟸** containment is the digit reassembly; the **⟹** containment is that `phiIdeal w`
  is an ideal (θ-closure via `theta_mul_assemble` + `dexp_antitone`/`dexp_wrap`, and it contains
  every generator). The θ-closure inequalities hold for ALL `e` (no `gcd(e,h)=1` needed), so the
  count is general-`e`, not just `e = 2`.

* **`h = 1` collapse**: `card_filtIdeal_h_one_collapse` (`= p^(N·e − w)`, via the banked
  `filtIdeal_eq_span_theta_pow_of_h_one` + `card_span_theta_pow`) and `prod_dexp_h_one`
  (the general product itself collapses to `p^(N·e − w)`).

* **Gate lemmas** (concrete, by `decide`/`norm_num` on the closed count): the wild gapped ⟨2,3⟩
  sizes at `N=5` (`w∈{1,2,3}`, matching `gate_w6a.py`: `card F_1 = card F_2 = 512`, refuting the
  naive `2^(N·e−w)`) and `N=7` (`w=13`, phaseb_w6h readable case), plus the `h=1` `p=3` collapse.

Discipline: no `sorry`/`axiom`/`native_decide`; mathlib-only beyond `RphiRing`/`RphiRingGenH`;
frozen interface on the W6a base.
-/

namespace LeanUrat.OM.RphiGenHCount

open Polynomial LeanUrat.OM.RphiRing LeanUrat.OM.RphiRingGenH

variable (p N e h : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ)

noncomputable section

def digitEquivFull (hN : 0 < N) (he : 0 < e) :
    Rphi p N e h c ≃ₗ[ZMod (p ^ N)] (Fin e → ZMod (p ^ N)) :=
  (digitEquiv p N e h c hN he).symm.trans (degreeLTEquiv (ZMod (p ^ N)) e)

def digitCoeff (hN : 0 < N) (he : 0 < e) (x : Rphi p N e h c) : Fin e → ZMod (p ^ N) :=
  digitEquivFull p N e h c hN he x

def assemble (b : Fin e → ZMod (p ^ N)) : Rphi p N e h c :=
  ∑ i : Fin e, algebraMap (ZMod (p ^ N)) (Rphi p N e h c) (b i) * theta p N e h c ^ (i : ℕ)

theorem assemble_eq (hN : 0 < N) (he : 0 < e) (b : Fin e → ZMod (p ^ N)) :
    assemble p N e h c b
      = digitEquiv p N e h c hN he ((degreeLTEquiv (ZMod (p ^ N)) e).symm b) := by
  rw [assemble, digitEquiv_apply]
  have hpoly : (((degreeLTEquiv (ZMod (p ^ N)) e).symm b : degreeLT (ZMod (p ^ N)) e)
      : (ZMod (p ^ N))[X]) = ∑ i : Fin e, monomial (i : ℕ) (b i) := rfl
  rw [hpoly, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
    ← theta_eq_root, ← AdjoinRoot.algebraMap_eq]

theorem digitCoeff_assemble (hN : 0 < N) (he : 0 < e) (b : Fin e → ZMod (p ^ N)) :
    digitCoeff p N e h c hN he (assemble p N e h c b) = b := by
  rw [digitCoeff, digitEquivFull, assemble_eq p N e h c hN he]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]

theorem assemble_digitCoeff (hN : 0 < N) (he : 0 < e) (x : Rphi p N e h c) :
    assemble p N e h c (digitCoeff p N e h c hN he x) = x := by
  rw [assemble_eq p N e h c hN he, digitCoeff, digitEquivFull]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]

def shiftVec (n : ℕ) (b : Fin (n + 1) → ZMod (p ^ N)) : Fin (n + 1) → ZMod (p ^ N) :=
  Fin.cons ((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h * b (Fin.last n))
    (fun j : Fin n => b (Fin.castSucc j))

theorem theta_mul_assemble (n : ℕ) (b : Fin (n + 1) → ZMod (p ^ N)) :
    theta p N (n + 1) h c * assemble p N (n + 1) h c b
      = assemble p N (n + 1) h c (shiftVec p N h c n b) := by
  rw [assemble, assemble, Finset.mul_sum]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_succ]
  have hlast : theta p N (n + 1) h c
        * ((algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (b (Fin.last n))
          * theta p N (n + 1) h c ^ (Fin.last n : ℕ))
      = (algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (shiftVec p N h c n b 0)
          * theta p N (n + 1) h c ^ ((0 : Fin (n + 1)) : ℕ) := by
    rw [shiftVec, Fin.cons_zero, Fin.val_last, Fin.val_zero, pow_zero, mul_one]
    rw [map_mul, map_mul, map_pow]
    have hθe : theta p N (n + 1) h c ^ (n + 1)
        = algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)
            ((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h) := theta_pow_e p N (n + 1) h c
    rw [map_mul, map_pow] at hθe
    calc theta p N (n + 1) h c
            * ((algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (b (Fin.last n))
              * theta p N (n + 1) h c ^ n)
        = (algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (b (Fin.last n))
            * theta p N (n + 1) h c ^ (n + 1) := by rw [pow_succ]; ring
      _ = (algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (b (Fin.last n))
            * ((algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (c : ZMod (p ^ N))
              * (algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (p : ZMod (p ^ N)) ^ h) := by
            rw [hθe]
      _ = (algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (c : ZMod (p ^ N))
            * (algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (p : ZMod (p ^ N)) ^ h
            * (algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (b (Fin.last n)) := by ring
  have hsum : (∑ i : Fin n, theta p N (n + 1) h c
        * ((algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (b i.castSucc)
          * theta p N (n + 1) h c ^ (i.castSucc : ℕ)))
      = ∑ i : Fin n, (algebraMap (ZMod (p ^ N)) (Rphi p N (n + 1) h c)) (shiftVec p N h c n b i.succ)
          * theta p N (n + 1) h c ^ (i.succ : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    have hs : shiftVec p N h c n b i.succ = b i.castSucc := by rw [shiftVec, Fin.cons_succ]
    rw [hs]
    have hv1 : (i.succ : ℕ) = (i.castSucc : ℕ) + 1 := by
      rw [Fin.val_succ, Fin.val_castSucc]
    rw [hv1, pow_succ]
    ring
  rw [hlast, hsum]; ring

/-! ## The dexp helpers -/

def dexp (w i : ℕ) : ℕ := (w - i * h) ⌈/⌉ e

theorem dexp_le_iff (he : 0 < e) (w i k : ℕ) :
    dexp e h w i ≤ k ↔ w ≤ i * h + e * k := by
  rw [dexp, ceilDiv_le_iff_le_mul he, Nat.sub_le_iff_le_add, Nat.add_comm]

theorem dexp_antitone (he : 0 < e) (w : ℕ) {i j : ℕ} (hij : i ≤ j) :
    dexp e h w j ≤ dexp e h w i := by
  rw [dexp_le_iff e h he]
  have hd := (dexp_le_iff e h he w i (dexp e h w i)).mp le_rfl
  have : i * h ≤ j * h := Nat.mul_le_mul_right _ hij
  omega

theorem dexp_wrap (he : 0 < e) (w : ℕ) :
    dexp e h w 0 ≤ dexp e h w (e - 1) + h := by
  rw [dexp_le_iff e h he]
  have hd := (dexp_le_iff e h he w (e-1) (dexp e h w (e-1))).mp le_rfl
  have h1 : (e - 1) * h ≤ e * h := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  rw [Nat.mul_add]
  omega

/-! ## The `Phi` predicate and θ-closure -/

/-- `Phi w x`: each digit `a_i` of `x` is divisible by `p^(dexp w i)`. -/
def Phi (hN : 0 < N) (he : 0 < e) (w : ℕ) (x : Rphi p N e h c) : Prop :=
  ∀ i : Fin e, ((p : ZMod (p ^ N)))^(dexp e h w (i : ℕ)) ∣ digitCoeff p N e h c hN he x i

/-- **θ-closure of `Phi`**: multiplying by `θ` preserves `Phi`. -/
theorem Phi_theta (hN : 0 < N) (he : 0 < e) (w : ℕ) {x : Rphi p N e h c}
    (hx : Phi p N e h c hN he w x) :
    Phi p N e h c hN he w (theta p N e h c * x) := by
  -- write e = n+1
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  -- θ*x = assemble (shiftVec (digitCoeff x))
  have hx_eq : x = assemble p N (n + 1) h c (digitCoeff p N (n + 1) h c hN he x) :=
    (assemble_digitCoeff p N (n + 1) h c hN he x).symm
  have hshift : theta p N (n + 1) h c * x
      = assemble p N (n + 1) h c (shiftVec p N h c n (digitCoeff p N (n + 1) h c hN he x)) := by
    conv_lhs => rw [hx_eq]
    exact theta_mul_assemble p N h c n (digitCoeff p N (n + 1) h c hN he x)
  intro i
  rw [hshift, digitCoeff_assemble p N (n + 1) h c hN he]
  -- case on i = 0 or i = j.succ
  refine Fin.cases ?_ ?_ i
  · -- i = 0: shiftVec 0 = c p^h b(last); need p^(dexp w 0) ∣ that
    rw [shiftVec, Fin.cons_zero]
    -- p^(dexp w (e-1)) ∣ b(last), and dexp w 0 ≤ dexp w (e-1) + h
    have hbl : ((p : ZMod (p ^ N)))^(dexp (n+1) h w n)
        ∣ digitCoeff p N (n + 1) h c hN he x (Fin.last n) := by
      have := hx (Fin.last n); rwa [Fin.val_last] at this
    have hwrap : dexp (n+1) h w 0 ≤ dexp (n+1) h w n + h := by
      have := dexp_wrap (n+1) h he w
      simpa using this
    -- p^(dexp w 0) ∣ p^(dexp w n + h) ∣ c * p^h * b(last)
    have hstep : ((p : ZMod (p ^ N)))^(dexp (n+1) h w n + h)
        ∣ (c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h
            * digitCoeff p N (n + 1) h c hN he x (Fin.last n) := by
      obtain ⟨t, ht⟩ := hbl
      refine ⟨(c : ZMod (p ^ N)) * t, ?_⟩
      rw [ht, pow_add]; ring
    exact dvd_trans (pow_dvd_pow _ hwrap) hstep
  · -- i = j.succ: shiftVec (succ j) = b (castSucc j)
    intro j
    rw [shiftVec, Fin.cons_succ]
    have hbj : ((p : ZMod (p ^ N)))^(dexp (n+1) h w (j.castSucc : ℕ))
        ∣ digitCoeff p N (n + 1) h c hN he x (Fin.castSucc j) := hx (Fin.castSucc j)
    have hmono : dexp (n+1) h w (j.succ : ℕ) ≤ dexp (n+1) h w (j.castSucc : ℕ) := by
      apply dexp_antitone (n+1) h he
      rw [Fin.val_succ, Fin.val_castSucc]; omega
    exact dvd_trans (pow_dvd_pow _ hmono) hbj

/-- `Phi` holds for `0`. -/
theorem Phi_zero (hN : 0 < N) (he : 0 < e) (w : ℕ) : Phi p N e h c hN he w 0 := by
  intro i
  rw [digitCoeff, map_zero]
  simp

/-- `Phi` is closed under addition. -/
theorem Phi_add (hN : 0 < N) (he : 0 < e) (w : ℕ) {x y : Rphi p N e h c}
    (hx : Phi p N e h c hN he w x) (hy : Phi p N e h c hN he w y) :
    Phi p N e h c hN he w (x + y) := by
  intro i
  have hd : digitCoeff p N e h c hN he (x + y) i
      = digitCoeff p N e h c hN he x i + digitCoeff p N e h c hN he y i := by
    rw [digitCoeff, digitCoeff, digitCoeff, map_add]; rfl
  rw [hd]
  exact dvd_add (hx i) (hy i)

/-- `Phi` is closed under scalar multiplication. -/
theorem Phi_smul (hN : 0 < N) (he : 0 < e) (w : ℕ) (s : ZMod (p ^ N)) {x : Rphi p N e h c}
    (hx : Phi p N e h c hN he w x) :
    Phi p N e h c hN he w (s • x) := by
  intro i
  have hd : digitCoeff p N e h c hN he (s • x) i = s * digitCoeff p N e h c hN he x i := by
    rw [digitCoeff, digitCoeff, map_smul]; rfl
  rw [hd]
  exact Dvd.dvd.mul_left (hx i) s

/-- `Phi` is closed under multiplication by `θ^k`. -/
theorem Phi_theta_pow (hN : 0 < N) (he : 0 < e) (w k : ℕ) {x : Rphi p N e h c}
    (hx : Phi p N e h c hN he w x) :
    Phi p N e h c hN he w (theta p N e h c ^ k * x) := by
  induction k with
  | zero => rwa [pow_zero, one_mul]
  | succ m ih =>
    have : theta p N e h c ^ (m + 1) * x = theta p N e h c * (theta p N e h c ^ m * x) := by
      rw [pow_succ]; ring
    rw [this]
    exact Phi_theta p N e h c hN he w ih

/-- `Phi` is closed under multiplication by an arbitrary ring element (ideal property). -/
theorem Phi_mul (hN : 0 < N) (he : 0 < e) (w : ℕ) (r : Rphi p N e h c) {x : Rphi p N e h c}
    (hx : Phi p N e h c hN he w x) :
    Phi p N e h c hN he w (r * x) := by
  -- write r = assemble (digitCoeff r) = Σ_i d_i • θ^i
  set d := digitCoeff p N e h c hN he r with hd_def
  have hr : r = ∑ i : Fin e, d i • theta p N e h c ^ (i : ℕ) := by
    have hass : assemble p N e h c d = r := assemble_digitCoeff p N e h c hN he r
    rw [assemble] at hass
    rw [← hass]
    apply Finset.sum_congr rfl
    intro i _
    rw [Algebra.smul_def]
  rw [hr, Finset.sum_mul]
  apply Finset.sum_induction _ (fun z => Phi p N e h c hN he w z)
    (fun a b => Phi_add p N e h c hN he w) (Phi_zero p N e h c hN he w)
  intro i _
  -- (d_i • θ^i) * x = d_i • (θ^i * x)
  rw [smul_mul_assoc]
  exact Phi_smul p N e h c hN he w _ (Phi_theta_pow p N e h c hN he w (i : ℕ) hx)

/-- The ideal of elements satisfying `Phi w`. -/
def phiIdeal (hN : 0 < N) (he : 0 < e) (w : ℕ) : Ideal (Rphi p N e h c) where
  carrier := {x | Phi p N e h c hN he w x}
  add_mem' hx hy := Phi_add p N e h c hN he w hx hy
  zero_mem' := Phi_zero p N e h c hN he w
  smul_mem' r _x hx := Phi_mul p N e h c hN he w r hx

theorem mem_phiIdeal (hN : 0 < N) (he : 0 < e) (w : ℕ) (x : Rphi p N e h c) :
    x ∈ phiIdeal p N e h c hN he w ↔ Phi p N e h c hN he w x := Iff.rfl

omit hp in
/-- A single-digit element `algebraMap a · θ^i` (for `i < e`) equals `assemble (Pi.single i a)`. -/
theorem single_digit_eq (i : Fin e) (a : ZMod (p ^ N)) :
    algebraMap (ZMod (p ^ N)) (Rphi p N e h c) a * theta p N e h c ^ (i : ℕ)
      = assemble p N e h c (Pi.single i a) := by
  rw [assemble, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero, zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- `digitCoeff` of a single-digit element is `Pi.single`. -/
theorem digitCoeff_single (hN : 0 < N) (he : 0 < e) (i : Fin e) (a : ZMod (p ^ N)) :
    digitCoeff p N e h c hN he
        (algebraMap (ZMod (p ^ N)) (Rphi p N e h c) a * theta p N e h c ^ (i : ℕ))
      = Pi.single i a := by
  rw [single_digit_eq p N e h c i a, digitCoeff_assemble]

/-! ## The two containments -/

omit hp in
/-- `(p : Rphi)^k = algebraMap (p^k)`. -/
theorem pCast_pow_eq_algebraMap (k : ℕ) :
    ((p : ℕ) : Rphi p N e h c) ^ k
      = algebraMap (ZMod (p ^ N)) (Rphi p N e h c) ((p : ZMod (p ^ N)) ^ k) := by
  rw [map_pow, map_natCast]

omit hp in
/-- **Term membership (⟸ ingredient)**: if `p^(dexp w i) ∣ a` then the single-digit element
`algebraMap a · θ^i` lies in `filtIdeal w`. -/
theorem term_mem_filtIdeal (hN : 0 < N) (he : 0 < e) (w : ℕ) (i : Fin e) {a : ZMod (p ^ N)}
    (hdvd : ((p : ZMod (p ^ N)))^(dexp e h w (i : ℕ)) ∣ a) :
    algebraMap (ZMod (p ^ N)) (Rphi p N e h c) a * theta p N e h c ^ (i : ℕ)
      ∈ filtIdeal p N e h c w := by
  set m := min N (dexp e h w (i : ℕ)) with hm
  -- p^m ∣ a (since m ≤ dexp)
  have hmdvd : ((p : ZMod (p ^ N)))^m ∣ a :=
    dvd_trans (pow_dvd_pow _ (min_le_right _ _)) hdvd
  obtain ⟨b, hb⟩ := hmdvd
  by_cases hval : w ≤ (i : ℕ) * h + e * m
  · -- the monomial θ^i · p^m is a generator of filtIdeal w
    have hval' : (i : ℕ) * h + m * e ≥ w := by rw [Nat.mul_comm m e]; exact hval
    have hgen : theta p N e h c ^ (i : ℕ) * ((p : ℕ) : Rphi p N e h c) ^ m
        ∈ filtIdeal p N e h c w :=
      Ideal.subset_span ⟨(i : ℕ), m, i.isLt, min_le_left _ _, hval', rfl⟩
    -- algebraMap a · θ^i = algebraMap b · (θ^i · p^m)
    have heq : algebraMap (ZMod (p ^ N)) (Rphi p N e h c) a * theta p N e h c ^ (i : ℕ)
        = algebraMap (ZMod (p ^ N)) (Rphi p N e h c) b
            * (theta p N e h c ^ (i : ℕ) * ((p : ℕ) : Rphi p N e h c) ^ m) := by
      rw [hb, map_mul, pCast_pow_eq_algebraMap]; ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ hgen
  · -- w > i*h + e*m; since m = N here (dexp > N), p^m = p^N kills a, so a = 0
    have hmN : m = N := by
      by_contra hne
      have : m = dexp e h w (i : ℕ) := by omega
      rw [hm] at this
      -- then w ≤ i*h + e*dexp (from dexp_le_iff le_rfl), contradiction with hval
      have hd := (dexp_le_iff e h he w (i : ℕ) (dexp e h w (i : ℕ))).mp le_rfl
      rw [← this] at hd
      exact hval hd
    have ha0 : a = 0 := by
      rw [hb, hmN, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
    rw [ha0, map_zero, zero_mul]
    exact Ideal.zero_mem _

/-- **⟸ containment**: `phiIdeal w ≤ filtIdeal w`. -/
theorem phiIdeal_le_filtIdeal (hN : 0 < N) (he : 0 < e) (w : ℕ) :
    phiIdeal p N e h c hN he w ≤ filtIdeal p N e h c w := by
  intro x hx
  rw [mem_phiIdeal] at hx
  -- x = Σ_i algebraMap (a_i) θ^i, each term ∈ filtIdeal
  have hxsum : x = ∑ i : Fin e, algebraMap (ZMod (p ^ N)) (Rphi p N e h c)
      (digitCoeff p N e h c hN he x i) * theta p N e h c ^ (i : ℕ) := by
    have := assemble_digitCoeff p N e h c hN he x
    rw [assemble] at this
    exact this.symm
  rw [hxsum]
  apply Ideal.sum_mem
  intro i _
  exact term_mem_filtIdeal p N e h c hN he w i (hx i)

/-- **⟹ containment**: `filtIdeal w ≤ phiIdeal w` (generators satisfy `Phi`). -/
theorem filtIdeal_le_phiIdeal (hN : 0 < N) (he : 0 < e) (w : ℕ) :
    filtIdeal p N e h c w ≤ phiIdeal p N e h c hN he w := by
  rw [filtIdeal, Ideal.span_le]
  rintro g ⟨i, k, hi, hk, hval, rfl⟩
  -- g = θ^i · p^k = algebraMap (p^k) · θ^i (as single digit at i)
  rw [SetLike.mem_coe, mem_phiIdeal]
  have hg : theta p N e h c ^ i * ((p : ℕ) : Rphi p N e h c) ^ k
      = algebraMap (ZMod (p ^ N)) (Rphi p N e h c) ((p : ZMod (p ^ N)) ^ k)
          * theta p N e h c ^ i := by
    rw [pCast_pow_eq_algebraMap]; ring
  rw [hg]
  intro j
  rw [digitCoeff_single p N e h c hN he ⟨i, hi⟩]
  by_cases hji : j = (⟨i, hi⟩ : Fin e)
  · subst hji
    rw [Pi.single_eq_same]
    -- p^(dexp w i) ∣ p^k since dexp w i ≤ k (from w ≤ i*h + k*e)
    have hle : dexp e h w (i : ℕ) ≤ k := by
      rw [dexp_le_iff e h he, Nat.mul_comm e k]; omega
    exact pow_dvd_pow _ hle
  · rw [Pi.single_eq_of_ne hji]; exact dvd_zero _

/-- **The filtration ideal equals the digit-ball ideal.** -/
theorem filtIdeal_eq_phiIdeal (hN : 0 < N) (he : 0 < e) (w : ℕ) :
    filtIdeal p N e h c w = phiIdeal p N e h c hN he w :=
  le_antisymm (filtIdeal_le_phiIdeal p N e h c hN he w)
    (phiIdeal_le_filtIdeal p N e h c hN he w)

/-! ## The per-coordinate `p`-adic ball count -/

omit c in
/-- **Ball count**: `#{a : ZMod(p^N) | p^m ∣ a} = p^(N-m)` for `m ≤ N`. -/
theorem ball_count (m : ℕ) (hm : m ≤ N) :
    Nat.card {a : ZMod (p ^ N) // ((p : ZMod (p^N)))^m ∣ a} = p ^ (N - m) := by
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set K := RingHom.ker (ZMod.castHom (pow_dvd_pow p hm) (ZMod (p ^ m))) with hK
  have hchar : ∀ a : ZMod (p^N), a ∈ K ↔ ((p : ZMod (p^N)))^m ∣ a := by
    intro a
    rw [hK, RingHom.mem_ker]
    constructor
    · intro hzero
      obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective (n := p^N) a
      rw [map_natCast, ZMod.natCast_eq_zero_iff] at hzero
      obtain ⟨b, rfl⟩ := hzero
      rw [Nat.cast_mul, Nat.cast_pow]
      exact ⟨(b : ZMod (p^N)), rfl⟩
    · intro hdvd
      obtain ⟨b, rfl⟩ := hdvd
      rw [map_mul, map_pow, map_natCast]
      have hz : ((p ^ m : ℕ) : ZMod (p ^ m)) = 0 := ZMod.natCast_self (p ^ m)
      rw [Nat.cast_pow] at hz
      rw [hz, zero_mul]
  have hequiv : {a : ZMod (p ^ N) // ((p : ZMod (p^N)))^m ∣ a} ≃ K :=
    Equiv.subtypeEquivRight (fun a => (hchar a).symm)
  rw [Nat.card_congr hequiv]
  have hquot : Nat.card (ZMod (p ^ N) ⧸ K) = p ^ m := by
    rw [hK, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
          (ZMod.castHom_surjective (pow_dvd_pow p hm))).toEquiv, Nat.card_zmod]
  have hlag := Submodule.card_eq_card_quotient_mul_card (R := ZMod (p^N)) K
  rw [Nat.card_zmod, hquot] at hlag
  have hsplit : p ^ N = p ^ (N - m) * p ^ m := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < p ^ m := pow_pos hp.out.pos m
  exact Nat.eq_of_mul_eq_mul_right hpos (hlag.symm.trans hsplit)

omit c in
/-- Ball count with clamping: `#{a | p^k ∣ a} = p^(N - min N k)` for arbitrary `k`
(when `k > N`, `p^k = 0` so only `a = 0` qualifies, `= p^0 = 1`). -/
theorem ball_count_clamped (k : ℕ) :
    Nat.card {a : ZMod (p ^ N) // ((p : ZMod (p^N)))^k ∣ a} = p ^ (N - min N k) := by
  rcases le_total k N with hle | hle
  · rw [min_eq_right hle, ball_count p N k hle]
  · -- k ≥ N: p^k = 0 = p^N, so the set equals the p^N-ball; min N k = N so target = p^0 = 1
    rw [min_eq_left hle]
    have hpk0 : ((p : ZMod (p ^ N)))^k = 0 := ZMod.natCast_pow_eq_zero_of_le p hle
    have hpN0 : ((p : ZMod (p ^ N)))^N = 0 := by
      have := ZMod.natCast_self (p ^ N)
      rwa [Nat.cast_pow] at this
    have hset : {a : ZMod (p ^ N) // ((p : ZMod (p^N)))^k ∣ a}
        = {a : ZMod (p ^ N) // ((p : ZMod (p^N)))^N ∣ a} := by
      congr 1
      ext a
      rw [hpk0, hpN0]
    rw [hset, ball_count p N N le_rfl]

/-! ## The per-digit product count -/

/-- **The filtration ideal card = per-digit product** (general `e`, general `h`).
`card (filtIdeal w) = ∏_{i<e} p^(N − min N ⌈(w−ih)/e⌉⁺)`. -/
theorem card_filtIdeal (hN : 0 < N) (he : 0 < e) (w : ℕ) :
    Nat.card (filtIdeal p N e h c w)
      = ∏ i : Fin e, p ^ (N - min N (dexp e h w (i : ℕ))) := by
  rw [filtIdeal_eq_phiIdeal p N e h c hN he w]
  -- phiIdeal carrier ≃ {a : Fin e → ZMod | ∀ i, p^(dexp w i) ∣ a i} via digitEquivFull
  have hcarrier : (phiIdeal p N e h c hN he w : Set (Rphi p N e h c))
      = digitEquivFull p N e h c hN he ⁻¹'
          {a : Fin e → ZMod (p ^ N) | ∀ i : Fin e, ((p : ZMod (p^N)))^(dexp e h w (i:ℕ)) ∣ a i} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_setOf_eq]
    rw [mem_phiIdeal]
    rfl
  -- card of ideal (subtype) = card of the ball-product subtype
  have hcard1 : Nat.card (phiIdeal p N e h c hN he w)
      = Nat.card {a : Fin e → ZMod (p ^ N) //
          ∀ i : Fin e, ((p : ZMod (p^N)))^(dexp e h w (i:ℕ)) ∣ a i} := by
    apply Nat.card_congr
    refine (Equiv.subtypeEquiv (digitEquivFull p N e h c hN he).toEquiv ?_)
    intro x
    rw [mem_phiIdeal]
    rfl
  rw [hcard1]
  -- {a // ∀ i, P i (a i)} ≃ ∀ i, {y // P i y}, then Nat.card_pi
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun (i : Fin e) (y : ZMod (p ^ N)) => ((p : ZMod (p^N)))^(dexp e h w (i:ℕ)) ∣ y))]
  rw [Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact ball_count_clamped p N (dexp e h w (i : ℕ))

/-! ## The reverse valuation anchors (exact `vL θ = h`, `vL p = e`) -/

omit hp in
/-- `vL x ≤ w` when `x ∉ filtIdeal (w+1)` (and `w+1 ≤ N·e`). -/
theorem vL_le_of_not_mem (he : 0 < e) {x : Rphi p N e h c} {w : ℕ} (hw : w + 1 ≤ N * e)
    (hmem : x ∉ filtIdeal p N e h c (w + 1)) :
    vL p N e h c x ≤ w := by
  by_contra hcon
  exact hmem ((le_vL_iff p N e h c he hw).mp (Nat.lt_of_not_le hcon))

/-- **Reverse anchor `vL θ = h`** (general `e ≥ 2`, general `h`): upgrades the banked `h ≤ vL θ`
to equality. The `≥` comes from `θ ∉ filtIdeal (h+1)`: `θ`'s only nonzero digit is at `i = 1`
with value `1`, and `dexp (h+1) 1 = 1`, so membership would need `p ∣ 1`. -/
theorem vL_theta_eq (hN : 0 < N) (he2 : 1 < e) (hhN : h ≤ N * e) (hh : 0 < h) :
    vL p N e h c (theta p N e h c) = h := by
  refine le_antisymm ?_ (le_vL_theta p N e h c he2 hhN)
  -- vL θ ≤ h via θ ∉ filtIdeal (h+1)
  have he : 0 < e := by omega
  by_cases hcap : h + 1 ≤ N * e
  · apply vL_le_of_not_mem p N e h c he hcap
    rw [filtIdeal_eq_phiIdeal p N e h c hN he, mem_phiIdeal]
    intro hphi
    -- θ = algebraMap 1 · θ^1, digit at 1 is 1
    have hθ : theta p N e h c
        = algebraMap (ZMod (p ^ N)) (Rphi p N e h c) 1 * theta p N e h c ^ ((⟨1, he2⟩ : Fin e) : ℕ) := by
      rw [map_one, one_mul]; norm_num
    have hd1 := hphi ⟨1, he2⟩
    rw [hθ, digitCoeff_single p N e h c hN he ⟨1, he2⟩, Pi.single_eq_same] at hd1
    -- dexp (h+1) 1 = 1, so p^1 ∣ 1
    have hdexp : 1 ≤ dexp e h (h + 1) ((⟨1, he2⟩ : Fin e) : ℕ) := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      have := (dexp_le_iff e h he (h + 1) ((⟨1, he2⟩ : Fin e) : ℕ) 0).mp (by omega)
      simp only [Fin.val_mk, Nat.mul_zero, Nat.add_zero, Nat.one_mul] at this
      omega
    have hp1 : ((p : ZMod (p ^ N)))^1 ∣ (1 : ZMod (p ^ N)) :=
      dvd_trans (pow_dvd_pow _ hdexp) hd1
    rw [pow_one] at hp1
    -- p ∣ 1 in ZMod(p^N) contradicts p not a unit (N ≥ 1)
    haveI := neZero_pow_base p N hN
    have hunit : IsUnit ((p : ZMod (p ^ N))) := isUnit_of_dvd_one hp1
    rw [ZMod.isUnit_iff_coprime] at hunit
    -- Coprime p (p^N) is false: p ∣ p^N
    have hdvd : p ∣ p ^ N := dvd_pow_self p hN.ne'
    have hne1 : p ≠ 1 := hp.out.one_lt.ne'
    exact hne1 (Nat.eq_one_of_dvd_coprimes hunit (dvd_refl p) hdvd)
  · -- h + 1 > N·e; vL θ ≤ N·e ≤ h
    have := vL_le p N e h c (theta p N e h c)
    omega

omit c in
/-- For `N ≥ 2`, `p^2 ∤ (p : ZMod(p^N))`. -/
theorem not_pSq_dvd_p (hN2 : 2 ≤ N) :
    ¬ (((p : ZMod (p ^ N)))^2 ∣ (p : ZMod (p ^ N))) := by
  intro hdvd
  -- reduce mod p^2 via castHom: p^2 ∣ p ⟹ (p : ZMod(p^2)) = 0 ⟹ p^2 ∣ p in ℕ, false.
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hmap : ((ZMod.castHom (pow_dvd_pow p hN2) (ZMod (p ^ 2))) ((p : ZMod (p ^ N)))) ^ 2
      ∣ (ZMod.castHom (pow_dvd_pow p hN2) (ZMod (p ^ 2))) ((p : ZMod (p ^ N))) := by
    have := map_dvd (ZMod.castHom (pow_dvd_pow p hN2) (ZMod (p ^ 2))) hdvd
    rwa [map_pow] at this
  rw [map_natCast] at hmap
  -- (p : ZMod(p^2))^2 = 0, so 0 ∣ castHom p, so castHom p = 0
  have hp2 : ((p : ZMod (p ^ 2)))^2 = 0 := by
    have := ZMod.natCast_self (p ^ 2)
    rwa [Nat.cast_pow] at this
  rw [hp2, zero_dvd_iff] at hmap
  -- (p : ZMod(p^2)) = 0 ↔ p^2 ∣ p, false
  rw [ZMod.natCast_eq_zero_iff] at hmap
  have : p ^ 2 ≤ p := Nat.le_of_dvd hp.out.pos hmap
  nlinarith [hp.out.one_lt]

/-- **Reverse anchor `vL p = e`** (general `e`, general `h`): upgrades the banked `e ≤ vL p`
to equality. The `≥` comes from `p ∉ filtIdeal (e+1)`: `p`'s only nonzero digit is at `i = 0`
with value `p`, and `dexp (e+1) 0 = 2`, so membership would need `p² ∣ p`. -/
theorem vL_natCast_p_eq (hN : 0 < N) (he : 0 < e) (heN : e ≤ N * e) :
    vL p N e h c (((p : ℕ) : Rphi p N e h c)) = e := by
  refine le_antisymm ?_ (le_vL_natCast_p p N e h c hN he heN)
  by_cases hcap : e + 1 ≤ N * e
  · -- e + 1 ≤ N·e forces N ≥ 2
    have hN2 : 2 ≤ N := by nlinarith [Nat.mul_le_mul_right e (show 1 ≤ N from hN)]
    apply vL_le_of_not_mem p N e h c he hcap
    rw [filtIdeal_eq_phiIdeal p N e h c hN he, mem_phiIdeal]
    intro hphi
    -- p = algebraMap (p:ZMod) · θ^0, digit at 0 is (p:ZMod)
    have hpeq : ((p : ℕ) : Rphi p N e h c)
        = algebraMap (ZMod (p ^ N)) (Rphi p N e h c) ((p : ZMod (p ^ N)))
            * theta p N e h c ^ ((⟨0, he⟩ : Fin e) : ℕ) := by
      rw [map_natCast]; norm_num
    have hd0 := hphi ⟨0, he⟩
    rw [hpeq, digitCoeff_single p N e h c hN he ⟨0, he⟩, Pi.single_eq_same] at hd0
    -- dexp (e+1) 0 = 2, so p^2 ∣ p
    have hdexp : 2 ≤ dexp e h (e + 1) ((⟨0, he⟩ : Fin e) : ℕ) := by
      by_contra hlt
      have hle1 : dexp e h (e + 1) ((⟨0, he⟩ : Fin e) : ℕ) ≤ 1 := Nat.lt_succ_iff.mp
        (Nat.lt_of_not_le hlt)
      -- dexp ≤ 1 means e+1 ≤ 0*h + e*1 = e, false
      have := (dexp_le_iff e h he (e + 1) ((⟨0, he⟩ : Fin e) : ℕ) 1).mp hle1
      simp only [Fin.val_mk, Nat.zero_mul, Nat.zero_add, Nat.mul_one] at this
      omega
    have hp2 : ((p : ZMod (p ^ N)))^2 ∣ (p : ZMod (p ^ N)) :=
      dvd_trans (pow_dvd_pow _ hdexp) hd0
    exact not_pSq_dvd_p p N hN2 hp2
  · have := vL_le p N e h c (((p : ℕ) : Rphi p N e h c))
    omega

/-! ## `h = 1` collapse check -/

/-- **`h = 1` collapse**: at `h = 1` the per-digit product count collapses to the ungapped W1
form `p^(N·e − w)` (via the banked `filtIdeal_eq_span_theta_pow_of_h_one` + `card_span_theta_pow`).
Since `⟨e,1⟩ = ℕ` has no gaps, the product `∏_i p^(N − min N ⌈(w−i)/e⌉)` equals `p^(N·e − w)`. -/
theorem card_filtIdeal_h_one_collapse (hN : 0 < N) (he : 0 < e) {w : ℕ} (hw : w ≤ N * e) :
    Nat.card (filtIdeal p N e 1 c w) = p ^ (N * e - w) := by
  haveI := finite_Rphi p N e 1 c hN he
  rw [filtIdeal_eq_span_theta_pow_of_h_one p N e c hN he hw]
  exact card_span_theta_pow p N e c hN he w hw

/-- The per-digit product itself collapses to `p^(N·e − w)` at `h = 1` (consistency of the
general formula with the ungapped count). -/
theorem prod_dexp_h_one (hN : 0 < N) (he : 0 < e) {w : ℕ} (hw : w ≤ N * e) :
    (∏ i : Fin e, p ^ (N - min N (dexp e 1 w (i : ℕ)))) = p ^ (N * e - w) := by
  have h1 := card_filtIdeal p N e 1 (1 : (ZMod (p ^ N))ˣ) hN he w
  rw [card_filtIdeal_h_one_collapse p N e (1 : (ZMod (p ^ N))ˣ) hN he hw] at h1
  exact h1.symm

/-! ## Gate lemmas (concrete filtration sizes matching `gate_w6a.py`) -/

/-- **Gate (wild gapped ⟨2,3⟩, p=2, N=5, w=2)**: `card (filtIdeal 2) = 512 = 2^9`
(the gate finds `card F_2 = 512`, refuting the naive `2^(N·e−2) = 2^8 = 256`). -/
theorem gate_w6a_e2_h3_N5_w2 (cc : (ZMod (2 ^ 5))ˣ) :
    Nat.card (filtIdeal 2 5 2 3 cc 2) = 512 := by
  rw [card_filtIdeal 2 5 2 3 cc (by norm_num) (by norm_num) 2]; decide

/-- **Gate (wild gapped ⟨2,3⟩, p=2, N=5, w=3)**: `card (filtIdeal 3) = 256 = 2^8`. -/
theorem gate_w6a_e2_h3_N5_w3 (cc : (ZMod (2 ^ 5))ˣ) :
    Nat.card (filtIdeal 2 5 2 3 cc 3) = 256 := by
  rw [card_filtIdeal 2 5 2 3 cc (by norm_num) (by norm_num) 3]; decide

/-- **Gate (wild gapped ⟨2,3⟩, p=2, N=5, w=1)**: `card (filtIdeal 1) = 512 = 2^9`
(equal to `card F_2` — the successive quotient at the semigroup gap `j=1` is index `1`). -/
theorem gate_w6a_e2_h3_N5_w1 (cc : (ZMod (2 ^ 5))ˣ) :
    Nat.card (filtIdeal 2 5 2 3 cc 1) = 512 := by
  rw [card_filtIdeal 2 5 2 3 cc (by norm_num) (by norm_num) 1]; decide

/-- **Gate (wild gapped ⟨2,3⟩, p=2, N=7, w=13)**: the phaseb_w6h wild readable case `N=7`.
`card (filtIdeal 13) = 4 = 2^2`. -/
theorem gate_w6h_e2_h3_N7_w13 (cc : (ZMod (2 ^ 7))ˣ) :
    Nat.card (filtIdeal 2 7 2 3 cc 13) = 4 := by
  rw [card_filtIdeal 2 7 2 3 cc (by norm_num) (by norm_num) 13]; decide

/-- **Gate (h = 1, ungapped, p=3, N=3, e=2, w=3)**: collapses to `p^(N·e−w) = 3^3 = 27`. -/
theorem gate_w6a_e2_h1_N3_w3 (cc : (ZMod (3 ^ 3))ˣ) :
    Nat.card (filtIdeal 3 3 2 1 cc 3) = 27 := by
  rw [card_filtIdeal_h_one_collapse 3 3 2 cc (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end

end LeanUrat.OM.RphiGenHCount
