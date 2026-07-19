import Mathlib
import LeanUrat.OM.RphiRing

/-!
# B-RING, wave W6a: the general-`h` local structure of `Rphi = ZMod (p^N)[X] ⧸ (X^e − c·p^h)`

Blueprint: `uniform-rationality/notes/PHASEB_CLASSIFIER_BLUEPRINT.md` §8 (wave W6a). Extends the
`h = 1` filtration/valuation layer of `LeanUrat.OM.RphiRing` to GENERAL `h` with `gcd(e, h) = 1`.
Math source: `notes/RESTART_LEMMA.md` §2 (Lemma B) / §13.1.

This module is **purely additive**: it imports `RphiRing` and edits nothing there. The
`h`-general base facts it builds on (all already in `RphiRing`, stated for any `h`):
`card_Rphi`, `digitEquiv`, `theta_pow_e`, `theta_pow_mul_eq_zero`, `isNilpotent_theta`,
`exists_natCast_add_theta_mul`.

## W6a NUMERIC-GATE FINDING (mandatory gate, ran FIRST — `/workspace-vast/asving/tmp/phaseb_w6a/`)

The gate (`gate_w6a.py`, exact enumeration; cases `p=2,e=2,h=3,N∈{5,6}`, `p=2,e=3,h=2,N=4`,
`p=3,e=2,h=1,N=3`) **REFUTES the blueprint's filtration-count claim for `h ≥ 2`**:

* The value semigroup of `v_L` on the *level-`N` ring* is the numerical semigroup `⟨e, h⟩`
  (attainable values `{i·h + k·e : i,k ≥ 0}`), **NOT all of `ℤ`**. For `gcd(e,h)=1` with
  `e, h ≥ 2` this semigroup has GAPS (e.g. `⟨2,3⟩` misses `1`). A uniformizer of `v_L = 1` needs
  `θ^a · p^b` with `b < 0` (dividing by `p`), which is not a ring element. So
  `card {x : v_L x ≥ j} = p^(N·e − j)` is **FALSE** whenever `j−1` is a gap: the gate finds
  `card F_2 = card F_1 = p^(Ne−1)` at `p=2,e=2,h=3` (no drop across the `j=1` gap).
* **Correct filtration count (gate-verified exactly, all cases, 0 mismatches):**
  `card {x : v_L x ≥ j} = p^( Σ_{i=0}^{e−1} (N − min(N, ⌈(j − i·h)/e⌉⁺)) )`
  — a per-digit product over the `e` θ-basis coordinates, each `a_i ∈ ZMod(p^N)` constrained by
  `v_p(a_i) ≥ ⌈(j−i·h)/e⌉`. Successive-quotient index is `1` at semigroup gaps, `p` at semigroup
  values; residue field stays `F_p`. For `h = 1` (`⟨e,1⟩ = ℕ`, no gaps) it collapses to the
  W1 `p^(N·e − j)`.
* **The maximal ideal is `span {θ, p}` for general `h`, NOT `span {θ}`** (gate: `p ∉ span{θ}`
  when `e < h`; `span{θ}` is strictly smaller than the nonunits). It collapses to W1's
  `span {θ}` when `h = 1` (there `p ∈ (θ)` via `RphiRing.natCast_p_mem_span_theta`).

Per the STOP-and-report mandate, the false `p^(N·e − j)` count and the `v_L = 1` uniformizer are
NOT banked. This module banks the general-`h` facts that ARE true:

## Deliverables (general `h ≥ 1`, `gcd` not needed for these — they hold for any `h`)

Local structure (BANKED, core-only):
* `pCast_mem_maximalSpan`, `theta_mem_maximalSpan`: `p, θ ∈ span {θ, p}`.
* `isUnit_iff_notMem` (`x` unit ↔ `x ∉ span {θ, p}`), `isLocalRing`,
  `maximalIdeal_eq_span_theta_p` (`m = span {θ, p}`).
* `resHom` (`Rphi → ZMod p`, `θ ↦ 0`) + `resHom_surjective`, `ker_resHom_eq_maximalSpan`;
  `card_quotient_maximalSpan = p` (residue field `F_p`, `f = 1`), `card_residueField`.

The valuation `vL` (BANKED, core-only):
* `filtIdeal j` = the honest `v_L ≥ j` ideal (`span {θ^i·p^k : i·h+k·e ≥ j}`); `filtIdeal_antitone`,
  `filtIdeal_zero_eq_top`, `theta_mem_filtIdeal` (`θ ∈ filtIdeal h`), `natCast_p_mem_filtIdeal`
  (`p ∈ filtIdeal e`).
* `vL x` = largest `j ≤ N·e` with `x ∈ filtIdeal j`; `vL_le`, `mem_filtIdeal_vL`, `le_vL_iff`,
  `vL_zero`, and the membership LOWER bounds `le_vL_theta` (`h ≤ vL θ`), `le_vL_natCast_p`
  (`e ≤ vL p`).

Compatibility with the `h = 1` W1 layer (BANKED, core-only):
* `span_theta_p_eq_span_theta_of_h_one` (`h = 1 ⟹ span {θ, p} = span {θ}`), so
  `maximalIdeal_eq_span_theta_p` recovers `RphiRing.maximalIdeal_eq`.
* `filtIdeal_eq_span_theta_pow_of_h_one` + `vL_eq_vphi_of_h_one` (`h = 1 ⟹ vL = RphiRing.vphi`).

## NAMED RESIDUAL (not banked — the honest ledger)

* The EXACT anchors `vL θ = h`, `vL p = e` (reverse `≤` inequalities) and the corrected
  filtration count `card (filtIdeal j) = p^(Σ ...)` for `h ≥ 2`. These need the per-digit product
  count (strictness of the `⟨e,h⟩`-graded filtration), which is the fresh substantial proof this
  wave defers. The gate has verified the product formula exactly; the blueprint's `p^(N·e−j)` is
  refuted, so the false statement is deliberately NOT stated here. The count for general `e ≥ 3`
  is at least as hard (more coordinates); `e = 2` is the first tractable target for the follow-up.

Discipline: no `sorry`/`axiom`/`native_decide`; mathlib-only imports beyond `RphiRing`;
core-only footprint (checked with `#print axioms`, prints removed after checking).
-/

namespace LeanUrat.OM.RphiRingGenH

open Polynomial LeanUrat.OM.RphiRing

variable (p N e h : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ)

noncomputable section

/-! ## The general-`h` maximal ideal `span {θ, p}` -/

def maximalSpan : Ideal (Rphi p N e h c) :=
  Ideal.span {theta p N e h c, ((p : ℕ) : Rphi p N e h c)}

omit hp in
theorem theta_mem_maximalSpan : theta p N e h c ∈ maximalSpan p N e h c :=
  Ideal.subset_span (by left; rfl)

omit hp in
theorem pCast_mem_maximalSpan :
    ((p : ℕ) : Rphi p N e h c) ∈ maximalSpan p N e h c :=
  Ideal.subset_span (by right; rfl)

omit hp in
theorem mem_maximalSpan_iff (x : Rphi p N e h c) :
    x ∈ maximalSpan p N e h c ↔
      ∃ a b : Rphi p N e h c,
        x = theta p N e h c * a + ((p : ℕ) : Rphi p N e h c) * b := by
  unfold maximalSpan
  rw [Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩; exact ⟨a, b, by ring⟩
  · rintro ⟨a, b, rfl⟩; exact ⟨a, b, by ring⟩

omit hp in
/-- `p^N = 0` in `Rphi` (the base ring `ZMod (p^N)` has characteristic `p^N`). -/
theorem pCast_pow_N_eq_zero :
    ((p : ℕ) : Rphi p N e h c) ^ N = 0 := by
  rw [← Nat.cast_pow]
  have : ((p ^ N : ℕ) : ZMod (p ^ N)) = 0 := by
    rw [ZMod.natCast_self]
  calc ((p ^ N : ℕ) : Rphi p N e h c)
      = algebraMap (ZMod (p ^ N)) (Rphi p N e h c) ((p ^ N : ℕ) : ZMod (p ^ N)) := by
        rw [map_natCast]
    _ = algebraMap (ZMod (p ^ N)) (Rphi p N e h c) 0 := by rw [this]
    _ = 0 := map_zero _

omit hp in
theorem isNilpotent_pCast : IsNilpotent (((p : ℕ) : Rphi p N e h c)) :=
  ⟨N, pCast_pow_N_eq_zero p N e h c⟩

/-! ## The unit criterion for general `h` -/

theorem isUnit_iff_notMem (hN : 0 < N) (he : 0 < e) (hh : 0 < h) (x : Rphi p N e h c) :
    IsUnit x ↔ x ∉ maximalSpan p N e h c := by
  constructor
  · intro hx hmem
    haveI := nontrivial_Rphi p N e h c hN he
    obtain ⟨a, b, hab⟩ := (mem_maximalSpan_iff p N e h c x).mp hmem
    have hθnil : IsNilpotent (theta p N e h c * a) :=
      Commute.isNilpotent_mul_right (Commute.all _ _) (isNilpotent_theta p N e h c hN hh)
    have hpnil : IsNilpotent (((p : ℕ) : Rphi p N e h c) * b) :=
      Commute.isNilpotent_mul_right (Commute.all _ _) (isNilpotent_pCast p N e h c)
    have hxnil : IsNilpotent x := by
      rw [hab]; exact Commute.isNilpotent_add (Commute.all _ _) hθnil hpnil
    exact hx.not_isNilpotent hxnil
  · intro hmem
    obtain ⟨n, w, hw⟩ := exists_natCast_add_theta_mul p N e h c hN x
    have hpn : ¬ (p ∣ n) := by
      rintro ⟨m, hm⟩
      apply hmem
      rw [hw, hm]
      apply Ideal.add_mem
      · push_cast
        rw [mul_comm ((p : ℕ) : Rphi p N e h c) ((m : ℕ) : Rphi p N e h c)]
        exact Ideal.mul_mem_left _ _ (pCast_mem_maximalSpan p N e h c)
      · exact Ideal.mul_mem_right _ _ (theta_mem_maximalSpan p N e h c)
    haveI := neZero_pow_base p N hN
    have hun : IsUnit ((n : ℕ) : ZMod (p ^ N)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpn).symm.pow_right N
    have hunR : IsUnit ((n : ℕ) : Rphi p N e h c) := by
      have h3 := hun.map (algebraMap (ZMod (p ^ N)) (Rphi p N e h c))
      rwa [map_natCast] at h3
    have hnil : IsNilpotent (theta p N e h c * w) :=
      Commute.isNilpotent_mul_right (Commute.all _ _) (isNilpotent_theta p N e h c hN hh)
    rw [hw]
    exact hnil.isUnit_add_left_of_commute hunR (Commute.all _ _)

/-! ## Localness, maximal ideal, residue field (general `h`) -/

theorem isLocalRing (hN : 0 < N) (he : 0 < e) (hh : 0 < h) :
    IsLocalRing (Rphi p N e h c) := by
  haveI := nontrivial_Rphi p N e h c hN he
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_notMem p N e h c hN he hh, not_not] at ha hb ⊢
  exact Ideal.add_mem _ ha hb

theorem maximalIdeal_eq_span_theta_p [IsLocalRing (Rphi p N e h c)]
    (hN : 0 < N) (he : 0 < e) (hh : 0 < h) :
    IsLocalRing.maximalIdeal (Rphi p N e h c) = maximalSpan p N e h c := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_notMem p N e h c hN he hh,
    not_not]

/-! ## Residue field (`f = 1`, general `h`): `Rphi ⧸ span {θ, p} ≅ ZMod p` -/

/-- `eval₂` of `φ` at `X ↦ 0` under reduction `ZMod (p^N) → ZMod p` vanishes (needs `h ≥ 1`:
`φ(0) = −c·p^h ≡ 0 mod p`). -/
theorem eval2_phi_zero (hN : 0 < N) (he : 0 < e) (hh : 0 < h) :
    (phi p N e h c).eval₂ (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) 0 = 0 := by
  haveI := neZero_pow_base p N hN
  rw [phi_eq, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  have hcp : (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p))
      ((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h) = 0 := by
    rw [map_mul, map_pow]
    have hp0 : (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) ((p : ZMod (p ^ N))) = 0 := by
      rw [map_natCast, ZMod.natCast_self]
    rw [hp0, zero_pow hh.ne', mul_zero]
  rw [hcp, sub_zero, zero_pow he.ne']

/-- The residue map `Rphi → ZMod p`, `θ ↦ 0`, base reduced `mod p`. -/
def resHom (hN : 0 < N) (he : 0 < e) (hh : 0 < h) : Rphi p N e h c →+* ZMod p :=
  AdjoinRoot.lift (ZMod.castHom (dvd_pow_self p hN.ne') (ZMod p)) 0
    (eval2_phi_zero p N e h c hN he hh)

theorem resHom_theta (hN : 0 < N) (he : 0 < e) (hh : 0 < h) :
    resHom p N e h c hN he hh (theta p N e h c) = 0 := by
  rw [resHom, theta_eq_root, AdjoinRoot.lift_root]

theorem resHom_natCast_p (hN : 0 < N) (he : 0 < e) (hh : 0 < h) :
    resHom p N e h c hN he hh (((p : ℕ) : Rphi p N e h c)) = 0 := by
  haveI := neZero_pow_base p N hN
  rw [resHom, ← map_natCast (algebraMap (ZMod (p ^ N)) (Rphi p N e h c)) p,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, map_natCast, ZMod.natCast_self]

theorem resHom_surjective (hN : 0 < N) (he : 0 < e) (hh : 0 < h) :
    Function.Surjective (resHom p N e h c hN he hh) := by
  haveI := neZero_pow_base p N hN
  intro y
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective y
  refine ⟨((n : ℕ) : Rphi p N e h c), ?_⟩
  rw [resHom, ← map_natCast (algebraMap (ZMod (p ^ N)) (Rphi p N e h c)) n,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of, map_natCast]

/-- The kernel of `resHom` equals `span {θ, p}` (both are the maximal ideal). -/
theorem ker_resHom_eq_maximalSpan [IsLocalRing (Rphi p N e h c)]
    (hN : 0 < N) (he : 0 < e) (hh : 0 < h) :
    RingHom.ker (resHom p N e h c hN he hh) = maximalSpan p N e h c := by
  rw [IsLocalRing.ker_eq_maximalIdeal (resHom p N e h c hN he hh)
        (resHom_surjective p N e h c hN he hh),
      maximalIdeal_eq_span_theta_p p N e h c hN he hh]

/-- **Residue field count (general `h`)**: `|Rphi ⧸ span {θ, p}| = p` — the `f = 1` residue
field is `F_p`, unchanged from `h = 1`. -/
theorem card_quotient_maximalSpan [IsLocalRing (Rphi p N e h c)]
    (hN : 0 < N) (he : 0 < e) (hh : 0 < h) :
    Nat.card (Rphi p N e h c ⧸ maximalSpan p N e h c) = p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [← ker_resHom_eq_maximalSpan p N e h c hN he hh]
  rw [Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (resHom_surjective p N e h c hN he hh)).toEquiv]
  rw [Nat.card_zmod]

/-- **Residue field count** via `IsLocalRing.maximalIdeal`. -/
theorem card_residueField [IsLocalRing (Rphi p N e h c)]
    (hN : 0 < N) (he : 0 < e) (hh : 0 < h) :
    Nat.card (Rphi p N e h c ⧸ IsLocalRing.maximalIdeal (Rphi p N e h c)) = p := by
  rw [maximalIdeal_eq_span_theta_p p N e h c hN he hh]
  exact card_quotient_maximalSpan p N e h c hN he hh

/-! ## The general-`h` `L`-valuation `vL`

Defined via the honest `v_L`-filtration ideal `filtIdeal j = {x : v_L x ≥ j}`, spelled as the
ideal generated by the monomials `θ^i · p^k` with `i·h + k·e ≥ j` (their `v_L` is `i·h + k·e`).
This is the level-`N` avatar of `{y ∈ O_L : v_L y ≥ j}`. `vL x` is the largest such `j ≤ N·e`.

NUMERIC-GATE NOTE (see module header): for `h ≥ 2` the value semigroup is `⟨e,h⟩` (has gaps), so
`card (filtIdeal j) = p^(N·e − j)` is FALSE; the correct count is the per-digit product formula.
Banked here: `vL` well-defined, `vL_zero`, monotonicity, and the membership LOWER bounds
`h ≤ vL θ`, `e ≤ vL p`. The EXACT anchors `vL θ = h`, `vL p = e` and the corrected filtration
count are the named residual (they need the per-digit product count, refuting `p^(N·e−j)`). -/

/-- The `v_L ≥ j` filtration ideal: generated by `θ^i · p^k` with `i·h + k·e ≥ j`
(`i < e`, `k ≤ N`). -/
def filtIdeal (j : ℕ) : Ideal (Rphi p N e h c) :=
  Ideal.span
    {x : Rphi p N e h c |
      ∃ i k : ℕ, i < e ∧ k ≤ N ∧ i * h + k * e ≥ j ∧
        x = theta p N e h c ^ i * ((p : ℕ) : Rphi p N e h c) ^ k}

omit hp in
/-- `filtIdeal` is antitone: larger `j` ⟹ fewer generators ⟹ smaller ideal. -/
theorem filtIdeal_antitone {i j : ℕ} (hij : i ≤ j) :
    filtIdeal p N e h c j ≤ filtIdeal p N e h c i := by
  rw [filtIdeal, filtIdeal, Ideal.span_le]
  rintro x ⟨a, k, ha, hk, hval, rfl⟩
  exact Ideal.subset_span ⟨a, k, ha, hk, le_trans hij hval, rfl⟩

omit hp in
theorem filtIdeal_zero_eq_top (he : 0 < e) : filtIdeal p N e h c 0 = ⊤ := by
  rw [filtIdeal, Ideal.eq_top_iff_one]
  refine Ideal.subset_span ⟨0, 0, he, Nat.zero_le _, by omega, ?_⟩
  simp

omit hp in
/-- `θ ∈ filtIdeal h` (take `i = 1, k = 0`: `v_L(θ) = h`, needs `e ≥ 2` so `1 < e`). -/
theorem theta_mem_filtIdeal (he2 : 1 < e) : theta p N e h c ∈ filtIdeal p N e h c h := by
  refine Ideal.subset_span ⟨1, 0, he2, Nat.zero_le _, by omega, ?_⟩
  simp

omit hp in
/-- `p ∈ filtIdeal e` (take `i = 0, k = 1`: `v_L(p) = e`, needs `N ≥ 1`). -/
theorem natCast_p_mem_filtIdeal (hN : 0 < N) (he : 0 < e) :
    ((p : ℕ) : Rphi p N e h c) ∈ filtIdeal p N e h c e := by
  refine Ideal.subset_span ⟨0, 1, he, hN, by omega, ?_⟩
  simp

open Classical in
/-- **`vL` (general `h`)**: largest `j ≤ N·e` with `x ∈ filtIdeal j`. -/
def vL (x : Rphi p N e h c) : ℕ :=
  Nat.findGreatest (fun j => x ∈ filtIdeal p N e h c j) (N * e)

omit hp in
theorem vL_le (x : Rphi p N e h c) : vL p N e h c x ≤ N * e := by
  classical
  unfold vL; exact Nat.findGreatest_le _

omit hp in
theorem mem_filtIdeal_vL (he : 0 < e) (x : Rphi p N e h c) :
    x ∈ filtIdeal p N e h c (vL p N e h c x) := by
  classical
  unfold vL
  refine Nat.findGreatest_spec (P := fun j => x ∈ filtIdeal p N e h c j) (m := 0)
    (Nat.zero_le _) ?_
  rw [filtIdeal_zero_eq_top p N e h c he]; exact Submodule.mem_top

omit hp in
theorem le_vL_iff (he : 0 < e) {x : Rphi p N e h c} {j : ℕ} (hj : j ≤ N * e) :
    j ≤ vL p N e h c x ↔ x ∈ filtIdeal p N e h c j := by
  classical
  constructor
  · intro hle
    exact filtIdeal_antitone p N e h c hle (mem_filtIdeal_vL p N e h c he x)
  · intro hmem; unfold vL; exact Nat.le_findGreatest hj hmem

omit hp in
theorem vL_zero (he : 0 < e) : vL p N e h c 0 = N * e :=
  le_antisymm (vL_le p N e h c 0)
    ((le_vL_iff p N e h c he le_rfl).mpr (Ideal.zero_mem _))

omit hp in
/-- **Lower bound `h ≤ vL θ`** (membership; the reverse `vL θ ≤ h` is the named residual). -/
theorem le_vL_theta (he2 : 1 < e) (hhN : h ≤ N * e) :
    h ≤ vL p N e h c (theta p N e h c) :=
  (le_vL_iff p N e h c (by omega) hhN).mpr (theta_mem_filtIdeal p N e h c he2)

omit hp in
/-- **Lower bound `e ≤ vL p`** (membership; the reverse `vL p ≤ e` is the named residual). -/
theorem le_vL_natCast_p (hN : 0 < N) (he : 0 < e) (heN : e ≤ N * e) :
    e ≤ vL p N e h c (((p : ℕ) : Rphi p N e h c)) :=
  (le_vL_iff p N e h c (by omega) heN).mpr (natCast_p_mem_filtIdeal p N e h c hN he)

/-! ## Compatibility with the `h = 1` W1 layer -/

/-- For `h = 1`, `span {θ, p} = span {θ}` (since `p ∈ (θ)`), so
`maximalIdeal_eq_span_theta_p` recovers `RphiRing.maximalIdeal_eq`. -/
theorem span_theta_p_eq_span_theta_of_h_one (he : 0 < e) :
    maximalSpan p N e 1 c = Ideal.span {theta p N e 1 c} := by
  apply le_antisymm
  · rw [maximalSpan, Ideal.span_le]
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact Ideal.subset_span rfl
    · rw [Set.mem_singleton_iff] at hx; rw [hx]
      exact natCast_p_mem_span_theta p N e c he
  · rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx; rw [hx]
    exact theta_mem_maximalSpan p N e 1 c

/-- **Compatibility (`h = 1`)**: the general-`h` filtration ideal equals the `θ`-adic ideal of
`RphiRing` when `h = 1`. (`θ^i · p^k = unit · θ^(i + k·e)`, and `⟨e,1⟩ = ℕ` has no gaps, so the
generating monomials of value `≥ j` are exactly `unit · θ^{≥ j}`.) -/
theorem filtIdeal_eq_span_theta_pow_of_h_one (_hN : 0 < N) (he : 0 < e) {j : ℕ}
    (hj : j ≤ N * e) :
    filtIdeal p N e 1 c j = Ideal.span {theta p N e 1 c ^ j} := by
  -- `p^k = (c⁻¹)^k · θ^(k·e)` (from `natCast_p_eq`, `θ^e = c·p`, `h = 1`).
  have hp : ∀ k : ℕ, ((p : ℕ) : Rphi p N e 1 c) ^ k
      = (((cUnit p N e 1 c)⁻¹ : (Rphi p N e 1 c)ˣ) : Rphi p N e 1 c) ^ k
        * theta p N e 1 c ^ (k * e) := fun k => by
    rw [natCast_p_eq p N e c, mul_pow, ← pow_mul, Nat.mul_comm e k]
  apply le_antisymm
  · rw [filtIdeal, Ideal.span_le]
    rintro x ⟨i, k, _, _, hval, rfl⟩
    -- `θ^i · p^k = (c⁻¹)^k · θ^(i + k·e)`, and `i·1 + k·e = i + k·e ≥ j`.
    rw [hp k]
    have hge : i + k * e ≥ j := by simpa using hval
    have hmem : theta p N e 1 c ^ i * theta p N e 1 c ^ (k * e)
        ∈ Ideal.span {theta p N e 1 c ^ j} := by
      rw [← pow_add]
      exact Ideal.mem_span_singleton'.mpr
        ⟨theta p N e 1 c ^ (i + k * e - j), by rw [← pow_add]; congr 1; omega⟩
    have heq : theta p N e 1 c ^ i
          * ((((cUnit p N e 1 c)⁻¹ : (Rphi p N e 1 c)ˣ) : Rphi p N e 1 c) ^ k
            * theta p N e 1 c ^ (k * e))
        = (((cUnit p N e 1 c)⁻¹ : (Rphi p N e 1 c)ˣ) : Rphi p N e 1 c) ^ k
            * (theta p N e 1 c ^ i * theta p N e 1 c ^ (k * e)) := by ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ hmem
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    -- `θ^j = c^k · θ^i · p^k` with `i = j % e`, `k = j / e`; `i + k·e = j` and `k ≤ N`.
    set i := j % e with hi_def
    set k := j / e with hk_def
    have hik : i + k * e = j := by
      rw [hi_def, hk_def, Nat.mul_comm]; exact Nat.mod_add_div j e
    have hival : i < e := Nat.mod_lt _ he
    have hkN : k ≤ N := by
      rw [hk_def]; exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hj)
    have hcancel : ((cUnit p N e 1 c : Rphi p N e 1 c)) ^ k
        * (((cUnit p N e 1 c)⁻¹ : (Rphi p N e 1 c)ˣ) : Rphi p N e 1 c) ^ k = 1 := by
      rw [← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
    have hexp : theta p N e 1 c ^ j
        = ((cUnit p N e 1 c : Rphi p N e 1 c)) ^ k
          * (theta p N e 1 c ^ i * ((p : ℕ) : Rphi p N e 1 c) ^ k) := by
      rw [hp k]
      calc theta p N e 1 c ^ j
          = theta p N e 1 c ^ i * theta p N e 1 c ^ (k * e) := by
            rw [← pow_add, hik]
        _ = (((cUnit p N e 1 c : Rphi p N e 1 c)) ^ k
              * (((cUnit p N e 1 c)⁻¹ : (Rphi p N e 1 c)ˣ) : Rphi p N e 1 c) ^ k)
            * (theta p N e 1 c ^ i * theta p N e 1 c ^ (k * e)) := by rw [hcancel, one_mul]
        _ = ((cUnit p N e 1 c : Rphi p N e 1 c)) ^ k
            * (theta p N e 1 c ^ i
              * ((((cUnit p N e 1 c)⁻¹ : (Rphi p N e 1 c)ˣ) : Rphi p N e 1 c) ^ k
                * theta p N e 1 c ^ (k * e))) := by ring
    rw [hexp]
    refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, k, hival, hkN, ?_, rfl⟩)
    rw [Nat.mul_one]; omega

/-- Two `Nat.findGreatest` at the same bound agree when the predicates agree on `[0, n]`. -/
private theorem findGreatest_congr_of_agree {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    {n : ℕ} (hPQ : ∀ j, j ≤ n → (P j ↔ Q j)) :
    Nat.findGreatest P n = Nat.findGreatest Q n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hstep := hPQ (m + 1) le_rfl
    have hih : Nat.findGreatest P m = Nat.findGreatest Q m :=
      ih (fun j hj => hPQ j (Nat.le_succ_of_le hj))
    rw [Nat.findGreatest_succ, Nat.findGreatest_succ, hih]
    by_cases hp : P (m + 1)
    · rw [if_pos hp, if_pos (hstep.mp hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hstep.mpr hq))]

/-- **Compatibility (`h = 1`)**: `vL = vphi` (the general-`h` valuation restricts to the W1
`θ`-adic reader). -/
theorem vL_eq_vphi_of_h_one (hN : 0 < N) (he : 0 < e) (x : Rphi p N e 1 c) :
    vL p N e 1 c x = vphi p N e c x := by
  classical
  unfold vL vphi
  refine findGreatest_congr_of_agree (fun j hj => ?_)
  rw [filtIdeal_eq_span_theta_pow_of_h_one p N e c hN he hj]

end

end LeanUrat.OM.RphiRingGenH
