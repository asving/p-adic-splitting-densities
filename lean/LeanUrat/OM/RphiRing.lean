import Mathlib

/-!
# B-RING (Phase-B W1): the level-N avatar of `O_L` — `Rphi = ZMod (p^N)[X] ⧸ (φ')`

Blueprint: `uniform-rationality/notes/PHASEB_CLASSIFIER_BLUEPRINT.md` §5 (wave W1).
Math source: `uniform-rationality/notes/RESTART_LEMMA.md` §2 (Lemma B, the side lift) and §3
Step 2 (the totally ramified descent, `f = 1`): the child key `φ' = X^e − c·p^h` with
`gcd(e,h) = 1`, and for `h = 1` (the genuinely Eisenstein case) the quotient
`Rphi := ZMod (p^N)[X] ⧸ (span {φ'})` is the level-N truncation of the ramified extension ring
`O_L = O[θ]`, `θ^e = c·p`.

Numeric gate (mandatory, ran first): `/workspace-vast/asving/tmp/phaseb_w1/gate_w1.py`
(p = 2, N ∈ {1,2,3}, e = 2, c = 1, h = 1, plus p = 3 spot checks) — verifies every statement
banked below: `card = p^(N·e)`, filtration sizes `p^(N·e−j)`, residue field size `p`,
`nonunits = (θ)`, and the `vphi` table. GATE PASS 2026-07-04.

## Deliverables (h = 1 unless stated; general `h` kept where it is free)

1. `card_Rphi : Nat.card Rphi = p^(N·e)` (any `h`), and the digit identification
   `digitEquiv : degreeLT (ZMod (p^N)) e ≃ₗ[ZMod (p^N)] Rphi` whose forward map is literally
   the quotient map (`digitEquiv_apply`) — RESTART_LEMMA §2's "`b ↦ b(θ)` carries digit
   spaces to `O_L`" at level N.
2. Local structure at `h = 1`: `theta_pow_e` (`θ^e = c·p`, stated for any `h`),
   `theta_pow_mul_eq_zero` / `isNilpotent_theta` (`θ^(N·e) = 0`, any `h ≥ 1`),
   `isUnit_iff_notMem` (`x` unit ↔ `x ∉ (θ)`), `isLocalRing`, `maximalIdeal_eq` (`m = (θ)`),
   `card_residueField` (`|Rphi/m| = p`, the δ = f = 1 case).
3. The π-adic filtration count: `card_span_theta_pow` (`|(θ^j)| = p^(N·e−j)` for `j ≤ N·e`),
   `card_quotient_span_theta_pow` (`|Rphi/(θ^j)| = p^j`), and the successive quotient
   `card_map_span_theta_pow` (`|(θ^j)/(θ^(j+1))| = p`, spelled as the image ideal in
   `Rphi/(θ^(j+1))`).
4. `vphi : Rphi → ℕ` (largest `j ≤ N·e` with `x ∈ (θ^j)`; junk value `N·e` at 0) with spec:
   `vphi_theta = 1`, `vphi_natCast_p = e`, `isUnit_iff_vphi_eq_zero`, `min_le_vphi_mul`,
   `vphi_theta_pow`, `vphi_unit_mul`, `vphi_zero`.

Discipline: no `sorry`/`axiom`/`native_decide`; mathlib-only imports; core-only footprints
(checked with `#print axioms`, prints removed after checking).
-/

namespace LeanUrat.OM.RphiRing

open Polynomial

variable (p N e h : ℕ) [hp : Fact p.Prime] (c : (ZMod (p ^ N))ˣ)

noncomputable section

/-! ## Base-ring helpers -/

theorem one_lt_pow_base (hN : 0 < N) : 1 < p ^ N :=
  one_lt_pow' hp.out.one_lt hN.ne'

theorem neZero_pow_base (hN : 0 < N) : NeZero (p ^ N) :=
  ⟨(Nat.zero_lt_of_lt (one_lt_pow_base p N hN)).ne'⟩

theorem nontrivial_base (hN : 0 < N) : Nontrivial (ZMod (p ^ N)) :=
  haveI : Fact (1 < p ^ N) := ⟨one_lt_pow_base p N hN⟩
  ZMod.nontrivial _

/-! ## The key polynomial and the ring -/

/-- The child key polynomial `φ' = X^e − c·p^h` at level `N` (blueprint §5; RESTART_LEMMA §2's
side lift with `f = 1`). For `h = 1` this is the genuinely Eisenstein case. -/
def phi : (ZMod (p ^ N))[X] :=
  X ^ e - C (c : ZMod (p ^ N)) * C ((p : ZMod (p ^ N))) ^ h

omit hp in
theorem phi_eq :
    phi p N e h c = X ^ e - C ((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h) := by
  simp only [phi, map_mul, map_pow]

theorem monic_phi (he : 0 < e) : (phi p N e h c).Monic := by
  rw [phi_eq]; exact monic_X_pow_sub_C _ he.ne'

theorem natDegree_phi (hN : 0 < N) : (phi p N e h c).natDegree = e := by
  haveI := nontrivial_base p N hN
  rw [phi_eq]; exact natDegree_X_pow_sub_C

theorem degree_phi (hN : 0 < N) (he : 0 < e) : (phi p N e h c).degree = e := by
  haveI := nontrivial_base p N hN
  rw [phi_eq]; exact degree_X_pow_sub_C he _

/-- The restart target ring `Rphi = (ZMod (p^N))[X] ⧸ (Ideal.span {phi})`, spelled via
`AdjoinRoot` (which is *reducibly* that quotient — see `Rphi_eq_quotient`) so that the full
`AdjoinRoot` API applies. -/
abbrev Rphi : Type _ := AdjoinRoot (phi p N e h c)

omit hp in
theorem Rphi_eq_quotient :
    Rphi p N e h c = ((ZMod (p ^ N))[X] ⧸ Ideal.span {phi p N e h c}) := rfl

/-- `θ`, the image of `X` in `Rphi` (the level-N avatar of the uniformizer for `h = 1`). -/
def theta : Rphi p N e h c := AdjoinRoot.root (phi p N e h c)

omit hp in
theorem theta_eq_root : theta p N e h c = AdjoinRoot.root (phi p N e h c) := rfl

/-! ## Deliverable 1: digit identification and cardinality -/

/-- The `ZMod (p^N)`-linear "assemble digits" map: inclusion of `degreeLT` followed by the
quotient map. -/
def digitMap : degreeLT (ZMod (p ^ N)) e →ₗ[ZMod (p ^ N)] Rphi p N e h c :=
  (AdjoinRoot.mkₐ (phi p N e h c)).toLinearMap ∘ₗ (degreeLT (ZMod (p ^ N)) e).subtype

omit hp in
@[simp] theorem digitMap_apply (b : degreeLT (ZMod (p ^ N)) e) :
    digitMap p N e h c b = AdjoinRoot.mk (phi p N e h c) (b : (ZMod (p ^ N))[X]) := rfl

theorem digitMap_injective (hN : 0 < N) (he : 0 < e) :
    Function.Injective (digitMap p N e h c) := by
  haveI := nontrivial_base p N hN
  rw [injective_iff_map_eq_zero]
  rintro ⟨b, hb⟩ hb0
  apply Subtype.ext
  show b = 0
  by_contra hne
  exact AdjoinRoot.mk_ne_zero_of_degree_lt (monic_phi p N e h c he) hne
    (by rw [degree_phi p N e h c hN he]; exact mem_degreeLT.mp hb) hb0

theorem digitMap_surjective (hN : 0 < N) (he : 0 < e) :
    Function.Surjective (digitMap p N e h c) := by
  haveI := nontrivial_base p N hN
  intro x
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨⟨g %ₘ phi p N e h c, mem_degreeLT.mpr ?_⟩, ?_⟩
  · rw [← degree_phi p N e h c hN he]
    exact degree_modByMonic_lt g (monic_phi p N e h c he)
  · rw [digitMap_apply]
    have hmod : g %ₘ phi p N e h c + phi p N e h c * (g /ₘ phi p N e h c) = g :=
      modByMonic_add_div g (phi p N e h c)
    exact AdjoinRoot.mk_eq_mk.mpr ⟨-(g /ₘ phi p N e h c), by linear_combination hmod⟩

/-- **Deliverable 1 (digit identification, blueprint §5 bullet 2)**: polynomials of degree
`< e` map `ZMod (p^N)`-linearly and bijectively onto `Rphi` via the quotient map. -/
def digitEquiv (hN : 0 < N) (he : 0 < e) :
    degreeLT (ZMod (p ^ N)) e ≃ₗ[ZMod (p ^ N)] Rphi p N e h c :=
  LinearEquiv.ofBijective (digitMap p N e h c)
    ⟨digitMap_injective p N e h c hN he, digitMap_surjective p N e h c hN he⟩

@[simp] theorem digitEquiv_apply (hN : 0 < N) (he : 0 < e) (b : degreeLT (ZMod (p ^ N)) e) :
    digitEquiv p N e h c hN he b
      = AdjoinRoot.mk (phi p N e h c) (b : (ZMod (p ^ N))[X]) := rfl

theorem finite_Rphi (hN : 0 < N) (he : 0 < e) : Finite (Rphi p N e h c) := by
  haveI := neZero_pow_base p N hN
  exact Finite.of_equiv _
    ((degreeLTEquiv (ZMod (p ^ N)) e).toEquiv.symm.trans
      (digitEquiv p N e h c hN he).toEquiv)

/-- **Deliverable 1 (cardinality)**: `card Rphi = p^(N·e)`. -/
theorem card_Rphi (hN : 0 < N) (he : 0 < e) :
    Nat.card (Rphi p N e h c) = p ^ (N * e) := by
  haveI := neZero_pow_base p N hN
  calc Nat.card (Rphi p N e h c)
      = Nat.card (degreeLT (ZMod (p ^ N)) e) :=
        (Nat.card_congr (digitEquiv p N e h c hN he).toEquiv).symm
    _ = Nat.card (Fin e → ZMod (p ^ N)) :=
        Nat.card_congr (degreeLTEquiv (ZMod (p ^ N)) e).toEquiv
    _ = p ^ (N * e) := by
        rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin,
          ← pow_mul]

theorem nontrivial_Rphi (hN : 0 < N) (he : 0 < e) : Nontrivial (Rphi p N e h c) := by
  have hcard := card_Rphi p N e h c hN he
  refine ⟨0, 1, fun h01 => ?_⟩
  haveI : Subsingleton (Rphi p N e h c) := subsingleton_of_zero_eq_one h01
  have h1 : Nat.card (Rphi p N e h c) = 1 := Nat.card_of_subsingleton 0
  rw [hcard] at h1
  have h2 : 1 < p ^ (N * e) :=
    one_lt_pow' hp.out.one_lt (Nat.mul_ne_zero hN.ne' he.ne')
  omega

/-! ## Deliverable 2: local structure (`h = 1` for the Eisenstein facts) -/

/-- The defining relation: `θ^e = c·p^h` (image in `Rphi`). -/
theorem theta_pow_e :
    theta p N e h c ^ e =
      algebraMap (ZMod (p ^ N)) (Rphi p N e h c)
        ((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h) := by
  have h1 : AdjoinRoot.mk (phi p N e h c)
      (X ^ e - C ((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h)) = 0 := by
    rw [← phi_eq]; exact AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at h1
  rw [theta_eq_root, h1, AdjoinRoot.algebraMap_eq]
  rfl

/-- `θ^e = c·p` — the Eisenstein relation (`h = 1`). -/
theorem theta_pow_e_one :
    theta p N e 1 c ^ e =
      algebraMap (ZMod (p ^ N)) (Rphi p N e 1 c)
        ((c : ZMod (p ^ N)) * (p : ZMod (p ^ N))) := by
  simpa using theta_pow_e p N e 1 c

/-- **Deliverable 2 (nilpotency, explicit exponent)**: `θ^(N·e) = 0` for any `h ≥ 1`
(`θ^(N·e) = (c·p^h)^N = c^N·p^(h·N) = 0` at level `N`). -/
theorem theta_pow_mul_eq_zero (hN : 0 < N) (hh : 0 < h) :
    theta p N e h c ^ (N * e) = 0 := by
  haveI := neZero_pow_base p N hN
  rw [Nat.mul_comm N e, pow_mul, theta_pow_e, ← map_pow]
  have hz : ((c : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ h) ^ N = 0 := by
    rw [mul_pow, ← pow_mul]
    have hp0 : ((p : ZMod (p ^ N))) ^ (h * N) = 0 := by
      rw [← Nat.cast_pow, CharP.cast_eq_zero_iff (ZMod (p ^ N)) (p ^ N)]
      exact pow_dvd_pow p (Nat.le_mul_of_pos_left N hh)
    rw [hp0, mul_zero]
  rw [hz, map_zero]

theorem isNilpotent_theta (hN : 0 < N) (hh : 0 < h) : IsNilpotent (theta p N e h c) :=
  ⟨N * e, theta_pow_mul_eq_zero p N e h c hN hh⟩

/-- The image of `c` as a unit of `Rphi`. -/
def cUnit : (Rphi p N e h c)ˣ :=
  Units.map (algebraMap (ZMod (p ^ N)) (Rphi p N e h c)).toMonoidHom c

omit hp in
@[simp] theorem cUnit_val :
    (cUnit p N e h c : Rphi p N e h c)
      = algebraMap (ZMod (p ^ N)) (Rphi p N e h c) (c : ZMod (p ^ N)) := rfl

set_option maxHeartbeats 800000 in
/-- `p = c⁻¹·θ^e` in `Rphi` (`h = 1`): `p` is a unit multiple of `θ^e`. -/
theorem natCast_p_eq :
    ((p : ℕ) : Rphi p N e 1 c) = ((cUnit p N e 1 c)⁻¹ : (Rphi p N e 1 c)ˣ)
      * theta p N e 1 c ^ e := by
  have h1 := theta_pow_e_one p N e c
  rw [map_mul, map_natCast, ← cUnit_val p N e 1 c] at h1
  rw [h1, Units.inv_mul_cancel_left]

set_option maxHeartbeats 800000 in
theorem natCast_p_mem_span_theta (he : 0 < e) :
    ((p : ℕ) : Rphi p N e 1 c) ∈ Ideal.span {theta p N e 1 c} := by
  rw [natCast_p_eq p N e c]
  have hθ : theta p N e 1 c ∈ Ideal.span {theta p N e 1 c} :=
    Ideal.subset_span (Set.mem_singleton _)
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hθ e he)

/-- Digit-decomposition of an arbitrary element: `x = n + θ·w` with `n : ℕ`
(the constant-digit representative). Any `h`. -/
theorem exists_natCast_add_theta_mul (hN : 0 < N) (x : Rphi p N e h c) :
    ∃ (n : ℕ) (w : Rphi p N e h c), x = (n : Rphi p N e h c) + theta p N e h c * w := by
  haveI := neZero_pow_base p N hN
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨(g.coeff 0).val, AdjoinRoot.mk (phi p N e h c) g.divX, ?_⟩
  conv_lhs => rw [← X_mul_divX_add g]
  rw [map_add, map_mul, AdjoinRoot.mk_X, ← theta_eq_root]
  have h2 : AdjoinRoot.mk (phi p N e h c) (C (g.coeff 0))
      = (((g.coeff 0).val : ℕ) : Rphi p N e h c) := by
    conv_lhs => rw [← ZMod.natCast_rightInverse (g.coeff 0)]
    rw [map_natCast C, map_natCast]
  rw [h2, add_comm]

/-! ## Deliverable 3: the θ-adic filtration counts (`h = 1`) -/

omit hp in
theorem span_theta_pow_succ_le (j : ℕ) :
    Ideal.span {theta p N e 1 c ^ (j + 1)} ≤ Ideal.span {theta p N e 1 c ^ j} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ j))

omit hp in
theorem span_theta_pow_antitone {i j : ℕ} (hij : i ≤ j) :
    Ideal.span {theta p N e 1 c ^ j} ≤ Ideal.span {theta p N e 1 c ^ i} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hij)

/-- Arithmetic sandwich: a multiplicative chain with unit steps `≤ P`, total `P^K`,
is pinned to exactly `P^j` at every level. -/
private theorem nat_sandwich {P K : ℕ} (hP : 0 < P) (a : ℕ → ℕ) (h0 : a 0 = 1)
    (hK : a K = P ^ K) (hstep : ∀ j, j < K → ∃ k ≤ P, a (j + 1) = a j * k) :
    ∀ j, j ≤ K → a j = P ^ j := by
  have up : ∀ j, j ≤ K → a j ≤ P ^ j := by
    intro j
    induction j with
    | zero => intro _; simp [h0]
    | succ n ih =>
      intro hn1
      obtain ⟨k, hk, hak⟩ := hstep n (by omega)
      calc a (n + 1) = a n * k := hak
        _ ≤ P ^ n * P := Nat.mul_le_mul (ih (by omega)) hk
        _ = P ^ (n + 1) := (pow_succ P n).symm
  have down : ∀ d j, j + d = K → a K ≤ a j * P ^ d := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have hjK : j = K := by omega
      subst hjK
      simp
    | succ n ih =>
      intro j hj
      obtain ⟨k, hk, hak⟩ := hstep j (by omega)
      calc a K ≤ a (j + 1) * P ^ n := ih (j + 1) (by omega)
        _ = a j * k * P ^ n := by rw [hak]
        _ ≤ a j * P * P ^ n :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)
        _ = a j * P ^ (n + 1) := by rw [pow_succ]; ring
  intro j hj
  have hKe : P ^ K = P ^ j * P ^ (K - j) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : P ^ j * P ^ (K - j) ≤ a j * P ^ (K - j) := by
    rw [← hKe, ← hK]
    exact down (K - j) j (by omega)
  exact le_antisymm (up j hj) (Nat.le_of_mul_le_mul_right h1 (pow_pos hP _))

omit hp in
theorem card_quotient_span_theta_pow_zero :
    Nat.card (Rphi p N e 1 c ⧸ Ideal.span {theta p N e 1 c ^ 0}) = 1 := by
  have hsub : Subsingleton (Rphi p N e 1 c ⧸ Ideal.span {theta p N e 1 c ^ 0}) := by
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top
  exact Nat.card_of_subsingleton 0

theorem card_quotient_span_theta_pow_top (hN : 0 < N) (he : 0 < e) :
    Nat.card (Rphi p N e 1 c ⧸ Ideal.span {theta p N e 1 c ^ (N * e)})
      = p ^ (N * e) := by
  have hbot : Ideal.span {theta p N e 1 c ^ (N * e)} = (⊥ : Ideal (Rphi p N e 1 c)) := by
    rw [theta_pow_mul_eq_zero p N e 1 c hN Nat.one_pos]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  rw [hbot,
    Nat.card_congr (Submodule.quotEquivOfEqBot (⊥ : Ideal (Rphi p N e 1 c)) rfl).toEquiv]
  exact card_Rphi p N e 1 c hN he

/-- One filtration step: `|Rphi/(θ^(j+1))| = |Rphi/(θ^j)| · k` with `k ≤ p`. The factor `k`
is the cardinality of the kernel of the connecting map, which is cyclic (generated by the
class of `θ^j`, by the digit decomposition) and `p`-torsion (since `p ∈ (θ^e)`, `e ≥ 1`). -/
theorem card_quotient_span_theta_pow_succ (hN : 0 < N) (he : 0 < e) (j : ℕ) :
    ∃ k ≤ p,
      Nat.card (Rphi p N e 1 c ⧸ Ideal.span {theta p N e 1 c ^ (j + 1)}) =
        Nat.card (Rphi p N e 1 c ⧸ Ideal.span {theta p N e 1 c ^ j}) * k := by
  haveI := finite_Rphi p N e 1 c hN he
  have hIJ : Ideal.span {theta p N e 1 c ^ (j + 1)} ≤ Ideal.span {theta p N e 1 c ^ j} :=
    span_theta_pow_succ_le p N e c j
  set I := Ideal.span {theta p N e 1 c ^ (j + 1)} with hIdef
  set J := Ideal.span {theta p N e 1 c ^ j} with hJdef
  have hsurj : Function.Surjective (Ideal.Quotient.factor hIJ) := fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk I x, Ideal.Quotient.factor_mk hIJ x⟩
  have hlag := Submodule.card_eq_card_quotient_mul_card
    (RingHom.ker (Ideal.Quotient.factor hIJ))
  have hiso : ((Rphi p N e 1 c ⧸ I) ⧸ RingHom.ker (Ideal.Quotient.factor hIJ)) ≃+*
      (Rphi p N e 1 c ⧸ J) :=
    RingHom.quotientKerEquivOfSurjective hsurj
  have hg_mem : Ideal.Quotient.mk I (theta p N e 1 c ^ j)
      ∈ RingHom.ker (Ideal.Quotient.factor hIJ) := by
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, hJdef]
    exact Ideal.subset_span rfl
  have hker0 : Ideal.Quotient.mk I (((p : ℕ) : Rphi p N e 1 c) * theta p N e 1 c ^ j)
      = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, hIdef, Ideal.mem_span_singleton,
      natCast_p_eq p N e c, mul_assoc, ← pow_add]
    exact Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _
  refine ⟨Nat.card (RingHom.ker (Ideal.Quotient.factor hIJ)), ?_, ?_⟩
  · -- the kernel has at most `p` elements: it is the surjective image of `Fin p`
    have hpG : ((p : ℕ) : Rphi p N e 1 c ⧸ I)
        * Ideal.Quotient.mk I (theta p N e 1 c ^ j) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I) p, ← map_mul]
      exact hker0
    have hsur2 : Function.Surjective (fun i : Fin p =>
        (⟨((i : ℕ) : Rphi p N e 1 c ⧸ I) * Ideal.Quotient.mk I (theta p N e 1 c ^ j),
          Ideal.mul_mem_left _ _ hg_mem⟩ :
          RingHom.ker (Ideal.Quotient.factor hIJ))) := by
      rintro ⟨y, hy⟩
      rw [RingHom.mem_ker] at hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, hJdef] at hy
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hy
      obtain ⟨n, w, hw⟩ := exists_natCast_add_theta_mul p N e 1 c hN z
      refine ⟨⟨n % p, Nat.mod_lt _ hp.out.pos⟩, Subtype.ext ?_⟩
      show ((n % p : ℕ) : Rphi p N e 1 c ⧸ I)
          * Ideal.Quotient.mk I (theta p N e 1 c ^ j) = Ideal.Quotient.mk I x
      have hx2 : x = ((n : ℕ) : Rphi p N e 1 c) * theta p N e 1 c ^ j
          + theta p N e 1 c ^ (j + 1) * w := by
        rw [← hz, hw]; ring
      have hth0 : Ideal.Quotient.mk I (theta p N e 1 c ^ (j + 1) * w) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, hIdef]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
      have hnG : ((n : ℕ) : Rphi p N e 1 c ⧸ I)
          * Ideal.Quotient.mk I (theta p N e 1 c ^ j)
          = ((n % p : ℕ) : Rphi p N e 1 c ⧸ I)
          * Ideal.Quotient.mk I (theta p N e 1 c ^ j) := by
        conv_lhs => rw [← Nat.div_add_mod n p]
        push_cast
        rw [add_mul]
        have hres : ((p : ℕ) : Rphi p N e 1 c ⧸ I) * ((n / p : ℕ) : Rphi p N e 1 c ⧸ I)
            * Ideal.Quotient.mk I (theta p N e 1 c ^ j)
            = ((n / p : ℕ) : Rphi p N e 1 c ⧸ I)
            * (((p : ℕ) : Rphi p N e 1 c ⧸ I)
              * Ideal.Quotient.mk I (theta p N e 1 c ^ j)) := by
          ring
        rw [hres, hpG, mul_zero, zero_add]
      rw [hx2, map_add, hth0, add_zero, map_mul, map_natCast]
      exact hnG.symm
    calc Nat.card (RingHom.ker (Ideal.Quotient.factor hIJ))
        ≤ Nat.card (Fin p) := Nat.card_le_card_of_surjective _ hsur2
      _ = p := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  · rw [hlag, Nat.card_congr hiso.toEquiv]
    exact mul_comm _ _

/-- **Deliverable 3a (quotient counts)**: `|Rphi/(θ^j)| = p^j` for `j ≤ N·e`. -/
theorem card_quotient_span_theta_pow (hN : 0 < N) (he : 0 < e) (j : ℕ) (hj : j ≤ N * e) :
    Nat.card (Rphi p N e 1 c ⧸ Ideal.span {theta p N e 1 c ^ j}) = p ^ j :=
  nat_sandwich hp.out.pos
    (fun i => Nat.card (Rphi p N e 1 c ⧸ Ideal.span {theta p N e 1 c ^ i}))
    (card_quotient_span_theta_pow_zero p N e c)
    (card_quotient_span_theta_pow_top p N e c hN he)
    (fun i _ => card_quotient_span_theta_pow_succ p N e c hN he i) j hj

/-- **Deliverable 3b (filtration counts)**: `|(θ^j)| = p^(N·e−j)` for `j ≤ N·e` —
the index law `[Rphi : (θ^j)] = p^j` in its level-N form. -/
theorem card_span_theta_pow (hN : 0 < N) (he : 0 < e) (j : ℕ) (hj : j ≤ N * e) :
    Nat.card (Ideal.span {theta p N e 1 c ^ j}) = p ^ (N * e - j) := by
  haveI := finite_Rphi p N e 1 c hN he
  have hlag := Submodule.card_eq_card_quotient_mul_card
    (Ideal.span {theta p N e 1 c ^ j})
  rw [card_Rphi p N e 1 c hN he, card_quotient_span_theta_pow p N e c hN he j hj] at hlag
  have hsplit : p ^ (N * e) = p ^ (N * e - j) * p ^ j := by
    rw [← pow_add]
    congr 1
    omega
  have hpos : 0 < p ^ j := pow_pos hp.out.pos j
  exact Nat.eq_of_mul_eq_mul_right hpos (hlag.symm.trans hsplit)

/-- **Deliverable 3c (successive quotients)**: `|(θ^j)/(θ^(j+1))| = p` for `j < N·e`,
spelled as the cardinality of the image ideal of `(θ^j)` inside `Rphi/(θ^(j+1))`. -/
theorem card_map_span_theta_pow (hN : 0 < N) (he : 0 < e) (j : ℕ) (hj : j < N * e) :
    Nat.card (Ideal.map (Ideal.Quotient.mk (Ideal.span {theta p N e 1 c ^ (j + 1)}))
      (Ideal.span {theta p N e 1 c ^ j})) = p := by
  haveI := finite_Rphi p N e 1 c hN he
  have hIJ : Ideal.span {theta p N e 1 c ^ (j + 1)} ≤ Ideal.span {theta p N e 1 c ^ j} :=
    span_theta_pow_succ_le p N e c j
  have hlag := Submodule.card_eq_card_quotient_mul_card
    (Ideal.map (Ideal.Quotient.mk (Ideal.span {theta p N e 1 c ^ (j + 1)}))
      (Ideal.span {theta p N e 1 c ^ j}))
  have hq : Nat.card ((Rphi p N e 1 c ⧸ Ideal.span {theta p N e 1 c ^ (j + 1)})
      ⧸ Ideal.map (Ideal.Quotient.mk (Ideal.span {theta p N e 1 c ^ (j + 1)}))
        (Ideal.span {theta p N e 1 c ^ j})) = p ^ j := by
    have hsup : Ideal.span {theta p N e 1 c ^ (j + 1)} ⊔ Ideal.span {theta p N e 1 c ^ j}
        = Ideal.span {theta p N e 1 c ^ j} := sup_eq_right.mpr hIJ
    rw [Nat.card_congr (DoubleQuot.quotQuotEquivQuotSup
      (Ideal.span {theta p N e 1 c ^ (j + 1)})
      (Ideal.span {theta p N e 1 c ^ j})).toEquiv, hsup]
    exact card_quotient_span_theta_pow p N e c hN he j (by omega)
  rw [card_quotient_span_theta_pow p N e c hN he (j + 1) (by omega), hq] at hlag
  have h2 : p ^ (j + 1) = p * p ^ j := by rw [pow_succ, mul_comm]
  have hpos : 0 < p ^ j := pow_pos hp.out.pos j
  exact Nat.eq_of_mul_eq_mul_right hpos (hlag.symm.trans h2)

/-! ## Deliverable 2 (continued): units, localness, residue field (`h = 1`) -/

/-- **Deliverable 2 (residue count)**: `|Rphi/(θ)| = p`. -/
theorem card_quotient_span_theta (hN : 0 < N) (he : 0 < e) :
    Nat.card (Rphi p N e 1 c ⧸ Ideal.span {theta p N e 1 c}) = p := by
  have h1 := card_quotient_span_theta_pow p N e c hN he 1 (Nat.mul_pos hN he)
  simpa using h1

/-- **Deliverable 2 (unit criterion)**: `x` is a unit iff `x ∉ (θ)`. -/
theorem isUnit_iff_notMem (hN : 0 < N) (he : 0 < e) (x : Rphi p N e 1 c) :
    IsUnit x ↔ x ∉ Ideal.span {theta p N e 1 c} := by
  constructor
  · intro hx hmem
    haveI := nontrivial_Rphi p N e 1 c hN he
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
    have hnil : IsNilpotent x := by
      refine ⟨N * e, ?_⟩
      rw [← hy, mul_pow, theta_pow_mul_eq_zero p N e 1 c hN Nat.one_pos, mul_zero]
    exact hx.not_isNilpotent hnil
  · intro hmem
    obtain ⟨n, w, hw⟩ := exists_natCast_add_theta_mul p N e 1 c hN x
    have hpn : ¬ (p ∣ n) := by
      rintro ⟨m, hm⟩
      apply hmem
      rw [hw, hm]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
      push_cast
      exact Ideal.mul_mem_right _ _ (natCast_p_mem_span_theta p N e c he)
    haveI := neZero_pow_base p N hN
    have hun : IsUnit ((n : ℕ) : ZMod (p ^ N)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpn).symm.pow_right N
    have hunR : IsUnit ((n : ℕ) : Rphi p N e 1 c) := by
      have h3 := hun.map (algebraMap (ZMod (p ^ N)) (Rphi p N e 1 c))
      rwa [map_natCast] at h3
    have hnil : IsNilpotent (theta p N e 1 c * w) := by
      refine ⟨N * e, ?_⟩
      rw [mul_pow, theta_pow_mul_eq_zero p N e 1 c hN Nat.one_pos, zero_mul]
    rw [hw]
    exact hnil.isUnit_add_left_of_commute hunR (Commute.all _ _)

/-- **Deliverable 2 (localness)**: `Rphi` is a local ring (`h = 1`). -/
theorem isLocalRing (hN : 0 < N) (he : 0 < e) : IsLocalRing (Rphi p N e 1 c) := by
  haveI := nontrivial_Rphi p N e 1 c hN he
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_notMem p N e c hN he, not_not] at ha hb ⊢
  exact Ideal.add_mem _ ha hb

/-- **Deliverable 2 (maximal ideal)**: the maximal ideal is `(θ)` (`h = 1`).
(`IsLocalRing` is a `Prop`-class, so this holds for any instance — supply it via
`isLocalRing` above.) -/
theorem maximalIdeal_eq [IsLocalRing (Rphi p N e 1 c)] (hN : 0 < N) (he : 0 < e) :
    IsLocalRing.maximalIdeal (Rphi p N e 1 c) = Ideal.span {theta p N e 1 c} := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_notMem p N e c hN he,
    not_not]

/-- **Deliverable 2 (residue field)**: the residue field has exactly `p` elements —
the `δ = f = 1` case of blueprint §5 (the tower-general case is later work). -/
theorem card_residueField [IsLocalRing (Rphi p N e 1 c)] (hN : 0 < N) (he : 0 < e) :
    Nat.card (Rphi p N e 1 c ⧸ IsLocalRing.maximalIdeal (Rphi p N e 1 c)) = p := by
  rw [maximalIdeal_eq p N e c hN he]
  exact card_quotient_span_theta p N e c hN he

/-! ## Deliverable 4: the θ-adic valuation reader `vphi` (`h = 1`) -/

open Classical in
/-- **Deliverable 4**: `vphi x` = the largest `j ≤ N·e` with `x ∈ (θ^j)`
(junk value `N·e` at `x = 0`, consistently: `0` lies in every `(θ^j)`). -/
def vphi (x : Rphi p N e 1 c) : ℕ :=
  Nat.findGreatest (fun j => x ∈ Ideal.span {theta p N e 1 c ^ j}) (N * e)

theorem vphi_le (x : Rphi p N e 1 c) : vphi p N e c x ≤ N * e := by
  classical
  unfold vphi
  exact Nat.findGreatest_le _

theorem mem_span_theta_pow_vphi (x : Rphi p N e 1 c) :
    x ∈ Ideal.span {theta p N e 1 c ^ (vphi p N e c x)} := by
  classical
  unfold vphi
  refine Nat.findGreatest_spec
    (P := fun j => x ∈ Ideal.span {theta p N e 1 c ^ j}) (m := 0) (Nat.zero_le _) ?_
  rw [pow_zero, Ideal.span_singleton_one]
  exact Submodule.mem_top

theorem le_vphi_iff {x : Rphi p N e 1 c} {j : ℕ} (hj : j ≤ N * e) :
    j ≤ vphi p N e c x ↔ x ∈ Ideal.span {theta p N e 1 c ^ j} := by
  classical
  constructor
  · intro hle
    exact span_theta_pow_antitone p N e c hle (mem_span_theta_pow_vphi p N e c x)
  · intro hmem
    unfold vphi
    exact Nat.le_findGreatest hj hmem

theorem vphi_zero : vphi p N e c 0 = N * e :=
  le_antisymm (vphi_le p N e c 0)
    ((le_vphi_iff p N e c le_rfl).mpr (Ideal.zero_mem _))

/-- `vphi (θ^j) = j` for `j ≤ N·e` (strictness of the filtration, via the counts). -/
theorem vphi_theta_pow (hN : 0 < N) (he : 0 < e) {j : ℕ} (hj : j ≤ N * e) :
    vphi p N e c (theta p N e 1 c ^ j) = j := by
  refine le_antisymm ?_ ((le_vphi_iff p N e c hj).mpr (Ideal.subset_span rfl))
  by_contra hcon
  have h1 : j + 1 ≤ vphi p N e c (theta p N e 1 c ^ j) := by omega
  have hj1 : j + 1 ≤ N * e := le_trans h1 (vphi_le p N e c _)
  have hmem : theta p N e 1 c ^ j ∈ Ideal.span {theta p N e 1 c ^ (j + 1)} :=
    span_theta_pow_antitone p N e c h1 (mem_span_theta_pow_vphi p N e c _)
  have heq : Ideal.span {theta p N e 1 c ^ j} = Ideal.span {theta p N e 1 c ^ (j + 1)} :=
    le_antisymm (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem))
      (span_theta_pow_succ_le p N e c j)
  have hc1 := card_span_theta_pow p N e c hN he j hj
  have hc2 := card_span_theta_pow p N e c hN he (j + 1) hj1
  rw [heq, hc2] at hc1
  have := Nat.pow_right_injective hp.out.two_le hc1
  omega

/-- **Deliverable 4 spec**: `vphi θ = 1`. -/
theorem vphi_theta (hN : 0 < N) (he : 0 < e) : vphi p N e c (theta p N e 1 c) = 1 := by
  have h1 : (1 : ℕ) ≤ N * e := Nat.mul_pos hN he
  simpa using vphi_theta_pow p N e c hN he h1

/-- `vphi` is invariant under multiplication by a unit. -/
theorem vphi_unit_mul {u : Rphi p N e 1 c} (hu : IsUnit u) (x : Rphi p N e 1 c) :
    vphi p N e c (u * x) = vphi p N e c x := by
  apply le_antisymm
  · exact (le_vphi_iff p N e c (vphi_le p N e c _)).mpr
      ((Ideal.unit_mul_mem_iff_mem _ hu).mp (mem_span_theta_pow_vphi p N e c (u * x)))
  · exact (le_vphi_iff p N e c (vphi_le p N e c _)).mpr
      (Ideal.mul_mem_left _ _ (mem_span_theta_pow_vphi p N e c x))

/-- **Deliverable 4 spec**: `vphi p = e` (since `p = c⁻¹·θ^e`). -/
theorem vphi_natCast_p (hN : 0 < N) (he : 0 < e) :
    vphi p N e c ((p : ℕ) : Rphi p N e 1 c) = e := by
  rw [natCast_p_eq p N e c, vphi_unit_mul p N e c (Units.isUnit _)]
  exact vphi_theta_pow p N e c hN he (Nat.le_mul_of_pos_left e hN)

/-- **Deliverable 4 spec**: `x` is a unit iff `vphi x = 0`. -/
theorem isUnit_iff_vphi_eq_zero (hN : 0 < N) (he : 0 < e) (x : Rphi p N e 1 c) :
    IsUnit x ↔ vphi p N e c x = 0 := by
  rw [isUnit_iff_notMem p N e c hN he]
  constructor
  · intro hnot
    by_contra h0
    have h1 : 1 ≤ vphi p N e c x := Nat.pos_of_ne_zero h0
    have h2 := span_theta_pow_antitone p N e c h1 (mem_span_theta_pow_vphi p N e c x)
    rw [pow_one] at h2
    exact hnot h2
  · intro h0 hmem
    have h1 : (1 : ℕ) ≤ N * e := Nat.mul_pos hN he
    have h2 := (le_vphi_iff p N e c h1).mpr (by rwa [pow_one])
    omega

/-- **Deliverable 4 spec (submultiplicativity)**: `min (vphi x + vphi y) (N·e) ≤ vphi (x·y)`. -/
theorem min_le_vphi_mul (x y : Rphi p N e 1 c) :
    min (vphi p N e c x + vphi p N e c y) (N * e) ≤ vphi p N e c (x * y) := by
  apply (le_vphi_iff p N e c (min_le_right _ _)).mpr
  apply span_theta_pow_antitone p N e c (min_le_left _ _)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (mem_span_theta_pow_vphi p N e c x)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (mem_span_theta_pow_vphi p N e c y)
  have hxy : x * y = (a * b) * theta p N e 1 c ^ (vphi p N e c x + vphi p N e c y) := by
    conv_lhs => rw [← ha, ← hb]
    rw [pow_add]; ring
  rw [hxy]
  exact Ideal.mem_span_singleton'.mpr ⟨a * b, rfl⟩

end

end LeanUrat.OM.RphiRing

