/-
Kernels/KA6b1 — BP4-c4 E-phase skeleton for unit KA6b1 [NEW id at REV 2 —
the F2/F13 split of the retired KA6b]: the finite-field counting layer (pure
F_q[z], NO table seam) (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.A (1d) +
§4 KA6b1; adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

Four legs, all over an abstract field F (finite where counting demands it):
 · the squarefree-monic COUNT: #{squarefree monics of degree e over F_q} =
   q^e − q^{e−1} for e ≥ 2, and its positivity (q ≥ 2 is automatic for a
   finite field — `Fintype.one_lt_card`);
 · degree-1 monics are separable outright;
 · z·(squarefree cofactor with z ∤ cofactor) is squarefree — the a = 1
   anchored-target mechanism;
 · the COMPILED IMPOSSIBILITY (the F2 fact, stated positively so no prover
   re-attempts the dead route): for a ≥ 2, z^a·c is NEVER squarefree — z²
   divides every such residual REGARDLESS of the cofactor.  At a ≥ 2
   anchored states the squarefree-residual exit mechanism is provably
   ABSENT; the open (state, pool) seam is the sibling unit KA6b2, gated by
   KA6a's anchored-first probe.

Consumers: KA6b2 (the window/table seam — NOT in this cluster).
deps: — (self-contained; pure Mathlib polynomial algebra).

RECORDED RESOLUTIONS (statement transcription):
· "number q^e − q^{e−1}" is stated via `Nat.card` of the subtype of monic
  squarefree degree-e polynomials (no Fintype instance obligation on the
  subtype at statement time).
· "z" is `Polynomial.X`; "coprime to z" is transcribed as ¬ X ∣ c (the
  blueprint's own "z ∤ cofactor" phrasing, §3.A (1d) a = 1).
· "degree e" is `natDegree = e`; positivity of the count is a separate
  corollary rather than a "> 0" annotation on the equality.
· File placement: the §4 KA header assigns KA units to E0Matrix/E0Route;
  KA6b1 is pure polynomial counting with no matrix content, so it takes the
  default <UnitId>.lean per the campaign file-naming rule.

Build: cd lean && lake build LeanUrat.Kernels.KA6b1
-/
import Mathlib

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open Polynomial

/-! ## Leg 1 — the squarefree-monic count (e ≥ 2) -/

/-! ### Prover helpers (private) for the count law.  Route: the classical
squarefree decomposition f = g²·h (g monic, h monic squarefree) — existence
and uniqueness by strong induction on degree with monic-prime extraction —
gives the partition bijection

  Σ_{d ≤ n/2} (monics of deg d) × (squarefree monics of deg n − 2d) ≃
    (monics of deg n),

hence the recursion  q^n = Σ_{d ≤ n/2} q^d · S_{n−2d}  (monics of deg d
number q^d via the `degreeLT`-coefficient equivalence).  Subtracting q times
the level-(e−2) recursion from the level-e one telescopes the whole tail:
S_e = q^e − q^{e−1}.  No new mathematics — the standard zeta-quotient count,
arranged induction-free at the final step. -/

section CountHelpers

variable {F : Type*} [Field F]

/-- Existence half of the squarefree decomposition. -/
private theorem ka6b1_exists_sq_decomp :
    ∀ (n : ℕ) (f : Polynomial F), f.Monic → f.natDegree = n →
      ∃ g h : Polynomial F, g.Monic ∧ h.Monic ∧ Squarefree h ∧ f = g ^ 2 * h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn
    by_cases hsf : Squarefree f
    · exact ⟨1, f, monic_one, hf, hsf, by ring⟩
    · -- extract a monic irreducible whose square divides f
      unfold Squarefree at hsf
      push_neg at hsf
      obtain ⟨x, hxx, hxu⟩ := hsf
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hf.ne_zero (by simpa using hxx)
      obtain ⟨π₀, hπ₀irr, hπ₀dvd⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx0
      haveI := Classical.decEq F
      have hπmon : (normalize π₀).Monic := Polynomial.monic_normalize hπ₀irr.ne_zero
      have hπirr : Irreducible (normalize π₀) :=
        (associated_normalize π₀).irreducible hπ₀irr
      have hπdvd : normalize π₀ ∣ x := (normalize_dvd_iff).mpr hπ₀dvd
      have hππ : (normalize π₀) ^ 2 ∣ f := by
        rw [sq]
        exact dvd_trans (mul_dvd_mul hπdvd hπdvd) hxx
      obtain ⟨f', hf'⟩ := hππ
      have hf'mon : f'.Monic := (hπmon.pow 2).of_mul_monic_left (hf' ▸ hf)
      have hdeg' : f'.natDegree < n := by
        have hne : ((normalize π₀) ^ 2) ≠ 0 := (hπmon.pow 2).ne_zero
        have h := Polynomial.natDegree_mul hne hf'mon.ne_zero
        rw [← hf', hn, Polynomial.natDegree_pow] at h
        have := hπirr.natDegree_pos
        omega
      obtain ⟨g', h, hg', hh, hsfh, hfh⟩ := ih f'.natDegree hdeg' f' hf'mon rfl
      exact ⟨normalize π₀ * g', h, hπmon.mul hg', hh, hsfh, by rw [hf', hfh]; ring⟩

/-- Uniqueness half of the squarefree decomposition (monic components). -/
private theorem ka6b1_sq_decomp_unique :
    ∀ (n : ℕ) (g₁ g₂ h₁ h₂ : Polynomial F), g₁.Monic → g₂.Monic → h₁.Monic →
      h₂.Monic → Squarefree h₁ → Squarefree h₂ → g₁ ^ 2 * h₁ = g₂ ^ 2 * h₂ →
      g₁.natDegree = n → g₁ = g₂ ∧ h₁ = h₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g₁ g₂ h₁ h₂ hg₁ hg₂ hh₁ hh₂ hs₁ hs₂ heq hn
    by_cases hdeg : g₁.natDegree = 0
    · have hg1 : g₁ = 1 := (Polynomial.Monic.natDegree_eq_zero hg₁).mp hdeg
      subst hg1
      rw [one_pow, one_mul] at heq
      have hg2 : g₂ = 1 := by
        have hdvd : g₂ * g₂ ∣ h₁ := by
          rw [heq, ← sq]
          exact dvd_mul_right _ _
        exact Polynomial.Monic.eq_one_of_isUnit hg₂ (hs₁ g₂ hdvd)
      subst hg2
      rw [one_pow, one_mul] at heq
      exact ⟨rfl, heq⟩
    · -- extract a monic irreducible factor π of g₁; it must divide g₂,
      -- else π² lands in the squarefree h₂.
      obtain ⟨π₀, hπ₀irr, hπ₀dvd⟩ := WfDvdMonoid.exists_irreducible_factor
        (Polynomial.not_isUnit_of_natDegree_pos _ (Nat.pos_of_ne_zero hdeg))
        hg₁.ne_zero
      haveI := Classical.decEq F
      have hπmon : (normalize π₀).Monic := Polynomial.monic_normalize hπ₀irr.ne_zero
      have hπirr : Irreducible (normalize π₀) :=
        (associated_normalize π₀).irreducible hπ₀irr
      have hπg₁ : normalize π₀ ∣ g₁ := (normalize_dvd_iff).mpr hπ₀dvd
      have hπg₂ : normalize π₀ ∣ g₂ := by
        by_contra hnd
        have hrel2 : IsRelPrime ((normalize π₀) ^ 2) (g₂ ^ 2) :=
          (hπirr.isRelPrime_iff_not_dvd.mpr hnd).pow
        have hd : (normalize π₀) ^ 2 ∣ g₂ ^ 2 * h₂ := by
          rw [← heq]
          exact (pow_dvd_pow_of_dvd hπg₁ 2).mul_right h₁
        have hππ : normalize π₀ * normalize π₀ ∣ h₂ := by
          rw [← sq]
          exact hrel2.dvd_of_dvd_mul_left hd
        exact hπirr.not_isUnit (hs₂ _ hππ)
      obtain ⟨g₁', hg₁'⟩ := hπg₁
      obtain ⟨g₂', hg₂'⟩ := hπg₂
      have hg₁'mon : g₁'.Monic := hπmon.of_mul_monic_left (hg₁' ▸ hg₁)
      have hg₂'mon : g₂'.Monic := hπmon.of_mul_monic_left (hg₂' ▸ hg₂)
      have hπne : normalize π₀ ≠ 0 := hπmon.ne_zero
      have heq' : g₁' ^ 2 * h₁ = g₂' ^ 2 * h₂ := by
        have h2 : (normalize π₀) ^ 2 * (g₁' ^ 2 * h₁)
            = (normalize π₀) ^ 2 * (g₂' ^ 2 * h₂) := by
          calc (normalize π₀) ^ 2 * (g₁' ^ 2 * h₁)
              = (normalize π₀ * g₁') ^ 2 * h₁ := by ring
            _ = (normalize π₀ * g₂') ^ 2 * h₂ := by rw [← hg₁', ← hg₂']; exact heq
            _ = (normalize π₀) ^ 2 * (g₂' ^ 2 * h₂) := by ring
        exact mul_left_cancel₀ (pow_ne_zero 2 hπne) h2
      have hdeg' : g₁'.natDegree < n := by
        have h := Polynomial.natDegree_mul hπne hg₁'mon.ne_zero
        rw [← hg₁', hn] at h
        have := hπirr.natDegree_pos
        omega
      obtain ⟨he1, he2⟩ := ih g₁'.natDegree hdeg' g₁' g₂' h₁ h₂ hg₁'mon hg₂'mon
        hh₁ hh₂ hs₁ hs₂ heq' rfl
      exact ⟨by rw [hg₁', hg₂', he1], he2⟩

variable (F)

/-- Monics of degree d ≃ polynomials of degree < d (subtract/add X^d). -/
private noncomputable def ka6b1_monicEquiv (d : ℕ) :
    {f : Polynomial F // f.Monic ∧ f.natDegree = d} ≃ Polynomial.degreeLT F d where
  toFun f := ⟨f.1 - Polynomial.X ^ d, by
    rw [Polynomial.mem_degreeLT]
    have hd : f.1.degree = (Polynomial.X ^ d : Polynomial F).degree := by
      rw [Polynomial.degree_eq_natDegree f.2.1.ne_zero, f.2.2, Polynomial.degree_X_pow]
    have hlt := Polynomial.degree_sub_lt hd f.2.1.ne_zero
      (by rw [f.2.1.leadingCoeff, (Polynomial.monic_X_pow d).leadingCoeff])
    rw [Polynomial.degree_eq_natDegree f.2.1.ne_zero, f.2.2] at hlt
    exact hlt⟩
  invFun g := ⟨g.1 + Polynomial.X ^ d, by
    have hglt : g.1.degree < (Polynomial.X ^ d : Polynomial F).degree := by
      rw [Polynomial.degree_X_pow]
      exact Polynomial.mem_degreeLT.mp g.2
    constructor
    · have h := (Polynomial.monic_X_pow (R := F) d).add_of_left hglt
      rwa [add_comm] at h
    · have hdeg : (g.1 + Polynomial.X ^ d).degree
          = (Polynomial.X ^ d : Polynomial F).degree := by
        rw [add_comm]
        exact Polynomial.degree_add_eq_left_of_degree_lt hglt
      rw [Polynomial.degree_X_pow] at hdeg
      exact Polynomial.natDegree_eq_of_degree_eq_some hdeg⟩
  left_inv f := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)

private instance [Fintype F] (d : ℕ) :
    Finite {f : Polynomial F // f.Monic ∧ f.natDegree = d} :=
  Finite.of_equiv _
    ((ka6b1_monicEquiv F d).trans (Polynomial.degreeLTEquiv F d).toEquiv).symm

private instance [Fintype F] (m : ℕ) :
    Finite {f : Polynomial F // f.Monic ∧ f.natDegree = m ∧ Squarefree f} :=
  Finite.of_injective
    (fun f => (⟨f.1, f.2.1, f.2.2.1⟩ : {f : Polynomial F // f.Monic ∧ f.natDegree = m}))
    (fun a b hab => by
      apply Subtype.ext
      have h := congrArg Subtype.val hab
      simpa using h)

/-- Monics of degree d number q^d. -/
private theorem ka6b1_card_monic [Fintype F] (d : ℕ) :
    Nat.card {f : Polynomial F // f.Monic ∧ f.natDegree = d}
      = Fintype.card F ^ d := by
  rw [Nat.card_congr
    ((ka6b1_monicEquiv F d).trans (Polynomial.degreeLTEquiv F d).toEquiv)]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

/-- The partition recursion  q^n = Σ_{d ≤ n/2} q^d · S_{n−2d}. -/
private theorem ka6b1_monic_recursion [Fintype F] (n : ℕ) :
    Fintype.card F ^ n =
      ∑ d ∈ Finset.range (n / 2 + 1),
        Fintype.card F ^ d *
          Nat.card {h : Polynomial F //
            h.Monic ∧ h.natDegree = n - 2 * d ∧ Squarefree h} := by
  classical
  -- the decomposition map onto monics of degree n
  let Φ : (Σ d : Fin (n / 2 + 1),
      {g : Polynomial F // g.Monic ∧ g.natDegree = (d : ℕ)} ×
      {h : Polynomial F // h.Monic ∧ h.natDegree = n - 2 * (d : ℕ) ∧ Squarefree h}) →
      {f : Polynomial F // f.Monic ∧ f.natDegree = n} := fun x =>
    ⟨x.2.1.1 ^ 2 * x.2.2.1, (x.2.1.2.1.pow 2).mul x.2.2.2.1, by
      have hlt : (x.1 : ℕ) < n / 2 + 1 := x.1.isLt
      rw [Polynomial.natDegree_mul (pow_ne_zero 2 x.2.1.2.1.ne_zero)
        x.2.2.2.1.ne_zero, Polynomial.natDegree_pow, x.2.1.2.2, x.2.2.2.2.1]
      omega⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨d₁, hd₁⟩, ⟨g₁, hg₁⟩, ⟨h₁, hh₁⟩⟩ ⟨⟨d₂, hd₂⟩, ⟨g₂, hg₂⟩, ⟨h₂, hh₂⟩⟩ hxy
    simp only [Φ, Subtype.mk.injEq] at hxy
    obtain ⟨hg, hh⟩ := ka6b1_sq_decomp_unique g₁.natDegree g₁ g₂ h₁ h₂
      hg₁.1 hg₂.1 hh₁.1 hh₂.1 hh₁.2.2 hh₂.2.2 hxy rfl
    have hd : d₁ = d₂ := by
      have h1 : g₁.natDegree = d₁ := hg₁.2
      have h2 : g₂.natDegree = d₂ := hg₂.2
      rw [← h1, ← h2, hg]
    subst hd
    subst hg
    subst hh
    rfl
  have hsurj : Function.Surjective Φ := by
    rintro ⟨f, hfm, hfd⟩
    obtain ⟨g, h, hgm, hhm, hs, hf⟩ :=
      ka6b1_exists_sq_decomp f.natDegree f hfm rfl
    have hdeg : 2 * g.natDegree + h.natDegree = n := by
      have h1 := Polynomial.natDegree_mul (pow_ne_zero 2 hgm.ne_zero) hhm.ne_zero
      rw [← hf, Polynomial.natDegree_pow, hfd] at h1
      omega
    refine ⟨⟨⟨g.natDegree, by omega⟩, ⟨g, hgm, rfl⟩, ⟨h, hhm, ?_, hs⟩⟩,
      Subtype.ext hf.symm⟩
    show h.natDegree = n - 2 * g.natDegree
    omega
  calc Fintype.card F ^ n
      = Nat.card {f : Polynomial F // f.Monic ∧ f.natDegree = n} :=
        (ka6b1_card_monic F n).symm
    _ = Nat.card (Σ d : Fin (n / 2 + 1),
          {g : Polynomial F // g.Monic ∧ g.natDegree = (d : ℕ)} ×
          {h : Polynomial F //
            h.Monic ∧ h.natDegree = n - 2 * (d : ℕ) ∧ Squarefree h}) :=
        (Nat.card_eq_of_bijective Φ ⟨hinj, hsurj⟩).symm
    _ = ∑ d : Fin (n / 2 + 1),
          Nat.card ({g : Polynomial F // g.Monic ∧ g.natDegree = (d : ℕ)} ×
            {h : Polynomial F //
              h.Monic ∧ h.natDegree = n - 2 * (d : ℕ) ∧ Squarefree h}) :=
        Nat.card_sigma
    _ = ∑ d ∈ Finset.range (n / 2 + 1),
          Fintype.card F ^ d *
            Nat.card {h : Polynomial F //
              h.Monic ∧ h.natDegree = n - 2 * d ∧ Squarefree h} := by
        rw [Fin.sum_univ_eq_sum_range (fun d =>
          Nat.card ({g : Polynomial F // g.Monic ∧ g.natDegree = d} ×
            {h : Polynomial F //
              h.Monic ∧ h.natDegree = n - 2 * d ∧ Squarefree h}))]
        exact Finset.sum_congr rfl (fun d _ => by
          rw [Nat.card_prod, ka6b1_card_monic])

end CountHelpers

/-- KA6b1 (count law): squarefree monics of degree e over a finite field F
number q^e − q^{e−1}, for e ≥ 2 (q := Fintype.card F).  deps: —.  Sketch:
the classical zeta-function/Möbius count — every monic f factors uniquely as
g²·h with h squarefree ... at degree e ≥ 2 the count telescopes to
q^e − q^{e−1}; alternatively port the generating-function identity
Σ (#squarefree monics of deg e)·t^e = (1 − qt²)/(1 − qt).  hard leg of the
unit (known mathematics, no new content). -/
theorem ka6b1_card_squarefree_monic (F : Type*) [Field F] [Fintype F]
    (e : ℕ) (he : 2 ≤ e) :
    Nat.card {f : Polynomial F // f.Monic ∧ f.natDegree = e ∧ Squarefree f} =
      Fintype.card F ^ e - Fintype.card F ^ (e - 1) := by
  classical
  -- level-e recursion, d = 0 term split off
  have R1 := ka6b1_monic_recursion F e
  rw [Finset.sum_range_succ'] at R1
  simp only [Nat.mul_zero, Nat.sub_zero, pow_zero, one_mul] at R1
  -- q·(level-(e−2) recursion) IS the remaining tail
  have hqR2 : Fintype.card F ^ (e - 1) =
      ∑ d ∈ Finset.range (e / 2),
        Fintype.card F ^ (d + 1) *
          Nat.card {h : Polynomial F //
            h.Monic ∧ h.natDegree = e - 2 * (d + 1) ∧ Squarefree h} := by
    have h1 : Fintype.card F ^ (e - 1) =
        Fintype.card F * Fintype.card F ^ (e - 2) := by
      have h2 : e - 1 = (e - 2) + 1 := by omega
      rw [h2, pow_succ]
      ring
    rw [h1, ka6b1_monic_recursion F (e - 2), Finset.mul_sum]
    have hrange : (e - 2) / 2 + 1 = e / 2 := by omega
    rw [← hrange]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have hidx : e - 2 - 2 * d = e - 2 * (d + 1) := by omega
    rw [hidx]
    ring
  rw [← hqR2] at R1
  omega

/-- KA6b1 (positivity — the "> 0" of the blueprint display): the
squarefree-monic count at degree e ≥ 2 is positive; q ≥ 2 is automatic
(`Fintype.one_lt_card` for a finite field).  deps: the count law (or a direct
witness, e.g. a product of e distinct monic linears when q ≥ e, X^e − z
adjustments otherwise — the count route is the intended one).  Consumed by
KA6b2 as "some free-digit choice makes the residual squarefree" at a = 0. -/
theorem ka6b1_card_squarefree_monic_pos (F : Type*) [Field F] [Fintype F]
    (e : ℕ) (he : 2 ≤ e) :
    0 < Nat.card {f : Polynomial F // f.Monic ∧ f.natDegree = e ∧ Squarefree f} := by
  rw [ka6b1_card_squarefree_monic F e he]
  have h2 : 1 < Fintype.card F := Fintype.one_lt_card
  have hlt : Fintype.card F ^ (e - 1) < Fintype.card F ^ e :=
    Nat.pow_lt_pow_right h2 (by omega)
  omega

/-! ## Leg 2 — degree-1 residuals are separable outright -/

/-- KA6b1 (degree-1 leg): every degree-1 monic over a field is separable
(hence squarefree — `Polynomial.Separable.squarefree` closes the consumer
form).  deps: —.  Sketch: f monic of natDegree 1 has derivative 1;
IsCoprime f 1.  (Monicity is not strictly needed over a field but is the
shape the residual reads deliver — kept per the blueprint text "degree-1
monics separable".) -/
theorem ka6b1_degree_one_separable {F : Type*} [Field F]
    (f : Polynomial F) (hm : f.Monic) (hf : f.natDegree = 1) :
    f.Separable := by
  rw [hm.eq_X_add_C hf]
  exact Polynomial.separable_X_add_C _

/-! ## Leg 3 — the a = 1 anchored mechanism -/

/-- KA6b1 (a = 1 leg): z·(squarefree cofactor with z ∤ cofactor) is
squarefree.  deps: —.  Sketch: X is prime in F[z]; a product of coprime
squarefree factors is squarefree (X ∤ c gives IsCoprime X c over the PID/
Bézout field-polynomial ring; then `Squarefree.mul` along coprimality, X
itself squarefree as a prime). -/
theorem ka6b1_X_mul_squarefree {F : Type*} [Field F]
    {c : Polynomial F} (hc : Squarefree c) (hz : ¬ (X : Polynomial F) ∣ c) :
    Squarefree ((X : Polynomial F) * c) := by
  rw [squarefree_mul_iff]
  exact ⟨(Polynomial.irreducible_X.isRelPrime_iff_not_dvd).mpr hz,
    Polynomial.irreducible_X.squarefree, hc⟩

/-! ## Leg 4 — the compiled impossibility at a ≥ 2 (the F2 fact) -/

/-- KA6b1 (a ≥ 2 leg, COMPILED IMPOSSIBILITY — stated positively so no
prover re-attempts the dead route): for a ≥ 2 no polynomial of the form
z^a·c is squarefree, REGARDLESS of the cofactor c (including c = 0: the zero
polynomial is not squarefree).  deps: —.  Sketch: X·X = X² ∣ X^a ∣ X^a·c and
X is not a unit; c = 0 is `not_squarefree_zero`.  This is the §3.A (1d)
a ≥ 2 verdict: the squarefree-residual exit mechanism is ABSENT at deep
anchors — KA6b2 must route those states through the cofactor criterion or
the class-level escape (KA2c). -/
theorem ka6b1_anchor_not_squarefree {F : Type*} [Field F]
    (a : ℕ) (ha : 2 ≤ a) (c : Polynomial F) :
    ¬ Squarefree ((X : Polynomial F) ^ a * c) := by
  intro hsq
  have hdvd : (X : Polynomial F) * X ∣ (X : Polynomial F) ^ a * c := by
    have h2 : (X : Polynomial F) ^ 2 ∣ (X : Polynomial F) ^ a * c :=
      (pow_dvd_pow X ha).mul_right c
    simpa [sq] using h2
  exact Polynomial.not_isUnit_X (hsq X hdvd)

end LeanUrat.Kernels
