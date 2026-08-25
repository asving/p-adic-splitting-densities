/-
DEC2 elaboration check — af′ REVERSE plan (`docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md`).

Part 1 pins every LANDED input the plan consumes, at the exact type the plan claims for it
(an `example` that fails to elaborate = a wrong claim in the plan).
Part 2 elaborates every PLANNED new signature as a `Prop`-valued `def` (statement
elaboration only — no proof, no `sorry`, no axiom).

Run: `cd leanfinal && lake env lean scratch/DEC2_check.lean` — must exit 0.
-/
import Uniformity.ChapC.C131ae
import Uniformity.ChapC.C131w
import Uniformity.ChapC.C130rp2
import Uniformity.ChapC.C26
import Uniformity.ChapC.C35

set_option linter.unusedVariables false

namespace DEC2Check

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 1 — landed inputs, pinned at the plan's claimed types -/

/-! ### 1.1 The two definitional bridges the whole plan stands on -/

/-- BRIDGE 1: the level-two height IS the level-one cleared support at `(u₂, e₂)` — by `rfl`.
So C131w's `dv2Hgt` kit and the C.51 locus's `dvSupp`/`IsDvPure` data are the same carrier. -/
example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (A : Polynomial O) :
    dv2Hgt (T.levelDatum hπ) A = dvSupp F A T.u₂ T.e₂ := rfl

/-- BRIDGE 2: `dvHgt` is `stageHeight` of the flat digit — by `rfl` (C.06). -/
example (f : Polynomial O) (i : ℕ) : dvHgt F f i = F.stageHeight (dev F.key f i) := rfl

/-- BRIDGE 3: `dv2Pin` is `dv2Hgt` of the composed digit — by `rfl` (C.11); so AF-4 is
literally C.54(c)'s node-floor carrier, strict form. -/
example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (f : Polynomial O) (j : ℕ) :
    dv2Pin (T.levelDatum hπ) (composedKey T) f j
      = dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) := rfl

/-- BRIDGE 4: `wtCoeff`'s offset is `slotOffset` — same ℕ expression (C.50 / C.131a′). -/
example (T : TowerDatum F H₀ hpin) (c : O) (a b : ℕ) :
    C131a.wtCoeff T c a b
      = (F.e₁ * T.e₂) • addVal O c + ((slotOffset T a b : ℕ) : ℕ∞) := rfl

/-- BRIDGE 5: `budgetFloor`'s body, with the `let`s spelled out (the AF-5 target shape). -/
example (T : TowerDatum F H₀ hpin) (μ₂ j a b : ℕ) :
    budgetFloor T μ₂ j a b
      = (if (μ₂ - j) * T.E₂ < slotOffset T a b then 0
         else ((μ₂ - j) * T.E₂ - slotOffset T a b + F.e₁ * T.e₂ - 1) / (F.e₁ * T.e₂)
           + (if ((μ₂ - j) * T.E₂ - slotOffset T a b) % (F.e₁ * T.e₂) == 0 then 1
              else 0)) := rfl

/-! ### 1.2 The locus, destructured (C.51), and its residual clause instantiable at any pin -/

example (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} {f : Polynomial O}
    (hf : f ∈ towerLocus T μ₂) :
    f.Monic ∧ f.natDegree = μ₂ * T.D₂ ∧ IsDvPure F f T.u₂ T.e₂ :=
  ⟨hf.1, hf.2.1, hf.2.2.1⟩

example (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} {f : Polynomial O}
    (hf : f ∈ towerLocus T μ₂)
    (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty) (M₀ : ℕ)
    (hp : dvHgt F f (dvSideMin F f T.u₂ T.e₂ hne) = (M₀ : ℕ∞)) :
    dvResPoly F H₀ hpin f T.u₂ T.e₂ hne M₀ hp = (towerLabel T) ^ μ₂ :=
  hf.2.2.2 hne M₀ hp

/-- `IsDvPure` gives both endpoint memberships (C.29). -/
example {g : Polynomial O} {u ℓ : ℕ} (h : IsDvPure F g u ℓ) :
    0 ∈ dvSideSet F g u ℓ ∧ g.natDegree / (F.e₁ * F.f₁) ∈ dvSideSet F g u ℓ := h

/-! ### 1.3 The reference object and the exact-half entry point (C.131ac′; carries the cite) -/

example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {μ₂ : ℕ} (hμ₂ : 0 < μ₂) :
    composedKey T ^ μ₂ ∈ towerLocus T μ₂ :=
  composedKey_pow_mem_towerLocus T hπ hh hμ₂

#check @Uniformity.Density.Tower.exists_dvHgt_pin

/-! ### 1.4 The landed reverse ledgers (C.131w′) at their claimed shapes -/

example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (A B : Polynomial O) :
    min (dv2Hgt (T.levelDatum hπ) A) (dv2Hgt (T.levelDatum hπ) B)
      ≤ dv2Hgt (T.levelDatum hπ) (A + B) :=
  C131w.dv2Hgt_add_min T hπ A B

example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (A : Polynomial O) :
    dv2Hgt (T.levelDatum hπ) (-A) = dv2Hgt (T.levelDatum hπ) A :=
  C131w.dv2Hgt_neg T hπ A

/-- The honest-digit ledger, at the exact instantiation AF-4 uses
(`n := A.natDegree`, `w := μ₂E₂ + 1`). -/
example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) {μ₂ : ℕ} (A : Polynomial O)
    (hw : ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) A) (j : ℕ) :
    ((μ₂ * T.E₂ + 1 - j * T.E₂ : ℕ) : ℕ∞)
      ≤ dv2Hgt (T.levelDatum hπ) (dev (composedKey T) A j) :=
  C131w.dv2Hgt_dev_floor T hπ A.natDegree A le_rfl hw j

/-! ### 1.5 The flattening chain (C.131t′ + C.131a′ + C.131k′) -/

example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (A : Polynomial O) :
    dv2Hgt (T.levelDatum hπ) A = C131a.WT T (C131k.xNF F A) :=
  C131t.dv2Hgt_eq_WT_phiNF T hπ A

example (T : TowerDatum F H₀ hpin) (P : Polynomial (Polynomial O)) (a b : ℕ) :
    C131a.WT T P ≤ C131a.wtCoeff T ((P.coeff b).coeff a) a b :=
  C131a.WT_le_wtCoeff T P a b

/-- The two-key digit IS the `xNF` coefficient (C.131k′): the flattening lands exactly on the
budget clause's scalar. -/
example (A : Polynomial O) (b : ℕ) :
    (C131k.xNF F A).coeff b = dev F.key A b := by
  rw [C131k.xNF_coeff, C131k.xDigit_eq_dev]

/-! ### 1.6 The read laws (C.130rp2, GENERIC section) and C.26's residual teeth -/

example (hπ : Irreducible π) {A B : Polynomial O} {k : ℕ}
    (hA : (k : ℕ∞) ≤ F.stageHeight A) (hB : (k : ℕ∞) ≤ F.stageHeight B) :
    F.twistRead H₀ hpin k (A + B) = F.twistRead H₀ hpin k A + F.twistRead H₀ hpin k B :=
  C130rp2.twistRead_add_of_le F hπ H₀ hpin hA hB

example (hπ : Irreducible π) {A : Polynomial O} {k : ℕ}
    (hk : (k : ℕ∞) < F.stageHeight A) : F.twistRead H₀ hpin k A = 0 :=
  C130rp2.twistRead_eq_zero_of_lt F hπ H₀ hpin hk

/-- C.26 (ii)/(iii): nonzero constant term of ANY nonempty-side residual — the strictness
engine, applied to `g := f − Φ₂^{μ₂}` in AF-3. -/
example (hπ : Irreducible π) {g : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hne : (dvSideSet F g u ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F g (dvSideMin F g u ℓ hne) = (M₀ : ℕ∞)) :
    (dvResPoly F H₀ hpin g u ℓ hne M₀ hp).coeff 0 ≠ 0 :=
  (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).2

/-- C.26 (ii): residual degree = side degree — with the locus pin this yields
`dvSideDeg f = μ₂f₂` for free (AF-1). -/
example (hπ : Irreducible π) {f : Polynomial O} {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hne : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞)) :
    (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).natDegree = dvSideDeg F f u ℓ hne :=
  (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1

/-- The residual-coefficient extraction glue AF-3 re-derives locally (C.26's `hcoeff`
pattern, from the public `Uniformity.Hensel.coeff_sum_range_C_mul_X_pow`) — proved here in
full as the pre-check that the two-liner works outside C26.lean. -/
example (hπ : Irreducible π) {f : Polynomial O} {u ℓ : ℕ}
    (hne : (dvSideSet F f u ℓ).Nonempty) {M₀ : ℕ}
    (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞)) {t : ℕ}
    (ht : t ≤ dvSideDeg F f u ℓ hne) :
    (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).coeff t
      = F.twistRead H₀ hpin (M₀ - u * t)
          (dev F.key f (dvSideMin F f u ℓ hne + ℓ * t)) := by
  rw [dvResPoly, Uniformity.Hensel.coeff_sum_range_C_mul_X_pow,
    if_pos (Nat.lt_succ_of_le ht), Nat.mul_comm t u, Nat.mul_comm t ℓ]

/-! ### 1.7 Side-set membership/attainment vocabulary (C.35, C.07, mathlib) -/

example {u ℓ j : ℕ} {f : Polynomial O} (h : j ∈ dvSideSet F f u ℓ) :
    DvOnSide F f u ℓ j := (dvOnSide_of_mem_dvSideSet h)

example {u ℓ j : ℕ} {f : Polynomial O} (h : DvOnSide F f u ℓ j) :
    dvSupp F f u ℓ = ℓ • dvHgt F f j + (u * j : ℕ∞) ∧ dvHgt F f j ≠ ⊤ := h

/-- `Finset.inf` attainment (AF-2's engine). -/
example {α : Type} (s : Finset α) (h : s.Nonempty) (f : α → ℕ∞) :
    ∃ i ∈ s, s.inf f = f i := Finset.exists_mem_eq_inf s h f

/-- `dvSupp` is below each of its terms (in range). -/
example {u ℓ : ℕ} (f : Polynomial O) {i : ℕ} (hi : i ∈ Finset.range (f.natDegree + 1)) :
    dvSupp F f u ℓ ≤ ℓ • dvHgt F f i + (u * i : ℕ∞) := Finset.inf_le hi

/-- ℕ∞ strict-to-`+1` conversion (AF-3's closing step). -/
example {m : ℕ} {x : ℕ∞} (h : (m : ℕ∞) < x) : ((m + 1 : ℕ) : ℕ∞) ≤ x := by
  exact_mod_cast Order.add_one_le_of_lt h

/-! ### 1.8 Digit bookkeeping (C.131v′, C.52, C.131ae′, B.32a) -/

example {φ : Polynomial O} (hφ : φ.Monic) (A B : Polynomial O) (j : ℕ) :
    dev φ (A - B) j = dev φ A j - dev φ B j := C131v.dev_sub hφ A B j

example {φ : Polynomial O} (hφ : φ.Monic) (a b : Polynomial O) (j : ℕ) :
    dev φ (a + b) j = dev φ a j + dev φ b j := dev_add_of_monic hφ a b j

example {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree) (μ j : ℕ) :
    dev φ (φ ^ μ) j = if j = μ then 1 else 0 := dev_pow_self hφ hd μ j

/-- Monic top digit is `1` (C.131v′) — the exactness half of the entry computation. -/
example {n : ℕ} (A : Polynomial O) (hA : A.Monic)
    (hdeg : A.natDegree = n * F.key.natDegree) :
    dev F.key A n = 1 :=
  C131v.dev_top_eq_one F.hmonic F.natDegree_key_pos n A hA hdeg

example : F.stageHeight (1 : Polynomial O) = 0 := C131ae.stageHeight_one F

-- Degree drop of the perturbation (C.131ae′'s own step, reused verbatim in AF-3).
#check @Uniformity.Hensel.degree_sub_lt_of_monic_of_natDegree_eq

/-! ### 1.9 Tower-datum arithmetic fields the plan consumes -/

example (T : TowerDatum F H₀ hpin) : Nat.Coprime T.u₂ T.e₂ := T.hcop
example (T : TowerDatum F H₀ hpin) : 0 < T.e₂ := T.he₂
example (T : TowerDatum F H₀ hpin) : 0 < T.f₂ := T.hf₂
example (T : TowerDatum F H₀ hpin) : T.E₂ = T.e₂ * T.f₂ * T.u₂ := rfl
example (T : TowerDatum F H₀ hpin) : 1 ≤ T.margin := T.one_le_margin
example (T : TowerDatum F H₀ hpin) (μ₂ j : ℕ) :
    T.theta μ₂ j = (μ₂ - j) * T.E₂ + T.margin := rfl
example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (towerLabel T).natDegree = T.f₂ := (towerLabel_spec T hπ).2.2.1

/-- The C.131ae′ node itself — the direction af′ is assembled WITH (binder shape frozen). -/
example (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂)
    (hbud : ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j a b : ℕ∞)
        ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a)) :
    f ∈ towerLocus T μ₂ :=
  mem_towerLocus_of_budget T hπ hh hμ₂ hf hdeg hbud

/-! ## Part 2 — the PLANNED signatures (elaboration only; the nodes prove them) -/

/-- AF-1a (`towerLocus_dvSupp_eq`): a locus member's cleared support is EXACTLY `μ₂E₂`. -/
def SIG_AF1a : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} {f : Polynomial O},
    f ∈ towerLocus T μ₂ →
    dvSupp F f T.u₂ T.e₂ = ((μ₂ * T.E₂ : ℕ) : ℕ∞)

/-- AF-1b (`dvSideMin_eq_zero_of_isDvPure`): pure polynomials have left endpoint `0`. -/
def SIG_AF1b : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {g : Polynomial O} {u ℓ : ℕ},
    IsDvPure F g u ℓ → ∀ (hne : (dvSideSet F g u ℓ).Nonempty),
    dvSideMin F g u ℓ hne = 0

/-- AF-1c (`towerLocus_dvHgt_zero_pin`): the locus left-endpoint height numeral. -/
def SIG_AF1c : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} {f : Polynomial O},
    f ∈ towerLocus T μ₂ →
    dvHgt F f 0 = ((μ₂ * T.f₂ * T.u₂ : ℕ) : ℕ∞)

/-- AF-1d (`towerLocus_dvSideDeg`): the locus side degree, via C.26(ii) + the residual pin
+ `towerLabel_spec` (no endpoint bookkeeping needed). -/
def SIG_AF1d : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin), Irreducible π → ∀ {μ₂ : ℕ} {f : Polynomial O},
    f ∈ towerLocus T μ₂ → ∀ (hne : (dvSideSet F f T.u₂ T.e₂).Nonempty),
    dvSideDeg F f T.u₂ T.e₂ hne = μ₂ * T.f₂

/-- AF-2a (`dvSideSet_nonempty_of_dvSupp_eq_coe`): a finite cleared support is attained. -/
def SIG_AF2a : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {g : Polynomial O} {u ℓ : ℕ}, 0 < ℓ →
    ∀ {W : ℕ}, dvSupp F g u ℓ = (W : ℕ∞) → (dvSideSet F g u ℓ).Nonempty

/-- AF-2b (`towerLattice_solve`): the on-line left endpoint of a support-`μ₂E₂` polynomial
sits on the `e₂`-lattice, with its height numeral solved. -/
def SIG_AF2b : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ : ℕ} {g : Polynomial O},
    dvSupp F g T.u₂ T.e₂ = ((μ₂ * T.E₂ : ℕ) : ℕ∞) →
    ∀ (hne : (dvSideSet F g T.u₂ T.e₂).Nonempty),
    ∃ t₀ ≤ μ₂ * T.f₂,
      dvSideMin F g T.u₂ T.e₂ hne = T.e₂ * t₀ ∧
      dvHgt F g (dvSideMin F g T.u₂ T.e₂ hne)
        = ((μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂ : ℕ) : ℕ∞)

/-- AF-3a (`towerLocus_read_eq`): any two members of the same locus have EQUAL ϖ-reads at
every lattice point of the shared side — both read the coefficients of `towerLabel T ^ μ₂`.
(Instantiated in AF-3 at `f` and `composedKey T ^ μ₂`.) -/
def SIG_AF3a : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin), Irreducible π →
    ∀ {μ₂ : ℕ} {f f' : Polynomial O},
    f ∈ towerLocus T μ₂ → f' ∈ towerLocus T μ₂ → ∀ {t₀ : ℕ}, t₀ ≤ μ₂ * T.f₂ →
    F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂) (dev F.key f (T.e₂ * t₀))
      = F.twistRead H₀ hpin (μ₂ * T.f₂ * T.u₂ - t₀ * T.u₂) (dev F.key f' (T.e₂ * t₀))

/-- AF-3 (`dvSupp_sub_composedKey_pow`, THE HEART): the perturbation `f − Φ₂^{μ₂}` of a locus
member clears `μ₂E₂ + 1` STRICTLY — the reverse correspondence's entire triangular content,
absorbed by the C.131ac′ reference + C.26's teeth. Carries the cite (via C.131ac′). -/
def SIG_AF3 : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin), Irreducible π → 1 ≤ F.h →
    ∀ [Finite (ResidueField O)] {μ₂ : ℕ}, 0 < μ₂ →
    ∀ {f : Polynomial O}, f ∈ towerLocus T μ₂ →
    ((μ₂ * T.E₂ + 1 : ℕ) : ℕ∞) ≤ dvSupp F (f - composedKey T ^ μ₂) T.u₂ T.e₂

/-- AF-4 (`towerLocus_dev_strict_floor`): the strict per-digit floor — C.54(c)'s node floor
(`dv2Pin ≥ (μ₂−j)E₂ + 1`) obtained from AF-3 through C.131w′'s honest-digit ledger. -/
def SIG_AF4 : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π), 1 ≤ F.h →
    ∀ [Finite (ResidueField O)] {μ₂ : ℕ}, 0 < μ₂ →
    ∀ {f : Polynomial O}, f ∈ towerLocus T μ₂ → ∀ {j : ℕ}, j < μ₂ →
    (((μ₂ - j) * T.E₂ + 1 : ℕ) : ℕ∞)
      ≤ dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j)

/-- AF-5a (`budgetFloor_le_of_succ_le`, pure ℕ): the ceiling arithmetic, in `budgetFloor`'s
own spelling.  `X := (μ₂−j)E₂`, `w := slotOffset`, `d := e₁e₂`. -/
def SIG_AF5a : Prop :=
  ∀ {d v w X : ℕ}, 0 < d → X + 1 ≤ d * v + w →
    (if X < w then 0
     else (X - w + d - 1) / d + (if (X - w) % d == 0 then 1 else 0)) ≤ v

/-- AF-5b (`budgetFloor_le_addVal_of_wtCoeff`, the ℕ∞ wrapper). -/
def SIG_AF5b : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) {μ₂ j a b : ℕ} {c : O},
    (((μ₂ - j) * T.E₂ + 1 : ℕ) : ℕ∞) ≤ C131a.wtCoeff T c a b →
    (budgetFloor T μ₂ j a b : ℕ∞) ≤ addVal O c

/-- AF-6a (★ `budget_of_mem_towerLocus`, NODE C.131af′ / C.52 Step 3 / `EFF.GENTOW1.22`):
locus membership implies every budget floor — the reverse of C.131ae′. -/
def SIG_AF6a : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π), 1 ≤ F.h →
    ∀ [Finite (ResidueField O)] {μ₂ : ℕ}, 0 < μ₂ →
    ∀ {f : Polynomial O}, f ∈ towerLocus T μ₂ →
    ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j a b : ℕ∞)
        ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a)

/-- AF-6b (★ `towerLocus_iff_budget`, NODE C.52 assembly / `EFF.GENTOW1.15`): the signed
iff, byte-mirroring the leanspec NODE C.52 axiom twin. -/
def SIG_AF6b : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (ResidueField O)]
    {μ₂ : ℕ} (hμ₂ : 0 < μ₂) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = μ₂ * T.D₂),
    f ∈ towerLocus T μ₂
      ↔ ∀ j a b : ℕ, j < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
          (budgetFloor T μ₂ j a b : ℕ∞)
            ≤ addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a)

/-- AF-7c (`towerLocus_band_window_empty`, general form of the honest finding): at a
margin-`1` tower the C.72 faithful-band hypothesis is unsatisfiable on the locus —
a direct corollary of AF-4. -/
def SIG_AF7c : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π), 1 ≤ F.h → T.margin = 1 →
    ∀ [Finite (ResidueField O)] {μ₂ : ℕ}, 0 < μ₂ →
    ∀ {f : Polynomial O}, f ∈ towerLocus T μ₂ → ∀ {j : ℕ}, j < μ₂ → ∀ {m : ℕ},
    dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j) = (m : ℕ∞) →
    ¬ m < T.theta μ₂ j

end DEC2Check
