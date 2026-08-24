/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C72
import Uniformity.ChapC.C131n
import Uniformity.ChapC.C131t
import Uniformity.ChapC.C131v
import Uniformity.ChapC.C131ad

/-!
# Uniformity.ChapC.C131w — C.72 `shadow_floor`

**Chapter C, NODE C.131w′ — C.72 `shadow_floor`, the dv-graded engine's headline theorem**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §3.8 (`Cnv14`) and §5, row C.131w′).

The signed statement (leanspec `ChapC.lean`, NODE C.72; the statement carrier is C.72's
`ShadowFloorStatement`): for `f` in the tower-entry locus and `j < μ₂`,

```lean
(T.theta μ₂ j : ℕ∞)
  ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j)
```

— every `dv₂`-height at which the stage-shadow read and the composed (honest) read carry
different slot digits clears the faithfulness threshold `Θ_j = (μ₂ − j)E₂ + δ`.

## The splice, and the two strong-induction ledgers it runs on

C.131v′'s `shadow_discrepancy` rewrites the difference to `- dev (composedKey T)
(censusOverflow T f) j`, so the theorem is a floor on the honest `Φ₂`-redevelopment of the
paid census value.  Three floors chain:

1. **The overflow entry floor** (`dv2Hgt_censusOverflow_floor`): `dv2Hgt (censusOverflow T f)
   ≥ μ₂E₂ + δ`.  The locus prices `f`'s entry (`towerLocus_entry_floor`: the `IsDvPure`
   right endpoint gives `dv2Hgt f ≥ μ₂E₂` — v2 §2's "the FULL-SIDE hypothesis, consumed
   exactly once, through `μ₁u₂ = μ₂E₂`"); C.131n′'s ledger `quotDigit_floor_of_le` carries
   `(μ₂ − j′)E₂` to the two-variable digit `S_{j′}` at every census coordinate; the paid
   part of the census at `S_{j′}` is priced with the extra `δ` by the **inner paid ledger**
   `dev_coeff_paid_floor` (this file): the `m`-th `Φ′`-digit of a coefficientwise-floored
   inner polynomial gains exactly `m·δ` of outer weight — F11's `paid ≥ 1 ⟹ +δ` invariant,
   proved by strong induction on the inner degree, peeling the top monomial through the
   x-carry `x^{D′+k} = (x^{D′} − Φ′)x^k + Φ′·x^k` (tail branch priced by C.131d′–e′'s
   `xCarry_tail_floor`, paid branch by the exact `wtCoeff_paid_shift`, i.e. `u₂ = e₂D′h + δ`).
   The paid census value is reassembled through `collapse_unpaid_add_paid` +
   `collapse_unpaidValue` (C.131v′) — no tagged-list bookkeeping is repeated here.
2. **The honest-digit ledger** (`dv2Hgt_dev_floor`, this file): `dv2Hgt A ≥ w ⟹
   dv2Hgt (dev Φ₂ A i) ≥ w − i·E₂`.  This is F6–F8 at the honest key: strong induction on
   `natDegree A`, peeling the top block `g·Φ′^M` of the canonical normal form against
   `Φ′^{M−q}·Φ₂` — the outer carry `Y^q = (Y^q − K_T) + K_T`, its tail priced at `E₂` by
   C.131g′'s `K_T_monomial_floor`, its paid branch moving one honest `Φ₂`-coordinate up
   (C.131n′'s `recarry_moves_up_one`) at the exact cost `E₂` (`wtCoeff_outer_key_shift`).
   Every weight floor descends to the canonical digits through C.131ad′'s value-blind
   carry-down `dev_coeff_floor` (`le_dv2Hgt_of_eval`), and heights convert through
   C.131t′'s `dv2Hgt_eq_WT_phiNF` (Cnv11).
3. **The threshold arithmetic**: `(μ₂E₂ + δ) − jE₂ = (μ₂ − j)E₂ + δ = Θ_j` for `j ≤ μ₂`
   (C.71's `theta`; the same cancellation as C.131n′'s `recarry_cancel`).

`dv2Hgt` is invariant under negation (`dv2Hgt_neg`, via `xNF_neg` + C.131h′'s `WT_neg`),
which absorbs `shadow_discrepancy`'s sign.

**Honest supersession note.**  C.131o′'s parameterized `census_floor` (F11 over an abstract
tagged list with a `PaidFloor` hypothesis) is not consumed: the missing glue it left open —
pricing the honest `Φ₂`-REDEVELOPMENT of the erased paid value, where x-overflow recarries
across coordinates — is exactly what the two strong-induction ledgers above prove, and they
subsume the list-level floor for this node's purpose.  The mathematical content (entry
ledger + `paid ≥ 1 ⟹ +δ` + upward recarry priced by F9/F10) is v2 §3.8's, unchanged.

## Statement discipline

`shadow_floor` below carries the leanspec NODE C.72 binder list byte-for-byte (including the
unconsumed `hh : 1 ≤ F.h` and `[Finite (ResidueField O)]` — the statement is frozen; the
x-free stratum in `C72.lean` keeps them too).  `shadow_floor_statement` ties the landing to
C.72's signed statement carrier `ShadowFloorStatement`.  No cite is consumed: the axiom
footprint of every declaration below is Lean-core only.

## Status

Sorry-free, axiom-free (Lean core only; AxCheck footer).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131w

open Polynomial IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131a Uniformity.Density.Tower.C131f
open Uniformity.Density.Tower.C131h Uniformity.Density.Tower.C131k
open Uniformity.Density.Tower.C131n Uniformity.Density.Tower.C131p
open Uniformity.Density.Tower.C131t Uniformity.Density.Tower.C131v
open Uniformity.Density.Tower.C131ad

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
variable {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}

/-! ## Part 0 — weight/normal-form glue -/

/-- A uniform floor on every two-index scalar coefficient is a floor on the weight. -/
theorem le_WT_of_forall_wtCoeff (T : TowerDatum F H₀ hpin)
    {P : Polynomial (Polynomial O)} {w : ℕ∞}
    (h : ∀ a b, w ≤ wtCoeff T ((P.coeff b).coeff a) a b) : w ≤ WT T P := by
  unfold WT
  exact Finset.le_inf fun b _ => Finset.le_inf fun a _ => h a b

/-- The weight of a single outer block is the inner support infimum at that outer index. -/
theorem WT_C_mul_X_pow_eq (T : TowerDatum F H₀ hpin) (g : Polynomial O) (b : ℕ) :
    WT T (Polynomial.C g * Polynomial.X ^ b)
      = g.support.inf (fun a => wtCoeff T (g.coeff a) a b) := by
  by_cases hg : g = 0
  · subst hg
    simp [WT]
  · unfold WT
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.support_monomial b hg,
      Finset.inf_singleton, Polynomial.coeff_monomial, if_pos rfl]

/-- The canonical x-normal form is additive (C.131t′'s inline fact, exported). -/
theorem xNF_add (F : KeyFrame O π) (A B : Polynomial O) :
    xNF F (A + B) = xNF F A + xNF F B := by
  apply Polynomial.ext
  intro b
  rw [Polynomial.coeff_add, xNF_coeff, xNF_coeff, xNF_coeff]
  simp only [xDigit_eq_dev]
  exact dev_add_of_monic F.hmonic A B b

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- B.02's development of `0` vanishes (public form; B.04's `dev_zero` is private). -/
theorem dev_zero' (φ : Polynomial O) (j : ℕ) : dev φ (0 : Polynomial O) j = 0 := by
  rw [← devQ_eq_dev]
  exact devQ_of_zero φ j

/-- B.02's development commutes with negation. -/
theorem dev_neg {φ : Polynomial O} (hφ : φ.Monic) (A : Polynomial O) (j : ℕ) :
    dev φ (-A) j = -(dev φ A j) := by
  have h := dev_sub hφ 0 A j
  rw [zero_sub, dev_zero', zero_sub] at h
  exact h

/-- The canonical x-normal form commutes with negation. -/
theorem xNF_neg (F : KeyFrame O π) (A : Polynomial O) : xNF F (-A) = -(xNF F A) := by
  apply Polynomial.ext
  intro b
  rw [Polynomial.coeff_neg, xNF_coeff, xNF_coeff]
  simp only [xDigit_eq_dev]
  exact dev_neg F.hmonic A b

/-- The level-two height is ultrametric (through Cnv11 and `WT_add`). -/
theorem dv2Hgt_add_min (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (A B : Polynomial O) :
    min (dv2Hgt (T.levelDatum hπ) A) (dv2Hgt (T.levelDatum hπ) B)
      ≤ dv2Hgt (T.levelDatum hπ) (A + B) := by
  rw [dv2Hgt_eq_WT_phiNF T hπ, dv2Hgt_eq_WT_phiNF T hπ, dv2Hgt_eq_WT_phiNF T hπ, xNF_add]
  exact WT_add T _ _

/-- The level-two height is invariant under negation. -/
theorem dv2Hgt_neg (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (A : Polynomial O) :
    dv2Hgt (T.levelDatum hπ) (-A) = dv2Hgt (T.levelDatum hπ) A := by
  rw [dv2Hgt_eq_WT_phiNF T hπ, dv2Hgt_eq_WT_phiNF T hπ, xNF_neg, WT_neg]

/-- **The lift-to-height conversion**: any two-variable lift's weight floor is a level-two
height floor on its evaluation (C.131ad′'s carry-down composed with Cnv11). -/
theorem le_dv2Hgt_of_eval (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    (Q : Polynomial (Polynomial O)) {w : ℕ∞} (hw : w ≤ WT T Q) :
    w ≤ dv2Hgt (T.levelDatum hπ) (Polynomial.eval F.key Q) := by
  rw [dv2Hgt_eq_WT_phiNF T hπ]
  refine le_WT_of_forall_wtCoeff T fun a b => ?_
  rw [xNF_coeff, xDigit_eq_dev]
  exact dev_coeff_floor T Q hw b a

private theorem coe_sub_le_of_le_add {w c : ℕ} {x : ℕ∞}
    (h : (w : ℕ∞) ≤ x + (c : ℕ∞)) : ((w - c : ℕ) : ℕ∞) ≤ x := by
  induction x using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
      have hm : w ≤ m + c := by exact_mod_cast h
      exact_mod_cast (show w - c ≤ m by omega)

/-- C.131f′'s reduced two-variable image of the composed key IS the canonical x-normal
form of the composed key. -/
theorem K_T_eq_xNF (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    K_T T = xNF F (composedKey T) := by
  apply Polynomial.ext
  intro b
  rw [xNF_coeff, xDigit_eq_dev]
  by_cases hb : b ≤ T.e₂ * T.f₂
  · exact coeff_K_T T hb
  · rw [not_le] at hb
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_K_T]; omega)]
    refine (dev_eq_zero_of_lt F.hmonic F.natDegree_key_pos (composedKey T) b ?_).symm
    rw [composedKey_natDegree_mul T hπ]
    exact mul_lt_mul_of_pos_right hb F.natDegree_key_pos

/-! ## Part 1 — the inner paid ledger (F11's `+δ` invariant, structural form)

`dev_coeff_paid_floor`: if every scalar coefficient of an inner polynomial `g` clears `w`
at outer index `b`, then every scalar coefficient of its `m`-th `Φ′`-digit clears
`w + m·δ` at outer index `m + b`.  Strong induction on `natDegree g`, peeling the top
monomial through the x-carry: the tail branch is priced by C.131d′–e′'s
`xCarry_tail_floor`, the paid `Φ′`-branch gains exactly `δ` (`wtCoeff_paid_shift`,
i.e. `u₂ = e₂·D′h + δ`) and moves one digit up (C.131n′'s `recarry_moves_up_one`). -/

/-- The exact price of one paid x-carry: trading `D′` inner degrees for one outer degree
gains exactly the margin `δ` (`u₂ = e₂D′h + δ`, C.42's node floor made an equation). -/
theorem wtCoeff_paid_shift (T : TowerDatum F H₀ hpin) (c : O) (k b : ℕ) :
    wtCoeff T c k (b + 1)
      = wtCoeff T c (F.e₁ * F.f₁ + k) b + (T.margin : ℕ∞) := by
  have hle : T.e₂ * ((F.e₁ * F.f₁) * F.h) ≤ T.u₂ :=
    Nat.le_of_lt (by simpa [Nat.mul_assoc] using T.hfloor)
  have hm : T.e₂ * ((F.e₁ * F.f₁) * F.h) + T.margin = T.u₂ := by
    simpa only [TowerDatum.margin] using Nat.add_sub_of_le hle
  have hnat : k * (T.e₂ * F.h) + (b + 1) * T.u₂
      = ((F.e₁ * F.f₁ + k) * (T.e₂ * F.h) + b * T.u₂) + T.margin := by
    rw [← hm]; ring
  unfold wtCoeff
  rw [hnat]
  push_cast
  ring

private theorem paid_floor_small (T : TowerDatum F H₀ hpin) {g : Polynomial O}
    (hg : g.natDegree < F.key.natDegree) {w : ℕ∞} {b : ℕ}
    (hfl : ∀ a, w ≤ wtCoeff T (g.coeff a) a b) (m a : ℕ) :
    w + ((m * T.margin : ℕ) : ℕ∞) ≤ wtCoeff T ((dev F.key g m).coeff a) a (m + b) := by
  have hdeg : g.degree < F.key.degree := degree_lt_degree hg
  cases m with
  | zero =>
      have h0 : dev F.key g 0 = g := by
        show g %ₘ F.key = g
        exact (modByMonic_eq_self_iff F.hmonic).2 hdeg
      rw [h0]
      simpa using hfl a
  | succ m =>
      have h1 : dev F.key g (m + 1) = 0 := by
        show dev F.key (g /ₘ F.key) m = 0
        rw [(divByMonic_eq_zero_iff F.hmonic).2 hdeg]
        exact dev_zero' F.key m
      rw [h1, Polynomial.coeff_zero, wtCoeff_zero]
      exact le_top

/-- **The inner paid ledger.**  A coefficientwise floor `w` at outer index `b` descends to
the `m`-th canonical `Φ′`-digit with the exact paid gain `m·δ`, at outer index `m + b`. -/
theorem dev_coeff_paid_floor (T : TowerDatum F H₀ hpin) :
    ∀ (n : ℕ) (g : Polynomial O), g.natDegree ≤ n →
      ∀ {w : ℕ∞} {b : ℕ}, (∀ a, w ≤ wtCoeff T (g.coeff a) a b) →
      ∀ (m a : ℕ),
        w + ((m * T.margin : ℕ) : ℕ∞) ≤ wtCoeff T ((dev F.key g m).coeff a) a (m + b) := by
  have hkeyD : F.key.natDegree = F.e₁ * F.f₁ := F.hdeg
  have hDpos : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  intro n
  induction n with
  | zero =>
      intro g hg w b hfl m a
      exact paid_floor_small T (by omega) hfl m a
  | succ n ih =>
      intro g hgn w b hfl m a
      by_cases hsmall : g.natDegree < F.key.natDegree
      · exact paid_floor_small T hsmall hfl m a
      rw [not_lt] at hsmall
      rw [hkeyD] at hsmall
      set c := g.coeff g.natDegree with hc
      set k := g.natDegree - F.e₁ * F.f₁ with hk
      have hdk : g.natDegree = F.e₁ * F.f₁ + k := by omega
      -- the three-way split of the top monomial through one x-carry
      have hsplit : g = (g - Polynomial.C c * Polynomial.X ^ (F.e₁ * F.f₁ + k))
          + (Polynomial.C c * ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ k)
             + F.key * (Polynomial.C c * Polynomial.X ^ k)) := by
        rw [pow_add]; ring
      -- degree bounds for the three parts
      have hglowdeg : (g - Polynomial.C c * Polynomial.X ^ (F.e₁ * F.f₁ + k)).natDegree ≤ n := by
        have hle : (g - Polynomial.C c * Polynomial.X ^ (F.e₁ * F.f₁ + k)).natDegree
            ≤ g.natDegree - 1 := by
          refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
          have hNge : g.natDegree ≤ N := by omega
          rw [Polynomial.coeff_sub, Polynomial.C_mul_X_pow_eq_monomial,
            Polynomial.coeff_monomial]
          rcases eq_or_lt_of_le hNge with hEq | hLt
          · rw [← hEq, if_pos hdk.symm, ← hc, sub_self]
          · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hLt, if_neg (by omega), sub_zero]
        omega
      have htaildeg : (Polynomial.C c *
          ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ k)).natDegree ≤ n := by
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_X_pow]
        have := natDegree_X_pow_sub_key_le F
        omega
      have hpaydeg : (Polynomial.C c * Polynomial.X ^ k).natDegree ≤ n := by
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X_pow]
        omega
      -- coefficientwise floors for the three parts
      have hcg : g.coeff (F.e₁ * F.f₁ + k) = c := by rw [← hdk]
      have hbase' : w ≤ wtCoeff T c (F.e₁ * F.f₁ + k) b := by
        have h := hfl (F.e₁ * F.f₁ + k)
        rwa [hcg] at h
      have hflglow : ∀ a',
          w ≤ wtCoeff T ((g - Polynomial.C c * Polynomial.X ^ (F.e₁ * F.f₁ + k)).coeff a')
            a' b := by
        intro a'
        rw [Polynomial.coeff_sub, Polynomial.C_mul_X_pow_eq_monomial,
          Polynomial.coeff_monomial]
        by_cases ha' : F.e₁ * F.f₁ + k = a'
        · rw [if_pos ha', ← ha', hcg, sub_self, wtCoeff_zero]
          exact le_top
        · rw [if_neg ha', sub_zero]
          exact hfl a'
      have hfltail : ∀ a', w ≤ wtCoeff T ((Polynomial.C c *
          ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ k)).coeff a') a' b := by
        intro a'
        rw [Polynomial.coeff_C_mul]
        have hmulw := wtCoeff_mul T c
          (((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ k).coeff a') 0 a' 0 b
        rw [zero_add, zero_add] at hmulw
        rw [hmulw]
        have hproj := le_trans (xCarry_tail_floor T k b)
          (WT_le_wtCoeff T (Polynomial.C ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key)
            * Polynomial.X ^ k) * Polynomial.X ^ b) a' b)
        have hcb : ((Polynomial.C ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key)
            * Polynomial.X ^ k) * Polynomial.X ^ b).coeff b)
            = (Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ k := by
          rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial, if_pos rfl]
        rw [hcb] at hproj
        refine le_trans hbase' ?_
        refine le_trans (le_of_eq (wtCoeff_add_shift T c k b)) ?_
        exact add_le_add le_rfl hproj
      have hflpay : ∀ a', w + (T.margin : ℕ∞)
          ≤ wtCoeff T ((Polynomial.C c * Polynomial.X ^ k).coeff a') a' (b + 1) := by
        intro a'
        rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
        by_cases hka : k = a'
        · rw [if_pos hka, ← hka, wtCoeff_paid_shift T c k b]
          exact add_le_add hbase' le_rfl
        · rw [if_neg hka, wtCoeff_zero]
          exact le_top
      -- the three digit floors
      have h1 := ih _ hglowdeg hflglow m a
      have h2 := ih _ htaildeg hfltail m a
      have h3 : w + ((m * T.margin : ℕ) : ℕ∞)
          ≤ wtCoeff T ((dev F.key (F.key * (Polynomial.C c * Polynomial.X ^ k)) m).coeff a)
            a (m + b) := by
        cases m with
        | zero =>
            have h0 : dev F.key (F.key * (Polynomial.C c * Polynomial.X ^ k)) 0 = 0 := by
              rw [← devQ_eq_dev]
              exact recarry_step_zero F.hmonic _
            rw [h0, Polynomial.coeff_zero, wtCoeff_zero]
            exact le_top
        | succ m' =>
            have hstep : dev F.key (F.key * (Polynomial.C c * Polynomial.X ^ k)) (m' + 1)
                = dev F.key (Polynomial.C c * Polynomial.X ^ k) m' := by
              rw [← devQ_eq_dev, ← devQ_eq_dev]
              exact recarry_moves_up_one F.hmonic _ m'
            rw [hstep]
            have hihp := ih _ hpaydeg hflpay m' a
            have hidx : m' + (b + 1) = m' + 1 + b := by omega
            rw [hidx] at hihp
            refine le_trans (le_of_eq ?_) hihp
            push_cast
            ring
      -- combine through the additive development
      have hdev3 : dev F.key g m
          = dev F.key (g - Polynomial.C c * Polynomial.X ^ (F.e₁ * F.f₁ + k)) m
            + (dev F.key (Polynomial.C c *
                ((Polynomial.X ^ (F.e₁ * F.f₁) - F.key) * Polynomial.X ^ k)) m
              + dev F.key (F.key * (Polynomial.C c * Polynomial.X ^ k)) m) := by
        conv_lhs => rw [hsplit]
        rw [dev_add_of_monic F.hmonic, dev_add_of_monic F.hmonic]
      rw [hdev3, Polynomial.coeff_add, Polynomial.coeff_add]
      exact le_trans (le_min h1 (le_trans (le_min h2 h3)
          (min_wtCoeff_le_wtCoeff_add T _ _ a (m + b))))
        (min_wtCoeff_le_wtCoeff_add T _ _ a (m + b))

/-! ## Part 2 — the honest-digit ledger (F6–F8 at the honest key) -/

private theorem dev2_floor_small (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    {A : Polynomial O} (hA : A.natDegree < (composedKey T).natDegree) {w : ℕ}
    (hw : (w : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) A) (i : ℕ) :
    ((w - i * T.E₂ : ℕ) : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) (dev (composedKey T) A i) := by
  have hdeg : A.degree < (composedKey T).degree := degree_lt_degree hA
  cases i with
  | zero =>
      have h0 : dev (composedKey T) A 0 = A := by
        show A %ₘ composedKey T = A
        exact (modByMonic_eq_self_iff (composedKey_monic T)).2 hdeg
      rw [h0]
      exact le_trans (by exact_mod_cast Nat.sub_le w _) hw
  | succ i =>
      have h1 : dev (composedKey T) A (i + 1) = 0 := by
        show dev (composedKey T) (A /ₘ composedKey T) i = 0
        rw [(divByMonic_eq_zero_iff (composedKey_monic T)).2 hdeg]
        exact dev_zero' _ i
      rw [h1, dv2Hgt_zero]
      exact le_top

/-- **The honest-digit ledger.**  A level-two height floor descends to every honest
`Φ₂`-development digit at the homogeneous cost `E₂` per coordinate:
`dv2Hgt A ≥ w ⟹ dv2Hgt (dev Φ₂ A i) ≥ w − i·E₂`.  Strong induction on `natDegree A`,
peeling the top block of the canonical normal form against `Φ′^{M−q}·Φ₂`. -/
theorem dv2Hgt_dev_floor (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    ∀ (n : ℕ) (A : Polynomial O), A.natDegree ≤ n →
      ∀ {w : ℕ}, (w : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) A →
      ∀ i : ℕ, ((w - i * T.E₂ : ℕ) : ℕ∞)
        ≤ dv2Hgt (T.levelDatum hπ) (dev (composedKey T) A i) := by
  have hD : 0 < F.key.natDegree := F.natDegree_key_pos
  have hq2 : 2 ≤ T.e₂ * T.f₂ := T.hcomp
  have hΦdeg : (composedKey T).natDegree = (T.e₂ * T.f₂) * F.key.natDegree :=
    composedKey_natDegree_mul T hπ
  intro n
  induction n with
  | zero =>
      intro A hA w hw i
      refine dev2_floor_small T hπ ?_ hw i
      have : 0 < (T.e₂ * T.f₂) * F.key.natDegree := Nat.mul_pos (by omega) hD
      omega
  | succ n ih =>
      intro A hAn w hw i
      by_cases hAsmall : A.natDegree < (composedKey T).natDegree
      · exact dev2_floor_small T hπ hAsmall hw i
      rw [not_lt] at hAsmall
      rw [hΦdeg] at hAsmall
      have hqDpos : 0 < (T.e₂ * T.f₂) * F.key.natDegree := Nat.mul_pos (by omega) hD
      have hAne : A ≠ 0 := fun h0 => by
        rw [h0, Polynomial.natDegree_zero] at hAsmall; omega
      have hxne : xNF F A ≠ 0 := fun h0 =>
        hAne (by rw [← xNF_eval F A, h0, Polynomial.eval_zero])
      set M : ℕ := (xNF F A).natDegree with hMdef
      set g : Polynomial O := dev F.key A M with hgdef
      have hgcoeff : (xNF F A).coeff M = g := by rw [xNF_coeff, xDigit_eq_dev]
      have hgne : g ≠ 0 := by
        intro h0
        refine hxne (Polynomial.leadingCoeff_eq_zero.mp ?_)
        rw [Polynomial.leadingCoeff, ← hMdef, hgcoeff]
        exact h0
      have hgdeg : g.natDegree ≤ F.key.natDegree - 1 := by
        have hlt : g.degree < F.key.degree := by
          rw [← hgcoeff]
          exact xNF_coeff_degree_lt F A M
        have := Polynomial.natDegree_lt_natDegree hgne hlt
        omega
      -- the degree bookkeeping of the canonical top block
      have hdevdeg : ∀ b, (dev F.key A b).natDegree ≤ F.key.natDegree - 1 := by
        intro b
        by_cases h0 : dev F.key A b = 0
        · rw [h0, Polynomial.natDegree_zero]; omega
        · have hlt : (dev F.key A b).degree < F.key.degree := by
            rw [← xDigit_eq_dev, ← xNF_coeff]
            exact xNF_coeff_degree_lt F A b
          have := Polynomial.natDegree_lt_natDegree h0 hlt
          omega
      have hMle : M ≤ A.natDegree := by
        rw [hMdef, xNF]
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
        calc (Polynomial.C (xDigit F.key A b) * Polynomial.X ^ b).natDegree
            ≤ (Polynomial.C (xDigit F.key A b)).natDegree
              + ((Polynomial.X : Polynomial (Polynomial O)) ^ b).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ b := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
          _ ≤ A.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hArec : A = ∑ b ∈ Finset.range (M + 1), dev F.key A b * F.key ^ b := by
        have hbound : A.natDegree < (A.natDegree + 1) * F.key.natDegree := by
          calc A.natDegree < A.natDegree + 1 := Nat.lt_succ_self _
            _ = (A.natDegree + 1) * 1 := (Nat.mul_one _).symm
            _ ≤ (A.natDegree + 1) * F.key.natDegree := Nat.mul_le_mul_left _ hD
        have h1 : ∑ b ∈ Finset.range (A.natDegree + 1), dev F.key A b * F.key ^ b = A :=
          sum_dev_eq F.hmonic hD A hbound
        conv_lhs => rw [← h1]
        symm
        refine Finset.sum_subset ?_ ?_
        · intro x hx
          rw [Finset.mem_range] at hx ⊢
          omega
        · intro b hb hbn
          have hMb : M < b := by
            simp only [Finset.mem_range] at hb hbn
            omega
          have hz : dev F.key A b = 0 := by
            rw [← xDigit_eq_dev, ← xNF_coeff]
            exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [← hMdef]; exact hMb)
          rw [hz, zero_mul]
      have hAdegle : A.natDegree ≤ M * F.key.natDegree + (F.key.natDegree - 1) := by
        conv_lhs => rw [hArec]
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
        have hbM : b ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
        calc (dev F.key A b * F.key ^ b).natDegree
            ≤ (dev F.key A b).natDegree + (F.key ^ b).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ (F.key.natDegree - 1) + b * F.key.natDegree := by
              have h1 := hdevdeg b
              have h2 : (F.key ^ b).natDegree ≤ b * F.key.natDegree :=
                Polynomial.natDegree_pow_le
              omega
          _ ≤ M * F.key.natDegree + (F.key.natDegree - 1) := by
              have := Nat.mul_le_mul_right F.key.natDegree hbM
              omega
      have hMq : T.e₂ * T.f₂ ≤ M := by
        have h1 : (T.e₂ * T.f₂) * F.key.natDegree ≤ A.natDegree := hAsmall
        have h2 : A.natDegree < (M + 1) * F.key.natDegree := by
          rw [Nat.succ_mul]
          omega
        have h3 : (T.e₂ * T.f₂) * F.key.natDegree < (M + 1) * F.key.natDegree :=
          lt_of_le_of_lt h1 h2
        exact Nat.lt_succ_iff.mp (lt_of_mul_lt_mul_right h3 (Nat.zero_le _))
      have hM1 : 1 ≤ M := le_trans (by omega) hMq
      set low : Polynomial O := ∑ b ∈ Finset.range M, dev F.key A b * F.key ^ b with hlowdef
      have hAsplit : A = low + g * F.key ^ M := by
        rw [hlowdef, hgdef]
        conv_lhs => rw [hArec]
        exact Finset.sum_range_succ _ M
      have hlowdeg : low.natDegree ≤ M * F.key.natDegree - 1 := by
        rw [hlowdef]
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
        have hbM : b < M := Finset.mem_range.mp hb
        calc (dev F.key A b * F.key ^ b).natDegree
            ≤ (dev F.key A b).natDegree + (F.key ^ b).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ (F.key.natDegree - 1) + b * F.key.natDegree := by
              have h1 := hdevdeg b
              have h2 : (F.key ^ b).natDegree ≤ b * F.key.natDegree :=
                Polynomial.natDegree_pow_le
              omega
          _ ≤ M * F.key.natDegree - 1 := by
              have h1 : b * F.key.natDegree ≤ (M - 1) * F.key.natDegree :=
                Nat.mul_le_mul_right _ (by omega)
              have h2 : (M - 1) * F.key.natDegree + F.key.natDegree = M * F.key.natDegree := by
                rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hM1]
              omega
      have hgkdeg : (g * F.key ^ M).natDegree = g.natDegree + M * F.key.natDegree := by
        rw [Polynomial.natDegree_mul hgne (pow_ne_zero M F.hmonic.ne_zero),
          Polynomial.natDegree_pow]
      have hdegA : A.natDegree = g.natDegree + M * F.key.natDegree := by
        conv_lhs => rw [hAsplit]
        rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt, hgkdeg]
        rw [hgkdeg]
        have : 0 < M * F.key.natDegree := Nat.mul_pos (by omega) hD
        omega
      -- the peel objects
      set u : Polynomial O := g * F.key ^ (M - T.e₂ * T.f₂) with hudef
      set B : Polynomial O := composedKey T * u with hBdef
      have hpowMq : F.key ^ (M - T.e₂ * T.f₂) * F.key ^ (T.e₂ * T.f₂) = F.key ^ M := by
        rw [← pow_add, Nat.sub_add_cancel hMq]
      -- the two-variable lift of A − B and its weight floor
      have hwA : (w : ℕ∞) ≤ WT T (xNF F A) := by
        rw [← dv2Hgt_eq_WT_phiNF T hπ]
        exact hw
      have hwg : ∀ a, (w : ℕ∞) ≤ wtCoeff T (g.coeff a) a M := by
        intro a
        have h := le_trans hwA (WT_le_wtCoeff T (xNF F A) a M)
        rwa [hgcoeff] at h
      have hWTM : (w : ℕ∞) ≤ WT T (Polynomial.C g * Polynomial.X ^ M) := by
        rw [WT_C_mul_X_pow_eq]
        exact Finset.le_inf fun a _ => hwg a
      have hkeyshift : WT T (Polynomial.C g * Polynomial.X ^ (M - T.e₂ * T.f₂))
          + (T.E₂ : ℕ∞) = WT T (Polynomial.C g * Polynomial.X ^ M) := by
        rw [WT_C_mul_X_pow_eq, WT_C_mul_X_pow_eq, enat_finset_inf_add]
        refine Finset.inf_congr rfl fun a _ => ?_
        rw [← wtCoeff_outer_key_shift]
        congr 1
        omega
      have hpart1 : (w : ℕ∞) ≤ WT T (xNF F A - Polynomial.C g * Polynomial.X ^ M) := by
        refine le_WT_of_forall_wtCoeff T fun a b => ?_
        rw [Polynomial.coeff_sub, Polynomial.C_mul_X_pow_eq_monomial,
          Polynomial.coeff_monomial]
        by_cases hbM : M = b
        · rw [if_pos hbM, ← hbM, hgcoeff, sub_self, Polynomial.coeff_zero, wtCoeff_zero]
          exact le_top
        · rw [if_neg hbM, sub_zero]
          exact le_trans hwA (WT_le_wtCoeff T (xNF F A) a b)
      have htailfloor : (T.E₂ : ℕ∞)
          ≤ WT T (Polynomial.X ^ (T.e₂ * T.f₂) - K_T T) := by
        have hns : Polynomial.X ^ (T.e₂ * T.f₂) - K_T T
            = -(K_T T - Polynomial.X ^ (T.e₂ * T.f₂)) := by ring
        rw [hns, WT_neg]
        refine le_WT_of_forall_wtCoeff T fun a b => ?_
        by_cases hbq : b = T.e₂ * T.f₂
        · subst hbq
          rw [Polynomial.coeff_sub, coeff_K_T_top, Polynomial.coeff_X_pow, if_pos rfl,
            sub_self, Polynomial.coeff_zero, wtCoeff_zero]
          exact le_top
        · have hco : (K_T T - Polynomial.X ^ (T.e₂ * T.f₂)).coeff b = (K_T T).coeff b := by
            rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg hbq, sub_zero]
          rw [hco]
          by_cases hz : ((K_T T).coeff b).coeff a = 0
          · rw [hz, wtCoeff_zero]
            exact le_top
          · exact K_T_monomial_floor T hπ
              (Polynomial.mem_support_iff.mpr
                (fun h0 => hz (by rw [h0, Polynomial.coeff_zero])))
              (Polynomial.mem_support_iff.mpr hz)
      have hpart2 : (w : ℕ∞) ≤ WT T ((Polynomial.C g * Polynomial.X ^ (M - T.e₂ * T.f₂))
          * (Polynomial.X ^ (T.e₂ * T.f₂) - K_T T)) := by
        calc (w : ℕ∞)
            ≤ WT T (Polynomial.C g * Polynomial.X ^ (M - T.e₂ * T.f₂)) + (T.E₂ : ℕ∞) := by
              rw [hkeyshift]; exact hWTM
          _ ≤ WT T (Polynomial.C g * Polynomial.X ^ (M - T.e₂ * T.f₂))
              + WT T (Polynomial.X ^ (T.e₂ * T.f₂) - K_T T) := add_le_add le_rfl htailfloor
          _ ≤ WT T _ := WT_mul T _ _
      have hevalQ' : Polynomial.eval F.key
          ((xNF F A - Polynomial.C g * Polynomial.X ^ M)
            + (Polynomial.C g * Polynomial.X ^ (M - T.e₂ * T.f₂))
              * (Polynomial.X ^ (T.e₂ * T.f₂) - K_T T)) = A - B := by
        simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, xNF_eval,
          eval_K_T T hπ]
        rw [hBdef, hudef]
        linear_combination g * hpowMq
      have hwAB : (w : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) (A - B) := by
        rw [← hevalQ']
        exact le_dv2Hgt_of_eval T hπ _ (le_trans (le_min hpart1 hpart2) (WT_add T _ _))
      -- degree drop of both recursive arguments
      have hkq : (F.key ^ (T.e₂ * T.f₂) - composedKey T).natDegree
          ≤ (T.e₂ * T.f₂) * F.key.natDegree - 1 := by
        by_cases h0 : F.key ^ (T.e₂ * T.f₂) - composedKey T = 0
        · rw [h0, Polynomial.natDegree_zero]; omega
        · have hdd : (F.key ^ (T.e₂ * T.f₂) - composedKey T).degree
              < (F.key ^ (T.e₂ * T.f₂)).degree := by
            refine Polynomial.degree_sub_lt ?_ (F.hmonic.pow _).ne_zero ?_
            · rw [Polynomial.degree_eq_natDegree (F.hmonic.pow _).ne_zero,
                Polynomial.degree_eq_natDegree (composedKey_monic T).ne_zero,
                Polynomial.natDegree_pow, hΦdeg]
            · rw [(F.hmonic.pow _).leadingCoeff, (composedKey_monic T).leadingCoeff]
          have h1 := Polynomial.natDegree_lt_natDegree h0 hdd
          rw [Polynomial.natDegree_pow] at h1
          omega
      have hABid : A - B = low + g * F.key ^ (M - T.e₂ * T.f₂)
          * (F.key ^ (T.e₂ * T.f₂) - composedKey T) := by
        rw [hBdef, hudef]
        conv_lhs => rw [hAsplit]
        linear_combination (-g) * hpowMq
      have hsplitmul : (M - T.e₂ * T.f₂) * F.key.natDegree
          + (T.e₂ * T.f₂) * F.key.natDegree = M * F.key.natDegree := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hMq]
      have hABdeg : (A - B).natDegree ≤ n := by
        rw [hABid]
        refine le_trans (Polynomial.natDegree_add_le _ _) ?_
        have hterm2 : (g * F.key ^ (M - T.e₂ * T.f₂)
            * (F.key ^ (T.e₂ * T.f₂) - composedKey T)).natDegree
            ≤ g.natDegree + (M - T.e₂ * T.f₂) * F.key.natDegree
              + ((T.e₂ * T.f₂) * F.key.natDegree - 1) := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          have ha : (g * F.key ^ (M - T.e₂ * T.f₂)).natDegree
              ≤ g.natDegree + (M - T.e₂ * T.f₂) * F.key.natDegree := by
            refine le_trans Polynomial.natDegree_mul_le ?_
            have : (F.key ^ (M - T.e₂ * T.f₂)).natDegree
                ≤ (M - T.e₂ * T.f₂) * F.key.natDegree := Polynomial.natDegree_pow_le
            omega
          omega
        have hM0 : 0 < M * F.key.natDegree := Nat.mul_pos (by omega) hD
        refine max_le ?_ ?_
        · omega
        · omega
      have hudeg : u.natDegree ≤ n := by
        rw [hudef]
        refine le_trans Polynomial.natDegree_mul_le ?_
        have h1 : (F.key ^ (M - T.e₂ * T.f₂)).natDegree
            ≤ (M - T.e₂ * T.f₂) * F.key.natDegree := Polynomial.natDegree_pow_le
        omega
      have hwu : ((w - T.E₂ : ℕ) : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) u := by
        have hWTu : ((w - T.E₂ : ℕ) : ℕ∞)
            ≤ WT T (Polynomial.C g * Polynomial.X ^ (M - T.e₂ * T.f₂)) := by
          refine coe_sub_le_of_le_add ?_
          rw [hkeyshift]
          exact hWTM
        have hevalu : Polynomial.eval F.key
            (Polynomial.C g * Polynomial.X ^ (M - T.e₂ * T.f₂)) = u := by
          rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
            Polynomial.eval_X, hudef]
        rw [← hevalu]
        exact le_dv2Hgt_of_eval T hπ _ hWTu
      -- the honest-digit recursion
      have hdevsplit : ∀ i', dev (composedKey T) A i'
          = dev (composedKey T) (A - B) i' + dev (composedKey T) B i' := by
        intro i'
        conv_lhs => rw [show A = (A - B) + B by ring]
        exact dev_add_of_monic (composedKey_monic T) _ _ i'
      cases i with
      | zero =>
          have hB0 : dev (composedKey T) B 0 = 0 := by
            rw [← devQ_eq_dev, hBdef]
            exact recarry_step_zero (composedKey_monic T) u
          rw [hdevsplit 0, hB0, add_zero]
          exact ih (A - B) hABdeg hwAB 0
      | succ i =>
          have hBstep : dev (composedKey T) B (i + 1) = dev (composedKey T) u i := by
            rw [← devQ_eq_dev, ← devQ_eq_dev, hBdef]
            exact recarry_moves_up_one (composedKey_monic T) u i
          rw [hdevsplit (i + 1), hBstep]
          have h1 := ih (A - B) hABdeg hwAB (i + 1)
          have h2raw := ih u hudeg hwu i
          have harith : w - T.E₂ - i * T.E₂ = w - (i + 1) * T.E₂ := by
            rw [Nat.succ_mul]
            omega
          rw [harith] at h2raw
          exact le_trans (le_min h1 h2raw) (dv2Hgt_add_min T hπ _ _)

/-! ## Part 3 — pricing the paid census value -/

/-- The strictly-paid part of the development reconstruction: everything above digit `0`. -/
theorem sum_dev_tail {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (g : Polynomial O) :
    ∑ i ∈ Finset.range g.natDegree, dev φ g (i + 1) * φ ^ (i + 1) = g - g %ₘ φ := by
  have hbound : g.natDegree < (g.natDegree + 1) * φ.natDegree := by
    calc g.natDegree < g.natDegree + 1 := Nat.lt_succ_self _
      _ = (g.natDegree + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (g.natDegree + 1) * φ.natDegree := Nat.mul_le_mul_left _ hd
  have h := sum_dev_eq hφ hd g hbound
  rw [Finset.sum_range_succ'] at h
  have h0 : dev φ g 0 * φ ^ 0 = g %ₘ φ := by
    rw [pow_zero, mul_one]
    rfl
  rw [h0] at h
  exact eq_sub_of_add_eq h

/-- The two-variable paid lift of a census digit `S`: every strictly positive `Φ′`-digit
of every coefficient of `S`, re-priced at its paid outer position `(i + 1) + b`. -/
noncomputable def paidLift (F : KeyFrame O π) (S : Polynomial (Polynomial O)) :
    Polynomial (Polynomial O) :=
  ∑ b ∈ Finset.range (S.natDegree + 1),
    ∑ i ∈ Finset.range ((S.coeff b).natDegree),
      Polynomial.C (dev F.key (S.coeff b) (i + 1)) * Polynomial.X ^ (i + 1 + b)

/-- The paid lift evaluates to the census digit minus its reduced (unpaid) part. -/
theorem eval_paidLift (F : KeyFrame O π) (S : Polynomial (Polynomial O)) :
    Polynomial.eval F.key (paidLift F S)
      = Polynomial.eval F.key S
        - ∑ b ∈ Finset.range (S.natDegree + 1), (S.coeff b %ₘ F.key) * F.key ^ b := by
  have hD : 0 < F.key.natDegree := F.natDegree_key_pos
  rw [paidLift, Polynomial.eval_finsetSum]
  have hterm : ∀ b ∈ Finset.range (S.natDegree + 1),
      Polynomial.eval F.key (∑ i ∈ Finset.range ((S.coeff b).natDegree),
        Polynomial.C (dev F.key (S.coeff b) (i + 1)) * Polynomial.X ^ (i + 1 + b))
      = (S.coeff b - S.coeff b %ₘ F.key) * F.key ^ b := by
    intro b _
    rw [Polynomial.eval_finsetSum]
    have hinner : ∀ i ∈ Finset.range ((S.coeff b).natDegree),
        Polynomial.eval F.key
          (Polynomial.C (dev F.key (S.coeff b) (i + 1)) * Polynomial.X ^ (i + 1 + b))
        = dev F.key (S.coeff b) (i + 1) * F.key ^ (i + 1) * F.key ^ b := by
      intro i _
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        pow_add]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, sum_dev_tail F.hmonic hD]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_congr rfl (fun x _ => sub_mul (S.coeff x) (S.coeff x %ₘ F.key) (F.key ^ x)),
    Finset.sum_sub_distrib]
  congr 1
  exact (Polynomial.eval_eq_sum_range F.key).symm

/-- **The paid lift clears the census-digit floor plus one margin**: every strictly paid
digit gains at least `δ` (the inner paid ledger at `m = i + 1 ≥ 1`). -/
theorem WT_paidLift (T : TowerDatum F H₀ hpin) {S : Polynomial (Polynomial O)} {w : ℕ}
    (hS : (w : ℕ∞) ≤ WT T S) :
    ((w + T.margin : ℕ) : ℕ∞) ≤ WT T (paidLift F S) := by
  rw [paidLift]
  refine le_WT_sum T _ _ fun b _ => le_WT_sum T _ _ fun i _ => ?_
  refine le_WT_C_mul_X_pow T _ _ fun a => ?_
  have hfl : ∀ a', (w : ℕ∞) ≤ wtCoeff T ((S.coeff b).coeff a') a' b :=
    fun a' => le_trans hS (WT_le_wtCoeff T S a' b)
  have h := dev_coeff_paid_floor T ((S.coeff b).natDegree) (S.coeff b) le_rfl hfl (i + 1) a
  refine le_trans ?_ h
  have h1 : T.margin ≤ (i + 1) * T.margin := Nat.le_mul_of_pos_left _ (Nat.succ_pos i)
  calc ((w + T.margin : ℕ) : ℕ∞) ≤ ((w + (i + 1) * T.margin : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : w + T.margin ≤ w + (i + 1) * T.margin)
    _ = (w : ℕ∞) + (((i + 1) * T.margin : ℕ) : ℕ∞) := by push_cast; ring

/-- **The census-overflow entry floor**: `dv2Hgt (censusOverflow T f) ≥ μ₂E₂ + δ`, from
the entry ledger on `f` (C.131n′'s `quotDigit_floor_of_le` at every coordinate) plus one
paid margin per overflow contribution (`WT_paidLift`). -/
theorem dv2Hgt_censusOverflow_floor (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    {μ₂ : ℕ} {f : Polynomial O}
    (hentry : ((μ₂ * T.E₂ : ℕ) : ℕ∞) ≤ WT T (xNF F f)) :
    ((μ₂ * T.E₂ + T.margin : ℕ) : ℕ∞)
      ≤ dv2Hgt (T.levelDatum hπ) (censusOverflow T f) := by
  classical
  have heval : Polynomial.eval F.key
      (∑ j' ∈ Finset.range ((xNF F f).natDegree + 1),
        paidLift F (devQ (xNF F (composedKey T)) (xNF F f) j') * K_T T ^ j')
      = censusOverflow T f := by
    rw [Polynomial.eval_finsetSum, censusOverflow]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_pow, eval_K_T T hπ, eval_paidLift]
    congr 1
    have hsplit := collapse_unpaid_add_paid F (xNF F (composedKey T)) f j'
    rw [collapse_unpaidValue] at hsplit
    exact (eq_sub_of_add_eq' hsplit).symm
  have hWT : ((μ₂ * T.E₂ + T.margin : ℕ) : ℕ∞)
      ≤ WT T (∑ j' ∈ Finset.range ((xNF F f).natDegree + 1),
          paidLift F (devQ (xNF F (composedKey T)) (xNF F f) j') * K_T T ^ j') := by
    refine le_WT_sum T _ _ fun j' _ => ?_
    have hdig : ((μ₂ * T.E₂ - j' * T.E₂ : ℕ) : ℕ∞)
        ≤ WT T (devQ (xNF F (composedKey T)) (xNF F f) j') := by
      rw [← K_T_eq_xNF T hπ, devQ_eq_quotDigit]
      exact quotDigit_floor_of_le T hπ (μ₂ * T.E₂) (xNF F f) hentry j'
    have hpl := WT_paidLift T hdig
    have hpow := le_WT_K_T_pow T hπ j'
    calc ((μ₂ * T.E₂ + T.margin : ℕ) : ℕ∞)
        ≤ ((μ₂ * T.E₂ - j' * T.E₂ + T.margin + j' * T.E₂ : ℕ) : ℕ∞) := by
          exact_mod_cast (by omega :
            μ₂ * T.E₂ + T.margin ≤ μ₂ * T.E₂ - j' * T.E₂ + T.margin + j' * T.E₂)
      _ = ((μ₂ * T.E₂ - j' * T.E₂ + T.margin : ℕ) : ℕ∞) + ((j' * T.E₂ : ℕ) : ℕ∞) := by
          push_cast; ring
      _ ≤ WT T (paidLift F (devQ (xNF F (composedKey T)) (xNF F f) j'))
          + WT T (K_T T ^ j') := add_le_add hpl hpow
      _ ≤ WT T _ := WT_mul T _ _
  rw [← heval]
  exact le_dv2Hgt_of_eval T hπ _ hWT

/-! ## Part 4 — the locus entry floor -/

/-- **The tower-entry floor** (v2's "the FULL-SIDE hypothesis, consumed exactly once,
through `μ₁u₂ = μ₂E₂`"): a locus member's level-two height clears `μ₂E₂`, from the
`IsDvPure` right endpoint `μ₁ = μ₂e₂f₂` of the level polygon. -/
theorem towerLocus_entry_floor (T : TowerDatum F H₀ hpin) (hπ : Irreducible π)
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) :
    ((μ₂ * T.E₂ : ℕ) : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) f := by
  obtain ⟨hmon, hdeg, hpure, hres⟩ := hf
  have hD : 0 < F.e₁ * F.f₁ := Nat.mul_pos F.he₁ F.hf₁
  have hj₁ : f.natDegree / (F.e₁ * F.f₁) = μ₂ * (T.e₂ * T.f₂) := by
    rw [hdeg, TowerDatum.D₂,
      show μ₂ * ((F.e₁ * F.f₁) * (T.e₂ * T.f₂)) = (F.e₁ * F.f₁) * (μ₂ * (T.e₂ * T.f₂))
        by ring]
    exact Nat.mul_div_cancel_left _ hD
  have hmem := hpure.2
  rw [hj₁] at hmem
  unfold dvSideSet at hmem
  simp only [Finset.mem_filter] at hmem
  have heq := hmem.2.1
  rw [dv2Hgt]
  change ((μ₂ * T.E₂ : ℕ) : ℕ∞) ≤ dvSupp F f T.u₂ T.e₂
  rw [heq]
  refine le_trans (le_of_eq ?_) le_add_self
  simp only [TowerDatum.E₂]
  push_cast
  ring

/-! ## Part 5 — NODE C.131w′: the headline theorem -/

-- Binders byte-frozen from the leanspec twin (NODE C.72, `shadow_floor`); the unconsumed
-- signed binders `hh` and `[Finite (ResidueField O)]` are kept, as in `C72.lean`.
set_option linter.unusedVariables false in
/-- ★ **NODE C.131w′ — C.72 `shadow_floor` (GENTOW-3(i), the FLOOR).**  For `f` in the
tower-entry locus and `j < μ₂`, every `dv₂`-height at which the stage-shadow read and the
composed (honest) read differ clears the faithfulness threshold
`Θ_j = (μ₂ − j)E₂ + δ = T.theta μ₂ j`.

Proof: C.131v′'s `shadow_discrepancy` identifies the difference with the (negated) honest
redevelopment of the paid census value `censusOverflow T f`; the locus prices the entry at
`μ₂E₂` (`towerLocus_entry_floor`), the paid census gains `δ`
(`dv2Hgt_censusOverflow_floor`), and the honest-digit ledger pays `jE₂` down to
coordinate `j` (`dv2Hgt_dev_floor`), landing exactly at `Θ_j`. -/
theorem shadow_floor {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (IsLocalRing.ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂) :
    (T.theta μ₂ j : ℕ∞)
      ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T f j - dev (composedKey T) f j) := by
  rw [shadow_discrepancy T hπ f j, dv2Hgt_neg T hπ]
  have hentry : ((μ₂ * T.E₂ : ℕ) : ℕ∞) ≤ WT T (xNF F f) := by
    rw [← dv2Hgt_eq_WT_phiNF T hπ]
    exact towerLocus_entry_floor T hπ hf
  have hco := dv2Hgt_censusOverflow_floor T hπ hentry
  have hdev := dv2Hgt_dev_floor T hπ ((censusOverflow T f).natDegree)
    (censusOverflow T f) le_rfl hco j
  refine le_trans ?_ hdev
  have hjE : j * T.E₂ ≤ μ₂ * T.E₂ := Nat.mul_le_mul_right _ (Nat.le_of_lt hj)
  have hth : T.theta μ₂ j ≤ μ₂ * T.E₂ + T.margin - j * T.E₂ := by
    have h1 : (μ₂ - j) * T.E₂ = μ₂ * T.E₂ - j * T.E₂ := Nat.sub_mul μ₂ j T.E₂
    simp only [TowerDatum.theta, h1]
    omega
  exact_mod_cast hth

set_option linter.unusedVariables false in
/-- The landing, tied to C.72's signed statement carrier: `ShadowFloorStatement` holds at
every locus member and every coordinate `j < μ₂`. -/
theorem shadow_floor_statement {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
    [Finite (IsLocalRing.ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (hf : f ∈ towerLocus T μ₂) {j : ℕ} (hj : j < μ₂) :
    ShadowFloorStatement T hπ μ₂ f j :=
  shadow_floor T hπ hh hf hj

end Uniformity.Density.Tower.C131w

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131w.le_WT_of_forall_wtCoeff
#print axioms Uniformity.Density.Tower.C131w.WT_C_mul_X_pow_eq
#print axioms Uniformity.Density.Tower.C131w.xNF_add
#print axioms Uniformity.Density.Tower.C131w.dev_neg
#print axioms Uniformity.Density.Tower.C131w.xNF_neg
#print axioms Uniformity.Density.Tower.C131w.dv2Hgt_add_min
#print axioms Uniformity.Density.Tower.C131w.dv2Hgt_neg
#print axioms Uniformity.Density.Tower.C131w.le_dv2Hgt_of_eval
#print axioms Uniformity.Density.Tower.C131w.K_T_eq_xNF
#print axioms Uniformity.Density.Tower.C131w.wtCoeff_paid_shift
#print axioms Uniformity.Density.Tower.C131w.dev_coeff_paid_floor
#print axioms Uniformity.Density.Tower.C131w.dv2Hgt_dev_floor
#print axioms Uniformity.Density.Tower.C131w.sum_dev_tail
#print axioms Uniformity.Density.Tower.C131w.paidLift
#print axioms Uniformity.Density.Tower.C131w.eval_paidLift
#print axioms Uniformity.Density.Tower.C131w.WT_paidLift
#print axioms Uniformity.Density.Tower.C131w.dv2Hgt_censusOverflow_floor
#print axioms Uniformity.Density.Tower.C131w.towerLocus_entry_floor
#print axioms Uniformity.Density.Tower.C131w.shadow_floor
#print axioms Uniformity.Density.Tower.C131w.shadow_floor_statement

end AxCheck
