/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10RungPacks

/-!
# Uniformity.ChapI.I10RungLift3 — UNIT RL3: `RungLift` at rungs ≥ 3 — the generic core

RUNG (`I10RungPacks`) adjudicated the per-rung key lift `RungLift` (hom to the next
letter's ring + key pack + pushed nonvanishing) as the honest named obligation at rungs
≥ 3.  This file DISCHARGES the generic parts:

* §1 ★ the two D3AD-interface support laws (`supp_mod`/`supp_quot`) at the ITERATED
  carrier are DERIVED, not assumed: from the pack's own laws (`nextSupp_mul`,
  `nextRead` additivity/multiplicativity/nonvanishing) plus a prime factor `ρ` of the
  next key's read (the root-relation datum) and the small-degree coprimality
  (`SmallCoprime`, FGMN's `graded_scalar_nonzero` genre), both laws follow.  The
  case analyses are neg-free on the support side (reads at the dominated grade).
* §2 ★ `RungLift.ofPrime` — the generic rung-≥3 constructor: the next letter's ring is
  BUILT (`AdjoinRoot ρ`), so the root relation `read_key = 0` holds by construction
  (`AdjoinRoot.mk_eq_zero`), and every `CarrierKey` field is supplied.  The honest
  per-rung remainder shrinks to: the next key with its exact iterated grade, the
  prime factor of its read, `SmallCoprime`, and the slope data.
* §3 ★★ the f′ = 1 closed form `RungLift.ofRootF1`: when the next key degree is
  ≤ ℓ·(inner key degree) and `gcd u ℓ = 1`, the grade-`m` diagonal of any `g` below
  the key-degree fence holds AT MOST ONE dev slot (`nextRead_eq_monomial` — guard
  slots are spaced `ℓ` apart, dev slots run only to `⌊deg g/deg key⌋ < ℓ`), so for
  `φ = eval` at any NONZERO root `c` of the key's read the pushed nonvanishing is
  GENERIC.  The next ring is `K` itself — iterable without ring growth.  This is the
  S2 witness's actual mechanism (`eval 1`, residual `X+1`, f′ = 1 at every stage).
* §4 f′ ≥ 2 supports: existence of a prime factor of the key's read over a field
  (`exists_prime_factor_nextRead`), and the degree-fence route to `SmallCoprime`
  (`smallCoprime_of_natDegree_le` — generic exactly when e′ = 1, i.e. the next key
  degree is ≤ (deg ρ)·(inner key degree)).
* §5 bundled `LiftAt` wrappers, so `towerPacks` fires through the constructors.

Uniformity: no `residueCard`, no numeral, no S2 datum in §§1–5.

The honest remainder per rung ≥ 3 after this file, exactly: (i) the next key
`key₃` with its exact iterated grade `nextSupp key₃ = kgrade` (the tower-norm
computation), (ii) the root datum — a nonzero root `c` of `nextRead kgrade key₃`
(f′ = 1) or a prime factor `ρ` with `SmallCoprime` when `e′ > 1, f′ ≥ 2` (the genuine
FGMN residual mechanics), and (iii) the next slopes with `ℓ'·kgrade < u'` (the
tower's `hfloor` datum, D3AD-spine genre).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.I10rl3

open Polynomial Uniformity.Density Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.I10wcc
open Uniformity.Density.Tower.I10rung

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type*} [CommRing K]

/-! ## §1 — the derived D3AD-interface laws at the iterated carrier -/

section Derived

variable {u ℓ : ℕ} (R : RungPack O K u ℓ)

/-- **The small-degree coprimality** (FGMN `graded_scalar_nonzero` genre): the reads of
exact-grade elements below the next key's degree fence avoid the factor `ρ`. -/
def SmallCoprime (key₃ : Polynomial O) (ρ : Polynomial K) : Prop :=
  ∀ {m : ℕ} {g : Polynomial O}, g.natDegree < key₃.natDegree →
    nextSupp R.C R.P g = (m : ℕ∞) → ¬ ρ ∣ nextRead R.C R.P m g

/-- the remainder mod a monic key of positive degree stays below the key degree. -/
private theorem natDegree_mod_lt {key₃ : Polynomial O} (hmon : key₃.Monic)
    (hdpos : 0 < key₃.natDegree) (f : Polynomial O) :
    (f %ₘ key₃).natDegree < key₃.natDegree := by
  rcases eq_or_ne (f %ₘ key₃) 0 with h0 | h0
  · rw [h0, Polynomial.natDegree_zero]; exact hdpos
  · exact Polynomial.natDegree_lt_natDegree h0 (Polynomial.degree_modByMonic_lt f hmon)

/-- ★ **The derived sharp quotient bound** (`supp_quot` at the iterated carrier, for
EVERY dividend): from the root-relation datum and `SmallCoprime` alone. -/
theorem nextSupp_quot_le [NoZeroDivisors K] {key₃ : Polynomial O} {kg : ℕ}
    (hmon : key₃.Monic) (hdpos : 0 < key₃.natDegree)
    (hsupp : nextSupp R.C R.P key₃ = (kg : ℕ∞)) {ρ : Polynomial K}
    (hdvd : ρ ∣ nextRead R.C R.P kg key₃) (hcop : SmallCoprime R key₃ ρ)
    (f : Polynomial O) :
    nextSupp R.C R.P f ≤ (kg : ℕ∞) + nextSupp R.C R.P (f /ₘ key₃) := by
  rcases eq_or_ne (nextSupp R.C R.P (f /ₘ key₃)) ⊤ with hqT | hqT
  · rw [hqT, add_top]; exact le_top
  obtain ⟨Sq, hSq⟩ := ENat.ne_top_iff_exists.1 hqT
  by_contra hlt
  rw [not_le] at hlt
  -- the division identity and the quotient-part support
  have hid : f %ₘ key₃ + key₃ * (f /ₘ key₃) = f := Polynomial.modByMonic_add_div f key₃
  have hkq : nextSupp R.C R.P (key₃ * (f /ₘ key₃))
      = ((kg + Sq : ℕ) : ℕ∞) := by
    rw [nextSupp_mul R, hsupp, ← hSq]; push_cast; rfl
  have hm' : (kg : ℕ∞) + nextSupp R.C R.P (f /ₘ key₃) = ((kg + Sq : ℕ) : ℕ∞) := by
    rw [← hSq]; push_cast; rfl
  rw [hm'] at hlt
  rcases lt_or_ge (nextSupp R.C R.P (f %ₘ key₃)) (((kg + Sq : ℕ) : ℕ∞)) with hA | hB
  · -- Case A: the remainder's support is strictly below the quotient part — its exact
    -- read survives while both `f` and the quotient part read `0` there.
    have hrT : nextSupp R.C R.P (f %ₘ key₃) ≠ ⊤ :=
      ne_top_of_lt hA
    obtain ⟨m'', hm''⟩ := ENat.ne_top_iff_exists.1 hrT
    have hAm : ((m'' : ℕ) : ℕ∞) < ((kg + Sq : ℕ) : ℕ∞) := by rw [hm'']; exact hA
    have hsplit : nextRead R.C R.P m'' f
        = nextRead R.C R.P m'' (f %ₘ key₃)
          + nextRead R.C R.P m'' (key₃ * (f /ₘ key₃)) := by
      have h := nextRead_add R (le_of_eq hm'')
        (show ((m'' : ℕ) : ℕ∞) ≤ nextSupp R.C R.P (key₃ * (f /ₘ key₃)) by
          rw [hkq]; exact le_of_lt hAm)
      rw [hid] at h
      exact h
    have hf0 : nextRead R.C R.P m'' f = 0 :=
      nextRead_above R (lt_trans hAm hlt)
    have hkq0 : nextRead R.C R.P m'' (key₃ * (f /ₘ key₃)) = 0 :=
      nextRead_above R (by rw [hkq]; exact hAm)
    rw [hf0, hkq0, add_zero] at hsplit
    exact nextRead_ne_zero_of_exact R hm''.symm hsplit.symm
  · -- Case B: the remainder rides at or above the quotient part; the read at the
    -- quotient grade forces the remainder's exact support THERE, and its read is a
    -- key-read multiple — refuted by `SmallCoprime`.
    have hsplit : nextRead R.C R.P (kg + Sq) f
        = nextRead R.C R.P (kg + Sq) (f %ₘ key₃)
          + nextRead R.C R.P (kg + Sq) (key₃ * (f /ₘ key₃)) := by
      have h := nextRead_add R hB
        (show ((kg + Sq : ℕ) : ℕ∞) ≤ nextSupp R.C R.P (key₃ * (f /ₘ key₃)) from
          le_of_eq hkq.symm)
      rw [hid] at h
      exact h
    have hf0 : nextRead R.C R.P (kg + Sq) f = 0 := nextRead_above R hlt
    have hmul : nextRead R.C R.P (kg + Sq) (key₃ * (f /ₘ key₃))
        = nextRead R.C R.P kg key₃ * nextRead R.C R.P Sq (f /ₘ key₃) :=
      nextRead_mul R hsupp hSq.symm
    rw [hf0, hmul] at hsplit
    have hrne : nextRead R.C R.P (kg + Sq) (f %ₘ key₃)
        = -(nextRead R.C R.P kg key₃ * nextRead R.C R.P Sq (f /ₘ key₃)) :=
      eq_neg_of_add_eq_zero_left hsplit.symm
    have hne : nextRead R.C R.P (kg + Sq) (f %ₘ key₃) ≠ 0 := by
      rw [hrne, neg_ne_zero]
      exact mul_ne_zero (nextRead_ne_zero_of_exact R hsupp)
        (nextRead_ne_zero_of_exact R hSq.symm)
    have hrsupp : nextSupp R.C R.P (f %ₘ key₃) = ((kg + Sq : ℕ) : ℕ∞) := by
      refine le_antisymm ?_ hB
      by_contra hgt
      rw [not_le] at hgt
      exact hne (nextRead_above R hgt)
    refine hcop (natDegree_mod_lt hmon hdpos f) hrsupp ?_
    rw [hrne]
    exact dvd_neg.mpr (Dvd.dvd.mul_right hdvd _)

/-- ★ **The derived reduction law** (`supp_mod` at the iterated carrier): reduction mod
the next key preserves the iterated support of a small-degree product. -/
theorem nextSupp_mod_eq [NoZeroDivisors K] {key₃ : Polynomial O} {kg : ℕ}
    (hmon : key₃.Monic) (hdpos : 0 < key₃.natDegree)
    (hsupp : nextSupp R.C R.P key₃ = (kg : ℕ∞)) {ρ : Polynomial K} (hρ : Prime ρ)
    (hdvd : ρ ∣ nextRead R.C R.P kg key₃) (hcop : SmallCoprime R key₃ ρ)
    {a b : Polynomial O} (ha : a.natDegree < key₃.natDegree)
    (hb : b.natDegree < key₃.natDegree) :
    nextSupp R.C R.P ((a * b) %ₘ key₃) = nextSupp R.C R.P a + nextSupp R.C R.P b := by
  have hid : (a * b) %ₘ key₃ + key₃ * ((a * b) /ₘ key₃) = a * b :=
    Polynomial.modByMonic_add_div (a * b) key₃
  have hab : nextSupp R.C R.P (a * b) = nextSupp R.C R.P a + nextSupp R.C R.P b :=
    nextSupp_mul R a b
  have hquot : nextSupp R.C R.P (a * b)
      ≤ (kg : ℕ∞) + nextSupp R.C R.P ((a * b) /ₘ key₃) :=
    nextSupp_quot_le R hmon hdpos hsupp hdvd hcop (a * b)
  have hkq : nextSupp R.C R.P (key₃ * ((a * b) /ₘ key₃))
      = (kg : ℕ∞) + nextSupp R.C R.P ((a * b) /ₘ key₃) := by
    rw [nextSupp_mul R, hsupp]
  -- Step 1: the remainder's support is ≥ the product's (else its exact read survives
  -- a grade where both `a·b` and the key part read `0`).
  have hge : nextSupp R.C R.P (a * b) ≤ nextSupp R.C R.P ((a * b) %ₘ key₃) := by
    by_contra hgt
    rw [not_le] at hgt
    have hrT : nextSupp R.C R.P ((a * b) %ₘ key₃) ≠ ⊤ := ne_top_of_lt hgt
    obtain ⟨m'', hm''⟩ := ENat.ne_top_iff_exists.1 hrT
    have hgt' : ((m'' : ℕ) : ℕ∞) < nextSupp R.C R.P (a * b) := by rw [hm'']; exact hgt
    have hsplit : nextRead R.C R.P m'' (a * b)
        = nextRead R.C R.P m'' ((a * b) %ₘ key₃)
          + nextRead R.C R.P m'' (key₃ * ((a * b) /ₘ key₃)) := by
      have h := nextRead_add R (le_of_eq hm'')
        (show ((m'' : ℕ) : ℕ∞) ≤ nextSupp R.C R.P (key₃ * ((a * b) /ₘ key₃)) from
          le_trans (le_of_lt hgt') (le_trans hquot (le_of_eq hkq.symm)))
      rw [hid] at h
      exact h
    have hf0 : nextRead R.C R.P m'' (a * b) = 0 := nextRead_above R hgt'
    have hkq0 : nextRead R.C R.P m'' (key₃ * ((a * b) /ₘ key₃)) = 0 :=
      nextRead_above R (lt_of_lt_of_le hgt' (le_trans hquot (le_of_eq hkq.symm)))
    rw [hf0, hkq0, add_zero] at hsplit
    exact nextRead_ne_zero_of_exact R hm''.symm hsplit.symm
  -- Step 2: the remainder's support is ≤ the product's.  At an exact finite product
  -- grade the product's read is a nonzero product of small exact reads; were the
  -- remainder strictly above, the split would make it a key-read multiple — refuted
  -- by primality of `ρ` and `SmallCoprime` on both factors.
  refine le_antisymm ?_ (hab ▸ hge)
  rcases eq_or_ne (nextSupp R.C R.P a + nextSupp R.C R.P b) ⊤ with hT | hT
  · rw [hT]; exact le_top
  have haT : nextSupp R.C R.P a ≠ ⊤ := fun h => hT (by rw [h, top_add])
  have hbT : nextSupp R.C R.P b ≠ ⊤ := fun h => hT (by rw [h, add_top])
  obtain ⟨Sa, hSa⟩ := ENat.ne_top_iff_exists.1 haT
  obtain ⟨Sb, hSb⟩ := ENat.ne_top_iff_exists.1 hbT
  by_contra hgt
  rw [not_le] at hgt
  have hSab : nextSupp R.C R.P (a * b) = ((Sa + Sb : ℕ) : ℕ∞) := by
    rw [hab, ← hSa, ← hSb]; push_cast; rfl
  have hgt' : ((Sa + Sb : ℕ) : ℕ∞) < nextSupp R.C R.P ((a * b) %ₘ key₃) := by
    refine lt_of_le_of_lt ?_ hgt
    rw [← hSa, ← hSb]; push_cast; rfl
  -- the product's read at its exact grade, split across the division identity
  have hsplit : nextRead R.C R.P (Sa + Sb) (a * b)
      = nextRead R.C R.P (Sa + Sb) ((a * b) %ₘ key₃)
        + nextRead R.C R.P (Sa + Sb) (key₃ * ((a * b) /ₘ key₃)) := by
    have h := nextRead_add R (le_of_lt hgt')
      (show ((Sa + Sb : ℕ) : ℕ∞) ≤ nextSupp R.C R.P (key₃ * ((a * b) /ₘ key₃)) from
        le_trans (le_of_eq hSab.symm) (le_trans hquot (le_of_eq hkq.symm)))
    rw [hid] at h
    exact h
  have hr0 : nextRead R.C R.P (Sa + Sb) ((a * b) %ₘ key₃) = 0 :=
    nextRead_above R hgt'
  have habr : nextRead R.C R.P (Sa + Sb) (a * b)
      = nextRead R.C R.P Sa a * nextRead R.C R.P Sb b :=
    nextRead_mul R hSa.symm hSb.symm
  rw [hr0, zero_add, habr] at hsplit
  -- the key part's support: pinned to the exact product grade by the split
  have habne : nextRead R.C R.P Sa a * nextRead R.C R.P Sb b ≠ 0 :=
    mul_ne_zero (nextRead_ne_zero_of_exact R hSa.symm)
      (nextRead_ne_zero_of_exact R hSb.symm)
  have hqT : nextSupp R.C R.P ((a * b) /ₘ key₃) ≠ ⊤ := by
    intro h
    have : nextSupp R.C R.P (key₃ * ((a * b) /ₘ key₃)) = ⊤ := by rw [hkq, h, add_top]
    exact habne (by rw [hsplit]; exact nextRead_above R (by rw [this]; exact ENat.coe_lt_top _))
  obtain ⟨Sq, hSq⟩ := ENat.ne_top_iff_exists.1 hqT
  -- if the key part rides strictly above the product grade, the product read dies
  have hkey_exact : ((Sa + Sb : ℕ) : ℕ∞) = ((kg + Sq : ℕ) : ℕ∞) := by
    have hle : ((Sa + Sb : ℕ) : ℕ∞) ≤ ((kg + Sq : ℕ) : ℕ∞) := by
      have := le_trans (le_of_eq hSab.symm) hquot
      rw [← hSq] at this
      exact le_trans this (by push_cast; rfl)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exfalso
      refine habne ?_
      rw [hsplit]
      refine nextRead_above R ?_
      rw [hkq, ← hSq]
      exact lt_of_lt_of_le hlt (by push_cast; rfl)
    · exact heq
  have hSaSb : Sa + Sb = kg + Sq := by exact_mod_cast hkey_exact
  -- the product read IS a key-read multiple — the prime factor lands on a factor
  have hkmul : nextRead R.C R.P (Sa + Sb) (key₃ * ((a * b) /ₘ key₃))
      = nextRead R.C R.P kg key₃ * nextRead R.C R.P Sq ((a * b) /ₘ key₃) := by
    rw [hSaSb]
    exact nextRead_mul R hsupp hSq.symm
  rw [hkmul] at hsplit
  have hρdvd : ρ ∣ nextRead R.C R.P Sa a * nextRead R.C R.P Sb b := by
    rw [hsplit]
    exact Dvd.dvd.mul_right hdvd _
  rcases hρ.2.2 _ _ hρdvd with hda | hdb
  · exact hcop ha hSa.symm hda
  · exact hcop hb hSb.symm hdb

end Derived

/-! ## §2 — the generic constructor: the next letter's ring is BUILT -/

section OfPrime

variable {u ℓ : ℕ}

/-- ★ **The generic rung-≥3 lift**: given the next key with its exact iterated grade, a
prime factor `ρ` of its read (the root-relation datum), the small-degree coprimality,
and the next slopes, the `RungLift` EXISTS with next ring `AdjoinRoot ρ` — the root
relation `read_key = 0` holds BY CONSTRUCTION. -/
noncomputable def RungLift.ofPrime (R : RungPack O K u ℓ) [NoZeroDivisors K]
    {key₃ : Polynomial O} {kg u' ℓ' : ℕ} (hmon : key₃.Monic)
    (hdpos : 0 < key₃.natDegree) (hsupp : nextSupp R.C R.P key₃ = (kg : ℕ∞))
    {ρ : Polynomial K} (hρ : Prime ρ) (hdvd : ρ ∣ nextRead R.C R.P kg key₃)
    (hcop : SmallCoprime R key₃ ρ) (hℓ' : 0 < ℓ') (hstrict : ℓ' * kg < u') :
    RungLift R (AdjoinRoot ρ) u' ℓ' where
  φ := AdjoinRoot.mk ρ
  P' :=
    { key := key₃
      kgrade := kg
      monic := hmon
      deg_pos := hdpos
      supp_key := hsupp
      read_key := show AdjoinRoot.mk ρ (nextRead R.C R.P kg key₃) = 0 from
        AdjoinRoot.mk_eq_zero.mpr hdvd
      ell_pos := hℓ'
      strict := hstrict
      supp_mod := fun ha hb => nextSupp_mod_eq R hmon hdpos hsupp hρ hdvd hcop ha hb
      supp_quot := fun {a b} _ _ => by
        show nextSupp R.C R.P a + nextSupp R.C R.P b
          ≤ (kg : ℕ∞) + nextSupp R.C R.P ((a * b) /ₘ key₃)
        rw [← nextSupp_mul R]
        exact nextSupp_quot_le R hmon hdpos hsupp hdvd hcop (a * b) }
  exact_ne' := fun hdeg hsupp' h0 =>
    hcop hdeg hsupp' (AdjoinRoot.mk_eq_zero.mp h0)

end OfPrime

/-! ## §3 — the f′ = 1 closed form: eval at a nonzero root, generic -/

section RootF1

variable {u ℓ : ℕ}

/-- an occupied `wcoeff` slot below the f′ = 1 degree fence: it lies in `[0, ℓ)` and
carries the line guard (dev slots run only to `⌊deg g/deg key⌋ < ℓ`). -/
private theorem slot_facts (R : RungPack O K u ℓ) {key₃ : Polynomial O}
    (hdegk : key₃.natDegree ≤ ℓ * R.P.key.natDegree)
    {m : ℕ} {g : Polynomial O} (hdeg : g.natDegree < key₃.natDegree)
    {j : ℕ} (hj : wcoeff R.C R.P m g j ≠ 0) :
    j < ℓ ∧ u * j ≤ m ∧ ℓ ∣ (m - u * j) := by
  by_cases hgu : u * j ≤ m ∧ ℓ ∣ (m - u * j)
  swap
  · exact absurd (if_neg hgu : wcoeff R.C R.P m g j = 0) hj
  refine ⟨?_, hgu.1, hgu.2⟩
  have hdev : dev R.P.key g j ≠ 0 := by
    intro h0
    apply hj
    have hw : wcoeff R.C R.P m g j
        = R.C.read ((m - u * j) / ℓ) (dev R.P.key g j) := if_pos hgu
    rw [hw, h0, R.C.read_zero]
  have hnlt : j * R.P.key.natDegree ≤ g.natDegree :=
    Nat.le_of_not_lt fun hc =>
      hdev (dev_eq_zero_of_lt R.P.monic R.P.deg_pos g j hc)
  exact Nat.lt_of_mul_lt_mul_right
    (lt_of_le_of_lt hnlt (lt_of_lt_of_le hdeg hdegk))

/-- with coprime slopes, at most one slot below the fence is occupied: guard slots are
spaced `ℓ` apart while occupied slots lie in `[0, ℓ)`. -/
private theorem slot_unique (R : RungPack O K u ℓ) {key₃ : Polynomial O}
    (hdegk : key₃.natDegree ≤ ℓ * R.P.key.natDegree) (hgcd : Nat.gcd u ℓ = 1)
    {m : ℕ} {g : Polynomial O} (hdeg : g.natDegree < key₃.natDegree)
    {j j' : ℕ} (hj : wcoeff R.C R.P m g j ≠ 0)
    (hj' : wcoeff R.C R.P m g j' ≠ 0) : j = j' := by
  have h1 := slot_facts R hdegk hdeg hj
  have h2 := slot_facts R hdegk hdeg hj'
  have hm1 : u * j ≡ m [MOD ℓ] := (Nat.modEq_iff_dvd' h1.2.1).mpr h1.2.2
  have hm2 : u * j' ≡ m [MOD ℓ] := (Nat.modEq_iff_dvd' h2.2.1).mpr h2.2.2
  have hgcd' : Nat.gcd ℓ u = 1 := by rw [Nat.gcd_comm]; exact hgcd
  have hjj : j ≡ j' [MOD ℓ] :=
    Nat.ModEq.cancel_left_of_coprime hgcd' (hm1.trans hm2.symm)
  have hmod : j % ℓ = j' % ℓ := hjj
  rwa [Nat.mod_eq_of_lt h1.1, Nat.mod_eq_of_lt h2.1] at hmod

/-- ★ **The diagonal singleton**: below the fence `deg key₃ ≤ ℓ·deg key` with coprime
slopes, the iterated read of an exact-grade element is a single monomial with nonzero
scalar — guard slots are spaced `ℓ` apart while dev slots run only to
`⌊deg g/deg key⌋ < ℓ`. -/
theorem nextRead_eq_monomial (R : RungPack O K u ℓ) {key₃ : Polynomial O}
    (hdegk : key₃.natDegree ≤ ℓ * R.P.key.natDegree) (hgcd : Nat.gcd u ℓ = 1)
    {m : ℕ} {g : Polynomial O} (hdeg : g.natDegree < key₃.natDegree)
    (hsupp : nextSupp R.C R.P g = (m : ℕ∞)) :
    ∃ j₀ : ℕ, ∃ w : K, w ≠ 0 ∧
      nextRead R.C R.P m g = Polynomial.C w * Polynomial.X ^ j₀ := by
  have hne : nextRead R.C R.P m g ≠ 0 := nextRead_ne_zero_of_exact R hsupp
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, wcoeff R.C R.P m g j₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (Polynomial.ext fun J => by
      rw [nextRead_coeff, hc J, Polynomial.coeff_zero])
  refine ⟨j₀, wcoeff R.C R.P m g j₀, hj₀, ?_⟩
  refine Polynomial.ext fun J => ?_
  rw [nextRead_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hJ : J = j₀
  · subst hJ
    rw [if_pos rfl, mul_one]
  · rw [if_neg hJ, mul_zero]
    by_contra hw
    exact hJ (slot_unique R hdegk hgcd hdeg hw hj₀)

/-- ★★ **The f′ = 1 lift, fully generic**: when the next key degree is at most
`ℓ·deg key` and the slopes are coprime, ANY nonzero root `c` of the next key's read
supplies the whole `RungLift` with next ring `K` itself (`φ = eval c`): the pushed
nonvanishing is the diagonal singleton, and the support laws are §1 at `ρ = X − C c`.
This is the S2 witness's mechanism (`eval 1`, residual `X + 1`) made frame-generic. -/
noncomputable def RungLift.ofRootF1 (R : RungPack O K u ℓ) [IsDomain K]
    {key₃ : Polynomial O} {kg u' ℓ' : ℕ} (hmon : key₃.Monic)
    (hdpos : 0 < key₃.natDegree) (hdegk : key₃.natDegree ≤ ℓ * R.P.key.natDegree)
    (hgcd : Nat.gcd u ℓ = 1) (hsupp : nextSupp R.C R.P key₃ = (kg : ℕ∞))
    {c : K} (hc0 : c ≠ 0)
    (hroot : Polynomial.eval c (nextRead R.C R.P kg key₃) = 0)
    (hℓ' : 0 < ℓ') (hstrict : ℓ' * kg < u') :
    RungLift R K u' ℓ' :=
  have hρ : Prime (Polynomial.X - Polynomial.C c) := Polynomial.prime_X_sub_C c
  have hdvd : (Polynomial.X - Polynomial.C c) ∣ nextRead R.C R.P kg key₃ :=
    Polynomial.dvd_iff_isRoot.mpr hroot
  have hcop : SmallCoprime R key₃ (Polynomial.X - Polynomial.C c) := by
    intro m g hdeg hs hdvd'
    obtain ⟨j₀, w, hw, hEq⟩ := nextRead_eq_monomial R hdegk hgcd hdeg hs
    have h0 : Polynomial.eval c (nextRead R.C R.P m g) = 0 :=
      Polynomial.dvd_iff_isRoot.mp hdvd'
    rw [hEq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact hw h
    · exact pow_ne_zero _ hc0 h
  { φ := Polynomial.evalRingHom c
    P' :=
      { key := key₃
        kgrade := kg
        monic := hmon
        deg_pos := hdpos
        supp_key := hsupp
        read_key := show Polynomial.eval c (nextRead R.C R.P kg key₃) = 0 from hroot
        ell_pos := hℓ'
        strict := hstrict
        supp_mod := fun ha hb =>
          nextSupp_mod_eq R hmon hdpos hsupp hρ hdvd hcop ha hb
        supp_quot := fun {a b} _ _ => by
          show nextSupp R.C R.P a + nextSupp R.C R.P b
            ≤ (kg : ℕ∞) + nextSupp R.C R.P ((a * b) /ₘ key₃)
          rw [← nextSupp_mul R]
          exact nextSupp_quot_le R hmon hdpos hsupp hdvd hcop (a * b) }
    exact_ne' := fun {m g} hdeg hs h0 => by
      obtain ⟨j₀, w, hw, hEq⟩ := nextRead_eq_monomial R hdegk hgcd hdeg hs
      have h0' : Polynomial.eval c (nextRead R.C R.P m g) = 0 := h0
      rw [hEq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X] at h0'
      rcases mul_eq_zero.mp h0' with h | h
      · exact hw h
      · exact pow_ne_zero _ hc0 h }

end RootF1

/-! ## §4 — f′ ≥ 2 supports -/

section F2

variable {u ℓ : ℕ}

/-- over a FIELD, the next key's read (nonzero of positive degree) has a prime factor —
the residual polynomial exists generically; only its `SmallCoprime` is per-realization. -/
theorem exists_prime_factor_nextRead {K : Type*} [Field K] (R : RungPack O K u ℓ)
    {key₃ : Polynomial O} {kg : ℕ} (hsupp : nextSupp R.C R.P key₃ = (kg : ℕ∞))
    (hdegpos : 0 < (nextRead R.C R.P kg key₃).natDegree) :
    ∃ ρ : Polynomial K, Prime ρ ∧ ρ ∣ nextRead R.C R.P kg key₃ := by
  have hne : nextRead R.C R.P kg key₃ ≠ 0 := nextRead_ne_zero_of_exact R hsupp
  have hnu : ¬ IsUnit (nextRead R.C R.P kg key₃) :=
    Polynomial.not_isUnit_of_natDegree_pos _ hdegpos
  obtain ⟨ρ, hirr, hdvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hne
  exact ⟨ρ, hirr.prime, hdvd⟩

/-- the degree-fence route to `SmallCoprime` (generic exactly when the next key degree
is ≤ (deg ρ)·(inner key degree), i.e. the e′ = 1 regime): small-degree exact reads have
degree `< deg ρ` and are nonzero, hence avoid `ρ`. -/
theorem smallCoprime_of_natDegree_le (R : RungPack O K u ℓ) [NoZeroDivisors K]
    {key₃ : Polynomial O} {ρ : Polynomial K}
    (hdegk : key₃.natDegree ≤ ρ.natDegree * R.P.key.natDegree) :
    SmallCoprime R key₃ ρ := by
  intro m g hdeg hs hdvd
  have hne : nextRead R.C R.P m g ≠ 0 := nextRead_ne_zero_of_exact R hs
  have hcoeff : ∀ J, ρ.natDegree ≤ J → (nextRead R.C R.P m g).coeff J = 0 := by
    intro J hJ
    rw [nextRead_coeff]
    have hd0 : dev R.P.key g J = 0 := by
      refine dev_eq_zero_of_lt R.P.monic R.P.deg_pos g J ?_
      calc g.natDegree < key₃.natDegree := hdeg
        _ ≤ ρ.natDegree * R.P.key.natDegree := hdegk
        _ ≤ J * R.P.key.natDegree := Nat.mul_le_mul_right _ hJ
    by_cases hgu : u * J ≤ m ∧ ℓ ∣ (m - u * J)
    · have hw : wcoeff R.C R.P m g J
          = R.C.read ((m - u * J) / ℓ) (dev R.P.key g J) := if_pos hgu
      rw [hw, hd0, R.C.read_zero]
    · exact (if_neg hgu : wcoeff R.C R.P m g J = 0)
  rcases Nat.eq_zero_or_pos ρ.natDegree with hρ0 | hρ0
  · exact hne (Polynomial.ext fun J => by
      rw [hcoeff J (hρ0 ▸ Nat.zero_le J), Polynomial.coeff_zero])
  · have hdlt : (nextRead R.C R.P m g).natDegree < ρ.natDegree := by
      by_contra hge
      rw [not_lt] at hge
      exact (Polynomial.leadingCoeff_ne_zero.mpr hne) (hcoeff _ hge)
    exact absurd (Polynomial.natDegree_le_of_dvd hdvd hne) (not_le.mpr hdlt)

end F2

/-! ## §5 — bundled wrappers: `towerPacks` fires through the constructors -/

section Wrappers

universe v

/-- the f′ = 1 lift bundled at a `PackAt`: the ring does not grow. -/
noncomputable def liftAtOfRootF1 (Q : PackAt.{v} O) [IsDomain Q.K]
    {key₃ : Polynomial O} {kg u' ℓ' : ℕ} (hmon : key₃.Monic)
    (hdpos : 0 < key₃.natDegree)
    (hdegk : key₃.natDegree ≤ Q.ℓ * Q.pack.P.key.natDegree)
    (hgcd : Nat.gcd Q.u Q.ℓ = 1)
    (hsupp : nextSupp Q.pack.C Q.pack.P key₃ = (kg : ℕ∞)) {c : Q.K} (hc0 : c ≠ 0)
    (hroot : Polynomial.eval c (nextRead Q.pack.C Q.pack.P kg key₃) = 0)
    (hℓ' : 0 < ℓ') (hstrict : ℓ' * kg < u') : LiftAt O Q :=
  ⟨Q.K, u', ℓ', RungLift.ofRootF1 Q.pack hmon hdpos hdegk hgcd hsupp hc0 hroot hℓ' hstrict⟩

/-- the general (f′ ≥ 1) lift bundled at ANY `PackAt`: the ring grows to `AdjoinRoot ρ`,
a domain again by primality of `ρ` (quotient by the prime ideal `(ρ)`), so the stream
stays iterable. -/
noncomputable def liftAtOfPrime (Q : PackAt.{v} O)
    {key₃ : Polynomial O} {kg u' ℓ' : ℕ} (hmon : key₃.Monic)
    (hdpos : 0 < key₃.natDegree)
    (hsupp : nextSupp Q.pack.C Q.pack.P key₃ = (kg : ℕ∞)) {ρ : Polynomial Q.K}
    (hρ : Prime ρ) (hdvd : ρ ∣ nextRead Q.pack.C Q.pack.P kg key₃)
    (hcop : SmallCoprime Q.pack key₃ ρ) (hℓ' : 0 < ℓ') (hstrict : ℓ' * kg < u') :
    LiftAt O Q :=
  haveI : (Ideal.span ({ρ} : Set (Polynomial Q.K))).IsPrime :=
    (Ideal.span_singleton_prime hρ.ne_zero).mpr hρ
  haveI hdom : IsDomain (Polynomial Q.K ⧸ Ideal.span ({ρ} : Set (Polynomial Q.K))) :=
    Ideal.Quotient.isDomain _
  { K' := AdjoinRoot ρ
    ring' := inferInstance
    nzd' := hdom.to_noZeroDivisors
    u' := u'
    ℓ' := ℓ'
    lift := RungLift.ofPrime Q.pack hmon hdpos hsupp hρ hdvd hcop hℓ' hstrict }

end Wrappers

/-! ## §6 — the S2 rung-3 witness: the exact remainder (documented, not landed)

The S2 depth-4 tower CARRIES the rung-3 data in landed form — the depth-3 key
`C136d2.g16 = g8² − 2⁸·Φ₂` (monic, `natDegree 16 = 2·8` — exactly the f′ = 1 fence
`deg key₃ = ℓ·deg key` at the S2 slopes `(u,ℓ) = (85,2)`, `gcd 85 2 = 1`), its exact
depth-3 grade `170` (`C136d2.g16_exactGrade : S2Mu4ExactGrade 170 g16`), and its μ₄
residual `X + 1` (`C136d2.s2Mu4GradedRes_g16`) with root `c = 1 ≠ 0` in char 2 — the
SAME eval-at-1 mechanism `RungLift.ofRootF1` makes generic.  Firing `ofRootF1` at the
witness therefore needs exactly THREE dictionary lemmas, none landed:

* **(W-a) the S2 rung-2 `RungPack`**: WCC's `s2Carrier`/`s2Key` lack only `exact_ne` —
  the eval-1 nonvanishing at exact `dv2Supp` grade below the `g8` fence.  True by the
  SAME diagonal-singleton mechanism one level down (`(21,2)` coprime, `8 = 2·4`), but
  the proof needs the C132rp1 `s2Mu3Coeff` gate structure, not the abstract packs.
* **(W-b) the grade dictionary**: `nextSupp (s2Carrier) (s2Key) g16 = 170` from
  `g16_exactGrade` — i.e. `nextSupp = dv3Supp/s2Hgt₄` at the S2 pins (an
  `iInf`-vs-range-inf identification plus the landed `s2Hgt₄_eq_dv3Supp`, `toZ` bridge).
* **(W-c) the root dictionary**: `eval 1 (nextRead (s2Carrier) (s2Key) 170 g16) = 0`
  from `s2Mu4GradedRes_g16 = X + 1` — eval-1 is reindex-invariant, so the WCC
  coefficient dictionary (`s2Mu4Coeff_eq_wcoeff`, private there) transports it.

With (W-a)–(W-c), `liftAtOfRootF1` + `towerPacks` fire at the witness with the tower's
own next slopes (the μ₅ table, `s2Hgt₅`/C136r1).  No weakened statement is offered in
their place. -/

/-! ## §7 — the two adjacent legs (charge 3): honest fences

* **`PrevGrade` at `f′ ≥ 2`** (`LevelSiteBank.prev`, I10SiteCalc): a field of the
  CALCULUS spine (`FGMNCalculus`), vacuous at `f′ = 1` (the keystone genre,
  `levelSiteBank_of_inertia_trivial`).  On the CARRIER spine there is no separate
  `PrevGrade` obligation at any rung: the lattice gate `ℓ ∣ (β − u·J)` is DEFINITIONAL
  in `wcoeff`, and `RungLift.ofRootF1`'s signature carries no `PrevGrade`-genre input —
  the f′ = 1 collapse is machine-visible.  At `f′ ≥ 2` the calculus-side `prev` field
  remains exactly where SCS put it; tying it to a carrier-side statement is part of the
  carrier→calculus spine bridge (the L2E program's remaining leg), not of `RungLift`.
* **the `CarrierReadLaw` tie** (I10LadderRead): its multiplicativity half is exactly
  what the pack machinery exports at EVERY rung — `pushCarrier (nextCarrier R) φ` is a
  `WeightedCarrier`, whose `read_mul` is the `hmul` input of
  `carrierReadLaw_of_mult_agree`.  The remaining halves (`hagree` on the height kernel
  and the peel `tie`) mention the arena/normalizer/node of a `RealizedInput` — they are
  realization-side data, the same spine-bridge leg as above.  Honest fence: no carrier
  read at rungs ≥ 3 is CLAIMED to satisfy the full normal form until the bridge lands. -/

end Uniformity.Density.Tower.I10rl3

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.I10rl3.nextSupp_quot_le
#print axioms Uniformity.Density.Tower.I10rl3.nextSupp_mod_eq
#print axioms Uniformity.Density.Tower.I10rl3.RungLift.ofPrime
#print axioms Uniformity.Density.Tower.I10rl3.nextRead_eq_monomial
#print axioms Uniformity.Density.Tower.I10rl3.RungLift.ofRootF1
#print axioms Uniformity.Density.Tower.I10rl3.exists_prime_factor_nextRead
#print axioms Uniformity.Density.Tower.I10rl3.smallCoprime_of_natDegree_le
#print axioms Uniformity.Density.Tower.I10rl3.liftAtOfRootF1
#print axioms Uniformity.Density.Tower.I10rl3.liftAtOfPrime

end AxCheck
