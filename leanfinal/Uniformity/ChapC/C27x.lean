/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C27
import Uniformity.ChapC.C61
import Uniformity.ChapC.C131p
import Uniformity.ChapB.B32a

/-!
# Uniformity.ChapC.C27x — the RE-SIGNED C.27 (`slot2_exact` + `hx`): the reachable reads landed

**Chapter C, NODE C.27** [theorem], the A-C.10 RE-SIGNED form (leanspec `ChapC.lean`, the
`slot2_exact` axiom with the x-purity guard `hx : IsPure Polynomial.X g F.h F.e₁` added,
2026-08-24).  `Uniformity/ChapC/C27.lean` refutes the OLD unguarded form (`slot2_exact_false`,
`4 = 3` at `(s2Frame, L₀, g₀, C := X)` over `ℤ_[2]`); THIS file is the first proof attempt
against the re-signed form (unit AC15C27, 2026-08-25).

## Status in one line

**The re-signed statement is NOT proved in general; its π-, constant-, and X-reads — two of
C.59's three consumer reads — are PROVED here, unconditionally, at every frame.**  The X-read
is the exact slot the refuter fired on, now discharged WITH the `hx` rider: the end-to-end
vindication that A-C.10's repair is the correct one.  The third consumer read (`C := F.key`)
and the general `C` are BLOCKED on two named missing mechanisms (below).

## What lands

* `Slot2ExactResignedStatement` — the ∀-closure of the RE-SIGNED axiom, byte-frozen as a Prop
  carrier (no axiom, no `sorry`; the signed name stays at the leanspec stub, the
  C.33/C.34/C.61 convention).
* `dv2Hgt_C` — the level-2 slot height of a CONSTANT: `dv2Hgt L (C a) = ℓ • (e₁ • v(a))`,
  every frame, every `a` (including `a = 0`, where both sides are `⊤`).
* `dv2Hgt_C_pi` — the π-pin: `dv2Hgt L (C π) = ℓ·e₁`.
* `dv2Hgt_X` — the level-2 slot height of `X` is `ℓ·h`, every frame.  The `deg key = 1`
  branch reads the key's own constant coefficient through the level-1 purity value law
  (`isPure_addVal_coeff_zero` at `F.hpure`); the `deg key ≥ 2` branch is the direct
  development computation; in both, the `j = 1` slot is dominated via `L.hκ` (`ℓ·D′·h < u`)
  with no development computation at all.
* `dv2Hgt_key` — the level-2 slot height of the FRAME KEY is `u`: the slot HALF of C.59's
  third read, every frame.  This pins the third read's whole remaining gap onto the norm
  side alone.
* `slot2_exact_resigned_const` — **the constant read of the re-signed C.27, PROVED**: the
  signed conclusion at `C := Polynomial.C a`, `a ≠ 0`, from the signed context hypotheses.
  (`hC`/`hC0` are omitted: both are THEOREMS at this instance — `natDegree (C a) = 0 <
  keyDeg₂` by `keyDeg₂_pos`, finiteness by `dv2Hgt_C` — so the statement is strictly
  stronger than the signed instance.)
* `slot2_exact_resigned_pi` — the π-read with the value PINNED: `v = ℓ·e₁`, the cleared
  level-2 value of the uniformizer (C.59's first read).
* `slot2_exact_resigned_X` — **the X-read of the re-signed C.27, PROVED** (C.59's second
  read): `v = ℓ·h`, and the norm side is `norm_adjoinRoot_root` + the purity value law.
  At the refuter's own instance the old form demanded `4 = 3`; with `hx` the demanded
  identity IS `e₁·v(g(0)) = h·deg g`, which is `hx`'s content.
* `self_mem_monicFactors`, `ramLeg_dvd_of_ell_one` — chain-row supply: the signed C.59
  (`ramLeg_dvd`) PROVED on the extra rider `L.ℓ = 1`, via the landed `F.e₁`-half
  (`e1_dvd_ramIndexOf_of_mem_monicFactors`, C61) — the `ℓ = 1` slice of the chain does not
  wait on C.27 at all.

## The precise obstruction (the honest core of this unit's verdict)

The missing read is `C := F.key`: its slot half `dv2Hgt L F.key = u` IS landed below
(`dv2Hgt_key`), but the norm side `(e₁ℓ)·v(N(mk g F.key)) = deg g · u` is not.  Two
mechanisms are absent from the landed corpus, and nothing landed substitutes:

1. **Norm/resultant symmetry** — `v(N_{O[x]/(g)}(Φ′ mod g)) = v(N_{O[x]/(Φ′)}(g mod Φ′))`
   (both are `± Res(g, Φ′)`).  Mathlib has no norm-resultant bridge; B53c's
   `addVal_norm_key_eval` is the analogue ONE level down (order-1 key, Gauss value) and its
   proof route (B53a/B53b span transport) is key-residual-specific.
2. **Ramified level-1 exactness at the frame key** — `v(N_{AdjoinRoot Φ′}(A₀(β))) =
   f₁ · stageHeight(A₀)` for `deg A₀ < D′`: the slope-`h/e₁` analogue of B53b's
   `span_mk_eq_span_algebraMap_pow` (which is the `h = 0`, residually-irreducible case).
   `HasLabel`'s purity then closes the read only when `D′ ∣ deg g` — at `D′ ∤ deg g` the
   level-2 polygon endpoint `dv(A_{n₂})` is not `0` and the classical identity needs the
   fractional endpoint, i.e. the FULL one-side resultant sum (the same mechanism).

For GENERAL `C` (`deg C < D″`) the statement additionally needs label heredity to the monic
factors of `g` — C.35's `BlockFrontier` frontier (`C35_BLOCKED_2026-08-20.md`), whose
purity-of-factors half is the declared cite `fgmn_dv_exact_mul` (C66b) — plus level-2
exactness per factor.  So general-`C` C.27 is STRICTLY ABOVE the `BlockFrontier` frontier,
not below it: the CCUR classification "self-contained norm-computation task" holds only for
the three consumer reads, of which two land here.

## The three mandated checks

1. **Floor-divided degrees are not used**: no proof below reads a degree off a label; the
   X-read's divisibility-free mechanism is the purity EQUATION `e₁·v(g(0)) = h·deg g`.
2. **CONTENT-FREE TYPE check**: the carrier's unguarded parent has a machine-checked FALSE
   instance (`slot2_exact_false`, C27.lean), and the reads proved here instantiate every
   binder; nothing below is `True`-shaped.
3. **INHABITATION**: all binder chains are inhabited by the landed `ℤ_[2]` witnesses
   (`s2Frame`, `L₀`, `g₀` for the context; `hx`'s locus by `F.key` itself via `F.hpure`).
   The reads are stated at explicit `C`'s, not at an abstract locus.

## Status

Zero `sorry`; no new axiom; axiom footprint Lean-core only (AxCheck footer).  No cite.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C27x

open Polynomial IsLocalRing IsDiscreteValuationRing
open Uniformity.Density Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131p

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 0. The RE-SIGNED statement, byte-frozen as a Prop carrier

The ∀-closure of the A-C.10 re-signed `axiom slot2_exact` (leanspec `Leanspec/ChapC.lean`,
NODE C.27).  The only edits are the closure head and `:` → `,` at the end of the hypothesis
block — the C27.lean `Slot2ExactStatement` convention, with the `hx` rider inserted exactly
where the re-sign put it. -/

/-- The ∀-closure of the RE-SIGNED `slot2_exact` (A-C.10, 2026-08-24).  NOT proved and NOT
refuted here: its `C := Polynomial.C a` / `C := X` instances are PROVED below; its
`C := F.key` instance and the general case are open (module docstring, "the precise
obstruction"). -/
def Slot2ExactResignedStatement : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (_hπ : Irreducible π) [Finite (ResidueField O)]
    {g : Polynomial O} (_hg : HasLabel L g) (_hx : IsPure Polynomial.X g F.h F.e₁)
    {C : Polynomial O}
    (_hC : C.natDegree < L.keyDeg₂) (_hC0 : dv2Hgt L C ≠ ⊤),
    ∃ v : ℕ, dv2Hgt L C = (v : ℕ∞) ∧
      (F.e₁ * L.ℓ) * (addVal O (Algebra.norm O (AdjoinRoot.mk g C))).toNat = g.natDegree * v

/-! ## 1. ℕ∞ helper -/

private theorem nsmul_top_of_pos {n : ℕ} (hn : 0 < n) : n • (⊤ : ℕ∞) = ⊤ := by
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ k => rw [succ_nsmul]; exact WithTop.add_top _

/-! ## 2. The slot heights of the read points, at every frame -/

/-- **The level-2 slot height of a constant** is its cleared valuation
`ℓ • (e₁ • v(a))` — at every frame, every level datum, and every `a` (at `a = 0` both
sides are `⊤`). -/
theorem dv2Hgt_C {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) (a : O) :
    dv2Hgt L (Polynomial.C a) = L.ℓ • (F.e₁ • addVal O a) := by
  have hdev : dev F.key (Polynomial.C a) 0 = Polynomial.C a := by
    show (Polynomial.C a) %ₘ F.key = Polynomial.C a
    rw [Polynomial.modByMonic_eq_self_iff F.hmonic]
    exact lt_of_le_of_lt Polynomial.degree_C_le (key_degree_pos F)
  rw [dv2Hgt, dvSupp]
  simp only [Polynomial.natDegree_C, show Finset.range (0 + 1) = {0} from rfl,
    Finset.inf_singleton, dvHgt, hdev, stageHeight_eq_coeff_inf,
    Polynomial.coeff_C_zero]
  simp

/-- The π-pin: `dv2Hgt L (C π) = ℓ·e₁` — the cleared level-2 value of the uniformizer. -/
theorem dv2Hgt_C_pi {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) :
    dv2Hgt L (Polynomial.C π) = ((L.ℓ * F.e₁ : ℕ) : ℕ∞) := by
  rw [dv2Hgt_C, addVal_uniformizer hπ]
  simp [nsmul_eq_mul]

/-- **The level-2 slot height of `X` is `ℓ·h`** — at every frame.  The `j = 1` development
slot is dominated by `L.hκ` (`ℓ·D′·h < u ≤` the slot's weight) with no computation; the
`j = 0` slot is `stageHeight (X %ₘ key)`, which is `h` in both key-degree regimes (at
`deg key = 1` through the key's own purity value law). -/
theorem dv2Hgt_X {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    dv2Hgt L (Polynomial.X : Polynomial O) = ((L.ℓ * F.h : ℕ) : ℕ∞) := by
  -- the `j = 0` slot
  have hslot0 : F.stageHeight (dev F.key (Polynomial.X : Polynomial O) 0) = (F.h : ℕ∞) := by
    rcases Nat.lt_or_ge 1 F.key.natDegree with hgt | hle
    · -- `deg key ≥ 2`: the development coefficient is `X` itself
      have hdev : dev F.key (Polynomial.X : Polynomial O) 0 = Polynomial.X := by
        show (Polynomial.X : Polynomial O) %ₘ F.key = Polynomial.X
        rw [Polynomial.modByMonic_eq_self_iff F.hmonic, Polynomial.degree_X,
          Polynomial.degree_eq_natDegree F.hmonic.ne_zero]
        exact_mod_cast hgt
      rw [hdev, stageHeight_eq_coeff_inf]
      simp only [Polynomial.natDegree_X, show Finset.range (1 + 1) = {0, 1} from rfl,
        Finset.inf_insert, Finset.inf_singleton, Polynomial.coeff_X_zero,
        Polynomial.coeff_X_one, addVal_zero, (addVal O).map_one,
        nsmul_top_of_pos F.he₁, smul_zero]
      simp
    · -- `deg key = 1`: the development coefficient is `−C (key.coeff 0)`, whose valuation
      -- the key's own purity value law reads as `h`
      have h1 : F.key.natDegree = 1 := le_antisymm hle (keyDeg_pos F)
      have hkey : F.key = Polynomial.X + Polynomial.C (F.key.coeff 0) :=
        F.hmonic.eq_X_add_C h1
      have hdev : dev F.key (Polynomial.X : Polynomial O) 0
          = -(Polynomial.C (F.key.coeff 0)) := by
        show (Polynomial.X : Polynomial O) %ₘ F.key = -(Polynomial.C (F.key.coeff 0))
        have hX : (Polynomial.X : Polynomial O)
            = F.key + -(Polynomial.C (F.key.coeff 0)) := by
          nth_rewrite 1 [hkey]
          ring
        rw [hX, Polynomial.add_modByMonic, Polynomial.modByMonic_self F.hmonic, zero_add,
          Polynomial.modByMonic_eq_self_iff F.hmonic]
        have hdegneg : (-(Polynomial.C (F.key.coeff 0)) : Polynomial O).degree ≤ 0 := by
          rw [Polynomial.degree_neg]; exact Polynomial.degree_C_le
        exact lt_of_le_of_lt hdegneg (key_degree_pos F)
      have hval : F.e₁ • addVal O (F.key.coeff 0) = ((F.h : ℕ) : ℕ∞) := by
        have := isPure_addVal_coeff_zero F.hmonic F.hpure
        rwa [h1, Nat.mul_one] at this
      rw [hdev, stageHeight_eq_coeff_inf]
      simp only [Polynomial.natDegree_neg, Polynomial.natDegree_C,
        show Finset.range (0 + 1) = {0} from rfl, Finset.inf_singleton,
        Polynomial.coeff_neg, Polynomial.coeff_C_zero, (addVal O).map_neg, hval]
      simp
  -- `ℓh < u` in `ℕ`, from the above-floor fence `hκ`
  have hlt : L.ℓ * F.h < L.u := by
    have h1 : L.ℓ * F.h ≤ L.ℓ * (F.e₁ * F.f₁) * F.h :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.mul_pos F.he₁ F.hf₁))
    exact lt_of_le_of_lt h1 L.hκ
  -- assemble the two-slot infimum
  rw [dv2Hgt, dvSupp]
  simp only [Polynomial.natDegree_X, show Finset.range (1 + 1) = {0, 1} from rfl,
    Finset.inf_insert, Finset.inf_singleton, dvHgt, hslot0]
  have h0 : L.ℓ • ((F.h : ℕ)  : ℕ∞) + ((L.u : ℕ∞) * ((0 : ℕ) : ℕ∞))
      = ((L.ℓ * F.h : ℕ) : ℕ∞) := by
    simp [nsmul_eq_mul]
  have hge : ((L.ℓ * F.h : ℕ) : ℕ∞)
      ≤ L.ℓ • F.stageHeight (dev F.key (Polynomial.X : Polynomial O) 1)
        + ((L.u : ℕ∞) * ((1 : ℕ) : ℕ∞)) := by
    calc ((L.ℓ * F.h : ℕ) : ℕ∞) ≤ ((L.u : ℕ) : ℕ∞) := by exact_mod_cast hlt.le
      _ = (L.u : ℕ∞) * ((1 : ℕ) : ℕ∞) := by simp
      _ ≤ L.ℓ • F.stageHeight (dev F.key (Polynomial.X : Polynomial O) 1)
          + (L.u : ℕ∞) * ((1 : ℕ) : ℕ∞) := le_add_self
  calc (L.ℓ • ((F.h : ℕ) : ℕ∞) + ((L.u : ℕ∞) * ((0 : ℕ) : ℕ∞)))
        ⊓ (L.ℓ • F.stageHeight (dev F.key (Polynomial.X : Polynomial O) 1)
          + ((L.u : ℕ∞) * ((1 : ℕ) : ℕ∞)))
      = ((L.ℓ * F.h : ℕ) : ℕ∞)
        ⊓ (L.ℓ • F.stageHeight (dev F.key (Polynomial.X : Polynomial O) 1)
          + ((L.u : ℕ∞) * ((1 : ℕ) : ℕ∞))) := by rw [h0]
    _ = ((L.ℓ * F.h : ℕ) : ℕ∞) := inf_eq_left.2 hge

/-- **The level-2 slot height of the frame key is `u`** — the slot HALF of C.59's third
consumer read (`C := F.key`), at every frame.  The key's own development is
`0 + 1·Φ′` (`dev_mul_pow` at `t = 1`), so the `j = 1` slot contributes `ℓ·0 + u·1 = u`,
the `j = 0` slot is `⊤`, and every `j ≥ 1` slot weighs at least `u·j ≥ u`.  What remains
missing for the full `F.key`-read is ONLY the norm side (module docstring, obstruction
mechanisms 1–2). -/
theorem dv2Hgt_key {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin) :
    dv2Hgt L F.key = ((L.u : ℕ) : ℕ∞) := by
  have hone : (1 : Polynomial O) * F.key ^ 1 = F.key := by ring
  have hdev0 : dev F.key F.key 0 = 0 := by
    have h := dev_mul_pow_of_lt F.hmonic 1 1 0 Nat.zero_lt_one
    rwa [hone] at h
  have hdev1 : dev F.key F.key 1 = 1 := by
    have h := dev_mul_pow F.hmonic 1 1 0
    rw [hone] at h
    have h1 : dev F.key (1 : Polynomial O) 0 = 1 := by
      show (1 : Polynomial O) %ₘ F.key = 1
      rw [Polynomial.modByMonic_eq_self_iff F.hmonic, Polynomial.degree_one]
      exact key_degree_pos F
    rw [h1] at h
    exact h
  have hsh1 : F.stageHeight (1 : Polynomial O) = 0 := by
    rw [stageHeight_eq_coeff_inf]
    simp
  rw [dv2Hgt, dvSupp]
  refine le_antisymm ?_ ?_
  · -- the infimum is at most the `j = 1` slot, which is exactly `u`
    have hmem : (1 : ℕ) ∈ Finset.range (F.key.natDegree + 1) := by
      rw [Finset.mem_range]
      have := keyDeg_pos F
      omega
    refine le_trans (Finset.inf_le hmem) ?_
    rw [dvHgt, hdev1, hsh1, smul_zero, zero_add]
    simp
  · -- every slot weighs at least `u`
    refine Finset.le_inf fun j hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [dvHgt, hdev0, KeyFrame.stageHeight, suppVal_zero_eq_top F.he₁,
        nsmul_top_of_pos L.hℓ]
      simp
    · calc ((L.u : ℕ) : ℕ∞) = (L.u : ℕ∞) * ((1 : ℕ) : ℕ∞) := by simp
        _ ≤ (L.u : ℕ∞) * ((j : ℕ) : ℕ∞) := by
            refine mul_le_mul' le_rfl ?_
            exact_mod_cast hjpos
        _ ≤ L.ℓ • dvHgt F F.key j + (L.u : ℕ∞) * ((j : ℕ) : ℕ∞) := le_add_self

/-! ## 3. The reachable reads of the RE-SIGNED C.27, PROVED

Each is the signed conclusion at an explicit `C`, from the signed context hypotheses
(`hπ`/`[Finite (ResidueField O)]` carried for signature fidelity; the norm computations do
not consume them).  `hC`/`hC0` are omitted where they are theorems at the instance. -/

/-- **The CONSTANT read of the re-signed C.27, PROVED** (`C := Polynomial.C a`, `a ≠ 0`).
The norm of a constant is `a ^ deg g` (`Algebra.norm_algebraMap` at the power basis), and
the slot height is `dv2Hgt_C`; the signed identity is then `ℕ`-ring arithmetic.  `hC` and
`hC0` hold at this instance (`natDegree_C` + `keyDeg₂_pos`; `dv2Hgt_C` + `ha`), so this is
the full signed instance. -/
theorem slot2_exact_resigned_const {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (_hπ : Irreducible π) [Finite (ResidueField O)]
    {g : Polynomial O} (hg : HasLabel L g) (_hx : IsPure Polynomial.X g F.h F.e₁)
    {a : O} (ha : a ≠ 0) :
    ∃ v : ℕ, dv2Hgt L (Polynomial.C a) = (v : ℕ∞) ∧
      (F.e₁ * L.ℓ) *
        (addVal O (Algebra.norm O (AdjoinRoot.mk g (Polynomial.C a)))).toNat
        = g.natDegree * v := by
  classical
  obtain ⟨va, hva⟩ := ENat.ne_top_iff_exists.1 (addVal_eq_top_iff.not.2 ha)
  refine ⟨L.ℓ * (F.e₁ * va), ?_, ?_⟩
  · rw [dv2Hgt_C, ← hva]
    simp [nsmul_eq_mul]
  · haveI : Module.Free O (AdjoinRoot g) :=
      Module.Free.of_basis (AdjoinRoot.powerBasis' hg.1).basis
    haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg.1).finite
    have hrk : Module.finrank O (AdjoinRoot g) = g.natDegree := by
      rw [(AdjoinRoot.powerBasis' hg.1).finrank]; rfl
    have hmk : AdjoinRoot.mk g (Polynomial.C a) = algebraMap O (AdjoinRoot g) a := by
      rw [AdjoinRoot.algebraMap_eq]; rfl
    rw [hmk, Algebra.norm_algebraMap, hrk, addVal_pow, ← hva,
      show g.natDegree • ((va : ℕ) : ℕ∞) = ((g.natDegree * va : ℕ) : ℕ∞) by
        simp [nsmul_eq_mul],
      ENat.toNat_coe]
    ring

/-- **The π-read of the re-signed C.27, with the value PINNED**: `v = ℓ·e₁`, the cleared
level-2 value of the uniformizer — C.59's first consumer read. -/
theorem slot2_exact_resigned_pi {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [Finite (ResidueField O)]
    {g : Polynomial O} (hg : HasLabel L g) (hx : IsPure Polynomial.X g F.h F.e₁) :
    dv2Hgt L (Polynomial.C π) = ((L.ℓ * F.e₁ : ℕ) : ℕ∞) ∧
      (F.e₁ * L.ℓ) *
        (addVal O (Algebra.norm O (AdjoinRoot.mk g (Polynomial.C π)))).toNat
        = g.natDegree * (L.ℓ * F.e₁) := by
  obtain ⟨v, hv, hnorm⟩ := slot2_exact_resigned_const L hπ hg hx hπ.ne_zero
  have hpin' : ((v : ℕ) : ℕ∞) = ((L.ℓ * F.e₁ : ℕ) : ℕ∞) := by
    rw [← hv, dv2Hgt_C_pi L hπ]
  have hveq : v = L.ℓ * F.e₁ := by exact_mod_cast hpin'
  exact ⟨dv2Hgt_C_pi L hπ, hveq ▸ hnorm⟩

/-- **The X-read of the re-signed C.27, PROVED** — the exact slot `slot2_exact_false`
(C27.lean) fired on, now discharged WITH the `hx` rider: `v = ℓ·h` (`dv2Hgt_X`), the norm
is `±g(0)` (`norm_adjoinRoot_root`), and the signed identity IS the level-1 purity value
law `e₁·v(g(0)) = h·deg g` (`isPure_addVal_coeff_zero` at `hx`) — the content `HasLabel`
alone does not supply and the old refutation exploited.  C.59's second consumer read. -/
theorem slot2_exact_resigned_X {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (_hπ : Irreducible π) [Finite (ResidueField O)]
    {g : Polynomial O} (hg : HasLabel L g) (hx : IsPure Polynomial.X g F.h F.e₁) :
    ∃ v : ℕ, dv2Hgt L (Polynomial.X : Polynomial O) = (v : ℕ∞) ∧
      (F.e₁ * L.ℓ) *
        (addVal O (Algebra.norm O (AdjoinRoot.mk g (Polynomial.X : Polynomial O)))).toNat
        = g.natDegree * v := by
  classical
  have hval : F.e₁ • addVal O (g.coeff 0) = ((F.h * g.natDegree : ℕ) : ℕ∞) :=
    isPure_addVal_coeff_zero hg.1 hx
  have hne : addVal O (g.coeff 0) ≠ ⊤ := by
    intro htop
    rw [htop, nsmul_top_of_pos F.he₁] at hval
    exact (ENat.coe_ne_top _) hval.symm
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 hne
  have hnat : F.e₁ * c = F.h * g.natDegree := by
    have hcast : ((F.e₁ * c : ℕ) : ℕ∞) = ((F.h * g.natDegree : ℕ) : ℕ∞) := by
      rw [← hval, ← hc]
      simp [nsmul_eq_mul]
    exact_mod_cast hcast
  refine ⟨L.ℓ * F.h, dv2Hgt_X L, ?_⟩
  have hmk : AdjoinRoot.mk g (Polynomial.X : Polynomial O) = AdjoinRoot.root g := rfl
  rw [hmk, norm_adjoinRoot_root hg.1 hg.2.1, (addVal O).map_mul,
    addVal_eq_zero_iff.2 (isUnit_one.neg.pow g.natDegree), zero_add, ← hc, ENat.toNat_coe]
  calc (F.e₁ * L.ℓ) * c = L.ℓ * (F.e₁ * c) := by ring
    _ = L.ℓ * (F.h * g.natDegree) := by rw [hnat]
    _ = g.natDegree * (L.ℓ * F.h) := by ring

/-! ## 4. Chain-row supply: the signed C.59 (`ramLeg_dvd`) PROVED on the rider `L.ℓ = 1`

C.59 is the C.27 chain's first consumer (its route is C.27's three cleared-value reads at
`π`/`X`/`F.key` — `C61_BLOCKED_2026-08-20.md`).  At `L.ℓ = 1` its conclusion is the
`F.e₁`-half alone, which C61 landed from `hx` through CHAP-B with no C.27 input
(`e1_dvd_ramIndexOf_of_mem_monicFactors`); the missing `F.key`-read is needed only for the
`L.ℓ`-half.  So the `ℓ = 1` slice of the whole 6-row chain does not wait on C.27. -/

/-- A monic irreducible polynomial is a member of its own monic factorization. -/
theorem self_mem_monicFactors {g : Polynomial O} (hg : g.Monic) (hirr : Irreducible g) :
    g ∈ monicFactors g := by
  have h : monicFactors g = {g} :=
    monicFactors_eq ⟨fun p hp => by
      rw [Multiset.mem_singleton] at hp; subst hp; exact ⟨hg, hirr⟩,
      Multiset.prod_singleton g⟩
  rw [h]
  exact Multiset.mem_singleton_self g

/-- **The signed C.59 (`ramLeg_dvd`) on the extra rider `L.ℓ = 1`** — the signed binder row
(`hg`/`hirr`/`hlab`/`hx`, leanspec NODE C.59) plus the rider; the conclusion is the signed
conclusion verbatim.  No C.27 input: the `e₁`-half is C61's landed
`e1_dvd_ramIndexOf_of_mem_monicFactors` at `g ∈ monicFactors g`. -/
theorem ramLeg_dvd_of_ell_one {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (hg : g.Monic) (hirr : Irreducible g) (_hlab : HasLabel L g)
    (hx : IsPure Polynomial.X g F.h F.e₁) (hℓ : L.ℓ = 1) :
    (F.e₁ * L.ℓ) ∣ ramIndexOf g := by
  rw [hℓ, Nat.mul_one]
  exact e1_dvd_ramIndexOf_of_mem_monicFactors hπ hg hx (self_mem_monicFactors hg hirr)

end Uniformity.Density.Tower.C27x

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C27x.Slot2ExactResignedStatement
#print axioms Uniformity.Density.Tower.C27x.dv2Hgt_C
#print axioms Uniformity.Density.Tower.C27x.dv2Hgt_C_pi
#print axioms Uniformity.Density.Tower.C27x.dv2Hgt_X
#print axioms Uniformity.Density.Tower.C27x.dv2Hgt_key
#print axioms Uniformity.Density.Tower.C27x.slot2_exact_resigned_const
#print axioms Uniformity.Density.Tower.C27x.slot2_exact_resigned_pi
#print axioms Uniformity.Density.Tower.C27x.slot2_exact_resigned_X
#print axioms Uniformity.Density.Tower.C27x.self_mem_monicFactors
#print axioms Uniformity.Density.Tower.C27x.ramLeg_dvd_of_ell_one

end AxCheck
