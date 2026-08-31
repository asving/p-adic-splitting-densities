/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.I10CExport

/-!
# Uniformity.ChapI.I10IfaceCore — UNIT IEC: `IfaceExportedCore` DISCHARGED (CEX's R1)
[IEC 2026-08-31]

**Unit IEC** — the windows engine over E.11's `ladderSuppVal`/`onLadderSide`, and the
discharge of CEX's export core.  CEX (`I10CExport.lean`) typed the contentful C-to-E
export relation `IfaceExportedCore B I` (every side of `I` a genuine two-abscissa argmin
side of `B.devHgt`, `I.len` = the side's extremal window width) and left R1 open:
inhabit it.  This file inhabits it.

## What is PROVED (charge 2)

* **The windows engine** (§1–§4, all Lean-core, fresh — the corpus's other hull machinery
  lives on chapter-B/C height types; only E13's endpoint facts are reused):
  `sideArg`/`winMin`/`winMax` (the extremal argmin window reads, `mem_sideArg` ↔ E.11's
  `onLadderSide`); the `WithTop ℤ → ℤ` transfer kit; the LOCAL side laws `winLen_dvd`
  (two-point equation + coprimality ⟹ `ℓ ∣ width`) and `side_node_of_steep` (see below);
  ★ `peel_step` + ★ `tiles_of_entry` — the right-to-left peel: below any hull-supported
  right endpoint, finitely many coprime slope pairs' genuine windows tile `[0, k]`
  exactly.  NOTE (machine-caught): the peel and the tiling need NO steepness — descent
  is forced by the entry window's own strictness.
* **`SteepBlock B`** — the ONE block-local law the discharge needs:
  `∀ j < μ, (μ−j)·T < devHgt j` (the development heights clear the slope-`T` line through
  the monic top strictly).  It enters at exactly two points: the top entry
  (`winMin_zero_one`: the flat pair `(0,1)` pins the argmin to `μ`) and the node bound
  (`side_node_of_steep`: every genuine side has `ℓ·T < u` — no hull chaining, purely
  local from the right endpoint's argmin property against abscissa `μ`).
* ★ **`he7aPackageExported_of_steep : SteepBlock B → HE7APackageExported C B`** — CEX's
  R1 discharged at EVERY (STEEP) pair, generic in `(C, B)`: the tiled windows give
  `sides`/`len`/`hlen_sum = μ` (the genuinely-arising fields); the residual/count fields
  are filled synthetically at the CEX pattern, legal by `winLen_dvd` (R2, the
  full-strength residual clauses, stays open exactly as CEX scoped it).
* **Rigidity/redundancy teeth**: `IfaceExportedCore.win_forced` (the core's extremality
  clause makes the witness pair UNIQUE — `len` is pinned to `winMax − winMin`),
  `exported_node_forced` (at a (STEEP) block the export relation REPROVES E.12's
  `hside_node` on any consumer interface), `exported_len_dvd` (structure for the E.57
  funnel).
* **Arising wrappers**: `exists_realizedExport_of_steep` (LB1G's demanded
  `RealizedRungInterfaceExport` genre INHABITED at (STEEP) realized blocks);
  ★ `ifaceExportedCore_of_arising` (the charge's named target, at its honest minimal
  restriction — the config binder is deliberately UNCONSUMED, see remainder);
  `LadderPackageExportedSupplier` (R3's target shape) and
  ★ `ladderPackageExportedSupplier_of_steep` (the steep supplier fires it at every degree).
* **GATE (§7, executed)**: a full concrete `SlotCarrier`/`BlockData` over `ℚ`
  (`Φ = X`, `F = X² + 1`, `μ = 2`, `T = 0`, all ten carrier laws discharged) is proved
  (STEEP) and the discharge FIRES on it — the premise is not provably empty, and the
  peel's `⊤`-branch is exercised (`A 1 = 0`).

## Honest remainder (charge 3) — named, minimal

1. **R1′ = `LadderSteepSupplier`** (OPEN): prove `SteepBlock B` at arising pairs.  This
   is the F1 `BlockFrontier` frontier (`BLOCKERS_PLAN_2026-08-26.md` — genuinely new
   mathematics), scoped by this unit from "build the whole exporter" (the old XL pricing)
   down to ONE pointwise height inequality.  Nothing landed pins it: `BlockViewEq` pins
   the block's data fields, and `CanonicalThresholdAt` is the (WINDOW) law about the
   KEY's height at the point, not the development coefficients'.
2. **R2** (unchanged from CEX): the full-strength export clauses (residual factorizations
   through `C.dig`, pinned counts, rank carrier).
3. **The lb1 leg** — ⚠ PROMINENT CORRECTION of the unit brief: post-IEC the lb1 twin does
   NOT rest on the owner re-sign alone.  `PartitionLeg I` (E57p) demands a genuine
   coprime factorization of `B.F` per residual class (HE7.96(a), C.63/C.69 content) — the
   polygon engine cannot produce it.  Honest boundary: lb1 = `hpart` (partition legs at
   core-exported triggering interfaces; this file's forced-window lemmas are the
   structure its constructor will consume) + R3.  The PACKAGE leg = R1′ + R3 alone.
   Joint wiring pin: `exportedTwins_of_steep_partitionLegs`.
4. **Owner amendments (flagged, NOT enacted)**: re-signing the capstone's `package` leg
   to `LadderPackageExportedSupplier` and `lb1` to the exported twin (CEX §3 / LDR §3 —
   R3).

## Trust boundary

NEW STATEMENTS (standing review): `SteepBlock`, `LadderSteepSupplier`,
`LadderPackageExportedSupplier` (+ the engine reads `sideVal`/`sideArg`/`winMin`/`winMax`
and the gate artifacts `gateSlot`/`gateBlock` — definitional, no signed name touched).
Cite ledger: **EMPTY** — Lean core over the landed corpus; the `#print axioms` footer is
the audit.  Zero `sorry`, zero new axiom.  Verdict: `runs/wave-c/verdict_IEC.md`.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC5

open Uniformity.Density
open Uniformity.Density.Tower

/-! ## §1 The argmin-window reads off `B.devHgt` -/

section Windows

universe uO uK

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K]
variable {C : Ladder.SlotCarrier O K}

/-- The support-value of abscissa `j` against the slope pair `p = (u, ℓ)` — the raw
expression E.11's `onLadderSide` and CEX's `IfaceExportedCore` read. -/
noncomputable def sideVal (B : Ladder.BlockData C) (p : ℕ × ℕ) (j : ℕ) : WithTop ℤ :=
  p.2 • B.devHgt j + ((j * p.1 : ℕ) : WithTop ℤ)

/-- The argmin abscissas of the slope pair `p` on the block's development ladder. -/
noncomputable def sideArg (B : Ladder.BlockData C) (p : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (B.μ + 1)).filter fun j =>
    sideVal B p j = Ladder.ladderSuppVal B.devHgt p.1 p.2 B.μ

theorem mem_sideArg {B : Ladder.BlockData C} {p : ℕ × ℕ} {j : ℕ} :
    j ∈ sideArg B p ↔ Ladder.onLadderSide B.devHgt p.1 p.2 B.μ j := by
  simp [sideArg, sideVal, Ladder.onLadderSide]

theorem sideArg_nonempty (B : Ladder.BlockData C) (p : ℕ × ℕ) :
    (sideArg B p).Nonempty := by
  obtain ⟨j, hj, hval⟩ := Finset.exists_mem_eq_inf (Finset.range (B.μ + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun j => p.2 • B.devHgt j + ((j * p.1 : ℕ) : WithTop ℤ))
  exact ⟨j, Finset.mem_filter.mpr ⟨hj, hval.symm⟩⟩

/-- The left end of the extremal argmin window. -/
noncomputable def winMin (B : Ladder.BlockData C) (p : ℕ × ℕ) : ℕ :=
  (sideArg B p).min' (sideArg_nonempty B p)

/-- The right end of the extremal argmin window. -/
noncomputable def winMax (B : Ladder.BlockData C) (p : ℕ × ℕ) : ℕ :=
  (sideArg B p).max' (sideArg_nonempty B p)

theorem winMin_mem (B : Ladder.BlockData C) (p : ℕ × ℕ) : winMin B p ∈ sideArg B p :=
  Finset.min'_mem _ _

theorem winMax_mem (B : Ladder.BlockData C) (p : ℕ × ℕ) : winMax B p ∈ sideArg B p :=
  Finset.max'_mem _ _

theorem winMin_onSide (B : Ladder.BlockData C) (p : ℕ × ℕ) :
    Ladder.onLadderSide B.devHgt p.1 p.2 B.μ (winMin B p) :=
  mem_sideArg.mp (winMin_mem B p)

theorem winMax_onSide (B : Ladder.BlockData C) (p : ℕ × ℕ) :
    Ladder.onLadderSide B.devHgt p.1 p.2 B.μ (winMax B p) :=
  mem_sideArg.mp (winMax_mem B p)

theorem winMin_le {B : Ladder.BlockData C} {p : ℕ × ℕ} {j : ℕ}
    (hj : Ladder.onLadderSide B.devHgt p.1 p.2 B.μ j) : winMin B p ≤ j :=
  Finset.min'_le _ _ (mem_sideArg.mpr hj)

theorem le_winMax {B : Ladder.BlockData C} {p : ℕ × ℕ} {j : ℕ}
    (hj : Ladder.onLadderSide B.devHgt p.1 p.2 B.μ j) : j ≤ winMax B p :=
  Finset.le_max' _ _ (mem_sideArg.mpr hj)

theorem winMax_le_mu (B : Ladder.BlockData C) (p : ℕ × ℕ) : winMax B p ≤ B.μ :=
  (winMax_onSide B p).1

theorem winMin_le_mu (B : Ladder.BlockData C) (p : ℕ × ℕ) : winMin B p ≤ B.μ :=
  (winMin_onSide B p).1

end Windows

/-! ## §2 Finiteness and transfer to `ℤ` -/

section Transfer

universe uO uK

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K]
variable {C : Ladder.SlotCarrier O K}

theorem nsmul_top {n : ℕ} (hn : n ≠ 0) : n • (⊤ : WithTop ℤ) = ⊤ := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m => rw [succ_nsmul, add_top]

theorem nsmul_coe (n : ℕ) (a : ℤ) :
    n • ((a : WithTop ℤ)) = (((n : ℤ) * a : ℤ) : WithTop ℤ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [succ_nsmul, ih, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

theorem exists_coe_of_ne_top {x : WithTop ℤ} (hx : x ≠ ⊤) :
    ∃ a : ℤ, x = (a : WithTop ℤ) := by
  lift x to ℤ using hx
  exact ⟨x, rfl⟩

/-- The block's monic top: `devHgt μ = 0`. -/
theorem devHgt_mu (B : Ladder.BlockData C) : B.devHgt B.μ = 0 := by
  simp [Ladder.BlockData.devHgt]

/-- The `(KEY-FREE)` shadow: `devHgt 0` is finite (E.13's gate fact, restated). -/
theorem devHgt_zero_ne_top (B : Ladder.BlockData C) : B.devHgt 0 ≠ ⊤ := by
  have hμ := B.hμ
  have h0 : B.devHgt 0 = C.hgt (B.A 0) := by
    have h1 : ¬ ((0 : ℕ) = B.μ) := by omega
    have h2 : (0 : ℕ) < B.μ := by omega
    simp [Ladder.BlockData.devHgt, h1, h2]
  rw [h0]
  exact C.hgt_ne_top (B.A 0) B.hA0 (B.hdegA 0 hμ)

/-- The support value is finite (E.13(iii), restated without `[IsDomain O]`). -/
theorem suppVal_ne_top (B : Ladder.BlockData C) (u ℓ : ℕ) :
    Ladder.ladderSuppVal B.devHgt u ℓ B.μ ≠ ⊤ := by
  have hmem : B.μ ∈ Finset.range (B.μ + 1) := Finset.self_mem_range_succ B.μ
  have hle : Ladder.ladderSuppVal B.devHgt u ℓ B.μ
      ≤ ℓ • B.devHgt B.μ + ((B.μ * u : ℕ) : WithTop ℤ) := Finset.inf_le hmem
  rw [devHgt_mu, smul_zero, zero_add] at hle
  exact ne_top_of_le_ne_top (by simp) hle

/-- Transfer: `sideVal` at a finite height is the corresponding `ℤ` value. -/
theorem sideVal_coe {B : Ladder.BlockData C} {p : ℕ × ℕ} {j : ℕ} {a : ℤ}
    (ha : B.devHgt j = (a : WithTop ℤ)) :
    sideVal B p j = (((p.2 : ℤ) * a + (j : ℤ) * (p.1 : ℤ) : ℤ) : WithTop ℤ) := by
  have h1 : ((j * p.1 : ℕ) : WithTop ℤ) = (((j : ℤ) * (p.1 : ℤ) : ℤ) : WithTop ℤ) := by
    rw [← WithTop.coe_natCast (α := ℤ)]
    norm_cast
  rw [sideVal, ha, nsmul_coe, h1, ← WithTop.coe_add]

/-- `sideVal` at a `⊤` height with `1 ≤ ℓ` is `⊤`. -/
theorem sideVal_top {B : Ladder.BlockData C} {p : ℕ × ℕ} (hℓ : 1 ≤ p.2) {j : ℕ}
    (ha : B.devHgt j = ⊤) : sideVal B p j = ⊤ := by
  rw [sideVal, ha, nsmul_top (by omega), top_add]

/-- An argmin abscissa of a slope pair with `1 ≤ ℓ` has finite height. -/
theorem devHgt_int_of_arg {B : Ladder.BlockData C} {p : ℕ × ℕ} (hℓ : 1 ≤ p.2) {j : ℕ}
    (hj : j ∈ sideArg B p) : ∃ a : ℤ, B.devHgt j = (a : WithTop ℤ) := by
  by_cases htop : B.devHgt j = ⊤
  · exfalso
    have hval : sideVal B p j = Ladder.ladderSuppVal B.devHgt p.1 p.2 B.μ :=
      (Finset.mem_filter.mp hj).2
    rw [sideVal_top hℓ htop] at hval
    exact suppVal_ne_top B p.1 p.2 hval.symm
  · exact exists_coe_of_ne_top htop

/-- The support value is the `inf`: it bounds every abscissa's value. -/
theorem suppVal_le {B : Ladder.BlockData C} (p : ℕ × ℕ) {m : ℕ} (hm : m ≤ B.μ) :
    Ladder.ladderSuppVal B.devHgt p.1 p.2 B.μ ≤ sideVal B p m := by
  rw [Ladder.ladderSuppVal]
  exact Finset.inf_le (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))

/-- Argmin values dominate: an argmin's value is `≤` the value at any abscissa `≤ μ`. -/
theorem sideVal_arg_le {B : Ladder.BlockData C} {p : ℕ × ℕ} {j : ℕ}
    (hj : j ∈ sideArg B p) {m : ℕ} (hm : m ≤ B.μ) : sideVal B p j ≤ sideVal B p m := by
  rw [(Finset.mem_filter.mp hj).2]
  exact suppVal_le p hm

/-- Membership from domination: if `k ≤ μ` and `sideVal k` is `≤` every value, `k` is argmin. -/
theorem mem_sideArg_of_forall_le {B : Ladder.BlockData C} {p : ℕ × ℕ} {k : ℕ}
    (hk : k ≤ B.μ) (h : ∀ m ≤ B.μ, sideVal B p k ≤ sideVal B p m) :
    k ∈ sideArg B p := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hk), ?_⟩
  refine le_antisymm ?_ (suppVal_le p hk)
  rw [Ladder.ladderSuppVal]
  refine Finset.le_inf fun m hm => ?_
  exact h m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))

end Transfer

/-! ## §3 The steepness law and the local side laws -/

section Steep

universe uO uK

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K]
variable {C : Ladder.SlotCarrier O K}

/-- **`SteepBlock B` — the (STEEP) law**: every development height clears the threshold
line through `(μ, 0)` of slope `T` strictly: `(μ − j)·T < devHgt j` for `j < μ`.
This is the block-local residue of the F1 frontier at arising pairs (see the header).
NEW STATEMENT (review). -/
def SteepBlock (B : Ladder.BlockData C) : Prop :=
  ∀ j < B.μ, (((B.μ - j) * B.T : ℕ) : WithTop ℤ) < B.devHgt j

/-- LOCAL LAW 1 (two-point divisibility): the extremal window width of a coprime slope
pair is divisible by the denominator `ℓ`. -/
theorem winLen_dvd {B : Ladder.BlockData C} {p : ℕ × ℕ}
    (hcop : Nat.Coprime p.1 p.2) (hℓ : 1 ≤ p.2) :
    p.2 ∣ (winMax B p - winMin B p) := by
  obtain ⟨a, ha⟩ := devHgt_int_of_arg hℓ (winMin_mem B p)
  obtain ⟨b, hb⟩ := devHgt_int_of_arg hℓ (winMax_mem B p)
  have hval : sideVal B p (winMin B p) = sideVal B p (winMax B p) := by
    rw [(Finset.mem_filter.mp (winMin_mem B p)).2, (Finset.mem_filter.mp (winMax_mem B p)).2]
  rw [sideVal_coe ha, sideVal_coe hb] at hval
  have hZ := WithTop.coe_injective hval
  have hle : winMin B p ≤ winMax B p := Finset.min'_le _ _ (winMax_mem B p)
  have hdvd : (p.2 : ℤ) ∣ (((winMax B p - winMin B p) * p.1 : ℕ) : ℤ) := by
    refine ⟨a - b, ?_⟩
    push_cast
    rw [Nat.cast_sub hle]
    linarith [hZ]
  have hdvd' : p.2 ∣ (winMax B p - winMin B p) * p.1 := by exact_mod_cast hdvd
  exact Nat.Coprime.dvd_of_dvd_mul_right hcop.symm hdvd'

/-- LOCAL LAW 2 (the node bound): under (STEEP), every genuine two-abscissa side clears
the threshold: `ℓ·T < u`.  No hull chaining: the right endpoint's argmin property against
abscissa `μ` plus (STEEP) at the left endpoint suffice. -/
theorem side_node_of_steep {B : Ladder.BlockData C} (hsteep : SteepBlock B) {p : ℕ × ℕ}
    (hℓ : 1 ≤ p.2) (hlt : winMin B p < winMax B p) : p.2 * B.T < p.1 := by
  obtain ⟨a, ha⟩ := devHgt_int_of_arg hℓ (winMin_mem B p)
  obtain ⟨b, hb⟩ := devHgt_int_of_arg hℓ (winMax_mem B p)
  have hkμ : winMax B p ≤ B.μ := winMax_le_mu B p
  have hjμ : winMin B p < B.μ := lt_of_lt_of_le hlt hkμ
  -- two-point equality at the window ends
  have hval : sideVal B p (winMin B p) = sideVal B p (winMax B p) := by
    rw [(Finset.mem_filter.mp (winMin_mem B p)).2, (Finset.mem_filter.mp (winMax_mem B p)).2]
  rw [sideVal_coe ha, sideVal_coe hb] at hval
  have hZ := WithTop.coe_injective hval
  -- the right end's argmin property against the monic top `μ`
  have hμval : sideVal B p (winMax B p) ≤ sideVal B p B.μ :=
    sideVal_arg_le (winMax_mem B p) le_rfl
  have hμcoe : B.devHgt B.μ = ((0 : ℤ) : WithTop ℤ) := by rw [devHgt_mu]; rfl
  rw [sideVal_coe hb, sideVal_coe hμcoe] at hμval
  have hZ2 := WithTop.coe_le_coe.mp hμval
  -- (STEEP) at the left end
  have hst := hsteep (winMin B p) hjμ
  rw [ha] at hst
  rw [← WithTop.coe_natCast (α := ℤ)] at hst
  have hZ3 : (((B.μ - winMin B p) * B.T : ℕ) : ℤ) < a := WithTop.coe_lt_coe.mp hst
  have hZ3' : ((B.μ : ℤ) - (winMin B p : ℤ)) * (B.T : ℤ) < a := by
    rw [← Nat.cast_sub hjμ.le]
    exact_mod_cast hZ3
  -- integer arithmetic: `ℓ·a ≤ (μ−j)·u` and `ℓ·(μ−j)·T < ℓ·a` cancel to `ℓT < u`
  have hp2 : (0 : ℤ) < (p.2 : ℤ) := by exact_mod_cast hℓ
  have hμj : (0 : ℤ) < (B.μ : ℤ) - (winMin B p : ℤ) := by omega
  have h4 : (p.2 : ℤ) * a ≤ ((B.μ : ℤ) - (winMin B p : ℤ)) * (p.1 : ℤ) := by
    nlinarith [hZ, hZ2]
  have h5a : (p.2 : ℤ) * (((B.μ : ℤ) - (winMin B p : ℤ)) * (B.T : ℤ)) < (p.2 : ℤ) * a :=
    mul_lt_mul_of_pos_left hZ3' hp2
  have h5 : ((B.μ : ℤ) - (winMin B p : ℤ)) * ((p.2 : ℤ) * (B.T : ℤ))
      < ((B.μ : ℤ) - (winMin B p : ℤ)) * (p.1 : ℤ) := by nlinarith [h4, h5a]
  have hgoal : (p.2 : ℤ) * (B.T : ℤ) < (p.1 : ℤ) := lt_of_mul_lt_mul_left h5 hμj.le
  exact_mod_cast hgoal

end Steep

/-! ## §4 The peel recursion: tiling `[0, μ]` by genuine argmin windows -/

section Peel

universe uO uK

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K]
variable {C : Ladder.SlotCarrier O K}

/-- **The peel step**: at a hull-supported right endpoint `k > 0` there is a coprime slope
pair whose extremal window ends exactly at `k` and starts strictly left of it.
NOTE: (STEEP) is NOT needed here — the descent comes from the entry window's own
strictness; (STEEP) enters only at the top entry (`winMin_zero_one`) and the node bound
(`side_node_of_steep`). -/
theorem peel_step {B : Ladder.BlockData C} {k : ℕ} (hk : 0 < k)
    {u₀ ℓ₀ : ℕ} (hℓ₀ : 1 ≤ ℓ₀) (hwm : winMin B (u₀, ℓ₀) = k) :
    ∃ u ℓ : ℕ, Nat.Coprime u ℓ ∧ 1 ≤ ℓ ∧ winMin B (u, ℓ) < k ∧ winMax B (u, ℓ) = k := by
  classical
  have hkmem : k ∈ sideArg B (u₀, ℓ₀) := hwm ▸ winMin_mem B (u₀, ℓ₀)
  have hkμ : k ≤ B.μ := hwm ▸ winMin_le_mu B (u₀, ℓ₀)
  obtain ⟨b, hb⟩ := devHgt_int_of_arg hℓ₀ hkmem
  -- the finite abscissas strictly left of `k`, and the shallowest-slope minimizer among them
  have hJne : ((Finset.range k).filter (fun j => B.devHgt j ≠ ⊤)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, devHgt_zero_ne_top B⟩⟩
  obtain ⟨j', hj'J, hmin⟩ := Finset.exists_min_image _
    (fun j => ((WithTop.untopD 0 (B.devHgt j) - b : ℤ) : ℚ) / ((k - j : ℕ) : ℚ)) hJne
  have hj'k : j' < k := Finset.mem_range.mp (Finset.mem_filter.mp hj'J).1
  have hj'μ : j' ≤ B.μ := le_trans hj'k.le hkμ
  obtain ⟨a', ha'⟩ := exists_coe_of_ne_top (Finset.mem_filter.mp hj'J).2
  -- j' is strictly left of the entry window, so its entry value is strictly worse
  have hstrict : sideVal B (u₀, ℓ₀) k < sideVal B (u₀, ℓ₀) j' := by
    have hle : Ladder.ladderSuppVal B.devHgt u₀ ℓ₀ B.μ ≤ sideVal B (u₀, ℓ₀) j' :=
      suppVal_le _ hj'μ
    have hne : sideVal B (u₀, ℓ₀) j' ≠ Ladder.ladderSuppVal B.devHgt u₀ ℓ₀ B.μ := by
      intro heq
      have hmem : j' ∈ sideArg B (u₀, ℓ₀) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj'μ), heq⟩
      have h2 : winMin B (u₀, ℓ₀) ≤ j' := Finset.min'_le _ _ hmem
      rw [hwm] at h2
      omega
    have hsupp : sideVal B (u₀, ℓ₀) k = Ladder.ladderSuppVal B.devHgt u₀ ℓ₀ B.μ :=
      (Finset.mem_filter.mp hkmem).2
    rw [hsupp]
    exact lt_of_le_of_ne hle (Ne.symm hne)
  rw [sideVal_coe hb, sideVal_coe ha', WithTop.coe_lt_coe] at hstrict
  -- hstrict : ℓ₀·b + k·u₀ < ℓ₀·a' + j'·u₀  (ℤ)
  have hℓ₀Z : (0 : ℤ) < (ℓ₀ : ℤ) := by exact_mod_cast hℓ₀
  have hkj'Z : (0 : ℤ) < (k : ℤ) - (j' : ℤ) := by omega
  have hu₀Z : (0 : ℤ) ≤ (u₀ : ℤ) := Int.natCast_nonneg u₀
  -- descent: the height strictly drops from j' to k
  have hn : (0 : ℤ) < a' - b := by
    nlinarith [hstrict, mul_nonneg hkj'Z.le hu₀Z, hℓ₀Z]
  obtain ⟨nN, hnN⟩ : ∃ nN : ℕ, (nN : ℤ) = a' - b := ⟨(a' - b).toNat, Int.toNat_of_nonneg hn.le⟩
  have hnNpos : 0 < nN := by omega
  -- the reduced slope pair (u, ℓ)
  set g := Nat.gcd nN (k - j') with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (by omega)
  set u := nN / g with hudef
  set ℓ := (k - j') / g with hℓdef
  have hgu : g * u = nN := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hgl : g * ℓ = k - j' := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hcop : Nat.Coprime u ℓ := Nat.coprime_div_gcd_div_gcd hgpos
  have hℓpos : 1 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h | h
    · rw [h, mul_zero] at hgl; omega
    · exact h
  have hupos : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h, mul_zero] at hgu; omega
    · exact h
  -- cast dictionaries
  have hgZ : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hgpos
  have hℓZ : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓpos
  have e1 : (nN : ℤ) = (g : ℤ) * (u : ℤ) := by exact_mod_cast hgu.symm
  have e2 : (k : ℤ) - (j' : ℤ) = (g : ℤ) * (ℓ : ℤ) := by
    have h := hgl.symm
    have h2 : ((k - j' : ℕ) : ℤ) = ((g * ℓ : ℕ) : ℤ) := by exact_mod_cast h
    rw [Nat.cast_sub hj'k.le] at h2
    push_cast at h2
    linarith [h2]
  -- the new slope is strictly steeper than the entry slope
  have hsteeper : (ℓ : ℤ) * (u₀ : ℤ) < (ℓ₀ : ℤ) * (u : ℤ) := by
    have h1 : ((k : ℤ) - (j' : ℤ)) * (u₀ : ℤ) < (ℓ₀ : ℤ) * (a' - b) := by linarith [hstrict]
    rw [← hnN, e1, e2] at h1
    have h2 : (g : ℤ) * ((ℓ : ℤ) * (u₀ : ℤ)) < (g : ℤ) * ((ℓ₀ : ℤ) * (u : ℤ)) := by
      linarith [h1]
    exact lt_of_mul_lt_mul_left h2 hgZ.le
  -- STRICTNESS to the right: every abscissa beyond k has strictly larger value
  have hstrictR : ∀ m ≤ B.μ, k < m → sideVal B (u, ℓ) k < sideVal B (u, ℓ) m := by
    intro m hm hkm
    by_cases htop : B.devHgt m = ⊤
    · rw [sideVal_coe hb, sideVal_top hℓpos htop]
      exact WithTop.coe_lt_top _
    · obtain ⟨c, hc⟩ := exists_coe_of_ne_top htop
      rw [sideVal_coe hb, sideVal_coe hc, WithTop.coe_lt_coe]
      have hev : sideVal B (u₀, ℓ₀) k ≤ sideVal B (u₀, ℓ₀) m := sideVal_arg_le hkmem hm
      rw [sideVal_coe hb, sideVal_coe hc] at hev
      have hevZ := WithTop.coe_le_coe.mp hev
      -- hevZ : ℓ₀·b + k·u₀ ≤ ℓ₀·c + m·u₀
      have hmkZ : (k : ℤ) < (m : ℤ) := by exact_mod_cast hkm
      have s1 : ((k : ℤ) - (m : ℤ)) * (u₀ : ℤ) ≤ (ℓ₀ : ℤ) * (c - b) := by linarith [hevZ]
      have s2 : (ℓ : ℤ) * (((k : ℤ) - (m : ℤ)) * (u₀ : ℤ)) ≤ (ℓ : ℤ) * ((ℓ₀ : ℤ) * (c - b)) :=
        mul_le_mul_of_nonneg_left s1 hℓZ.le
      have s3 : ((m : ℤ) - (k : ℤ)) * ((ℓ : ℤ) * (u₀ : ℤ))
          < ((m : ℤ) - (k : ℤ)) * ((ℓ₀ : ℤ) * (u : ℤ)) :=
        mul_lt_mul_of_pos_left hsteeper (by linarith)
      have s4 : (ℓ₀ : ℤ) * (((k : ℤ) - (m : ℤ)) * (u : ℤ)) < (ℓ₀ : ℤ) * ((ℓ : ℤ) * (c - b)) := by
        linarith [s2, s3]
      have s5 : ((k : ℤ) - (m : ℤ)) * (u : ℤ) < (ℓ : ℤ) * (c - b) :=
        lt_of_mul_lt_mul_left s4 hℓ₀Z.le
      linarith [s5]
  -- DOMINATION: k's value bounds every abscissa's value
  have hdom : ∀ m ≤ B.μ, sideVal B (u, ℓ) k ≤ sideVal B (u, ℓ) m := by
    intro m hm
    rcases lt_trichotomy m k with hmk | rfl | hkm
    · by_cases htop : B.devHgt m = ⊤
      · rw [sideVal_top hℓpos htop]
        exact le_top
      · obtain ⟨c, hc⟩ := exists_coe_of_ne_top htop
        rw [sideVal_coe hb, sideVal_coe hc, WithTop.coe_le_coe]
        have hmJ : m ∈ (Finset.range k).filter (fun j => B.devHgt j ≠ ⊤) :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmk, htop⟩
        have hf := hmin m hmJ
        simp only [ha', hc, WithTop.untopD_coe] at hf
        rw [div_le_div_iff₀ (by exact_mod_cast Nat.sub_pos_of_lt hj'k)
          (by exact_mod_cast Nat.sub_pos_of_lt hmk)] at hf
        have hfZ : (a' - b) * ((k - m : ℕ) : ℤ) ≤ (c - b) * ((k - j' : ℕ) : ℤ) := by
          exact_mod_cast hf
        rw [Nat.cast_sub hmk.le, Nat.cast_sub hj'k.le, ← hnN, e1] at hfZ
        have hfZ2 : (c - b) * ((k : ℤ) - (j' : ℤ)) = (c - b) * ((g : ℤ) * (ℓ : ℤ)) := by
          rw [e2]
        rw [hfZ2] at hfZ
        -- hfZ : (g·u)·(k−m) ≤ (c−b)·(g·ℓ) — cancel g
        have hc1 : (g : ℤ) * ((u : ℤ) * ((k : ℤ) - (m : ℤ))) ≤
            (g : ℤ) * ((ℓ : ℤ) * (c - b)) := by linarith [hfZ]
        have hc2 : (u : ℤ) * ((k : ℤ) - (m : ℤ)) ≤ (ℓ : ℤ) * (c - b) :=
          le_of_mul_le_mul_left hc1 hgZ
        linarith [hc2]
    · exact le_rfl
    · exact (hstrictR m hm hkm).le
  -- assemble: k is an argmin, maximal; j' is an argmin strictly left of k
  have hkarg : k ∈ sideArg B (u, ℓ) := mem_sideArg_of_forall_le hkμ hdom
  have hmax : winMax B (u, ℓ) = k := by
    refine le_antisymm (Finset.max'_le _ _ _ fun m hmarg => ?_) (Finset.le_max' _ _ hkarg)
    by_contra hgt
    have hgt' : k < m := not_le.mp hgt
    have hmμ : m ≤ B.μ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hmarg).1)
    have hlt := hstrictR m hmμ hgt'
    exact absurd (sideVal_arg_le hmarg hkμ) (not_le.mpr hlt)
  have hj'val : sideVal B (u, ℓ) j' = sideVal B (u, ℓ) k := by
    rw [sideVal_coe ha', sideVal_coe hb, WithTop.coe_inj]
    have hkey : (ℓ : ℤ) * (a' - b) = ((k : ℤ) - (j' : ℤ)) * (u : ℤ) := by
      rw [← hnN, e1, e2]
      ring
    linarith [hkey]
  have hj'arg : j' ∈ sideArg B (u, ℓ) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hj'μ), ?_⟩
    rw [hj'val]
    exact (Finset.mem_filter.mp hkarg).2
  have hminlt : winMin B (u, ℓ) < k := lt_of_le_of_lt (Finset.min'_le _ _ hj'arg) hj'k
  exact ⟨u, ℓ, hcop, hℓpos, hminlt, hmax⟩

/-- **The tiling theorem**: below any hull-supported right endpoint `k`, the genuine
argmin windows of finitely many coprime slope pairs tile `[0, k]` exactly (window widths
sum to `k`).  Like `peel_step`, (STEEP)-free. -/
theorem tiles_of_entry (B : Ladder.BlockData C) :
    ∀ k : ℕ, (∃ u₀ ℓ₀ : ℕ, 1 ≤ ℓ₀ ∧ winMin B (u₀, ℓ₀) = k) →
    ∃ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, Nat.Coprime p.1 p.2 ∧ 1 ≤ p.2 ∧
        winMin B p < winMax B p ∧ winMax B p ≤ k) ∧
      ∑ p ∈ S, (winMax B p - winMin B p) = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hentry
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨∅, by simp, by simp⟩
    · obtain ⟨u₀, ℓ₀, hℓ₀, hwm⟩ := hentry
      obtain ⟨u, ℓ, hcop, hℓ, hminlt, hmax⟩ := peel_step hk hℓ₀ hwm
      obtain ⟨S', hS', hsum'⟩ := ih (winMin B (u, ℓ)) hminlt ⟨u, ℓ, hℓ, rfl⟩
      have hnotmem : (u, ℓ) ∉ S' := by
        intro hmem
        have h1 := (hS' _ hmem).2.2.1
        have h2 := (hS' _ hmem).2.2.2
        omega
      refine ⟨insert (u, ℓ) S', ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact ⟨hcop, hℓ, hmax ▸ hminlt, hmax.le⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hS' p hp'
          exact ⟨h1, h2, h3, le_trans h4 hminlt.le⟩
      · rw [Finset.sum_insert hnotmem, hsum', hmax]
        omega

/-- The flat pair `(0, 1)` reads the raw heights. -/
theorem sideVal_zero_one (B : Ladder.BlockData C) (j : ℕ) :
    sideVal B (0, 1) j = B.devHgt j := by
  simp [sideVal]

/-- Under (STEEP), heights strictly left of `μ` are strictly positive. -/
theorem devHgt_pos_of_steep {B : Ladder.BlockData C} (hsteep : SteepBlock B) {m : ℕ}
    (hm : m < B.μ) : (0 : WithTop ℤ) < B.devHgt m := by
  refine lt_of_le_of_lt ?_ (hsteep m hm)
  rw [← WithTop.coe_natCast (α := ℤ)]
  exact_mod_cast Int.natCast_nonneg _

/-- The top entry: under (STEEP) the flat pair `(0, 1)` has its whole argmin window at the
monic top `μ`. -/
theorem winMin_zero_one (B : Ladder.BlockData C) (hsteep : SteepBlock B) :
    winMin B (0, 1) = B.μ := by
  have hμmem : B.μ ∈ sideArg B (0, 1) := by
    refine mem_sideArg_of_forall_le le_rfl fun m hm => ?_
    rw [sideVal_zero_one, sideVal_zero_one, devHgt_mu]
    rcases eq_or_lt_of_le hm with rfl | hlt
    · rw [devHgt_mu]
    · exact (devHgt_pos_of_steep hsteep hlt).le
  have hj := winMin_mem B (0, 1)
  rcases eq_or_lt_of_le (winMin_le_mu B (0, 1)) with h | h
  · exact h
  · exfalso
    have hv : sideVal B (0, 1) (winMin B (0, 1)) = sideVal B (0, 1) B.μ := by
      rw [(Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hμmem).2]
    rw [sideVal_zero_one, sideVal_zero_one, devHgt_mu] at hv
    exact absurd hv (ne_of_gt (devHgt_pos_of_steep hsteep h))

end Peel

/-! ## §5 The discharge: `HE7APackageExported` at every (STEEP) pair -/

section Discharge

universe uO uK uW

variable {O : Type uO} [CommRing O] {K : Type uK} [Field K]
variable {C : Ladder.SlotCarrier O K}

/-- ★ **CEX's R1, discharged at (STEEP) blocks**: the windows engine assembles a
`RungInterface` whose sides are exactly the genuine hull sides of `B.devHgt` with their
extremal window widths, and which is CORE-EXPORTED.  Generic in `(C, B)`: the only
hypothesis is the block-local (STEEP) law. -/
theorem he7aPackageExported_of_steep (B : Ladder.BlockData C) (hsteep : SteepBlock B) :
    HE7APackageExported.{uO, uK, uW} C B := by
  obtain ⟨S, hS, hsum⟩ := tiles_of_entry B B.μ ⟨0, 1, le_rfl, winMin_zero_one B hsteep⟩
  refine ⟨{ sides := S
            hside_cop := fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩
            hside_node := fun p hp => side_node_of_steep hsteep (hS p hp).2.1 (hS p hp).2.2.1
            len := fun p => winMax B p - winMin B p
            hlen_pos := fun p hp => by have := (hS p hp).2.2.1; omega
            hlen_sum := hsum
            linFac := fun p => {((0 : K), (winMax B p - winMin B p) / p.2)}
            hiFac := fun _ => 0
            hresdeg := fun p hp => by
              have hdvd : p.2 ∣ (winMax B p - winMin B p) :=
                winLen_dvd (hS p hp).1 (hS p hp).2.1
              simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_zero,
                Multiset.sum_zero, add_zero]
              exact Nat.mul_div_cancel' hdvd
            rootCount := fun p => C.D * (winMax B p - winMin B p)
            haccount := fun _ _ => rfl
            classCount := fun p _ => C.D * (winMax B p - winMin B p)
            classCountHi := fun _ _ => 0
            hnonempty := fun p hp =>
              ⟨fun _ _ => Nat.mul_pos C.hD (by have := (hS p hp).2.2.1; omega),
               fun q hq => absurd hq (by simp)⟩
            hforce := fun p hp =>
              ⟨fun _ _ => Nat.mul_le_mul_left _
                (Nat.le_of_dvd (by have := (hS p hp).2.2.1; omega)
                  (winLen_dvd (hS p hp).1 (hS p hp).2.1)),
               fun q hq => absurd hq (by simp)⟩
            hexhaust := fun p hp => by simp
            W := PUnit.{uW + 1}
            wf := emptyWf
            σRank := PUnit.unit }, ?_⟩
  intro p hp
  refine ⟨winMin B p, winMax B p, (hS p hp).2.2.1,
    winMin_onSide B p, winMax_onSide B p, rfl, ?_⟩
  intro m hm
  exact ⟨winMin_le hm, le_winMax hm⟩

/-! ### Forced-window teeth: the export core PINS every consumer interface's data -/

/-- FORCED WINDOWS: a core-exported interface's per-side witnesses are exactly the
extremal window reads — `IfaceExportedCore` pins each side to a genuine window and
`len` to `winMax − winMin`.  (The core's extremality clause makes the witness pair
UNIQUE, so the relation is rigid, not just inhabited.) -/
theorem IfaceExportedCore.win_forced {B : Ladder.BlockData C}
    {I : Ladder.RungInterface.{uO, uK, uW} C B} (h : IfaceExportedCore B I) :
    ∀ p ∈ I.sides, winMin B p < winMax B p ∧ I.len p = winMax B p - winMin B p := by
  intro p hp
  obtain ⟨j, k, hjk, hj, hk, hlen, hext⟩ := h p hp
  have hjeq : j = winMin B p :=
    le_antisymm (hext _ (winMin_onSide B p)).1 (winMin_le hj)
  have hkeq : k = winMax B p :=
    le_antisymm (le_winMax hk) (hext _ (winMax_onSide B p)).2
  rw [hjeq, hkeq] at hjk hlen
  exact ⟨hjk, hlen⟩

/-- REDUNDANCY TOOTH: at a (STEEP) block, E.12's node clause `ℓ·T < u` is FORCED on
every core-exported interface — the export relation reproves `hside_node` on its own.
(Evidence of contentfulness: nothing `⊤`-shaped can do this.) -/
theorem exported_node_forced {B : Ladder.BlockData C} (hsteep : SteepBlock B)
    {I : Ladder.RungInterface.{uO, uK, uW} C B} (h : IfaceExportedCore B I) :
    ∀ p ∈ I.sides, 1 ≤ p.2 → p.2 * B.T < p.1 := fun p hp hℓ =>
  side_node_of_steep hsteep hℓ (h.win_forced p hp).1

/-- STRUCTURE for the E.57 funnel (`hpart` consumers): every core-exported interface's
side length is divisible by its denominator. -/
theorem exported_len_dvd {B : Ladder.BlockData C}
    {I : Ladder.RungInterface.{uO, uK, uW} C B} (h : IfaceExportedCore B I) :
    ∀ p ∈ I.sides, Nat.Coprime p.1 p.2 → 1 ≤ p.2 → p.2 ∣ I.len p := by
  intro p hp hcop hℓ
  rw [(h.win_forced p hp).2]
  exact winLen_dvd hcop hℓ

/-- **The two exported twins fire together at a (STEEP) block**: CEX's lb1 wiring plus
this unit's package discharge.  The lb1 leg's honest remainder is `hpart` (E.57
partition legs at core-exported triggering interfaces — the C-side HE7.96(a)
factorization funnel) + the owner re-sign (R3); the PACKAGE leg's remainder is (STEEP)
at arising pairs (R1′) + R3 ALONE. -/
theorem exportedTwins_of_steep_partitionLegs [IsDomain O]
    {B : Ladder.BlockData C} (hsteep : SteepBlock B)
    (hpart : ∀ I : Ladder.RungInterface.{uO, uK, uW} C B, IfaceExportedCore B I →
      (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
      Nonempty (Ladder.PartitionLeg I)) :
    HE7APackageExported.{uO, uK, uW} C B ∧
      LB1CarrierLive.{uO, uK, uW} C B (IfaceExportedCore B) :=
  ⟨he7aPackageExported_of_steep B hsteep, lb1CarrierExported_of_partitionLegs hpart⟩

end Discharge

/-! ## §6 The arising wrappers — CEX's `RealizedRungInterfaceExport` genre INHABITED at
(STEEP) realizations, and the supplier layer -/

section Realized

universe uE uG uKt uL uW

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Kt : Type uKt} [Field Kt] {E : Type uE} [Field E] {L : Type uL} [Field L]
variable [Algebra Kt L]
variable {n : ℕ} {core : ArisingCore (O := O) Kt L n}
variable {Aℛ : ChainRealization (O := O) (π := core.π) (F := core.F)
  (H₀ := core.H₀) (hpin := core.hpin) core.T Kt E L}

/-- ★ LB1G's demanded genre INHABITED: at a (STEEP) realized block, some interface is
realized-exported (CEX's `RealizedRungInterfaceExport`, discharged). -/
theorem exists_realizedExport_of_steep (X : RealizedInput core Aℛ)
    {K : Type} [Field K] (eK : core.T.fld core.i ≃+* K)
    (hsteep : SteepBlock (X.inputBlockTransport eK)) :
    ∃ I : Ladder.RungInterface.{0, 0, uW}
      (X.stageCarrierTransport eK) (X.inputBlockTransport eK),
      RealizedRungInterfaceExport X eK I :=
  he7aPackageExported_of_steep (X.inputBlockTransport eK) hsteep

end Realized

section Suppliers

universe uW uG uKt uL

/-- ★ **`ifaceExportedCore_of_arising`** — the charge's named target, at its honest
minimal restriction: at an arising pair, (STEEP) discharges the export core.  ⚠ The
config witness is deliberately UNCONSUMED (machine-visible `_hcfg`): deriving
`SteepBlock B` FROM the realization is exactly the F1 frontier residue R1′ — named
below as `LadderSteepSupplier`, NOT landed mathematics. -/
theorem ifaceExportedCore_of_arising {O : Type} [CommRing O] {K : Type} [Field K]
    {C : Ladder.SlotCarrier O K} {B : Ladder.BlockData C}
    {G : Type uG} [CommGroup G] {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L]
    [Algebra Kt L] {N : Gauge.NormSection G} {v : ℕ → (G →* Multiplicative ℤ)}
    {ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ} {q : ℕ → ℤ} {n : ℕ}
    (_hcfg : CanonicalLadderConfig C B G Kt L N v ρ q n) (hsteep : SteepBlock B) :
    ∃ I : Ladder.RungInterface.{0, 0, uW} C B, IfaceExportedCore B I :=
  he7aPackageExported_of_steep B hsteep

/-- **R1′ — the ONE remaining arising obligation** (the F1 `BlockFrontier` residue,
scoped by this unit to a single pointwise height inequality): every arising degree-`n`
configuration's block is (STEEP).  NEW STATEMENT (review); OPEN — the honest remainder,
deliberately named rather than assumed. -/
def LadderSteepSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
    SteepBlock B

/-- **R3's target shape** — the exported-package supplier: IFC0's `LadderPackageSupplier`
with the conclusion strengthened from the (tautological) `HE7APackage` to the contentful
`HE7APackageExported`.  Re-signing the capstone's `package` leg to THIS is the owner
amendment (flagged, NOT enacted).  NEW STATEMENT (review). -/
def LadderPackageExportedSupplier (n : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K]
    (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
    (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
    [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
    (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
    CanonicalLadderConfig C B G Kt L N v ρ q n →
    HE7APackageExported.{0, 0, uW} C B

/-- ★ **The supplier-level discharge**: the steep supplier fires the exported-package
supplier at every degree — post-IEC, the meaningful package leg rests on R1′ (+ R3)
alone. -/
theorem ladderPackageExportedSupplier_of_steep {n : ℕ}
    (hs : LadderSteepSupplier.{uG, uKt, uL} n) :
    LadderPackageExportedSupplier.{uW, uG, uKt, uL} n :=
  fun O _ K _ C B G _ Kt _ L _ _ N v ρ q hcfg =>
    he7aPackageExported_of_steep B (hs O K C B G Kt L N v ρ q hcfg)

end Suppliers

/-! ## §7 GATE (executed nonvacuity): a concrete (STEEP) block, and the engine fired on it

The vacuity standard (this repo's central discipline): `he7aPackageExported_of_steep`
must not live on a provably-empty premise.  The gate exhibits a full `SlotCarrier` over
`ℚ` (constant height `1`, digit = constant coefficient — all ten laws discharged), the
block `F = X² + 1` over the key `Φ = X` (`μ = 2`, `T = 0`), proves it (STEEP), and fires
the discharge.  On this block the engine's answer is the single side `(1, 2)` of window
`[0, 2]` — the interior abscissa has height `⊤` (`A 1 = 0`), so the gate also exercises
the `⊤`-branch of the peel. -/

section Gate

open Polynomial

/-- The gate slot carrier: `D = 1`, constant height `1` on nonzero polynomials, digit =
constant coefficient, full heights `{1}`. -/
noncomputable def gateSlot : Ladder.SlotCarrier ℚ ℚ where
  D := 1
  hD := one_pos
  eC := 1
  fC := 1
  hef := rfl
  heC := le_rfl
  hfC := le_rfl
  hgt := fun A => if A = 0 then ⊤ else 1
  dig := fun A => A.coeff 0
  hgt_zero := by simp
  dig_zero := by simp
  hgt_ne_top := fun A hA _ => by simp [hA]
  dig_ne_zero := fun A hA hdeg => by
    intro hc
    exact hA (by
      have h0 : A.natDegree = 0 := by omega
      have := Polynomial.eq_C_of_natDegree_le_zero h0.le
      rw [this, hc, Polynomial.C_0])
  hgt_add_ge := fun A B => by
    by_cases hA : A = 0
    · simp [hA]
    · by_cases hB : B = 0
      · simp [hB]
      · by_cases hAB : A + B = 0 <;> simp [hA, hB, hAB]
  hgt_add_eq := fun A B hne => by
    by_cases hA : A = 0
    · by_cases hB : B = 0
      · exact absurd (by simp [hA, hB]) hne
      · simp [hA, hB]
    · by_cases hB : B = 0
      · simp [hA, hB]
      · exact absurd (by simp [hA, hB]) hne
  dig_add := fun A B k hA hB hne => by
    have hA0 : A ≠ 0 := by
      intro h
      rw [h] at hA
      simp at hA
    have hB0 : B ≠ 0 := by
      intro h
      rw [h] at hB
      simp at hB
    have hAB : A + B ≠ 0 := by
      intro h
      have : (A + B).coeff 0 = 0 := by rw [h]; simp
      rw [Polynomial.coeff_add] at this
      exact hne this
    constructor
    · rw [if_neg hA0] at hA
      simpa [hAB] using hA
    · exact Polynomial.coeff_add A B 0
  Full := fun k => k = 1
  hlift := fun k hk c hc =>
    ⟨Polynomial.C c, by simpa using hc, by simp,
      by simp [Polynomial.C_eq_zero.not.mpr hc, hk], by simp⟩

/-- The gate block over `gateSlot`: `Φ = X`, `F = X² + 1`, `μ = 2`, `T = 0`. -/
noncomputable def gateBlock : Ladder.BlockData gateSlot where
  Φ := Polynomial.X
  F := Polynomial.X ^ 2 + Polynomial.C 1
  μ := 2
  hμ := by omega
  hΦ := Polynomial.monic_X
  hΦdeg := Polynomial.natDegree_X
  A := fun j => if j = 0 then Polynomial.C 1 else 0
  hdev := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp
  hdegA := fun j hj => by
    by_cases h : j = 0 <;> simp [h, gateSlot]
  hkeyfree := by
    refine ⟨1, -Polynomial.X, ?_⟩
    simp only [Polynomial.C_1, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one]
    ring
  hA0 := by simp
  T := 0

/-- The gate block is (STEEP): both left abscissas clear the (trivial) threshold line. -/
theorem gateBlock_steep : SteepBlock gateBlock := by
  intro j hj
  have hμ : gateBlock.μ = 2 := rfl
  rw [hμ] at hj
  interval_cases j
  · have h0 : gateBlock.devHgt 0 = 1 := by
      simp [Ladder.BlockData.devHgt, gateBlock, gateSlot]
    rw [h0]
    simp
  · have h1 : gateBlock.devHgt 1 = ⊤ := by
      simp [Ladder.BlockData.devHgt, gateBlock, gateSlot]
    rw [h1]
    simp

/-- GATE: the discharge FIRES on a concrete block — `HE7APackageExported` is inhabited
at a real pair, so the (STEEP) premise is not provably empty. -/
example : HE7APackageExported.{0, 0, 0} gateSlot gateBlock :=
  he7aPackageExported_of_steep gateBlock gateBlock_steep

end Gate

end Uniformity.Density.IFC5

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only. -/

#print axioms Uniformity.Density.IFC5.sideArg
#print axioms Uniformity.Density.IFC5.winMin
#print axioms Uniformity.Density.IFC5.winMax
#print axioms Uniformity.Density.IFC5.SteepBlock
#print axioms Uniformity.Density.IFC5.winLen_dvd
#print axioms Uniformity.Density.IFC5.side_node_of_steep
#print axioms Uniformity.Density.IFC5.peel_step
#print axioms Uniformity.Density.IFC5.tiles_of_entry
#print axioms Uniformity.Density.IFC5.winMin_zero_one
#print axioms Uniformity.Density.IFC5.he7aPackageExported_of_steep
#print axioms Uniformity.Density.IFC5.IfaceExportedCore.win_forced
#print axioms Uniformity.Density.IFC5.exported_node_forced
#print axioms Uniformity.Density.IFC5.exported_len_dvd
#print axioms Uniformity.Density.IFC5.exportedTwins_of_steep_partitionLegs
#print axioms Uniformity.Density.IFC5.exists_realizedExport_of_steep
#print axioms Uniformity.Density.IFC5.ifaceExportedCore_of_arising
#print axioms Uniformity.Density.IFC5.LadderSteepSupplier
#print axioms Uniformity.Density.IFC5.LadderPackageExportedSupplier
#print axioms Uniformity.Density.IFC5.ladderPackageExportedSupplier_of_steep
