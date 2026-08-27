/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFC0
import Uniformity.ChapC.C132sg3

/-!
# Uniformity.ChapI.IFC1 — the deepTwist supplier bridge: μ₃'s `GENTOW5WCleared` toward
DT0's `DeepGentowSupplier`

**[FDTB, 2026-08-27]** (`docs/in-progress/CAPSTONE_IFACE_2026-08-26.md` §DT0;
supply side `Uniformity/ChapC/C132sg3.lean`, the A-C.21/ANORM landing).

**⚠ TRUST BOUNDARY — `GentowWWindow` is a NEW statement**, flagged for the standing
review; the two wiring hypothesis SHAPES (`hread`/`htheta` below) are the DISPLAYED open
identifications, also review-flagged.  Nothing here is signed; nothing binds into
leanspec.  Zero `sorry`, zero new axiom; AxChk footer expects Lean core only.

## The demand and the supply (the analyzed gap)

DT0's `DeepGentowSupplier n` (IFC0 §2) demands, at every arising joint witness of depth
`r`, the flat family `∀ j, 3 ≤ j → j < r → Gauge.GentowW (A j) (q j) (R j) (w j)`, where
D.44's raw identity `GentowW A q R w = ∀ s : ℕ, R (N.n (s·q)) = θ(q,s)·w^s` quantifies
over ALL exponents and `(A, R, w)` are the witness's OWN exports (C130vw's
`ArenaFamilyViewEq`: `R j` = the chain node's `towerRead`, `w j` = its `peelUnit`).
The μ₃ campaign's endpoint `C132sg3.s2Mu3_gentow5w_two : GENTOW5WCleared (s2DepthTwo …)
2 1 21 (s2Mu3Calculus …)` speaks the FGMN-calculus language instead: per-`t` laws
`Rgr(e'·((f'−t)·u')) (chainNormBelow r ((f'−t)·u')) · thetaRatioCleared (f'−t) = w^(f'−t)`
with witness in `W.fld r`.  The bridge therefore decomposes into THREE independent gaps:

1. **RANGE**: the cleared carrier supplies exponents `s = f'−t ∈ [1, f']` only; D.44 also
   demands the `s = 0` normalization clause and the `s > f'` tail.  §1 names the supplied
   part (`GentowWWindow`) and proves the EXACT decomposition
   `GentowW ↔ zero-clause ∧ window ∧ tail`, so the residual demand is machine-readable.
2. **WIRING (GC-13, OPEN)**: no landed declaration relates the FGMN reads
   (`Rgr`/`chainNormBelow`/`thetaRatioCleared`, `W.fld r`-valued) to the witness's gauge
   exports (`towerRead`-read at ladder points, arena `theta`, `Kt`-valued).  §2's
   translation lemma displays the two exact missing identifications as hypotheses
   through a level receiver `φ : W.fld r →+* Kt`:
   `hread : R (N.n (s·q)) = φ (Rgr (e'·(s·u')) (chainNormBelow r (s·u')))` and
   `htheta : θ(q,s) · φ (thetaRatioCleared s) = 1` — D.44's GC-13 note
   (`θ_i(t) = Θ_N(s;u_{i+1})`, `w_i = R_{i+1,κ̄_i}(n̂_i(u_{i+1}))`), never formalized.
   Given both, `GENTOW5WCleared → window` is pure `CommRing` algebra (proved here).
   ⚠ D-D12 fence: `hread`/`htheta` may only ever be discharged at an arising witness's
   OWN exported `(A, R, w)` — instantiating them at cooked gauge data proves nothing
   toward the supplier, whose guard pins the data (no cheap fabricated instance is landed
   here, and none may be presented as teeth).
3. **DEPTH**: the demand bites only at witnesses of depth `r ≥ 4` (live range
   `3 ≤ j < r` nonempty); the ONLY landed arising witness (the S2 frontier) has `r = 2`,
   where the family is vacuous — machine-pinned in §4.  The μ₃ endpoint is a depth-2
   SHAPE tooth: §3 plugs it into the translation lemma at `(e',f',u') = (2,1,21)`,
   exercising the exact plug-in route the DT0 doc promised, at the one exponent `s = 1`.

## What remains open after this file (the honest interface note)

* the GC-13 wiring at the realized S2 exports (discharging `hread`/`htheta` at
  `towerReadFamily`/`arenaFamily`/`peelUnitFamily` data) — the next campaign;
* the `s = 0` clause and `s > f'` tail of D.44's identity (gap 1's residue — open math);
* per-level supply at any level `j ≥ 3` of a depth-`≥ 4` witness (no such witness is
  landed; the μ₃ tooth is depth 2);
* the entire ϑ half (`DeepVarthetaSupplier`) — research-open, E.61 has no teeth;
* the non-vacuity teeth the CIFACE doc demands before any positive-conditionality claim
  (an inhabited degree-2 socket instance) — unchanged by this unit.
-/

set_option linter.style.longLine false

noncomputable section

namespace Uniformity.Density.IFC1

open Uniformity.Density Uniformity.Density.Tower

universe uT

/-! ## §1 The exponent window of D.44's identity (gap 1 made exact) -/

/-- **The campaign-window slice of D.44's `GentowW`**: the raw identity restricted to the
exponents `1 ≤ s ≤ f'` a rung-`f'` GENTOW5W endpoint supplies (`s = f' − t`, `t < f'`).
NEW STATEMENT (review). -/
def GentowWWindow {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : Gauge.NormSection G} (A : Gauge.GaugeArena G Kt N) (q : ℤ) (R : G → Kt)
    (w : Ktˣ) (f' : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → s ≤ f' → R (N.n (s * q)) = (A.theta q s : Kt) * (w : Kt) ^ s

/-- ★ **The RANGE gap, exact**: D.44's full identity is EXACTLY the `s = 0` normalization
clause plus the window plus the `s > f'` tail.  Forward: instances.  Backward: three-way
case split on `s`.  This is the machine-readable residue of feeding a per-level campaign
endpoint into `DeepGentowSupplier`'s per-level demand. -/
theorem gentowW_iff_zero_window_tail {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : Gauge.NormSection G} (A : Gauge.GaugeArena G Kt N) (q : ℤ) (R : G → Kt)
    (w : Ktˣ) (f' : ℕ) :
    Gauge.GentowW A q R w ↔
      R (N.n 0) = (A.theta q 0 : Kt) ∧ GentowWWindow A q R w f' ∧
        ∀ s : ℕ, f' < s → R (N.n (s * q)) = (A.theta q s : Kt) * (w : Kt) ^ s := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun s hs1 _ => h s, fun s _ => h s⟩
  · rintro ⟨h0, hwin, htail⟩ s
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · simpa using h0
    · rcases Nat.lt_or_ge f' s with hsf | hsf
      · exact htail s hsf
      · exact hwin s hs1 hsf

/-- The projection half alone: the full identity restricts to every window. -/
theorem GentowWWindow.of_gentowW {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : Gauge.NormSection G} {A : Gauge.GaugeArena G Kt N} {q : ℤ} {R : G → Kt}
    {w : Ktˣ} (h : Gauge.GentowW A q R w) (f' : ℕ) : GentowWWindow A q R w f' :=
  fun s _ _ => h s

/-! ## §2 The translation lemma (gap 2 displayed, its algebra discharged) -/

/-- **The translation core, pinned witness**: a cleared per-`t` law family (the
`GENTOW5WCleared` body at witness `wC`), a receiver `φ`, the peel-unit identification
`hunit`, and the two GC-13 wiring identifications `hread`/`htheta` yield the D.44 window.
The mathematics is `CommRing` algebra; every open identification is a DISPLAYED
hypothesis (review-flagged shapes; see the module fence on D-D12). -/
theorem gentowWWindow_of_cleared_law {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : Gauge.NormSection G} (A : Gauge.GaugeArena G Kt N) (q : ℤ) (R : G → Kt)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ} (I : FGMNCalculus W e' f' u')
    (φ : W.fld r →+* Kt) (wC : W.fld r) (w : Ktˣ)
    (hlaw : ∀ t, t < f' →
      I.Rgr (e' * ((f' - t) * u')) (I.chainNormBelow r ((f' - t) * u'))
          * I.thetaRatioCleared (f' - t) = wC ^ (f' - t))
    (hunit : (w : Kt) = φ wC)
    (hread : ∀ s, 1 ≤ s → s ≤ f' → R (N.n (s * q)) =
      φ (I.Rgr (e' * (s * u')) (I.chainNormBelow r (s * u'))))
    (htheta : ∀ s, 1 ≤ s → s ≤ f' →
      (A.theta q s : Kt) * φ (I.thetaRatioCleared s) = 1) :
    GentowWWindow A q R w f' := by
  intro s hs1 hsf
  have h1 := hlaw (f' - s) (by omega)
  rw [show f' - (f' - s) = s by omega] at h1
  have h2 : φ (I.Rgr (e' * (s * u')) (I.chainNormBelow r (s * u')))
      * φ (I.thetaRatioCleared s) = φ wC ^ s := by
    rw [← map_mul, ← map_pow, h1]
  have h3 : (A.theta q s : Kt) * φ wC ^ s
      = φ (I.Rgr (e' * (s * u')) (I.chainNormBelow r (s * u'))) := by
    rw [← h2, mul_left_comm, htheta s hs1 hsf, mul_one]
  rw [hread s hs1 hsf, hunit]
  exact h3.symm

/-- ★ **The translation lemma at the signed carrier**: `GENTOW5WCleared` plus the two
GC-13 identifications through a receiver yield the D.44 window at the receiver image of
the C-side peel witness.  The μ₃ endpoint plugs in below with NO repackaging — exactly
the DT0 design promise. -/
theorem gentowWWindow_of_gentow5wCleared {G : Type*} [CommGroup G] {Kt : Type*}
    [Field Kt] {N : Gauge.NormSection G} (A : Gauge.GaugeArena G Kt N) (q : ℤ)
    (R : G → Kt)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} {r : ℕ}
    {W : DeepTower.{0, uT} F H₀ hpin r} {e' f' u' : ℕ} (I : FGMNCalculus W e' f' u')
    (hC : GENTOW5WCleared W e' f' u' I) (φ : W.fld r →+* Kt)
    (hread : ∀ s, 1 ≤ s → s ≤ f' → R (N.n (s * q)) =
      φ (I.Rgr (e' * (s * u')) (I.chainNormBelow r (s * u'))))
    (htheta : ∀ s, 1 ≤ s → s ≤ f' →
      (A.theta q s : Kt) * φ (I.thetaRatioCleared s) = 1) :
    ∃ w : Ktˣ, GentowWWindow A q R w f' := by
  obtain ⟨wC, hwC, hlaw⟩ := hC
  exact ⟨Units.mk0 (φ wC) (fun h => hwC (RingHom.injective φ (by rw [h, map_zero]))),
    gentowWWindow_of_cleared_law A q R I φ wC _ hlaw rfl hread htheta⟩

/-! ## §3 The μ₃ depth-2 tooth: the campaign endpoint plugs in at `(2, 1, 21)` -/

section S2

open IsLocalRing Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C132sg2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- ★ **The first per-level tooth `deepTwist`-ward**: the UNCONDITIONAL μ₃ endpoint
(`C132sg3.s2Mu3_gentow5w_two`) feeds the translation lemma at `(e',f',u') = (2,1,21)`,
depth 2 — leaving exactly the two wiring equations at the single exponent `s = 1` as the
displayed residue.  A SHAPE tooth (module note, gap 3): at depth 2 the supplier's live
range is empty, so this is the plug-in route rehearsed, not a level-`j` supply. -/
theorem s2Mu3_gentowWWindow {G : Type*} [CommGroup G] {Kt : Type*} [Field Kt]
    {N : Gauge.NormSection G} (A : Gauge.GaugeArena G Kt N) (q : ℤ) (R : G → Kt)
    (φ : (s2DepthTwo h2 hq).fld 2 →+* Kt)
    (hread : R (N.n ((1 : ℕ) * q)) =
      φ ((s2Mu3Calculus h2 hq).Rgr (2 * (1 * 21))
          ((s2Mu3Calculus h2 hq).chainNormBelow 2 (1 * 21))))
    (htheta : (A.theta q 1 : Kt) *
      φ ((s2Mu3Calculus h2 hq).thetaRatioCleared 1) = 1) :
    ∃ w : Ktˣ, GentowWWindow A q R w 1 :=
  gentowWWindow_of_gentow5wCleared A q R (s2Mu3Calculus h2 hq)
    (C132sg3.s2Mu3_gentow5w_two h2 hq) φ
    (fun s hs1 hsf => by
      have hs : s = 1 := by omega
      subst hs; exact hread)
    (fun s hs1 hsf => by
      have hs : s = 1 := by omega
      subst hs; exact htheta)

end S2

/-! ## §4 The depth pin (gap 3): shallow witnesses demand nothing -/

/-- At depth `r ≤ 3` the per-level family `DeepGentowSupplier` demands is VACUOUS — the
DT0 doc's honest scope note, machine-pinned.  The only landed arising witness (the S2
frontier, `r = 2`) therefore demands nothing today; DT0's content begins at `r ≥ 4`. -/
theorem deepGentow_demand_vacuous_of_shallow {G : Type*} [CommGroup G] {Kt : Type*}
    [Field Kt] {N : Gauge.NormSection G} (A : ℕ → Gauge.GaugeArena G Kt N)
    (q : ℕ → ℤ) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) {r : ℕ} (hr : r ≤ 3) :
    ∀ j, 3 ≤ j → j < r → Gauge.GentowW (A j) (q j) (R j) (w j) :=
  fun _ h3 hjr => absurd (h3.trans_lt hjr) (by omega)

end Uniformity.Density.IFC1

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}` only.
The μ₃ tooth consumes the UNCONDITIONAL `C132sg3.s2Mu3_gentow5w_two` (cite-free); nothing
here may add to the trusted base. -/

#print axioms Uniformity.Density.IFC1.GentowWWindow
#print axioms Uniformity.Density.IFC1.gentowW_iff_zero_window_tail
#print axioms Uniformity.Density.IFC1.GentowWWindow.of_gentowW
#print axioms Uniformity.Density.IFC1.gentowWWindow_of_cleared_law
#print axioms Uniformity.Density.IFC1.gentowWWindow_of_gentow5wCleared
#print axioms Uniformity.Density.IFC1.s2Mu3_gentowWWindow
#print axioms Uniformity.Density.IFC1.deepGentow_demand_vacuous_of_shallow
