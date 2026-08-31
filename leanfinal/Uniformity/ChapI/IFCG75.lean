/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG48

/-!
# Uniformity.ChapI.IFCG75 — [H2L 2026-08-31] the slope-`h ≥ 2` recentring currency:
the Bézout normalization, the multiplication-by-`h` coordinate lattice, and the
normalized cell transport

Stage H2L of the cone census (design record `runs/codex/H2C_design.md`, verdict
`runs/wave-c/verdict_H2L.md`).  The mixed/deep census axes at slope `h/e` with
`h ≥ 2` were stalled on a STATEMENT-CURRENCY gap: the naive recentring ring
`O[X]/(X^e − zπ^h)` is NOT normal (not a DVR — the design's verdict), so IFCG43's
`h = 1` cell transport does not extend verbatim.  This file transcribes the design's
two-layer package:

* **§1 Bézout arithmetic.**  The single pin is `(B): a·h = b·e + 1` — positivity of
  `a, h` and coprimality of `(h, e)` are DERIVED from it, and the multiplication-by-`h`
  permutation `i ↦ h·i % e` of `{0, …, e−1}` comes with the EXPLICIT inverse
  `j ↦ a·j % e`.  Existence/uniqueness of `(a, b)` from coprimality is
  `bezout_exists`/`bezout_unique`.
* **§2 the Bézout presentation.**  The correct recentring DVR is
  `O' := AdjoinRoot (eisKey π (−(↑u^a)) e)` — the EISENSTEIN presentation
  `O[Y]/(Y^e − u^a·π)` — so IFCG39's landed `h = 1` cascade INSTANTIATES (nothing is
  re-proved): complete DVR, totally ramified of degree `e`, `𝔪' = (γ)`, residue
  cardinality unchanged (`bez_recentring_stack`).  The anti-drift pins (R):
  `γ^e = u^a·π`, `ξ := u^{−b}·γ^h` satisfies `ξ^e = u·π^h` and `ξ^a = π^b·γ`.
* **§3 the order embedding.**  `bezRawKey π u h e = X^e − C(u·π^h)` (monic, degree
  `e`) presents the raw order `A`; `bezOrderMap : A →+* O'` sends `x ↦ ξ` (its
  well-definedness IS (R2)) and is INJECTIVE (`bezOrderMap_injective`, via the §4
  coordinate permutation).  **The corresponding DVR/complete/maximal-ideal claims for
  `A` itself are deliberately, permanently ABSENT: they are FALSE for `h ≥ 2`** (the
  design's §3.3 obstruction; e.g. at `(h, e) = (2, 3)` the induced map
  `A/π^N → O'/γ^{3N}` is not injective).  Never re-derive an `h = 1`-style transport
  through the raw ring map.
* **§4 the coordinate lattice.**  (C1): `ξ^i = δ_i·π^{q_i}·γ^{r_i}` with
  `q_i = h·i / e`, `r_i = h·i % e`, `δ_i = u^{a·q_i}·u^{−b·i} ∈ O^×`; the raw-order
  lattice (L-raw) `γ^w ∣ ι(mk P) ⟺ π^{⌈(w − h·i)/e⌉⁺} ∣ P_i`; the Bézout coordinate
  normalization `Θ` (C2) — an `O`-linear equivalence, deliberately NOT a ring map —
  with its lattice (L-norm) and the level-exact specialization (L-level)
  `γ^{e·N} ∣ Θ(P) ⟺ π^N ∣ P_i`.  `Θ`, not the ring embedding, supports the finite
  boxes: the carry factors `π^{q_i}` are exactly what breaks the raw map.
* **§5 the normalized development and the finite cell transport.**  `bezDevT` (the
  `bezRawKey`-adic development with `Θ` postcomposed coefficientwise), `bezReassT`
  (its inverse), round trips, two-way level exactness, and the count-preserving
  `bezCellTransport : Coeff O (e·k) N ≃ Coeff O' k (e·N)` with the same three
  interface theorems as IFCG43 (`_apply`, `_symm_apply`, `_card_image`) and the box
  count pin `#Coeff(O', k, e·N) = q^{k·e·N}`.
* **§6 LAYER 2 — the correspondence surface (stated, NOT asserted).**
  `SlopeBezoutFactorCorrespondenceAt h k`: the named Prop in the
  `IFCG48.FactorCorrespondenceAt` genre — under the slope-`h/e` lattice and the
  Bézout deep-box condition (A) on the normalized development, the monic factors of
  `g` match those of `bezDevT g` with `(e, f) ↦ (e·e, f)` legs.  Its reductions:
  (TS) `typeOf g = scaleType e (typeOf (bezDevT g))` fires through IFCG48's
  `typeOf_eq_scaleType_of_rel` VERBATIM (the multiset reduction is generic in the
  Eisenstein unit), and (DT) the decision transport
  `DecidedAt O' k σ' (e·N) (transport c) ⟺ DecidedAt O (e·k) (scaleType e σ') N c`
  replays IFCG47 §2's skeleton against the Bézout transport.
* **§7 THE RESIDUAL-BOX TRANSFER CRITERION (RB), PROVED.**  The design's "new proof
  obligation": `bez_transfer_digits_iff` — the C110 binomial replay with `π^{h(s−t)}`
  shifts (all terms at common height `h(k−t)`; the same binomial vanishing removes
  the lower combinations; the carry `q_i` cancels between the lattice supply and the
  box line at every slot `i ≥ 1`, and the `+1` at slot `0` is the digit pin) — and
  its sector-facing form `bez_xres_eq_pow_iff_box`, consuming IFCG44's landed
  `xres_eq_pow_iff_digits_h` for the residual side.  The box condition is
  BYTE-IDENTICAL to the Layer-2 Prop's hypothesis.  Plus the design §5 exponent
  identity `bez_box_exponent_identity`: `Σ λ_{t,i} = Σ⌈h(ek−j)/e⌉ + k` — the hostile
  test of every `+1` and carry convention, aligning the box cost with IFCG64's
  `card_slopeBox` exponent.

## Honest scope (the exact named remainder)

Per the design §8: the ONE literature-grade claim is `SlopeBezoutFactorCorrespondenceAt`
— it is STATED and CONSUMED conditionally here, never asserted.  CP2's current legs do
NOT certify it (leg E is the `h = 1` case, where all carries `q_i = 0` vanish and raw =
normalized; leg R decides squarefree residual blocks) — signing it as a fourth package
leg requires the design §8 dictionary audit against the source (the source's normalizer
must produce exactly `(q_i, r_i, δ_i)` and the transformed polynomial must be `bezDevT`,
not the raw scalar extension).  Deferred as named remainders: the `bezoutAlphaBox`
SUBSET of the transported `O'`-coordinates with its cardinality (Count) — the base-side
box (A), its criterion (RB), and its total exponent are all landed, so only the
`Res O' (e·N) ≅ (Res O N)^e` coordinate read of the set remains; the
`bezout_isIntegralClosure` certificate (presentational: injectivity, the fraction-field
pin (R3), and the full DVR stack are landed); and the `resPoly`-frame wrapper of (RB)
(the `xres` form is the census currency, per IFCG44).  No master row fires here:
IFCG62's honesty fence named "the analogues of `cellTransport`/`transport_decidedAt_iff`
at `h ≥ 2`" as the open set — THIS file supplies them at the `(h ≥ 2, d = 1)` axis
(count transport UNCONDITIONAL, decision transport conditional on exactly the named
Prop); the per-frame `MixedFaceLaw` discharges remain the counting campaign's, and the
`(h ≥ 2, d ≥ 2)` axis needs this file instantiated over the compositum ring (legal:
everything here is ∀-DVR, so `O := AdjoinRoot φ` fires verbatim).

## Axiom fence

Everything here is expected PURE Lean core `{propext, Classical.choice, Quot.sound}`
(the file only composes IFCG39/43/47/48's landed Lean-core material; the B.42/C.33
cites must NOT occur).  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Uniformity.Density.IFCG75

open IsLocalRing Polynomial
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG39 (eisKey eisKey_monic eisKey_natDegree eisKey_irreducible
  eis_root_pow eis_root_pow_dvd_mk_iff eis_isDomain eis_isLocalRing eis_maximalIdeal_eq
  eis_isDVR eis_map_pow_maximalIdeal eis_isAdicComplete eis_finite_residueField
  eis_residueCard devT reassT devT_coeff devT_monic devT_reassT reassT_devT reassT_monic)
open Uniformity.Density.IFCG43 (eisKey_neg eis_root_irreducible eis_recentring_stack)
open Uniformity.Density.IFCG47 (scaleType scaleType_injective CellTypeScalingAt)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt typeOf_eq_scaleType_of_rel)

attribute [local instance] Classical.propDecidable

/-! ## §1 — Bézout arithmetic: the pin `(B): a·h = b·e + 1` and the
multiplication-by-`h` permutation -/

section BezoutArith

/-- Positivity of both Bézout partners is forced by the pin. -/
theorem bezout_pos {h e a b : ℕ} (hB : a * h = b * e + 1) : 0 < a ∧ 0 < h := by
  constructor
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp at hB
    · exact ha
  · rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp at hB
    · exact hh

/-- Coprimality of `(h, e)` is forced by the pin (the design's hypothesis reduction:
`(B)` is the single trusted input). -/
theorem bezout_coprime {h e a b : ℕ} (hB : a * h = b * e + 1) : Nat.Coprime h e := by
  have h1 : Nat.gcd h e ∣ b * e + 1 := by
    rw [← hB]
    exact Dvd.dvd.mul_left (Nat.gcd_dvd_left h e) a
  have h2 : Nat.gcd h e ∣ b * e := Dvd.dvd.mul_left (Nat.gcd_dvd_right h e) b
  have h3 : Nat.gcd h e ∣ 1 := (Nat.dvd_add_right h2).mp h1
  exact Nat.eq_one_of_dvd_one h3

/-- **Existence of the positive Bézout pair**: for `gcd(h, e) = 1`, `e ≥ 2`, there are
`a ∈ {1, …, e−1}` and `b` with `a·h = b·e + 1` (the design's positive orientation —
no `±1` sign branch). -/
theorem bezout_exists {h e : ℕ} (he : 2 ≤ e) (hcop : Nat.Coprime h e) :
    ∃ a b : ℕ, 0 < a ∧ a < e ∧ a * h = b * e + 1 := by
  haveI : NeZero e := ⟨by omega⟩
  set A : (ZMod e)ˣ := (ZMod.unitOfCoprime h hcop)⁻¹ with hA
  set a : ℕ := (A : ZMod e).val with ha
  have halt : a < e := ZMod.val_lt _
  have hcast : ((a * h : ℕ) : ZMod e) = ((1 : ℕ) : ZMod e) := by
    rw [Nat.cast_mul, Nat.cast_one, ha, ZMod.natCast_val, ZMod.cast_id]
    have hh : (h : ZMod e) = ((ZMod.unitOfCoprime h hcop : (ZMod e)ˣ) : ZMod e) :=
      (ZMod.coe_unitOfCoprime h hcop).symm
    rw [hh, hA]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmod : (a * h) % e = 1 % e := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have h1e : 1 % e = 1 := Nat.mod_eq_of_lt (by omega)
  have hdm := Nat.div_add_mod (a * h) e
  refine ⟨a, a * h / e, ?_, halt, ?_⟩
  · by_cases ha0 : a = 0
    · rw [ha0, Nat.zero_mul, Nat.zero_mod, h1e] at hmod
      omega
    · exact Nat.pos_of_ne_zero ha0
  · rw [hmod, h1e] at hdm
    rw [Nat.mul_comm (a * h / e) e]
    omega

/-- Uniqueness of `a` in `{1, …, e−1}` (design §1). -/
theorem bezout_unique {h e a b a' b' : ℕ} (hB : a * h = b * e + 1)
    (hB' : a' * h = b' * e + 1) (hae : a < e) (hae' : a' < e) : a = a' := by
  -- `a ≡ a·(a'·h) = a'·(a·h) ≡ a' [MOD e]`
  have h1 : a * (a' * h) ≡ a * 1 [MOD e] := by
    rw [hB']
    exact Nat.ModEq.mul_left a (by
      show (b' * e + 1) % e = 1 % e
      rw [Nat.add_comm, Nat.add_mul_mod_self_right])
  have h2 : a' * (a * h) ≡ a' * 1 [MOD e] := by
    rw [hB]
    exact Nat.ModEq.mul_left a' (by
      show (b * e + 1) % e = 1 % e
      rw [Nat.add_comm, Nat.add_mul_mod_self_right])
  have h3 : a * (a' * h) = a' * (a * h) := by ring
  rw [Nat.mul_one] at h1 h2
  have h4 : a ≡ a' [MOD e] := by
    calc a ≡ a * (a' * h) [MOD e] := h1.symm
      _ = a' * (a * h) := h3
      _ ≡ a' [MOD e] := h2
  have h5 : a % e = a' % e := h4
  rwa [Nat.mod_eq_of_lt hae, Nat.mod_eq_of_lt hae'] at h5

/-- The kernel cancellation of the pin: `a·(h·i) ≡ i [MOD e]`. -/
theorem bezout_cancel {h e a b : ℕ} (hB : a * h = b * e + 1) (i : ℕ) :
    a * (h * i) ≡ i [MOD e] := by
  have h1 : a * (h * i) = i + (b * i) * e := by
    have h2 : a * (h * i) = (a * h) * i := by ring
    rw [h2, hB]
    ring
  show (a * (h * i)) % e = i % e
  rw [h1, Nat.add_mul_mod_self_right]

/-- ★ **The multiplication-by-`h` permutation, injectivity**: `i ↦ h·i % e` is
injective on `{0, …, e−1}` (the design §3's coordinate permutation). -/
theorem bezout_hmul_mod_injOn {h e a b : ℕ} (hB : a * h = b * e + 1)
    {i j : ℕ} (hi : i < e) (hj : j < e) (hij : h * i % e = h * j % e) : i = j := by
  have h1 : h * i ≡ h * j [MOD e] := hij
  have h2 : a * (h * i) ≡ a * (h * j) [MOD e] := Nat.ModEq.mul_left a h1
  have h3 : i ≡ j [MOD e] :=
    ((bezout_cancel hB i).symm.trans h2).trans (bezout_cancel hB j)
  have h4 : i % e = j % e := h3
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h4

/-- ★ **The multiplication-by-`h` permutation, the explicit inverse**: `j ↦ a·j % e`
inverts it — `h·(a·j % e) % e = j` for `j < e`. -/
theorem bezout_hmul_mod_surjOn {h e a b : ℕ} (hB : a * h = b * e + 1)
    {j : ℕ} (hj : j < e) : h * (a * j % e) % e = j := by
  have he : 0 < e := by omega
  have h1 : h * (a * j % e) ≡ h * (a * j) [MOD e] :=
    Nat.ModEq.mul_left h (Nat.mod_modEq (a * j) e)
  have h2 : h * (a * j) ≡ j [MOD e] := by
    have h3 : h * (a * j) = a * (h * j) := by ring
    rw [h3]
    exact bezout_cancel hB j
  have h4 : h * (a * j % e) ≡ j [MOD e] := h1.trans h2
  have h5 : h * (a * j % e) % e = j % e := h4
  rwa [Nat.mod_eq_of_lt hj] at h5

/-- **The carry shift** (the design §3's exponent arithmetic): for `s = e·q + r` with
`r < e`, the lattice ceiling at `r` less the carry `q` is the lattice ceiling at `s`:
`⌈(w − r)/e⌉⁺ − q = ⌈(w − s)/e⌉⁺` in the corpus's `(w + e − 1 − ·)/e` form. -/
theorem bezout_cceil_shift {e q r s w : ℕ} (he : 0 < e) (hs : s = e * q + r)
    (hr : r < e) : (w + e - 1 - r) / e - q = (w + e - 1 - s) / e := by
  subst hs
  generalize hA : e * q = A
  rcases Nat.le_total (A + r) (w + e - 1) with hWs | hWs
  · -- the generic stratum: `W − r = (W − (A + r)) + e·q`
    have h1 : w + e - 1 - r = (w + e - 1 - (A + r)) + e * q := by omega
    rw [h1, Nat.add_mul_div_left _ q he, Nat.add_sub_cancel]
  · -- the degenerate stratum: both sides are `0`
    have h0 : w + e - 1 - (A + r) = 0 := by omega
    rw [h0, Nat.zero_div]
    have h1 : w + e - 1 - r ≤ e * q := by omega
    have h3 := Nat.div_le_div_right (c := e) h1
    rw [Nat.mul_div_cancel_left q he] at h3
    exact Nat.sub_eq_zero_of_le h3

/-- **The level collapse**: at `w = e·N` every slot's ceiling is exactly `N`
(IFCG39's `hexp` idiom, exported). -/
theorem bezout_cceil_level {e r N : ℕ} (he : 0 < e) (hr : r < e) :
    (e * N + e - 1 - r) / e = N := by
  have h1 : e * N + e - 1 - r = e * N + (e - 1 - r) := by
    generalize e * N = A
    omega
  rw [h1, Nat.mul_add_div he, Nat.div_eq_of_lt (by omega : e - 1 - r < e)]
  omega

end BezoutArith

/-! ## §2 — the Bézout presentation: the Eisenstein target ring `O'` and the pins (R)

The recentring DVR for slope `h/e` is `O' := AdjoinRoot (eisKey π (−(u^a)) e)` — the
presentation `O[Y]/(Y^e − u^a·π)` of the design.  Because the key IS an IFCG39
Eisenstein key (at the unit parameter `−u^a`), the ENTIRE landed cascade
(`eis_isDomain/isLocalRing/isDVR/isAdicComplete/finite_residueField/residueCard/
map_pow_maximalIdeal/root_pow_dvd_mk_iff` and IFCG43's `eis_root_irreducible`,
`cellTransport`, …) instantiates verbatim; nothing is re-proved here.  The claims
`AdjoinRoot (X^e − C(u·π^h))` is a DVR / local / complete are deliberately ABSENT:
they are FALSE for `h ≥ 2`. -/

section Presentation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {u : Oˣ} {a b h e : ℕ}

/-- A unit has nonzero residue (kit). -/
theorem residue_ne_zero_of_isUnit {x : O} (hx : IsUnit x) :
    IsLocalRing.residue O x ≠ 0 := by
  intro h0
  exact mem_nonunits_iff.mp
    ((IsLocalRing.mem_maximalIdeal x).mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)) hx

/-- The Eisenstein unit parameter `−u^a` has nonzero residue (the cascade's gate). -/
theorem bez_unit_residue_ne_zero (u : Oˣ) (a : ℕ) :
    IsLocalRing.residue O (-((u : O) ^ a)) ≠ 0 :=
  residue_ne_zero_of_isUnit ((u.isUnit.pow a).neg)

/-- Anti-drift pin: the Bézout key IS the design's normalized Eisenstein polynomial
`Y^e − u^a·π`. -/
theorem bezKey_eq (π : O) (u : Oˣ) (a e : ℕ) :
    eisKey π (-((u : O) ^ a)) e = Polynomial.X ^ e - Polynomial.C ((u : O) ^ a * π) :=
  eisKey_neg π ((u : O) ^ a) e

/-- **(R1)** `γ^e = u^a·π` — the root relation of the normalized presentation. -/
theorem bez_root_pow (he : 0 < e) :
    (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ e
      = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) ((u : O) ^ a * π) := by
  rw [eis_root_pow he, neg_mul, map_neg, neg_neg]

/-- ★ **THE BÉZOUT RECENTRING STACK** — the design's `bezout_recentring_stack`:
`O' = O[Y]/(Y^e − u^a·π)` is a complete DVR with finite residue field of UNCHANGED
cardinality (totally ramified of degree `e`) — IFCG43's `eis_recentring_stack`
instantiated at the unit parameter `−u^a`; a legal instantiation point for every
∀-DVR law family at the SAME `q`. -/
theorem bez_recentring_stack [IsAdicComplete (maximalIdeal O) O]
    [Finite (ResidueField O)] (hπ : Irreducible π) (u : Oˣ) (a : ℕ) (he : 2 ≤ e) :
    ∃ (_ : IsDomain (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))
      (_ : IsLocalRing (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))
      (_ : IsDiscreteValuationRing (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))
      (_ : Finite (ResidueField (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))),
      IsAdicComplete (maximalIdeal (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))
          (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
      ∧ residueCard (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) = residueCard O :=
  eis_recentring_stack π (-((u : O) ^ a)) hπ (bez_unit_residue_ne_zero u a) he

/-- ★ `γ` is irreducible in `O'` (the design's `bezout_root_irreducible`) —
IFCG43's `eis_root_irreducible`, instantiated. -/
theorem bez_root_irreducible [Finite (ResidueField O)]
    [IsDomain (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))]
    [Finite (ResidueField (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))]
    (hπ : Irreducible π) (he : 2 ≤ e) :
    Irreducible (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) :=
  eis_root_irreducible hπ (bez_unit_residue_ne_zero u a) he

/-- ★ Total ramification `(𝔪_O^K)·O' = 𝔪'^{e·K}` (the design's ramification pin) —
IFCG39's `eis_map_pow_maximalIdeal`, instantiated.  Together with `γ` irreducible this
is the integral form of `v(γ) = 1/e`, value group `(1/e)·ℤ`. -/
theorem bez_map_pow_maximalIdeal
    [IsLocalRing (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))]
    (hπ : Irreducible π) (he : 2 ≤ e) (K : ℕ) :
    ((maximalIdeal O) ^ K).map
        (algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))
      = (maximalIdeal (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))) ^ (e * K) :=
  eis_map_pow_maximalIdeal hπ (bez_unit_residue_ne_zero u a) he K

/-- **The Bézout element** `ξ = u^{−b}·γ^h` — the image of the raw-order root in the
normalized presentation.  Its valuation read is definitional: `ξ` is `u^{−b}·γ^h`, so
`v(ξ) = h·v(γ) = h/e` (the design's `bezout_values`, integral form). -/
def bezXi (π : O) (u : Oˣ) (a b h e : ℕ) :
    AdjoinRoot (eisKey π (-((u : O) ^ a)) e) :=
  algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) (((u⁻¹ : Oˣ) : O) ^ b)
    * (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ h

/-- Unit cancellation kit: `(u⁻¹)^n · u^n = 1` in `O`. -/
private theorem unit_inv_pow_mul_pow (u : Oˣ) (n : ℕ) :
    ((u⁻¹ : Oˣ) : O) ^ n * ((u : O)) ^ n = 1 := by
  rw [← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]

/-- **(R2)** `ξ^e = u·π^h` — the well-definedness identity of the order embedding:
the Bézout pin `a·h = b·e + 1` pays exactly one factor of the centre unit. -/
theorem bezXi_pow_e (hB : a * h = b * e + 1) (he : 0 < e) :
    bezXi π u a b h e ^ e
      = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) ((u : O) * π ^ h) := by
  have hO : (((u⁻¹ : Oˣ) : O) ^ b) ^ e * (((u : O) ^ a * π) ^ h)
      = (u : O) * π ^ h := by
    rw [← pow_mul, mul_pow, ← pow_mul, hB, pow_succ, ← mul_assoc, ← mul_assoc,
      unit_inv_pow_mul_pow, one_mul]
  calc bezXi π u a b h e ^ e
      = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
            ((((u⁻¹ : Oˣ) : O) ^ b) ^ e)
          * ((AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ e) ^ h := by
        rw [bezXi, mul_pow, ← map_pow]
        congr 1
        rw [← pow_mul, mul_comm h e, pow_mul]
    _ = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
          ((((u⁻¹ : Oˣ) : O) ^ b) ^ e * (((u : O) ^ a * π) ^ h)) := by
        rw [bez_root_pow he, ← map_pow, ← map_mul]
    _ = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) ((u : O) * π ^ h) := by
        rw [hO]

/-- **(R3)** `ξ^a = π^b·γ` — the fraction-field equality, concrete form
(the design's `bezout_fractionField_eq`: `γ = ξ^a / π^b`). -/
theorem bezXi_pow_a (hB : a * h = b * e + 1) (he : 0 < e) :
    bezXi π u a b h e ^ a
      = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) (π ^ b)
          * AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e) := by
  have hO : (((u⁻¹ : Oˣ) : O) ^ b) ^ a * (((u : O) ^ a * π) ^ b) = π ^ b := by
    rw [← pow_mul, mul_pow, ← pow_mul, ← mul_assoc, mul_comm b a,
      unit_inv_pow_mul_pow, one_mul]
  calc bezXi π u a b h e ^ a
      = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
            ((((u⁻¹ : Oˣ) : O) ^ b) ^ a)
          * (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (h * a) := by
        rw [bezXi, mul_pow, ← map_pow, ← pow_mul, ← pow_mul]
    _ = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
            ((((u⁻¹ : Oˣ) : O) ^ b) ^ a)
          * (((AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ e) ^ b
              * AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) := by
        rw [mul_comm h a, hB, pow_succ, mul_comm b e, pow_mul]
    _ = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
            ((((u⁻¹ : Oˣ) : O) ^ b) ^ a * (((u : O) ^ a * π) ^ b))
          * AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e) := by
        rw [bez_root_pow he, ← map_pow, ← mul_assoc, ← map_mul]
    _ = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) (π ^ b)
          * AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e) := by
        rw [hO]

end Presentation

/-! ## §3 — the raw order and the order embedding

`A := AdjoinRoot (bezRawKey π u h e)` is the raw slope-`h/e` order `O[x]/(x^e − u·π^h)`.
**The DVR/local/complete-DVR claims for `A` are deliberately ABSENT — they are FALSE
for `h ≥ 2`** (the design's §0 verdict; the order is not normal).  The design §3.3
obstruction: at `(h, e) = (2, 3)`, `x = γ²` and the class of `π^{N−1}·x²` is nonzero
mod `π^N·A` while its image is `π^{N−1}·γ⁴ = u^{a}·π^N·γ ≡ 0` mod `γ^{3N}` — the
induced map `A/π^N·A → O'/γ^{eN}` is NOT injective, so no count-preserving transport
exists through the raw ring map; only the §4 coordinate normalization `Θ` transports
the finite boxes. -/

section OrderEmbedding

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {u : Oˣ} {a b h e : ℕ}

/-- **The raw slope key** `κ = X^e − C(u·π^h)`. -/
def bezRawKey (π : O) (u : Oˣ) (h e : ℕ) : Polynomial O :=
  Polynomial.X ^ e - Polynomial.C ((u : O) * π ^ h)

theorem bezRawKey_monic (he : 0 < e) : (bezRawKey π u h e).Monic :=
  Polynomial.monic_X_pow_sub_C _ he.ne'

theorem bezRawKey_natDegree : (bezRawKey π u h e).natDegree = e := by
  rw [bezRawKey, Polynomial.natDegree_X_pow_sub_C]

/-- **The order embedding** `ι : A →+* O'`, characterized by `x ↦ ξ` — its
well-definedness is exactly (R2) `ξ^e = u·π^h`. -/
def bezOrderMap (π : O) (u : Oˣ) (a b h e : ℕ) (hB : a * h = b * e + 1)
    (he : 0 < e) :
    AdjoinRoot (bezRawKey π u h e) →+* AdjoinRoot (eisKey π (-((u : O) ^ a)) e) :=
  AdjoinRoot.lift (algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))
    (bezXi π u a b h e) (by
      rw [bezRawKey, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
        bezXi_pow_e hB he, sub_self])

theorem bezOrderMap_mk (hB : a * h = b * e + 1) (he : 0 < e) (P : Polynomial O) :
    bezOrderMap π u a b h e hB he (AdjoinRoot.mk (bezRawKey π u h e) P)
      = P.eval₂ (algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))
          (bezXi π u a b h e) := by
  rw [bezOrderMap, AdjoinRoot.lift_mk]

theorem bezOrderMap_root (hB : a * h = b * e + 1) (he : 0 < e) :
    bezOrderMap π u a b h e hB he (AdjoinRoot.root (bezRawKey π u h e))
      = bezXi π u a b h e := by
  rw [bezOrderMap, AdjoinRoot.lift_root]

theorem bezOrderMap_algebraMap (hB : a * h = b * e + 1) (he : 0 < e) (x : O) :
    bezOrderMap π u a b h e hB he
        (algebraMap O (AdjoinRoot (bezRawKey π u h e)) x)
      = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) x := by
  rw [AdjoinRoot.algebraMap_eq, bezOrderMap, AdjoinRoot.lift_of]

end OrderEmbedding

/-! ## §4 — the multiplication-by-`h` coordinate lattice -/

section CoordinateLattice

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {u : Oˣ} {a b h e : ℕ}

/-- **The coordinate unit** `δ_i = u^{a·q_i}·u^{−b·i}` (design §3), as a UNIT — the
design's `z^{a·q_i − b·i}` with the negative exponent handled in `Oˣ`. -/
def bezDelta (u : Oˣ) (a b h e i : ℕ) : Oˣ :=
  u ^ (a * (h * i / e)) * (u⁻¹ : Oˣ) ^ (b * i)

/-- The value of the coordinate unit in `O` (kit). -/
theorem bezDelta_val (u : Oˣ) (a b h e i : ℕ) :
    ((bezDelta u a b h e i : Oˣ) : O)
      = (u : O) ^ (a * (h * i / e)) * ((u⁻¹ : Oˣ) : O) ^ (b * i) := by
  rw [bezDelta, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]

/-- **(C1)** the coordinate calculation `ξ^i = δ_i·π^{q_i}·γ^{r_i}` with
`q_i = h·i / e`, `r_i = h·i % e` — for EVERY `i` (pure exponent arithmetic
from (B) and (R1)). -/
theorem bezXi_pow (hB : a * h = b * e + 1) (he : 0 < e) (i : ℕ) :
    bezXi π u a b h e ^ i
      = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
          (((bezDelta u a b h e i : Oˣ) : O) * π ^ (h * i / e))
        * (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (h * i % e) := by
  have hO : ((u⁻¹ : Oˣ) : O) ^ (b * i) * (((u : O) ^ a * π) ^ (h * i / e))
      = ((bezDelta u a b h e i : Oˣ) : O) * π ^ (h * i / e) := by
    rw [bezDelta_val, mul_pow, ← pow_mul]
    ring
  calc bezXi π u a b h e ^ i
      = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
            (((u⁻¹ : Oˣ) : O) ^ (b * i))
          * (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (h * i) := by
        rw [bezXi, mul_pow, ← map_pow, ← pow_mul, ← pow_mul]
    _ = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
            (((u⁻¹ : Oˣ) : O) ^ (b * i))
          * (((AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ e) ^ (h * i / e)
              * (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (h * i % e)) := by
        congr 1
        conv_lhs => rw [← Nat.div_add_mod (h * i) e]
        rw [pow_add, pow_mul]
    _ = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
            (((u⁻¹ : Oˣ) : O) ^ (b * i) * (((u : O) ^ a * π) ^ (h * i / e)))
          * (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (h * i % e) := by
        rw [bez_root_pow he, ← map_pow, ← mul_assoc, ← map_mul]
    _ = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
            (((bezDelta u a b h e i : Oˣ) : O) * π ^ (h * i / e))
          * (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (h * i % e) := by
        rw [hO]

/-! ### the permuted-sum kit and the lattice core -/

/-- Degree bound for permuted sums (kit). -/
private theorem perm_sum_degree_lt (he : 0 < e) (c : ℕ → O) :
    (∑ i ∈ Finset.range e,
        Polynomial.C (c i) * Polynomial.X ^ (h * i % e)).degree
      < ((e : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe e)]
  intro i _
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast Nat.mod_lt _ he

/-- The permuted-sum coefficient read (kit): the permutation collapses the sum to the
single term at `i₀`. -/
private theorem perm_sum_coeff (hB : a * h = b * e + 1) (he : 0 < e) (c : ℕ → O)
    {i₀ : ℕ} (hi₀ : i₀ < e) :
    (∑ i ∈ Finset.range e,
        Polynomial.C (c i) * Polynomial.X ^ (h * i % e)).coeff (h * i₀ % e)
      = c i₀ := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single i₀]
  · rw [if_pos rfl, mul_one]
  · intro i hi hne
    rw [if_neg, mul_zero]
    intro hcon
    exact hne (bezout_hmul_mod_injOn hB hi₀ (Finset.mem_range.mp hi) hcon).symm
  · intro hcon
    exact absurd (Finset.mem_range.mpr hi₀) hcon

/-- ★ **The permuted-coordinate lattice core**: IFCG39's Eisenstein lattice read
through the multiplication-by-`h` permutation — distinct `i`'s occupy distinct
`γ`-power coordinates, so the divisibility reads off coordinatewise. -/
private theorem bez_root_pow_dvd_mk_perm_iff (hπ : Irreducible π)
    (hB : a * h = b * e + 1) (he : 0 < e) (c : ℕ → O) (w : ℕ) :
    (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ w
        ∣ AdjoinRoot.mk (eisKey π (-((u : O) ^ a)) e)
            (∑ i ∈ Finset.range e, Polynomial.C (c i) * Polynomial.X ^ (h * i % e))
      ↔ ∀ i < e, π ^ ((w + e - 1 - h * i % e) / e) ∣ c i := by
  rw [eis_root_pow_dvd_mk_iff hπ (bez_unit_residue_ne_zero u a) he
    (perm_sum_degree_lt he c) w]
  constructor
  · intro hall i hi
    have h1 := hall (h * i % e) (Nat.mod_lt _ he)
    rwa [perm_sum_coeff hB he c hi] at h1
  · intro hall j hj
    have hi : a * j % e < e := Nat.mod_lt _ he
    have hji : h * (a * j % e) % e = j := bezout_hmul_mod_surjOn hB hj
    rw [← hji, perm_sum_coeff hB he c hi]
    exact hall _ hi

/-- Divisibility through a `π`-power cofactor (kit): `π^A ∣ x·π^q ⟺ π^{A−q} ∣ x`. -/
private theorem pow_dvd_mul_pow_iff (hπ0 : π ≠ 0) (x : O) (A q : ℕ) :
    π ^ A ∣ x * π ^ q ↔ π ^ (A - q) ∣ x := by
  rcases Nat.le_total A q with hAq | hAq
  · have h0 : A - q = 0 := by omega
    rw [h0, pow_zero]
    simp only [one_dvd, iff_true]
    exact dvd_mul_of_dvd_right (pow_dvd_pow π hAq) x
  · have hA : A = (A - q) + q := by omega
    conv_lhs => rw [hA, pow_add]
    exact mul_dvd_mul_iff_right (pow_ne_zero q hπ0)

/-- The eval₂ read of the order embedding on a degree-`< e` representative:
`ι(mk P) = mk (Σ_{i<e} C(P_i·δ_i·π^{q_i})·X^{r_i})` — the design's raw coordinate
form (§6.3's displayed map). -/
private theorem bezOrderMap_mk_eq_perm_sum (hB : a * h = b * e + 1) (he : 0 < e)
    {P : Polynomial O} (hPnat : P.natDegree < e) :
    bezOrderMap π u a b h e hB he (AdjoinRoot.mk (bezRawKey π u h e) P)
      = AdjoinRoot.mk (eisKey π (-((u : O) ^ a)) e)
          (∑ i ∈ Finset.range e,
            Polynomial.C (P.coeff i * (((bezDelta u a b h e i : Oˣ) : O)
              * π ^ (h * i / e))) * Polynomial.X ^ (h * i % e)) := by
  rw [bezOrderMap_mk hB he,
    Polynomial.eval₂_eq_sum_range' (n := e) _ hPnat (bezXi π u a b h e), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hC : ∀ y : O, AdjoinRoot.mk (eisKey π (-((u : O) ^ a)) e) (Polynomial.C y)
      = algebraMap O (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) y := fun y => rfl
  rw [map_mul, map_pow, AdjoinRoot.mk_X, hC, map_mul, bezXi_pow hB he i, ← mul_assoc]

/-- ★★ **(L-raw), the raw-order lattice** (design §3.1
`bezout_root_pow_dvd_orderMk_iff`): for `P` of degree `< e`,
`γ^w ∣ ι(mk P) ⟺ π^{⌈(w − h·i)/e⌉⁺} ∣ P_i` for every `i < e` — in the `i`-coordinate,
divisibility by `γ^w` is exactly `e·(v_π(P_i) + q_i) + r_i ≥ w`, i.e.
`e·v_π(P_i) + h·i ≥ w`; the units `δ_i` do not affect divisibility. -/
theorem bez_root_pow_dvd_orderMk_iff (hπ : Irreducible π)
    (hB : a * h = b * e + 1) (he : 0 < e) {P : Polynomial O}
    (hP : P.degree < ((e : ℕ) : WithBot ℕ)) (w : ℕ) :
    (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ w
        ∣ bezOrderMap π u a b h e hB he (AdjoinRoot.mk (bezRawKey π u h e) P)
      ↔ ∀ i < e, π ^ ((w + e - 1 - h * i) / e) ∣ P.coeff i := by
  have hPnat : P.natDegree < e := by
    rcases eq_or_ne P 0 with rfl | hne
    · rw [Polynomial.natDegree_zero]
      exact he
    · have h1 := hP
      rw [Polynomial.degree_eq_natDegree hne] at h1
      exact_mod_cast h1
  rw [bezOrderMap_mk_eq_perm_sum hB he hPnat,
    bez_root_pow_dvd_mk_perm_iff hπ hB he _ w]
  refine forall₂_congr fun i hi => ?_
  rw [← mul_assoc, pow_dvd_mul_pow_iff hπ.ne_zero _ _ _, Units.dvd_mul_right,
    bezout_cceil_shift he (Nat.div_add_mod (h * i) e).symm (Nat.mod_lt _ he)]

/-! ### the injectivity of the order embedding -/

/-- Degree-bounded representatives vanish when their class does (kit; IFCG39's
`eis_eq_zero_of_mk_eq_zero`, replicated at the Bézout unit). -/
private theorem bez_eq_zero_of_mk_eq_zero (he : 0 < e) {P : Polynomial O}
    (hP : P.degree < ((e : ℕ) : WithBot ℕ))
    (h0 : AdjoinRoot.mk (eisKey π (-((u : O) ^ a)) e) P = 0) : P = 0 := by
  by_contra hne
  refine AdjoinRoot.mk_ne_zero_of_degree_lt (eisKey_monic he) hne ?_ h0
  rw [Polynomial.degree_eq_natDegree (eisKey_monic he).ne_zero, eisKey_natDegree he]
  exact hP

/-- The canonical representative of an `AdjoinRoot` element has degree `< deg φ`
(kit; IFCG39's private, replicated). -/
private theorem degree_modByMonicHom_lt {φ : Polynomial O} (hφ : φ.Monic)
    (x : AdjoinRoot φ) :
    (AdjoinRoot.modByMonicHom hφ x).degree < φ.degree := by
  obtain ⟨Q, hQ⟩ := AdjoinRoot.mk_surjective x
  rw [← hQ, AdjoinRoot.modByMonicHom_mk]
  exact Polynomial.degree_modByMonic_lt Q hφ

/-- ★★ **The order embedding is INJECTIVE** (design
`bezout_orderEmbedding_injective`): a degree-`< e` relation among the powers of `ξ`
becomes, through the permutation `i ↦ h·i % e`, a relation among the free power basis
`1, γ, …, γ^{e−1}` — so all coefficients vanish. -/
theorem bezOrderMap_injective (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 0 < e) : Function.Injective (bezOrderMap π u a b h e hB he) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- the canonical degree-`< e` representative
  have hmk : AdjoinRoot.mk (bezRawKey π u h e)
      (AdjoinRoot.modByMonicHom (bezRawKey_monic he) x) = x :=
    AdjoinRoot.mk_leftInverse (bezRawKey_monic he) x
  set P : Polynomial O := AdjoinRoot.modByMonicHom (bezRawKey_monic he) x with hPdef
  have hPdeg : P.degree < ((e : ℕ) : WithBot ℕ) := by
    have h1 := degree_modByMonicHom_lt (bezRawKey_monic he) x
    rwa [Polynomial.degree_eq_natDegree (bezRawKey_monic he).ne_zero,
      bezRawKey_natDegree] at h1
  have hPnat : P.natDegree < e := by
    rcases eq_or_ne P 0 with h0 | hne
    · rw [h0, Polynomial.natDegree_zero]
      exact he
    · have h1 := hPdeg
      rw [Polynomial.degree_eq_natDegree hne] at h1
      exact_mod_cast h1
  -- its image is the permuted sum; class zero forces the sum polynomial to vanish
  have himg : AdjoinRoot.mk (eisKey π (-((u : O) ^ a)) e)
      (∑ i ∈ Finset.range e,
        Polynomial.C (P.coeff i * (((bezDelta u a b h e i : Oˣ) : O)
          * π ^ (h * i / e))) * Polynomial.X ^ (h * i % e)) = 0 := by
    rw [← bezOrderMap_mk_eq_perm_sum hB he hPnat, hmk]
    exact hx
  have hsum0 := bez_eq_zero_of_mk_eq_zero he (perm_sum_degree_lt he _) himg
  -- coordinatewise vanishing through the permutation read
  have hcoeff : ∀ i < e, P.coeff i = 0 := by
    intro i hi
    have h1 : P.coeff i * (((bezDelta u a b h e i : Oˣ) : O) * π ^ (h * i / e)) = 0 := by
      have h2 := perm_sum_coeff hB he
        (fun i => P.coeff i * (((bezDelta u a b h e i : Oˣ) : O) * π ^ (h * i / e))) hi
      rw [hsum0, Polynomial.coeff_zero] at h2
      exact h2.symm
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact h3
    · exact absurd h3 (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ hπ.ne_zero))
  -- hence the representative, hence the class
  have hP0 : P = 0 := by
    refine Polynomial.ext fun i => ?_
    rcases Nat.lt_or_ge i e with hi | hi
    · rw [hcoeff i hi, Polynomial.coeff_zero]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.coeff_zero]
  rw [← hmk, hP0, map_zero]

/-! ### the Bézout coordinate normalization `Θ` (C2) and its lattice -/

/-- The Bézout key's degree (kit). -/
private theorem bez_eisKey_degree (he : 0 < e) :
    (eisKey π (-((u : O) ^ a)) e).degree = ((e : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (eisKey_monic he).ne_zero, eisKey_natDegree he]

/-- Plain-sum degree bound (kit). -/
private theorem plain_sum_degree_lt (he : 0 < e) (c : ℕ → O) :
    (∑ i ∈ Finset.range e, Polynomial.C (c i) * Polynomial.X ^ i).degree
      < ((e : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe e)]
  intro i hi
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast Finset.mem_range.mp hi

/-- Plain-sum coefficient read (kit). -/
private theorem plain_sum_coeff (c : ℕ → O) {j : ℕ} (hj : j < e) :
    (∑ i ∈ Finset.range e, Polynomial.C (c i) * Polynomial.X ^ i).coeff j = c j := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
  · intro i _ hne
    rw [if_neg (fun hcon => hne hcon.symm), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_range.mpr hj) hcon

/-- **(C2) The Bézout coordinate normalization**
`Θ(Σ p_i X^i) = Σ p_i·δ_i·γ^{r_i}` — the design's `O`-linear equivalence from the
rank-`e` coordinate module of the order to `O'`.  Deliberately NOT a ring
homomorphism: the carry factors `π^{q_i}` of the raw embedding (§6.3 of the design)
are REMOVED, which is exactly what makes the finite level boxes correspond. -/
def bezTheta (π : O) (u : Oˣ) (a b h e : ℕ) (P : Polynomial O) :
    AdjoinRoot (eisKey π (-((u : O) ^ a)) e) :=
  AdjoinRoot.mk (eisKey π (-((u : O) ^ a)) e)
    (∑ i ∈ Finset.range e,
      Polynomial.C (P.coeff i * ((bezDelta u a b h e i : Oˣ) : O))
        * Polynomial.X ^ (h * i % e))

/-- `Θ` is additive on differences (the `O`-linearity used by the level bookkeeping). -/
theorem bezTheta_sub (P P' : Polynomial O) :
    bezTheta π u a b h e P - bezTheta π u a b h e P'
      = bezTheta π u a b h e (P - P') := by
  rw [bezTheta, bezTheta, bezTheta, ← map_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_mul, ← Polynomial.C_sub, ← sub_mul, ← Polynomial.coeff_sub]

/-- `Θ(1) = 1` (the monicity carrier: `δ_0 = 1`, `r_0 = 0`). -/
theorem bezTheta_one (he : 0 < e) : bezTheta π u a b h e (1 : Polynomial O) = 1 := by
  rw [bezTheta]
  have hsum : (∑ i ∈ Finset.range e,
      Polynomial.C ((1 : Polynomial O).coeff i * ((bezDelta u a b h e i : Oˣ) : O))
        * Polynomial.X ^ (h * i % e)) = 1 := by
    rw [Finset.sum_eq_single 0]
    · rw [Polynomial.coeff_one_zero, bezDelta_val, Nat.mul_zero, Nat.zero_div,
        Nat.mul_zero, Nat.zero_mod, Nat.mul_zero, pow_zero, pow_zero, pow_zero,
        one_mul, one_mul, mul_one]
      exact Polynomial.C_1
    · intro i _ hne
      rw [Polynomial.coeff_one, if_neg (fun hcon => hne hcon), zero_mul,
        Polynomial.C_0, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_range.mpr he) hcon
  rw [hsum, map_one]

/-- **The inverse normalization** `Θ⁻¹`: read the canonical degree-`< e`
representative, un-permute the coordinates, and strip the units. -/
def bezThetaInv (π : O) (u : Oˣ) (a b h e : ℕ) (he : 0 < e)
    (y : AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) : Polynomial O :=
  ∑ i ∈ Finset.range e,
    Polynomial.C ((AdjoinRoot.modByMonicHom (eisKey_monic he) y).coeff (h * i % e)
        * (((bezDelta u a b h e i)⁻¹ : Oˣ) : O))
      * Polynomial.X ^ i

theorem bezThetaInv_degree_lt (he : 0 < e)
    (y : AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) :
    (bezThetaInv π u a b h e he y).degree < ((e : ℕ) : WithBot ℕ) :=
  plain_sum_degree_lt he _

/-- `Θ⁻¹` is additive on differences. -/
theorem bezThetaInv_sub (he : 0 < e)
    (y y' : AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) :
    bezThetaInv π u a b h e he y - bezThetaInv π u a b h e he y'
      = bezThetaInv π u a b h e he (y - y') := by
  rw [bezThetaInv, bezThetaInv, bezThetaInv, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_mul, ← Polynomial.C_sub, ← sub_mul, ← Polynomial.coeff_sub, ← map_sub]

/-- **Round trip 1**: `Θ⁻¹ ∘ Θ = id` on degree-`< e` representatives. -/
theorem bezThetaInv_bezTheta (hB : a * h = b * e + 1) (he : 0 < e)
    {P : Polynomial O} (hP : P.degree < ((e : ℕ) : WithBot ℕ)) :
    bezThetaInv π u a b h e he (bezTheta π u a b h e P) = P := by
  have hR : AdjoinRoot.modByMonicHom (eisKey_monic he) (bezTheta π u a b h e P)
      = ∑ i ∈ Finset.range e,
          Polynomial.C (P.coeff i * ((bezDelta u a b h e i : Oˣ) : O))
            * Polynomial.X ^ (h * i % e) := by
    rw [bezTheta, AdjoinRoot.modByMonicHom_mk]
    refine (Polynomial.modByMonic_eq_self_iff (eisKey_monic he)).mpr ?_
    rw [bez_eisKey_degree he]
    exact perm_sum_degree_lt he _
  refine Polynomial.ext fun i => ?_
  rcases Nat.lt_or_ge i e with hi | hi
  · rw [bezThetaInv, plain_sum_coeff _ hi, hR, perm_sum_coeff hB he _ hi, mul_assoc]
    have hcancel : (((bezDelta u a b h e i : Oˣ) : O)
        * (((bezDelta u a b h e i)⁻¹ : Oˣ) : O)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hcancel, mul_one]
  · rw [Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le (bezThetaInv_degree_lt he _) (by exact_mod_cast hi)),
      Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hP (by exact_mod_cast hi))]

/-- **Round trip 2**: `Θ ∘ Θ⁻¹ = id` on `O'` — the permutation resummation. -/
theorem bezTheta_bezThetaInv (hB : a * h = b * e + 1) (he : 0 < e)
    (y : AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) :
    bezTheta π u a b h e (bezThetaInv π u a b h e he y) = y := by
  set Q : Polynomial O := AdjoinRoot.modByMonicHom (eisKey_monic he) y with hQdef
  have hQnat : Q.natDegree < e := by
    have hQdeg : Q.degree < ((e : ℕ) : WithBot ℕ) := by
      have h1 := degree_modByMonicHom_lt (eisKey_monic he) y
      rwa [bez_eisKey_degree he] at h1
    rcases eq_or_ne Q 0 with h0 | hne
    · rw [h0, Polynomial.natDegree_zero]
      exact he
    · have h1 := hQdeg
      rw [Polynomial.degree_eq_natDegree hne] at h1
      exact_mod_cast h1
  have hcoeff : ∀ i, i < e → (bezThetaInv π u a b h e he y).coeff i
      = Q.coeff (h * i % e) * (((bezDelta u a b h e i)⁻¹ : Oˣ) : O) := by
    intro i hi
    rw [bezThetaInv, plain_sum_coeff _ hi]
  rw [bezTheta]
  have hterm : ∀ i ∈ Finset.range e,
      Polynomial.C ((bezThetaInv π u a b h e he y).coeff i
          * ((bezDelta u a b h e i : Oˣ) : O)) * Polynomial.X ^ (h * i % e)
        = Polynomial.C (Q.coeff (h * i % e)) * Polynomial.X ^ (h * i % e) := by
    intro i hi
    rw [hcoeff i (Finset.mem_range.mp hi), mul_assoc]
    have hcancel : ((((bezDelta u a b h e i)⁻¹ : Oˣ) : O)
        * ((bezDelta u a b h e i : Oˣ) : O)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hcancel, mul_one]
  have hresum : ∑ i ∈ Finset.range e,
      Polynomial.C (Q.coeff (h * i % e)) * Polynomial.X ^ (h * i % e)
        = ∑ j ∈ Finset.range e, Polynomial.C (Q.coeff j) * Polynomial.X ^ j := by
    refine Finset.sum_nbij' (fun i => h * i % e) (fun j => a * j % e) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_range.mpr (Nat.mod_lt _ he)
    · intro j hj
      exact Finset.mem_range.mpr (Nat.mod_lt _ he)
    · intro i hi
      -- `a·(h·i % e) % e = i`: the inverse permutation on the left
      have hi' := Finset.mem_range.mp hi
      have h1 : a * (h * i % e) ≡ a * (h * i) [MOD e] :=
        Nat.ModEq.mul_left a (Nat.mod_modEq (h * i) e)
      have h2 : a * (h * i % e) % e = i % e := h1.trans (bezout_cancel hB i)
      exact h2.trans (Nat.mod_eq_of_lt hi')
    · intro j hj
      exact bezout_hmul_mod_surjOn hB (Finset.mem_range.mp hj)
    · intro i hi
      rfl
  have hQsum : ∑ j ∈ Finset.range e, Polynomial.C (Q.coeff j) * Polynomial.X ^ j
      = Q := by
    conv_rhs => rw [Polynomial.as_sum_range' Q e (by omega)]
    exact Finset.sum_congr rfl fun j _ => Polynomial.C_mul_X_pow_eq_monomial
  rw [Finset.sum_congr rfl hterm, hresum, hQsum, hQdef]
  exact AdjoinRoot.mk_leftInverse (eisKey_monic he) y

/-- ★★ **(L-norm)**: the normalized lattice — `γ^w ∣ Θ(P) ⟺ π^{⌈(w − r_i)/e⌉⁺} ∣ P_i`
for every `i < e` (no carry: the design's (L-norm)). -/
theorem bez_root_pow_dvd_theta_iff (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 0 < e) (P : Polynomial O) (w : ℕ) :
    (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ w ∣ bezTheta π u a b h e P
      ↔ ∀ i < e, π ^ ((w + e - 1 - h * i % e) / e) ∣ P.coeff i := by
  rw [bezTheta, bez_root_pow_dvd_mk_perm_iff hπ hB he _ w]
  refine forall₂_congr fun i hi => ?_
  rw [Units.dvd_mul_right]

/-- ★★ **(L-level)**: the level-exact specialization — `γ^{e·N} ∣ Θ(P) ⟺ π^N ∣ P_i`
for every `i < e`.  THIS is what lets `Θ` (and not the ring embedding `ι`) support a
bijection of the ordinary finite coefficient boxes. -/
theorem bez_theta_level_iff (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 0 < e) (P : Polynomial O) (N : ℕ) :
    (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (e * N)
        ∣ bezTheta π u a b h e P
      ↔ ∀ i < e, π ^ N ∣ P.coeff i := by
  rw [bez_root_pow_dvd_theta_iff hπ hB he P (e * N)]
  refine forall₂_congr fun i hi => ?_
  rw [bezout_cceil_level he (Nat.mod_lt _ he)]

end CoordinateLattice

/-! ## §5 — the normalized development and its level exactness

`bezDevT` is the design's (D): the `bezRawKey`-adic development read through `Θ`
coefficientwise — NOT through the ring embedding `ι` (whose carry factors `π^{q_i}`
break inbound level exactness; the design's §7 table records the raw-embedding version
of the level lemmas as FALSE in equivalence form). -/

section NormalizedDev

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {u : Oˣ} {a b h e k : ℕ}

theorem bezRawKey_degree (he : 0 < e) :
    (bezRawKey π u h e).degree = ((e : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_eq_natDegree (bezRawKey_monic he).ne_zero, bezRawKey_natDegree]

/-- The zero slot of the coordinate unit (kit). -/
theorem bezDelta_zero (u : Oˣ) (a b h e : ℕ) : bezDelta u a b h e 0 = 1 := by
  simp [bezDelta]

/-- **The normalized development transform** (design (D)):
`bezDevT f = Σ_{t ≤ k} Θ(dev_κ f t)·T^t`. -/
def bezDevT (π : O) (u : Oˣ) (a b h e k : ℕ) (f : Polynomial O) :
    Polynomial (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) :=
  ∑ t ∈ Finset.range (k + 1),
    Polynomial.C (bezTheta π u a b h e (dev (bezRawKey π u h e) f t))
      * Polynomial.X ^ t

/-- **The normalized reassembly**: `Θ⁻¹` coefficientwise against the powers of `κ`. -/
def bezReassT (π : O) (u : Oˣ) (a b h e : ℕ) (he : 0 < e) (k : ℕ)
    (G : Polynomial (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))) : Polynomial O :=
  ∑ t ∈ Finset.range (k + 1),
    (bezThetaInv π u a b h e he (G.coeff t)) * (bezRawKey π u h e) ^ t

theorem bezDevT_coeff (f : Polynomial O) {j : ℕ} (hj : j ≤ k) :
    (bezDevT π u a b h e k f).coeff j
      = bezTheta π u a b h e (dev (bezRawKey π u h e) f j) := by
  rw [bezDevT, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
  · intro i _ hne
    rw [if_neg (fun hcon => hne hcon.symm), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_range.mpr (by omega)) hcon

private theorem bezDevT_natDegree_le (f : Polynomial O) :
    (bezDevT π u a b h e k f).natDegree ≤ k := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  exact le_trans (Polynomial.natDegree_monomial_le _)
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- `1 ≠ 0` in the recentring ring (kit). -/
private theorem bez_one_ne_zero (he : 0 < e) :
    (1 : AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) ≠ 0 := by
  intro h1
  have h2 : (eisKey π (-((u : O) ^ a)) e) ∣ 1 := by
    rw [← AdjoinRoot.mk_eq_zero, map_one]
    exact h1
  have h3 := Polynomial.natDegree_le_of_dvd h2 one_ne_zero
  rw [Polynomial.natDegree_one, eisKey_natDegree he] at h3
  omega

/-- ★ The transform of a monic degree-`e·k` block is monic of degree `k`
(`Θ(1) = 1` carries the top). -/
theorem bezDevT_monic (he : 0 < e) {f : Polynomial O} (hf : f.Monic)
    (hdeg : f.natDegree = e * k) :
    (bezDevT π u a b h e k f).Monic ∧ (bezDevT π u a b h e k f).natDegree = k := by
  have hDpos : 0 < (bezRawKey π u h e).natDegree := by
    rw [bezRawKey_natDegree]
    exact he
  have htop : (bezDevT π u a b h e k f).coeff k = 1 := by
    rw [bezDevT_coeff f (le_refl k),
      dev_top (μ := k) (bezRawKey_monic he) hDpos hf
        (by rw [hdeg, bezRawKey_natDegree, Nat.mul_comm]),
      bezTheta_one he]
  have hmon : (bezDevT π u a b h e k f).Monic :=
    Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ (bezDevT_natDegree_le f) htop
  refine ⟨hmon,
    le_antisymm (bezDevT_natDegree_le f) (Polynomial.le_natDegree_of_ne_zero ?_)⟩
  rw [htop]
  exact bez_one_ne_zero he

/-- ★ **Round trip, outbound** (`bezDevT_bezReassT`): the transform of the
reassembly is the identity on degree-`≤ k` polynomials over `O'`. -/
theorem bezDevT_bezReassT (hB : a * h = b * e + 1) (he : 0 < e)
    {G : Polynomial (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))}
    (hG : G.natDegree ≤ k) :
    bezDevT π u a b h e k (bezReassT π u a b h e he k G) = G := by
  have hDpos : 0 < (bezRawKey π u h e).natDegree := by
    rw [bezRawKey_natDegree]
    exact he
  have hdig : ∀ j < k + 1,
      bezThetaInv π u a b h e he (G.coeff j)
        = dev (bezRawKey π u h e) (bezReassT π u a b h e he k G) j :=
    dev_unique (bezRawKey_monic he) hDpos
      (fun j => by
        rw [bezRawKey_degree he]
        exact bezThetaInv_degree_lt he (G.coeff j)) rfl
  refine Polynomial.ext fun j => ?_
  by_cases hj : j ≤ k
  · rw [bezDevT_coeff _ hj, ← hdig j (by omega), bezTheta_bezThetaInv hB he]
  · rw [not_le] at hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (bezDevT_natDegree_le _) hj),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hG hj)]

/-- ★ **Round trip, inbound** (`bezReassT_bezDevT`): the reassembly of the transform
is the identity on degree-`< (k+1)·e` blocks over `O`. -/
theorem bezReassT_bezDevT (hB : a * h = b * e + 1) (he : 0 < e)
    {f : Polynomial O} (hdeg : f.natDegree < (k + 1) * e) :
    bezReassT π u a b h e he k (bezDevT π u a b h e k f) = f := by
  have hDpos : 0 < (bezRawKey π u h e).natDegree := by
    rw [bezRawKey_natDegree]
    exact he
  have h1 : ∀ j ∈ Finset.range (k + 1),
      (bezThetaInv π u a b h e he ((bezDevT π u a b h e k f).coeff j))
          * (bezRawKey π u h e) ^ j
        = dev (bezRawKey π u h e) f j * (bezRawKey π u h e) ^ j := by
    intro j hj
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [bezDevT_coeff f hj', bezThetaInv_bezTheta hB he
      (by
        have h2 := degree_dev_lt (bezRawKey_monic he) hDpos f j
        rwa [bezRawKey_degree he] at h2)]
  rw [bezReassT, Finset.sum_congr rfl h1,
    sum_dev_eq (bezRawKey_monic he) hDpos f (by rwa [bezRawKey_natDegree])]

/-- `Θ⁻¹(1) = 1` (kit for the reassembly's monicity). -/
theorem bezThetaInv_one (hB : a * h = b * e + 1) (he : 0 < e) :
    bezThetaInv π u a b h e he
        (1 : AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) = 1 := by
  have hmod : AdjoinRoot.modByMonicHom (eisKey_monic he)
      (1 : AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) = 1 := by
    rw [show (1 : AdjoinRoot (eisKey π (-((u : O) ^ a)) e))
        = AdjoinRoot.mk (eisKey π (-((u : O) ^ a)) e) 1 from (map_one _).symm,
      AdjoinRoot.modByMonicHom_mk]
    refine (Polynomial.modByMonic_eq_self_iff (eisKey_monic he)).mpr ?_
    rw [bez_eisKey_degree he, Polynomial.degree_one]
    exact_mod_cast he
  rw [bezThetaInv, hmod]
  rw [Finset.sum_eq_single 0]
  · rw [Nat.mul_zero, Nat.zero_mod, Polynomial.coeff_one_zero, bezDelta_zero,
      inv_one, Units.val_one, mul_one, pow_zero, mul_one, Polynomial.C_1]
  · intro i hi hne
    have hri : h * i % e ≠ 0 := by
      intro hcon
      refine hne (bezout_hmul_mod_injOn hB (Finset.mem_range.mp hi) he ?_)
      rw [hcon, Nat.mul_zero, Nat.zero_mod]
    rw [Polynomial.coeff_one, if_neg hri, zero_mul, Polynomial.C_0, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_range.mpr he) hcon

/-- ★ The reassembly of a monic degree-`k` polynomial over `O'` is monic of degree
`e·k`. -/
theorem bezReassT_monic (hB : a * h = b * e + 1) (he : 0 < e)
    {G : Polynomial (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))}
    (hG : G.Monic) (hGdeg : G.natDegree = k) :
    (bezReassT π u a b h e he k G).Monic
      ∧ (bezReassT π u a b h e he k G).natDegree = e * k := by
  have hak : bezThetaInv π u a b h e he (G.coeff k) = 1 := by
    have h1 : G.coeff k = 1 := by
      rw [← hGdeg]
      exact hG.coeff_natDegree
    rw [h1, bezThetaInv_one hB he]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h2 : bezReassT π u a b h e he 0 G = 1 := by
      rw [bezReassT, Finset.sum_range_one, pow_zero, mul_one, hak]
    rw [h2]
    exact ⟨Polynomial.monic_one, by rw [Polynomial.natDegree_one, Nat.mul_zero]⟩
  · have hsplit : bezReassT π u a b h e he k G
        = (∑ j ∈ Finset.range k,
            (bezThetaInv π u a b h e he (G.coeff j)) * (bezRawKey π u h e) ^ j)
          + (bezRawKey π u h e) ^ k := by
      rw [bezReassT, Finset.sum_range_succ, hak, one_mul]
    have hDdeg : (bezRawKey π u h e).natDegree = e := bezRawKey_natDegree
    have hkD : 0 < k * e := Nat.mul_pos hk he
    have ha : ∀ y : AdjoinRoot (eisKey π (-((u : O) ^ a)) e),
        (bezThetaInv π u a b h e he y).natDegree ≤ e - 1 := by
      intro y
      by_cases hy : bezThetaInv π u a b h e he y = 0
      · rw [hy, Polynomial.natDegree_zero]
        omega
      · have h3 : (bezThetaInv π u a b h e he y).natDegree < e := by
          have h4 := bezThetaInv_degree_lt (π := π) (u := u) (a := a) (b := b)
            (h := h) he y
          rw [Polynomial.degree_eq_natDegree hy] at h4
          exact_mod_cast h4
        omega
    have htail : (∑ j ∈ Finset.range k,
        (bezThetaInv π u a b h e he (G.coeff j)) * (bezRawKey π u h e) ^ j).natDegree
          ≤ k * e - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
      have hj' : j < k := Finset.mem_range.mp hj
      refine le_trans Polynomial.natDegree_mul_le ?_
      have h4 : ((bezRawKey π u h e) ^ j).natDegree = j * e := by
        rw [(bezRawKey_monic he).natDegree_pow, hDdeg]
      have h5 : j * e ≤ (k - 1) * e := Nat.mul_le_mul (by omega) (le_refl _)
      have h6 : (k - 1) * e = k * e - e := by
        rw [Nat.sub_mul, Nat.one_mul]
      have h7 := ha (G.coeff j)
      have h8 : e ≤ k * e := Nat.le_mul_of_pos_left _ hk
      rw [h4]
      omega
    have hmono : ((bezRawKey π u h e) ^ k).Monic := (bezRawKey_monic he).pow k
    have hdlt : (∑ j ∈ Finset.range k,
        (bezThetaInv π u a b h e he (G.coeff j)) * (bezRawKey π u h e) ^ j).degree
          < ((bezRawKey π u h e) ^ k).degree := by
      have h9 : ((bezRawKey π u h e) ^ k).degree = ((k * e : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hmono.ne_zero,
          (bezRawKey_monic he).natDegree_pow, hDdeg]
      rw [h9]
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      exact_mod_cast lt_of_le_of_lt htail (by omega)
    rw [hsplit]
    refine ⟨Polynomial.Monic.add_of_right hmono hdlt, ?_⟩
    rw [Polynomial.natDegree_add_eq_right_of_degree_lt hdlt,
      (bezRawKey_monic he).natDegree_pow, hDdeg, Nat.mul_comm]

/-- ★★ **Level exactness, outbound**: blocks congruent coefficientwise mod `π^N`
over `O` have transforms congruent coefficientwise mod `γ^{e·N}` over `O'` —
B.10's `dev_congr` composed with (L-level). -/
theorem bezDevT_sub_root_pow_dvd (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 0 < e) {N : ℕ} {f f' : Polynomial O}
    (hcong : ∀ l, π ^ N ∣ (f - f').coeff l) {j : ℕ} (hj : j ≤ k) :
    (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (e * N)
      ∣ (bezDevT π u a b h e k f - bezDevT π u a b h e k f').coeff j := by
  rw [Polynomial.coeff_sub, bezDevT_coeff f hj, bezDevT_coeff f' hj, bezTheta_sub]
  refine (bez_theta_level_iff hπ hB he _ N).mpr ?_
  intro i _
  exact dev_congr hπ (bezRawKey_monic he) hcong j i

/-- ★★ **Level exactness, inbound**: transforms congruent coefficientwise mod
`γ^{e·N}` reassemble to blocks congruent coefficientwise mod `π^N` — the reverse
direction of (L-level) on `Θ⁻¹`. -/
theorem bezReassT_sub_pi_pow_dvd (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 0 < e) {N : ℕ}
    {G G' : Polynomial (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))}
    (hcong : ∀ j, (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (e * N)
        ∣ (G - G').coeff j) (l : ℕ) :
    π ^ N ∣ (bezReassT π u a b h e he k G - bezReassT π u a b h e he k G').coeff l := by
  have hsub : bezReassT π u a b h e he k G - bezReassT π u a b h e he k G'
      = ∑ j ∈ Finset.range (k + 1),
          (bezThetaInv π u a b h e he ((G - G').coeff j)) * (bezRawKey π u h e) ^ j := by
    rw [bezReassT, bezReassT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_mul, bezThetaInv_sub, ← Polynomial.coeff_sub]
  rw [hsub, Polynomial.finsetSum_coeff]
  refine Finset.dvd_sum fun j _ => ?_
  have hrep : ∀ i, π ^ N ∣ (bezThetaInv π u a b h e he ((G - G').coeff j)).coeff i := by
    have hθ : (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) ^ (e * N)
        ∣ bezTheta π u a b h e (bezThetaInv π u a b h e he ((G - G').coeff j)) := by
      rw [bezTheta_bezThetaInv hB he]
      exact hcong j
    have h1 := (bez_theta_level_iff hπ hB he _ N).mp hθ
    intro i
    rcases Nat.lt_or_ge i e with hi | hi
    · exact h1 i hi
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le (bezThetaInv_degree_lt he _) (by exact_mod_cast hi))]
      exact dvd_zero _
  exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mp
    (Dvd.dvd.mul_right ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hrep) _) l

end NormalizedDev

/-! ## §5b — THE FINITE CELL TRANSPORT (T): the normalized transform descends to the
coefficient boxes, count-preservingly — IFCG43 §2's skeleton against `bezDevT` -/

section CellTransport

/-- Level-`N` class equality IS `ϖ^N`-divisibility of the difference (IFCG43's
private, replicated generically). -/
private theorem res_mk_eq_iff {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) {N : ℕ} {x y : R} :
    Ideal.Quotient.mk ((maximalIdeal R) ^ N) x
        = Ideal.Quotient.mk ((maximalIdeal R) ^ N) y
      ↔ ϖ ^ N ∣ x - y := by
  rw [Ideal.Quotient.eq]
  exact mem_pow_maximalIdeal_iff hϖ N _

/-- `monicPoly` reads its own vector below the top (IFCG43's private, replicated). -/
private theorem monicPoly_coeff_lt {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {n : ℕ} (v : Fin n → R) {i : ℕ} (hi : i < n) :
    (monicPoly v).coeff i = v ⟨i, hi⟩ := by
  classical
  rw [monicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    if_neg (by omega : ¬ i = n), zero_add, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
  · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
  · intro c _ hc
    rw [Polynomial.coeff_C_mul_X_pow,
      if_neg (fun hcon => hc (Fin.val_injective hcon.symm))]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- A monic polynomial of degree `n` is `monicPoly` of its own low coefficient vector
(IFCG43's private, replicated). -/
private theorem monicPoly_coeff_self {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {n : ℕ} {f : Polynomial R} (hf : f.Monic)
    (hn : f.natDegree = n) : monicPoly (fun i : Fin n => f.coeff i.1) = f := by
  classical
  have hlead : f.coeff n = 1 := by
    rw [← hn]
    exact hf.coeff_natDegree
  refine Polynomial.ext fun m => ?_
  rcases lt_trichotomy m n with hm | hm | hm
  · rw [monicPoly_coeff_lt _ hm]
  · have h1 : (monicPoly (fun i : Fin n => f.coeff i.1)).coeff n = 1 := by
      have h2 := (monicPoly_monic (fun i : Fin n => f.coeff i.1)).coeff_natDegree
      rwa [monicPoly_natDegree] at h2
    rw [hm, h1, hlead]
  · have h1 : (monicPoly (fun i : Fin n => f.coeff i.1)).natDegree = n :=
      monicPoly_natDegree _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega :
        (monicPoly (fun i : Fin n => f.coeff i.1)).natDegree < m),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < m)]

/-- Class-equal coefficient vectors have `ϖ^N`-divisible monic-block differences at
EVERY slot (IFCG43's private, replicated). -/
private theorem pow_dvd_monicPoly_sub_coeff {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) {n N : ℕ}
    {v v' : Fin n → R} (hvv : proj R n N v = proj R n N v') (l : ℕ) :
    ϖ ^ N ∣ (monicPoly v - monicPoly v').coeff l := by
  rw [Polynomial.coeff_sub]
  rcases lt_trichotomy l n with hl | hl | hl
  · rw [monicPoly_coeff_lt v hl, monicPoly_coeff_lt v' hl]
    have hcl : Ideal.Quotient.mk ((maximalIdeal R) ^ N) (v ⟨l, hl⟩)
        = Ideal.Quotient.mk ((maximalIdeal R) ^ N) (v' ⟨l, hl⟩) :=
      congrFun hvv ⟨l, hl⟩
    exact (res_mk_eq_iff hϖ).mp hcl
  · subst hl
    have h1 : (monicPoly v).coeff l = 1 := by
      have := (monicPoly_monic v).coeff_natDegree
      rwa [monicPoly_natDegree] at this
    have h2 : (monicPoly v').coeff l = 1 := by
      have := (monicPoly_monic v').coeff_natDegree
      rwa [monicPoly_natDegree] at this
    rw [h1, h2, sub_self]
    exact dvd_zero _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
      sub_self]
    exact dvd_zero _

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {u : Oˣ} {a b h e : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))]
  [Finite (ResidueField O)]
  [Finite (ResidueField (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))]

/-- **The Bézout transform vector**: the `O'`-coordinates of the normalized transform
of the monic block with coefficient vector `v`. -/
def bezDevVec (π : O) (u : Oˣ) (a b h e k : ℕ) (v : Fin (e * k) → O) :
    Fin k → AdjoinRoot (eisKey π (-((u : O) ^ a)) e) :=
  fun j => (bezDevT π u a b h e k (monicPoly v)).coeff j.1

/-- **The Bézout reassembly vector**. -/
def bezReassVec (π : O) (u : Oˣ) (a b h e : ℕ) (he : 0 < e) (k : ℕ)
    (y : Fin k → AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) : Fin (e * k) → O :=
  fun i => (bezReassT π u a b h e he k (monicPoly y)).coeff i.1

/-- Level-`N` classes transport to level-`e·N` classes (outbound well-definedness). -/
private theorem bezDevVec_congr (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) {k N : ℕ} {v v' : Fin (e * k) → O}
    (hvv : proj O (e * k) N v = proj O (e * k) N v') :
    proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
        (bezDevVec π u a b h e k v)
      = proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
          (bezDevVec π u a b h e k v') := by
  have hα : Irreducible (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) :=
    bez_root_irreducible hπ he
  funext j
  have hdvd := bezDevT_sub_root_pow_dvd (u := u) (k := k) hπ hB
    (Nat.zero_lt_two.trans_le he) (N := N) (f := monicPoly v) (f' := monicPoly v')
    (fun l => pow_dvd_monicPoly_sub_coeff hπ hvv l) (j := j.1) j.isLt.le
  rw [Polynomial.coeff_sub] at hdvd
  exact (res_mk_eq_iff hα).mpr hdvd

/-- Level-`e·N` classes transport back to level-`N` classes (inbound
well-definedness). -/
private theorem bezReassVec_congr (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) {k N : ℕ}
    {y y' : Fin k → AdjoinRoot (eisKey π (-((u : O) ^ a)) e)}
    (hyy : proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N) y
        = proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N) y') :
    proj O (e * k) N (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y)
      = proj O (e * k) N (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y') := by
  have hα : Irreducible (AdjoinRoot.root (eisKey π (-((u : O) ^ a)) e)) :=
    bez_root_irreducible hπ he
  funext i
  have hdvd := bezReassT_sub_pi_pow_dvd (u := u) (k := k) hπ hB
    (Nat.zero_lt_two.trans_le he) (N := N) (G := monicPoly y) (G' := monicPoly y')
    (fun j => pow_dvd_monicPoly_sub_coeff hα hyy j) i.1
  rw [Polynomial.coeff_sub] at hdvd
  exact (res_mk_eq_iff hπ).mpr hdvd

/-- The exact round trip on canonical lifts, outbound-then-inbound. -/
private theorem bezReassVec_bezDevVec (hB : a * h = b * e + 1) (he : 2 ≤ e) (k : ℕ)
    (v : Fin (e * k) → O) :
    bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k
        (bezDevVec π u a b h e k v) = v := by
  have he' : 0 < e := Nat.zero_lt_two.trans_le he
  have hdeg : (monicPoly v).natDegree = e * k := monicPoly_natDegree v
  have hmon := bezDevT_monic (π := π) (u := u) (a := a) (b := b) (h := h)
    (k := k) he' (monicPoly_monic v) hdeg
  have hfun : monicPoly (bezDevVec π u a b h e k v)
      = bezDevT π u a b h e k (monicPoly v) :=
    monicPoly_coeff_self hmon.1 hmon.2
  have hlt : (monicPoly v).natDegree < (k + 1) * e := by
    rw [monicPoly_natDegree, Nat.add_mul, Nat.one_mul, Nat.mul_comm e k]
    generalize k * e = A
    omega
  funext i
  show (bezReassT π u a b h e (Nat.zero_lt_two.trans_le he) k
      (monicPoly (bezDevVec π u a b h e k v))).coeff i.1 = v i
  rw [hfun, bezReassT_bezDevT hB he' hlt]
  exact monicPoly_coeff_lt v i.isLt

/-- The exact round trip on canonical lifts, inbound-then-outbound. -/
private theorem bezDevVec_bezReassVec (hB : a * h = b * e + 1) (he : 2 ≤ e) (k : ℕ)
    (y : Fin k → AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) :
    bezDevVec π u a b h e k
        (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y) = y := by
  have he' : 0 < e := Nat.zero_lt_two.trans_le he
  have hre := bezReassT_monic (π := π) (u := u) (k := k) hB he'
    (monicPoly_monic y) (monicPoly_natDegree y)
  have hfun : monicPoly (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y)
      = bezReassT π u a b h e (Nat.zero_lt_two.trans_le he) k (monicPoly y) :=
    monicPoly_coeff_self hre.1 hre.2
  funext j
  show (bezDevT π u a b h e k
      (monicPoly (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y))).coeff j.1
    = y j
  rw [hfun, bezDevT_bezReassT hB he' (le_of_eq (monicPoly_natDegree y))]
  exact monicPoly_coeff_lt y j.isLt

/-- ★★★ **THE BÉZOUT CELL TRANSPORT (T)** — the design's
`bezCellTransport : Coeff(O, e·k, N) ≃ Coeff(O', k, e·N)`: the normalized transform
descends to the finite coefficient boxes, level scaling by exactly the ramification
`e` — uniformly in `q, h, e, k, N`, every DVR pair.  Computed on lifts by
`bezCellTransport_apply` / `bezCellTransport_symm_apply`. -/
noncomputable def bezCellTransport (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) (k N : ℕ) :
    Coeff O (e * k) N ≃ Coeff (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N) where
  toFun x := proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
    (bezDevVec π u a b h e k (proj_surjective O (e * k) N x).choose)
  invFun y := proj O (e * k) N
    (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k
      (proj_surjective (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N) y).choose)
  left_inv := fun x => by
    have ha : proj O (e * k) N (proj_surjective O (e * k) N x).choose = x :=
      (proj_surjective O (e * k) N x).choose_spec
    have hb : proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
        (proj_surjective (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
          (proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
            (bezDevVec π u a b h e k (proj_surjective O (e * k) N x).choose))).choose
        = proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
            (bezDevVec π u a b h e k (proj_surjective O (e * k) N x).choose) :=
      (proj_surjective (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
        _).choose_spec
    have h1 := bezReassVec_congr (u := u) hπ hB he hb
    rw [bezReassVec_bezDevVec hB he k _] at h1
    exact h1.trans ha
  right_inv := fun y => by
    have hb : proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
        (proj_surjective (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
          y).choose = y :=
      (proj_surjective (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
        y).choose_spec
    have ha : proj O (e * k) N (proj_surjective O (e * k) N
        (proj O (e * k) N
          (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k
            (proj_surjective (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
              y).choose))).choose
        = proj O (e * k) N
            (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k
              (proj_surjective (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
                y).choose) :=
      (proj_surjective O (e * k) N _).choose_spec
    have h1 := bezDevVec_congr (u := u) hπ hB he ha
    rw [bezDevVec_bezReassVec hB he k _] at h1
    exact h1.trans hb

/-- ★ The transport is computed on ANY lift by the transform vector. -/
theorem bezCellTransport_apply (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) (k N : ℕ) (v : Fin (e * k) → O) :
    bezCellTransport hπ hB he k N (proj O (e * k) N v)
      = proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
          (bezDevVec π u a b h e k v) :=
  bezDevVec_congr (u := u) hπ hB he
    (proj_surjective O (e * k) N (proj O (e * k) N v)).choose_spec

/-- ★ The inverse transport is computed on ANY lift by the reassembly vector. -/
theorem bezCellTransport_symm_apply (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) (k N : ℕ)
    (y : Fin k → AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) :
    (bezCellTransport hπ hB he k N).symm
        (proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N) y)
      = proj O (e * k) N
          (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y) :=
  bezReassVec_congr (u := u) hπ hB he
    (proj_surjective (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
      (proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N) y)).choose_spec

/-- ★ **THE COUNT TRANSPORT**: the transport carries every cell set to a set of the
SAME cardinality (design (T), counting form). -/
theorem bezCellTransport_card_image (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) (k N : ℕ) (S : Set (Coeff O (e * k) N)) :
    Nat.card ((bezCellTransport (u := u) hπ hB he k N) '' S) = Nat.card S :=
  Nat.card_image_of_injective (bezCellTransport (u := u) hπ hB he k N).injective S

/-- ★ The recentred box counts at the SAME `q`:
`#Coeff(O', k, e·N) = q^{k·e·N} = q^{(e·k)·N}` (design's unchanged normalization
identity). -/
theorem bez_card_coeff (hπ : Irreducible π) (he : 2 ≤ e) (k N : ℕ) :
    Nat.card (Coeff (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N))
      = residueCard O ^ (k * (e * N)) := by
  rw [card_coeff, eis_residueCard hπ (bez_unit_residue_ne_zero u a) he]

end CellTransport

/-! ## §6 — LAYER 2: the correspondence surface (stated, NOT asserted)

The design §6/§8: the sole literature-grade claim of the slope-`h ≥ 2` recentring is
the factor correspondence between `g` and its NORMALIZED transform `bezDevT g`.  It
is a named Prop here — never asserted, never axiomatized.  **CP2's current legs do
NOT certify it**: leg E (IFCG48's `FactorCorrespondenceAt`) is exactly the `h = 1`
case, where every carry `q_i = h·i/e` vanishes on `i < e` and the raw/normalized
coordinate distinction disappears; leg R decides squarefree residual blocks and does
not supply the deep-primary iteration.  Signing this Prop as a fourth
`FGMNCitePackage` leg requires the design §8 dictionary audit against the source:
its normalizer must produce exactly `(q_i, r_i, δ_i)` of (C2) — including the unit
`z^{a·q_i − b·i}` — and its transformed polynomial must be `bezDevT` (D), NOT the raw
scalar extension through `ι` (design §6.3: removing the carry factors is an
`O`-linear coordinate normalization, not a ring map, so (FC) does not follow formally
from factorization after scalar extension). -/

section Layer2

open Uniformity.Density.IFCG47 (scaleType)

/-- ★★★ **THE SLOPE-BÉZOUT FACTOR CORRESPONDENCE at slope numerator `h`, depth `k`**
(design §6.1, the exact cite surface; the analogue of IFCG48's
`FactorCorrespondenceAt`, which is its `h = 1` instance): under the Bézout pin
`a·h = b·e + 1` (which FORCES `0 < h`, `0 < a`, `gcd(h,e) = 1`), the slope-`h/e`
lattice on `g`, and the Bézout deep-box condition (A) on the `bezRawKey`-adic
development, the monic irreducible factors of `g` over `O` are matched — as a
multiset relation — with those of the normalized transform `bezDevT g` over `O'`,
each matched pair `(g₀, G₀)` carrying `inertiaDegOf g₀ = inertiaDegOf G₀` (the
`f`-leg) and `deg g₀ = e·deg G₀` (the `e`-leg): (FC). -/
def SlopeBezoutFactorCorrespondenceAt (h k : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ (π : O) (u : Oˣ), Irreducible π →
  ∀ a b e : ℕ, 2 ≤ e → a * h = b * e + 1 →
  ∀ [IsDomain (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))],
  ∀ g : Polynomial O, g.Monic → g.natDegree = e * k →
    (∀ j, j < e * k → π ^ ((h * (e * k - j) + (e - 1)) / e) ∣ g.coeff j) →
    (∀ t, t < k → ∀ i, i < e →
      π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
        ∣ (dev (bezRawKey π u h e) g t).coeff i) →
    Multiset.Rel
      (fun g₀ G₀ => inertiaDegOf g₀ = inertiaDegOf G₀
        ∧ g₀.natDegree = e * G₀.natDegree)
      (monicFactors g) (monicFactors (bezDevT π u a b h e k g))

/-- **The pointwise type-scaling form** (the analogue of IFCG47's
`CellTypeScalingAt`): same hypotheses, conclusion
`typeOf g = scaleType e (typeOf (bezDevT g))` — the (TS) surface consumed by the
decision transport. -/
def SlopeBezoutCellTypeScalingAt (h k : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ (π : O) (u : Oˣ), Irreducible π →
  ∀ a b e : ℕ, 2 ≤ e → a * h = b * e + 1 →
  ∀ [IsDomain (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))]
    [IsDiscreteValuationRing (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))],
  ∀ g : Polynomial O, g.Monic → g.natDegree = e * k →
    (∀ j, j < e * k → π ^ ((h * (e * k - j) + (e - 1)) / e) ∣ g.coeff j) →
    (∀ t, t < k → ∀ i, i < e →
      π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
        ∣ (dev (bezRawKey π u h e) g t).coeff i) →
    typeOf g = scaleType e (typeOf (bezDevT π u a b h e k g))

/-- ★★ **(TS): the correspondence fires the type-scaling read** — through IFCG48's
landed multiset reduction `typeOf_eq_scaleType_of_rel` VERBATIM (the `(e, f)`
bookkeeping is generic in the Eisenstein unit parameter, so `h ≥ 2` inherits it
unchanged; only the correspondence itself is new mathematics). -/
theorem slopeBezoutCellTypeScalingAt_of_correspondence {h k : ℕ}
    (hFC : SlopeBezoutFactorCorrespondenceAt h k) :
    SlopeBezoutCellTypeScalingAt h k := by
  intro O _ _ _ _ _ π u hπ a b e he hB _ _ g hg hdeg hlat hbox
  have he' : 0 < e := by omega
  obtain ⟨hGm, _⟩ := bezDevT_monic (π := π) (u := u) (a := a) (b := b) (h := h)
    (k := k) he' hg hdeg
  exact typeOf_eq_scaleType_of_rel hGm (hFC O π u hπ a b e he hB g hg hdeg hlat hbox)

end Layer2

/-! ### (DT): the decision transport across the Bézout cell transport -/

section Transport

-- ER4's universe fence (fourth contact): the named Prop quantifies `O : Type`.
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
variable {π : O} {u : Oˣ} {a b h e k : ℕ}
variable [IsDomain (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))]
  [IsDiscreteValuationRing (AdjoinRoot (eisKey π (-((u : O) ^ a)) e))]
  [Finite (ResidueField (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)))]

open Uniformity.Density.IFCG47 (scaleType)

/-- ★★ **(DT), inbound**: an `O'`-decision at `σ'`, level `e·N`, on the transported
class PULLS BACK to an `O`-decision at the `e`-scaled type, level `N` — conditional
on exactly `SlopeBezoutCellTypeScalingAt h k`.  The lattice/box premises enter at the
LIFT level (`∀`-lift form: the full-span side pins at slope `h/e` and the transported
deep box, design §6.2). -/
theorem bez_decidedAt_of_transport_decidedAt
    (hCTS : SlopeBezoutCellTypeScalingAt h k)
    (hπ : Irreducible π) (hB : a * h = b * e + 1) (he : 2 ≤ e) {N : ℕ}
    {c : Coeff O (e * k) N}
    (hlat : ∀ v : Fin (e * k) → O, proj O (e * k) N v = c →
      ∀ j, j < e * k → π ^ ((h * (e * k - j) + (e - 1)) / e) ∣ (monicPoly v).coeff j)
    (hbox : ∀ v : Fin (e * k) → O, proj O (e * k) N v = c →
      ∀ t, t < k → ∀ i, i < e →
        π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
          ∣ (dev (bezRawKey π u h e) (monicPoly v) t).coeff i)
    {σ' : FactorizationType}
    (hdec : DecidedAt (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k σ' (e * N)
      (bezCellTransport hπ hB he k N c)) :
    DecidedAt O (e * k) (scaleType e σ') N c := by
  intro v hv
  have he' : 0 < e := Nat.zero_lt_two.trans_le he
  -- the pointwise scaling law at the lift
  have hscale := hCTS O π u hπ a b e he hB (monicPoly v) (monicPoly_monic v)
    (monicPoly_natDegree v) (hlat v hv) (hbox v hv)
  -- the transform is an `O'`-lift of the transported class
  have hb : proj (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k (e * N)
      (bezDevVec π u a b h e k v) = bezCellTransport hπ hB he k N c := by
    rw [← hv, bezCellTransport_apply]
  have hdev := hdec (bezDevVec π u a b h e k v) hb
  -- `monicPoly (bezDevVec v) = bezDevT (monicPoly v)`
  have hmon := bezDevT_monic (π := π) (u := u) (a := a) (b := b) (h := h) (k := k)
    he' (monicPoly_monic v) (monicPoly_natDegree v)
  have hfun : monicPoly (bezDevVec π u a b h e k v)
      = bezDevT π u a b h e k (monicPoly v) :=
    monicPoly_coeff_self hmon.1 hmon.2
  rw [hfun] at hdev
  rw [hscale, hdev]

/-- ★★ **(DT), outbound**: an `O`-decision at the `e`-scaled type PUSHES FORWARD to
an `O'`-decision at `σ'`, level `e·N` — the same pointwise law, driven through
`scaleType`-injectivity (IFCG47 §2's skeleton against the Bézout transport). -/
theorem bez_transport_decidedAt_of_decidedAt
    (hCTS : SlopeBezoutCellTypeScalingAt h k)
    (hπ : Irreducible π) (hB : a * h = b * e + 1) (he : 2 ≤ e) {N : ℕ}
    {c : Coeff O (e * k) N}
    (hlat : ∀ v : Fin (e * k) → O, proj O (e * k) N v = c →
      ∀ j, j < e * k → π ^ ((h * (e * k - j) + (e - 1)) / e) ∣ (monicPoly v).coeff j)
    (hbox : ∀ v : Fin (e * k) → O, proj O (e * k) N v = c →
      ∀ t, t < k → ∀ i, i < e →
        π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
          ∣ (dev (bezRawKey π u h e) (monicPoly v) t).coeff i)
    {σ' : FactorizationType}
    (hdec : DecidedAt O (e * k) (scaleType e σ') N c) :
    DecidedAt (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k σ' (e * N)
      (bezCellTransport hπ hB he k N c) := by
  intro y hy
  have he' : 0 < e := Nat.zero_lt_two.trans_le he
  -- the reassembly is an `O`-lift of `c`
  have ha : proj O (e * k) N
      (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y) = c := by
    have h1 := bezCellTransport_symm_apply (u := u) hπ hB he k N y
    rw [hy, Equiv.symm_apply_apply] at h1
    exact h1.symm
  -- the pointwise scaling law at the reassembled lift
  have hscale := hCTS O π u hπ a b e he hB
    (monicPoly (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y))
    (monicPoly_monic _) (monicPoly_natDegree _) (hlat _ ha) (hbox _ ha)
  -- `monicPoly (bezReassVec y) = bezReassT (monicPoly y)`, so its transform is
  -- `monicPoly y`
  have hre := bezReassT_monic (π := π) (u := u) (k := k) hB he'
    (monicPoly_monic y) (monicPoly_natDegree y)
  have hfun : monicPoly (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y)
      = bezReassT π u a b h e (Nat.zero_lt_two.trans_le he) k (monicPoly y) :=
    monicPoly_coeff_self hre.1 hre.2
  have hkey : bezDevT π u a b h e k
      (monicPoly (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y))
      = monicPoly y := by
    rw [hfun]
    exact bezDevT_bezReassT hB he' (le_of_eq (monicPoly_natDegree y))
  have hdec' := hdec (bezReassVec π u a b h e (Nat.zero_lt_two.trans_le he) k y) ha
  rw [hscale, hkey] at hdec'
  exact scaleType_injective he' hdec'

/-- ★★★ **(DT), the iff form** (design §6.2's `bezCellTransport_decidedAt_iff`): at
the slope-`h/e` full-span pins with the deep box, the transported class is
`σ'`-decided over the recentring ring at level `e·N` IF AND ONLY IF the class is
`scaleType e σ'`-decided over the base at level `N` — conditional on exactly the
named correspondence (through its type-scaling form); the target is the ORDINARY
`DecidedAt` over the complete DVR `O'`, no weakened decision predicate. -/
theorem bez_transport_decidedAt_iff (hCTS : SlopeBezoutCellTypeScalingAt h k)
    (hπ : Irreducible π) (hB : a * h = b * e + 1) (he : 2 ≤ e) {N : ℕ}
    {c : Coeff O (e * k) N}
    (hlat : ∀ v : Fin (e * k) → O, proj O (e * k) N v = c →
      ∀ j, j < e * k → π ^ ((h * (e * k - j) + (e - 1)) / e) ∣ (monicPoly v).coeff j)
    (hbox : ∀ v : Fin (e * k) → O, proj O (e * k) N v = c →
      ∀ t, t < k → ∀ i, i < e →
        π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
          ∣ (dev (bezRawKey π u h e) (monicPoly v) t).coeff i)
    (σ' : FactorizationType) :
    DecidedAt (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k σ' (e * N)
        (bezCellTransport hπ hB he k N c)
      ↔ DecidedAt O (e * k) (scaleType e σ') N c :=
  ⟨fun hdec => bez_decidedAt_of_transport_decidedAt hCTS hπ hB he hlat hbox hdec,
   fun hdec => bez_transport_decidedAt_of_decidedAt hCTS hπ hB he hlat hbox hdec⟩

/-- The same socket directly from the CORRESPONDENCE surface. -/
theorem bez_transport_decidedAt_iff_of_correspondence
    (hFC : SlopeBezoutFactorCorrespondenceAt h k)
    (hπ : Irreducible π) (hB : a * h = b * e + 1) (he : 2 ≤ e) {N : ℕ}
    {c : Coeff O (e * k) N}
    (hlat : ∀ v : Fin (e * k) → O, proj O (e * k) N v = c →
      ∀ j, j < e * k → π ^ ((h * (e * k - j) + (e - 1)) / e) ∣ (monicPoly v).coeff j)
    (hbox : ∀ v : Fin (e * k) → O, proj O (e * k) N v = c →
      ∀ t, t < k → ∀ i, i < e →
        π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
          ∣ (dev (bezRawKey π u h e) (monicPoly v) t).coeff i)
    (σ' : FactorizationType) :
    DecidedAt (AdjoinRoot (eisKey π (-((u : O) ^ a)) e)) k σ' (e * N)
        (bezCellTransport hπ hB he k N c)
      ↔ DecidedAt O (e * k) (scaleType e σ') N c :=
  bez_transport_decidedAt_iff
    (slopeBezoutCellTypeScalingAt_of_correspondence hFC) hπ hB he hlat hbox σ'

end Transport

/-! ## §7 — the residual-box transfer criterion (RB) at slope `h/e`

Design §5: `resPoly(f) = (X − z̄)^k ⟺` the transform lies in the Bézout deep box —
"a new proof obligation, not verbatim IFCG43": the C110 binomial shift replayed with
`π^{h(s−t)}` in place of `π^{s−t}`; all terms in the relevant sum have common height
`h(k−t)`; the same binomial-vanishing identity removes the lower combinations.
IFCG44's landed `xres_eq_pow_iff_digits_h` supplies the residual side.  The box is
taken in the design's base-side normalized form (A): `π^{λ_{t,i}} ∣ (dev_κ g t)_i`
with `λ_{t,i} = ⌈(e·h(k−t) + 1 − h·i)/e⌉⁺` — exactly the Layer-2 Prop's hypothesis,
so the criterion certifies the named Prop's box against the corpus's residual
objects.  The C110 support stack (shiftDev, the `X^e`-block reads, the digit kit,
the binomial vanishing) is replicated private from IFCG43 §4. -/

section TransferSupport

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {u : Oˣ} {a b h e : ℕ}

/-! ### C110's shift stack, replicated (private; IFCG43 §4) -/

private theorem degree_C_lt_of_pos {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (c : O) :
    (Polynomial.C c : Polynomial O).degree < φ.degree := by
  refine lt_of_le_of_lt Polynomial.degree_C_le ?_
  rw [Polynomial.degree_eq_natDegree hφ.ne_zero]
  exact_mod_cast hd

private theorem monic_sub_C {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (c : O) : (φ - Polynomial.C c).Monic :=
  hφ.sub_of_left (degree_C_lt_of_pos hφ hd c)

private theorem degree_sub_C_eq {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (c : O) : (φ - Polynomial.C c).degree = φ.degree := by
  rw [sub_eq_add_neg]
  exact Polynomial.degree_add_eq_left_of_degree_lt
    (by rw [Polynomial.degree_neg]; exact degree_C_lt_of_pos hφ hd c)

private theorem natDegree_sub_C_eq {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (c : O) : (φ - Polynomial.C c).natDegree = φ.natDegree :=
  Polynomial.natDegree_eq_of_degree_eq (degree_sub_C_eq hφ hd c)

private noncomputable def shiftDev (φ : Polynomial O) (c : O) (f : Polynomial O)
    (n j : ℕ) : Polynomial O :=
  ∑ i ∈ Finset.Ico j n, Polynomial.C (c ^ (i - j) * (i.choose j : O)) * dev φ f i

private theorem degree_C_mul_le' (x : O) (p : Polynomial O) :
    (Polynomial.C x * p).degree ≤ p.degree := by
  refine le_trans (Polynomial.degree_mul_le _ _) ?_
  simpa using add_le_add_left (Polynomial.degree_C_le (a := x)) p.degree

private theorem degree_shiftDev_lt {φ : Polynomial O} (hφ : φ.Monic)
    (hd : 0 < φ.natDegree) (c : O) (f : Polynomial O) (n j : ℕ) :
    (shiftDev φ c f n j).degree < φ.degree := by
  have hbot : (⊥ : WithBot ℕ) < φ.degree := by
    rw [Polynomial.degree_eq_natDegree hφ.ne_zero]
    exact WithBot.bot_lt_coe _
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ((Finset.sup_lt_iff hbot).2 ?_)
  intro i _
  exact lt_of_le_of_lt (degree_C_mul_le' _ _) (degree_dev_lt hφ hd f i)

private theorem dev_sub_C {φ : Polynomial O} (hφ : φ.Monic) (hd : 0 < φ.natDegree)
    (c : O) (f : Polynomial O) {n : ℕ} (hf : f.natDegree < n * φ.natDegree) (j : ℕ)
    (hj : j < n) : dev (φ - Polynomial.C c) f j = shiftDev φ c f n j := by
  classical
  set ψ : Polynomial O := φ - Polynomial.C c with hψdef
  have hψ : ψ.Monic := monic_sub_C hφ hd c
  have hψd : ψ.natDegree = φ.natDegree := natDegree_sub_C_eq hφ hd c
  have hψdeg : ψ.degree = φ.degree := degree_sub_C_eq hφ hd c
  have hφeq : ψ + Polynomial.C c = φ := by
    rw [hψdef]
    ring
  have hdeg : ∀ t, (shiftDev φ c f n t).degree < ψ.degree := by
    intro t
    rw [hψdeg]
    exact degree_shiftDev_lt hφ hd c f n t
  have hsum : ∑ t ∈ Finset.range n, shiftDev φ c f n t * ψ ^ t = f := by
    have h1 : ∑ t ∈ Finset.range n, shiftDev φ c f n t * ψ ^ t
        = ∑ t ∈ Finset.Ico 0 n, ∑ i ∈ Finset.Ico t n,
            Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t := by
      rw [Finset.range_eq_Ico]
      exact Finset.sum_congr rfl fun t _ => by rw [shiftDev, Finset.sum_mul]
    have h2 : ∑ t ∈ Finset.Ico 0 n, ∑ i ∈ Finset.Ico t n,
          Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t
        = ∑ i ∈ Finset.Ico 0 n, ∑ t ∈ Finset.Ico 0 (i + 1),
            Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t :=
      Finset.sum_Ico_Ico_comm 0 n
        (fun t i => Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t)
    have h3 : ∀ i, ∑ t ∈ Finset.Ico 0 (i + 1),
          Polynomial.C (c ^ (i - t) * (i.choose t : O)) * dev φ f i * ψ ^ t
        = dev φ f i * φ ^ i := by
      intro i
      rw [← hφeq, add_pow, Finset.mul_sum, ← Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Polynomial.C_mul, map_pow, Polynomial.C_eq_natCast]
      ring
    rw [h1, h2, Finset.sum_congr rfl fun i _ => h3 i, ← Finset.range_eq_Ico]
    exact sum_dev_eq hφ hd f hf
  exact (dev_unique hψ (by rw [hψd]; exact hd) hdeg hsum j hj).symm

/-! ### the `X^e`-adic development reads coefficient blocks (private; IFCG43 §4) -/

private theorem blk_coeff (f : Polynomial O) (t j : ℕ) :
    (∑ i ∈ Finset.range e,
        Polynomial.C (f.coeff (e * t + i)) * Polynomial.X ^ i).coeff j
      = if j < e then f.coeff (e * t + j) else 0 := by
  classical
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range e) j (fun i => f.coeff (e * t + i))]
  simp [Finset.mem_range]

private theorem blk_degree_lt (_he : 0 < e) (f : Polynomial O) (t : ℕ) :
    (∑ i ∈ Finset.range e,
        Polynomial.C (f.coeff (e * t + i)) * Polynomial.X ^ i).degree
      < ((e : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe e)]
  intro i hi
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast Finset.mem_range.mp hi

private theorem sum_blk_eq (he : 0 < e) {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e) :
    ∑ t ∈ Finset.range n,
        (∑ i ∈ Finset.range e,
          Polynomial.C (f.coeff (e * t + i)) * Polynomial.X ^ i)
          * (Polynomial.X ^ e : Polynomial O) ^ t = f := by
  classical
  refine Polynomial.ext fun m => ?_
  rw [Polynomial.finsetSum_coeff]
  have hterm : ∀ t, ((∑ i ∈ Finset.range e,
        Polynomial.C (f.coeff (e * t + i)) * Polynomial.X ^ i)
        * (Polynomial.X ^ e : Polynomial O) ^ t).coeff m
      = if e * t ≤ m ∧ m - e * t < e then f.coeff (e * t + (m - e * t)) else 0 := by
    intro t
    rw [← pow_mul, Polynomial.coeff_mul_X_pow']
    by_cases h1 : e * t ≤ m
    · rw [if_pos h1, blk_coeff]
      by_cases h2 : m - e * t < e
      · rw [if_pos h2, if_pos ⟨h1, h2⟩]
      · rw [if_neg h2, if_neg (fun hcon => h2 hcon.2)]
    · rw [if_neg h1, if_neg (fun hcon => h1 hcon.1)]
  rw [Finset.sum_congr rfl fun t _ => hterm t]
  have hdm := Nat.div_add_mod m e
  have hmod : m % e < e := Nat.mod_lt m he
  by_cases hm : m / e < n
  · rw [Finset.sum_eq_single (m / e)]
    · have h1 : e * (m / e) ≤ m := by
        generalize hA : e * (m / e) = A at hdm
        omega
      have h2 : m - e * (m / e) < e := by
        generalize hA : e * (m / e) = A at hdm
        omega
      rw [if_pos ⟨h1, h2⟩]
      refine congrArg f.coeff ?_
      generalize hA : e * (m / e) = A at hdm ⊢
      omega
    · intro c _ hc
      rw [if_neg]
      rintro ⟨hc1, hc2⟩
      have hc1' : c * e ≤ m := by rwa [Nat.mul_comm] at hc1
      have hc2' : m < (c + 1) * e := by
        have h4 : m < e * c + e := by
          generalize hB : e * c = B at hc1 hc2
          omega
        calc m < e * c + e := h4
          _ = (c + 1) * e := by ring
      exact hc (Nat.div_eq_of_lt_le hc1' hc2').symm
    · intro hcon
      exact absurd (Finset.mem_range.mpr hm) hcon
  · rw [Finset.sum_eq_zero, eq_comm]
    · refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hf ?_)
      have h1 : n ≤ m / e := by omega
      have h2 : n * e ≤ (m / e) * e := Nat.mul_le_mul_right e h1
      have h3 : (m / e) * e ≤ m := Nat.div_mul_le_self m e
      omega
    · intro t ht
      rw [if_neg]
      rintro ⟨ht1, ht2⟩
      have htn : t < n := Finset.mem_range.mp ht
      have ht1' : t * e ≤ m := by rwa [Nat.mul_comm] at ht1
      have ht2' : m < (t + 1) * e := by
        have h4 : m < e * t + e := by
          generalize hB : e * t = B at ht1 ht2
          omega
        calc m < e * t + e := h4
          _ = (t + 1) * e := by ring
      have hdiv : m / e = t := Nat.div_eq_of_lt_le ht1' ht2'
      omega

private theorem dev_X_pow_blk (he : 0 < e) {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e) {t : ℕ} (ht : t < n) :
    dev (Polynomial.X ^ e : Polynomial O) f t
      = ∑ i ∈ Finset.range e,
          Polynomial.C (f.coeff (e * t + i)) * Polynomial.X ^ i := by
  have hmon : (Polynomial.X ^ e : Polynomial O).Monic := Polynomial.monic_X_pow e
  have hd : 0 < (Polynomial.X ^ e : Polynomial O).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    exact he
  refine (dev_unique hmon hd (a := fun t => ∑ i ∈ Finset.range e,
      Polynomial.C (f.coeff (e * t + i)) * Polynomial.X ^ i) (fun j => ?_)
      (sum_blk_eq he hf) t ht).symm
  rw [Polynomial.degree_X_pow]
  exact blk_degree_lt he f j

private theorem dev_X_pow_coeff (he : 0 < e) {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e) {t : ℕ} (ht : t < n) (i : ℕ) :
    (dev (Polynomial.X ^ e : Polynomial O) f t).coeff i
      = if i < e then f.coeff (e * t + i) else 0 := by
  rw [dev_X_pow_blk he hf ht, blk_coeff]

/-! ### the two shift readings between `X^e` and the raw slope key -/

/-- The raw slope key is the `C(u·π^h)`-shift of `X^e` (anti-drift pin). -/
private theorem bezRawKey_eq_sub :
    bezRawKey π u h e = Polynomial.X ^ e - Polynomial.C ((u : O) * π ^ h) := rfl

/-- The raw-key digits as binomial combinations of the coefficient-block digits. -/
private theorem dev_bezRawKey_eq (he : 0 < e) {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e) {t : ℕ} (ht : t < n) :
    dev (bezRawKey π u h e) f t
      = ∑ s ∈ Finset.Ico t n,
          Polynomial.C (((u : O) * π ^ h) ^ (s - t) * (s.choose t : O))
            * dev (Polynomial.X ^ e : Polynomial O) f s := by
  have hmon : (Polynomial.X ^ e : Polynomial O).Monic := Polynomial.monic_X_pow e
  have hd : 0 < (Polynomial.X ^ e : Polynomial O).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    exact he
  rw [bezRawKey_eq_sub]
  exact dev_sub_C hmon hd ((u : O) * π ^ h) f
    (by rw [Polynomial.natDegree_X_pow]; exact hf) t ht

/-- The coefficient-block digits as binomial combinations of the raw-key digits
(the inverse shift). -/
private theorem dev_X_pow_eq_bez (he : 0 < e) {f : Polynomial O} {n : ℕ}
    (hf : f.natDegree < n * e) {t : ℕ} (ht : t < n) :
    dev (Polynomial.X ^ e : Polynomial O) f t
      = ∑ s ∈ Finset.Ico t n,
          Polynomial.C ((-((u : O) * π ^ h)) ^ (s - t) * (s.choose t : O))
            * dev (bezRawKey π u h e) f s := by
  have hkm : (bezRawKey π u h e).Monic := bezRawKey_monic he
  have hkd : 0 < (bezRawKey π u h e).natDegree := by
    rw [bezRawKey_natDegree]
    exact he
  have hkey : (Polynomial.X ^ e : Polynomial O)
      = bezRawKey π u h e - Polynomial.C (-((u : O) * π ^ h)) := by
    rw [bezRawKey_eq_sub, map_neg, sub_neg_eq_add, sub_add_cancel]
  rw [hkey]
  exact dev_sub_C hkm hkd (-((u : O) * π ^ h)) f
    (by rw [bezRawKey_natDegree]; exact hf) t ht

/-! ### the digit kit and the binomial vanishing (private; IFCG43 §4) -/

private theorem digAt_zero' (hπ : Irreducible π) (K : ℕ) : digAt π K (0 : O) = 0 := by
  rw [digAt_eq hπ (mul_zero (π ^ K)).symm]
  exact map_zero _

private theorem digAt_sum (hπ : Irreducible π) {K : ℕ} (s : Finset ℕ) (g : ℕ → O)
    (hg : ∀ x ∈ s, π ^ K ∣ g x) :
    digAt π K (∑ x ∈ s, g x) = ∑ x ∈ s, digAt π K (g x) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, digAt_zero' hπ]
  | cons x s hx ih =>
    rw [Finset.sum_cons, Finset.sum_cons,
      digAt_add hπ (hg x (Finset.mem_cons_self x s))
        (Finset.dvd_sum fun c hc => hg c (Finset.mem_cons_of_mem hc)),
      ih (fun c hc => hg c (Finset.mem_cons_of_mem hc))]

private theorem binom_vanish {F : Type*} [CommRing F] (w : F) {t k : ℕ} (ht : t < k) :
    ∑ s ∈ Finset.Ico t (k + 1),
        w ^ (s - t) * ((s.choose t : F) * (k.choose s : F)) * (-w) ^ (k - s) = 0 := by
  have hstep : ∀ s ∈ Finset.Ico t (k + 1),
      w ^ (s - t) * ((s.choose t : F) * (k.choose s : F)) * (-w) ^ (k - s)
        = (k.choose t : F) * (((k - t).choose (s - t) : F)
            * (w ^ (s - t) * (-w) ^ (k - t - (s - t)))) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
    have hch : k.choose s * s.choose t = k.choose t * (k - t).choose (s - t) :=
      Nat.choose_mul (by omega : t ≤ s)
    have hexp : k - s = k - t - (s - t) := by omega
    calc w ^ (s - t) * ((s.choose t : F) * (k.choose s : F)) * (-w) ^ (k - s)
        = ((k.choose s * s.choose t : ℕ) : F) * (w ^ (s - t) * (-w) ^ (k - s)) := by
          push_cast
          ring
      _ = ((k.choose t * (k - t).choose (s - t) : ℕ) : F)
            * (w ^ (s - t) * (-w) ^ (k - t - (s - t))) := by rw [hch, hexp]
      _ = (k.choose t : F) * (((k - t).choose (s - t) : F)
            * (w ^ (s - t) * (-w) ^ (k - t - (s - t)))) := by
          push_cast
          ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have hpow : (w + -w) ^ (k - t) = ∑ j ∈ Finset.range (k - t + 1),
      ((k - t).choose j : F) * (w ^ j * (-w) ^ (k - t - j)) := by
    rw [add_pow]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hreindex : ∑ s ∈ Finset.Ico t (k + 1),
      ((k - t).choose (s - t) : F) * (w ^ (s - t) * (-w) ^ (k - t - (s - t)))
        = ∑ j ∈ Finset.range (k - t + 1),
            ((k - t).choose j : F) * (w ^ j * (-w) ^ (k - t - j)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hr : k + 1 - t = k - t + 1 := by omega
    rw [hr]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Nat.add_sub_cancel_left]
  rw [hreindex, ← hpow, add_neg_cancel, zero_pow (by omega : k - t ≠ 0), mul_zero]

/-! ### the carry-exponent identities (the genuinely `h ≥ 2` arithmetic) -/

/-- The deep-box exponent at slot `0` is `h·(k−t) + 1` (the `+1` the vanishing
pays). -/
private theorem bez_lat_exp_zero (he : 0 < e) (M : ℕ) :
    (e * M + 1 + e - 1 - h * 0) / e = M + 1 := by
  rw [Nat.mul_zero, Nat.sub_zero]
  have h1 : e * M + 1 + e - 1 = e * M + e := by
    generalize e * M = A
    omega
  rw [h1, Nat.mul_add_div he, Nat.div_self he]

/-- The deep-box exponent at slots `1 ≤ i < e` is `h·(k−t) − q_i` — the carry `q_i`
is exactly what the slot's own `γ`-position pays (`r_i ≠ 0` via the pin). -/
private theorem bez_lat_exp_pos (hB : a * h = b * e + 1) (he : 0 < e) {M : ℕ}
    (hM : 1 ≤ M) {i : ℕ} (hi1 : 1 ≤ i) (hi2 : i < e) :
    (e * (h * M) + 1 + e - 1 - h * i) / e = h * M - h * i / e := by
  have hh : 0 < h := (bezout_pos hB).2
  have hr0 : h * i % e ≠ 0 := by
    intro hcon
    have h00 : h * 0 % e = 0 := by rw [Nat.mul_zero, Nat.zero_mod]
    have := bezout_hmul_mod_injOn hB hi2 he (by rw [hcon, h00])
    omega
  have hdm := Nat.div_add_mod (h * i) e
  have hrlt : h * i % e < e := Nat.mod_lt _ he
  have hqh : h * i / e < h := by
    rw [Nat.div_lt_iff_lt_mul he]
    exact mul_lt_mul_of_pos_left hi2 hh
  have hqM : h * i / e < h * M := lt_of_lt_of_le hqh (Nat.le_mul_of_pos_right h hM)
  have hsplit : e * (h * M - h * i / e) + e * (h * i / e) = e * (h * M) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hkey : e * (h * M) + 1 + e - 1 - h * i
      = e * (h * M - h * i / e) + (e - h * i % e) := by
    generalize hA : e * (h * M - h * i / e) = A at hsplit ⊢
    generalize hBq : e * (h * i / e) = B at hsplit hdm ⊢
    generalize hC : e * (h * M) = C at hsplit ⊢
    omega
  rw [hkey, Nat.mul_add_div he, Nat.div_eq_of_lt (by omega : e - h * i % e < e),
    Nat.add_zero]

/-- The slope-lattice exponent at slot `e·s + i` (`s < k`, `i < e`) is
`h·(k−s) − q_i` — the raw purity supply after the carry. -/
private theorem bez_pure_exp (hB : a * h = b * e + 1) (he : 0 < e) {k s i : ℕ}
    (hs : s < k) (hi : i < e) :
    (h * (e * k - (e * s + i)) + (e - 1)) / e = h * (k - s) - h * i / e := by
  have hh : 0 < h := (bezout_pos hB).2
  have hdm := Nat.div_add_mod (h * i) e
  have hrlt : h * i % e < e := Nat.mod_lt _ he
  have hqh : h * i / e < h := by
    rw [Nat.div_lt_iff_lt_mul he]
    exact mul_lt_mul_of_pos_left hi hh
  have hh_le : h ≤ h * (k - s) := Nat.le_mul_of_pos_right h (by omega)
  have hks : e * (k - s) + e * s = e * k := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hik : i ≤ e * (k - s) := by
    have h1 : e * 1 ≤ e * (k - s) := Nat.mul_le_mul_left e (by omega)
    omega
  have h2 : h * (e * k - (e * s + i)) + h * i = h * (e * (k - s)) := by
    rw [← Nat.mul_add]
    congr 1
    generalize hA : e * (k - s) = A at hks hik ⊢
    generalize hBk : e * s = B at hks ⊢
    generalize hC : e * k = C at hks ⊢
    omega
  have h3 : h * (e * (k - s)) = e * (h * (k - s)) := by ring
  have hsplit : e * (h * (k - s) - h * i / e) + e * (h * i / e)
      = e * (h * (k - s)) := by
    rw [← Nat.mul_add]
    congr 1
    have hq_le : h * i / e ≤ h * (k - s) := le_trans (le_of_lt hqh) hh_le
    omega
  have hkey : h * (e * k - (e * s + i)) + (e - 1)
      = e * (h * (k - s) - h * i / e) + (e - 1 - h * i % e) := by
    generalize hX : h * (e * k - (e * s + i)) = X at h2 ⊢
    generalize hA : e * (h * (k - s) - h * i / e) = A at hsplit ⊢
    generalize hBq : e * (h * i / e) = B at hsplit hdm ⊢
    generalize hC : e * (h * (k - s)) = C at hsplit h3 ⊢
    generalize hD : h * (e * (k - s)) = D at h2 h3 ⊢
    generalize hHI : h * i = HI at h2 hdm hrlt ⊢
    omega
  rw [hkey, Nat.mul_add_div he,
    Nat.div_eq_of_lt (by omega : e - 1 - h * i % e < e), Nat.add_zero]

end TransferSupport

/-! ### the two directions of the criterion -/

section TransferCriterion

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {π : O} {u : Oˣ} {a b h e : ℕ}

/-- **Digits → box**: if the lattice digits of `G` at heights `h·(k−t)` read
`(X − ū)^k`, every raw-key development coefficient clears the deep-box line — the
binomial vanishing pays the `+1` at slot `0`; purity + the carry pays every other
slot. -/
private theorem bez_box_of_digits (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) {k : ℕ} {G : Polynomial O} (hG : G.Monic)
    (hGdeg : G.natDegree = e * k)
    (hpure : ∀ j, j < e * k → π ^ ((h * (e * k - j) + (e - 1)) / e) ∣ G.coeff j)
    (hdig : ∀ t, t < k → digAt π (h * (k - t)) (G.coeff (e * t))
        = (k.choose t : IsLocalRing.ResidueField O)
            * (- IsLocalRing.residue O (u : O)) ^ (k - t))
    {t : ℕ} (ht : t < k) {i : ℕ} (hi : i < e) :
    π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
      ∣ (dev (bezRawKey π u h e) G t).coeff i := by
  have he' : 0 < e := by omega
  have hh : 0 < h := (bezout_pos hB).2
  have hGdeg' : G.natDegree < (k + 1) * e := by
    rw [hGdeg]
    calc e * k < e * k + e := by omega
      _ = (k + 1) * e := by ring
  have hGtop : G.coeff (e * k) = 1 := by
    rw [← hGdeg]
    exact hG.coeff_natDegree
  rw [dev_bezRawKey_eq he' hGdeg' (by omega : t < k + 1), Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  have hread : ∀ s, s < k + 1 →
      (dev (Polynomial.X ^ e : Polynomial O) G s).coeff i = G.coeff (e * s + i) := by
    intro s hs2
    rw [dev_X_pow_coeff he' hGdeg' hs2 i, if_pos hi]
  -- the uniform `π`-power supply at the block slots
  have hdvd0 : ∀ s, s < k + 1 → π ^ (h * (k - s)) ∣ G.coeff (e * s) := by
    intro s hs2
    rcases Nat.lt_or_ge s k with hsk | hsk
    · have hlt : e * s < e * k := mul_lt_mul_of_pos_left hsk he'
      have hexp := bez_pure_exp (i := 0) hB he' hsk he'
      rw [Nat.add_zero, Nat.mul_zero, Nat.zero_div, Nat.sub_zero] at hexp
      have h1 := hpure (e * s) hlt
      rwa [hexp] at h1
    · have hsk' : s = k := by omega
      subst hsk'
      rw [Nat.sub_self, Nat.mul_zero, pow_zero]
      exact one_dvd _
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · -- slot 0: the digit-combination vanishing lifts the divisibility by one
    subst hi0
    rw [bez_lat_exp_zero (h := h) he' (h * (k - t))]
    have hsum : ∑ s ∈ Finset.Ico t (k + 1),
        ((u : O) * π ^ h) ^ (s - t) * (s.choose t : O)
          * (dev (Polynomial.X ^ e : Polynomial O) G s).coeff 0
        = ∑ s ∈ Finset.Ico t (k + 1),
            ((u : O) * π ^ h) ^ (s - t) * (s.choose t : O) * G.coeff (e * s) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      rw [hread s hs2, Nat.add_zero]
    rw [hsum]
    -- the uniform digit values at every `s ≤ k`
    have hdig' : ∀ s, t ≤ s → s < k + 1 →
        digAt π (h * (k - s)) (G.coeff (e * s))
          = (k.choose s : IsLocalRing.ResidueField O)
              * (- IsLocalRing.residue O (u : O)) ^ (k - s) := by
      intro s hs1 hs2
      rcases Nat.lt_or_ge s k with hsk | hsk
      · exact hdig s hsk
      · have hsk' : s = k := by omega
        subst hsk'
        rw [Nat.sub_self, Nat.mul_zero, digAt_zero, hGtop, map_one, Nat.choose_self,
          Nat.cast_one, pow_zero, mul_one]
    -- every term is `π^{h(k−t)}`-divisible
    have hterm_dvd : ∀ s ∈ Finset.Ico t (k + 1),
        π ^ (h * (k - t))
          ∣ ((u : O) * π ^ h) ^ (s - t) * (s.choose t : O) * G.coeff (e * s) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      obtain ⟨y, hy⟩ := hdvd0 s hs2
      have hkt : h * (k - t) = h * (s - t) + h * (k - s) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      refine ⟨(u : O) ^ (s - t) * (s.choose t : O) * y, ?_⟩
      rw [hy, mul_pow, ← pow_mul, hkt, pow_add]
      ring
    have hDdvd : π ^ (h * (k - t)) ∣ ∑ s ∈ Finset.Ico t (k + 1),
        ((u : O) * π ^ h) ^ (s - t) * (s.choose t : O) * G.coeff (e * s) :=
      Finset.dvd_sum hterm_dvd
    rw [← digAt_eq_zero_iff hπ hDdvd, digAt_sum hπ _ _ hterm_dvd]
    -- each term's digit is the binomial combination of the residual digits
    have hterm_dig : ∀ s ∈ Finset.Ico t (k + 1),
        digAt π (h * (k - t))
            (((u : O) * π ^ h) ^ (s - t) * (s.choose t : O) * G.coeff (e * s))
          = (IsLocalRing.residue O (u : O)) ^ (s - t)
              * ((s.choose t : IsLocalRing.ResidueField O)
                * (k.choose s : IsLocalRing.ResidueField O))
              * (- IsLocalRing.residue O (u : O)) ^ (k - s) := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
      obtain ⟨y, hy⟩ := hdvd0 s hs2
      have hry : IsLocalRing.residue O y
          = (k.choose s : IsLocalRing.ResidueField O)
              * (- IsLocalRing.residue O (u : O)) ^ (k - s) :=
        (digAt_eq hπ hy).symm.trans (hdig' s hs1 hs2)
      have hkt : h * (k - t) = h * (s - t) + h * (k - s) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      have heq : ((u : O) * π ^ h) ^ (s - t) * (s.choose t : O) * G.coeff (e * s)
          = π ^ (h * (k - t)) * ((u : O) ^ (s - t) * (s.choose t : O) * y) := by
        rw [hy, mul_pow, ← pow_mul, hkt, pow_add]
        ring
      have hcalc1 : digAt π (h * (k - t))
          (((u : O) * π ^ h) ^ (s - t) * (s.choose t : O) * G.coeff (e * s))
          = IsLocalRing.residue O ((u : O) ^ (s - t) * (s.choose t : O) * y) :=
        digAt_eq hπ heq
      rw [hcalc1, map_mul, map_mul, map_pow, map_natCast, hry]
      ring
    rw [Finset.sum_congr rfl hterm_dig]
    exact binom_vanish (IsLocalRing.residue O (u : O)) ht
  · -- slots `1 ≤ i < e`: purity + the carry pays the box line exactly
    rw [bez_lat_exp_pos hB he' (by omega : 1 ≤ k - t) hipos hi]
    refine Finset.dvd_sum fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
    rw [hread s hs2]
    rcases Nat.lt_or_ge s k with hsk | hsk
    · have hlt : e * s + i < e * k := by
        have h3 : e * (s + 1) ≤ e * k := Nat.mul_le_mul_left e (by omega)
        rw [Nat.mul_add, Nat.mul_one] at h3
        generalize hA : e * s = A at h3 ⊢
        generalize hC : e * k = C at h3 ⊢
        omega
      have h1 := hpure (e * s + i) hlt
      rw [bez_pure_exp hB he' hsk hi] at h1
      obtain ⟨y, hy⟩ := h1
      have hqh : h * i / e < h := by
        rw [Nat.div_lt_iff_lt_mul he']
        exact mul_lt_mul_of_pos_left hi hh
      have hqle : h * i / e ≤ h * (k - s) :=
        le_trans (le_of_lt hqh) (Nat.le_mul_of_pos_right h (by omega))
      have hkt2 : h * (k - t) - h * i / e
          = h * (s - t) + (h * (k - s) - h * i / e) := by
        have hmul : h * (k - t) = h * (s - t) + h * (k - s) := by
          rw [← Nat.mul_add]
          congr 1
          omega
        generalize hA : h * (k - t) = A at hmul ⊢
        generalize hBt : h * (s - t) = B at hmul ⊢
        generalize hC : h * (k - s) = C at hmul hqle ⊢
        omega
      refine ⟨(u : O) ^ (s - t) * (s.choose t : O) * y, ?_⟩
      rw [hy, mul_pow, ← pow_mul, hkt2, pow_add]
      ring
    · have hsk' : s = k := by omega
      have hcz : G.coeff (e * s + i) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hGdeg, hsk']; omega)
      rw [hcz, mul_zero]
      exact dvd_zero _

/-- **Box → digits**: if the raw-key development lies in the deep box, the lattice
digits of `G` read exactly the recentred `k`-th power — the inverse binomial
expansion, with the deep terms falling out of the digit. -/
private theorem bez_digits_of_box (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) {k : ℕ} {G : Polynomial O} (hG : G.Monic)
    (hGdeg : G.natDegree = e * k)
    (hbox : ∀ t, t < k → ∀ i, i < e →
        π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
          ∣ (dev (bezRawKey π u h e) G t).coeff i)
    {t : ℕ} (ht : t < k) :
    digAt π (h * (k - t)) (G.coeff (e * t))
      = (k.choose t : IsLocalRing.ResidueField O)
          * (- IsLocalRing.residue O (u : O)) ^ (k - t) := by
  have he' : 0 < e := by omega
  have hGdeg' : G.natDegree < (k + 1) * e := by
    rw [hGdeg]
    calc e * k < e * k + e := by omega
      _ = (k + 1) * e := by ring
  -- the block coefficient as a binomial combination of the raw-key digits
  have h1 := dev_X_pow_coeff he' hGdeg' (by omega : t < k + 1) 0
  rw [if_pos he', Nat.add_zero] at h1
  have h0 : G.coeff (e * t)
      = ∑ s ∈ Finset.Ico t (k + 1), (-((u : O) * π ^ h)) ^ (s - t) * (s.choose t : O)
          * (dev (bezRawKey π u h e) G s).coeff 0 := by
    rw [← h1, dev_X_pow_eq_bez he' hGdeg' (by omega : t < k + 1),
      Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl fun s _ => by rw [Polynomial.coeff_C_mul]
  -- the deep supply at `s < k` — the box at slot 0
  have hdeep : ∀ s, s < k →
      π ^ (h * (k - s) + 1) ∣ (dev (bezRawKey π u h e) G s).coeff 0 := by
    intro s hs
    have h3 := hbox s hs 0 he'
    rwa [bez_lat_exp_zero (h := h) he' (h * (k - s))] at h3
  -- the top digit is `1`
  have htop : dev (bezRawKey π u h e) G k = 1 :=
    dev_top (bezRawKey_monic he') (by rw [bezRawKey_natDegree]; exact he') hG
      (by rw [hGdeg, bezRawKey_natDegree, Nat.mul_comm])
  rw [h0, Finset.sum_Ico_succ_top (by omega : t ≤ k)]
  -- the deep part: strictly below the digit
  have hSdvd : π ^ (h * (k - t) + 1) ∣ ∑ s ∈ Finset.Ico t k,
      (-((u : O) * π ^ h)) ^ (s - t) * (s.choose t : O)
        * (dev (bezRawKey π u h e) G s).coeff 0 := by
    refine Finset.dvd_sum fun s hs => ?_
    obtain ⟨hs1, hs2⟩ := Finset.mem_Ico.mp hs
    obtain ⟨y, hy⟩ := hdeep s hs2
    have hkt : h * (k - t) + 1 = h * (s - t) + (h * (k - s) + 1) := by
      have hmul : h * (k - t) = h * (s - t) + h * (k - s) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega
    refine ⟨(-(u : O)) ^ (s - t) * (s.choose t : O) * y, ?_⟩
    rw [hy, ← neg_mul, mul_pow, ← pow_mul, hkt, pow_add]
    ring
  have hS' : π ^ (h * (k - t)) ∣ ∑ s ∈ Finset.Ico t k,
      (-((u : O) * π ^ h)) ^ (s - t) * (s.choose t : O)
        * (dev (bezRawKey π u h e) G s).coeff 0 :=
    dvd_trans (pow_dvd_pow π (by omega : h * (k - t) ≤ h * (k - t) + 1)) hSdvd
  -- the top term carries exactly the digit
  have heq : (-((u : O) * π ^ h)) ^ (k - t) * (k.choose t : O)
      * (dev (bezRawKey π u h e) G k).coeff 0
      = π ^ (h * (k - t)) * ((-(u : O)) ^ (k - t) * (k.choose t : O)) := by
    rw [htop, Polynomial.coeff_one_zero, ← neg_mul, mul_pow, ← pow_mul]
    ring
  have hT' : π ^ (h * (k - t)) ∣ (-((u : O) * π ^ h)) ^ (k - t) * (k.choose t : O)
      * (dev (bezRawKey π u h e) G k).coeff 0 :=
    ⟨(-(u : O)) ^ (k - t) * (k.choose t : O), heq⟩
  rw [digAt_add hπ hS' hT', (digAt_eq_zero_iff hπ hS').mpr hSdvd, zero_add,
    digAt_eq hπ heq, map_mul, map_pow, map_neg, map_natCast]
  ring

/-- ★★★ **THE SLOPE-`h/e` RESIDUAL-BOX TRANSFER CRITERION, digit form** — the
`h ≥ 2` replay of IFCG43's `eis_transfer_digits_iff` (C110's mechanism with
`π^{h(s−t)}` shifts): a monic block `G` of degree `e·k`, pure of slope `h/e`, has
lattice digits at heights `h(k−t)` reading `(X − ū)^k` IF AND ONLY IF its raw-key
development lies in the Bézout deep box (A) — exactly the Layer-2 named Prop's box
hypothesis.  Uniform in `q, h, e, k, u`, every DVR. -/
theorem bez_transfer_digits_iff (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) {k : ℕ} {G : Polynomial O} (hG : G.Monic)
    (hGdeg : G.natDegree = e * k)
    (hpure : ∀ j, j < e * k → π ^ ((h * (e * k - j) + (e - 1)) / e) ∣ G.coeff j) :
    (∀ t, t < k → ∀ i, i < e →
        π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
          ∣ (dev (bezRawKey π u h e) G t).coeff i)
      ↔ ∀ t, t < k →
          digAt π (h * (k - t)) (G.coeff (e * t))
            = (k.choose t : IsLocalRing.ResidueField O)
                * (- IsLocalRing.residue O (u : O)) ^ (k - t) :=
  ⟨fun hbox t ht => bez_digits_of_box (t := t) hπ hB he hG hGdeg hbox ht,
    fun hdig t ht i hi => bez_box_of_digits (t := t) (i := i) hπ hB he hG hGdeg
      hpure hdig ht hi⟩

/-- ★★★ **(RB), the sector-facing form** (design §5's
`resPoly_eq_pow_iff_bezoutBox`, xres currency): under the slope-`h/e` side pins, the
x-frame residual is the recentred `k`-th power `(X − ū)^k` IF AND ONLY IF the
`bezRawKey`-adic development lies in the Bézout deep box — IFCG44's landed
`xres_eq_pow_iff_digits_h` supplies the residual side; this file's transfer iff
supplies the box side.  The box condition is BYTE-IDENTICAL to the Layer-2 named
Prop's hypothesis, closing the loop between the census residual objects and the
correspondence surface. -/
theorem bez_xres_eq_pow_iff_box (hπ : Irreducible π) (hB : a * h = b * e + 1)
    (he : 2 ≤ e) {k : ℕ} {G : Polynomial O} (hG : G.Monic)
    (hGdeg : G.natDegree = e * k)
    (hpure : ∀ j, j < e * k → π ^ ((h * (e * k - j) + (e - 1)) / e) ∣ G.coeff j)
    (hne : (sideSet (Polynomial.X : Polynomial O) G h e).Nonempty)
    (hmin : sideMin (Polynomial.X : Polynomial O) G h e hne = 0)
    (hdeg : sideDeg (Polynomial.X : Polynomial O) G h e hne = k) :
    Uniformity.Density.IFCG37.xres π G h e hne (h * k)
        = (Polynomial.X - Polynomial.C (IsLocalRing.residue O (u : O))) ^ k
      ↔ ∀ t, t < k → ∀ i, i < e →
          π ^ ((e * (h * (k - t)) + 1 + e - 1 - h * i) / e)
            ∣ (dev (bezRawKey π u h e) G t).coeff i := by
  rw [Uniformity.Density.IFCG44.xres_eq_pow_iff_digits_h (z := (u : O)) hG hGdeg
    hne hmin hdeg, ← bez_transfer_digits_iff hπ hB he hG hGdeg hpure]

end TransferCriterion

/-! ### the box-exponent identity: the hostile test of the `+1` and carry conventions

Design §5: `Σ_{t<k} Σ_{i<e} λ_{t,i} = Σ_{j<ek} ⌈h(ek−j)/e⌉ + k` — the Bézout deep box
costs exactly the slope lattice PLUS one digit pin per slot, so its count identifies
with IFCG64's `card_slopeBox` exponent (`q^{ekN − Σ⌈⌉ − k}`). -/

section ExponentIdentity

variable {a b h e : ℕ}

/-- ★ **The box-exponent identity** (design §5): the total Bézout deep-box cost is
the slope-lattice cost plus exactly `k` — one `+1` per development slot, paid at the
`i = 0` coordinate (where the digit pin lives); every carry `q_i` cancels between the
two sides. -/
theorem bez_box_exponent_identity (hB : a * h = b * e + 1) (he : 2 ≤ e) (k : ℕ) :
    ∑ t ∈ Finset.range k, ∑ i ∈ Finset.range e,
        (e * (h * (k - t)) + 1 + e - 1 - h * i) / e
      = (∑ j ∈ Finset.range (e * k), (h * (e * k - j) + (e - 1)) / e) + k := by
  have he' : 0 < e := by omega
  -- per-slot: `λ_{t,i} = (slope exponent at j = e·t + i) + [i = 0]`
  have hslot : ∀ t ∈ Finset.range k, ∀ i ∈ Finset.range e,
      (e * (h * (k - t)) + 1 + e - 1 - h * i) / e
        = (h * (e * k - (e * t + i)) + (e - 1)) / e + (if i = 0 then 1 else 0) := by
    intro t ht i hi
    have ht' := Finset.mem_range.mp ht
    have hi' := Finset.mem_range.mp hi
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [if_pos rfl, bez_lat_exp_zero (h := h) he' (h * (k - t))]
      have hexp := bez_pure_exp (h := h) (i := 0) hB he' ht' he'
      rw [Nat.mul_zero, Nat.zero_div, Nat.sub_zero] at hexp
      rw [hexp]
    · rw [if_neg (by omega), bez_lat_exp_pos hB he' (by omega : 1 ≤ k - t) hipos hi',
        bez_pure_exp hB he' ht' hi', Nat.add_zero]
  -- sum the per-slot identity; the `ite` column contributes exactly `1` per `t`
  have hrow : ∀ t ∈ Finset.range k,
      ∑ i ∈ Finset.range e, (e * (h * (k - t)) + 1 + e - 1 - h * i) / e
        = (∑ i ∈ Finset.range e, (h * (e * k - (e * t + i)) + (e - 1)) / e) + 1 := by
    intro t ht
    rw [Finset.sum_congr rfl (hslot t ht), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq' (Finset.range e) 0 (fun _ => 1),
      if_pos (Finset.mem_range.mpr he')]
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, Nat.mul_one]
  congr 1
  -- the block reindex `j ↔ (t, i) = (j/e, j%e)` of the slope sum
  have hprod : (∑ t ∈ Finset.range k, ∑ i ∈ Finset.range e,
        (h * (e * k - (e * t + i)) + (e - 1)) / e)
      = ∑ p ∈ Finset.range k ×ˢ Finset.range e,
          (h * (e * k - (e * p.1 + p.2)) + (e - 1)) / e := by
    rw [Finset.sum_product]
  rw [hprod]
  refine Finset.sum_nbij' (fun p : ℕ × ℕ => e * p.1 + p.2)
    (fun j : ℕ => (j / e, j % e)) ?_ ?_ ?_ ?_ ?_
  · -- membership: `(t, i) ↦ e·t + i` lands in `range (e·k)`
    rintro ⟨t, i⟩ hp
    obtain ⟨ht, hi⟩ := Finset.mem_product.mp hp
    have ht' := Finset.mem_range.mp ht
    have hi' := Finset.mem_range.mp hi
    show e * t + i ∈ Finset.range (e * k)
    refine Finset.mem_range.mpr ?_
    have h1 : e * (t + 1) ≤ e * k := Nat.mul_le_mul_left e (by omega)
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega
  · -- membership: `j ↦ (j/e, j%e)` lands in the product
    intro j hj
    have hj' := Finset.mem_range.mp hj
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr
      (Nat.mod_lt _ he')⟩
    rw [Nat.div_lt_iff_lt_mul he']
    rwa [Nat.mul_comm]
  · -- left inverse
    rintro ⟨t, i⟩ hp
    obtain ⟨ht, hi⟩ := Finset.mem_product.mp hp
    have hi' := Finset.mem_range.mp hi
    have h1 : (e * t + i) / e = t := by
      rw [Nat.mul_add_div he', Nat.div_eq_of_lt hi', Nat.add_zero]
    have h2 : (e * t + i) % e = i := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
    show ((e * t + i) / e, (e * t + i) % e) = (t, i)
    rw [Prod.mk.injEq]
    exact ⟨h1, h2⟩
  · -- right inverse
    intro j _
    exact Nat.div_add_mod j e
  · -- value compatibility
    rintro ⟨t, i⟩ _
    rfl

end ExponentIdentity

end Uniformity.Density.IFCG75

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.IFCG75.bezout_exists
#print axioms Uniformity.Density.IFCG75.bezout_unique
#print axioms Uniformity.Density.IFCG75.bezout_coprime
#print axioms Uniformity.Density.IFCG75.bezout_hmul_mod_injOn
#print axioms Uniformity.Density.IFCG75.bezout_hmul_mod_surjOn
#print axioms Uniformity.Density.IFCG75.bez_recentring_stack
#print axioms Uniformity.Density.IFCG75.bez_root_irreducible
#print axioms Uniformity.Density.IFCG75.bez_map_pow_maximalIdeal
#print axioms Uniformity.Density.IFCG75.bez_root_pow
#print axioms Uniformity.Density.IFCG75.bezXi_pow_e
#print axioms Uniformity.Density.IFCG75.bezXi_pow_a
#print axioms Uniformity.Density.IFCG75.bezOrderMap_injective
#print axioms Uniformity.Density.IFCG75.bezXi_pow
#print axioms Uniformity.Density.IFCG75.bez_root_pow_dvd_orderMk_iff
#print axioms Uniformity.Density.IFCG75.bezThetaInv_bezTheta
#print axioms Uniformity.Density.IFCG75.bezTheta_bezThetaInv
#print axioms Uniformity.Density.IFCG75.bez_root_pow_dvd_theta_iff
#print axioms Uniformity.Density.IFCG75.bez_theta_level_iff
#print axioms Uniformity.Density.IFCG75.bezDevT_monic
#print axioms Uniformity.Density.IFCG75.bezReassT_monic
#print axioms Uniformity.Density.IFCG75.bezDevT_bezReassT
#print axioms Uniformity.Density.IFCG75.bezReassT_bezDevT
#print axioms Uniformity.Density.IFCG75.bezDevT_sub_root_pow_dvd
#print axioms Uniformity.Density.IFCG75.bezReassT_sub_pi_pow_dvd
#print axioms Uniformity.Density.IFCG75.bezCellTransport
#print axioms Uniformity.Density.IFCG75.bezCellTransport_apply
#print axioms Uniformity.Density.IFCG75.bezCellTransport_symm_apply
#print axioms Uniformity.Density.IFCG75.bezCellTransport_card_image
#print axioms Uniformity.Density.IFCG75.bez_card_coeff
#print axioms Uniformity.Density.IFCG75.slopeBezoutCellTypeScalingAt_of_correspondence
#print axioms Uniformity.Density.IFCG75.bez_transport_decidedAt_iff
#print axioms Uniformity.Density.IFCG75.bez_transport_decidedAt_iff_of_correspondence
#print axioms Uniformity.Density.IFCG75.bez_transfer_digits_iff
#print axioms Uniformity.Density.IFCG75.bez_xres_eq_pow_iff_box
#print axioms Uniformity.Density.IFCG75.bez_box_exponent_identity
end AxCheck
