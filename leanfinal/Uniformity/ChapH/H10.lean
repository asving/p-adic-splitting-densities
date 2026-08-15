/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.ZMod.Basic
import Uniformity.ChapH.H07
import Uniformity.ChapH.H08

/-!
# Uniformity.ChapH.H10 — every height above `D′h` is occupied

**Chapter H, NODE H.10** (`blueprint/CHAP-H_general_induction.md` §3). For a genre datum `G`
(H.01) and a `dv`-height `m` strictly above the key-degree height `D′h = keyDeg · h` (H.02), the
height is **occupied** (H.07): there is an integral normalizer monomial `n(m) = x^i π^a` with
`0 ≤ i < e₁`, `a ≥ 0` and `i·h + e₁·a = m`. Consequently every stage-initial node floor
`G.nodeHeight j`, `j < μ`, is occupied, because H.08(i) puts every floor strictly above `D′h`.

## The proof, in words

`LEMMA GENHN-LIFT`'s construction, verbatim. Since `gcd(h, e₁) = 1`, the class of `h` is a **unit**
of `ZMod e₁`, so `x := (h)⁻¹ · m` solves `x · h = m` there; take `i := x.val`, which is `< e₁` by
`ZMod.val_lt`. The residue equation lifts to `i·h ≡ m [MOD e₁]`, and the *integrality* step is the
inequality `i·h ≤ m`:

`i·h < e₁·h ≤ (e₁ f₁)·h = D′h < m`,

where the middle step needs only `1 ≤ f₁` (which `hkey : 2 ≤ e₁ f₁` forces). With `i·h ≤ m` the
congruence becomes the divisibility `e₁ ∣ m − i·h` (`Nat.modEq_iff_dvd'`), and
`a := (m − i·h) / e₁` is the exponent asked for.

The degenerate case `e₁ = 1` needs no separate treatment here: `ZMod 1` is trivial, `x.val = 0`,
and the construction returns `(i, a) = (0, m)` on its own.

DEPENDS: H.01 (`GenreDatum`), H.02 (`GenreDatum.keyDeg`, `GenreDatum.nodeHeight`), H.07
(`GenreDatum.Occupied`), H.08 (`GenreDatum.keyDeg_mul_h_lt_nodeHeight`).

SOURCE: `EFF.GENHN.81` (`LEMMA GENHN-LIFT`'s hypothesis and its integrality step, verbatim:
*"Let `M > D'h = e_1f_1h`, and let `i = i(M)`, `0 ≤ i < e_1`, be determined by
`ih ≡ M (mod e_1)`, `a = (M − ih)/e_1`"* and *"Since `i + e_1s ≤ D'−1` and `M > D'h`,
`a − sh = (M − (i+e_1s)h)/e_1 ≥ 0`"*); `EFF.GENHN.09` (the owner re-display's clause: *"Every
height `m > D′h` is occupied, with the explicit lift supplied by `LEMMA GENHN-LIFT`"*).

ARITHMETIC AUDIT (blueprint, recomputed): the chain `e₁ ≤ keyDeg = e₁ f₁` needs `1 ≤ f₁`, which
follows from `2 ≤ e₁ f₁`; then `i·h ≤ (e₁−1)·h < e₁·h ≤ keyDeg·h < m`. At the first-live genres:
E `(e₁,f₁,h) = (2,1,1)` gives `keyDeg·h = 2`, so every `m ≥ 3` is occupied, and the node floors
are `nodeHeight 0 = 2·2·1+1 = 5`, `nodeHeight 1 = 1·2·1+1 = 3`, both `> 2`; F `(1,2,1)` gives
`keyDeg·h = 2` and floors `5, 3`; E31 `(3,1,1)` gives `keyDeg·h = 3` and floors `7, 4`. All of
these are re-executed in the numeric gate below, together with the *negative* control at the A2
witness `(e₁,h) = (3,2)`, where the sub-`D′h` height `m = 1` is genuinely unoccupied (H.11) — so
the hypothesis `keyDeg·h < m` is load-bearing, not decorative.

TEETH: **PROOF-ONLY at the corrected scope** (`EFF.GENHN.09`: *"No battery row exercises an
unoccupied height: every row has `f₁ = 1` and every consumed pin sits at `dv > D′h`"*).
Disposition: `decorrelated-model audit` for the *scope*, **Lean theorem** for the lemma — this
file discharges the latter.

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- **NODE H.10.** *Every height above `D′h` is occupied.* For `keyDeg · h < m` the `dv`-height
`m` carries an integral normalizer monomial `x^i π^a` with `i < e₁` — the `GENHN-LIFT`
construction `i ≡ h⁻¹ m (mod e₁)`, `a = (m − i h)/e₁`. -/
theorem GenreDatum.occupied_of_keyDeg_mul_h_lt (G : GenreDatum) {m : ℕ}
    (hm : G.keyDeg * G.h < m) : G.Occupied m := by
  -- `1 ≤ f₁`: otherwise `e₁ f₁ = 0`, contradicting `hkey`.
  have hf₁ : 0 < G.f₁ := Nat.pos_of_ne_zero fun h0 => by
    have hk := G.hkey; rw [h0, Nat.mul_zero] at hk; omega
  have he₁ : 0 < G.e₁ := G.he₁
  haveI : NeZero G.e₁ := ⟨Nat.pos_iff_ne_zero.mp he₁⟩
  -- `h` is a unit mod `e₁` (coprimality), so `m` is in the image of `· * h`.
  obtain ⟨x, hxu⟩ : ∃ x : ZMod G.e₁, x * (G.h : ZMod G.e₁) = (m : ZMod G.e₁) := by
    refine ⟨(m : ZMod G.e₁) *
      (((ZMod.unitOfCoprime G.h G.hcop)⁻¹ : (ZMod G.e₁)ˣ) : ZMod G.e₁), ?_⟩
    have hcu : ((ZMod.unitOfCoprime G.h G.hcop : (ZMod G.e₁)ˣ) : ZMod G.e₁) = (G.h : ZMod G.e₁) :=
      ZMod.coe_unitOfCoprime G.h G.hcop
    rw [← hcu]
    exact Units.inv_mul_cancel_right _ _
  have hxlt : x.val < G.e₁ := ZMod.val_lt x
  -- Integrality: `i·h < e₁·h ≤ keyDeg·h < m`.
  have hstep : x.val * G.h < G.e₁ * G.h := mul_lt_mul_of_pos_right hxlt G.hh
  have hkeydef : G.keyDeg = G.e₁ * G.f₁ := rfl
  have hwide : G.e₁ * G.h ≤ G.keyDeg * G.h := by
    rw [hkeydef]
    exact Nat.mul_le_mul_right G.h (Nat.le_mul_of_pos_right G.e₁ hf₁)
  have hle : x.val * G.h ≤ m := by omega
  -- The congruence, hence the divisibility, hence the exponent `a`.
  have hmod : x.val * G.h ≡ m [MOD G.e₁] := by
    refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact hxu
  have hdvd : G.e₁ ∣ m - x.val * G.h := (Nat.modEq_iff_dvd' hle).mp hmod
  refine ⟨x.val, (m - x.val * G.h) / G.e₁, hxlt, ?_⟩
  have hcancel : G.e₁ * ((m - x.val * G.h) / G.e₁) = m - x.val * G.h := Nat.mul_div_cancel' hdvd
  omega

/-- **NODE H.10, corollary.** Every stage-initial node floor is occupied: H.08(i) puts
`G.nodeHeight j` strictly above `D′h` for every `j < μ`, which is exactly the terminal scope of
the lift. -/
theorem GenreDatum.occupied_nodeHeight (G : GenreDatum) {j : ℕ} (hj : j < G.μ) :
    G.Occupied (G.nodeHeight j) :=
  G.occupied_of_keyDeg_mul_h_lt (G.keyDeg_mul_h_lt_nodeHeight hj)

end Uniformity.Density.Induction

/-! ## Numeric gate — the lift, brute-forced.
`#guard` fails elaboration when the proposition evaluates to `false`, so these are build-time
checks. `Occupied` itself is an unbounded `∃` and is not decidable, but the witness search is:
for `m ≤ 39` any solution of `i·h + e₁·a = m` has `a ≤ m`, so the bounded search below is
exhaustive over exactly the same solution set. -/

section NumericGate

/-- Bounded witness search for `∃ i < e₁, ∃ a, i·h + e₁·a = m` (exhaustive for `a ≤ m`). -/
private def occupiedB (e₁ h m : ℕ) : Bool :=
  (List.range e₁).any fun i => (List.range (m + 1)).any fun a => i * h + e₁ * a == m

-- The lemma itself on the three genre columns of the blueprint's audit — E `(e₁,f₁,h) = (2,1,1)`,
-- F `(1,2,1)`, E31 `(3,1,1)` — plus a wild column `(2,1,3)` and a two-prime column `(3,2,2)`,
-- swept over every height `m ≤ 39`: whenever `keyDeg·h < m`, the height is occupied.
#guard [(2, 1, 1), (1, 2, 1), (3, 1, 1), (2, 1, 3), (3, 2, 2)].all fun t =>
  (List.range 40).all fun m =>
    !decide (t.1 * t.2.1 * t.2.2 < m) || occupiedB t.1 t.2.2 m

-- Node floors: `nodeHeight j = (μ − j)·keyDeg·h + 1` at `μ = 2`. E and F give `(5, 3)`, E31 gives
-- `(7, 4)`; the corresponding `keyDeg·h` are `2`, `2`, `3` — every floor strictly above.
#guard [((2, 1), 1), ((1, 2), 1), ((3, 1), 1)].all fun t =>
  let keyDeg := t.1.1 * t.1.2
  let h := t.2
  (List.range 2).all fun j => keyDeg * h < (2 - j) * keyDeg * h + 1

#guard (2 - 0) * (2 * 1) * 1 + 1 == 5 && (2 - 1) * (2 * 1) * 1 + 1 == 3
#guard (2 - 0) * (1 * 2) * 1 + 1 == 5 && (2 - 1) * (1 * 2) * 1 + 1 == 3
#guard (2 - 0) * (3 * 1) * 1 + 1 == 7 && (2 - 1) * (3 * 1) * 1 + 1 == 4

-- NEGATIVE control (the A2/R4 witness of H.11, `(Q; e₁,f₁,μ; h) = (2; 3,1,2; 2)`): the height
-- `m = 1` sits BELOW `keyDeg·h = 3` and is genuinely unoccupied, so the hypothesis of the lemma
-- is load-bearing.
#guard !occupiedB 3 2 1

end NumericGate

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.GenreDatum.occupied_of_keyDeg_mul_h_lt
#print axioms Uniformity.Density.Induction.GenreDatum.occupied_nodeHeight

end AxCheck
