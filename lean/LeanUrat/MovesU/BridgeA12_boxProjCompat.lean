/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeA9_boxPolyEquiv
import LeanUrat.MovesU.BridgeA11_boxEquivD

/-!
# IB-A12 — (†3c) `boxProj` compatibility: polynomial reduction and digit truncation

E-phase skeleton per `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.2 (†3c) /
§4 group A (IB-A12).

INFORMAL STATEMENT: the level reduction `boxProj p n (h : N ≤ N')` corresponds
(a) under (†2)'s polynomial dictionary to `Polynomial.map (ZMod.castHom …)` —
    reducing the coefficient box then reading the polynomial IS reading the
    polynomial then mapping coefficients along `ZMod (p^N') →+* ZMod (p^N)`;
(b) under (†3)'s digit dictionary to DIGIT TRUNCATION — for k < N the (i,k)
    slot read of the reduced box equals the (i,k) slot read of the original
    (the low N digits of `v mod p^N` are the low N digits of v).
Consumed by the `canonical_stable` plumbing (IB-D8) "and by nothing else"
(blueprint §3.2).

DEPS: IB-A9 (`boxPolyEquiv`), IB-A11 (`boxEquivD`).

PROOF SKETCH:
* (a) `boxProj_toPoly` at the raw `Box.toPoly`: push `Polynomial.map` through
  `X^n + Σ_i C (f i) X^i` (`Polynomial.map_add`/`map_pow`/`map_X`/
  `Polynomial.map_sum`/`map_C`); `boxProj`'s definition IS the castHom applied
  entrywise (MovesU/Defs.lean:44).  `boxPolyEquiv_boxProj` is its restatement
  through the (†2) equiv (toFun := `Box.toPoly` definitionally).
* (b) `boxEquivD_boxProj`: `ZMod.castHom` reads as val-reduction —
  `(castHom … (f i)).val = (f i).val % p^N` (`ZMod.castHom_apply` +
  `ZMod.val_natCast` route); then digit stability below the cut,
  `((v % p^N) / p^k) % p = (v / p^k) % p` for k < N (div/mod arithmetic:
  `Nat.mod_pow_div`-style telescoping — v % p^N and v differ by a multiple of
  p^{k+1} for k < N).

TRANSCRIPTION RESOLUTIONS (recorded): (i) "boxProj ↔ Polynomial.map castHom
under (†2)" is transcribed TWICE — once at the raw `Box.toPoly` (the working
form, guard-free) and once through `boxPolyEquiv` (the literal (†2) reading,
carrying both level guards); (ii) "digit truncation under (†3)" is transcribed
in the `digitIdx` vocabulary as slot-read stability at every k < N — the
truncation map on raw `MovesD.Box` indices is NOT introduced (the interleaved
i·N + k layout makes the slotwise form the faithful one; no consumer reads a
raw truncation map); (iii) the embedded `Fin N ↪ Fin N'` is spelled
`⟨(k : ℕ), lt_of_lt_of_le k.isLt h⟩`.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU
open Polynomial

/-- IB-A12(a), raw form — level reduction commutes with the polynomial read:
    `Box.toPoly (boxProj p n h f) = (Box.toPoly f).map (ZMod.castHom …)`. -/
theorem boxProj_toPoly (p n : ℕ) [Fact p.Prime] {N N' : ℕ} (h : N ≤ N')
    (f : Box p n N') :
    Box.toPoly (boxProj p n h f)
      = (Box.toPoly f).map (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N))) :=
  sorry

/-- IB-A12(a), (†2) form — the same law read through `boxPolyEquiv` on both
    levels (toFun is `Box.toPoly` definitionally). -/
theorem boxPolyEquiv_boxProj (p n : ℕ) [Fact p.Prime] {N N' : ℕ} (h : N ≤ N')
    (hN : 0 < N) (hN' : 0 < N') (f : Box p n N') :
    (boxPolyEquiv p n N hN (boxProj p n h f)).1
      = (boxPolyEquiv p n N' hN' f).1.map
          (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ N))) :=
  sorry

/-- IB-A12(b), (†3) form — level reduction is digit truncation: below the cut
    (k < N) the (i,k) slot read of the reduced box equals the (i,k) slot read
    of the original box. -/
theorem boxEquivD_boxProj (p n : ℕ) [Fact p.Prime] {N N' : ℕ} (h : N ≤ N')
    (hN : 0 < N) (hN' : 0 < N') (f : Box p n N') (i : Fin n) (k : Fin N) :
    boxEquivD p n N hN (boxProj p n h f) (digitIdx n N i k)
      = boxEquivD p n N' hN' f
          (digitIdx n N' i ⟨(k : ℕ), lt_of_lt_of_le k.isLt h⟩) :=
  sorry

end LeanUrat.MovesU
