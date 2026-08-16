/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D04
import Uniformity.ChapD.D13

/-!
# Uniformity.ChapD.D06 — ★ THE ϑ FOUR-WAY ORIENTATION TABLE (anchor `D-THETA-TABLE`)

**Chapter D, NODE D.06** [table] [fresh] (`blueprint/CHAP-D_gauge_tchain.md` §3, anchor
`D-THETA-TABLE`; amendments A-1, A-D.1, A-D.2 govern — the TEETH row is A-D.1 re-signed, and
this file lands every tooth it lists). ENV-D2. One public declaration (the inversion theorem)
plus the file-local FRAME-C battery that executes the table.

**AUTHORITY.** The blueprint anchor `D-THETA-TABLE` (CHAP-D node D.06) is the ONE canonical
copy of the orientation table — GC-14, and PROJECT_STATE append #54's mandate ("the gauge
chapter's blueprint carry the four-way orientation table as a node annotation, else a sign
error no battery catches"). Chapters C, E and F cite the anchor and **no chapter restates the
content in its own words.** The transcription below is this node's own Lean-side copy of its
own anchor, kept for the reader of the Lean file; **if it ever differs from the blueprint, the
blueprint wins and this file is the defect.**

## The table (transcribed from the anchor, node D.06)

GENTOW2's single-argument, slot-indexed unit is the reference. Slots `t < f₃`; under the
substitution `s := f₃ − t`, its defining display (`EFF.GENTOW2.41`) is
`ϑ(t) := res((n̂₂(u₃(f₃−t)) / n̂₂(u₃)^{f₃−t})(x₀)) = res(n̂₂(su₃)/n̂₂(u₃)^s)` — numerator at the
SLOT height, denominator the `(f₃−t)`-th power of the TOP-SLOT normalizer.

1. **GENTOW2** `ϑ(t)` `= res((n̂₂(u₃(f₃−t))/n̂₂(u₃)^{f₃−t})(x₀))` — the reference. Lean name:
   `varthetaG2` (D.10).
2. **T1** `(C3-Theta)` `Θ_i(t) = ϑ_{i,f_{i+1}−t}⁻¹ = res(n̂_i((f_{i+1}−t)u_{i+1}) /
   n̂_i(u_{i+1})^{f_{i+1}−t})`. Relation: **`ϑ(t) = Θ₂(t)`** — the same object; hence GENTOW2's
   `ϑ` is the **INVERSE** of T1's two-index `ϑ_{i,s}`. Lean: `theta` at `s = f_{i+1}−t`, while
   T1's `ϑ_{i,s}` is `vartheta` (group level: D.04's `thetaEl` / `varthetaEl`).
3. **T3** `(T1-THETA)`/`(ABS-G2)` `Θ_N(s;q) = ϑ_N(s;q)⁻¹ = res(N(sq)/N(q)^s)`, and
   `ϑ_{G2}(t) := res(n̂₂(su₃)/n̂₂(u₃)^s) = Θ_N(s;u₃)`. Relation:
   **`ϑ(t) = ϑ_{G2}(t) = Θ_N(f₃−t; u₃)`**; T3 records the inverse orientation explicitly at its
   §8.1 check 2. Lean: `theta` — the same object as row 2.
4. **GENTOW5** `LEMMA GENTOW5-A1` `vartheta_t` (source L214–215):
   `theta_t := [n̂₂(λ)(x₀)]^t·[n̂₂(tλ)(x₀)]⁻¹ = ι(vartheta_t)`. Relation: **RECIPROCAL** —
   A1's `theta_t = res(n̂₂(λ)^t/n̂₂(tλ))`, so **`ϑ(t) = vartheta_{f₃−t}⁻¹` at `λ = u₃`**, the
   exact pair append #54's trap names. GENTOW2 itself **DECLINES to adjudicate** this
   correspondence (its NON-IMPORT N-7) — which is why THIS TABLE, not either note alone, is the
   authority. Lean: A1's `theta_t` is `vartheta u₃ t` (T1 orientation, argument `t`, NOT
   `f₃−t`).
5. **T5** L991–993, the reconciliation: "B″'s single-argument `ϑ(t)` is this note's `Θ₂(t)`,
   the inverse-telescope orientation" — the acceptance-pass verdict that closes the loop,
   **VERIFIED** (T5 ledger item 2, byte span `33f86204` L729–738, ledger md5-8 `d4c8b885`,
   raw-span md5 `8978f8ba…`; both legs re-checked at EFF compile time, `EFF.GENTOW2.25`). A
   verification record, not a new object.

**THE B-LAW DIRECTION — separate, and NOT to be conflated with the Θ/ϑ inversion.**
`u(β) := R_{3,β}(n̂₂(β̂))` is an FGMN-side read of a repo-side object, and direction (3) of
`LEMMA GENTOW2-B′` reads **`FGMN = u·repo`**, i.e. `R_{3,β}(g) = u(β)·digit(g)` — **NOT the
inverse** (`EFF.GENTOW2.34`'s orientation record; the r2 F3 finding exists because a fallback
clause once wrote the inverse convention). T1's `(C3-B-law)` `u(β_t) = Θ_i(t)·w_i^{f_{i+1}−t}`
and T3's `(ABS-G2)` `u(β_t) = ϑ_{G2}(t)·w^{f₃−t}` agree in that orientation — all three sides
consistent, and D.33 states the Lean form in exactly it. The battery below scores this
direction at FRAME-C (`U(s) = Θ_s·w^s` passes, `U(s) = ϑ_s·w^s` FAILS at `s = 2`).

**TOP-SLOT NORMALIZATION ANCHOR.** `ϑ(f₃−1) = 1`: the top slot `t = f₃−1` has `s = 1`, and
`κ̄ = β_{f₃−1}` gives `ϑ(f₃−1) = res(n̂₂(u₃)/n̂₂(u₃)¹) = 1` (`EFF.GENTOW2.41`'s orientation
record) — T3's §8.1 item 1 (`ϑ_N(0;q) = ϑ_N(1;q) = 1`) is the same anchor in T1 orientation
(both orientations agree at `s ∈ {0,1}` since `1⁻¹ = 1`). Lean forms: D.05's
`varthetaEl_zero`/`varthetaEl_one` at group level, D.09 residue-side, and the executed anchor
leg below.

## The Lean content of the node

The inversion, as a theorem — the executable half of the sign discipline:
`thetaEl_mul_varthetaEl : Θ_N(s;q)·ϑ_N(s;q) = 1` (T3 §8.1 check 2's content, group level).
Rows 2–3 of the table ARE this identity; row 1 is it read at the reflected index `s = f₃−t`;
row 4 is the reciprocal pair. The `K`-valued form is D.10's `varthetaG2`.

## Faithfulness

**⚠ Trust-boundary transcription.** Four points, flagged for the chapter cross-read:

* *the inversion is a theorem, not a definitional identity.* D.04 defines `varthetaEl` and
  `thetaEl` independently, each as its own source display spells it (`n(q)^s·n(sq)⁻¹` and
  `n(sq)·(n(q)^s)⁻¹`), precisely so that this node's `Θ·ϑ = 1` has content to check. A
  transcription that defined `thetaEl := (varthetaEl)⁻¹` would make the theorem `rfl` and the
  table unfalsifiable.
* *the ARGUMENT of the theorem is `s`, the T1 two-index slot count — not the GENTOW2 slot `t`.*
  The reindexing `s = f_{i+1} − t` is a CONSUMER's job (D.33, D.58), never baked in. A reader
  who silently reads `s` as `t` gets row 2 backwards; that is append #54's trap, and the
  reflection leg below (`ϑ_{G2}(t) ≠ Θ(t)` at `t = 1` and `t = 4`) is its battery.
* *`f₃`, slots and the letter group do not appear in the Lean statement.* The theorem is pure
  ENV-D2 group algebra over an arbitrary `CommGroup`; the tower data enters at D.07/D.10 and
  the `i = 2` letter-valuedness (`EFF.GENTOW2.42`: `ϑ` is `x₀`-free and letter-valued) is
  chapter C's, consumed at D.42.
* *the battery is FRAME-C data, file-local and `private`.* The six `private def`s below are the
  gate-verified stub's FRAME-C data (`leanspec/Leanspec/ChapD.lean` §10, where they are named
  `gate67vartheta`/`gate67thetaL`/`gate67theta`/`gate67U`/`gate06varthetaG2`/`gate06A1theta`);
  they are re-declared here under a uniform `gate06` prefix and `private`, so this node adds no
  public name (GC-6.5 is not engaged) and cannot collide with D.67's own landed copies.

DEPENDS: D.04 (`NormSection.varthetaEl`, `NormSection.thetaEl`, landed at
`Uniformity.ChapD.D04`) for the signed theorem. The file additionally imports D.13
(`Uniformity.ChapD.D13`) for `iexp` and the reducer `iexp_one` — a GATE-SIDE dependency only:
FRAME-C's `ϑ` is ASSEMBLED from D.18's exponent formula `ϑ_s = η^{⌊s·i(u₂)/e₁⌋}`, never
committed as literal data, and `iexp` is D.13's. The signed theorem depends on neither.

**PROOF.** The blueprint's: unfold both definitions; `group`. No commutativity is needed —
`n(sq)·(n(q)^s)⁻¹·(n(q)^s·n(sq)⁻¹)` cancels inside-out in any group — so `group` closes it as
written.

SOURCE: GC-14 (the czar pin — content re-transcribed from the specs, not from the pin);
`EFF.GENTOW2.25` (the `[TABLE]` at L1065–1075 including L1072, and the T5-verification
record), `.34` (the B-law direction record), `.41` (the defining display + top-slot anchor),
`.42` (`ϑ` is `x₀`-free and letter-valued); `EFF.T1.14` (`(C3-Theta)`, `(C3-B-law)`);
`EFF.T3.04` (`(T1-THETA)`), `EFF.T3.19` (`(ABS-G2)`); GENTOW5-A1 row: `EFF-GENTOW2.md:1072`
(per GC-14 — GENTOW5's own spec carries the merged-ID twin; C's author resolves it, GC-12);
T5 source L991–993 (row 5); FRAME-C values `EFF.T3.29`.

**TEETH** *(A-D.1 re-signed, 2026-08-16 — the trap NOW HAS AN EXECUTABLE BATTERY)*. Append
#54's premise ("a sign error no battery catches") is **superseded for this table**: the
stage-0e gate executed all four rows at FRAME-C (`f₃ = 5`, every quantity a concrete
`𝔽₅`-unit). The teeth, all landed here except where they name another node: (i) this node's
Lean inversion theorem; (ii) D.10's `K`-valued form; (iii) the executed `decide` legs below —
the involution `Θ_s·ϑ_s = 1` on `s = 0…5`, the top-slot anchor `ϑ(f₃−1) = 1`, **row 4's
reciprocal relation `ϑ_{G2}(t)·vartheta_{f₃−t} = 1`** (the exact GENTOW2/GENTOW5-A1 pair append
#54 names), and the numerical DISTINCTNESS of the two orientations; (iv) gate D.67's numeric
orientation leg (`U(s) = Θ_s·w^s` at the FRAME-C tables), landed below in its D.06 form; and
(v) the `ORIENTATION:` field discipline on every ϑ-touching node of chapters C/D/E/F. **The two
teeth that are NEW** (quoted from the gate's header): *"the wrong-orientation B-law
(`U(s) = ϑ_s·w^s`) now FAILS at `s = 2`, and the orientation swap FAILS at `t = 1` and
`t = 4`."* A silent row-1-for-row-4 swap is therefore a failing `decide`, not an undetectable
sign error.

⚠ **Scoring discipline, FINDING D-F3.** The distinctness leg must be scored at `t = 1` or
`t = 4` — FRAME-C has `ϑ₂ = ϑ₃ = 2` (both floors `⌊s/2⌋` equal 1), so an index-shift mutant
SURVIVES at the middle slots. The last two legs below are that discipline: the reflection is
scored at `t = 1` AND `t = 4`, and the middle-slot collision `Θ₂ = Θ₃` is landed as an
explicit witness so no later reader re-scores it there.

⚠ **FINDING D-F2.** FRAME-C's committed `ϑ`/`U` tables run `s = 0…4`, but the table's
`ϑ_{G2}(t) = Θ(f₃−t)` at the BOTTOM slot `t = 0` reads the telescope at `s = f₃ = 5`, one step
beyond. The assembled formula extends it (`ϑ_5 = 2^{⌊5/2⌋} = 4`, `Θ_5 = 4`) and the extension
is executed below, so the literal `Θ` table carries six entries, not five.

**A-D.1 VERDICT ON THE TABLE ITSELF** (2026-08-16, stage-0e gate): *"the four rows plus the
B-law direction block plus the top-slot anchor are MUTUALLY CONSISTENT"* — checked symbolically
row by row and then executed; **no sign error found**. This discharges the mechanical half of
blueprint §14 item 1 (the byte-check of the transcription against the four specs is still
owed). Executed values at FRAME-C: `ϑ = (1,1,2,2,4,4)` and `Θ = (1,1,3,3,4,4)` on `s = 0…5`.

ENVIRONMENT: ENV-D2 (`{G : Type*} [CommGroup G]`, written inline per the B.42 binder rule —
this file has no `variable` block); the battery is ENV-D1-flavoured `ZMod` arithmetic and is
`private`.

## Status

Sorry-free, axiom-free (Lean core only). The inversion is a PROVED theorem here, not the
leanspec `axiom` stub; every battery leg is an executed `decide`.
-/

namespace Uniformity.Density.Gauge

/-- ★ `D-THETA-TABLE`.  The two telescope orientations are mutually inverse:
`Θ_N(s;q)·ϑ_N(s;q) = 1` (T3 §8.1 check 2's content, group level).  Consumers: see the four-way
orientation table at blueprint anchor `D-THETA-TABLE` (CHAP-D node D.06).
ORIENTATION: the involution itself — rows 1–3 of the table made a theorem. -/
theorem NormSection.thetaEl_mul_varthetaEl {G : Type*} [CommGroup G]
    (N : NormSection G) (q : ℤ) (s : ℕ) :
    N.thetaEl q s * N.varthetaEl q s = 1 := by
  simp only [NormSection.thetaEl, NormSection.varthetaEl]
  group

end Uniformity.Density.Gauge

/-! ## THE TABLE, EXECUTED at FRAME-C (`p = 5`, `f₃ = 5`, `e₁ = 2`, `h = 1`, `η = 2`, `w = 3`)

The table's four rows as arithmetic, at the one frame where every quantity is a concrete
`𝔽₅`-unit (`EFF.T3.29`). Rows 1/2/3 are ONE object, row 4 is its RECIPROCAL at the reflected
index, and the two are numerically DISTINCT — so a silent swap is a failing `decide`.

Gate-writing rider (A-D.1/D-D1, mandatory): `iexp` routes through `ZMod.inv`, which does NOT
kernel-reduce, so every row that mentions `iexp` reduces through D.13's proved `iexp_one`
BEFORE deciding — `simp only [<local defs>, iexp_one]; decide`, never a bare `decide`. Per
SD-7, `Θ` and `U` are committed as LITERAL DATA and then CHECKED (the involution certifies
`Θ`, the two runner obligations certify `U`), so the legs below are genuine checks rather than
unfoldings; only `ϑ` is assembled, from D.18's exponent formula. -/

section Frames

open Uniformity.Density.Gauge

/-- FRAME-C's `ϑ`, ASSEMBLED from D.18's exponent formula `ϑ_s = η^{⌊s·i(u₂)/e₁⌋}` at
`e₁ = 2, h = 1, η = 2, u₂ = 1` — never from the endpoint formula (`EFF.T3.29`'s own
instruction). -/
private def gate06vartheta (s : ℕ) : ZMod 5 := (2 : ZMod 5) ^ (s * iexp 2 1 1 / 2)

/-- FRAME-C's `Θ_s = ϑ_s⁻¹` (table rows 2–3), as LITERAL DATA (defect D-D1: `ZMod.inv` does
not kernel-reduce, so the inverse cannot be spelled); committed here and CHECKED against `ϑ` by
the involution leg below.  Six entries, not five — FINDING D-F2's bottom-slot extension. -/
private def gate06thetaL : List (ZMod 5) := [1, 1, 3, 3, 4, 4]

/-- `Θ` as a function of the T1 two-index slot count `s`. -/
private def gate06theta (s : ℕ) : ZMod 5 := gate06thetaL.getD s 0

/-- FRAME-C's committed `U` table (the B-law's FGMN-side read), as LITERAL DATA — so the two
runner obligations below are genuine checks, not unfoldings. -/
private def gate06U : List (ZMod 5) := [1, 3, 2, 1, 4]

/-- **Row 1** (GENTOW2's `ϑ(t)`) `= Θ(f−t)`, i.e. rows 2/3 read at the reflected index — the
reference object of the table. -/
private def gate06varthetaG2 (f t : ℕ) : ZMod 5 := gate06theta (f - t)

/-- **Row 4** (GENTOW5-A1's `theta_t`) `=` T1's `ϑ_{i,t}` at argument `t`, NOT `f−t`. -/
private def gate06A1theta (t : ℕ) : ZMod 5 := gate06vartheta t

/-- The assembled telescope reproduces `EFF.T3.29`'s committed table `ϑ = (1,1,2,2,4)` on
`s = 0…4`. -/
example : (List.range 5).map (fun s => gate06vartheta s) = [1, 1, 2, 2, 4] := by
  simp only [gate06vartheta, iexp_one]; decide

/-- FINDING D-F2, executed: the bottom slot `t = 0` reads `s = f₃ = 5`, one step beyond the
committed range; the assembled formula gives `ϑ_5 = 2^{⌊5/2⌋} = 4`. -/
example : gate06vartheta 5 = 4 := by
  simp only [gate06vartheta, iexp_one]; decide

/-- **Rows 2–3, as the involution** `Θ_s·ϑ_s = 1` on `s = 0…5` (this node's theorem, at
FRAME-C) — the certificate that the committed `Θ` table really is the inverse-orientation
telescope. -/
example : ∀ s ∈ List.range 6, gate06theta s * gate06vartheta s = 1 := by
  simp only [gate06theta, gate06thetaL, gate06vartheta, iexp_one]; decide

/-- The runner obligation `w^s = U(s)·ϑ_s` at `w = 3`, all five `s` — the certificate for the
committed `U` table. -/
example : ∀ s ∈ List.range 5,
    (3 : ZMod 5) ^ s = gate06U.getD s 0 * gate06vartheta s := by
  simp only [gate06vartheta, gate06U, iexp_one]; decide

/-- The runner obligation in the B-LAW ORIENTATION: `U(s) = Θ_s·w^s` (the direction block
above; T1's `(C3-B-law)`, T3's `(ABS-G2)`), all five `s`. -/
example : ∀ s ∈ List.range 5,
    gate06U.getD s 0 = gate06theta s * (3 : ZMod 5) ^ s := by
  simp only [gate06theta, gate06thetaL, gate06U]; decide

/-- **MUTATION-KILLER 1 (NEW at A-D.1).** Writing the B-law in the WRONG orientation (`ϑ` where
`Θ` belongs) FAILS at `s = 2`: `ϑ₂·3² = 2·4 = 3 ≠ 2 = U(2)`.  The sign error `EFF.T1.45` /
append #54 says no battery catches now HAS a battery. -/
example : gate06U.getD 2 0 ≠ gate06vartheta 2 * (3 : ZMod 5) ^ 2 := by
  simp only [gate06vartheta, gate06U, iexp_one]; decide

/-- **The top-slot normalization anchor** `ϑ(f₃−1) = 1` (`EFF.GENTOW2.41`), together with the
T1-orientation form `ϑ_1 = Θ_1 = 1` — both orientations agree at `s ∈ {0,1}`. -/
example : gate06varthetaG2 5 4 = 1 ∧ gate06vartheta 1 = 1 ∧ gate06theta 1 = 1 := by
  simp only [gate06varthetaG2, gate06theta, gate06thetaL, gate06vartheta, iexp_one]; decide

/-- **Row 4's RECIPROCAL relation** `ϑ(t) = vartheta_{f₃−t}⁻¹` at `λ = u₃`
(`EFF-GENTOW2.md:1072`) — the exact GENTOW2/GENTOW5-A1 pair append #54 names, stated
multiplicatively (defect D-D1: no `ZMod.inv`). -/
example : ∀ t ∈ List.range 5,
    gate06varthetaG2 5 t * gate06A1theta (5 - t) = 1 := by
  simp only [gate06varthetaG2, gate06A1theta, gate06theta, gate06thetaL, gate06vartheta,
    iexp_one]
  decide

/-- **MUTATION-KILLER 2 (NEW at A-D.1), part 1.** The two orientations are numerically
DISTINCT, so a silent swap of row 1 for row 4 is caught: at `t = 2`, row 1 gives `3` and row 4
gives `2`. -/
example : gate06varthetaG2 5 2 ≠ gate06A1theta 2 := by
  simp only [gate06varthetaG2, gate06A1theta, gate06theta, gate06thetaL, gate06vartheta,
    iexp_one]
  decide

/-- **MUTATION-KILLER 2, part 2 — the reflection `t ↦ f₃−t` is not the identity either:**
`ϑ_{G2}(t) ≠ Θ(t)`.  ⚠ FINDING D-F3: scored at `t = 1` AND `t = 4`, NOT at `t = 2`/`t = 3`. -/
example : gate06varthetaG2 5 1 ≠ gate06theta 1 ∧ gate06varthetaG2 5 4 ≠ gate06theta 4 := by
  simp only [gate06varthetaG2, gate06theta, gate06thetaL]; decide

/-- FINDING D-F3's witness, landed so that no later reader re-scores the leg above at a middle
slot: FRAME-C really does have `Θ₂ = Θ₃` (equivalently `ϑ₂ = ϑ₃ = 2`, both floors `⌊s/2⌋`
equal `1`), where an index-shift mutant SURVIVES. -/
example : gate06theta 2 = gate06theta 3 := by
  simp only [gate06theta, gate06thetaL]; decide

end Frames

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.NormSection.thetaEl_mul_varthetaEl

end AxCheck
