/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E50

/-!
# Uniformity.ChapE.E51 — the peel row: the ARITHMETIC SHELL, and the placeholder defect

**Chapter E, NODE E.51** [theorem] (`blueprint/CHAP-E_sigma_ladder.md` §7 NODE E.51, line
3616), ENV-E1.

**⚠ THE SIGNED NAME `peel_row_law` IS DELIBERATELY *NOT* LANDED BY THIS FILE.**  The node is one
of chapter E's four BLOCKED-UNTIL-RESOLUTION sockets (§12: E.51, E.57, E.61, E.62), and its own
SIGNATURE NOTE forbids the landing outright:

> *"The `hpeel : True` placeholder is DELIBERATE and survives only until GC-13 resolution: the
> orchestrator replaces it with C's typed HE6R1-3 record at freeze; a fleet agent must NOT prove
> this node while the placeholder is `True` (it would be vacuous) — the node is BLOCKED until
> resolution, and §12's stub list marks it so."*

The stub carries the same fence (`leanspec/Leanspec/ChapE.lean:1121-1123`).  The GC-13 resolution
pre-check was re-run at this commit and **still fails**: the named supplier, chapter C's
NODE C.40 `level2_peel` (LEMMA HE6R1-3), has no landed declaration.  See §3 and the record
`leanfinal/Uniformity/ChapE/E51_BLOCKED_2026-08-20.md`.

## What IS landed here

Three theorems and two statement carriers — no `axiom`, no `sorry`, and **not** the signed name:

* `peel_row_arith` — the HONEST content of the quotient leg, exactly as the E.51 SIGNATURE NOTE
  describes it (*"the honest Lean content of the quotient leg is the arithmetic … the rest is
  the C-supplied emission"*): `4 ∣ e → e * f = 4 → e = 4 ∧ f = 1`.  This is the whole ℕ-level
  content of the node, banked, so the resolution pass is a one-liner.
* `peel_row_arith_of_shadow` — the same conclusion from the frozen DISJUNCTIVE forcing shadow
  `4 ∣ e ∨ (e = 4 ∧ f = 1)`, i.e. the frozen `he` binder.
* `PeelRowLawFrozen` / `PeelRowLawArith` (statement carriers, `def … : Prop`, per A-C.8.5's
  "statement carriers, never temporary axioms") and
* `peelRowLawFrozen_iff_arith` — **the defect certificate**: the frozen TYPE is *equivalent* to
  the bare ℕ arithmetic.  So the two inert binders provably carry nothing, and the frozen
  statement provably carries none of the peel content its name advertises.  This is the finding,
  machine-checked; it is NOT an assertion that the peel-row law holds.

## §0 BINDER-VACUITY AUDIT — committed BEFORE any proving (per the unit charge)

Checklist: `blueprint/CHAP-C_tower_grammar.md` A-C.8.4 (generalises across chapters), against the
A-C.7 registry's four collapse shapes.  **Verdict: THREE degeneracies in the frozen signature,
one of them the deliberate placeholder and two of them new findings.**  Classification per the
charge's three-way distinction (vacuous defect / provably always satisfied, restricts nothing /
load-bearing and sharp):

| frozen binder | verdict | evidence |
|---|---|---|
| `hpeel : True` | **RESTRICTS NOTHING — the deliberate placeholder (defect E-D<GC-13>)** | `True` is inhabited by `trivial`, so the binder can never fail and can never be consumed. It is not a *vacuous* guard in the A-C.7 sense (it does not empty the hypothesis set — it is the OPPOSITE failure: it empties the CONTENT). Its intended content — chapter C's HE6R1-3 emission record — is absent from the type, so a landed `peel_row_law` would advertise the peel emission while proving ℕ arithmetic. This is why the blueprint blocks the node, and this file honours the block. |
| `hforce4 : 4 ∣ e * f` | **RESTRICTS NOTHING — new finding, machine-checked** | it follows from `hef : e * f = 4` by `hef ▸ dvd_refl 4`. Landed as `hforce4_redundant` below, so the claim is a theorem, not a comment. |
| `he : 4 ∣ e ∨ (e = 4 ∧ f = 1)` | **HALF LOAD-BEARING, HALF THE CONCLUSION — new finding** | the SECOND disjunct *is* the conclusion, so on that branch the theorem is discharged by `exact h` and proves nothing. The forcing shadow the blueprint describes is carried by the FIRST disjunct alone, and that branch is genuinely load-bearing and SHARP: dropping `4 ∣ e` leaves `e * f = 4` with the counterexamples `(e,f) = (1,4)`, `(2,2)`, both of which satisfy every other frozen binder and refute the conclusion. Landed as `peel_row_shadow_sharp` below (the two counterexamples, machine-checked). The honest hypothesis is `he : 4 ∣ e`. |
| `hef : e * f = 4` | **LOAD-BEARING, SHARP** | without it, `4 ∣ e` alone permits `(e,f) = (8,1)`, refuting `e = 4`. Machine-checked in `peel_row_shadow_sharp`. |
| `{e f : ℕ}` implicit | fine | inhabited at `(4,1)`, the intended instance; the conclusion is realized, so the statement is not vacuously true by an empty domain. |

Collapse shapes checked and ABSENT: no unpinned carrier field (C.111 — no structure); no
self-loop over a quantified relation (C.94 — no relation); no inert `Nonempty` (C.113 — `hpeel`
is the *`True`* variant of that shape and is recorded as such above); no implication-guarded
`≠ ⊤` / unguarded top stratum (C.118 — no valuation appears).

**GC-1 (`blueprint/CONVENTIONS_2026-08-15.md`, the `H₀`/base-height pin at `sideMin`) —
CHECKED, NOT ENGAGED by the landed content.**  GC-1 binds *"E (any node consuming HE6's
slot-seam evaluations)"* and *"any future node that mentions `resPoly`/`H₀`"*.  Neither
`resPoly` nor `H₀` nor any polygon/side object occurs in E.51's frozen signature or in anything
landed here — the node's Lean content is ℕ arithmetic.  **Forward obligation, recorded for the
resolution pass:** the SUPPLIER is not GC-1-free.  C.40 `level2_peel` reads through `CBox1Side`
and `blockFactor`, i.e. through the residual layer, so when `hpeel` is typed against C.40 the
`sideMin` pin becomes live and the typed socket must inherit the REPAIRED pin (never the
abscissa-`0` one).

## Consumers — unaffected by the block

E.52 `he7a_prime_schema` is explicitly NOT blocked (§12: *"it consumes E.51's row only through
`mu2Sigma`"*), and `mu2Sigma .peelRow = some ⟨{(4,1),(4,1)}⟩` is landed at
`Uniformity/ChapE/E49.lean`.  So the peel ROW of the six-row dictionary is available regardless;
what is missing is only the LAW that the row is the right one, and that law's content is chapter
C's.

**SOURCE.** `EFF.HE7.60` (the peel row, verbatim derivation); `EFF.HE7.09` (the peel
convention).  **TEETH.** `he7r1_supp.py` A4/A5 (2/2 PARI on σ(f) AND σ(Ψ)) — the oracle evidence
is the SUPPLIER's machine leg, recorded in §13, not this file's.

## Status

Sorry-free, axiom-free (Lean core only); footprints printed at the end of the file.  The signed
`peel_row_law` remains OPEN.
-/

namespace Uniformity.Density.Ladder

/-! ## 1. The honest arithmetic content -/

/-- **E.51's honest quotient leg.**  At `μ₂′ = 1` every root of `f′` is a level-2 point, so the
peel degree `D″ = 4` divides the local degree (LEMMA HE6-0′) — the shadow `4 ∣ e` — and with
`e·f = 4` this forces `(e, f) = (4, 1)`, i.e. `f′` irreducible.  ℕ arithmetic; the emission that
justifies the shadow is chapter C's. -/
theorem peel_row_arith {e f : ℕ} (he : 4 ∣ e) (hef : e * f = 4) : e = 4 ∧ f = 1 := by
  have he4 : e ∣ 4 := ⟨f, hef.symm⟩
  have hE : e = 4 := Nat.dvd_antisymm he4 he
  subst hE
  exact ⟨rfl, by omega⟩

/-- The same conclusion from the frozen DISJUNCTIVE shadow (the frozen `he` binder). -/
theorem peel_row_arith_of_shadow {e f : ℕ} (he : 4 ∣ e ∨ (e = 4 ∧ f = 1))
    (hef : e * f = 4) : e = 4 ∧ f = 1 := by
  rcases he with he | he
  · exact peel_row_arith he hef
  · exact he

/-! ## 2. The audit findings, as theorems -/

/-- **§0 finding 2, machine-checked.**  `hforce4` restricts nothing. -/
theorem hforce4_redundant {e f : ℕ} (hef : e * f = 4) : 4 ∣ e * f := by
  rw [hef]

/-- **§0 findings 3 and 4, machine-checked.**  Both surviving hypotheses are SHARP: dropping the
forcing shadow `4 ∣ e` admits `(e,f) = (2,2)` (and `(1,4)`); dropping `e·f = 4` admits
`(e,f) = (8,1)`. -/
theorem peel_row_shadow_sharp :
    (2 * 2 = 4 ∧ ¬ (2 = 4 ∧ 2 = 1)) ∧ (1 * 4 = 4 ∧ ¬ (1 = 4 ∧ 4 = 1))
      ∧ ((4 : ℕ) ∣ 8 ∧ ¬ ((8 : ℕ) = 4 ∧ (1 : ℕ) = 1)) := by
  refine ⟨⟨by norm_num, by omega⟩, ⟨by norm_num, by omega⟩, ⟨by norm_num, by omega⟩⟩

/-! ## 3. The defect certificate — the frozen TYPE is bare arithmetic -/

/-- The frozen E.51 type, as a statement carrier (`leanspec/Leanspec/ChapE.lean:1125-1130`,
byte-frozen).  Carried as a `def … : Prop`, never asserted. -/
def PeelRowLawFrozen : Prop :=
  ∀ (_hpeel : True) {e f : ℕ}, 4 ∣ e * f → e * f = 4 → (4 ∣ e ∨ (e = 4 ∧ f = 1)) →
    e = 4 ∧ f = 1

/-- The honest arithmetic shell, as a statement carrier. -/
def PeelRowLawArith : Prop := ∀ {e f : ℕ}, 4 ∣ e → e * f = 4 → e = 4 ∧ f = 1

/-- **THE DEFECT CERTIFICATE (§0 findings 1–3 together).**  The frozen type is EQUIVALENT to the
bare ℕ arithmetic: the `hpeel : True` placeholder and the redundant `hforce4` provably carry
nothing, and the disjunctive shadow adds nothing beyond its first disjunct.  Hence a landed
`peel_row_law` would advertise the peel-row law (*"`Ψ` emits `(e,f) = (4,1)`"*) while delivering
arithmetic — which is exactly why the blueprint BLOCKS the node until `hpeel` is typed against
chapter C's HE6R1-3 emission record.  This is a certificate ABOUT the frozen type, not an
assertion of the law. -/
theorem peelRowLawFrozen_iff_arith : PeelRowLawFrozen ↔ PeelRowLawArith := by
  constructor
  · intro h e f he hef
    exact h trivial (hforce4_redundant hef) hef (Or.inl he)
  · intro h _hpeel e f _hforce4 hef he
    exact peel_row_arith_of_shadow (he.imp id id) hef

end Uniformity.Density.Ladder

/-! ## 4. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.peel_row_arith
#print axioms Uniformity.Density.Ladder.peel_row_arith_of_shadow
#print axioms Uniformity.Density.Ladder.hforce4_redundant
#print axioms Uniformity.Density.Ladder.peel_row_shadow_sharp
#print axioms Uniformity.Density.Ladder.PeelRowLawFrozen
#print axioms Uniformity.Density.Ladder.PeelRowLawArith
#print axioms Uniformity.Density.Ladder.peelRowLawFrozen_iff_arith

end AxCheck
