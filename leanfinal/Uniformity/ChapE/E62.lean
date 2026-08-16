/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D63

/-!
# Uniformity.ChapE.E62 — `WFrame`, the `𝒲_(≤i)` w-frame socket, TYPED

**Chapter E, NODE E.62** [def] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §9 — the
`(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` indexed carriers). ENV-E1 (plus chapter D's arena, imported).

The second half of Display A's `∀ i ≥ 3` conjunct, and the second of the chapter's four
BLOCKED-UNTIL-RESOLUTION sockets (§12: E.51, E.57, E.61, E.62): the blueprint signs it
`structure WFrame (i : ℕ) : Prop where supplied : True`, with ALL content chapter D's
(`EFF.T5 [supplied-by: chapter D]`, BRIEF D product (4): *"the `𝒲_(≤i)` carriers that
Display A's `∀ i ≥ 3` conjunct consumes (hand off to E/I by name)"*), E declaring only the
socket. **The GC-13 resolution is executed here**, against the LANDED chapter-D carriers
(chapter D complete, 2026-08-16): the field is D.55's cumulative `Wle` at D.44's
`GentowW` family.

## What the socket says

For a tower whose level-`j` gauge arena is `A j`, use-height `q j`, residual read `R j` and
peel unit `w j` (chapter D's T5 data — `EFF.T3.21`'s `θ_j(t) = Θ_N(s;u_{j+1})` and
`w_j = R_{j+1,κ̄_j}(n̂_j(u_{j+1}))`),

```
WFrame A q R w i   ↔   ∀ j, 3 ≤ j → j ≤ i → GentowW (A j) (q j) (R j) (w j)
                   =   ⋀_{3 ≤ j ≤ i} [GENTOW5-W(j)]      (D.55's `Wle` at D.44's family)
```

— the w-frame holding at every level up to `i`, which is exactly D.63's stated intended
instantiation of its `W` slot (`Wle W i` with `W q := GentowW` at the level-`q` data). The
`Iff` is machine-checked below, so the binding is a term, not a comment.

## Why the family is bound concretely (and not left abstract)

D.55/D.63 keep the `W` slot an abstract `ℕ → Prop` — deliberately, so that chapter D can state
the conjunct without naming chapter C's tower. Chapter E is where the ladder's levels live, so
the socket is bound at D's named carrier `GentowW` instead: an abstract-family socket
`WFrame W i := Wle W i` is dischargeable by `W := fun _ => True`, which is the same
fabricability class as the D-D12 defect that voided the pre-A-D.2 `(H-VARTHETA-RES)` form
(`HVarthetaResVoided`, machine-refuted, deliberately NOT in scope anywhere in `leanfinal`).
Binding at `GentowW` keeps the socket's strength at the ledger's: the level-`j` reads
`R j (N.n (s·q j)) = Θ(q j, s)·(w j)^s` must genuinely hold.

**This is a hypothesis carrier and NOTHING here discharges it.** Chapter C's C.89 (the
`[GENTOW5-W(i)]` open transported lemma) records the honest status: `i = 2` unconditional,
`i = 1` shape-only with the tie `u1 = w₁` OPEN, and **`i ≥ 3` OPEN** — the honest-sorry
analogue, carried into the capstone. Per the Part V owner ruling the conjunct's terminal
disposition is chapter I's: DISCHARGE NODE or LITERATURE CITE. Consistent with D.55's
non-discharge discipline (`EFF.T5.29`, ledger `HYP.63` CARRY), this file contains no theorem
concluding `WFrame … i` at any `i ≥ 3`.

## The signature delta against the committed stub (honest record)

Frozen by the blueprint and preserved: the NAME `WFrame`, the single field's name `supplied`,
the INDEX `i : ℕ` as the LAST explicit argument, and the consumption route (chapter I's
Display-A block consumes the conjunct through E.24/E.63). Left open by the blueprint and
supplied here: the field's TYPE, plus the level-indexed T5 data `(A, q, R, w)` as explicit
parameters — parameters and not existentially bundled fields ON PURPOSE (an `∃ data` wrapper is
the fabricable shape D-D12 refuted). Implicit/explicit split mirrors D.44's `GentowW`
(`{G} {K} {N}` implicit — inferable from `A` — families explicit).

**Consumer obligation created (flagged for the orchestrator, not patched here):** E.63's
`DeepTwistConjunct := ∀ i, 3 ≤ i → VarthetaRes i ∧ WFrame i` and, through E.24, I.10's `ladder`
field must thread the same level data when they land; neither is landed in this tree yet, so no
landed signature moves today. E.61 (landed today, same wave) received the parallel typing
against D.62.

## Faithfulness

**⚠ Mandatory, trust-boundary definition** (parent CLAUDE.md trust boundary; one definition).
Three recasts to check on the chapter cross-read:

* *the `𝒲` leg is CUMULATIVE, the HVR leg is per-rung.* `Wle` ranges over `3 ≤ j ≤ i`; E.61's
  socket reads index `i` alone. `EFF.T5.10` says the two families are two different conditional
  stacks on the same displays that must not be conflated, and D.63's fence repeats it; keeping
  the cumulation inside this socket and out of E.61's is that fence, structurally.
* *the range starts at 3, inside the carrier.* `Wle`'s `3 ≤ j` is D.55's, not an E-side choice;
  at `i ≤ 2` the conjunction is EMPTY, so `WFrame A q R w 2` holds outright (D.55's `Wle_two`)
  — machine-checked below. ⚠ That is a statement about an empty range and says NOTHING at
  `i ≥ 3`, where the leg is live and undischarged. It is the `n ≤ 2` slice the blueprint's
  TEETH row hands to chapter I's gates, and the arithmetic shadow of E.63's vacuity clause.
* *one arena family, one `q`/`R`/`w` family, no coherence asserted between levels.* The socket
  says nothing about how level `j`'s data relates to level `j+1`'s (no compatibility field);
  that bookkeeping belongs to chapter C's tower and to D's T-chain, and asserting it here would
  silently strengthen the carried hypothesis.

**DEPENDS.** D.55 (`Wle`), D.44 (`GentowW`, transitively imported), D.63 (`VarthetaWConjunct` —
the conjunct this socket is the `W` half of; the plug is checked below). Chapter C's C.89 is the
same hypothesis family on C's own tower objects; it is not landed in this tree, and this node
does not restate it.

**SOURCE.** ledger Display A (the `(H-VARTHETA-RES)_i ∧ 𝒲_(≤i)` `∀ i ≥ 3` conjunct, rows
HYP.57/HYP.63 — status CARRY); BRIEF D product (4) and BRIEF E product (4) (the hand-off by
name); `EFF.T3.22` (the `𝒲_{≤n}` conjunction), `EFF.T5.10` (the two stacked families),
`EFF.T5.13` (the cumulative hypothesis and its empty base), `EFF.T5.29` (non-discharge);
`EFF.GENTOW5.27` S11.2/S11.3 via C.89 (the three-regime honest status).

**TEETH.** none (a socket); chapter I's gates re-fire the `n ≤ 2` slices where the conjunct is
empty. GENTOW2 PE6's w-measurement (w-avatar ≠ 1 at 6 primes / 4 frames) is chapter C's
executable regression showing `w = 1` is NOT generic — i.e. the carrier is not idle.

**ENVIRONMENT.** ENV-E1.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Ladder

open Uniformity.Density.Gauge

/-- **NODE E.62** — `𝒲_(≤i)` (Display A, `∀ i ≥ 3`): the w-frame holds through level `i`.
Content [supplied-by: chapter D (T5)]; E declares the socket.

**TYPED AT THE GC-13 RESOLUTION** against the landed chapter-D carriers: the field is D.55's
cumulative `Wle` at D.44's `GentowW` family, i.e. `⋀_{3 ≤ j ≤ i} [GENTOW5-W(j)]` over the
level-`j` gauge arena `A j`, use-height `q j`, read `R j` and peel unit `w j` — D.63's stated
intended instantiation of its `W` slot. A CARRIER: `[GENTOW5-W(i)]` is OPEN at `i ≥ 3`
(chapter C's C.89, the honest-sorry analogue), nothing in chapter D or E discharges it, and the
terminal disposition is chapter I's (DISCHARGE NODE or LITERATURE CITE). -/
structure WFrame {G : Type*} [CommGroup G] {K : Type*} [Field K] {N : NormSection G}
    (A : ℕ → GaugeArena G K N) (q : ℕ → ℤ) (R : ℕ → G → K) (w : ℕ → Kˣ) (i : ℕ) : Prop where
  supplied : Wle (fun j => GentowW (A j) (q j) (R j) (w j)) i

/-- The binding, as a unit test rather than a comment: the socket unfolds to chapter D's
cumulative w-frame at the intended `GentowW` family (D.55 at D.44). Nothing is discharged —
this is a shape statement at arbitrary supplied data. -/
example {G : Type*} [CommGroup G] {K : Type*} [Field K] {N : NormSection G}
    {A : ℕ → GaugeArena G K N} {q : ℕ → ℤ} {R : ℕ → G → K} {w : ℕ → Kˣ} {i : ℕ} :
    WFrame A q R w i ↔ ∀ j, 3 ≤ j → j ≤ i → GentowW (A j) (q j) (R j) (w j) :=
  ⟨fun h => h.supplied, fun h => ⟨h⟩⟩

/-- The consumption route, as a unit test: the socket is a legal `W` half of D.63's
`VarthetaWConjunct` — plugged there, the conjunct is exactly `HVR i ∧ 𝒲_(≤i)` with the `𝒲` leg
at this socket. This is the shape chapter I's Display-A block consumes (through E.24/E.63); it
asserts neither leg. -/
example {G : Type*} [CommGroup G] {K : Type*} [Field K] {N : NormSection G}
    {A : ℕ → GaugeArena G K N} {q : ℕ → ℤ} {R : ℕ → G → K} {w : ℕ → Kˣ} (HVR : ℕ → Prop)
    (i : ℕ) :
    VarthetaWConjunct HVR (fun j => GentowW (A j) (q j) (R j) (w j)) i ↔
      HVR i ∧ WFrame A q R w i :=
  ⟨fun h => ⟨h.1, ⟨h.2⟩⟩, fun h => ⟨h.1, h.2.supplied⟩⟩

/-- The `n ≤ 2` slice (D.55's `Wle_two`, D.63's TEETH row): at `i = 2` the range `3 ≤ j ≤ 2` is
EMPTY, so the socket holds outright. ⚠ This says NOTHING at `i ≥ 3`, where `[GENTOW5-W(j)]` is
open (C.89(iii)) and this chapter discharges nothing. -/
example {G : Type*} [CommGroup G] {K : Type*} [Field K] {N : NormSection G}
    (A : ℕ → GaugeArena G K N) (q : ℕ → ℤ) (R : ℕ → G → K) (w : ℕ → Kˣ) :
    WFrame A q R w 2 :=
  ⟨Wle_two _⟩

end Uniformity.Density.Ladder

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Ladder.WFrame

end AxCheck
