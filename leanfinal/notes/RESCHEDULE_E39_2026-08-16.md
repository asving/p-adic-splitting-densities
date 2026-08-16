# RESCHEDULE record — NODE E.39 (`LB1Carrier`), Chapter-E fleet wave 4, agent 3

**Date.** 2026-08-16. **Verdict.** BLOCKED — one SIGNATURE-referenced definition not landed.
**Pre-check only; the carrier was not attempted, not weakened, no partial declaration committed.**

This agent's two other assignments LANDED this session:

| item | node | file | commit |
| --- | --- | --- | --- |
| `MidPeelEmission` + `MP1Carrier` (`(MP1)`, A-E.2 re-signed) | **E.40** | `leanfinal/Uniformity/ChapE/E40.lean` | `febcbe49` |
| `BlockSuite` (the FULL S1.7A record, A-E.2 signed) | **E.39a** | `leanfinal/Uniformity/ChapE/E39a.lean` | `965b704f` |

So the *content* of the E.39 re-sign is landed. What is blocked is the five-line carrier that
quantifies it.

## The block

E.39's A-E.2-signed SIGNATURE (`blueprint/CHAP-E_sigma_ladder.md` §6, lines ~2891–2897; twin
`leanspec/Leanspec/ChapE.lean:876-880`) is

```lean
def LB1Carrier {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) : Prop :=
  ∀ I : RungInterface.{uO, uK, uW} C B,
    (1 < I.sides.card ∨ ∃ p ∈ I.sides, ¬ I.SepSide p) →
    Nonempty (BlockSuite I)
```

The TRIGGER clause names **`RungInterface.SepSide`** — the numerical-shadow separability
predicate, which is **NODE E.14**'s `def` (blueprint line 1256):

```lean
def RungInterface.SepSide … (I : RungInterface C B) (p : ℕ × ℕ) : Prop :=
  (∀ q ∈ I.linFac p, q.2 = 1) ∧ (∀ q ∈ I.hiFac p, q.2 = 1)
```

There is **no `E14.lean`** in `leanfinal/Uniformity/ChapE/`, and
`grep -rn "SepSide" leanfinal/Uniformity/` returns exactly one hit — a prose mention in E.11's
module docstring — and no declaration. **RESCHEDULE: needs `RungInterface.SepSide` (E.14).**

The A-E.2 amendment is explicit that "names, binders and the TRIGGER are byte-preserved", so the
trigger is not paraphrasable: inlining `(∀ q ∈ I.linFac p, q.2 = 1) ∧ …` in place of
`I.SepSide p` would be a silent de-abbreviation of a frozen clause AND would collide with E.14
when it lands. Not done.

## What E.39 costs once E.14 lands

Five lines, in its own `leanfinal/Uniformity/ChapE/E39.lean`:

```lean
import Uniformity.ChapE.E14        -- RungInterface.SepSide
import Uniformity.ChapE.E39a       -- BlockSuite
```

then the `def` above verbatim. **`BlockSuite` must NOT be re-declared** — it is landed in
`E39a.lean` (twelve declarations, all Lean-core), and a second copy in the same namespace would
break the chapter roll-up. Everything else E.39 mentions (`SlotCarrier`, `BlockData`,
`RungInterface`, `sides`, `Finset.card`) is landed at E.10/E.11/E.12.

## Scope note — E.39a's landing is not a partial E.39

The distinction is the blueprint's/stub's own: `leanspec/Leanspec/ChapE.lean` §6 labels the
structure **`E.39a [structure, signed at A-E.2]`** and the carrier **`E.39 [def, RE-SIGNED at
A-E.2]`**. Landing the former without the latter states no obligation and discharges none:
`BlockSuite` is a record type, and until `LB1Carrier` exists nothing in `leanfinal` asserts that
a suite exists at a triggered state. Display A's `(LB1)` conjunct therefore remains **untranscribed**
on the Lean side, and chapter I cannot yet bind its `lb1` field (E.44 is likewise blocked on this,
independently of its own scheduling).

## Adjacent scheduling consequence

E.44 (`LadderObligations`, whose field list is `lb1 : LB1Carrier … , mp1 : MP1Carrier …`) now has
**one** of its two fields available (`MP1Carrier`, E.40, landed above). It stays blocked until
E.14 → E.39. E.41 (`clause12_lb1_free`) also reads `I.SepSide` in its hypotheses and is blocked on
E.14 for the same reason — scheduling E.14 unblocks three nodes at once (E.39, E.41, and, with
E.39, E.44).
