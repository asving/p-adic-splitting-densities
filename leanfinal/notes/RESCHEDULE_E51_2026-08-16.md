# RESCHEDULE record — NODE E.51 (`peel_row_law`), Chapter-E fleet wave 6, agent 2

**Date.** 2026-08-16. **Verdict.** **BLOCKED at the GC-13 resolution pre-check** — the chapter-C
anchor the socket must be typed against is **not landed in `leanfinal`**, and neither is the
vocabulary its statement is written in. **Nothing was attempted, nothing weakened, no partial
declaration committed.** The socket was NOT proved at the `True` placeholder (the blueprint and
the stub both forbid it: it would be vacuous), and it was NOT typed against an E-side
*restatement* of the chapter-C conclusion (see "Why not a restatement" below).

## What was asked, and the precedent it follows

Wave 6's charge: type E.51 the way **E.61/E.62 were typed today** (commits `4137d3cf`,
`87ec412b`) — the two `supplied : True` sockets of §9 were bound to chapter D's **landed**
carriers (`HVarthetaRes` at `ChapD/D62.lean`, `Wle`/`GentowW` at `ChapD/D55.lean`/`D44.lean`),
with the binding machine-checked as an `Iff` unit test inside the node file. That pass could run
because **chapter D is complete** (2026-08-16). The E.51 analogue cannot run, because chapter C
is not.

## The committed stub (verbatim, `leanspec/Leanspec/ChapE.lean:1078-1088`)

```lean
-- BLOCKED: GC-13 resolution (§12 BLOCKED-UNTIL-RESOLUTION; `hpeel : True` placeholder —
-- the orchestrator types it against chapter C's HE6R1-3 emission record at freeze. A fleet
-- agent must NOT prove E.51 while the placeholder is `True`: it would be vacuous.)
/-- **E.51** [theorem] The peel-row law (row 6, given the peel supplier). -/
axiom peel_row_law
    (hpeel : True)   -- placeholder anchoring the HE6R1-3 emission supplier
                     -- [supplied-by: chapter C]
    {e f : ℕ} (hforce4 : 4 ∣ e * f) (hef : e * f = 4)
    (he : 4 ∣ e ∨ (e = 4 ∧ f = 1)) :   -- the forcing shadow at μ₂′ = 1
    e = 4 ∧ f = 1
```

Blueprint twin: `blueprint/CHAP-E_sigma_ladder.md` §7 NODE E.51 (lines ~3578-3625), whose
SIGNATURE NOTE reads *"the orchestrator replaces it with C's typed HE6R1-3 record at freeze; a
fleet agent must NOT prove this node while the placeholder is `True`"*.

## The block: chapter C's HE6R1-3 emission record is not landed

The named supplier is **LEMMA HE6R1-3 = chapter C's NODE C.40 `level2_peel`**
(`blueprint/CHAP-C_tower_grammar.md` §5, lines ~2608-2665; stub twin
`leanspec/Leanspec/ChapC.lean:1589-1596`), whose conclusion IS the emission record E.51's
`hpeel` stands for:

```lean
axiom level2_peel {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hdvd : Ψ ∣ blockFactor L f) (hbox : CBox1Side L Ψ) :
    typeOf Ψ = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible Ψ ∧
    ∃ fS' : Polynomial O, blockFactor L f = Ψ * fS' ∧ ¬ Ψ ∣ fS' ∧
      fS'.natDegree = L.keyDeg₂ * (mult₂ L f - 1)
```

Pre-check evidence, this tree, 2026-08-16:

| needed | where it is signed | landed in `leanfinal`? |
| --- | --- | --- |
| `level2_peel` (C.40, the emission theorem) | `leanspec/Leanspec/ChapC.lean:1589` | **NO** — `grep -rn "level2_peel" leanfinal/` returns nothing; there is no `ChapC/C40.lean` |
| `blockFactor` (C.35 — in C.40's binders AND conclusion) | leanspec §5 (body elided; A-C.1 defect D2 calls it *"the single highest-value missing signature in the signed half of the chapter"*) | **NO** — two prose mentions only (`ChapC/C09.lean:67`, `ChapC/C38a.lean:43`), no declaration |
| `mult₂` (C.35 — in C.40's conclusion) | same | **NO** |
| `BlockContext` (C.33/C.34 context, C.40's `hctx`) | `leanspec/Leanspec/ChapC.lean:1593` | **NO** — `grep -rn "BlockContext" leanfinal/` returns nothing |
| `typeOf`, `LevelDatum` (C.09), `IsTestKey` (C.13), `CBox1Side` (C.60) | — | yes (landed) |

`leanfinal/Uniformity/ChapC.lean` jumps `C30 → C38a → C41`; §5's block layer (C.33-C.40) and §7's
Tier-1 emission (C.61, which C.40(ii) consumes) are both absent. **RESCHEDULE: needs
`Uniformity.Density.Tower.level2_peel` (C.40), which needs `blockFactor`/`mult₂` (C.35),
`BlockContext` (C.33/C.34) and `C.61`.**

## Why not a restatement (the amendment matter)

A tempting half-measure is to type `hpeel` as an E-side copy of C.40's first two conjuncts —
`typeOf Ψ = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible Ψ` — which *is* expressible
today (`typeOf`, `LevelDatum`, `IsTestKey` are landed). It was not done, for three reasons:

1. **No machine-checkable binding.** What made E.61/E.62 honest is that each node proves an `Iff`
   against the landed chapter-D declaration, so the socket cannot drift from the supplier. With
   C.40 absent there is nothing to prove an `Iff` against, and a hand-copied conclusion is exactly
   the shared-extraction shape that inherits any corruption in the copy.
2. **It moves E.51's signature far beyond a socket swap.** The record is stated over C's tower
   parameter block (`O`, `π`, `F : KeyFrame O π`, `H₀`, `hpin`, `L`, `Ψ`), none of which appears
   in the committed E.51 binders; adding them is a re-sign of the node, i.e. an amendment, not the
   resolution pass the blueprint delegates.
3. **`hpeel` is inert in the proof either way.** The Lean content of E.51 is the ℕ-arithmetic
   shell; `hpeel` is consumed by no step. Typing it wrongly would therefore never be caught by the
   build — the one situation where a by-name binding is doing all the work.

## Two signature observations for the resolution pass (not blockers, not patched here)

Both are about the arithmetic shell, and both are *hygiene*, not soundness:

* **`he`'s second disjunct is the conclusion.** `he : 4 ∣ e ∨ (e = 4 ∧ f = 1)` lets the theorem be
  discharged on that branch by `exact h`. The forcing shadow the blueprint describes ("`4 ∣ e*f`
  and `e*f = 4` forcing `(e,f) = (4,1)`" at `μ₂′ = 1`) is carried by the FIRST disjunct alone: with
  `hef : e * f = 4` and `4 ∣ e`, we get `e ∣ 4` and `4 ∣ e` with `e ≠ 0`, hence `e = 4`, `f = 1`.
  The honest hypothesis is `he : 4 ∣ e`.
* **`hforce4` is redundant.** `4 ∣ e * f` follows from `hef : e * f = 4` by `dvd_refl`-after-`rw`,
  so it constrains nothing.

Recommend both be settled in the same amendment that types `hpeel`, so E.51 is re-signed once.

## Consumers (unaffected today)

E.52 `he7a_prime_schema` is explicitly **not** blocked (§12: "it consumes E.51's row only through
`mu2Sigma`"), and `mu2Sigma .peelRow = some ⟨{(4,1),(4,1)}⟩` is landed at
`leanfinal/Uniformity/ChapE/E49.lean`. So the peel ROW of the six-row dictionary is available to
E.52 regardless of this block; what is missing is only the LAW that the row is the right one, and
that law's content is chapter C's.
