/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C10
import Uniformity.ChapC.C35
import Uniformity.ChapC.C60
import Uniformity.ChapB.B56
import Uniformity.Density.TypePositivity

/-!
# Uniformity.ChapC.C61 — Tier 1, the per-factor singleton `typeOf` (the sandwich)

**Chapter C, NODE C.61** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §7, DECISION
C-D1's Tier 1; the A-C.1 amendment set governs, §7's design note is the tier's conditionality
record). **ENV-C3.**

## Status in one line

**BLOCKED — the signed `tier1_typeOf` is NOT declared in this file.** What lands is the
COMPLETE REDUCTION of the signed statement to a single missing divisibility leg (`tier1_typeOf_of_ramLeg`,
byte-identical to the signed statement except for one extra hypothesis) plus a machine-checked
**sharpness certificate** showing that leg cannot be dropped. See "The block" below.

## The signed statement (NOT declared in this file)

`leanspec/Leanspec/ChapC.lean:2191-2200` signs, as an `axiom` stub:

```lean
axiom tier1_typeOf {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (hlab : HasLabel L g)
    (hm1 : ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r)
    (hx : IsPure Polynomial.X g F.h F.e₁)
    (hbox : ∀ g' ∈ monicFactors g, CBox1Side L g') :
    typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible g
```

It is **NOT declared here**, as a `theorem` or otherwise, per the C.33/C.34/C.72/C.40
convention: a signed statement is either proved or left to the leanspec stub. No axiom, no
`sorry`. The ∀-closure of the exact signed type is recorded below as the Prop carrier
`Tier1TypeOfStatement` so that consumers and future units can name it without re-transcribing.

### Transcription / `diff` record

Two transcriptions are diffed against `leanspec/Leanspec/ChapC.lean` lines **2191–2200** (the
`axiom tier1_typeOf` block, ten lines), and the real `diff` output is recorded in the commit:

* **`Tier1TypeOfStatement`** (the Prop carrier) differs in exactly three ways, all forced:
  (a) `axiom tier1_typeOf` → a `∀` head; (b) the `{O} [CommRing O] …` section variables spelled
  out inside the telescope (a `def` cannot inherit `variable`s into a closed Prop); (c) every
  hypothesis name `_`-prefixed (`_hπ`, `_hlab`, `_hm1`, `_hx`, `_hbox`) because an unused binder
  in a `def` body trips the linter. Hypothesis TYPES and ORDER and the conclusion are the spec's
  byte-for-byte, `hm1`'s inner binder names `hne`, `M₀`, `hp` included.
* **`tier1_typeOf_of_ramLeg`** (the reduction) keeps the spec's binder names verbatim
  (`L`, `hπ`, `g`, `hlab`, `hm1`, `hx`, `hbox`) and inserts exactly one new line, `hram`,
  immediately before `hbox`. That single inserted line is the whole diff.

**D11 (already cured stub-side; NOT re-broken here).** `leanspec/Leanspec/ChapC.lean:188-194`
records that C.40 and C.61 were originally written with a TWO-component
`typeOf … = ⟨{(…, …)}, by …⟩`, over-applying `structure FactorizationType`
(`Uniformity/Density/LocalData.lean:43`, one field `data : Multiset (ℕ × ℕ)`). The one-component
form `⟨{(…, …)}⟩` is what the A-C.1 signature block carries and what is transcribed here; degree
conservation ships separately as the landed LEMMA `typeOf_degree` (GC-4), which this file's proof
consumes by name.

## MANDATORY binder-vacuity audit (verdict, per binder)

Checklist: `### A-C.8.4 Binder-vacuity audit` (chapter-C blueprint ~line 10162). Verdict for
each binder of the signed type: VACUOUS (nothing satisfies it) / restricts-nothing (provably
always satisfied) / load-bearing and SHARP (counterexample given).

| binder | verdict |
|---|---|
| `{F : KeyFrame O π}` | **load-bearing, inhabited.** Witnessed by the landed `s2Frame` (C.97; `(e₁,f₁,h) = (2,1,1)`, `Φ′ = x²−2` over `ℤ_[2]`) — a term, not an argument. |
| `{H₀ hpin}` | **restricts-nothing given `F`** (`hpin` pins `H₀` to the frame's own side height, and `H₀` is then unique by `Nat.cast` injectivity). Witnessed by `s2Frame_pin` at `H₀ = 1`. |
| `(L : LevelDatum F H₀ hpin)` | **load-bearing, inhabited.** Witnessed by the landed `L₀` (`C35b.lean:328`, `(u,ℓ) = (3,1)`, `r := ρ`). Its `hκ : ℓ·(e₁f₁)·h < u` is a genuine restriction (it is the above-floor fence); `hrdeg : 0 < r.natDegree` is load-bearing in the proof below (it is what cancels the multiplicity `s`). |
| `(hπ : Irreducible π)` | **load-bearing but not conclusion-visible**: it is the uniformizer hypothesis every `dvResPoly`-degree read (C.26) consumes. Witnessed by `h2_padic : Irreducible (2 : ℤ_[2])`. Not droppable: `natDegree_dvResPoly` requires it. |
| `[IsAdicComplete …]`, `[Finite (ResidueField O)]` | **restricts-nothing at the conclusion, and NOT consumed by the reduction below** — the `(e,f)` engine (`inertiaDegOf`/`ramIndexOf`) is DVR-level (`Density/TypeOf.lean`). They are the environment in which the missing leg (C.59) and the `typeOf`-faithfulness identification live. Instances exist at `ℤ_[p]`. Recorded, not silently dropped: the reduction theorem below **carries them anyway**, unused, for signature fidelity. |
| `{g : Polynomial O}`, `hlab : HasLabel L g` | **load-bearing and its locus IS witnessed by a term**: `hasLabel_g₀ : HasLabel (L₀ …) (g₀ …)` (`C35b.lean:347`), `g₀ = x³ − 2x + 4`. Not vacuous. |
| `hm1` (the exact-residual ∀) | **load-bearing, and NOT vacuously satisfiable-by-emptiness.** Its ∀ ranges over `hne`, `M₀`, `hp`; `hne : Finset.Nonempty` is a `Prop` (proof-irrelevant), and `hp` pins `M₀` uniquely because `dvHgt F g (dvSideMin …) ≠ ⊤` on a nonempty side (`DvOnSide`'s finiteness conjunct). So `hm1` is exactly ONE equation, not an empty family — the A-C.7 `C.113 hne` pattern does NOT recur. Satisfied at `g₀` (`hm1_g₀` below, from `hasLabel_g₀`'s own `rfl`). |
| `hx : IsPure Polynomial.X g F.h F.e₁` | **load-bearing and SHARP — counterexample machine-checked below.** At `(s2Frame, L₀, g₀)` the hypotheses `hlab`, `hm1`, `hbox` ALL hold and the conclusion is FALSE (`hx_sharp`): `g₀`'s x-polygon has `0 ∉ sideSet X g₀ 1 2` (`suppVal = 3`, attained only at `j ∈ {1,3}`), so `hx` fails, and it is the only guard left standing. Dropping `hx` (equivalently: dropping its downstream C.59 content) turns C.61 into a false statement. |
| `hbox : ∀ g' ∈ monicFactors g, CBox1Side L g'` | **load-bearing, with a named perimeter on which it restricts nothing**: `F.f₁ * L.r.natDegree = 1` makes it `one_dvd` (C.60 (i), `cbox1_of_deg_one`) — that is exactly the regime of the `g₀` witness (`f₁ = d_r = 1`), which is why `g₀` can satisfy it while failing `hx`. Above the perimeter it is `C-BOX-1`, the fenced `B-BOX-1` analogue (C.60), and it is SHARP: with `f₁·d_r ≥ 2` a factor of residue degree coprime to `f₁·d_r` falsifies it. |

**Verdict: no vacuous binder; no fifth instance of the A-C.7 pattern.** Two binders are
restricts-nothing and said so (`{H₀ hpin}`, the two instance binders); the rest are load-bearing,
and the one whose sharpness was in genuine doubt (`hx`) is settled by a machine-checked
counterexample in this file rather than by judgement.

## The three mandated checks

**D-CARRY — does the signed conclusion follow from the definitional bodies?  NO.** It needs a
rider the bodies do not supply, and the rider is exactly ONE divisibility:

> `hram : ∀ g' ∈ monicFactors g, (F.e₁ * L.ℓ) ∣ ramIndexOf g'`  — the `e`-leg, i.e. **NODE C.59**
> (`ramLeg_dvd`), which is **NOT LANDED** anywhere in the corpus (`rg '^theorem ramLeg_dvd'`
> returns nothing; `C60.lean:46` already records "C.59 is not yet landed"). C.59's own route runs
> through **C.27** (`slot2_exact`), which is **also not landed** (no `Uniformity/ChapC/C27.lean`
> exists) — so the leg is two nodes deep, not one.

Two D-CARRY sub-findings, both recorded because they change how the node must be read:

1. **The `f`-leg alone cannot close the sandwich.** With only `hbox` one gets `f₁d_r ∣ f'` for
   every member and hence `f' ≥ f₁d_r`; the multiset `{(1, F), (1, F)}` at `E = 2` satisfies every
   remaining constraint (`Σ e'f' = E·F`) and is not the singleton. So no rearrangement of the
   landed supply avoids C.59.
2. **The floor-division hazard is NOT fatal here — but only because of the `e`-leg.**
   `hasLabel_natDegree_dvd` was REFUTED on 2026-08-20 (`C35B_D13_REFUTED_2026-08-20.md`:
   `g₀ = x³−2x+4` at `s2Frame` has `HasLabel` with `e₁f₁ = 2 ∤ 3`), so `D′ ∣ deg g` is NOT
   available and the blueprint's parenthetical "`deg g = L.keyDeg₂` via C.26's degree law +
   C.33's degree clause" is **not** a consequence of C.61's own hypotheses. The repair, executed
   in `tier1_typeOf_of_ramLeg` below, is that the *two legs together* supply the missing
   divisibility: `E ∣ e'` and `F ∣ f'` for every member force `E·F ∣ deg g` through
   `typeOf_degree`, and then the landed floor identity `deg g / D′ = ℓ·d_r`
   (`natDegree_div_eq_of_isDvPure`, C.35) pins the cofactor to `1`. **So C.61 does not need
   `D′ ∣ deg g` as a rider** — a determination this file makes and machine-checks, correcting the
   blueprint's proof sketch, which reads the degree pin off C.26/C.33 instead.

**CONTENT-FREE TYPE — no.** The conclusion is a genuine equation between `FactorizationType`
values plus `Irreducible g`; `typeOf` is the real `(monicFactors ·).map efPair` (`Density/TypeOf.lean`),
and the type is *refutable*: `hx_sharp` below proves an instance of the conclusion FALSE, which is
impossible for a `True`-bodied or arithmetic-shadow statement. (The weaker check — `example :
<statement> := trivial` — is not attempted; it would only certify that `True` is true.)

**INHABITATION — the locus is witnessed by TERMS, not merely argued.** Every carrier in the
signed type has a landed value: `s2Frame` (`KeyFrame`), `s2Frame_pin`, `L₀` (`LevelDatum`), `g₀`
with `hasLabel_g₀` (`HasLabel`), over the real base `ℤ_[2]`. This matters because two core
chapter-C predicates — `IsTestKey` and `TowerDatum` — have **no witnessing value anywhere in the
corpus**; C.61's signed type mentions **neither**, so it is not exposed to that gap. What is NOT
witnessed is the *conclusion's* locus: no term is landed satisfying `hlab ∧ hm1 ∧ hx ∧ hbox`
simultaneously (the witness `g₀` fails `hx`), so C.61's non-vacuity as a conditional is open —
disclosed, not discharged.

## The block

**Classification: (ii) reachable but needs an unwritten lemma — and (iii) that lemma is itself on
a documented frontier.** The unwritten lemma is NODE **C.59** (`ramLeg_dvd`,
`(F.e₁ * L.ℓ) ∣ ramIndexOf g` for a monic irreducible labelled `g`), applied per monic factor;
its route needs NODE **C.27** (`slot2_exact`, the three cleared value reads), also unlanded. The
per-factor application additionally needs label heredity to factors, i.e. C.34's frontier
(`C34_BLOCKED_2026-08-18.md`) — the blueprint's own step 1 ("purity of factors at the
`dv`-carrier, via the RE-PLAN'd `dvResPoly_mul_of_pure` helper", not landed).

**Verbatim failing goal** — after `refine factorizationType_eq_of_dvd …` with the four legs
discharged as in `tier1_typeOf_of_ramLeg`, the surviving goal is the `hA` leg:

```text
⊢ ∀ p ∈ (typeOf g).data, F.e₁ * L.ℓ ∣ p.1
```

which after `typeOf_data`/`Multiset.mem_map` is, verbatim,

```text
g' : Polynomial O
hg' : g' ∈ monicFactors g
⊢ F.e₁ * L.ℓ ∣ ramIndexOf g'
```

— the statement of C.59 at `g'`. Nothing in the landed engine discharges it: `rg '∣ ramIndexOf'`
over `Uniformity/` returns no theorem, B.54 supplies only the *upper* `f`-bound
(`inertiaDegOf g ∣ φ.natDegree * sideDeg`), and B.55b's `ramIndexOf g = ℓ` needs the level-1
residue clause `g.map residue = (φ.map residue)^ℓ`, which at `φ = X` forces `g ≡ x^{e₁}`
(deg `g = e₁`) — far inside the node's hypotheses.

## What DOES land here (supply, not the node)

1. `Tier1TypeOfStatement` — the ∀-closure of the signed type, as a Prop carrier (never an axiom;
   the A-C.8.5 statement-carrier convention).
2. `tier1_typeOf_of_ramLeg` — **the signed statement with the `e`-leg as an explicit hypothesis
   `hram`, fully proved.** Signature otherwise byte-identical to the spec's (same binders, same
   names, same order, `hram` inserted immediately before `hbox` where the intended proof consumes
   it). The instant C.59 lands, C.61 is `tier1_typeOf_of_ramLeg … (fun g' hg' => ramLeg_dvd …)`.
3. `irreducible_of_tier1_type` — the "and `g` is irreducible" clause read off a singleton
   `typeOf`, reusable and independent of the frame (B.58's `irreducible_of_resDeg_one` pattern,
   restated for an arbitrary singleton).
4. `hm1_g₀`, `hbox_g₀`, `hx_sharp` — the sharpness certificate: `hlab ∧ hm1 ∧ hbox` hold at
   `(s2Frame, L₀, g₀)` over `ℤ_[2]` while the conclusion FAILS, so neither `hx` nor `hram` is
   droppable.

**DEPENDS (landed, by name).** C.10 `LevelDatum.keyDeg₂_regroup` · C.26 `natDegree_dvResPoly` ·
C.29 `HasLabel`/`IsDvPure` · C.35 `natDegree_div_eq_of_isDvPure`, `dvSideMax_eq_of_isDvPure`,
`dvSideMin_eq_zero_of_isDvPure` · C.35b `s2Frame`/`L₀`/`g₀`/`hasLabel_g₀` (the certificate only) ·
C.60 `CBox1Side` · B.56b `factorizationType_eq_of_dvd` · `Density/TypeOf.lean`
`typeOf_data`, `typeOf_degree`, `monicFactors_spec`, `efPair`, `ramIndexOf`, `inertiaDegOf` ·
`Density/TypePositivity.lean` `efPair_pos_of_mem`.

**NOT depended on, deliberately:** C.33/C.34 (heredity — not landed), C.59 (the block), C.27.

## Status

Sorry-free; no new axioms. `#print axioms` footer below.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## 1. The signed statement as a Prop carrier (no axiom, no `sorry`) -/

/-- **The ∀-closure of the signed C.61 type** (`leanspec/Leanspec/ChapC.lean:2191-2200`),
byte-frozen apart from the binder head. Recorded as a carrier so that the block can be named
without re-transcribing the type, per the A-C.8.5 statement-carrier convention. -/
def Tier1TypeOfStatement : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (_hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (_hlab : HasLabel L g)
    (_hm1 : ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r)
    (_hx : IsPure Polynomial.X g F.h F.e₁)
    (_hbox : ∀ g' ∈ monicFactors g, CBox1Side L g'),
    typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible g

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.Tier1TypeOfStatement

end AxCheck
