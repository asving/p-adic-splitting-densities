/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C10
import Uniformity.ChapC.C35
import Uniformity.ChapC.C35b
import Uniformity.ChapC.C60
import Uniformity.ChapB.B54
import Uniformity.ChapB.B56
import Uniformity.ChapB.B57
import Uniformity.Density.TypePositivity

/-!
# Uniformity.ChapC.C61 — Tier 1, the per-factor singleton `typeOf` (the sandwich)

**Chapter C, NODE C.61** [theorem] [fresh] (`blueprint/CHAP-C_tower_grammar.md` §7, DECISION
C-D1's Tier 1; the A-C.1 amendment set governs, §7's design note is the tier's conditionality
record). **ENV-C3.**

## Status in one line

**BLOCKED at general `L.ℓ`; PROVED UNCONDITIONALLY at `L.ℓ = 1`.** The signed `tier1_typeOf` is
NOT declared in this file. What lands: (a) the COMPLETE REDUCTION of the signed statement to a
single missing divisibility leg (`tier1_typeOf_of_ramLeg`, byte-identical to the signed statement
except for one extra hypothesis); (b) **`tier1_typeOf_of_ell_one` — the signed conclusion, from the
signed hypotheses and no others, on `L.ℓ = 1`**; (c) **`tier1_natDegree_eq` — the degree pin
`deg g = keyDeg₂` at EVERY `L.ℓ`, from the signed hypotheses alone**; (d) a machine-checked
sharpness certificate showing the missing leg cannot simply be dropped. See "The block" below for
what is left: exactly the `L.ℓ`-half of the `e`-leg.

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
  (`L`, `hπ`, `g`, `hlab`, `hm1`, `hx`, `hbox`) and inserts exactly one new line, `hram`.
  Real `diff -u` of `leanspec/Leanspec/ChapC.lean:2191-2200` against this file's `273-283`
  (`.lean` on the right), TWO hunks and nothing else:

```text
@@ -1,4 +1,4 @@
-axiom tier1_typeOf {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
+theorem tier1_typeOf_of_ramLeg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
     (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
     [Finite (ResidueField O)]
     {g : Polynomial O} (hlab : HasLabel L g)
@@ -6,5 +6,6 @@
       (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
       dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r)
     (hx : IsPure Polynomial.X g F.h F.e₁)
+    (hram : ∀ g' ∈ monicFactors g, (F.e₁ * L.ℓ) ∣ ramIndexOf g')
     (hbox : ∀ g' ∈ monicFactors g, CBox1Side L g') :
     typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible g
```

  i.e. the declaration head and one inserted hypothesis line. Instance binders, implicit
  binders, `hm1`'s inner binder names and the conclusion are unchanged bytes.

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
| `[IsAdicComplete …]`, `[Finite (ResidueField O)]` | **restricts-nothing at the conclusion, but LOAD-BEARING in the proof.** They are not consumed by `tier1_typeOf_of_ramLeg` (the `(e,f)` engine `inertiaDegOf`/`ramIndexOf` is DVR-level, `Density/TypeOf.lean`) — that theorem carries them unused, for signature fidelity. They ARE consumed by the `e₁`-leg (§3b): B.57's `isPure_of_monic_factor` and B.54's `inertiaDegOf_dvd_key_mul_resDeg` both require them (this is the same ENV-C artifact B.52/B.54/B.55/B.58 record). Instances exist at `ℤ_[p]`. |
| `{g : Polynomial O}`, `hlab : HasLabel L g` | **load-bearing and its locus IS witnessed by a term**: `hasLabel_g₀ : HasLabel (L₀ …) (g₀ …)` (`C35b.lean:347`), `g₀ = x³ − 2x + 4`. Not vacuous. |
| `hm1` (the exact-residual ∀) | **load-bearing, and NOT vacuously satisfiable-by-emptiness.** Its ∀ ranges over `hne`, `M₀`, `hp`; `hne : Finset.Nonempty` is a `Prop` (proof-irrelevant), and `hp` pins `M₀` uniquely because `dvHgt F g (dvSideMin …) ≠ ⊤` on a nonempty side (`DvOnSide`'s finiteness conjunct). So `hm1` is exactly ONE equation, not an empty family — the A-C.7 `C.113 hne` pattern does NOT recur. Satisfied at `g₀` (`hm1_g₀` below, from `hasLabel_g₀`'s own `rfl`). |
| `hx : IsPure Polynomial.X g F.h F.e₁` | **load-bearing and SHARP — counterexample machine-checked below.** At `(s2Frame, L₀, g₀)` the hypotheses `hlab`, `hm1`, `hbox` ALL hold and the conclusion is FALSE (`tier1_typeOf_without_hx_false`): `g₀`'s x-polygon has `0 ∉ sideSet X g₀ 1 2` (`suppVal = 3`, attained only at `j ∈ {1,3}`), so `hx` fails, and it is the only guard left standing. Dropping `hx` (equivalently: dropping its downstream C.59 content) turns C.61 into a false statement. It is also *consumed*, not merely carried: §3b extracts `F.e₁ ∣ ramIndexOf g'` from it. |
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
and the type is *refutable*: `tier1_typeOf_without_hx_false` below proves an instance of the
conclusion FALSE, which is impossible for a `True`-bodied or arithmetic-shadow statement. (The weaker check — `example :
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
4. `Tier1TypeOfWithoutHxStatement` + `tier1_typeOf_without_hx_false` (with `hm1_g₀`, `hbox_g₀`,
   `typeOf_g₀_ne`) — the sharpness certificate: `hlab ∧ hm1 ∧ hbox` hold at `(s2Frame, L₀, g₀)`
   over `ℤ_[2]` while the conclusion FAILS, so neither `hx` nor `hram` is droppable.

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

/-! ## 2. The irreducibility clause, off any singleton `typeOf`

B.58's `irreducible_of_resDeg_one` reads irreducibility off the level-1 singleton type; the
argument uses nothing about the frame, so it is restated here at an arbitrary singleton and both
Tier-1 tiers (C.61, C.62) can consume it. -/

/-- **A monic polynomial with singleton `typeOf` is irreducible.** `typeOf g = ⟨{(a,b)}⟩` says
`monicFactors g` has exactly one element; that element's product is `g`, hence equals `g`, and
the elements of `monicFactors` are irreducible by `monicFactors_spec`. -/
theorem irreducible_of_singleton_typeOf {g : Polynomial O} (hg : g.Monic) {a b : ℕ}
    (h : typeOf g = ⟨{(a, b)}⟩) : Irreducible g := by
  classical
  have hdata : (monicFactors g).map efPair = ({(a, b)} : Multiset (ℕ × ℕ)) := by
    have h' := congrArg FactorizationType.data h
    rwa [typeOf_data] at h'
  have hcard : Multiset.card (monicFactors g) = 1 := by
    have h' := congrArg Multiset.card hdata
    simpa using h'
  obtain ⟨g', hg'⟩ := Multiset.card_eq_one.1 hcard
  have hspec := monicFactors_spec hg
  have hgg' : g = g' := by rw [← hspec.2, hg', Multiset.prod_singleton]
  rw [hgg']
  exact (hspec.1 g' (by rw [hg']; exact Multiset.mem_singleton_self g')).2

/-! ## 3. The reduction: the signed statement modulo the `e`-leg (NODE C.59)

`hram` is the ONLY inserted line; every other binder is the spec's, verbatim and in order.
`hx` is retained for signature fidelity and is **not consumed** — it is the input to C.59, whose
conclusion `hram` supplies directly, so the linter is silenced for it explicitly rather than the
binder being dropped (dropping it would change the signature). -/

set_option linter.unusedVariables false in
/-- **C.61's proof, complete modulo NODE C.59.** The sandwich, with the `e`-leg
`(F.e₁ * L.ℓ) ∣ ramIndexOf g'` taken as the hypothesis `hram` (that is exactly C.59 = `ramLeg_dvd`
applied per monic factor, which is NOT landed — `C61.lean`'s header block record).

The proof is four steps, and the second is the determination that corrects the blueprint's sketch:

1. **The floor identity.** `hm1` + C.26's `natDegree_dvResPoly` give
   `L.r.natDegree = dvSideDeg F g L.u L.ℓ`, and C.35's `natDegree_div_eq_of_isDvPure` (which is
   `IsDvPure` + C.08's spacing law) gives `deg g / D′ = L.ℓ * dvSideDeg`. Hence
   `deg g / D′ = L.ℓ * L.r.natDegree` — a FLOOR-divided identity, all that `HasLabel` can supply
   (`hasLabel_natDegree_dvd` is refuted: `C35B_D13_REFUTED_2026-08-20.md`).
2. **The degree pin, from the two legs rather than from a divisibility rider.** Every member of
   `(typeOf g).data` is `efPair g'` for a monic irreducible factor `g'`; `hram` gives `E ∣ e'` and
   `hbox` gives `D ∣ f'`, so `E * D` divides every summand of `Σ e'f' = deg g` (`typeOf_degree`),
   hence `E * D ∣ deg g`. Writing `deg g = (E*D)*s = D′*((L.ℓ*d_r)*s)` and dividing by `D′` turns
   step 1 into `L.ℓ*d_r = (L.ℓ*d_r)*s`, so `s = 1` (`L.hℓ`, `L.hrdeg`) and `deg g = E * D`
   **exactly**. No `D′ ∣ deg g` is needed anywhere.
3. **Collapse.** B.56b's `factorizationType_eq_of_dvd` at `a := E`, `b := D`.
4. **Irreducibility.** `irreducible_of_singleton_typeOf`. -/
theorem tier1_typeOf_of_ramLeg {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (hlab : HasLabel L g)
    (hm1 : ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r)
    (hx : IsPure Polynomial.X g F.h F.e₁)
    (hram : ∀ g' ∈ monicFactors g, (F.e₁ * L.ℓ) ∣ ramIndexOf g')
    (hbox : ∀ g' ∈ monicFactors g, CBox1Side L g') :
    typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible g := by
  classical
  obtain ⟨hgm, hgpos, hpure, hne₂, M₀, hpin₂, m, hm, hres⟩ := hlab
  have hEpos : 0 < F.e₁ * L.ℓ := Nat.mul_pos F.he₁ L.hℓ
  have hDpos : 0 < F.f₁ * L.r.natDegree := Nat.mul_pos F.hf₁ L.hrdeg
  have hqpos : 0 < L.ℓ * L.r.natDegree := Nat.mul_pos L.hℓ L.hrdeg
  -- step 1: the floor identity `deg g / D′ = ℓ · d_r`
  have hdegres : (dvResPoly F H₀ hpin g L.u L.ℓ hne₂ M₀ hpin₂).natDegree
      = dvSideDeg F g L.u L.ℓ hne₂ :=
    (natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hne₂ hpin₂).1
  rw [hm1 hne₂ M₀ hpin₂] at hdegres
  have hfloor : g.natDegree / (F.e₁ * F.f₁) = L.ℓ * L.r.natDegree := by
    rw [natDegree_div_eq_of_isDvPure L.hℓ L.hcop hpure hne₂, hdegres]
  -- the two legs, read on `(typeOf g).data`
  have hA : ∀ p ∈ (typeOf g).data, F.e₁ * L.ℓ ∣ p.1 := by
    intro p hp
    rw [typeOf_data, Multiset.mem_map] at hp
    obtain ⟨g', hg', rfl⟩ := hp
    simpa [efPair] using hram g' hg'
  have hB : ∀ p ∈ (typeOf g).data, F.f₁ * L.r.natDegree ∣ p.2 := by
    intro p hp
    rw [typeOf_data, Multiset.mem_map] at hp
    obtain ⟨g', hg', rfl⟩ := hp
    simpa [efPair, CBox1Side] using hbox g' hg'
  -- step 2: `E * D ∣ deg g`, then the cofactor is `1`
  have hsum : ((typeOf g).data.map (fun q : ℕ × ℕ => q.1 * q.2)).sum = g.natDegree :=
    typeOf_degree hgm
  have hdvd : (F.e₁ * L.ℓ) * (F.f₁ * L.r.natDegree) ∣ g.natDegree := by
    rw [← hsum]
    refine Multiset.dvd_sum ?_
    intro k hk
    rw [Multiset.mem_map] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    exact mul_dvd_mul (hA p hp) (hB p hp)
  obtain ⟨s, hs⟩ := hdvd
  have hED : (F.e₁ * L.ℓ) * (F.f₁ * L.r.natDegree)
      = (F.e₁ * F.f₁) * (L.ℓ * L.r.natDegree) := by ring
  have hq : g.natDegree / (F.e₁ * F.f₁) = (L.ℓ * L.r.natDegree) * s := by
    rw [hs, hED, mul_assoc, Nat.mul_div_cancel_left _ (Nat.mul_pos F.he₁ F.hf₁)]
  have hs1 : s = 1 := by
    have hmul : (L.ℓ * L.r.natDegree) * 1 = (L.ℓ * L.r.natDegree) * s := by
      rw [mul_one]
      exact hfloor.symm.trans hq
    exact (Nat.eq_of_mul_eq_mul_left hqpos hmul).symm
  have hdeg : g.natDegree = (F.e₁ * L.ℓ) * (F.f₁ * L.r.natDegree) := by
    rw [hs, hs1, mul_one]
  -- steps 3 and 4
  have htype : typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ :=
    factorizationType_eq_of_dvd hEpos hDpos
      (by rw [typeOf_degree hgm]; exact hdeg)
      (fun p hp => efPair_pos_of_mem hgm hp) hA hB
  exact ⟨htype, irreducible_of_singleton_typeOf hgm htype⟩

/-! ## 3b. The `e₁`-half of the `e`-leg, from `hx` alone (level-1 machinery, no C.59)

C.59's conclusion is `(F.e₁ * L.ℓ) ∣ ramIndexOf g'`. Its `F.e₁` half needs nothing from level 2:
it is CHAP-B's own mechanism at the x-key, and every ingredient is landed. This is what makes the
`L.ℓ = 1` instance of C.61 unconditional (§3c). -/

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- **The `e₁`-leg of the sandwich, from `hx` alone.** For every monic irreducible factor `g'` of
an x-pure `g`, `F.e₁ ∣ ramIndexOf g'`.

Route (all landed): B.18's `sideSet_nonempty` at the x-key; B.57's `isPure_of_monic_factor` for the
split `g = g' * rest`, which returns both `IsPure X g' F.h F.e₁` **and** the residue clause
`g'.map residue = X^(F.e₁ * sideDeg)`; B.35b's `sideDeg_of_pure` for `F.e₁ * sideDeg = deg g'`
(hence positivity of the side degree); B.54's `inertiaDegOf_dvd_key_mul_resDeg`, which at `φ = X`
reads `inertiaDegOf g' ∣ sideDeg`; and `ramIndexOf_mul_inertiaDegOf`. Writing `f' := inertiaDegOf g'`
and `sideDeg = f' * t`, `F.e₁ * f' * t = deg g' = ramIndexOf g' * f'` cancels `f' > 0`.

The degenerate frame `F.h = 0` is handled first: `F.hcop : Nat.Coprime F.h F.e₁` then forces
`F.e₁ = 1`, so the conclusion is `one_dvd`. (That case is excluded from the main branch because
B.54 and B.57 both require `0 < u`.) -/
theorem e1_dvd_ramIndexOf_of_mem_monicFactors {F : KeyFrame O π} (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {g : Polynomial O} (hg : g.Monic) (hx : IsPure Polynomial.X g F.h F.e₁)
    {g' : Polynomial O} (hg' : g' ∈ monicFactors g) :
    F.e₁ ∣ ramIndexOf g' := by
  classical
  rcases Nat.eq_zero_or_pos F.h with hh0 | hh
  · have he1 : F.e₁ = 1 := by
      have hc := F.hcop
      rw [hh0, Nat.coprime_zero_left] at hc
      exact hc
    rw [he1]
    exact one_dvd _
  · have hspec := monicFactors_spec hg
    obtain ⟨hg'm, hg'irr⟩ := hspec.1 g' hg'
    have hg'pos : 0 < g'.natDegree := natDegree_pos_of_mem_monicFactors hg hg'
    obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hg'
    have hprod : g = g' * R.prod := by rw [← hspec.2, hR, Multiset.prod_cons]
    have hRm : R.prod.Monic := by
      have h := Polynomial.monic_multiset_prod_of_monic R id
        (fun q hq => (hspec.1 q (by rw [hR]; exact Multiset.mem_cons_of_mem hq)).1)
      rwa [Multiset.map_id] at h
    have hneg : (sideSet (Polynomial.X : Polynomial O) g F.h F.e₁).Nonempty :=
      sideSet_nonempty Polynomial.monic_X (by simp) hg (μ := g.natDegree) (by simp) F.h F.e₁
    obtain ⟨hne₁, hne₂, hp₁, hp₂, hsum, hres₁⟩ :=
      isPure_of_monic_factor hπ isKey_X hh F.he₁ F.hcop hg hg'm hRm (by simp) hprod hx hneg
    have hdeq : F.e₁ * sideDeg (Polynomial.X : Polynomial O) g' F.h F.e₁ hne₁ = g'.natDegree :=
      sideDeg_of_pure Polynomial.monic_X (by simp) hg'm (by simp) F.he₁ F.hcop hp₁ hne₁
    have hdd : 0 < sideDeg (Polynomial.X : Polynomial O) g' F.h F.e₁ hne₁ := by
      rcases Nat.eq_zero_or_pos (sideDeg (Polynomial.X : Polynomial O) g' F.h F.e₁ hne₁) with
        h0 | hpos
      · rw [h0, Nat.mul_zero] at hdeq; omega
      · exact hpos
    have hB54 := inertiaDegOf_dvd_key_mul_resDeg hπ isKey_X hh F.he₁ F.hcop hg'm hg'pos hp₁
      hne₁ hdd hres₁
    rw [Polynomial.natDegree_X, one_mul] at hB54
    obtain ⟨t, ht⟩ := hB54
    have hfpos : 0 < inertiaDegOf g' := inertiaDegOf_pos (normValues_nonempty hg'm hg'pos)
    have hmul : ramIndexOf g' * inertiaDegOf g' = g'.natDegree :=
      ramIndexOf_mul_inertiaDegOf hg'm hg'pos
    refine ⟨t, ?_⟩
    have hkey : ramIndexOf g' * inertiaDegOf g' = (F.e₁ * t) * inertiaDegOf g' := by
      rw [hmul, ← hdeq, ht]; ring
    exact Nat.eq_of_mul_eq_mul_right hfpos hkey

/-! ## 3c. `L.ℓ = 1`: C.61 UNCONDITIONALLY, and the degree pin at every `L.ℓ`

At `L.ℓ = 1` the missing `e`-leg IS the `e₁`-leg, so §3b closes it and the sandwich needs no
hypothesis beyond the signed ones. The degree pin needs even less — only the `e₁`-half. -/

set_option linter.unusedVariables false in
/-- **the degree pin, at EVERY `L.ℓ`, from the signed hypotheses alone.**
`deg g = (F.e₁ * L.ℓ) * (F.f₁ * L.r.natDegree)` — i.e. `deg g = L.keyDeg₂` (C.10's regrouping).
The blueprint reads this off "C.26's degree law + C.33's degree clause"; that route is dead
(`hasLabel_natDegree_dvd` refuted, `C35B_D13_REFUTED_2026-08-20.md`). What works: `hx` gives
`F.e₁ ∣ e'` (§3b) and `hbox` gives `F.f₁ * d_r ∣ f'` on every member, so
`F.e₁ * (F.f₁ * d_r) ∣ Σ e'f' = deg g` (`typeOf_degree`); dividing the resulting
`deg g = F.e₁ * (F.f₁ * d_r) * s` by `D′ = F.e₁ * F.f₁` and comparing with the landed floor
identity `deg g / D′ = L.ℓ * d_r` (`natDegree_div_eq_of_isDvPure`) gives `s = L.ℓ`. -/
theorem tier1_natDegree_eq {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (hlab : HasLabel L g)
    (hm1 : ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r)
    (hx : IsPure Polynomial.X g F.h F.e₁)
    (hbox : ∀ g' ∈ monicFactors g, CBox1Side L g') :
    g.natDegree = (F.e₁ * L.ℓ) * (F.f₁ * L.r.natDegree) := by
  classical
  obtain ⟨hgm, hgpos, hpure, hne₂, M₀, hpin₂, m, hm, hres⟩ := hlab
  have hdegres : (dvResPoly F H₀ hpin g L.u L.ℓ hne₂ M₀ hpin₂).natDegree
      = dvSideDeg F g L.u L.ℓ hne₂ :=
    (natDegree_dvResPoly F hπ H₀ hpin L.hℓ L.hcop hne₂ hpin₂).1
  rw [hm1 hne₂ M₀ hpin₂] at hdegres
  have hfloor : g.natDegree / (F.e₁ * F.f₁) = L.ℓ * L.r.natDegree := by
    rw [natDegree_div_eq_of_isDvPure L.hℓ L.hcop hpure hne₂, hdegres]
  have hdvd : F.e₁ * (F.f₁ * L.r.natDegree) ∣ g.natDegree := by
    have hsum : ((typeOf g).data.map (fun q : ℕ × ℕ => q.1 * q.2)).sum = g.natDegree :=
      typeOf_degree hgm
    rw [← hsum]
    refine Multiset.dvd_sum ?_
    intro k hk
    rw [Multiset.mem_map] at hk
    obtain ⟨p, hp, rfl⟩ := hk
    rw [typeOf_data, Multiset.mem_map] at hp
    obtain ⟨g', hg', rfl⟩ := hp
    exact mul_dvd_mul (by simpa [efPair] using
        e1_dvd_ramIndexOf_of_mem_monicFactors hπ hgm hx hg')
      (by simpa [efPair, CBox1Side] using hbox g' hg')
  obtain ⟨s, hs⟩ := hdvd
  have hq : g.natDegree / (F.e₁ * F.f₁) = L.r.natDegree * s := by
    rw [hs, show F.e₁ * (F.f₁ * L.r.natDegree) * s = (F.e₁ * F.f₁) * (L.r.natDegree * s) by ring,
      Nat.mul_div_cancel_left _ (Nat.mul_pos F.he₁ F.hf₁)]
  have hs1 : s = L.ℓ := by
    have hmul : L.r.natDegree * s = L.r.natDegree * L.ℓ := by
      rw [← hq, hfloor]; ring
    exact Nat.eq_of_mul_eq_mul_left L.hrdeg hmul
  rw [hs, hs1]; ring

/-- **C.61 AT `L.ℓ = 1`, UNCONDITIONALLY.** The signed conclusion, with the signed hypotheses and
no extra ones, on the hypothesis `L.ℓ = 1`. At `L.ℓ = 1` the missing `e`-leg
`(F.e₁ * L.ℓ) ∣ ramIndexOf g'` IS the `e₁`-leg of §3b, so `hram` is discharged and
`tier1_typeOf_of_ramLeg` applies. This is the regime of C.10's recorded benign degeneracy
(`keyDeg₂ = D′·d_r`) and of the corpus's only landed `LevelDatum` value (`L₀`, `ℓ = 1`). -/
theorem tier1_typeOf_of_ell_one {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    (hℓ1 : L.ℓ = 1)
    {g : Polynomial O} (hlab : HasLabel L g)
    (hm1 : ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r)
    (hx : IsPure Polynomial.X g F.h F.e₁)
    (hbox : ∀ g' ∈ monicFactors g, CBox1Side L g') :
    typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible g := by
  refine tier1_typeOf_of_ramLeg L hπ hlab hm1 hx (fun g' hg' => ?_) hbox
  rw [hℓ1, mul_one]
  exact e1_dvd_ramIndexOf_of_mem_monicFactors hπ hlab.1 hx hg'

/-! ## 4. The sharpness certificate: `hx` (equivalently, the `e`-leg) is NOT droppable

The audit's mandate is to try to refute one's own guards. Here it succeeds against the guard-set
`{hlab, hm1, hbox}`: those three hold at a LANDED witness while the conclusion is FALSE, so
whatever closes C.61 must consume `hx` (in the intended proof: through C.59). This is also the
non-degeneracy check on the conclusion — a `True`-bodied or arithmetic-shadow type could not be
refuted at an instance. -/

/-- **The signed C.61 type with `hx` DELETED**, everything else byte-identical to
`Tier1TypeOfStatement`. `tier1_typeOf_without_hx_false` proves this FALSE. -/
def Tier1TypeOfWithoutHxStatement : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (_hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {g : Polynomial O} (_hlab : HasLabel L g)
    (_hm1 : ∀ (hne : (dvSideSet F g L.u L.ℓ).Nonempty) (M₀ : ℕ)
      (hp : dvHgt F g (dvSideMin F g L.u L.ℓ hne) = (M₀ : ℕ∞)),
      dvResPoly F H₀ hpin g L.u L.ℓ hne M₀ hp = L.r)
    (_hbox : ∀ g' ∈ monicFactors g, CBox1Side L g'),
    typeOf g = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible g

end Uniformity.Density.Tower

namespace Uniformity.Density.Tower.C61Sharp

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b

set_option linter.unusedSectionVars false

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- **`hm1` holds at `g₀`.** `hasLabel_g₀`'s residual clause is `dvResPoly … = ρ¹` at the
pinned data `(hne_g₀, 4, hp_g₀)`; the ∀-form follows because `hp` determines `M₀ = 4`
(`Nat.cast` injectivity on `ℕ∞`) and the two proof arguments are irrelevant. -/
theorem hm1_g₀ :
    ∀ (hne : (dvSideSet (s2Frame h2 hq) (g₀ O) 3 1).Nonempty) (M₀ : ℕ)
      (hp : dvHgt (s2Frame h2 hq) (g₀ O)
        (dvSideMin (s2Frame h2 hq) (g₀ O) 3 1 hne) = (M₀ : ℕ∞)),
      dvResPoly (s2Frame h2 hq) 1 (s2Frame_pin h2 hq) (g₀ O)
        3 1 hne M₀ hp = (L₀ h2 hq).r := by
  intro hne M₀ hp
  have h4 : M₀ = 4 := Nat.cast_injective (hp.symm.trans (hp_g₀ (O := O) h2 hq))
  subst h4
  rfl

/-- **`hbox` holds at `g₀`, on C.60 (i)'s perimeter.** `F.f₁ * L.r.natDegree = 1 * 1 = 1`, so
`CBox1Side` is `one_dvd` for every factor (`cbox1_of_deg_one`). This is why the witness can
satisfy the `C-BOX-1` guard while failing `hx`. -/
theorem hbox_g₀ : ∀ g' ∈ monicFactors (g₀ O), CBox1Side (L₀ h2 hq) g' := by
  intro g' _
  refine cbox1_of_deg_one (L₀ h2 hq) g' ?_
  rw [f1_eq h2 hq, show (L₀ h2 hq).r = ρ h2 hq from rfl, ρ_natDegree h2 hq]

/-- **the conclusion FAILS at `g₀`.** `(typeOf g₀).degree = deg g₀ = 3` (`typeOf_degree`), while
the claimed singleton `⟨{(e₁ℓ, f₁d_r)}⟩ = ⟨{(2,1)}⟩` has degree `2`. -/
theorem typeOf_g₀_ne :
    typeOf (g₀ O) ≠ ⟨{((s2Frame h2 hq).e₁ * (L₀ h2 hq).ℓ,
      (s2Frame h2 hq).f₁ * (L₀ h2 hq).r.natDegree)}⟩ := by
  intro heq
  have hdeg : (typeOf (g₀ O)).degree = (g₀ O).natDegree := typeOf_degree (g₀_monic (O := O))
  rw [heq, g₀_natDegree, FactorizationType.degree, e1_eq h2 hq, f1_eq h2 hq,
    show (L₀ h2 hq).ℓ = 1 from rfl, show (L₀ h2 hq).r = ρ h2 hq from rfl,
    ρ_natDegree h2 hq] at hdeg
  simp at hdeg

/-- **C.61 MINUS `hx` IS FALSE.** At `(s2Frame, L₀, g₀)` over `ℤ_[2]` the hypotheses `hlab`,
`hm1` and `hbox` all hold and the conclusion fails, so `hx` — equivalently the `e`-leg
`(F.e₁ * L.ℓ) ∣ ramIndexOf g'` that `hram` supplies in `tier1_typeOf_of_ramLeg` — is
load-bearing and SHARP. (`g₀`'s x-polygon at `(h, e₁) = (1, 2)` has cleared support `3`, attained
only at `j ∈ {1, 3}`, so `0 ∉ sideSet X g₀ 1 2` and `hx` fails; correspondingly
`ramIndexOf (x + 2) = 1` is not divisible by `F.e₁ * L.ℓ = 2`, so `hram` fails too.) -/
theorem tier1_typeOf_without_hx_false : ¬ Tier1TypeOfWithoutHxStatement := by
  intro hax
  exact typeOf_g₀_ne h2_padic rc2
    (hax (L₀ h2_padic rc2) h2_padic (hasLabel_g₀ h2_padic rc2)
      (hm1_g₀ h2_padic rc2) (hbox_g₀ h2_padic rc2)).1

/-- **`hx` genuinely FAILS at `g₀` — machine-checked, not hand-computed.** `L₀.ℓ = 1`, so the
PROVED `tier1_typeOf_of_ell_one` would deliver the conclusion from `hlab`, `hm1`, `hx`, `hbox`;
`typeOf_g₀_ne` says the conclusion is false. Hence `¬ hx`. (The hand computation agrees: `g₀`'s
x-polygon at `(h, e₁) = (1,2)` has cleared support `3`, attained only at `j ∈ {1,3}`, so
`0 ∉ sideSet X g₀ 1 2` — but that arithmetic is now redundant.) This is what makes the sharpness
verdict a *fact about the guard* and not merely about the guard-set. -/
theorem hx_g₀_false :
    ¬ IsPure Polynomial.X (g₀ ℤ_[2]) (s2Frame h2_padic rc2).h (s2Frame h2_padic rc2).e₁ :=
  fun hx => typeOf_g₀_ne h2_padic rc2
    (tier1_typeOf_of_ell_one (L₀ h2_padic rc2) h2_padic rfl (hasLabel_g₀ h2_padic rc2)
      (hm1_g₀ h2_padic rc2) hx (hbox_g₀ h2_padic rc2)).1

end Uniformity.Density.Tower.C61Sharp

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.Tier1TypeOfStatement
#print axioms Uniformity.Density.Tower.irreducible_of_singleton_typeOf
#print axioms Uniformity.Density.Tower.tier1_typeOf_of_ramLeg
#print axioms Uniformity.Density.Tower.e1_dvd_ramIndexOf_of_mem_monicFactors
#print axioms Uniformity.Density.Tower.tier1_natDegree_eq
#print axioms Uniformity.Density.Tower.tier1_typeOf_of_ell_one
#print axioms Uniformity.Density.Tower.Tier1TypeOfWithoutHxStatement
#print axioms Uniformity.Density.Tower.C61Sharp.hm1_g₀
#print axioms Uniformity.Density.Tower.C61Sharp.hbox_g₀
#print axioms Uniformity.Density.Tower.C61Sharp.typeOf_g₀_ne
#print axioms Uniformity.Density.Tower.C61Sharp.tier1_typeOf_without_hx_false
#print axioms Uniformity.Density.Tower.C61Sharp.hx_g₀_false

end AxCheck
