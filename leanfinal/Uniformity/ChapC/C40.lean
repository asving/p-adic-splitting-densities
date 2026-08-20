/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C35
import Uniformity.ChapC.C60

/-!
# Uniformity.ChapC.C40 — the level-2 peel (LEMMA HE6R1-3) — **PARTIAL: BLOCKED**

Landed by the ORCHESTRATOR (an Opus instance working the project directly, 2026-08-20),
not by a fleet agent: the API was killing subagents every ~20-30 minutes and this node was
picked up here instead.

## The signed statement (NOT declared in this file)

`leanspec/Leanspec/ChapC.lean:1687-1694` signs, as an `axiom` stub:

```lean
theorem level2_peel {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (ResidueField O)]
    {f Ψ : Polynomial O} (hΨ : IsTestKey L Ψ) (hctx : BlockContext L f)
    (hdvd : Ψ ∣ blockFactor L f) (hbox : CBox1Side L Ψ) :
    typeOf Ψ = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible Ψ ∧
    ∃ fS' : Polynomial O, blockFactor L f = Ψ * fS' ∧ ¬ Ψ ∣ fS' ∧
      fS'.natDegree = L.keyDeg₂ * (mult₂ L f - 1)
```

It is **NOT declared here**, as a `theorem` or otherwise, per the C.33/C.34/C.72 convention:
a signed statement is either proved or left to the leanspec stub. No axiom, no `sorry`.

## Why it is blocked — the exact mechanism, not a difficulty report

The conclusion is a three-way conjunction and the three conjuncts fail for **two different
reasons**, neither of which is proof-search difficulty:

**(ii) `typeOf Ψ = ⟨{(F.e₁ * L.ℓ, F.f₁ * L.r.natDegree)}⟩ ∧ Irreducible Ψ` — needs C.61,
which is UNLANDED.** The blueprint's own PROOF step 1 reads "C.61 applied to `Ψ` itself".
`rg` confirms there is no `leanfinal/Uniformity/ChapC/C61.lean` and no landed declaration of
C.61's signed name. C.40's DEPENDS line marks C.60/C.61 as a **forward dependency** ("§7
fires before this node"); §7's Tier-1 has not fired. Classification: **(ii) — reachable in
principle, but needs an unlanded supplier**, not a research frontier.

**(iii) `fS'.natDegree = L.keyDeg₂ * (mult₂ L f - 1)` — this is leanspec defect D13's site,
and D13's disposition is NOT AVAILABLE AS WRITTEN.** Quoting the leanspec
(`ChapC.lean:203-208`): `C.09`'s `LevelDatum` has no field for the multiplicity and `C.29`'s
`HasLabel` re-derives it — `C.35`'s `mult₂` is `(blockFactor …).natDegree / L.keyDeg₂` while
`HasLabel` existentially quantifies its own `m` with `dvResPoly … = L.r ^ m`, "nothing in the
chapter ties the two `m`s, and **`C.40`'s conclusion … is the node where they must agree**.
With C.35 unsignable (D2) this cannot be checked at the gate."

That is exactly the **D-CARRY** pattern the C.35 unit named earlier today
(`C35_CLAUSE3_DEFECT_2026-08-20.md`, commit `7bb36928`), and its record states the D13
disposition is not available as written: `IsDvPure` names the top abscissa by FLOOR
division, so purity constrains `⌊deg g / D′⌋` and says nothing about `deg g mod D′`.
C.40(iii) inherits that gap verbatim — `mult₂` is itself a floor division
(`natDegree / keyDeg₂`), so the equation asserts an EXACT degree where the available supply
gives only the divided identity. The C.35 record names the one-unit decidable question that
would settle it either way: **`hasLabel_natDegree_dvd`**.

**SETTLED (2026-08-20, later the same day): that question is REFUTED, so clause (iii) stays
blocked and its block is now KNOWN inseparable from C.34.** `C35b.lean` machine-checks a
counterexample at the corpus's own landed `s2Frame` (C.97, realized over ℤ_[2]):
`g₀ = x³ − 2x + 4 = x·Φ′ + 2²` is monic of degree 3 with `HasLabel L₀ g₀` at `m = 1`, while
`e₁f₁ = 2 ∤ 3`. `hasLabel_natDegree_dvd_false` negates the target at its exact binder shape.
So `mult₂` genuinely cannot be read off the label: `deg g₀ = 3 ≠ L.keyDeg₂ * m` for any `m`,
although `hasLabel_natDegree_div`'s divided identity holds at `m = 1`. Clause (iii) is
therefore NOT reachable by any C.35-local route; it needs C.34's within-slope maximality
refinement. Record: `C35B_D13_REFUTED_2026-08-20.md`.

The mechanism is worth stating because it is the deep reason: the purity is genuine (`g₀`'s
level polygon really is one-sided of slope −3); what `HasLabel` loses is PROVENANCE, since
`g₀ = (valuation-1 linear)·(θ-like quadratic)` hides a mixed factor in the odd degree that
the floor-divided top abscissa cannot see. C.29's FAITHFULNESS warning — the root-side
reading is not stated — is now executable rather than cautionary.

**THREE INDEPENDENT AUDITS CONVERGED ON THIS NODE** and it is worth recording that they
agree: (1) the C.35 unit's D-CARRY finding predicted C.40 would inherit the mismatch;
(2) the chapter-E unit found C.40's `level2_peel` to be the unlanded supplier blocking
E.51's signed `peel_row_law`; (3) the leanspec's own gate-time defect D13 names C.40 as the
node where the two multiplicities must agree. The prediction was correct.

## What IS landed here

One lemma, and it is deliberately stated **without any chapter-C dependency** so that it
cannot inherit the D13 gap: the peel-once leg of clause (i), as pure squarefree algebra.

`peel_once_of_squarefree` : in any `CommMonoidWithZero`, if `p` is `Squarefree`, `Ψ ∣ p` and
`Ψ` is not a unit, then `p = Ψ * q` for some `q` with `¬ Ψ ∣ q`. This is the honest content
of "the peel applies at most once (squarefreeness kills a second `Ψ`-factor)".

It is *supply*, not the node. Combined with C.61 it would give clauses (i) and (ii); clause
(iii) additionally needs `hasLabel_natDegree_dvd`.

## Binder-vacuity audit (A-C.8.4 checklist) — VERDICT: no vacuity instance, one disclosure

Run against the SIGNED binder list before any proving, per the mandatory protocol.

| binder | verdict |
|---|---|
| `hΨ : IsTestKey L Ψ` | **load-bearing, inhabited-in-principle.** Unfolds (C.13) to `Ψ.Monic ∧ Ψ.natDegree = L.keyDeg₂ ∧ dev F.key Ψ (L.ℓ * L.r.natDegree) = 1 ∧ …` — a genuine 5-clause slot-data constraint, not a guard that binds nothing. **DISCLOSED:** no `IsTestKey` VALUE is landed anywhere in the corpus, so its inhabitation is argued, not witnessed. Same disclosure the C.73 unit made for `TowerDatum`. |
| `hctx : BlockContext L f` | **load-bearing.** Carries `f.Monic ∧ Squarefree f ∧ ¬ F.key ∣ f` plus a nonempty `dvSideSet` with positive side degree and `L.r ∣ dvResPoly …`. Non-vacuous: the C.35 unit's audit cleared it. |
| `hdvd : Ψ ∣ blockFactor L f` | **load-bearing, and it does real work beyond its face value.** `blockFactor` is `Classical.choice`-based with junk value `1` when no labelled divisor exists; `hdvd` together with `hΨ`'s monic-of-degree-`keyDeg₂` rules the junk branch out whenever `keyDeg₂ > 0`, since `Ψ ∣ 1` would force `Ψ` to be a unit. So it is not merely a divisibility hypothesis — it is also what makes the `blockFactor` read meaningful. |
| `hbox : CBox1Side L Ψ` | **scope carrier, vacuous at `f₁·d_r = 1` BY DESIGN** and the blueprint says so ("vacuous at `f₁·d_r = 1`"). It is §7's `C-BOX-1` hypothesis carrier (C.60), i.e. this node inherits Tier-1's conditionality "and no more". Not a defect; recorded so no reader mistakes clause (ii) for unconditional. |
| `hπ`, the two instances | pin/plumbing, not guards. |

No A-C.7 pattern instance: no self-loop relation, no guard that excludes its own conclusion,
no empty ∀-domain, no hypothesis provably unsatisfiable. The one real hazard here is **not**
a vacuity of the hypotheses but the **D-CARRY conclusion-vs-body mismatch in clause (iii)**,
recorded above — a different failure mode, which is precisely why the A-C.7 registry checks
could not have caught it.

## Statement-fence note

Nothing was weakened to make anything provable. The signed statement is left OPEN at the
leanspec stub; the one landed lemma is stated at full strength and is not a trimmed version
of any signed clause.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf IsLocalRing Polynomial

/-- **The peel-once leg of NODE C.40(i), as pure squarefree algebra.**

If `p` is squarefree, `Ψ ∣ p`, and `Ψ` is not a unit, then the cofactor is `Ψ`-free:
`p = Ψ * q` with `¬ Ψ ∣ q`.  This is the honest content of the blueprint's "the peel applies
at most once (squarefreeness kills a second `Ψ`-factor)".

Stated with NO chapter-C dependency on purpose: `mult₂` and `blockFactor` are floor
divisions, and the D13 / D-CARRY gap recorded in this file's header lives exactly there, so
keeping this leg free of them keeps it free of the gap. -/
theorem peel_once_of_squarefree {M : Type*} [CommMonoidWithZero M] {p Ψ : M}
    (hsq : Squarefree p) (hdvd : Ψ ∣ p) (hnu : ¬ IsUnit Ψ) :
    ∃ q, p = Ψ * q ∧ ¬ Ψ ∣ q := by
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, hq, ?_⟩
  intro hqd
  obtain ⟨r, hr⟩ := hqd
  exact hnu (hsq Ψ ⟨r, by rw [hq, hr]; exact (mul_assoc _ _ _).symm⟩)

end Uniformity.Density.Tower

/-! ## AxCheck — footprint of every declaration landed in this file

Expect Lean core `{propext, Classical.choice, Quot.sound}` only.  No signed cite is
inherited here, and no axiom is declared.  The signed `level2_peel` is absent by design
(see the header): it is BLOCKED on C.61 (unlanded) and on D13 / `hasLabel_natDegree_dvd`. -/

#print axioms Uniformity.Density.Tower.peel_once_of_squarefree
