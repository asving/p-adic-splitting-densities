/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C71
import Uniformity.ChapC.C44
import Uniformity.ChapC.C11

/-!
# Uniformity.ChapC.C74 — `TouchCert`: the exact-`Θ_j` touch certificate

**Chapter C, NODE C.74 [def]** [signed: A-C.1 — `TouchCert` as the exact-`Θ_j` nonvanishing of
the key power's own read discrepancy] (`blueprint/CHAP-C_tower_grammar.md` §8, NODE C.74's
SIGNATURE block; twin `leanspec/Leanspec/ChapC.lean:3313`).  **ENV-C1**.  ONE declaration,
definitional.

## What the certificate says

Fix a frame `F` (C.01) pinned at `H₀` (C.14a's `F.Pin H₀`) and a tower datum `T` (C.42), and
write `Φ′ = F.key`, `Φ₂ = composedKey T` (C.43).  C.71 puts two different `Φ₂`-adic reads of a
polynomial side by side:

* the **composed (honest) read** `dev (composedKey T) f j` — B.02's development at `Φ₂`;
* the **stage-shadow read** `shadowDev T f j` — the same division tower run after reducing
  every coefficient mod `Φ′`, then lifted back by the canonical degree-`< D′` representative.

C.71 also names the **faithfulness threshold** `Θ_j = T.theta μ₂ j = (μ₂ − j)·E₂ + δ` (with
`δ = T.margin` the node-floor slack, `≥ 1` by `TowerDatum.one_le_margin`).  C.72 says the two
reads agree strictly below `Θ_j`, i.e. their difference has level-2 height `≥ Θ_j`; nothing so
far says the bound is *attained*.

`TouchCert T hπ μ₂ j` is exactly the statement that it is attained — and attained by the pure
power `Φ₂^{μ₂}` itself, on its own two reads:

```
dv2Hgt (T.levelDatum hπ) (shadowDev T (Φ₂^μ₂) j − dev Φ₂ (Φ₂^μ₂) j) = Θ_j
```

`dv2Hgt` is C.11's level-2 slot height, read at C.44's bridge datum `T.levelDatum hπ`; the
value lives in `ℕ∞`, so the equation is an equality of extended naturals and in particular
asserts the difference is nonzero (`dv2Hgt` of `0` is `⊤`, not a finite `Θ_j`).

## Why this shape and not `ShC_j ≠ 0` (the FR-M3 separation)

The blueprint's SIGNATURE block is explicit that the certificate is the **exact-`Θ_j`
discrepancy**, not the weaker "the shadow read is nonzero": the single-extraction sum's
non-cancellation IS the exactness, and `ShC_j ≠ 0` is NOT the certificate.  Recording the
distinction here because the two are easy to conflate at a glance and only the former is
strong enough to drive C.74's three terminal theorems.

## What this file lands, and what it does not

**LANDED: the `def` only.**  NODE C.74 is split-mandated into the definition plus three
terminal theorems — `shadow_attained_of_certificate` (the certificate forces the honest digit
to vanish and the shadow digit to sit exactly at `Θ_j`), `shadow_persistence` (the certificate
survives adding an in-budget `g`), and `shadow_not_sigma_function` (the two-witness S8.4
claim).  **None of the three is landed here, and none is axiomatized here**: they remain OPEN
in the landed corpus, carried only by the leanspec stub bank
(`leanspec/Leanspec/ChapC.lean:3319–3345`).  Consumers that need them must not read this file
as supplying them.

The def is landed on its own because it is the *statement carrier* for downstream nodes: NODE
C.128 (`lawBS2_pair_or_triple`, LAW B-S2) cannot even be stated without it, which is what the
reschedule record `leanfinal/notes/RESCHEDULE_C128_2026-08-16.md` diagnosed.

## Totality and junk

`TouchCert` is a total `Prop`-valued function of `(T, hπ, μ₂, j)`; no hypothesis (`Irreducible
π` aside, which `levelDatum` needs for its `spec` fields) rides on the term.  At `j ≥ μ₂` the
threshold degenerates to the bare margin `δ` (C.71's unfolding checks) and the certificate is
still a well-formed — if not corpus-relevant — statement.  `hπ` is a *data* argument here (it
feeds `T.levelDatum hπ`), so `TouchCert T hπ μ₂ j` for two different irreducibility proofs are
propositionally equal only via proof irrelevance, which Lean gives definitionally for `Prop`
arguments; nothing downstream depends on this.

**DEPENDS.** B.02 (`dev`) · C.01 (`KeyFrame`) · C.11 (`dv2Hgt`) · C.14a (`KeyFrame.Pin`) ·
C.42 (`TowerDatum`) · C.43 (`composedKey`) · C.44 (`TowerDatum.levelDatum`) · C.71
(`shadowDev`, `TowerDatum.theta`) — all imported, all landed.

**PROOF.** Definitional.

**SIZE.** 5 lines (the blueprint's own estimate for the definitional clause).

**SOURCE.** `EFF.GENTOW3.21` (the `[GT3-r2]` certificate, with the FR-M3 separation pin).

**TEETH.** Signed non-applicable at the definitional clause (C.74's SHARP rows ride on the
three theorems, which are not landed here).  The `example`s below are local unfolding checks.

**ENVIRONMENT.** ENV-C1.

## Status

Sorry-free, axiom-free (Lean core only).  Definitional.
-/

namespace Uniformity.Density.Tower

open Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **NODE C.74 — the TOUCH CERTIFICATE `[GT3-r2]`.**  `TouchCert T hπ μ₂ j` says that the pure
power `Φ₂^{μ₂}`'s two `j`-th reads — C.71's stage-shadow read `shadowDev T (Φ₂^μ₂) j` and the
composed (honest) read `dev Φ₂ (Φ₂^μ₂) j` — differ at level-2 height EXACTLY `Θ_j = T.theta μ₂ j`,
the faithfulness threshold of C.71.  C.72 gives the inequality `≥ Θ_j` for every member of the
locus; this is the assertion that the bound is attained, by the key power itself.

Not to be confused with `shadowDev T (Φ₂^μ₂) j ≠ 0` (the FR-M3 separation: the non-cancellation
of the single-extraction sum IS the exactness above, and mere nonvanishing is NOT the
certificate).

The three terminal theorems that consume it (`shadow_attained_of_certificate`,
`shadow_persistence`, `shadow_not_sigma_function`) are NOT landed in this file. -/
def TouchCert {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (μ₂ j : ℕ) : Prop :=
  dv2Hgt (T.levelDatum hπ)
      (shadowDev T ((composedKey T) ^ μ₂) j - dev (composedKey T) ((composedKey T) ^ μ₂) j)
    = (T.theta μ₂ j : ℕ∞)

end Uniformity.Density.Tower

/-! ## Unfolding checks

`example`s, not declarations: the local pins on the shape of the body — that it unfolds to the
`dv2Hgt`-equation verbatim (so a later edit to the body breaks a compile rather than silently
re-aiming every downstream `TouchCert` consumer), and that the threshold it is measured against
is C.71's `Θ`, in its two degenerate readings. -/

section UnfoldingChecks

open Uniformity.Density.Tower Uniformity.Density.Leaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- the body, verbatim: `TouchCert` IS the exact-`Θ_j` discrepancy equation. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (hπ : Irreducible π) (μ₂ j : ℕ) :
    TouchCert T hπ μ₂ j
      ↔ dv2Hgt (T.levelDatum hπ)
          (shadowDev T ((composedKey T) ^ μ₂) j
            - dev (composedKey T) ((composedKey T) ^ μ₂) j)
        = (T.theta μ₂ j : ℕ∞) := Iff.rfl

/-- at the top index the certificate is measured against the bare margin `δ` (C.71's
`theta μ₂ μ₂ = margin`), which `one_le_margin` keeps `≥ 1`: the certificate is never the
degenerate "height `0`" statement. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (hπ : Irreducible π) (μ₂ : ℕ) :
    TouchCert T hπ μ₂ μ₂
      ↔ dv2Hgt (T.levelDatum hπ)
          (shadowDev T ((composedKey T) ^ μ₂) μ₂
            - dev (composedKey T) ((composedKey T) ^ μ₂) μ₂)
        = (T.margin : ℕ∞) := by
  simp [TouchCert, TowerDatum.theta]

/-- at the bottom index it is measured against the full stack `μ₂·E₂ + δ`. -/
example {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀} (T : TowerDatum F H₀ hpin)
    (hπ : Irreducible π) (μ₂ : ℕ) :
    TouchCert T hπ μ₂ 0
      ↔ dv2Hgt (T.levelDatum hπ)
          (shadowDev T ((composedKey T) ^ μ₂) 0
            - dev (composedKey T) ((composedKey T) ^ μ₂) 0)
        = ((μ₂ * T.E₂ + T.margin : ℕ) : ℕ∞) := by
  simp [TouchCert, TowerDatum.theta]

end UnfoldingChecks

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.TouchCert

end AxCheck
