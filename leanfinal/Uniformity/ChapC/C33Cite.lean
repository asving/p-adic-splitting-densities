/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C33

/-!
# Uniformity.ChapC.C33Cite — the dv-level FGMN/GN15 cite pair (gate-(b), A-C.8)

**The FIFTH and SIXTH landed literature-cite axioms**, closing NODE C.33's two blocked
frontiers (amendment A-C.8, `blueprint/CHAP-C_tower_grammar.md`).

**OWNER SIGNATURE.** Asvin, 2026-08-18 (recorded in the amendment's §A-C.8.6 block), given
after the cite-vs-Hensel-primitive alternative was weighed; the Hensel-engine upgrade path
(the booked dv-graded engine retiring both cites) is recorded there.  The amendment's
certify-BEFORE-declare gate is SATISFIED: all three certification legs are green —
* Leg A+B: `C33_CITE_CERT.lean.txt` (zero sorry, compiles at the pin; the hand-built
  two-slope `DvDissection` over the `s2Frame` with UNIVERSAL `hsides`; the hostile
  retargets `legB_lowdeg`/`legB_swap`; the goal-closure tests `legB_goal1`/`legB_goal2`
  showing the two Props close the exact blocked goals, the second only through the landed
  reduction; all six `#print axioms` Lean-core);
* Leg C: `verification/ac8_dv_cite_check.py` (independent exact-integer implementation,
  26-row sweep + fixed tooth + both fences, green 2026-08-18).

## Faithfulness entry I — `exists_dvDissection`

* **Publications.** [GN15] J. Guàrdia, E. Nart, *Genetics of polynomials over local
  fields*, Contemp. Math. **637** (2015) 207–241, **Theorem 2.3** (A-3 verified across the
  referee round), co-primary with [FGMN] J. Fernández, J. Guàrdia, J. Montes, E. Nart,
  *Residual ideals of MacLane valuations*, J. Algebra **427** (2015) 30–75, **Thm 6.6 in
  arXiv v3** (⚠ the published Elsevier number is predicted 6.5 and has NOT been
  print-read — the pending owner check recorded at A-C.8.2; the statement TEXT is verified
  against the in-repo arXiv-v3 layout print).  Same co-primary pairing and reason as the
  landed B.42 (`exists_slope_factorization` = the `r = 0` instance of the same theorem
  pair; this axiom is the `r = 1` instance).
* **Statement.** Byte-for-byte NODE C.33's A-C.1 signed existence statement — the grouped-
  by-slope theorem of the polygon at the level carrier, in the landed `DvDissection`
  vocabulary.  The source-to-carrier map (grouping by slope, `g₀ = below`, `hkey` removing
  the explicit key power, the `λ > 0` fence as the cleared floor inequality) is the
  amendment's §A-C.8.2 table; the `KeyFrame`↔MacLane-chain/shear identification is the
  corpus-side dictionary and the disclosed principal faithfulness risk.
* **Vacuity audit** (A-C.8.4, against the five-instance A-C.7 registry): no instance; the
  certification's two-slope witness makes the conclusion inhabited non-vacuously and the
  low-degree purity collapse dies at the degree law (machine-checked).

## Faithfulness entry II — `fgmn_dvDissection_factor_eq`

* **Publication.** [FGMN], **Theorem 2.8** (number A-3-stable across versions): principal
  Newton polygons are additive, `N⁻(gh) = N⁻(g) + N⁻(h)`; the source itself prints why the
  entire-polygon analogue is false, and this clause stays on the principal/above-floor
  portion encoded by the `DvDissection` fields.
* **Transcription level (disclosed).** A deliberately narrow CONSUMER-NORMAL-FORM
  corollary, not a verbatim transcription: for two dissections of the same `f`, additivity
  plus the fields' purity/degree/floor data pin each indexed factor (the amendment's
  five-step derivation); monic cancellation is Lean-side, not literature.  Exposes no
  polygon addition, no residual law, no off-slope values.
* On this axiom, `dvDissection_unique` becomes a THEOREM below — the trusted names
  correspond one-to-one to the two blocked frontiers.

## Scope notes

C.34's residual-primary refinement is NOT covered (its record `C34_BLOCKED_2026-08-18.md`
confirms this pair is scope-fenced away from it).  The strict-sweep allowlist grows to
`{exists_slope_factorization, fgmn_residual_mul, agnprw_termination, bBox1_cite,
exists_dvDissection, fgmn_dvDissection_factor_eq}` + Lean core.
-/

namespace Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **NODE C.33 existence `[cite:GN15 Thm 2.3 + FGMN arXiv-v3 Thm 6.6]` (gate (b),
A-C.8).**  The slope dissection at the dv-level; statement byte-identical to the A-C.1
signed stub.  Full faithfulness entry in the module docstring. -/
axiom exists_dvDissection (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f) :
    Nonempty (DvDissection F f)

/-- **NODE C.33 separation `[cite:FGMN Thm 2.8]` (gate (b), A-C.8).**  The cross-slope
purity-separation frontier for two already-constructed dissections, in consumer normal
form.  Full faithfulness entry (including the disclosed transcription level) in the
module docstring. -/
axiom fgmn_dvDissection_factor_eq {F : KeyFrame O π} {f : Polynomial O}
    (D D' : DvDissection F f) :
    ∀ p ∈ D.slopes, D.factor p = D'.factor p

/-- **NODE C.33 uniqueness — now a THEOREM** (the A-C.8 design: the cite supplies exactly
the factor frontier; the slope-set and below equalities are the landed Lean-core
reductions).  Statement byte-identical to the A-C.1 signed stub. -/
theorem dvDissection_unique (F : KeyFrame O π) (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hkey : ¬ F.key ∣ f)
    (D D' : DvDissection F f) :
    D.slopes = D'.slopes ∧ D.below = D'.below ∧
      ∀ p ∈ D.slopes, D.factor p = D'.factor p :=
  dvDissection_unique_of_factor_eq D D' (fgmn_dvDissection_factor_eq D D')

end Uniformity.Density.Tower

/-! ## Axiom footprint (the axioms print themselves; the theorem inherits exactly them) -/

section AxCheck
#print axioms Uniformity.Density.Tower.exists_dvDissection
#print axioms Uniformity.Density.Tower.fgmn_dvDissection_factor_eq
#print axioms Uniformity.Density.Tower.dvDissection_unique
end AxCheck
