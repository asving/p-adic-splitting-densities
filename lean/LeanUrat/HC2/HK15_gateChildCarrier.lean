/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC2.HK13_bStageCoreP1a
import LeanUrat.HC1.DefsChild

/-!
# HC2.HK15_gateChildCarrier — HK-15: the gate child carrier σ₁

Bridge campaign BP2 (`lean/notes/BRIDGE_BP2_HC2K1_2026-07-30.md`, Block G, unit HK-15).
E-PHASE SKELETON: definitions + statements with `sorry` bodies/placeholders; P-phase
proves (routine-opus, est. ~60 lines).

**Unit HK-15** — blueprint statement: "The gate child carrier: Φ̂ := U31's landing key
(the recorded lift of ψ₂ = z²+z+1 at the (1,1) read, g = 2); instantiate HC1's S9
constructor data (ChildResData at bStage/ψ₂) to DEFINE σ₁ : Stage 2 F4 with `σ₁.K` card 4
(the `Nat.card ↥σ₁.K = 4` check — G1's carrier)."

TRANSCRIPTION RESOLUTIONS (recorded per the E-phase charge):
* Φ̂ := `U31.fq` — U31's recorded landing key: `U31.landingKey_ν₀ : LandingKey ν₀ fq`
  exhibits `fq = X² + 2X + 4` as the recorded lift of `ψ₂ = z² + z + 1` at the (1,1)
  root read, `g = 2`.
* CARRIER: `bStageP` (HK-13's base-pin re-dress) replaces the literal `U31.bStage`,
  per the finding recorded in `HK13_bStageCoreP1a.lean`'s module header (`StageCoreL`
  at the literal `bStage` is refutable; `w`/`R` are unchanged, so the landing-key data
  transport verbatim).
* z̄ := `gateRoot`, the canonical residue root `U31.r₀` (a root of ψ₂ in F4) as a unit
  of F4; `U31.r₀_prop`/`r₀_ne` are `private` in U31 — restated here with `sorry`
  (statements byte-faithful to the private originals).
* PARAMETERIZATION: the blueprint leaves σ₁'s stage pair to HK-18 ("HK-18 chooses ν₁'s
  data to satisfy hiaug" — HK-47(b)); since HK-18 `deps: HK-15`, σ₁ is declared here as
  a FUNCTION of the next-read pair `(e', h')` + Bézout data `(s', t')` + their Stage
  lawfulness (the exact `Stage` field laws), and HK-18 instantiates it at its chosen
  values.  Under the NEW keying (§3.1(c)) the child stage is keyed at the pair of the
  read AT the child node, so these are ν₁'s `(e, h, s, t)`.
* The `Nat.card ↥σ₁.K = 4` check is stated via the K-pin `σ₁.K = bStageP.nextField
  gateRoot` (= `K₂⟮r₀⟯`, all of F4).

deps: HK-13 (carrier); consumed by HK-16/HK-17/HK-18/HK-47 (and HK-24's `twoNodeKcardH`
hand-off — G1's card-4 carrier).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves

/-- HK-15 (supply): the canonical residue root is nonzero — restatement of U31's `private`
`r₀_ne` (byte-faithful; needed to clothe `r₀` as a unit).  [Blueprint BP2 HK-15.] -/
theorem gateRoot_ne_zero : U31.r₀ ≠ 0 := U31.ν₀.zbar.ne_zero

/-- HK-15: **the gate residue root z̄₀** — U31's canonical residue root `r₀` (the canonical
root of ψ₂ = z² + z + 1 in F4) as a unit of F4.  This is the `zbar₀` of HK-47's TransHyp
assembly.  [Blueprint BP2 HK-15; deps: HK-13 (file), U31's `r₀`.] -/
noncomputable def gateRoot : F4ˣ := Units.mk0 U31.r₀ gateRoot_ne_zero

/-- HK-15 (definitional pin): the unit's value is `r₀`. -/
theorem gateRoot_val : ((gateRoot : F4ˣ) : F4) = U31.r₀ := rfl

/-- HK-15 (supply): `gateRoot` is a root of ψ₂'s defining equation in F4 — restatement of
U31's `private` `r₀_prop` (byte-faithful).  [Blueprint BP2 HK-15.] -/
theorem gateRoot_spec :
    ((gateRoot : F4ˣ) : F4) ^ 2 + ((gateRoot : F4ˣ) : F4) + 1 = 0 := by
  rw [gateRoot_val]
  have h : Polynomial.eval₂ U31.K2.subtype U31.r₀ U31.ψ₂ = 0 := U31.ν₀.hzbarRoot
  simpa [U31.ψ₂, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_one] using h

/-- HK-15: **the gate ChildResData instantiation** — HC1's S9 constructor-data carrier
(the D.7(vi)-normalized child residual with the S5′ pinned shape and the D.3(b) key pin)
at `(σ, Φ̂, z̄) := (bStageP, fq, gateRoot)`, for the next-read pair `(e', h', s', t')`
(HK-18's data).  Inhabitation route: S9r/S9w at the concrete stage (`bR`-evaluation at
the root — `digPrime`; the `mfun ≡ 0` normalization is `hS5'`'s content, realized on
HC1's built child by `V8_childResidual.v8Rc_S5'`).
[Blueprint BP2 HK-15; deps: HK-13, HC1/DefsChild.] -/
noncomputable def gateChildResData (e' h' : ℕ) (s' t' : ℤ) :
    HC1.ChildResData bStageP U31.fq e' h' gateRoot s' t' := by
  sorry

/-- HK-15: **the gate child carrier σ₁** — the child stage of the root read, DEFINED from
HC1's S9 constructor data (`gateChildResData` + the S9a/S9b/S9c stage-literal recipe) at
the key `Φ̂ = fq` over the child field `K₂⟮r₀⟯`, keyed at the next-read pair
`(e', h', s', t')` (HK-18's data; the NEW-keying child pair).  The lawfulness arguments
are exactly `Stage`'s own field laws for the pair, so the pins below are unconditional.
[Blueprint BP2 HK-15; deps: HK-13; consumers: HK-16 (Stage laws via S9), HK-17 (the (NEW)
transition record), HK-18 (ν₁), HK-24 (G1's card-4 carrier).] -/
noncomputable def gateChildStage (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0) :
    Stage 2 F4 := by
  sorry

/-- HK-15 (key pin): σ₁'s key is U31's recorded landing key `fq` — the blueprint's
"Φ̂ := U31's landing key" clause.  [Blueprint BP2 HK-15.] -/
theorem gateChildStage_Phi (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0) :
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t).Φ = U31.fq := by
  sorry

/-- HK-15 (pair pins): σ₁ is keyed at the given next-read pair — `(e, h, s, t) =
(e', h', s', t')` (the NEW-keying `child_e`/`child_h` + Bézout-tie shape).
[Blueprint BP2 HK-15.] -/
theorem gateChildStage_pair (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0) :
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t).e = e' ∧
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t).h = h' ∧
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t).s = s' ∧
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t).t = t' := by
  sorry

/-- HK-15 (K pin): σ₁'s current field is the child field of the root read — `K₂⟮r₀⟯ =
bStageP.nextField gateRoot` (D.6/D.7(v)).  [Blueprint BP2 HK-15.] -/
theorem gateChildStage_K (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0) :
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t).K
      = bStageP.nextField gateRoot := by
  sorry

/-- HK-15 (THE G1 carrier check): `Nat.card ↥σ₁.K = 4` — the card-4 residue field
(K₂⟮r₀⟯ = all of F4, the genuine degree-g = 2 extension; MovesT/G1's `twoNodeKcardH`
consumes this through HK-24's hand-off).  [Blueprint BP2 HK-15.] -/
theorem gateChildStage_K_card (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0) :
    Nat.card ↥((gateChildStage e' h' s' t' he' hh' hcop hbez he1t).K) = 4 := by
  sorry

end LeanUrat.MovesJ
