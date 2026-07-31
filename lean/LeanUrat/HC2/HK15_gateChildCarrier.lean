/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.HC2.HK13_bStageCoreP1a
import LeanUrat.HC2.HK14_bStageCoreP2
import LeanUrat.HC2.HK56_bStageCoreP1b
import LeanUrat.HC2.HK47
import LeanUrat.HC1.DefsChild
import LeanUrat.HC1.S9r_childR
import LeanUrat.HC1.S9_transStage

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

QUEUE ITEM 16 EXECUTED (2026-07-31, Asvin sign-off on the consolidated queue — the
adjudicated preferred option "add hiaug named hypothesis"):
* THE REPAIR: the whole family gains `hiaug : IAug bStageP U31.fq e' h'` — the (I-aug)
  steepness guard whose absence made the family SUSPECT-FALSE as stated (the compiled
  evidence: `HK15_iaugProbe.lean` — the tuple (1,1,1,0) satisfies every OLD hypothesis
  yet violates (I-aug) at the proven `bStageP.w fq = 2`; M1 note appended there).
  `gateChildResData` (whose OLD row was hypothesis-FREE — not even Bézout data — and
  hence uninhabitable-in-general) gains the SAME full row: the uniform family re-type.
* THE DISCHARGES (all six sorries): via the forged-transHyp machinery exactly as the
  item bills — `gateTransHyp` generalizes HK-47's `transHyp_gate` / FORGE-A's
  `transHyp_ramified` (read-shaped fields reused verbatim; the four side-keyed fields
  are the new hypothesis row), then `HC1.S9r_childR` inhabits the ChildResData carrier
  and `HC1.S9_transStage` forges σ₁ with the transition record; Φ/K/e/h pins are the
  record's own fields; the card-4 check is `nextField = ⊤` (F₂(r₀) = F₄) + the
  GaloisField card. GATE PAIR (1,3,1,0): satisfies IAug (3 > 1·2) — every member of
  the family is DISCHARGED there (and at every steep pair, given the row).
* PAIR-PIN PER-LEG ADJUDICATION (/goal authority — "whichever option makes the proof
  work"; the ledger's two options applied PER LEG): the e/h legs hold at EVERY steep
  pair (the transition record pins them). The s/t legs CANNOT hold ∀-(s',t') at e' ≥ 2
  even with hiaug: S9's child carries the BUILDER's Bézout pair while (s',t') ranges
  over ≥ 2 legal pairs (they differ by (s+h'k, t−e'k); `Exists.choose` is
  proof-irrelevant in (s',t'), so one σ₁ would have to realize distinct s') — the
  hiaug repair alone does NOT cure those two conjuncts. The ledger's OTHER option
  ("specialize to the gate pair") is therefore applied to exactly those legs: they are
  GUARDED by `e' = 1` (the gate pair's e'; there the pair is FORCED on both sides —
  σ₁.t = 0 = t' by `he1t`, then σ₁.s = 1 = s' by `hbez`). HK-18's consumption is at
  (1,3,1,0), inside the guard. An UNGUARDED ∀-(s',t') pair pin would need an S9
  variant exposing the Bézout pair (the builder's literal already takes any legal
  (s',t') internally — a verbatim-builder-at-pinned-pair unit, HC1-owned; flagged for
  the synthesis duty, NOT executed here).
* STAGECORE REPLICA NOTE: `StageCoreL bStageP` is consumed through file-private
  replicas of FORGE-A's `R7Forge.bStageP_stageCore(L)` assemblies (same HK-13/HK-56/
  HK-14 pieces, slotted identically) rather than importing `MovesD/R7_ramifiedForge` —
  that leaf is under active edit by the queue's item-13 agent; keeping HK-15's import
  cone HC2/HC1-local decouples the builds. Dedup target for the item-8 sweep.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
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

/-! ### The file-private FORGE-A replicas + the parameterized gate TransHyp
(queue item 16, 2026-07-31 — see the module header's replica note). -/

/-- [file-private replica — provenance: `MovesD/R7_ramifiedForge.lean`
`R7Forge.bStageP_stageCore` (FORGE-A, 2026-07-31); same HK-13/HK-56/HK-14 pieces,
slotted identically.] -/
private theorem bStageP_stageCore' : StageCore bStageP where
  wPrev_mul := bStageP_wPrev_mul
  wPrev_ult := bStageP_wPrev_ult
  reps_nonempty := bStageP_reps_nonempty
  p_is_rep := bStageP_p_is_rep
  w_strict := bStageP_w_strict
  w_jump := bStageP_w_jump
  R_neg := bStageP_R_neg
  tvec := bStageP_tvecLaw
  prevIaug := bStageP_prevIaug
  slot := bStageP_slotDecomp
  coeff := bStageP_coeffFieldLawCore

/-- [file-private replica — provenance: `MovesD/R7_ramifiedForge.lean`
`R7Forge.bStageP_stageCoreL`.] -/
private theorem bStageP_stageCoreL' : StageCoreL bStageP where
  core := bStageP_stageCore'
  tvec_unit := bStageP_tvecUnitLaw
  coeff_loc := bStageP_coeffLocLaw

/-- HK-15 (queue item 16): **the parameterized gate transition hypothesis** — HK-47's
`transHyp_gate` with the four side-keyed fields ABSTRACTED into the family's hypothesis
row (the FORGE-A `transHyp_ramified` idiom, made a function of the pair): same
(ψ₂, g = 2, Φ̂ = fq) read shape, verbatim-reused fields; zbar := `gateRoot` (= the
recorded `U31.ν₀.zbar`, definitionally — both are `Units.mk0 U31.r₀ _`). -/
theorem gateTransHyp (e' h' : ℕ) (he' : 1 ≤ e') (hh' : 1 ≤ h')
    (hcop : Nat.gcd e' h' = 1) (hiaug : IAug bStageP U31.fq e' h') :
    HC1.TransHyp bStageP U31.ψ₂ 2 U31.fq e' h' gateRoot :=
  { hmonic := HK47.transHyp_gate.hmonic
    hirr := HK47.transHyp_gate.hirr
    hne_z := HK47.transHyp_gate.hne_z
    hdeg := HK47.transHyp_gate.hdeg
    hg := HK47.transHyp_gate.hg
    hlift := HK47.transHyp_gate.hlift
    he' := he'
    hh' := hh'
    hcop := hcop
    hiaug := hiaug
    hroot := HK47.transHyp_gate.hroot }

/-- HK-15 (queue item 16): **the forged child-stage existence** at any (I-aug)-steep
pair — `S9_transStage` fired on the gate read (`hEG : 1 < bStageP.e · 2 = 2`, the same
guard discharge as FORGE-A/HK-16): a child stage carrying the full transition record,
the round-5 stage core, and the K/e/h pins. -/
theorem gateChildStage_exists (e' h' : ℕ) (he' : 1 ≤ e') (hh' : 1 ≤ h')
    (hcop : Nat.gcd e' h' = 1) (hiaug : IAug bStageP U31.fq e' h') :
    ∃ σ' : Stage 2 F4,
      TransitionCoreL bStageP σ' U31.fq e' h' gateRoot ∧ StageCoreL σ' ∧
      σ'.K = bStageP.nextField gateRoot ∧ σ'.e = e' ∧ σ'.h = h' :=
  HC1.S9_transStage bStageP bStageP_stageCoreL' (gateTransHyp e' h' he' hh' hcop hiaug)
    (by rw [bStageP_e_def]; norm_num)

/-! ### The card-4 residue field: `K₂⟮r₀⟯ = F4` (the G1 carrier arithmetic). -/

/-- The ambient gate field has exactly 4 elements (`GaloisField.card`). -/
private lemma F4_card' : Nat.card F4 = 4 := by
  have h := GaloisField.card 2 2 (by norm_num)
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
  exact h

/-- The child field of the gate read is EVERYTHING: `K₂⟮r₀⟯ = F₂(r₀) = F₄` — the four
elements `{0, 1, r₀, 1 + r₀}` are distinct (char 2 + `r₀² + r₀ + 1 = 0`) and all lie in
the closure, and F4 has only four elements. -/
private lemma nextField_gateRoot_top : bStageP.nextField gateRoot = ⊤ := by
  classical
  haveI : Fintype F4 := Fintype.ofFinite _
  -- char-2 arithmetic
  have h2 : (2 : F4) = 0 := by exact_mod_cast CharP.cast_eq_zero F4 2
  have h11 : (1 : F4) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  have hprop : U31.r₀ ^ 2 + U31.r₀ + 1 = 0 := gateRoot_spec
  have hr0 : U31.r₀ ≠ 0 := gateRoot_ne_zero
  have hr1 : U31.r₀ ≠ 1 := by
    intro h
    rw [h] at hprop
    have h1 : (1 : F4) = 0 := by linear_combination hprop - h11
    exact one_ne_zero h1
  have h1r0 : (1 : F4) + U31.r₀ ≠ 0 := by
    intro h
    have h1 : U31.r₀ = 1 := by linear_combination h - h11
    exact hr1 h1
  have h1r1 : (1 : F4) + U31.r₀ ≠ 1 := by
    intro h
    have h1 : U31.r₀ = 0 := by linear_combination h
    exact hr0 h1
  have h1rr : (1 : F4) + U31.r₀ ≠ U31.r₀ := by
    intro h
    have h1 : (1 : F4) = 0 := by linear_combination h
    exact one_ne_zero h1
  -- the four distinct elements exhaust F4
  have hcard4 : ({0, 1, U31.r₀, 1 + U31.r₀} : Finset F4).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨zero_ne_one, fun h => hr0 h.symm, fun h => h1r0 h.symm⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨fun h => hr1 h.symm, fun h => h1r1 h.symm⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          exact fun h => h1rr h.symm),
        Finset.card_singleton]
  have huniv : ({0, 1, U31.r₀, 1 + U31.r₀} : Finset F4) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard4, ← Nat.card_eq_fintype_card, F4_card'])
  -- everything is in the closure
  have hrmem : U31.r₀ ∈ bStageP.nextField gateRoot :=
    Subfield.subset_closure (Or.inr rfl)
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ ({0, 1, U31.r₀, 1 + U31.r₀} : Finset F4) := by
    rw [huniv]
    exact Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact zero_mem _
  · exact one_mem _
  · exact hrmem
  · exact add_mem (one_mem _) hrmem

/-! ### The family, hiaug-repaired and discharged (queue item 16). -/

/-- HK-15: **the gate ChildResData instantiation** — HC1's S9 constructor-data carrier
(the D.7(vi)-normalized child residual with the S5′ pinned shape and the D.3(b) key pin)
at `(σ, Φ̂, z̄) := (bStageP, fq, gateRoot)`, for the next-read pair `(e', h', s', t')`
(HK-18's data).  Inhabitation route: S9r/S9w at the concrete stage (`bR`-evaluation at
the root — `digPrime`; the `mfun ≡ 0` normalization is `hS5'`'s content, realized on
HC1's built child by `V8_childResidual.v8Rc_S5'`).
QUEUE ITEM 16 (2026-07-31): gains the FULL hypothesis row incl. `hiaug` (the uniform
family re-type — the OLD bare row was uninhabitable-in-general, header record);
DISCHARGED by `S9r_childR` at `gateTransHyp`.
[Blueprint BP2 HK-15; deps: HK-13, HC1/DefsChild, HC1/S9r_childR.] -/
noncomputable def gateChildResData (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0)
    (hiaug : IAug bStageP U31.fq e' h') :
    HC1.ChildResData bStageP U31.fq e' h' gateRoot s' t' :=
  (HC1.S9r_childR bStageP bStageP_stageCoreL' (gateTransHyp e' h' he' hh' hcop hiaug)
    s' t' hbez he1t).some

/-- HK-15: **the gate child carrier σ₁** — the child stage of the root read, DEFINED from
HC1's S9 constructor data (the S9a/S9b/S9c stage-literal recipe through `S9_transStage`)
at the key `Φ̂ = fq` over the child field `K₂⟮r₀⟯`, keyed at the next-read pair
`(e', h', s', t')` (HK-18's data; the NEW-keying child pair).
QUEUE ITEM 16 (2026-07-31): gains `hiaug` (the adjudicated repair; the probe's (1,1,1,0)
tuple now fails the row) and is DISCHARGED as the chosen S9 child.
[Blueprint BP2 HK-15; deps: HK-13; consumers: HK-16 (Stage laws via S9), HK-17 (the (NEW)
transition record), HK-18 (ν₁), HK-24 (G1's card-4 carrier).] -/
noncomputable def gateChildStage (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0)
    (hiaug : IAug bStageP U31.fq e' h') :
    Stage 2 F4 :=
  (gateChildStage_exists e' h' he' hh' hcop hiaug).choose

/-- HK-15 (key pin): σ₁'s key is U31's recorded landing key `fq` — the blueprint's
"Φ̂ := U31's landing key" clause.  [Blueprint BP2 HK-15; queue item 16: `hiaug` row +
discharged via the transition record's `child_key`.] -/
theorem gateChildStage_Phi (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0)
    (hiaug : IAug bStageP U31.fq e' h') :
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).Φ = U31.fq :=
  (gateChildStage_exists e' h' he' hh' hcop hiaug).choose_spec.1.base.child_key

/-- HK-15 (pair pins): σ₁ is keyed at the given next-read pair — `(e, h) = (e', h')`
(the NEW-keying `child_e`/`child_h`), and at UNRAMIFIED reads (`e' = 1` — the gate
pair's leg) also `(s, t) = (s', t')` (the Bézout-tie shape, FORCED there on both sides
by `he1t` + `hbez`).
[Blueprint BP2 HK-15; queue item 16: `hiaug` row + the PER-LEG adjudication of the
s/t legs — see the module header (an unguarded ∀-(s',t') s/t pin is FALSE at e' ≥ 2
for any choice-based σ₁: Bézout non-uniqueness); HK-18 consumes at (1,3,1,0), inside
the guard.] -/
theorem gateChildStage_pair (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0)
    (hiaug : IAug bStageP U31.fq e' h') :
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).e = e' ∧
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).h = h' ∧
    (e' = 1 →
      (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).s = s' ∧
      (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).t = t') := by
  obtain ⟨-, -, -, he, hh⟩ := (gateChildStage_exists e' h' he' hh' hcop hiaug).choose_spec
  refine ⟨he, hh, fun h1 => ?_⟩
  -- at e' = 1 the Bézout pair is FORCED on both sides
  have hσe : (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).e = 1 := he.trans h1
  have hσt : (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).t = 0 :=
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).he1t hσe
  have ht'0 : t' = 0 := he1t h1
  have hσs : (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).s = 1 := by
    have hb := (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).hbez
    rw [hσe, hσt] at hb
    push_cast at hb
    linarith
  have hs'1 : s' = 1 := by
    rw [h1, ht'0] at hbez
    push_cast at hbez
    linarith
  exact ⟨by rw [hσs, hs'1], by rw [hσt, ht'0]⟩

/-- HK-15 (K pin): σ₁'s current field is the child field of the root read — `K₂⟮r₀⟯ =
bStageP.nextField gateRoot` (D.6/D.7(v)).  [Blueprint BP2 HK-15; queue item 16: `hiaug`
row + discharged via the transition record's `child_field`.] -/
theorem gateChildStage_K (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0)
    (hiaug : IAug bStageP U31.fq e' h') :
    (gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).K
      = bStageP.nextField gateRoot :=
  (gateChildStage_exists e' h' he' hh' hcop hiaug).choose_spec.2.2.1

/-- HK-15 (THE G1 carrier check): `Nat.card ↥σ₁.K = 4` — the card-4 residue field
(K₂⟮r₀⟯ = all of F4, the genuine degree-g = 2 extension; MovesT/G1's `twoNodeKcardH`
consumes this through HK-24's hand-off).  [Blueprint BP2 HK-15; queue item 16: `hiaug`
row + discharged via the K pin, `nextField_gateRoot_top`, and `GaloisField.card`.] -/
theorem gateChildStage_K_card (e' h' : ℕ) (s' t' : ℤ)
    (he' : 1 ≤ e') (hh' : 1 ≤ h') (hcop : Nat.gcd e' h' = 1)
    (hbez : (e' : ℤ) * s' + (h' : ℤ) * t' = 1) (he1t : e' = 1 → t' = 0)
    (hiaug : IAug bStageP U31.fq e' h') :
    Nat.card ↥((gateChildStage e' h' s' t' he' hh' hcop hbez he1t hiaug).K) = 4 := by
  rw [gateChildStage_K e' h' s' t' he' hh' hcop hbez he1t hiaug, nextField_gateRoot_top]
  rw [Nat.card_congr Subfield.topEquiv.toEquiv]
  exact F4_card'

/-- HK-15 (queue item 16, THE GATE-PAIR INSTANCE): the family discharged at the pair
(e', h', s', t') = (1, 3, 1, 0) — the pair HK-18 consumes; IAug there is the concrete
steepness `3 > 1·2` (the HK-47 `bw fq = 2` value). All four pair legs close (the s/t
guard fires at `e' = 1`). -/
theorem gateChildStage_gate_pins :
    (gateChildStage 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
        (fun _ => rfl) HK47.transHyp_gate.hiaug).Φ = U31.fq ∧
    (gateChildStage 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
        (fun _ => rfl) HK47.transHyp_gate.hiaug).e = 1 ∧
    (gateChildStage 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
        (fun _ => rfl) HK47.transHyp_gate.hiaug).h = 3 ∧
    (gateChildStage 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
        (fun _ => rfl) HK47.transHyp_gate.hiaug).s = 1 ∧
    (gateChildStage 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
        (fun _ => rfl) HK47.transHyp_gate.hiaug).t = 0 ∧
    Nat.card ↥((gateChildStage 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num)
        (by norm_num) (fun _ => rfl) HK47.transHyp_gate.hiaug).K) = 4 := by
  obtain ⟨he, hh, hst⟩ := gateChildStage_pair 1 3 1 0 (le_refl 1) (by norm_num)
    (by norm_num) (by norm_num) (fun _ => rfl) HK47.transHyp_gate.hiaug
  obtain ⟨hs, ht⟩ := hst rfl
  exact ⟨gateChildStage_Phi 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
      (fun _ => rfl) HK47.transHyp_gate.hiaug, he, hh, hs, ht,
    gateChildStage_K_card 1 3 1 0 (le_refl 1) (by norm_num) (by norm_num) (by norm_num)
      (fun _ => rfl) HK47.transHyp_gate.hiaug⟩

end LeanUrat.MovesJ

-- Axiom audit (queue item 16): the discharged family's footprint.
#print axioms LeanUrat.MovesJ.gateTransHyp
#print axioms LeanUrat.MovesJ.gateChildStage_pair
#print axioms LeanUrat.MovesJ.gateChildStage_K_card
#print axioms LeanUrat.MovesJ.gateChildStage_gate_pins
