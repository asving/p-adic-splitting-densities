/-
Unit R7-PROBE  (TreeCan designer round R7, countermodel-first record, 2026-07-31)
[The (†15) IB-D26 fill attempt — `canPolicy`/`canPolicy_pin` (MovesD/TreeCan.lean:485,492).
CHARGE: prove the sorried designer data per D-TM (BRIDGE_BP1_INSTANCE_2026-07-30.md §D-TM);
countermodel-first if a law smells false.  OUTCOME: **BLOCKED-FALSE-AS-QUANTIFIED** — this
module is the compiled obstruction record; the TreeCan sorries are UNTOUCHED (statement
fence) and remain the named residue.]

## The finding (compiled below, no sorry, imports MovesD.PolPin only — sorryAx-clean)

`OffsetPPin.total` + `OffsetPPin.digits_prescribed` jointly force EVERY value of the bare
`Node` type with `species = recentering` to admit a CENTER REALIZER
(`t ≠ 0 ∧ inC σ.Φ t ∧ σ.w t = σ.w σ.Φ ∧ σ.R t = C center · T 0` — this much is the landed
`OffsetPPin.lift_center_realizer`).  But `Node` places NO constraint tying the FRAME stage
`ν.σ` to the recentering species: `recProbeNode σ₀` below is a LEGAL recentering node over
an ARBITRARY stage `σ₀`.  Over a ramified frame no center realizer can exist:

  (†R7) `t ≠ 0 ∧ inC σ.Φ t` gives `σ.w t = σ.e · σ.wPrev t` (`hStretch`), while
        `σ.w t = σ.w σ.Φ = σ.h` (`hwΦ`) — so `σ.e ∣ σ.h`, and `hcop` forces `σ.e = 1`.

Hence (`offsetPPin_forces_stage_unramified`): **any inhabitant of `OffsetPPin pol`, for ANY
policy `pol`, proves every `Stage p F` unramified (`σ.e = 1`)** — a statement about the
whole Stage interface that is false in the intended semantics (the note's runs create
ramified stages at every increment read with `e ≥ 2`, e.g. the Eisenstein `X² − p` side;
`TransitionCoreL` ties the child stage's index to the read's).  Modulo constructing one
in-corpus ramified `Stage` instance (a bStage-scale build, not attempted here),
`OffsetPPin pol` is EMPTY for every `pol` (`offsetPPin_isEmpty_of_ramified` is the
conditional form), so `canPolicy_pin` is unfillable for ANY choice of `canPolicy` — no
HC-1 vocabulary export can cure it, because no formula can output a realizer where none
exists.

## Why this is a TRANSCRIPTION over-reach, not a note error

L1's totality (note 4665–4666, "No node exists where the policy is partial") quantifies
over nodes OF A RUN.  Coherent runs are fine: `LandingKey` (MovesC/Defs.lean:552) demands
the RECORDED lift of every history-coherent recentering node to be exactly such a center
realizer — so on reachable nodes existence holds (the node's own lift witnesses it), and
the frame is forced unramified THERE.  The pin's `total` widened "every node of the run"
to "every value of the `Node` type", where the frame is a free field.  The repair is a
STATEMENT-level re-scope of `OffsetPPin` (ratified file — orchestrator adjudication, not
this unit's to make); pre-scoped options for the fence event:
  (i) guard `total` (and hence the policy duty) by the frame side-condition the run
      guarantees (e.g. a center-realizer-existence antecedent, or `σ.e = 1` + weight
      reachability), keeping `digits_prescribed` as is;
  (ii) re-key `total` to nodes of `HistoryCoherent` histories (LandingKey's home), the
      exact quantifier of note 4665–4666.
Under either repair the SECOND, previously-recorded HC-1 residue stands unchanged: even at
`σ.e = 1`, the Stage interface alone cannot produce the realizer (hS6b needs the threshold
`wPrev Φ < h` — `centerRealizer_exists_of_unramified_threshold` below displays exactly
this: it is the ONLY missing existence ingredient at unramified frames for the w/R
clauses; the support/monomial clause of `support_forced` additionally needs the (S6b′)
formula, since `hS6b` controls the residual's shape, not the realizer's X-support).

moves_ref: note 4646–4651 (the ONE lift rule) + L1 note 4653–4667 (kernel (a) totality,
quantified over run nodes) + D.10/`LandingKey` (MovesC 545–557).
deps: PolPin (the pin under probe; brings MovesD.Defs, MovesC.Defs, Moves.Defs).
sketch: legal probe node over an arbitrary stage + the (†R7) parity argument.
difficulty: easy (the finding is the content).  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.MovesD.PolPin

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD

open Polynomial LeanUrat.Moves LeanUrat.MovesC

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **The probe node** — a LEGAL `Node` value of recentering species over an ARBITRARY
stage `σ₀` (nothing in `Node` ties the frame to the species): read index `(e,h) = (1,1)`
with the canonical Bézout pair `(s,t) = (1,0)`, `(g,μ) = (1,1)`, window `(s0,wSide) =
(0,1)`, flat line through `u* = 0`, `γ = 0`, `ψ = Ranch = X − C 1`, `pat = (−1, 1, 1, …)`,
`z̄ = center = 1`, junk lift `0`.  Every `Node` Prop field is discharged below; the ONLY
free datum is the frame `σ₀` itself — which is the point. -/
noncomputable def recProbeNode (σ0 : Stage p F) : Node p F where
  species := ReadSpecies.recentering
  σ := σ0
  e := 1
  h := 1
  s := 1
  t := 0
  g := 1
  μ := 1
  a := 0
  s0 := 0
  wSide := 1
  Dwidth := σ0.Φ.natDegree
  line := ⟨0, 0⟩
  ustar := 0
  gam := 0
  zbar := 1
  center := 1
  lift := 0
  ψ := Polynomial.X - Polynomial.C 1
  pat := fun k => if k = 0 then -1 else 1
  Ranch := Polynomial.X - Polynomial.C 1
  he := le_refl 1
  hh := le_refl 1
  hcop := Nat.gcd_self 1
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := le_refl 1
  hμ := le_refl 1
  hEdvd := one_dvd 1
  hDwidth := rfl
  hψmonic := monic_X_sub_C 1
  hψdeg := natDegree_X_sub_C 1
  hψirr := irreducible_X_sub_C 1
  hRanch := by
    rw [show (1 : ℕ) / 1 + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
    simp
    ring
  hpat0 := by simp
  hpatTop := by norm_num
  hAnchor := by norm_num
  hLineU := by simp [Line.at]
  hOrd := by
    refine ⟨by rw [pow_one], fun hdvd => ?_⟩
    have hne : (Polynomial.X - Polynomial.C 1 : Polynomial ↥σ0.K) ≠ 0 := X_sub_C_ne_zero 1
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [Polynomial.natDegree_pow, natDegree_X_sub_C] at hle
    omega
  hzbarRoot := by simp
  hspecInc := fun h => ReadSpecies.noConfusion h
  hspecRec := fun _ => ⟨rfl, rfl⟩
  hspecRecCenter := fun _ => ⟨rfl, by simp⟩

/-- **THE R7 OBSTRUCTION (†R7)** — a pin for ANY policy proves EVERY stage unramified:
`total` puts the policy's lift at the probe node into `Realizes`; `realizes_ne_zero` +
`digits_prescribed` make it a nonzero center realizer in `C_Φ` of weight `w Φ`; then
`hStretch`/`hwΦ` give `σ₀.e ∣ σ₀.h` and `hcop` kills every `σ₀.e ≥ 2`.  Since ramified
stages are the intended semantics of every `e ≥ 2` increment read, `OffsetPPin` as stated
is globally vacuous-by-emptiness, and the (†15) pair `canPolicy`/`canPolicy_pin`
(MovesD/TreeCan.lean) is unfillable for ANY policy choice — the designer round's
BLOCKED-FALSE record. -/
theorem offsetPPin_forces_stage_unramified {pol : CanonPolicy p F}
    (pin : OffsetPPin pol) (σ0 : Stage p F) : σ0.e = 1 := by
  set ν : Node p F := recProbeNode σ0 with hν
  have hspec : ν.species = ReadSpecies.recentering := rfl
  have hreal : pin.Realizes ν (pol.liftOf ν) := pin.total ν hspec
  have hne : pol.liftOf ν ≠ 0 := pin.realizes_ne_zero ν _ hreal
  obtain ⟨hin, hw, -⟩ := pin.digits_prescribed ν _ hreal hspec
  -- ν.σ ≡ σ0: read the center-realizer clauses at the ambient stage
  have hstr : σ0.w (pol.liftOf ν) = (σ0.e : ℤ) * σ0.wPrev (pol.liftOf ν) :=
    σ0.hStretch _ hne hin
  have hwφ : σ0.w (pol.liftOf ν) = (σ0.h : ℤ) := by
    have h2 : σ0.w (pol.liftOf ν) = σ0.w σ0.Φ := hw
    rw [h2, σ0.hwΦ]
  have hdvdZ : (σ0.e : ℤ) ∣ (σ0.h : ℤ) := ⟨σ0.wPrev (pol.liftOf ν), (hstr.symm.trans hwφ).symm⟩
  have hdvd : σ0.e ∣ σ0.h := by exact_mod_cast hdvdZ
  have hgcd : σ0.e ∣ Nat.gcd σ0.e σ0.h := Nat.dvd_gcd dvd_rfl hdvd
  rw [σ0.hcop] at hgcd
  exact Nat.dvd_one.mp hgcd

/-- The conditional-countermodel form: ONE ramified stage empties `OffsetPPin pol` for
EVERY policy.  (The unconditional countermodel = this + an in-corpus ramified `Stage`
instance — a bStage-scale construction, e.g. the `X² − p` Eisenstein read; deliberately
not attempted in this unit.) -/
theorem offsetPPin_isEmpty_of_ramified (σ0 : Stage p F) (h2 : σ0.e ≠ 1)
    (pol : CanonPolicy p F) : IsEmpty (OffsetPPin pol) :=
  ⟨fun pin => h2 (offsetPPin_forces_stage_unramified pin σ0)⟩

/-- **The repair-side evidence** (what a re-scoped pin CAN get from the Stage interface):
at an UNRAMIFIED frame whose key weight clears the (S6b) threshold (`wPrev Φ < h` — the
named reachability law a repair must carry; NOT derivable from the interface), `hS6b`
already produces a center realizer with ANY prescribed digit scalar — the w/R clauses of
`digits_prescribed` in full.  What it does NOT control is the realizer's X-support
(`support_forced`'s monomial clause): `hS6b` shapes the RESIDUAL, not the polynomial —
that piece is exactly the previously-recorded (S6b′)/HC-1 residue, unchanged by this
probe. -/
theorem centerRealizer_exists_of_unramified_threshold (σ0 : Stage p F)
    (h1 : σ0.e = 1) (hth : σ0.wPrev σ0.Φ < (σ0.h : ℤ)) (c : (↥σ0.K)ˣ) :
    ∃ t : Polynomial ℤ_[p], t ≠ 0 ∧ inC σ0.Φ t ∧ σ0.w t = σ0.w σ0.Φ ∧
      σ0.R t = LaurentPolynomial.C (c : ↥σ0.K) * LaurentPolynomial.T 0 := by
  obtain ⟨B, hB, hin, hwp, hR⟩ := σ0.hS6b (σ0.h : ℤ) c hth
  have ht0 : σ0.t = 0 := σ0.he1t h1
  refine ⟨B, hB, hin, ?_, ?_⟩
  · rw [σ0.hStretch B hB hin, hwp, σ0.hwΦ, h1]
    norm_num
  · rw [hR, ht0]
    norm_num

end

end LeanUrat.MovesD
