/-
Kernels/HmcReduction — BP4-c2 E-phase skeletons for units KC2a, KC3, KC4
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.C + §4 KC; F9 disposition
binding; adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

THE KERNEL (MovesV/Defs.lean:1180): HMC TE D ↔ ∀ m γ h₁ h₂,
(D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂) ↔ (D.dom (.last m)).Mem h₁ ∧
(D.dom γ).Mem h₂.  NOTHING in this file asserts HMC (risk R9: HMC may be
FALSE at the real table — the note's wall channel is the designed escape;
every KC output is a reduction, a perimeter theorem, or an instance check).

FILE-SCOPE NOTE (recorded resolution): the blueprint assigns ALL KC units to
this file; the sibling-cluster units (KC1 direction census, KC2b `DomProj`
def + derivation attempt, KC5 definitional assembly, KC6 `Order0Sys`, KC7
consumer glue) are NOT here — sibling files should import this one for
`MarkCompose`.  KC2a therefore states the DomProj VIOLATION in raw form (the
named `DomProj` def is KC2b's, which is sequenced AFTER this gate).

Build: cd lean && lake build LeanUrat.Kernels.HmcReduction
-/
import Mathlib
import LeanUrat.MovesV.V4_hmc

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open LeanUrat.MovesV

/-- KC3 — `MarkCompose`, DEFINED as the BARE TYPED IMPLICATION (REV 2, F9: of
the two readings the pre-revision blueprint mixed, this is the adjudicated
definition; the structural "per-step realized marks compose" reading is
demoted to motivation — it would need unratified marks-object vocabulary plus
a marks-to-Mem translation theorem).  The ⊇/composition leg of HMC: factor
domain memberships compose to composite membership along `Hpt.append` — the
retained-state matching is carried entirely by the TYPING of the append
(V4 cast toolkit, MovesV/Defs.lean:1196-1219).  It NAMES exactly the "marks
compose" gap (composite census positivity needs a composite MARK, and marks
do not compose — the round-8 structural analysis's ⊇ failure point).
⚑ named-law ratification (Q4: a hypothesis of reduction theorems, NEVER a
new field on the frozen `XHDd`).
deps: —.  Consumers: KC4 (¬MarkCompose at the toy — the content guard),
KC5 (DomProj ∧ MarkCompose ⟹ HMC, definitional assembly), KC6 (Order0Sys
instance leg).  Binder shape mirrors `MovesV.HMC` verbatim. -/
def MarkCompose {n : ℕ} {S : StepSys n} (TE : TmplEvents n S)
    (D : XHDd n S TE) : Prop :=
  ∀ {α β : S.Cell} (m : S.Move α β) (γ : Template n S β)
    (h₁ : Hpt (S.dim m)) (h₂ : Hpt γ.D),
    (D.dom (.last m)).Mem h₁ ∧ (D.dom γ).Mem h₂ →
      (D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂)

/-- The appended point (1, …, 0) is nonzero — its first coordinate survives
`Fin.append_left`.
[SYN2-S1 SWEEP-6, 2026-07-31: DE-PRIVATIZED as the family SURVIVOR (this module is the
cluster's shared reduction base); the KC1/KC6 copies are deleted and re-pointed here.] -/
lemma append_one_zero_ne_zero {D₁ D₂ : ℕ} (hD : 0 < D₁) :
    (Hpt.append (fun _ => 1) (fun _ => 0) : Hpt (D₁ + D₂)) ≠ 0 := by
  intro h0
  have h1 : (Hpt.append (fun _ => 1) (fun _ => 0) : Hpt (D₁ + D₂))
      (Fin.castAdd D₂ ⟨0, hD⟩) = 0 := by rw [h0]; rfl
  simp only [Hpt.append, Fin.append_left] at h1
  exact one_ne_zero h1

/-- KC2a — [CM-first GATE for KC2b; runs BEFORE the KC2b prover, REV 2 F5]
the DomProj countermodel attempt.  SEALED PREDICTION (stated before the
construction runs): `dom` is FREE DATA in `XHDd` (MovesV/Defs.lean:1060),
constrained only by `no_orphan`/`no_stray` against the census, so an instance
where a composite membership holds while a factor membership fails is
expected CONSTRUCTIBLE in ~1 field — the HmcToy-genre recipe: kill ONE
one-step census fiber (an `Empty` Assign carrier at a designated height
forces `tinst = ∅` there, so `no_stray` FORBIDS that height from the
one-step domain), while keeping a composite census positive at a composite
point projecting onto the dead height (so `no_orphan` FORCES composite
membership there).  OUTCOME EITHER WAY IS A DELIVERABLE (risk R4): a witness
⟹ DomProj is a genuinely new named law (⚑, consumed as a hypothesis, never
a new XHDd field without ratification); no witness constructible from the
laws ⟹ reroute to KC2b's derivation attempt from the no_stray/exactness
family.
deps: MovesV.Defs vocabulary (gate; KC2b depends on THIS).  The sorry body
IS the countermodel construction attempt; stated in raw violation form
(negating the DomProj implication at an instance) since the named `DomProj`
def is KC2b's. -/
theorem domProj_countermodel :
    ∃ (n : ℕ) (S : StepSys n) (TE : TmplEvents n S) (D : XHDd n S TE)
      (α β : S.Cell) (m : S.Move α β) (γ : Template n S β)
      (h₁ : Hpt (S.dim m)) (h₂ : Hpt γ.D),
      (D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂) ∧
        ¬ ((D.dom (.last m)).Mem h₁ ∧ (D.dom γ).Mem h₂) := by
  -- The witness is `HmcToy` ITSELF at a deep tail (γ composite): the composite
  -- domain `nzPart 3` contains the appended point (1,0,0) (first coordinate
  -- nonzero) while the TAIL factor domain `nzPart 2` misses h₂ = 0.  Gate
  -- outcome: witness CONSTRUCTIBLE ⟹ DomProj is a genuinely new named law (⚑).
  refine ⟨1, HmcToy.S, HmcToy.TE, HmcToy.XD, HmcToy.c0, HmcToy.c0, HmcToy.mv,
    .cons HmcToy.mv (.last HmcToy.mv), (fun _ => 1), (fun _ => 0), ?_, ?_⟩
  · exact HmcToy.nzPart_mem (append_one_zero_ne_zero Nat.one_pos)
  · rintro ⟨-, h2mem⟩
    exact HmcToy.nzPart_not_mem (fun _ => rfl) h2mem

/-- KC4 — [CM-first twin, the KC5 content guard] `markCompose_fails_at_toy`:
¬MarkCompose at the census-coupled toy `HmcToy` (V4_hmc.lean).  REQUIRED —
else the toy would satisfy HMC via KC5's assembly, contradicting
`hmc_false_witness` (V4_hmc.lean:369).  SEALED PREDICTION: FAILS at
h₁ = h₂ = 0 with m = HmcToy.mv, γ = .last HmcToy.mv: both one-step domains
are `fullPart` (contain the zero height) while the composite domain is
`nzPart` (misses it) — the SAME coupled point as `hmc_false_witness`.  The
compiled witness IS the sharpened obstruction record of the HMC kernel (the
"marks do not compose" wall).  Per R5 this and KC6's Order0Sys instance are
the two content guards KC5 ships with.
deps: KC3.  Sketch: decide-adjacent — instantiate at the zero heights;
`HmcToy.fullPart_mem` twice for the antecedent; `HmcToy.nzPart_not_mem` +
`Hpt.append` of zeros (simp [Hpt.append, Fin.append, Fin.addCases]) for the
refutation. -/
theorem markCompose_fails_at_toy : ¬ MarkCompose HmcToy.TE HmcToy.XD := by
  intro hMC
  have hmem := hMC HmcToy.mv (.last HmcToy.mv) (fun _ => 0) (fun _ => 0)
    ⟨HmcToy.fullPart_mem 1 _, HmcToy.fullPart_mem 1 _⟩
  refine HmcToy.nzPart_not_mem (fun k => ?_) hmem
  simp [Hpt.append, Fin.append, Fin.addCases]

end LeanUrat.Kernels
