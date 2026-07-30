/-
Kernels/KC6 — BP4-c5 E-phase skeletons for unit KC6: the `Order0Sys`
predicate + `hmc_of_order0` (HMC on the provable order-0 perimeter) + the two
instance checks (BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.C "the provable
perimeter" + §4 KC6; pre-approved split KC6a (predicate + instances) /
KC6b (the theorem); adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md
BP4 block).

THE PERIMETER (blueprint §3.C, quoted): HMC on ORDER-0/SELF-LOOP-FREE
templates — "steps whose domains are full products of per-coordinate
threshold conditions — there Mem is componentwise and the factorization is
`Iff.rfl`-adjacent" — the same perimeter as the capstone's order-0 slice and
the wave-A2 spword/instbij scopings.  NOTHING here asserts HMC at the real
table (risk R9): `hmc_of_order0` is a perimeter theorem conditional on the
named `Order0Sys` predicate.

RECORDED RESOLUTION (predicate design — the unit's flagged hard part): the
blueprint's "full products of per-coordinate threshold conditions" is typed
as PER-MOVE THRESHOLD VECTORS θ (one `Hpt (S.dim m)` per move, `Hpt (S.dimT
mT)` per terminal move) with the template membership predicate `ThrMem`
defined recursively — one-step: pointwise θ ≤ h (the Pi order on `Hpt`);
cons: head condition on `Hpt.take h` ∧ recursion on `Hpt.drop h`.
`Order0Sys TE D` then says SOME such threshold assignment presents EVERY
template domain: (D.dom γ).Mem h ↔ ThrMem θ θT γ h.  This is the minimal
carrier-free reading: the data is existential inside the Prop (Q4: a
hypothesis/carrier shape, never a new field on the frozen `XHDd`), and the
cons-compatibility that makes HMC `Iff.rfl`-adjacent is BUILT INTO ThrMem's
recursion rather than asserted separately.  ⚑ interface — flagged for
orchestrator ratification with the unit.

deps: MovesV.V4_hmc (HmcToy) + MovesV.V1_witnessB (the V1 witness,
transitive import).  KC3-KC5 optional (not imported: no statement here
mentions DomProj/MarkCompose).  difficulty: hard-fable, ~80 ln.

Build: cd lean && lake build LeanUrat.Kernels.KC6
-/
import LeanUrat.MovesV.V4_hmc

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open LeanUrat.MovesV

/-- KC6a (carrier def, no sorry) — `ThrMem θ θT γ h`: the FULL-PRODUCT
per-coordinate threshold membership of the height point `h` in the template
`γ`, from per-move threshold vectors `θ`/`θT`.  One-step templates read the
pointwise Pi-order condition θ ≤ h; a cons reads its head condition on
`Hpt.take h` and recurses on `Hpt.drop h` — so the composite condition IS
the product of the step conditions by construction (the order-0 mechanism
that makes HMC `Iff.rfl`-adjacent). -/
def ThrMem {n : ℕ} {S : StepSys n}
    (θ : ∀ (α β : S.Cell) (m : S.Move α β), Hpt (S.dim m))
    (θT : ∀ (α : S.Cell) (v : VLabel n) (mT : S.MoveT α v), Hpt (S.dimT mT)) :
    ∀ {α : S.Cell}, (γ : Template n S α) → Hpt γ.D → Prop
  | _, .last m,  h => θ _ _ m ≤ h
  | _, .lastT m, h => θT _ _ m ≤ h
  | _, .cons m γ, h => θ _ _ m ≤ Hpt.take h ∧ ThrMem θ θT γ (Hpt.drop h)

/-- KC6a (the named predicate, ⚑) — `Order0Sys TE D`: the domain face is an
ORDER-0 (self-loop-free genre) system — some per-move threshold assignment
presents every template domain as the full product of its per-coordinate
step conditions.  The blueprint's provable perimeter for HMC (same perimeter
as the capstone's order-0 slice). -/
def Order0Sys {n : ℕ} {S : StepSys n} (TE : TmplEvents n S)
    (D : XHDd n S TE) : Prop :=
  ∃ (θ : ∀ (α β : S.Cell) (m : S.Move α β), Hpt (S.dim m))
    (θT : ∀ (α : S.Cell) (v : VLabel n) (mT : S.MoveT α v), Hpt (S.dimT mT)),
    ∀ (α : S.Cell) (γ : Template n S α) (h : Hpt γ.D),
      (D.dom γ).Mem h ↔ ThrMem θ θT γ h

/-- KC6b — `hmc_of_order0`: full-product step domains ⟹ HMC (the provable
perimeter theorem).  Sketch: rewrite both sides of HMC's iff through the
Order0Sys presentation; on the composite side ThrMem (.cons m γ)
(Hpt.append h₁ h₂) unfolds to the head condition at `Hpt.take (Hpt.append
h₁ h₂)` ∧ the tail condition at `Hpt.drop (Hpt.append h₁ h₂)`; the
take/append and drop/append identities (Fin.castAdd/natAdd against
Fin.append — elementary `Fin.addCases` computations, stated as private
helper lemmas if absent from the corpus) collapse these to the conditions
at h₁ and h₂, i.e. to ThrMem (.last m) h₁ ∧ ThrMem γ h₂ — `Iff.rfl`-
adjacent, exactly as the blueprint promises. -/
theorem hmc_of_order0 {n : ℕ} {S : StepSys n} (TE : TmplEvents n S)
    (D : XHDd n S TE) (h0 : Order0Sys TE D) : HMC TE D := by
  sorry

/-- KC6a instance check 1 — the V1 witness satisfies `Order0Sys`: every
witness-system template has dimension 0 (`witS_tmpl_dim_zero`) and domain
`zeroPart γ.D`, so the empty threshold assignment (all `Fin 0 → ℕ` vacuous)
presents every domain — both sides of the iff are unconditionally true.
Sketch: refine ⟨fun _ _ _ => (fun i => i.elim0), …⟩-genre vectors (the dims
are 0 only up to `witS_tmpl_dim_zero`, so use `fun _ => 0` and prove the
iff by induction on γ with both sides True). -/
theorem wit_order0Sys : Order0Sys witTE witD := by
  sorry

/-- KC6a instance check 2 — `HmcToy` does NOT satisfy `Order0Sys` (the
blueprint's "¬Order0Sys — the toy's coupled census violates the predicate"):
the toy's composite domain at the depth-2 template is `nzPart 2` = {h ≠ 0},
which is NOT a threshold box: (1,0) and (0,1) are members, so any presenting
threshold θ would satisfy θ ≤ (1,0) and θ ≤ (0,1), forcing θ = 0 and hence
(0,0) ∈ box — but (0,0) ∉ nzPart 2 (`nzPart_not_mem`).  Together with
instance check 1 this is KC5's non-vacuity guard pair (R5). -/
theorem hmcToy_not_order0Sys : ¬ Order0Sys HmcToy.TE HmcToy.XD := by
  sorry

/-- KC6 rider — re-derive the V1 witness's HMC (`witHMC`,
V1_witnessB.lean:144) THROUGH the perimeter theorem: the content guard that
`hmc_of_order0` + `wit_order0Sys` compose (the pair is not False-everywhere,
R5).  Expected discharge: `hmc_of_order0 witTE witD wit_order0Sys`. -/
theorem wit_hmc_via_order0 : HMC witTE witD := by
  sorry

end LeanUrat.Kernels
