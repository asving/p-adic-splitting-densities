/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesV.V3_spwordD

/-!
# IB-G9 — `Slot_m4bConst` (bridge campaign BP1, cluster c12; E-phase statement unit)

Blueprint: `lean/notes/BRIDGE_BP1_INSTANCE_2026-07-30.md` §3.8 (row `m4bConst`) +
§4 group G (IB-G9); adjudications: `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`
(BP1 Q5: proceed NOW, statement-only, Codex audit before any consumer).

THE SLOT (U10_theoremU.lean docstring lines 82–83): `m4bConst` — CL-16, "M4b
height-translation constancy + M4b-T equivariance" (owner [1v]/[2b]).  CL-16's
ledger display (MOVES_2026-07-24.md 13327–13329): "M4b narrowed height-translation
constancy + M4b-T equivariance incl. the π_v clause (REV 10) — the count-closure
interface at fixed template, beyond the XHD portions already carried at CL-5."
M4b-T's own display (MOVES 10633ff, H.5.1): a bijection mapping realized entrance
prefixes at h_ent onto realized entrance prefixes at h_ent + v PRESERVING THE
LANDING CELL (twisted frame, π_v = id), hence I^ent_{ε,β₀}(h_ent) =
I^ent_{ε,β₀}(h_ent + v) — per listed component, one constant in h_ent.

DEPS: none (built MovesV height/translation carriers only: `CtsFamily`/`StepSys`/
`CtsMeasured`, the semilinear entrance domain `entDom`, the scoped
`writeHeights?` wrappers `instCensus`/`instRealizable`, `Order0Perimeter`).

RECORDED RESOLUTIONS (the sketch is a formulation target; each ambiguity resolved
minimally against the as-built corpus, per the E-phase charge):
* (r1) "constancy per listed component at fixed template": two height points of
  ONE listed `LinSet` component of `V.entDom εT` (the built disjoint-component
  semilinear partition) have equal census — the note's pairwise translation form
  h ↦ h + v generates exactly this same-component relation (`linset_add_period`),
  so component-constancy is its transitive closure read.
* (r2) the π_v = id clause: the SAME landing cell β₀ on BOTH sides of the
  comparison (no cell re-indexing), guarded by the built landing predicate
  `V.entLands εT β₀`.
* (r3) M4b-T's realized-prefix bijection face is carried as the two built
  transports its consumers read: the COUNT transport (`instCensus` equality —
  the count-closure interface) and the REALIZABILITY transport
  (`instRealizable` iff).  The literal prefix-set bijection needs a carrier for
  "realized entrance prefixes" the corpus does not display; recorded for the
  Codex audit as the known compression.
* (r4) THE ORDER-0-PERIMETER FENCE (blueprint §3.8: "mind the Order0Perimeter
  fence: do NOT consume the quarantined shim"): both height points carry the
  `Order0Perimeter` certificate — the ONLY token under which `writeHeights?`
  consumption is warranted (`writeHeights_total` is scoped; the unscoped shim is
  REFUTED at `WHNeg.writeHeights_total_false`, `V3_spword_negWitness2.lean`, and
  deleted).  Off the certified locus this Prop asserts NOTHING.

STATEMENT-FENCE FLAG: a NEW named Prop (wave-D discharges it by proof or carries
it visibly); per Q5 it gates nothing on the construction path and must pass the
Codex formulation audit + the IB-G11c falsifier before any consumer lands.
Non-vacuity duty: IB-G11c (`SlotsG11c_seamAudit.lean`).  Closure manifest:
IB-G12 (`SlotsG12_closureManifest.lean`).
-/

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesU

/-- IB-G9 / CL-16 (`theoremU`'s `m4bConst` parameter): M4b HEIGHT-TRANSLATION
    CONSTANCY + M4b-T EQUIVARIANCE, π_v = id — the count-closure interface at
    fixed template over the MovesV measured carrier.  For every entrance
    template εT and every LISTED component L of the semilinear entrance domain
    `V.entDom εT`: at any two `Order0Perimeter`-certified height points of L
    (the fence, resolution (r4)), at the SAME landing cell β₀ (π_v = id,
    resolution (r2)), the height-written entrance census is CONSTANT at every
    pool (M4b constancy — the count face of M4b-T's bijection) and
    realizability transports (the domain face; resolution (r3)). -/
def Slot_m4bConst (n : ℕ) {Cv : MovesV.CtsFamily n} {Sv : MovesV.StepSys n}
    (V : MovesV.CtsMeasured n Cv Sv) : Prop :=
  ∀ (εT : MovesV.EntTemplate n) (L : MovesV.LinSet εT.entDim),
    L ∈ (V.entDom εT).comps →
    ∀ h h' : MovesV.Hpt εT.entDim, L.Mem h → L.Mem h' →
      MovesV.Order0Perimeter εT h → MovesV.Order0Perimeter εT h' →
      ∀ β₀ : Sv.Cell, V.entLands εT β₀ →
        (∀ q₀ ∈ V.Pools,
          V.instCensus εT h β₀ q₀ = V.instCensus εT h' β₀ q₀) ∧
        (V.instRealizable εT h β₀ ↔ V.instRealizable εT h' β₀)

end LeanUrat.MovesU
