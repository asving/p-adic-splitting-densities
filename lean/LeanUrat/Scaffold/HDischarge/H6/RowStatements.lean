/-
HDISCHARGE_H6 §4 Wave D — `H6/RowStatements.lean`: unit D3 (EASY) — RootRows H6
bodies (BP_V §5.4 coordination — delivered as `HDischarge.H6.RowStatements`
content for BP_V's `Scaffold/RowStatements.lean` to re-export when it lands;
NO local alias of any BP_V name: `RootRows.TDec`/`TRead`/`TVerd` are BP_V's to
define, pointing here).

FOLD ROUND 1 (Codex finding 6 accepted — the first-draft ∀-over-EngineTied
bodies inherited the D-9/finding-5 error): the three faces are ∃-covering
forms sharing the core's witness SHAPE (shape probed at `TDecRow`):
`TDecRow n := ∀ (p) [Fact p.Prime] (F' : Type) [Field F'] [Finite F'], ∃ E,
EngineTied n p F' E ∧ EngineCovers n p F' E ∧ (A7's tDECdec + tDECcor faces)`;
`TReadRow n` / `TVerdRow n` likewise at the tREAD resp. tVERD + tVERDhen
faces. Face bodies are transcribed VERBATIM from unit A7's
`TerminalSeamHypsE` fields (`H6/Emission.lean`) with the witness `E` free.

## DISPLAYED SEAM NOTE (to the BP_V lead — route BEFORE `HypRows` lands)

The three faces at INDEPENDENT witnesses are JOINTLY WEAKER than
`TerminalSeamCore n p` (`H6/RowsK4.lean`, unit D1a): each face asserts its own
`∃ E`, so a `HypRows` package holding all three may hold them at a DIFFERENT
emission E per face — no single E is guaranteed to satisfy the trio together.
`rows_of_core` recovers all three from ONE core witness, but nothing recovers
the core from the three faces. If any Step-18 consumption site needs the JOINT
witness (one E satisfying tDEC + tREAD + tVERD simultaneously — e.g. anything
composing `rc_of_rows`-style ties across faces), it must consume
`TerminalSeamCore n p` directly, NOT the conjunction of the three rows —
route this check to the BP_V spine before `HypRows` lands.

## `rows_of_core` keying delta (displayed, not silent)

The blueprint schematic displays `rows_of_core : TerminalSeamCore n p →
(each face)`. The faces are n-keyed — p is quantified INSIDE each row, the
probed `TDecRow` shape above, matching BP_V's n-only `RootRows.*` keying — so
a single-p core cannot conclude them; the glue lemma consumes the p-UNIFORM
core `∀ (p) [Fact p.Prime], TerminalSeamCore n p`. Per (p, F') one core
witness projects to all three faces, which is the schematic's content.

## `FenceVIIRow n`: POSTPONED (BLOCKED-ON-CARRIER, with unit D2)

NO `FenceVIIRow` declaration lands here. Per unit D2 (`H6/Fence.lean`,
documentation-only; Codex finding 8: the six-Prop-slot device is WITHDRAWN —
caller-selected Prop slots are True-instantiable by the prover), the eventual
typed `FenceVII` must be a FIXED closed predicate of the BUILT pack/H-LIST
datum, constructible only when the value-side H-LIST/pack-builder carrier
lands (D-11/BP_IV territory). Until then BP_V's `HypRows.fenceVii` field keeps
its own bare named row per ITS charter — its call, our record.

Deps: A7 (`TerminalSeamHypsE`, `H6/Emission.lean`), B0 (`EngineTied`,
`H6/EngineConform.lean`), D1a (`EngineCovers`/`TerminalSeamCore`,
`H6/RowsK4.lean`), D2 (`H6/Fence.lean`, the FenceVII postponement record).
Unit D4 (the `RootHyps` intended-instantiation display) extends this file
separately per the §4 file plan.
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H6.RowsK4

namespace LeanUrat.Scaffold.HDischarge.H6

open LeanUrat.Scaffold.DictIII

/-- H6-D3 (shape probed at `lean/blueprints/HDISCHARGE_H6.md` §4 unit D3): the
(T-DEC) RootRows face — for every (p, F') there EXISTS an engine-tied (B0),
covering (D1a) terminal emission satisfying A7's `tDECdec` + `tDECcor` faces
(bodies verbatim from `TerminalSeamHypsE`). ∃-covering form (fold round 1,
Codex finding 6): a ∀-over-EngineTied form would be refutable (D-9/finding-5 —
`EngineTied` deliberately leaves shape fields untied and admits no-emission
interfaces). SEAM NOTE (header): at independent witnesses the three faces are
jointly weaker than `TerminalSeamCore`. -/
def TDecRow (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F' : Type) [Field F'] [Finite F'],
    ∃ E : TerminalEmission p F',
      EngineTied n p F' E ∧ EngineCovers n p F' E ∧
      (∀ f H (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
        ReadThroughIota f H D → ConsF f H D R →
        E.reaches f H →
        (DecIrrSeam H → ∃ ν EF, E.emits f H ν EF) ∧
        (DecHenSeam f H D → ∃ EF, E.emitsHen f H EF)) ∧
      (∀ f H (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
        ReadThroughIota f H D → ConsF f H D R →
        (∀ ν EF, E.emits f H ν EF → DecSeam f H D ∨ DeepCorner f H D) ∧
        (∀ EF, E.emitsHen f H EF → DecHenSeam f H D))

/-- H6-D3: the (T-READ) RootRows face — ∃-covering form at A7's `tREAD` face
(body verbatim from `TerminalSeamHypsE.tREAD`: the NONEMPTY + ∀-SIDES read).
Independent-witness caveat: see the seam note in the file header. -/
def TReadRow (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F' : Type) [Field F'] [Finite F'],
    ∃ E : TerminalEmission p F',
      EngineTied n p F' E ∧ EngineCovers n p F' E ∧
      (∀ f H ν EF (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
        ReadThroughIota f H D → ConsF f H D R →
        E.emits f H ν EF → DecSeam f H D →
        D.principalSides H.nodes.length ≠ [] ∧
        ∀ S ∈ D.principalSides H.nodes.length,
          (ν.e, ν.h, ν.ℓ, ν.s, ν.u) = (S.e, S.h, S.ℓ, S.s, S.u))

/-- H6-D3: the (T-VERD) RootRows face — ∃-covering form at A7's `tVERD` +
`tVERDhen` faces (bodies verbatim from `TerminalSeamHypsE`: the forced
terminal-datum verdict on the `emits` channel; the (1, f₀) pin on the
`emitsHen` machine-record channel). Independent-witness caveat: see the seam
note in the file header. -/
def TVerdRow (n : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F' : Type) [Field F'] [Finite F'],
    ∃ E : TerminalEmission p F',
      EngineTied n p F' E ∧ EngineCovers n p F' E ∧
      (∀ f H ν EF (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
        ReadThroughIota f H D → ConsF f H D R →
        E.emits f H ν EF → DecSeam f H D →
        EF = (terminalDatumD f H D).verdict) ∧
      (∀ f H EF (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
        ReadThroughIota f H D → ConsF f H D R →
        E.emitsHen f H EF → DecHenSeam f H D →
        EF = (1, H.psi0.natDegree))

/-- H6-D3, the glue lemma: ONE core witness projects to ALL THREE faces — the
p-uniform `TerminalSeamCore` (D1a) yields `TDecRow ∧ TReadRow ∧ TVerdRow` by
projecting the A7 row bundle fieldwise at each (p, F'). Keying delta from the
blueprint schematic is DISPLAYED in the file header (the faces are n-keyed, so
the glue consumes `∀ p [Fact p.Prime], TerminalSeamCore n p`). The converse
FAILS by design: independent face witnesses do not reassemble into the core —
joint-witness consumption sites must take `TerminalSeamCore` (seam note). -/
theorem rows_of_core {n : ℕ}
    (hcore : ∀ (p : ℕ) [Fact p.Prime], TerminalSeamCore n p) :
    TDecRow n ∧ TReadRow n ∧ TVerdRow n :=
  ⟨fun p _ F' _ _ => by
    obtain ⟨E, hTied, hCov, hRows⟩ := hcore p F'
    exact ⟨E, hTied, hCov, hRows.tDECdec, hRows.tDECcor⟩,
   fun p _ F' _ _ => by
    obtain ⟨E, hTied, hCov, hRows⟩ := hcore p F'
    exact ⟨E, hTied, hCov, hRows.tREAD⟩,
   fun p _ F' _ _ => by
    obtain ⟨E, hTied, hCov, hRows⟩ := hcore p F'
    exact ⟨E, hTied, hCov, hRows.tVERD, hRows.tVERDhen⟩⟩

end LeanUrat.Scaffold.HDischarge.H6
