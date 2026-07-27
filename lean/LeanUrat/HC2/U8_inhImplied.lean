/-
Unit U8.mkStratum_inh  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `JetSetup.inh_implied` ("C.1(i) AS A SENTENCE").
deps: D7.  difficulty: easy.  hypothesis_fields: none.
**CARRIES THE §2.1 DEVIATION DISPLAY — RATIFIED (blueprint AUDIT RULING 1, 2026-07-28):**
`mkStratum i := (mkFresh i).sat` — the constructed stratum is the FRESH clause content
only, so this law holds one unfold deep (the blueprint's `Iff.rfl`; the E-phase junk-guard
`∀ hi`-form costs one instantiation step). The note's C.1(i) ("on the state cylinder, the
inherited content is implied") is thereby INSTALLED rather than re-proved; the semantic
residue — constructed `Sigma` = the classifier's per-prefix locus — is carried by the
zc/fresh laws U9/U10 (which pin Sigma's geometry to the recorded node data exactly) and
the value gates U27/U28. Falsifiability: a wrong `mkFresh` still fails U6/U9/U10.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- On the state cylinder, the stratum reduces to exactly its fresh clauses (verbatim
`JetSetup.inh_implied`'s field type at the constructed chain). -/
theorem mkStratum_inh {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) (y : Fin (n * N) → ZMod p)
    (hy : (mkSigma H n N S vOf i).IsSolution y) :
    (mkStratum H n N S vOf i y ↔ (mkFresh H n N S vOf i hi).sat y) := by
  constructor
  · intro h
    exact h hi
  · intro h hi'
    exact h

end LeanUrat.MovesJ
