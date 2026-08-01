/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import LeanUrat.OM.UniformCapstone

/-!
# Scaffold/AnchorN2 — the numerics/instance anchors [wave VI-2]

E-phase transcription of `lean/blueprints/BP_VI.md` §1.4. Anchors are FLAGS,
never substitutes (tree §0 discipline). Per blueprint fix #13, unit VI-N1
imports only its actual OM source (`LeanUrat.OM.UniformCapstone`).

## BLOCKED(VI-N1): the §1.4 verbatim statement does not elaborate

The blueprint display (BP_VI.md:323–333) is, verbatim:

```
def AnchorN2 (p : ℕ) [Fact p.Prime] (σ : FactorizationType)
    (hσ : σ.degree = 2) : Prop :=
  Nonempty (montes_uniform_n2 σ hσ)

theorem anchor_n2 (p : ℕ) [Fact p.Prime] (σ : FactorizationType)
    (hσ : σ.degree = 2) : AnchorN2 p σ :=
  ⟨montes_uniform_n2 σ hσ⟩
```

Compiled against the built corpus (`lake env lean`, 2026-08-01 HEAD), it fails
with THREE errors, one of which is not curable by the sanctioned
binder-visibility convention (Spine.lean VI-S1/VI-S3 precedent):

1. `montes_uniform_n2 σ hσ` — "Application type mismatch: The argument σ has
   type FactorizationType but is expected to have type ℕ in the application
   @montes_uniform_n2 σ". Cause: `p`/`[hp : Fact p.Prime]` are EXPLICIT leading
   binders of `montes_uniform_n2` (section variable, OM/UniformCapstone.lean:295).
   This one IS the sanctioned binder-visibility class (unique well-typed
   reading `montes_uniform_n2 p σ hσ`).
2. `anchor_n2 … : AnchorN2 p σ` — "type expected, got
   (AnchorN2 p σ : σ.degree = 2 → Prop)". Also binder-visibility class
   (unique reading `AnchorN2 p σ hσ`).
3. FATAL, not binder-visibility: even after inserting `p`,
   `Nonempty (montes_uniform_n2 p σ hσ)` fails with "Application type
   mismatch: The argument montes_uniform_n2 p σ hσ has type ⟨the capstone
   conjunction⟩ of sort `Prop` but is expected to have type Sort ?u" —
   `montes_uniform_n2` is a THEOREM, so its application is a proof TERM, and
   `Nonempty : Sort u → Prop` cannot consume it. No insertion of binders
   yields a well-typed reading; the display is a category error at the
   blueprint level.

Compiled candidate repair (probe record, NOT landed — new token `type_of%`
exceeds the sanctioned convention, so it needs statement sign-off):
`Nonempty (type_of% (montes_uniform_n2 p σ hσ))` with conclusion
`AnchorN2 p σ hσ` compiles and is Lean-core
(`[propext, Classical.choice, Quot.sound]`); it takes `Nonempty` of the exact
capstone proposition (the TYPE of the proof term), preserving pole-freeness,
the common rational family, the value tie, and bracket uniqueness together,
with the prime instance explicit — the §1.4 intent. Alternative sign-off
option: drop `Nonempty` and define `AnchorN2 … : Prop :=
type_of% (montes_uniform_n2 p σ hσ)` with `anchor_n2 := montes_uniform_n2 p σ hσ`.

Unit VI-N1 is therefore NOT delivered here; no `AnchorN2`/`anchor_n2`
declaration exists below. VI-N2/VI-N3 may extend this file independently.
-/

namespace LeanUrat.Scaffold.AnchorN2

-- BLOCKED(VI-N1): see module header — the blueprint-verbatim statement does
-- not elaborate (Nonempty applied to a proof term), and the cure requires a
-- statement change beyond the sanctioned binder-visibility convention.

end LeanUrat.Scaffold.AnchorN2
