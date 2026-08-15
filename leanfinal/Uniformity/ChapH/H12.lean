/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H02
import Uniformity.ChapH.H07

/-!
# Uniformity.ChapH.H12 — the D2b witness: an OCCUPIED height that is NOT terminal

**Chapter H, NODE H.12** (`blueprint/CHAP-H_general_induction.md` §3). At the genre datum
`(Q, e₁, f₁, μ, h) = (2, 1, 2, 2, 1)` the `dv`-height `m = 0` **is** occupied (`i = 0`, `a = 0`,
i.e. `n(0) = 1` is integral), yet `m = 0` fails the terminal scope condition
`G.keyDeg * G.h < m` (indeed `keyDeg * h = 1 * 2 * 1 = 2 > 0`).

Hence the *occupied*-height re-display of `GENHN.A`(ii) is **strictly weaker** than the terminal
`D′h < m` scope, and the terminal scope is the one chapter H uses.

DEPENDS: H.01 (`GenreDatum`), H.02 (`GenreDatum.keyDeg`), H.07 (`GenreDatum.Occupied`).

SOURCE: `EFF.GENHN.09`, the post-D2b corrigendum transcribed verbatim: *"the re-display at step 3
is itself **too weak at `f₁ > 1`**: "sol's witness `(e₁, f₁, h, m) = (1, 2, 1, 0)`: `n(0) = 1` is
integral while the η-component would require `xπ^{−1}`". Final scope: "GENHN.A(ii)'s slot clause
holds per integer `dv`-height `m` with **`D′h < m`**, below the window cap … At `m ≤ D′h` the
clause is withdrawn entirely: a `K`-slot may be partial (the sol witness) or absent (the R4/A2
witness)."*

**⚠ WHAT THIS NODE DOES AND DOES NOT SAY** (blueprint). It does **not** formalize "the `η`-component
requires `xπ^{−1}`" — that is a statement about the stage lift's components and belongs to
H.54–H.56, where `stageLift` is only defined for `M > D′h` and therefore *cannot* be applied at
`m = 0`. What this node lands is the **separation of the two scopes**: occupied ⊉ terminal. That is
the checkable content and it is what protects every downstream consumer from re-widening the
clause. **Do not strengthen this node into a claim about partial slots.**

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Induction

/-- The post-D2b witness datum `(Q; e₁, f₁, μ; h) = (2; 1, 2, 2; 1)`. -/
def genreD2bwitness : GenreDatum where
  Q := 2
  e₁ := 1
  f₁ := 2
  μ := 2
  h := 1
  hQ := le_refl 2
  he₁ := le_refl 1
  hh := le_refl 1
  hkey := by omega
  hmul := le_refl 2
  hcop := by decide

/-- **NODE H.12(i).** The `dv`-height `m = 0` IS occupied at the D2b witness datum: take `i = 0`,
`a = 0`, i.e. the integral normalizer `n(0) = 1`. -/
theorem occupied_zero_genreD2bwitness : genreD2bwitness.Occupied 0 := by
  refine ⟨0, 0, ?_, ?_⟩ <;> simp [genreD2bwitness]

/-- **NODE H.12(ii).** Yet `m = 0` fails the TERMINAL scope condition `D′h < m`: here
`keyDeg * h = (1 * 2) * 1 = 2`, so `¬ (keyDeg * h < 0)`. Together with (i) this separates the two
scopes — occupied does not imply terminal — and chapter H uses the terminal one. -/
theorem not_keyDeg_mul_h_lt_zero_genreD2bwitness :
    ¬ (genreD2bwitness.keyDeg * genreD2bwitness.h < 0) := by
  simp [GenreDatum.keyDeg, genreD2bwitness]

end Uniformity.Density.Induction

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.genreD2bwitness
#print axioms Uniformity.Density.Induction.occupied_zero_genreD2bwitness
#print axioms Uniformity.Density.Induction.not_keyDeg_mul_h_lt_zero_genreD2bwitness

end AxCheck
