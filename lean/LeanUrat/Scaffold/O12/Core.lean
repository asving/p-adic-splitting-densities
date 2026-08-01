/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import LeanUrat.MovesU.O12PoleFree

/-!
# Scaffold/O12/Core — q, E_e, κ₀/κ₁ shared arithmetic [BP_II units II-C1..C4]

Movement II core definitions (blueprint `lean/blueprints/BP_II.md` §1.1; source of
mathematical truth: the verified leaf `lean/notes/openmath/O12_phaseB_verifybrief_rev4.md`
§2.2, §2.4).

This file carries **unit II-C1**: the transcribed definitions `qX`, `blockE`,
`kappa0`, `kappa1`. Units II-C2..C4 (the arithmetic lemmas `blockE_ge_three`,
`two_le_blockE_sub_one`, `kappa_add`, `gram_kappa0/1`) extend this module.
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU (MemRcyc Gram cycS DefinedAt AbsSolveTable detO1 detO2 detO3)

/-- The ambient field of symbolic rational functions in q (brief §2.2). -/
abbrev Qq := RatFunc ℚ

noncomputable def qX : Qq := algebraMap (Polynomial ℚ) Qq Polynomial.X

/-- `E_e = e(e+1)/2 = 1 + 2 + ⋯ + e` (brief §2.2). -/
def blockE (e : ℕ) : ℕ := e * (e + 1) / 2

/-- κ₀ = q^{−E} (the in-place loop mass, symbolic; brief §2.4). -/
noncomputable def kappa0 (e : ℕ) : Qq := (qX ^ blockE e)⁻¹

/-- κ₁ = (q−1)·q^{−E} (the recentering mass, symbolic). -/
noncomputable def kappa1 (e : ℕ) : Qq := (qX - 1) * (qX ^ blockE e)⁻¹

end LeanUrat.Scaffold
