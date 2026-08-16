/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Data.Set.Image
import Mathlib.Tactic.Linarith

/-!
# Uniformity.ChapF.F22 — `jbShear`, `JBVtxFace`: the JB position faces at ACCEPTED 2/2

**Chapter F, NODE F.22** [interface-carrier] (`blueprint/CHAP-F_weld_layer.md` §7), ENV-F1.
J-D0's L4 leg, from `EFF.JD0.25`'s accepted-supplier table: "JB-VTX vertex-for-vertex
polygon, JB-DEV same-division — the position faces S2.1(a)/(c); row 12's `u ≥ 0` proviso
carried where B-ties are consumed (BOX-1)". The B-ties are OUT of cone (§3 rows 1, 3, 13),
so **the `u ≥ 0` proviso is NOT carried here**.

What the cone consumes is two clauses:
* **(JB-DEV)** the harness division chain and the classifier's division chain are the SAME
  division (clause (i), `EFF.GRTJB.89`) — this has **no leanfinal carrier**: "the
  classifier's division" is chapter C's descent layer, so JB-DEV enters as PROVENANCE on
  F.04/F.11, never as a predicate in this file;
* **(JB-VTX)** the shear `Σ_q(i,u) = (i, e_q·u + h_q·i)` carries the harness polygon
  vertex-for-vertex to the print polygon (clauses (a)/(b), `EFF.GRTJB.101/.102`). This IS
  carried, because it is bare integer affine geometry.

The certifier annex E-3 correction (`EFF.GRTJB.172`) is honoured structurally: clause (c)'s
run datum is the ABSCISSA RUN, and **no ambient-lattice datum appears in the carrier**.
ACCEPTED 2/2 (`EFF.GRTJB.165`); instances are site data.

**Below the contract line** (GC-6.5): `jbShear_injective`, signed at amendment A-W.1/F-D4
(it was prose-only in the committed blueprint, so the stage-0e gate had no type to land) and
proved here at the signed type. Its `e ≠ 0` hypothesis is **necessary, not defensive** — at
`e = 0` the shear collapses the u-coordinate; the negative control below is the amendment's
own witness. The corpus frames have `e = e_q ≥ 1`, so the hypothesis is free at every
intended site. Consumers are set-level: `JBVtxFace` is an image equality, and injectivity is
what transports a vertex COUNT across the shear (and recovers the harness vertex from its
print image).

Signatures byte-identical to the stage-0e gate + A-W.1/F-D4's signed helper.
-/

namespace Uniformity.Density.Weld

/-- The JB frame shear `Σ_q(i,u) = (i, e·u + h·i)` (`EFF.GRTJB.86/.101`). -/
def jbShear (e h : ℤ) : ℤ × ℤ → ℤ × ℤ := fun p => (p.1, e * p.2 + h * p.1)

/-- JB-VTX's vertex transport, abstract: the shear maps the harness vertex set onto the
print vertex set (`EFF.GRTJB.102`). ACCEPTED 2/2; instances are site data. -/
def JBVtxFace (e h : ℤ) (harnessVtx printVtx : Set (ℤ × ℤ)) : Prop :=
  jbShear e h '' harnessVtx = printVtx

/-- [A-W.1/F-D4, below the contract line] The shear is injective away from `e = 0`. Lets a
consumer transport a vertex count across `JBVtxFace`'s image equality. -/
theorem jbShear_injective {e h : ℤ} (he : e ≠ 0) :
    Function.Injective (jbShear e h) := by
  intro p q hpq
  simp only [jbShear, Prod.mk.injEq] at hpq
  obtain ⟨h1, h2⟩ := hpq
  have h3 : e * p.2 = e * q.2 := by rw [h1] at h2; linarith
  exact Prod.ext h1 (mul_left_cancel₀ he h3)

-- [A-W.1/F-D4] the negative control the amendment machine-checked: the hypothesis `e ≠ 0`
-- is necessary — at `e = 0` the u-coordinate is collapsed.
example : ¬ Function.Injective (jbShear 0 1) := by
  intro hinj
  have : ((0 : ℤ), (0 : ℤ)) = ((0 : ℤ), (1 : ℤ)) := hinj (by decide)
  exact absurd (congrArg Prod.snd this) (by decide)

end Uniformity.Density.Weld
