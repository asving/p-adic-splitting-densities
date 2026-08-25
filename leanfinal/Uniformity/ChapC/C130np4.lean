/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C80
import Uniformity.ChapC.C10

/-!
# Uniformity.ChapC.C130np4 — the S2 inherited threshold, identified and evaluated (S2-source node NP-4)

**S2-source plan node NP-4** (`docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6 row NP-4):
"Identify the inherited S2 thresholds and prove integer/natural equality. **Stop as BLOCKED if
no source occurrence supplies them; do not choose a convenient numeral.**"

## The search (read before trusting the numeral below)

`CanonicalThresholdAt` (freeze-v2 layer C.130d, carrier-level cure landed as chain-carrier node
CC-7, `C130th.lean`) pins `EFF.T2.04`'s "inherited threshold `T ∈ ℤ`" and `EFF.T2.11`'s
`(WINDOW)` `T < d(Φ_i(ρ)) < ∞` as CARRIED data (`NodePointSource.thresholdZ`/`thresholdNat`),
because unit `C130A` (`runs/wave-b/verdict_C130A.md`) found **no function of `(DeepTower,i,F₀)`**
that determines `T`, and CC-7's own docstring quotes the ruling verbatim: "Neither row gives a
formula for `T`" at that level of generality. This node does not contest that ruling — it
answers the *different* question the plan's row NP-4 and §5 table actually ask: is there a
source occurrence that pins `T` for the campaign's own **concrete S2 instance**?

**Level 1 (the base carrier, `i = 1`): still no formula.** `s2DepthTwo`'s stage-1 data IS
`s2Frame h2 hq`'s own `(e₁,f₁,h) = (2,1,1)` (`C130s2.s2DepthTwo_stage1`, `C97.s2Frame_data`) —
level 1 is the base `KeyFrame`, not built from any `LevelDatum` composition, so there is no
"previous level" datum from which a level-1 threshold could be derived. `EFF.T2.04` stays a
`[hypothesis]` (verbatim: "the carrier has ... an inherited threshold `T ∈ 𝐙`") with no formula
anywhere in `spec/EFF-T2.md`, `spec/EFF-GENTOW5*.md`, or `spec/EFF-GENHN*.md`. **This confirms
CC-7/C130A independently, at the concrete S2 instance; it is not a new blocker.**

**Level 2 (the terminal stage of the depth-two S2 tower, `i = 2`): a genuine source formula.**
`EFF.HE6R1.18` (`spec/EFF-HE6R1.md`, verbatim: `"T₂ = ℓd_rλ = 1·2·λ = 2λ"`, an instrument-record
arithmetic audit) fixes the **level-2 disk threshold** — the object HE7's own text names as the
legality boundary "`dv₂(Ψ(ξ)) > T₂` iff `ξ` is a level-2 point" (`lean/notes/openmath/
he7rat_brief_2026-08-09.txt:571-572`) — and this is the SAME schema as `EFF.T2.11`'s `(WINDOW)`
`T < d(Φ(ρ)) < ∞`: `docs/in-progress/LEAN_SCOPING_consumption_map_2026-08-12.md` lists "HE7+HE6R1
(level 2)" as one of the five *span-pinned instances* of exactly that window clause. Already-
landed Lean transcribes the dictionary faithfully: `LevelDatum.seam` (`C09.lean`, SOURCE
`EFF.HE6R1.18`) defines `L.seam := L.r.natDegree * L.u`, docstring "`T₂ = ℓ·d_r·λ`, cleared to
the integer `d_r·u`"; `TowerDatum.levelDatum` (`C44.lean`) is the bridge from a `TowerDatum`
(hence from `s2Tower`, C.80) to this `LevelDatum`; `LevelDatum.seam_mul` (`C10.lean`) proves the
cleared identity `ℓ·seam = (ℓ·d_r)·u` (the `EFF.HE6R1.18` frame-audit arithmetic, as a Lean
theorem). **None of this is new mathematics — every ingredient is already landed**; what is new
here is the concrete evaluation at the campaign's own S2 tower and the identification claim.

## The concrete S2 evaluation

`s2Tower h2 hq : TowerDatum (s2Frame h2 hq) 1 (s2Frame_pin h2 hq)` (C.80) carries
`(e₂,f₂,u₂,ψ₂) = (2,1,5, X-1)`. Through `TowerDatum.levelDatum`, `d_r := (towerLabel
(s2Tower h2 hq)).natDegree = f₂ = 1` (`towerLabel_spec`, exactly `C80.keyDeg₂_s2Tower`'s own
`hr` step, reused verbatim below) and `u = u₂ = 5`, `ℓ = e₂ = 2`. Hence

* `seam = d_r · u = 1 · 5 = 5` — the level-2 disk threshold `T₂`, in the ORIGINAL (rational-
  cleared) normalization `EFF.HE6R1.18` states it in (`T₂ = ℓd_rλ` at `λ = u/ℓ`, the `ℓ`'s
  cancelling exactly as blueprint `C.09`'s parenthetical says);
* `ℓ · seam = 2 · 5 = 10` — the SAME quantity read in chapter C's internal `ℓ`-cleared height
  convention (`dvSupp`/`dv2Hgt`, C.05/C.06/C.11), the convention `dvSupp_testKey`
  (`C131aa.lean`) uses for a test key's own height at exactly this threshold.

This instance is not an invented worked example: `s2DepthTwo`'s stage-2 numerals are literally
`(e₁,f₁,h) = (2,1,1)`, `D″ = 4`, `T₂ = 2λ`, `μ₂ = 2` — the exact frame blueprint `C.09`'s TEETH
section names as `EFF.HE6R1.18`'s audited regression instance (`blueprint/
CHAP-C_tower_grammar.md:855`, `:951`). `λ = u₂/ℓ = 5/2` there, giving `T₂ = 2λ = 5`, matching
`seam` below by direct computation, independent of the `d_r·u` route.

## What this node does NOT claim

Which of `5` or `10` is the value a future, ambient-split-corrected `NodePointSource.thresholdZ
2` for S2 should carry is a NORMALIZATION-CONVENTION question for whichever node builds
`pointHgt` concretely (`NP-0`, blocked on `SF-2`/`NV-6`, per the plan) — this node does not
decide it, and does NOT construct, name, or attempt to inhabit any `NodePointSource` instance
(none exists yet at S2: `no_s2_node_source`/`no_s2_source_frontier`, unit U13). Both numerals are
proved here, honestly labelled by which normalization they belong to; no numeral is chosen to
make a later inequality convenient. `NP-5`'s window inequalities are NOT attempted here: they
need `S.pointHgt`/`S.point_exists` (`NP-0`) and the slot-value dictionary (`NP-2`), neither of
which is landed.

**DEPENDS.** C.80 (`s2Tower`, `s2Tower_data`, `towerLabel_spec` import) · C.44
(`TowerDatum.levelDatum`) · C.09 (`LevelDatum.seam`) — all transitively imported through C.80.

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no `NodePointSource`
instance attempted or claimed.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C130np4

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower Uniformity.Density.Tower.C35b
open Uniformity.Density.Tower.C80

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## The residual-factor degree at the S2 level-2 datum (reused from `C80.keyDeg₂_s2Tower`) -/

include h2 hq in
/-- `d_r = 1` at the S2 level-2 datum: the residual factor `towerLabel (s2Tower h2 hq)` has
degree `f₂ = 1`. Same fact `C80.keyDeg₂_s2Tower` extracts on its way to `keyDeg₂ = 4`. -/
theorem levelDatum_natDegree_s2Tower :
    ((s2Tower h2 hq).levelDatum h2).r.natDegree = 1 :=
  (towerLabel_spec (s2Tower h2 hq) h2).2.2.1

/-! ## The seam `T₂ = d_r · u`, `EFF.HE6R1.18`'s dictionary (`LevelDatum.seam`, C.09) -/

include h2 hq in
/-- ★ **the S2 level-2 disk threshold, in the source's own (rational-cleared) normalization**:
`seam = d_r · u = 1 · 5 = 5`. This is `EFF.HE6R1.18`'s `T₂ = ℓd_rλ` at `λ = u/ℓ`, transcribed
verbatim as `LevelDatum.seam` (`C09.lean`) and evaluated at the landed `s2Tower` (`C80.lean`). -/
theorem seam_s2Tower : ((s2Tower h2 hq).levelDatum h2).seam = 5 := by
  rw [LevelDatum.seam, levelDatum_natDegree_s2Tower h2 hq,
    show ((s2Tower h2 hq).levelDatum h2).u = 5 from rfl]

include h2 hq in
/-- The `ℤ`-cast spelling of the same value (the integer/natural dictionary the plan's row
NP-4 asks for): `(seam : ℤ) = 5`. -/
theorem seam_s2Tower_intCast : (((s2Tower h2 hq).levelDatum h2).seam : ℤ) = 5 := by
  rw [seam_s2Tower h2 hq]; norm_num

include h2 hq in
/-- The nonnegativity half of the dictionary (trivial at this concrete value, but stated in
the same shape as `C130th.NodePointSource.thresholdZ_nonneg`'s obligation): `0 ≤ (seam : ℤ)`. -/
theorem seam_s2Tower_nonneg : (0 : ℤ) ≤ (((s2Tower h2 hq).levelDatum h2).seam : ℤ) := by
  rw [seam_s2Tower_intCast h2 hq]; norm_num

include h2 hq in
/-- The `ℕ`-avatar is literally the numeral `5` (the unique natural casting to `seam_s2Tower_
intCast`'s value, in the shape of `C130th.NodePointSource.thresholdNat_unique`). -/
theorem seam_s2Tower_natAvatar {m : ℕ} (hm : (m : ℤ) = (((s2Tower h2 hq).levelDatum h2).seam : ℤ)) :
    m = 5 := by
  rw [seam_s2Tower_intCast h2 hq] at hm
  exact_mod_cast hm

/-! ## The `ℓ`-cleared companion, chapter C's internal height convention -/

include h2 hq in
/-- ★ **the SAME level-2 disk threshold, read in chapter C's internal `ℓ`-cleared height
convention** (`dvSupp`/`dv2Hgt`, and `dvSupp_testKey`'s own RHS `(ℓ·d_r)·u`):
`ℓ · seam = 2 · 5 = 10`. Recorded so that whichever convention a future `pointHgt` uses, the
correct numeral is already on record and not invented at that later node. -/
theorem ell_mul_seam_s2Tower :
    ((s2Tower h2 hq).levelDatum h2).ℓ * ((s2Tower h2 hq).levelDatum h2).seam = 10 := by
  rw [seam_s2Tower h2 hq, show ((s2Tower h2 hq).levelDatum h2).ℓ = 2 from rfl]

include h2 hq in
/-- Cross-check against the general dictionary theorem `LevelDatum.seam_mul` (C.10): the
same cleared identity, obtained from the general theorem rather than by direct computation. -/
theorem ell_mul_seam_s2Tower_via_seam_mul :
    ((s2Tower h2 hq).levelDatum h2).ℓ * ((s2Tower h2 hq).levelDatum h2).seam
      = (((s2Tower h2 hq).levelDatum h2).ℓ * ((s2Tower h2 hq).levelDatum h2).r.natDegree)
        * ((s2Tower h2 hq).levelDatum h2).u :=
  LevelDatum.seam_mul _

end Uniformity.Density.Tower.C130np4

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C130np4.levelDatum_natDegree_s2Tower
#print axioms Uniformity.Density.Tower.C130np4.seam_s2Tower
#print axioms Uniformity.Density.Tower.C130np4.seam_s2Tower_intCast
#print axioms Uniformity.Density.Tower.C130np4.seam_s2Tower_nonneg
#print axioms Uniformity.Density.Tower.C130np4.seam_s2Tower_natAvatar
#print axioms Uniformity.Density.Tower.C130np4.ell_mul_seam_s2Tower
#print axioms Uniformity.Density.Tower.C130np4.ell_mul_seam_s2Tower_via_seam_mul

end AxCheck
