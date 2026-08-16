/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapF.F04
import Uniformity.ChapF.F11
import Uniformity.ChapF.F12

/-!
# Uniformity.ChapF.F28 — `WeldObligations`: the carried-hypothesis block handed to chapter I

**Chapter F, NODE F.28** [def] (`blueprint/CHAP-F_weld_layer.md` §9), ENV-F1. One field per
SURVIVING Display-A weld obligation, at exactly ledger strength — nothing added, nothing
dropped:

* `jd0box2` — F.04's `JD0-BOX-2` perimeter (HYP.74) for each consumed value-dictionary
  site; the seven-site family is abstracted as the index type `Site`.
* `genhnBox2` — F.11's `GENHN-BOX-2` face (HYP.148, CARRY) for each carry site; the `μ ≥ 3`
  guard lives inside `GenhnBox2`, and chapter I indexes the conjunct field by `n ≥ 6`.
* `w1` — F.12's `W-1` transport (HYP.139, MATH) for the FGMN-framed sites.

**Annotations carried alongside — deliberately NOT Prop fields.** (i) The gate-(b) cite flag
on F.26: `[cite: FGMN Thm 4.2 (rank-one freeness), via EFF.GRTJC.43's (IN-3) package]`,
owner sign-off at chapter I's cite block. (ii) The `AllOInterfaces[W/J, J-D0]` generality
conjuncts (HYP.126, HYP.129): supplied STRUCTURALLY, by every F statement being quantified
over every finite `K` / every `O` and both characteristics — the ledger ROWS and their
conjunct fields remain chapter I's, and F does not absorb them.

**Termination discipline (Part V).** Every field here terminates in chapter I as a discharge
node or a gate-(b) literature cite — no third category. The one pending discharge route is
the blueprint's §8 arc (HYP.149), which is IN-PROGRESS and consumed by nothing in this
chapter: until its fold books it, HYP.148 stays CARRY and HYP.139 stays MATH, both at full
strength, and every carrier statement stands as written.

**Shape.** `Prop`-valued (`structure … : Prop where`) so the block can sit inside chapter
I's hypothesis position without size issues; the three site index types are PARAMETERS
because the concrete site enumerations are other chapters' objects (GC-13) — no F node
constructs one. The completeness certificate is the §3 reconciliation check: the Display-A
weld footprint is exactly these three fields plus the generality rows. Signature
byte-identical to the stage-0e gate.
-/

namespace Uniformity.Density.Weld

/-- The weld layer's carried obligations (chapter I's Display-A weld fields), at ledger
strength. -/
structure WeldObligations {K : Type*} [Field K] {Γ : Type*} [AddCommGroup Γ]
    {Site CSite FSite : Type*}
    (vsite : Site → ValueDictSite Γ K) (csite : CSite → CarrySite K)
    (Rh RG : FSite → K) : Prop where
  jd0box2 : ∀ s, JD0Box2 (vsite s)
  genhnBox2 : ∀ s, GenhnBox2 (csite s)
  w1 : W1Transport Rh RG

end Uniformity.Density.Weld
