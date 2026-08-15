/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B26
import Uniformity.ChapB.B49
import Uniformity.ChapB.B51
import Uniformity.Density.TypeOf

/-!
# Uniformity.ChapB.B52 — the residue-degree lower bound at the key level

**Chapter B, NODE B.52** [lemma] (`blueprint/CHAP-B_leaf_layer.md` §7, the `(e,f)` layer), ENV-C.

*The residue-degree lower bound at the key level.* Let `φ` be an order-1 key with
`m = φ.natDegree`, and let `g` be monic of positive degree with `ḡ = φ̄ ^ k`, `k ≥ 1`. Then

```
m ∣ inertiaDegOf g.
```

This is the `m` half of GMN Cor 1.20 ("`f(L/K)` is divisible by `m · deg ψ_i`"); the `deg ψ_i`
half is the chapter's explicit non-node `B-BOX-1`.

DEPENDS: B.01 (`IsKey`) · B.25 (`resField`) · B.26 (`instFiniteResField`, `card_resField`) ·
B.49 (`instLocalRingAdjoinRoot`, `residueFieldEquiv`) · B.51 (`residueDeg_dvd_addVal_norm`) ·
landed `Uniformity.Density.inertiaDegOf`, `normValues`, `normDivisors`,
`normValues_nonempty`, `inertiaDegOf_mem_normDivisors`, `inertiaDegOf_pos`, `le_inertiaDegOf`
(`Density/TypeOf.lean`), `Uniformity.Density.residueCard`, `two_le_residueCard`
(`Density/LocalData.lean`) · mathlib `AdjoinRoot.powerBasis'`, `Module.natCard_eq_pow_finrank`,
`Nat.pow_right_injective`, `Nat.lcm_dvd`, `Nat.lcm_pos`.

**PROOF.**
1. `A := AdjoinRoot g` is local (B.49 (a)), free and module-finite over `O`
   (`AdjoinRoot.powerBasis' hg`).
2. Its residue field has `ResidueField O`-dimension `m`. B.49 (b) gives only a **ring**
   isomorphism `ResidueField A ≃+* resField φ`, not a `ResidueField O`-linear one, so the
   dimension is read off **cardinalities** instead (this is why the node is ENV-C and not
   ENV-B — see the type-diff note below): `Nat.card (ResidueField A) = Nat.card (resField φ)
   = q ^ m` (B.26 (c)) and `Nat.card (ResidueField A) = q ^ dim` (`Module.natCard_eq_pow_finrank`),
   with `q = Nat.card (ResidueField O) ≥ 2` (`two_le_residueCard`), so `dim = m` by
   `Nat.pow_right_injective`.
3. B.51 at `s := m` then gives `m ∣ x` for every `x ∈ normValues g`, i.e. `m ∈ normDivisors g`.
4. **The lcm step (the node's flagged subtlety).** `inertiaDegOf g = sSup (normDivisors g)` is a
   supremum, *not* a gcd by definition, and this node has **no witness in `normValues g`** to
   feed the recognition principle `inertiaDegOf_eq_of` (B.55 does; that is the difference between
   the two nodes). So: `Nat.lcm m (inertiaDegOf g)` is again a common divisor of every
   norm-valuation (`Nat.lcm_dvd`), hence lies in `normDivisors g`, hence is `≤ inertiaDegOf g`
   by `le_inertiaDegOf`; it is also `≥ inertiaDegOf g` (a positive multiple), so it **equals**
   `inertiaDegOf g`, and `m ∣ Nat.lcm m (inertiaDegOf g) = inertiaDegOf g`.

## Type diff against the stage-0e stub: both ENV-C instances are included here

Exactly the artifact recorded at B.26 row (b), on **both** ENV-C binders. The blueprint's
ENVIRONMENT for this node is **ENV-C** = `[IsAdicComplete (maximalIdeal O) O]` +
`[Finite (ResidueField O)]`; the stub's `axiom` form silently drops both, because the *statement*
`φ.natDegree ∣ inertiaDegOf g` names neither, while this `theorem` uses both in the proof
(`Finite (ResidueField O)` in step 2, which counts elements of the residue fields;
`IsAdicComplete` through B.49's `instLocalRingAdjoinRoot`/`residueFieldEquiv`), so Lean's
use-driven variable inclusion keeps them. Recorded for the 0e type diff: the mismatch is the
blueprint's own declared ENV-C hypotheses reappearing, not a weakening introduced here.

## Faithfulness

`docs/GMN_citations.md` Cor 1.20, the `m` half. The Lean statement is the divisibility, not the
inequality `m ≤ f`: the inequality is what `le_inertiaDegOf` gives directly and it is strictly
weaker (it would not survive the `(e,f)` bracket of B.55).

**TEETH.** `HE-SIG` (`EFF.HE3.52`, 947 PARI jobs, 0 bad) stays an executable regression; nothing
here consumes it.

SOURCE: landed `Density/TypeOf.lean`; `docs/GMN_citations.md` Cor 1.20.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Leaf

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

section ENVC

-- ENV-C (blueprint §0.1): ENV-B plus finiteness of the residue field.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **B.52 — the residue-degree lower bound at the key level.** For an order-1 key `φ` and a
monic `g` of positive degree whose reduction is a power of `φ̄`, the key's degree divides the
residue degree of `g`. -/
theorem key_natDegree_dvd_inertiaDegOf (hπ : Irreducible π) {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) (hd : 0 < g.natDegree) {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    φ.natDegree ∣ inertiaDegOf g := by
  classical
  -- Step 1: the leaf's order is a local, free, module-finite `O`-algebra.
  haveI hloc : IsLocalRing (AdjoinRoot g) := instLocalRingAdjoinRoot hφ hg hk hres
  haveI hfin : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI hfree : Module.Free O (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  haveI hResFin : Finite (resField φ) := instFiniteResField hφ
  have hequiv := residueFieldEquiv hφ hg hk hres
  haveI : Finite (IsLocalRing.ResidueField (AdjoinRoot g)) :=
    Finite.of_equiv _ hequiv.toEquiv.symm
  -- Step 2: its residue field has `ResidueField O`-dimension `φ.natDegree`, counted.
  have hcard : Nat.card (IsLocalRing.ResidueField (AdjoinRoot g))
      = Nat.card (ResidueField O) ^ φ.natDegree := by
    rw [Nat.card_congr hequiv.toEquiv]
    exact card_resField hφ
  have hs : Module.finrank (ResidueField O) (IsLocalRing.ResidueField (AdjoinRoot g))
      = φ.natDegree := by
    have hpow : Nat.card (IsLocalRing.ResidueField (AdjoinRoot g))
        = Nat.card (ResidueField O)
          ^ Module.finrank (ResidueField O) (IsLocalRing.ResidueField (AdjoinRoot g)) :=
      Module.natCard_eq_pow_finrank
    refine Nat.pow_right_injective (two_le_residueCard O) ?_
    change Nat.card (ResidueField O)
        ^ Module.finrank (ResidueField O) (IsLocalRing.ResidueField (AdjoinRoot g))
      = Nat.card (ResidueField O) ^ φ.natDegree
    rw [← hpow, hcard]
  -- Step 3: `φ.natDegree` is a common divisor of the norm-valuations.
  have hne : (normValues g).Nonempty := normValues_nonempty hg hd
  have hmem : φ.natDegree ∈ normDivisors g := by
    refine ⟨hφ.pos, fun x hx => ?_⟩
    obtain ⟨-, z, -, hzval⟩ := hx
    exact residueDeg_dvd_addVal_norm hπ hs hzval
  -- Step 4: the lcm step — `sSup` is not a gcd by definition, and no witness is available.
  have hI := inertiaDegOf_mem_normDivisors hne
  have hIpos : 0 < inertiaDegOf g := inertiaDegOf_pos hne
  have hlcmpos : 0 < Nat.lcm φ.natDegree (inertiaDegOf g) := Nat.lcm_pos hφ.pos hIpos
  have hlcm : Nat.lcm φ.natDegree (inertiaDegOf g) ∈ normDivisors g :=
    ⟨hlcmpos, fun x hx => Nat.lcm_dvd (hmem.2 x hx) (hI.2 x hx)⟩
  have heq : Nat.lcm φ.natDegree (inertiaDegOf g) = inertiaDegOf g :=
    le_antisymm (le_inertiaDegOf hne hlcm)
      (Nat.le_of_dvd hlcmpos (Nat.dvd_lcm_right _ _))
  exact heq ▸ Nat.dvd_lcm_left φ.natDegree (inertiaDegOf g)

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.key_natDegree_dvd_inertiaDegOf
end AxCheck
