/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB.B25
import Uniformity.Quarry.AdjoinRootDVR

/-!
# Uniformity.ChapB.B49 — the leaf's order is local, with residual residue field

**Chapter B, NODE B.49** (`blueprint/CHAP-B_leaf_layer.md` §7), ENV-C.  Let `φ` be an order-1 key
and `g` monic with `ḡ = φ̄ ^ k` for some `k ≥ 1`.  Then `A := AdjoinRoot g` is a **local ring**,
and its residue field is `resField φ`.

Two signed declarations, both `[repaired: A-F.3/B-D2+B-D3]`:

* `instLocalRingAdjoinRoot` — a **theorem**, not an `instance`.  `IsLocalRing (AdjoinRoot g)` is a
  proof obligation, and an `instance` carrying the explicit non-class hypotheses
  `hφ`/`hg`/`hk`/`hres` is a hard error at our pin ("this instance has arguments that cannot be
  inferred using typeclass synthesis").  **Consumers must apply it explicitly** at every use site.
* `residueFieldEquiv` — data (`≃+*`) that only a proof can construct.  Its type names the local
  structure explicitly, `@IsLocalRing.ResidueField (AdjoinRoot g) _ (instLocalRingAdjoinRoot …)`,
  because nothing supplies `IsLocalRing (AdjoinRoot g)` by typeclass synthesis.

## The route actually taken, and why it is not the blueprint's

The blueprint's PROOF goes (1) `A ⧸ πA ≅ F[X] ⧸ (ḡ)`, (2) `F[X] ⧸ (φ̄ ^ k)` is local, (3) lift
locality back up through the surjection, (4) identify the residue field, (5) transport B.26's
`finrank`.  That plan carries the SPLIT MANDATE `B49a` = step 1, `B49b` = step 2, `B49c` = steps
3–5.

**The delivered proof has neither step 1 nor step 2**, so those two files would be empty and the
mandated split boundary does not exist in it; the node therefore lands as the single file
`B49.lean`.  The delivered route names the maximal ideal directly and never forms `A ⧸ πA`:

Let `Φ : A →+* resField φ` be `AdjoinRoot.map (residue O) g φ̄` — available because `φ̄ ∣ ḡ = φ̄ ^ k`
(this is where `0 < k` enters) — so that `Φ (mk g P) = mk φ̄ (P mod 𝔪)`.

1. **`Φ` is surjective** (`mk φ̄`, `Polynomial.map (residue O)` and `mk g` all are), so
   `A ⧸ ker Φ ≃+* resField φ`, a field because `φ̄` is irreducible (B.25's `instFieldResField`);
   hence **`ker Φ` is maximal** (`leafResKer_isMaximal`).
2. **Every maximal ideal `M` of `A` equals `ker Φ`.**  `A` is module-finite over `O` (`g` monic),
   hence integral, so `M` contracts to a maximal ideal of `O`, i.e. to `𝔪`, and therefore
   `𝔪 · A ≤ M` — this is the Quarry backport's own argument
   (`IsLocalRing.of_isMaximal_map_maximalIdeal`, `Uniformity/Quarry/AdjoinRootDVR.lean`), reused
   here at `k ≥ 2` where `𝔪 · A` is no longer maximal.  Next, `(mk g φ) ^ k = mk g (φ ^ k)` and
   `φ ^ k − g` reduces to `0` mod `𝔪`, so `(mk g φ) ^ k ∈ 𝔪 · A ≤ M`, and `M` prime gives
   `mk g φ ∈ M`.  Finally `ker Φ ≤ M`: if `Φ (mk g P) = 0` then `φ̄ ∣ P mod 𝔪`, say
   `P mod 𝔪 = φ̄ · (Q mod 𝔪)`, and then `mk g P = mk g (P − φ·Q) + mk g φ · mk g Q` with the first
   summand in `𝔪 · A` (all its coefficients reduce to `0`) and the second in `M`.  Two maximal
   ideals with `ker Φ ≤ M` are equal.
3. `IsLocalRing.of_unique_max_ideal` closes `instLocalRingAdjoinRoot`, and then
   `maximalIdeal A = ker Φ` (`IsLocalRing.eq_maximalIdeal`), so
   `ResidueField A = A ⧸ maximalIdeal A ≃+* A ⧸ ker Φ ≃+* resField φ` is `residueFieldEquiv`.

**The `finrank` clause of the STATEMENT is not a signed declaration** (the stub signs exactly the
two rows above); it is B.26's `finrank_resField` transported along `residueFieldEquiv`, and it
lands wherever B.26 lands.

## ⚠ This node generalises a landed node and does not redefine it

`Uniformity.Density.isMaximal_map_maximalIdeal_adjoinRoot` (`Density/InertLeaf.lean:71`) and the
Quarry's `AdjoinRoot.isMaximal_map_maximalIdeal` prove the `k = 1` case in the **stronger** form
"`𝔪 · A` is maximal".  At `k ≥ 2` that is **false** — `A ⧸ 𝔪A ≅ F[X] ⧸ (φ̄ ^ k)` has nilpotents —
which is exactly why the generalisation is "`A` is local with residue field `resField φ`".  Both
landed declarations are consumed unchanged at `k = 1` and neither is touched.

DEPENDS: B.01 (`IsKey`) · B.25 (`resField`, `instFieldResField`) · the Quarry backport
`Uniformity/Quarry/AdjoinRootDVR.lean` (imported for its integrality template; the shape of step 2
is its `IsLocalRing.of_isMaximal_map_maximalIdeal` argument) · mathlib `AdjoinRoot.map`,
`AdjoinRoot.mk_eq_zero`, `AdjoinRoot.mk_surjective`, `Polynomial.Monic.finite_adjoinRoot`,
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`, `Ideal.mem_map_C_iff`,
`Ideal.Quotient.maximal_of_isField`, `RingHom.quotientKerEquivOfSurjective`,
`IsLocalRing.of_unique_max_ideal`, `IsLocalRing.eq_maximalIdeal`, `IsLocalRing.ker_residue`.

**ENV-C is over-strong for this node.**  `[IsAdicComplete (maximalIdeal O) O]` and
`[Finite (ResidueField O)]` are auto-included section variables that neither signed proof consumes
(finiteness enters only at the blueprint's step 5, i.e. through B.26).  On the two signed
declarations they are **kept**, not `omit`ted, so the binder lists match the frozen stub
(`leanspec/Leanspec/ChapB.lean`, **B.49a**, **B.49b**, both signed inside its ENV-C section); only
`linter.unusedSectionVars` is silenced there.  The five private helpers, which are not signed and
whose binder lists are free, are declared **above** the ENV-C section, in plain ENV-A.

**SOURCE.** `EFF.HE3.10` verbatim: "Stage ring `R = O[x]/(Φ′)` is an order in field `L = K₀(θ)`,
**NOT a complete DVR in general**; carried through `O_L`" — the corpus's own record that the leaf's
order need not be maximal, which is why D-3 works with `AdjoinRoot g` and states its perimeter;
also `EFF.HE3.10`'s `[r1,F7]` correction (the carrier is `O_L`, not `R`).

**TEETH.** signed non-applicable (a structural lemma).

## Status

Sorry-free, axiom-free (Lean core only).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Leaf

open IsLocalRing Polynomial

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-! ### The residual surjection `Φ : AdjoinRoot g → resField φ` -/

/-- The residual surjection of the leaf: `AdjoinRoot g → resField φ`, reduction of the
coefficients mod `𝔪` followed by reduction mod `φ̄`.  It exists because `φ̄ ∣ ḡ = φ̄ ^ k`
(`0 < k`). -/
private noncomputable def leafRes {φ g : Polynomial O} {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    AdjoinRoot g →+* resField φ :=
  AdjoinRoot.map (IsLocalRing.residue O) g (φ.map (IsLocalRing.residue O))
    (by rw [hres]; exact dvd_pow_self _ hk.ne')

/-- `Φ` on a representative: reduce the coefficients, then reduce mod `φ̄`. -/
private theorem leafRes_mk {φ g : Polynomial O} {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k)
    (P : Polynomial O) :
    leafRes hk hres (AdjoinRoot.mk g P)
      = AdjoinRoot.mk (φ.map (IsLocalRing.residue O)) (P.map (IsLocalRing.residue O)) := by
  simp [leafRes, AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map,
    ← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

/-- `Φ` is surjective: `mk g`, `Polynomial.map (residue O)` and `mk φ̄` all are. -/
private theorem leafRes_surjective {φ g : Polynomial O} {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    Function.Surjective (leafRes hk hres) := by
  intro y
  obtain ⟨Y, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue O)
    IsLocalRing.residue_surjective Y
  exact ⟨AdjoinRoot.mk g Q, leafRes_mk hk hres Q⟩

/-- A polynomial whose reduction mod `𝔪` vanishes has its class in `𝔪 · AdjoinRoot g`. -/
private theorem mk_mem_map_maximalIdeal {g P : Polynomial O}
    (hP : P.map (IsLocalRing.residue O) = 0) :
    AdjoinRoot.mk g P ∈ (maximalIdeal O).map (algebraMap O (AdjoinRoot g)) := by
  have hcoeff : ∀ n, P.coeff n ∈ maximalIdeal O := by
    intro n
    have hn : (IsLocalRing.residue O) (P.coeff n) = 0 := by
      rw [← Polynomial.coeff_map, hP, Polynomial.coeff_zero]
    rwa [← IsLocalRing.ker_residue, RingHom.mem_ker]
  have hPmem : P ∈ (maximalIdeal O).map (Polynomial.C : O →+* Polynomial O) :=
    Ideal.mem_map_C_iff.2 hcoeff
  have hle : ((maximalIdeal O).map (Polynomial.C : O →+* Polynomial O)).map (AdjoinRoot.mk g)
      ≤ (maximalIdeal O).map (algebraMap O (AdjoinRoot g)) := by
    rw [Ideal.map_map, AdjoinRoot.algebraMap_eq]
    exact le_rfl
  exact hle (Ideal.mem_map_of_mem _ hPmem)

/-! ### The kernel of `Φ` is maximal -/

/-- `ker Φ` is a maximal ideal of `AdjoinRoot g`: the quotient by it is `resField φ`, a field
because `φ̄` is irreducible. -/
private theorem leafResKer_isMaximal {φ : Polynomial O} (hφ : IsKey φ) {g : Polynomial O} {k : ℕ}
    (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    (RingHom.ker (leafRes hk hres)).IsMaximal := by
  letI := instFieldResField hφ
  exact Ideal.Quotient.maximal_of_isField _
    ((RingHom.quotientKerEquivOfSurjective (leafRes_surjective hk hres)).toMulEquiv.isField
      (Field.toIsField (resField φ)))

section ENVC
-- ENV-C.  Neither instance is consumed below; both are kept to match the frozen stub.
variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-! ### The two signed declarations -/

set_option linter.unusedSectionVars false in
/-- **B.49 (a) — the leaf's order is local.**  For an order-1 key `φ` and monic `g` with
`ḡ = φ̄ ^ k`, `k ≥ 1`, the ring `AdjoinRoot g` is local.  Its maximal ideal is the kernel of the
residual surjection onto `resField φ`; at `k ≥ 2` it is strictly larger than `𝔪 · AdjoinRoot g`,
which is then not maximal.

`[repaired: A-F.3/B-D2+B-D3]`: a `theorem`, not an `instance` — apply it EXPLICITLY at every use
site (`haveI := instLocalRingAdjoinRoot hφ hg hk hres`). -/
theorem instLocalRingAdjoinRoot {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    IsLocalRing (AdjoinRoot g) := by
  have hmax := leafResKer_isMaximal hφ hk hres
  refine IsLocalRing.of_unique_max_ideal ⟨RingHom.ker (leafRes hk hres), hmax, ?_⟩
  intro M hM
  haveI : Module.Finite O (AdjoinRoot g) := hg.finite_adjoinRoot
  haveI : Algebra.IsIntegral O (AdjoinRoot g) := Algebra.IsIntegral.of_finite O _
  -- integrality: `M` contracts to `𝔪`, hence contains `𝔪 · A`
  have hc : (M.comap (algebraMap O (AdjoinRoot g))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hmM : (maximalIdeal O).map (algebraMap O (AdjoinRoot g)) ≤ M := by
    rw [← IsLocalRing.eq_maximalIdeal hc]; exact Ideal.map_comap_le
  -- `(mk g φ) ^ k ∈ 𝔪 · A ≤ M`, and `M` is prime
  have hφx : AdjoinRoot.mk g φ ∈ M := by
    refine hM.isPrime.mem_of_pow_mem k ?_
    have hzero : ((φ ^ k - g).map (IsLocalRing.residue O)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_pow, hres, sub_self]
    have hstep : AdjoinRoot.mk g (φ ^ k - g) = (AdjoinRoot.mk g φ) ^ k := by
      rw [map_sub, AdjoinRoot.mk_self, sub_zero, map_pow]
    exact hmM (hstep ▸ mk_mem_map_maximalIdeal hzero)
  -- `ker Φ ≤ M`
  have hker : RingHom.ker (leafRes hk hres) ≤ M := by
    intro y hy
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective y
    rw [RingHom.mem_ker, leafRes_mk] at hy
    obtain ⟨Y, hY⟩ := AdjoinRoot.mk_eq_zero.1 hy
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue O)
      IsLocalRing.residue_surjective Y
    have hzero : ((P - φ * Q).map (IsLocalRing.residue O)) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hY, sub_self]
    have hsplit : AdjoinRoot.mk g P
        = AdjoinRoot.mk g (P - φ * Q) + AdjoinRoot.mk g φ * AdjoinRoot.mk g Q := by
      rw [← map_mul, ← map_add]
      congr 1
      ring
    rw [hsplit]
    exact M.add_mem (hmM (mk_mem_map_maximalIdeal hzero)) (M.mul_mem_right _ hφx)
  exact (hmax.eq_of_le hM.ne_top hker).symm

set_option linter.unusedSectionVars false in
/-- **B.49 (b) — the leaf's residue field is the residual field of the key.**  Under
`instLocalRingAdjoinRoot`, `IsLocalRing.ResidueField (AdjoinRoot g) ≃+* resField φ`.

`[repaired: A-F.3/B-D2+B-D3]`: the type applies the local-ring structure explicitly, since
nothing supplies `IsLocalRing (AdjoinRoot g)` by typeclass synthesis. -/
noncomputable def residueFieldEquiv {φ : Polynomial O} (hφ : IsKey φ)
    {g : Polynomial O} (hg : g.Monic) {k : ℕ} (hk : 0 < k)
    (hres : g.map (IsLocalRing.residue O) = (φ.map (IsLocalRing.residue O)) ^ k) :
    @IsLocalRing.ResidueField (AdjoinRoot g) _ (instLocalRingAdjoinRoot hφ hg hk hres) ≃+*
      resField φ :=
  haveI := instLocalRingAdjoinRoot hφ hg hk hres
  (Ideal.quotEquivOfEq
      (IsLocalRing.eq_maximalIdeal (leafResKer_isMaximal hφ hk hres)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (leafRes_surjective hk hres))

end ENVC

end Uniformity.Density.Leaf

/-! ## Axiom footprint -/

section AxCheck
#print axioms Uniformity.Density.Leaf.instLocalRingAdjoinRoot
#print axioms Uniformity.Density.Leaf.residueFieldEquiv
end AxCheck
