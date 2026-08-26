/-
MRAMX elaboration probe (unit MRAMX, 2026-08-26) — ramified level-1 norm exactness at the
frame key, completion-free (docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md).

* Probe X0-a: the T1 statement carrier elaborates against landed vocabulary
  (KeyFrame, stageHeight, AdjoinRoot, Algebra.norm, addVal).  NOT proved here.
* Probe X0-b: the T2 statement carrier elaborates.  NOT proved here.
* Probe X9-a (PROVED): `AdjoinRoot F.key` is a domain from `F.hirr` alone — the B53b
  `keyIsDomain` argument with the frame's own irreducibility field.
* Probe X9-b (PROVED): the Cayley-Hamilton scalar-membership half of T2:
  `algebraMap O A (Algebra.norm O z) ∈ Ideal.span {z}` for ANY finite free O-algebra.
Zero sorry, zero axiom.
-/
import Uniformity.ChapC.C27x
import Uniformity.ChapB.B53c

set_option linter.style.longLine false

namespace MRAMXProbe

open Polynomial IsLocalRing IsDiscreteValuationRing
open Uniformity.Density Uniformity.Density.Leaf Uniformity.Density.Tower

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-- **Probe X0-a.**  The ∀-closure of T1 (`ramified_addVal_norm_exact`), the plan's F2.3
statement carrier: byte-shape of the theorem proved in
docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md §1.  NOT proved in Lean here. -/
def RamifiedNormExactStatement : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    (_hπ : Irreducible π) (F : KeyFrame O π)
    {A₀ : Polynomial O} (_h0 : A₀ ≠ 0) (_hdeg : A₀.natDegree < F.key.natDegree),
    addVal O (Algebra.norm O (AdjoinRoot.mk F.key A₀)) = F.f₁ • F.stageHeight A₀

/-- **Probe X0-b.**  The ∀-closure of T2 (`ramified_norm_scalar_membership`): the nonzero
scalar-membership certificate that the landed BW1 transfer
(`DEC4Check.normA_ne_zero_of_normB_ne_zero`) consumes.  The membership half is PROVED
below (`norm_mem_span_self`); the nonvanishing half is T2's domain argument. -/
def RamifiedNormMembershipStatement : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    (F : KeyFrame O π) {A₀ : Polynomial O} (_h0 : A₀ ≠ 0)
    (_hdeg : A₀.natDegree < F.key.natDegree),
    Algebra.norm O (AdjoinRoot.mk F.key A₀) ≠ 0 ∧
      algebraMap O (AdjoinRoot F.key) (Algebra.norm O (AdjoinRoot.mk F.key A₀))
        ∈ Ideal.span {AdjoinRoot.mk F.key A₀}

/-- **Probe X9-a.**  `AdjoinRoot F.key` is a domain, from `F.hirr` alone: irreducible is
prime in the UFD `O[X]`, so the principal ideal is prime.  (B53b's `keyIsDomain` shape,
with the frame's own irreducibility replacing the `IsKey` reduction argument.) -/
theorem keyFrame_isDomain (F : KeyFrame O π) : IsDomain (AdjoinRoot F.key) :=
  (Ideal.Quotient.isDomain_iff_prime (Ideal.span {F.key})).mpr
    ((Ideal.span_singleton_prime F.hmonic.ne_zero).mpr
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp F.hirr))

/-- **Probe X9-b (the Cayley-Hamilton membership).**  In any module-finite free algebra
over a commutative ring, the norm of `z`, pushed through `algebraMap`, lies in the
principal ideal `(z)`: evaluate the characteristic polynomial of multiplication-by-`z`
at `z` (zero by Cayley-Hamilton), and isolate the constant coefficient
`(-1)^n · norm z`. -/
theorem norm_mem_span_self {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A] (z : A) :
    algebraMap R A (Algebra.norm R z) ∈ Ideal.span {z} := by
  classical
  set f := Algebra.lmul R A z with hf
  have hCH : Polynomial.aeval (f : Module.End R A) (LinearMap.charpoly f) = 0 :=
    LinearMap.aeval_self_charpoly f
  -- transport Cayley-Hamilton along the algebra hom `lmul : A →ₐ End R A`
  have hz : Polynomial.aeval z (LinearMap.charpoly f) = 0 := by
    have hcomm : (Algebra.lmul R A) (Polynomial.aeval z (LinearMap.charpoly f))
        = Polynomial.aeval (f : Module.End R A) (LinearMap.charpoly f) := by
      rw [Polynomial.aeval_algHom_apply]
    have h0 : (Algebra.lmul R A) (Polynomial.aeval z (LinearMap.charpoly f)) = 0 := by
      rw [hcomm, hCH]
    have := congrArg (fun (g : Module.End R A) => g 1) h0
    simpa using this
  -- split off the constant coefficient: χ(z) = z * (Σ higher) + algebraMap (χ.coeff 0)
  set χ := LinearMap.charpoly f with hχ
  have hsplit : Polynomial.aeval z χ
      = z * Polynomial.aeval z (χ.divX) + algebraMap R A (χ.coeff 0) := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add χ]
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    ring
  have hmem : algebraMap R A (χ.coeff 0) ∈ Ideal.span {z} := by
    have heq : algebraMap R A (χ.coeff 0) = -(z * Polynomial.aeval z (χ.divX)) := by
      rw [hz] at hsplit
      linear_combination -hsplit
    rw [heq]
    exact neg_mem (Ideal.mem_span_singleton.mpr ⟨_, rfl⟩)
  -- the norm is `(-1)^n` times the constant coefficient; absorb the sign into the ideal
  have hc0 : Algebra.norm R z = (-1) ^ Module.finrank R A * χ.coeff 0 := by
    rw [Algebra.norm_apply, hχ, hf]
    exact LinearMap.det_eq_sign_charpoly_coeff _
  rw [hc0, map_mul]
  exact Ideal.mul_mem_left _ _ hmem

end MRAMXProbe

/-! ## Axiom footprint -/

section AxCheck
#print axioms MRAMXProbe.RamifiedNormExactStatement
#print axioms MRAMXProbe.RamifiedNormMembershipStatement
#print axioms MRAMXProbe.keyFrame_isDomain
#print axioms MRAMXProbe.norm_mem_span_self
end AxCheck
