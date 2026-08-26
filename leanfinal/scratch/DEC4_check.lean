/-
DEC4 elaboration probes — chapter-C chain-blocker plan (BLOCKERS_PLAN_2026-08-26.md).
Zero sorry, zero axiom.  Each probe certifies one load-bearing claim of the plan:

* PROBE F2-1: the C.27 norm↔resultant SYMMETRY bridge (mechanism 1 of
  `verdict_AC15C27.md`) is DERIVABLE from the landed corpus — B53a's fully generic
  `quotKeyEquiv` + B53c's generic `length_quot_eq_addVal_norm` compose into the
  valuation-level symmetry `v(N_{O[x]/(g)}(Φ mod g)) = v(N_{O[x]/(Φ)}(g mod Φ))`
  for ANY two monic positive-degree polynomials.  No new mathematics.
* PROBE F2-2: the membership-assisted norm-nonzero TRANSFER across the symmetry in both
  directions, the B53c step-2 pattern made generic via Cayley–Hamilton-free divisibility.
  A nonzero scalar in either principal ideal transfers through the quotient equivalence and
  forces the norm on the other side to be nonzero.  This is the exact contract the plan uses:
  ramified exactness supplies the scalar membership; bare norm-nonzero equivalence is NOT claimed.
* PROBE F1-1: the "conditional-on-frontier" landing pattern for the C.35 family
  typechecks — a downstream row's blockFactor-identity reads are supplied by
  `blockFactor_spec_of_frontier` alone.
* PROBE F3-1: the ∀-closures of the two RB3-blocked signed statements
  (`refine_invariants`, `shadow_persistence`) ELABORATE against the landed leanfinal
  vocabulary (composedKey, k2DigitLift, IsTestKey, shadowDev, budgetFloor, theta):
  every ingredient is landed, so the nodes can be attempted in leanfinal directly.
* PROBE F3-2: `dev` additivity (`dev_add_of_monic`, B32a) fires at the exact shape
  the shadow_persistence decomposition needs (dev of `Φ₂^μ₂ + g`).
-/
import Uniformity.ChapB.B53c
import Uniformity.ChapC.C35
import Uniformity.ChapC.C56a
import Uniformity.ChapC.C74
import Uniformity.ChapC.C131w

set_option linter.style.longLine false

namespace DEC4Check

open Polynomial IsLocalRing
open Uniformity.Density Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131k Uniformity.Density.Tower.C131v

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## PROBE F2-1 — the symmetry bridge from landed pieces (mechanism 1 of C.27) -/

/-- **PROBE F2-1.**  `v(N_{O[x]/(g)}(Φ(α))) = v(N_{O[x]/(Φ)}((g %ₘ Φ)(θ)))` for any two
monic positive-degree `Φ, g` with both norms nonzero: B53a's `quotKeyEquiv` (generic — no
key hypothesis, no monicity) + B53c's `length_quot_eq_addVal_norm` (generic — any free
module-finite `O`-algebra), composed.  This is the C.27 obstruction's "mechanism 1"
(norm/resultant symmetry) with the resultant replaced by the length, exactly as B53c
replaced it one level down. -/
theorem addVal_norm_symm (hπ : Irreducible π) {φ g : Polynomial O}
    (hφ : φ.Monic) (hg : g.Monic) (hdφ : 0 < φ.natDegree) (hdg : 0 < g.natDegree)
    (hnzA : Algebra.norm O (AdjoinRoot.mk g φ) ≠ 0)
    (hnzB : Algebra.norm O (AdjoinRoot.mk φ (dev φ g 0)) ≠ 0) :
    IsDiscreteValuationRing.addVal O (Algebra.norm O (AdjoinRoot.mk g φ))
      = IsDiscreteValuationRing.addVal O (Algebra.norm O (AdjoinRoot.mk φ (dev φ g 0))) := by
  classical
  haveI : Module.Free O (AdjoinRoot g) := Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI : Module.Free O (AdjoinRoot φ) := Module.Free.of_basis (AdjoinRoot.powerBasis' hφ).basis
  haveI : Module.Finite O (AdjoinRoot φ) := (AdjoinRoot.powerBasis' hφ).finite
  have hrkA : Module.finrank O (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis' hg).finrank]; rfl
  have hrkB : Module.finrank O (AdjoinRoot φ) = φ.natDegree := by
    rw [(AdjoinRoot.powerBasis' hφ).finrank]; rfl
  have hrA : 0 < Module.finrank O (AdjoinRoot g) := by rw [hrkA]; exact hdg
  have hrB : 0 < Module.finrank O (AdjoinRoot φ) := by rw [hrkB]; exact hdφ
  rw [← length_quot_eq_addVal_norm hπ hrA hnzA, ← length_quot_eq_addVal_norm hπ hrB hnzB]
  exact (quotKeyEquiv φ g).toLinearEquiv.length_eq

/-! ## PROBE F2-2 — membership-assisted norm-nonzero transfer, in both directions -/

/-- **PROBE F2-2.**  If the `AdjoinRoot φ`-side norm is nonzero then so is the
`AdjoinRoot g`-side one: `N_B(z_B) ≠ 0` puts `algebraMap O B (N_B z_B)` in `(z_B)`
(multiplication-by-`z_B` hits it: `z_B ∣ algebraMap (N z_B)` via the quotient
being torsion — here run in the B53c step-2 form: any element of `O` killed in
`B ⧸ (z_B)` is killed in `A ⧸ (z_A)`, and `N_A` of a nonzero `algebraMap` is
nonzero).  This is the hypothesis-discharge half node F2.1 needs so the symmetry
can consume a one-sided nonvanishing certificate. -/
theorem normA_ne_zero_of_normB_ne_zero {φ g : Polynomial O}
    (hg : g.Monic) {c : O} (hc : c ≠ 0)
    (hmemB : algebraMap O (AdjoinRoot φ) c ∈ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)}) :
    Algebra.norm O (AdjoinRoot.mk g φ) ≠ 0 := by
  classical
  haveI : Module.Free O (AdjoinRoot g) := Module.Free.of_basis (AdjoinRoot.powerBasis' hg).basis
  haveI : Module.Finite O (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  have hrkA : Module.finrank O (AdjoinRoot g) = g.natDegree := by
    rw [(AdjoinRoot.powerBasis' hg).finrank]; rfl
  -- transfer the membership through B53a's equivalence, exactly as B53c step 2
  have hmemA : algebraMap O (AdjoinRoot g) c ∈ Ideal.span {AdjoinRoot.mk g φ} := by
    have h2 : algebraMap O (AdjoinRoot φ ⧸ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)}) c
        = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmemB
    have h3 : algebraMap O (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g φ}) c = 0 :=
      (quotKeyEquiv φ g).injective
        (by rw [(quotKeyEquiv φ g).commutes, h2, map_zero])
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hmemA
  intro hzero
  have hnn : Algebra.norm O (algebraMap O (AdjoinRoot g) c) = 0 := by
    rw [hw, map_mul, hzero, zero_mul]
  rw [Algebra.norm_algebraMap, hrkA] at hnn
  exact (pow_ne_zero _ hc) hnn

/-- **PROBE F2-2b.**  The reverse orientation of the same quotient-transfer pattern: a
nonzero scalar in the `AdjoinRoot g`-side principal ideal transfers to the
`AdjoinRoot φ` side and forces the norm of `(dev φ g 0)(θ)` to be nonzero.  Together with
`normA_ne_zero_of_normB_ne_zero`, this is the honest "both-sides" form; neither theorem
asserts a bare implication from one norm's nonvanishing without a scalar-membership witness. -/
theorem normB_ne_zero_of_normA_ne_zero {φ g : Polynomial O}
    (hφ : φ.Monic) {c : O} (hc : c ≠ 0)
    (hmemA : algebraMap O (AdjoinRoot g) c ∈ Ideal.span {AdjoinRoot.mk g φ}) :
    Algebra.norm O (AdjoinRoot.mk φ (dev φ g 0)) ≠ 0 := by
  classical
  haveI : Module.Free O (AdjoinRoot φ) := Module.Free.of_basis (AdjoinRoot.powerBasis' hφ).basis
  haveI : Module.Finite O (AdjoinRoot φ) := (AdjoinRoot.powerBasis' hφ).finite
  have hrkB : Module.finrank O (AdjoinRoot φ) = φ.natDegree := by
    rw [(AdjoinRoot.powerBasis' hφ).finrank]; rfl
  have hmemB : algebraMap O (AdjoinRoot φ) c
      ∈ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)} := by
    have h2 : algebraMap O (AdjoinRoot g ⧸ Ideal.span {AdjoinRoot.mk g φ}) c = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmemA
    have h3 : algebraMap O
        (AdjoinRoot φ ⧸ Ideal.span {AdjoinRoot.mk φ (dev φ g 0)}) c = 0 := by
      rw [← (quotKeyEquiv φ g).commutes, h2, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mp h3
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hmemB
  intro hzero
  have hnn : Algebra.norm O (algebraMap O (AdjoinRoot φ) c) = 0 := by
    rw [hw, map_mul, hzero, zero_mul]
  rw [Algebra.norm_algebraMap, hrkB] at hnn
  exact (pow_ne_zero _ hc) hnn

/-! ## PROBE F1-1 — the conditional-on-frontier landing pattern for the C.35 family -/

/-- **PROBE F1-1.**  A downstream row's `blockFactor L f`-identity reads are fully
supplied by `BlockFrontier L f` through the landed `blockFactor_spec_of_frontier`
(C35.lean): under the frontier, the block is labelled, divides `f`, satisfies the
degree law, and has positive `mult₂` — the exact four reads the 8-row family's
conclusions consume.  This is the shape of every `*_of_frontier` node in the plan. -/
theorem family_reads_of_frontier {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hfr : BlockFrontier L f) :
    HasLabel L (blockFactor L f) ∧ blockFactor L f ∣ f ∧
      (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f ∧ 0 < mult₂ L f :=
  blockFactor_spec_of_frontier L hπ hfr

/-! ## PROBE F3-1 — the two RB3-blocked statements elaborate against landed vocabulary -/

/-- **PROBE F3-1a.**  The ∀-closure of the signed C.56 `refine_invariants`
(leanspec `ChapC.lean:2134`) elaborates against leanfinal's landed vocabulary:
`towerLocus` (C51), `composedKey` (C43), `k2DigitLift` (C56a), `dv2ResPoly` (C38a),
`IsTestKey` (C13), `TowerDatum.levelDatum` (C44).  Every ingredient is landed;
the node is attemptable in leanfinal as stated. -/
def RefineInvariantsStatement : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (_hh : 1 ≤ F.h)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    {μ₂ : ℕ} {f : Polynomial O} (_hf : f ∈ towerLocus T μ₂)
    {lam : ℕ} (_hslope : T.E₂ < lam) {s : AdjoinRoot (towerLabel T)} (_hs : s ≠ 0)
    (hne : (dv2SideSet (T.levelDatum hπ) (composedKey T) f lam 1).Nonempty)
    (_hres : dv2ResPoly (T.levelDatum hπ) (composedKey T) f lam 1 hne
      = (Polynomial.X - Polynomial.C s) ^ μ₂),
    (composedKey T - k2DigitLift T s lam).Monic ∧
    (composedKey T - k2DigitLift T s lam).natDegree = T.D₂ ∧
    IsTestKey (T.levelDatum hπ) (composedKey T - k2DigitLift T s lam)

/-- **PROBE F3-1b.**  The ∀-closure of the signed C.74-family `shadow_persistence`
(leanspec `ChapC.lean:3482`) elaborates against leanfinal's landed vocabulary:
`TouchCert` (C74), `budgetFloor` (C131w-side), `shadowDev`/`dev` (C72/B02),
`TowerDatum.theta` (C71), `dv2Hgt` (C38a-side).  Every ingredient is landed. -/
def ShadowPersistenceStatement : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}
    {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (_hh : 1 ≤ F.h)
    [Finite (ResidueField O)] {μ₂ j : ℕ} (_hj : j < μ₂) (_hc : TouchCert T hπ μ₂ j)
    {g : Polynomial O}
    (_hbudget : ∀ j' a b : ℕ, j' < μ₂ → a < F.e₁ * F.f₁ → b < T.e₂ * T.f₂ →
      (budgetFloor T μ₂ j' a b : ℕ∞)
        ≤ IsDiscreteValuationRing.addVal O
            ((dev F.key (dev (composedKey T) g j') b).coeff a)),
    ((T.theta μ₂ j + 1 : ℕ) : ℕ∞)
        ≤ dv2Hgt (T.levelDatum hπ) (shadowDev T g j - dev (composedKey T) g j) ∧
    dv2Hgt (T.levelDatum hπ)
        (shadowDev T ((composedKey T) ^ μ₂ + g) j
          - dev (composedKey T) ((composedKey T) ^ μ₂ + g) j)
      = (T.theta μ₂ j : ℕ∞)

/-! ## PROBE F3-2 — the persistence decomposition is derivable from landed linearity -/

/-- **PROBE F3-2.**  The `dev`-side decomposition step of `shadow_persistence`'s
clause 2 is already landed: `dev Φ₂ (Φ₂^μ₂ + g) j = dev Φ₂ (Φ₂^μ₂) j + dev Φ₂ g j`
(B32a `dev_add_of_monic`).  What is NOT landed is the same additivity for
`shadowDev`/`biRead` — the plan's node F3.4. -/
theorem dev_decomposes_at_persistence_shape {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hmonic : (composedKey T).Monic)
    (g : Polynomial O) (μ₂ j : ℕ) :
    dev (composedKey T) ((composedKey T) ^ μ₂ + g) j
      = dev (composedKey T) ((composedKey T) ^ μ₂) j + dev (composedKey T) g j :=
  dev_add_of_monic hmonic _ _ j

/-- **PROBE F3-2b.** `biRead` is additive.  This was absent under a public name at RB3,
but it is a short consequence of the landed coefficient formula and B32a's `dev` additivity. -/
theorem biRead_add {F : KeyFrame O π} (a b : Polynomial O) :
    biRead F (a + b) = biRead F a + biRead F b := by
  ext j
  rw [Polynomial.coeff_add, biRead_coeff, biRead_coeff, biRead_coeff,
    dev_add_of_monic F.hmonic, map_add]

/-- **PROBE F3-2c.** The divisor used by the shadow development is monic.  Identify
`biRead` coefficientwise with the mapped canonical `xNF`; C131v's landed `xNF_monic`
then supplies monicity. -/
theorem biRead_composedKey_monic {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) :
    (biRead F (composedKey T)).Monic := by
  have heq : biRead F (composedKey T)
      = (xNF F (composedKey T)).map (AdjoinRoot.mk F.key) := by
    ext j
    rw [biRead_coeff, Polynomial.coeff_map, xNF_coeff, xDigit_eq_dev]
  rw [heq]
  exact (xNF_monic F (composedKey_monic T) (composedKey_natDegree_mul T hπ)).map _

/-- **PROBE F3-2d.** Consequently `shadowDev` itself is additive in the polynomial
argument.  The alleged RB3 additivity gap is assembly, not new mathematics; the genuinely
new persistence mechanism is the coefficient-floor-to-shadow-discrepancy height bridge. -/
theorem shadowDev_add {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
    (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (a b : Polynomial O) (j : ℕ) :
    shadowDev T (a + b) j = shadowDev T a j + shadowDev T b j := by
  letI := F.nontrivial_adjoinRoot
  rw [shadowDev_eq_reass, shadowDev_eq_reass, shadowDev_eq_reass, biRead_add,
    devQ_add (biRead_composedKey_monic T hπ), reass_add]

end DEC4Check

/-! ## Axiom footprint — every probe is Lean-core only -/

section AxCheck
#print axioms DEC4Check.addVal_norm_symm
#print axioms DEC4Check.normA_ne_zero_of_normB_ne_zero
#print axioms DEC4Check.normB_ne_zero_of_normA_ne_zero
#print axioms DEC4Check.family_reads_of_frontier
#print axioms DEC4Check.RefineInvariantsStatement
#print axioms DEC4Check.ShadowPersistenceStatement
#print axioms DEC4Check.dev_decomposes_at_persistence_shape
#print axioms DEC4Check.biRead_add
#print axioms DEC4Check.biRead_composedKey_monic
#print axioms DEC4Check.shadowDev_add
end AxCheck
