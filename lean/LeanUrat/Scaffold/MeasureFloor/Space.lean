/-
BP_I §1.1 — Space and cylinders (MeasureFloor).
Unit I-A9 (`cylinder_vadd`), with its BP-verbatim dependencies
I-A4 (`toLevel`, `toLevel_add`) and I-A5 (`cylinder`).
Unit I-A6 (`isClopen_cylinder` + `measurableSet_cylinder`), with the
I-A2 Borel instance layer per the BP §1.1 instance sketch
(MeasurableSpace := borel on ℤ_[p]; Pi closure from mathlib).
-/
import Mathlib

namespace LeanUrat.Scaffold

open Function  -- scoped ` on ` notation (`Function.onFun`), used by `cylinder_disjoint`

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Monic degree-n polynomials over ℤ_p, as coefficient tuples (brief §1). -/
abbrev Coeff (p n : ℕ) [Fact p.Prime] : Type := Fin n → ℤ_[p]

/-- The level-N residue space: coefficient tuples mod p^N (brief (1); the
tuple twin of `OM.QuotientBox.monicBox`). -/
abbrev Level (p n N : ℕ) : Type := Fin n → ZMod (p ^ N)

-- Unit I-A3: the level-N space has exactly p^(nN) classes (Df §1.1);
-- card anchor: `LeanUrat.OM.QuotientBox.card_residueRing`.
theorem card_level (N : ℕ) : Nat.card (Level p n N) = p ^ (n * N) := by
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out (p := p.Prime)).ne_zero⟩
  rw [Level, Nat.card_pi]
  simp [Nat.card_eq_fintype_card, ZMod.card, ← pow_mul, Nat.mul_comm]

/-! ## I-A1: topology instances on `Coeff`, ℤ_[p] side first, then Pi closure -/

-- ℤ_[p] side (mathlib supplies all four; recorded as the I-A1 gate):
example : CompactSpace ℤ_[p] := inferInstance
example : T2Space ℤ_[p] := inferInstance
example : IsTopologicalAddGroup ℤ_[p] := inferInstance
example : SecondCountableTopology ℤ_[p] := inferInstance

-- Pi closure on `Coeff`:
instance : CompactSpace (Coeff p n) := inferInstance
instance : T2Space (Coeff p n) := inferInstance
instance : IsTopologicalAddGroup (Coeff p n) := inferInstance
instance : SecondCountableTopology (Coeff p n) := inferInstance

/-! ## I-A2: `MeasurableSpace := borel` + `BorelSpace` instances,
ℤ_[p] side first, then Pi closure (needs I-A1 second-countability) -/

/-- I-A2, ℤ_[p] side: the Borel σ-algebra on the p-adic integers (mathlib
carries no `MeasurableSpace ℤ_[p]` instance; this is the first). -/
noncomputable instance : MeasurableSpace ℤ_[p] := borel ℤ_[p]

/-- I-A2, ℤ_[p] side: the σ-algebra just declared is Borel (definitional). -/
instance : BorelSpace ℤ_[p] := ⟨rfl⟩

/-- I-A2, Pi closure: `Coeff` carries the Borel σ-algebra of its product
topology — mathlib's `Pi.borelSpace` chain (countable index, per-slot
second-countable by I-A1); re-declared as the unit's named deliverable
(a `Prop`-valued class, so no instance diamond). -/
instance : BorelSpace (Coeff p n) := Pi.borelSpace

-- I-A2 gates: the product σ-algebra synthesizes on `Coeff`, and it IS borel.
noncomputable example : MeasurableSpace (Coeff p n) := inferInstance
example : (inferInstance : MeasurableSpace (Coeff p n)) = borel (Coeff p n) :=
  BorelSpace.measurable_eq

/-- Componentwise reduction mod p^N (an AddMonoidHom; RingHom per slot). -/
noncomputable def toLevel (N : ℕ) : Coeff p n → Level p n N :=
  fun a i => PadicInt.toZModPow N (a i)

theorem toLevel_add (N : ℕ) (a b : Coeff p n) :
    toLevel p n N (a + b) = toLevel p n N a + toLevel p n N b := by
  funext i
  simp [toLevel]

-- Unit I-A8: the per-slot natural lift `ZMod (p^N) → ℤ_[p]` (via `ZMod.val`
-- cast) is a section of `toZModPow`, so `toLevel` is surjective.
theorem toLevel_surjective (N : ℕ) : Function.Surjective (toLevel p n N) := by
  intro x
  refine ⟨fun i => ((x i).val : ℤ_[p]), ?_⟩
  funext i
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out (p := p.Prime)).ne_zero⟩
  simp only [toLevel, map_natCast]
  exact ZMod.natCast_rightInverse (x i)

/-- The level-N residue class C_N(x) (brief (1)), as a `toLevel` fiber. -/
def cylinder (N : ℕ) (x : Level p n N) : Set (Coeff p n) := toLevel p n N ⁻¹' {x}

-- Unit I-A5: fibers of a function — membership, disjointness, covering.

theorem mem_cylinder_self (N : ℕ) (a : Coeff p n) :
    a ∈ cylinder p n N (toLevel p n N a) := rfl

theorem cylinder_disjoint (N : ℕ) : Pairwise (Disjoint on cylinder p n N) := by
  intro x y hxy
  refine Set.disjoint_left.mpr fun a ha hb => hxy ?_
  simp only [cylinder, Set.mem_preimage, Set.mem_singleton_iff] at ha hb
  exact ha.symm.trans hb

theorem iUnion_cylinder (N : ℕ) : ⋃ x, cylinder p n N x = Set.univ := by
  ext a
  simp [cylinder]

-- Unit I-A7: level cast + refinement.

/-- `levelCast : Level p n (N+1) → Level p n N` is componentwise `ZMod.castHom`. -/
def levelCast (N : ℕ) : Level p n (N + 1) → Level p n N :=
  fun x i => ZMod.castHom (pow_dvd_pow p (Nat.le_succ N)) (ZMod (p ^ N)) (x i)

theorem toLevel_levelCast (N : ℕ) :
    levelCast p n N ∘ toLevel p n (N + 1) = toLevel p n N := by
  funext a i
  exact RingHom.congr_fun
    (PadicInt.zmod_cast_comp_toZModPow (p := p) N (N + 1) (Nat.le_succ N)) (a i)

/-- Refinement: each level-(N+1) class sits inside its level-N cast (brief
Prop H1's splitting; carries the D_σ nesting). -/
theorem cylinder_succ_subset (N : ℕ) (x : Level p n (N + 1)) :
    cylinder p n (N + 1) x ⊆ cylinder p n N (levelCast p n N x) := by
  intro a ha
  have h := congr_fun (toLevel_levelCast p n N) a
  simp only [cylinder, Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
  rw [← ha]
  exact h.symm

/-! ## I-A2b: cylinders form a topological basis -/

/-- Cylinder membership is a `toLevel` equation (definitional). -/
theorem mem_cylinder_iff (N : ℕ) (x : Level p n N) (a : Coeff p n) :
    a ∈ cylinder p n N x ↔ toLevel p n N a = x := Iff.rfl

/-- Two p-adic integers agree mod p^N iff their difference has norm ≤ p^{-N}
(the `toZModPow` kernel plus the span-membership norm characterization). -/
theorem toZModPow_eq_iff_norm_sub_le (N : ℕ) (a b : ℤ_[p]) :
    PadicInt.toZModPow N a = PadicInt.toZModPow N b ↔
      ‖a - b‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero]

open TopologicalSpace in
/-- Cylinders form a topological basis, including the unique degree-zero
cylinder. -/
theorem isTopologicalBasis_cylinders :
    IsTopologicalBasis {s : Set (Coeff p n) | ∃ N x, s = cylinder p n N x} := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out (p := p.Prime)).pos
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · -- every cylinder is open: the sup-metric ball of radius p^{-N} at any of
    -- its points stays in the same fiber (per-slot norm bound → same residue)
    rintro s ⟨N, x, rfl⟩
    rw [Metric.isOpen_iff]
    intro a ha
    refine ⟨(p : ℝ) ^ (-(N : ℤ)), zpow_pos hp _, fun b hb => ?_⟩
    have hba : toLevel p n N b = toLevel p n N a := by
      funext i
      refine (toZModPow_eq_iff_norm_sub_le p N _ _).mpr ?_
      calc ‖b i - a i‖ = dist (b i) (a i) := (dist_eq_norm _ _).symm
        _ ≤ dist b a := dist_le_pi_dist b a i
        _ ≤ (p : ℝ) ^ (-(N : ℤ)) := le_of_lt (Metric.mem_ball.mp hb)
    exact (mem_cylinder_iff p n N x b).mpr
      (hba.trans ((mem_cylinder_iff p n N x a).mp ha))
  · -- basis condition: inside any open u ∋ a pick ε, pad all coordinate
    -- depths to a common N with p^{-N} < ε; the depth-N cylinder at a fits
    intro a u ha hu
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu a ha
    obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
    refine ⟨cylinder p n N (toLevel p n N a), ⟨N, toLevel p n N a, rfl⟩,
      mem_cylinder_self p n N a, fun b hb => hball ?_⟩
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro i
    have hbi : PadicInt.toZModPow N (b i) = PadicInt.toZModPow N (a i) :=
      congrFun ((mem_cylinder_iff p n N _ b).mp hb) i
    calc dist (b i) (a i) = ‖b i - a i‖ := dist_eq_norm _ _
      _ ≤ (p : ℝ) ^ (-(N : ℤ)) := (toZModPow_eq_iff_norm_sub_le p N _ _).mp hbi
      _ < ε := hN

/-- Translation moves classes to classes (feeds the mass law). -/
theorem cylinder_vadd (N : ℕ) (g : Coeff p n) (x : Level p n N) :
    (g + ·) ⁻¹' cylinder p n N x = cylinder p n N (x - toLevel p n N g) := by
  ext a
  simp only [cylinder, Set.mem_preimage, Set.mem_singleton_iff, toLevel_add]
  constructor
  · intro h
    rw [← h]
    abel
  · intro h
    rw [h]
    abel

/-! ## I-A2b closed-ball reading + the I-A6 clopen half

(dedup, wave-1 merge: `isTopologicalBasis_cylinders` itself is declared once
above — same BP-verbatim statement; this block keeps the closed-ball reading
of cylinders and derives I-A6's clopen half from the ultrametric ball API.)

Helper reading: the cylinder through `a` is exactly the sup-metric closed
ball of radius p^{−N} around `a` (per-slot congruence mod p^N = per-slot
norm ≤ p^{−N}). -/

/-- Membership in the cylinder through `a` is the sup-distance bound p^{−N}
(I-A2b helper). -/
theorem mem_cylinder_iff_dist (N : ℕ) (a b : Coeff p n) :
    b ∈ cylinder p n N (toLevel p n N a) ↔ dist b a ≤ (p : ℝ) ^ (-(N : ℤ)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out (p := p.Prime)).pos
  rw [dist_pi_le_iff (zpow_pos hp _).le]
  simp only [cylinder, Set.mem_preimage, Set.mem_singleton_iff, funext_iff, toLevel]
  refine forall_congr' fun i => ?_
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow N,
    RingHom.mem_ker, map_sub, sub_eq_zero]

/-- Each cylinder is the closed p^{−N}-ball around any of its points
(I-A2b helper). -/
theorem cylinder_eq_closedBall (N : ℕ) (x : Level p n N) (a : Coeff p n)
    (ha : a ∈ cylinder p n N x) :
    cylinder p n N x = Metric.closedBall a ((p : ℝ) ^ (-(N : ℤ))) := by
  have hx : toLevel p n N a = x := ha
  ext b
  rw [← hx, Metric.mem_closedBall]
  exact mem_cylinder_iff_dist p n N a b

-- Unit I-A6 (clopen half; transcribed dependency of I-A2b): each class is a
-- closed ball of nonzero radius in the ultrametric sup metric, hence clopen.
theorem isClopen_cylinder (N : ℕ) (x : Level p n N) : IsClopen (cylinder p n N x) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out (p := p.Prime)).pos
  obtain ⟨a, rfl⟩ := toLevel_surjective p n N x
  rw [cylinder_eq_closedBall p n N _ a (mem_cylinder_self p n N a)]
  exact ⟨Metric.isClosed_closedBall, IsUltrametricDist.isOpen_closedBall a (zpow_pos hp _).ne'⟩

-- (dedup, I-A2b prover: a second copy of `isTopologicalBasis_cylinders` —
-- same BP-verbatim statement, closed-ball route — stood here; removed, since
-- the theorem is declared once in the I-A2b section above. Its two helper
-- lemmas `mem_cylinder_iff_dist` / `cylinder_eq_closedBall` and the I-A6
-- clopen half survive above.)

-- Unit I-A2c: both inclusions at once — mathlib's
-- `TopologicalSpace.IsTopologicalBasis.borel_eq_generateFrom` (second-countable
-- space, I-A1) applied to the cylinder basis (I-A2b), read back through the
-- I-A2 `BorelSpace` layer.

/-- Lemma H0: the σ-algebra generated by all cylinders is exactly Borel. -/
theorem generateFrom_cylinders_eq_borel :
    MeasurableSpace.generateFrom
      {s : Set (Coeff p n) | ∃ N x, s = cylinder p n N x} = borel (Coeff p n) :=
  (isTopologicalBasis_cylinders p n).borel_eq_generateFrom.symm

/-! ## Unit I-A6: cylinders are clopen and measurable

`PadicInt.continuous_toZModPow` is a BP search hint absent from the pinned
mathlib tree; per the row's fallback, the per-slot reduction is proved locally
constant directly: by `ker_toZModPow` + `norm_le_pow_iff_mem_span_pow`, two
points share their image mod `p^N` iff they lie within distance `p^(-N)`, so
each fiber and its complement contain an open ball around each of their
points. Clopen → measurable then fires through the I-A2 Borel layer. -/

/-- Per-slot local constancy: inside the radius-`p^(-N)` ball at `a`, the
reduction `PadicInt.toZModPow N` is frozen at its value at `a`. -/
theorem toZModPow_eq_of_dist_lt {N : ℕ} {a b : ℤ_[p]}
    (h : dist b a < (p : ℝ) ^ (-(N : ℤ))) :
    PadicInt.toZModPow N b = PadicInt.toZModPow N a := by
  have hmem : b - a ∈ (Ideal.span {(p : ℤ_[p]) ^ N} : Ideal ℤ_[p]) := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    exact le_of_lt (by simpa [dist_eq_norm] using h)
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  exact hmem

/-- Per-slot fibers of `PadicInt.toZModPow` are clopen in ℤ_[p] (the
locally-constant fallback of BP row I-A6). -/
theorem isClopen_toZModPow_fiber (N : ℕ) (c : ZMod (p ^ N)) :
    IsClopen (PadicInt.toZModPow N ⁻¹' {c} : Set ℤ_[p]) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out (p := p.Prime)).pos
  have hε : (0 : ℝ) < (p : ℝ) ^ (-(N : ℤ)) := zpow_pos hp _
  constructor
  · rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro a ha
    refine ⟨_, hε, fun b hb => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
      at ha ⊢
    rw [toZModPow_eq_of_dist_lt p (Metric.mem_ball.mp hb)]
    exact ha
  · rw [Metric.isOpen_iff]
    intro a ha
    refine ⟨_, hε, fun b hb => ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
    rw [toZModPow_eq_of_dist_lt p (Metric.mem_ball.mp hb)]
    exact ha

-- (dedup, wave-1 merge: `isClopen_cylinder` itself is declared once above, in
-- the I-A2b block — same BP-verbatim statement; the per-slot clopen-fiber
-- route survives here as the two helper lemmas.)

theorem measurableSet_cylinder (N : ℕ) (x : Level p n N) :
    MeasurableSet (cylinder p n N x) :=
  (isClopen_cylinder p n N x).isOpen.measurableSet

end LeanUrat.Scaffold
