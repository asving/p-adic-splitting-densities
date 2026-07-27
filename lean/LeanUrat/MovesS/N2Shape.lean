/-
Unit `n2_shape` (medium; S5 construction batch) — TableShape DATA at n = 2:
block-1 layer (one state, one terminal outcome (1,1), Kmat 1 = 0) + the
THREE-outcome block-2 roster + vEquiv + Wloc/Wstate.  R44: the roster and the
numerators are a CONSISTENCY DEVICE, NOT note displays; note-displayed and
reproduced: the 1×1 block shape, the solve denominator q² + q + 1, the p = 2
ratio-1/8 shadow (`msW_eighth_le`), the checksum shadows.
  o_K   (c=1, m=1, member size 2)          — kcol
  o_spl (c=0, m=2, verdicts (1,1)+(1,1))   — termFin
  o_in  (c=0, m=1, verdict (1,2))          — termFin
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

/-! ### Carriers for the n = 2 instance (private construction data). -/

/-- One state per block level (block-1 and block-2 layers are singletons). -/
private abbrev n2State : ℕ → Type := fun _ => Unit

/-- The R20 structural verdict carrier: the (e, f) pairs of degree e·f ≤ 2. -/
private abbrev n2VType : Type := {ef : ℕ+ × ℕ+ // ((ef.1 : ℕ) * (ef.2 : ℕ)) ≤ 2}

private lemma n2VType_bound (v : n2VType) : (v.1.1 : ℕ) < 3 ∧ (v.1.2 : ℕ) < 3 := by
  obtain ⟨⟨a, b⟩, h⟩ := v
  have ha := a.pos
  have hb := b.pos
  simp only at h
  refine ⟨?_, ?_⟩ <;> nlinarith [ha, hb, h]

noncomputable instance : Fintype n2VType :=
  Fintype.ofInjective
    (fun v : n2VType => ((⟨(v.1.1 : ℕ), (n2VType_bound v).1⟩ : Fin 3),
                         (⟨(v.1.2 : ℕ), (n2VType_bound v).2⟩ : Fin 3)))
    (by
      intro v w hvw
      simp only [Prod.mk.injEq, Fin.mk.injEq] at hvw
      exact Subtype.ext (Prod.ext (PNat.coe_injective hvw.1) (PNat.coe_injective hvw.2)))

/-- Verdict labels as raw carrier elements (used inside the roster; `n2v11` etc.
below name the same objects through `vEquiv`). -/
private def w11 : n2VType := ⟨((1 : ℕ+), (1 : ℕ+)), by decide⟩
private def w12 : n2VType := ⟨((1 : ℕ+), (2 : ℕ+)), by decide⟩

/-- o_K: the kcol outcome — one continuing member of size 2. -/
private def n2outK : Outcome n2VType n2State :=
  ⟨[⟨2, 1, Sum.inr ()⟩], List.cons_ne_nil _ _⟩
/-- o_spl: the (1,1)+(1,1) split terminal outcome. -/
private def n2outSpl : Outcome n2VType n2State :=
  ⟨[⟨1, 1, Sum.inl w11⟩, ⟨1, 1, Sum.inl w11⟩], List.cons_ne_nil _ _⟩
/-- o_in: the (1,2) inert terminal outcome. -/
private def n2outIn : Outcome n2VType n2State :=
  ⟨[⟨2, 1, Sum.inl w12⟩], List.cons_ne_nil _ _⟩
/-- The block-1 layer's single terminal (1,1) outcome. -/
private def n2outT11 : Outcome n2VType n2State :=
  ⟨[⟨1, 1, Sum.inl w11⟩], List.cons_ne_nil _ _⟩

noncomputable def n2T : TableShape 2 where
  State := n2State
  fin := fun _ => inferInstance
  deq := fun _ => inferInstance
  VType := n2VType
  deqV := inferInstance
  finV := inferInstance
  vdeg := fun v => v.1.1 * v.1.2
  vEquiv := Equiv.refl _
  vdeg_spec := fun v => PNat.mul_coe _ _
  Out := fun _ _ => Fin 3
  finO := fun _ _ => inferInstance
  odata := fun e _ o =>
    if e = 2 then
      (if o = 0 then n2outK else if o = 1 then n2outSpl else n2outIn)
    else n2outT11
  Wloc := fun _ _ _ => 0
  Wstate := fun _ _ => 0

/-- THE block-2 state τ★. -/
noncomputable def n2τ : n2T.State 2 := ()
/-- The kcol outcome (rowVal q₀⁻³; the 1/8 shadow at q₀ = 2). -/
noncomputable def n2oK : n2T.Out 2 n2τ := (0 : Fin 3)
/-- The termFin outcome with verdicts (1,1) + (1,1) (rowVal 1 − q₀⁻¹). -/
noncomputable def n2oSpl : n2T.Out 2 n2τ := (1 : Fin 3)
/-- The termFin outcome with verdict (1,2) (rowVal q₀⁻¹ − q₀⁻³). -/
noncomputable def n2oIn : n2T.Out 2 n2τ := (2 : Fin 3)

/-- The verdict labels, named through the R20 structural pin vEquiv. -/
noncomputable def n2v11 : n2T.VType := n2T.vEquiv.symm ⟨(1, 1), by decide⟩
noncomputable def n2v12 : n2T.VType := n2T.vEquiv.symm ⟨(1, 2), by decide⟩
noncomputable def n2v21 : n2T.VType := n2T.vEquiv.symm ⟨(2, 1), by decide⟩

/-- The data pins: routes, verdicts, roster exhaustiveness, one state per block,
the block-1 layer's single terminal (1,1) outcome. -/
theorem n2_shape :
    routeOf (n2T.odata 2 n2τ n2oK) = .kcol ∧
    routeOf (n2T.odata 2 n2τ n2oSpl) = .termFin ∧
    routeOf (n2T.odata 2 n2τ n2oIn) = .termFin ∧
    (n2T.odata 2 n2τ n2oSpl).verdicts = {n2v11, n2v11} ∧
    (n2T.odata 2 n2τ n2oIn).verdicts = {n2v12} ∧
    (n2T.odata 2 n2τ n2oK).m = 1 ∧
    (∀ μ ∈ (n2T.odata 2 n2τ n2oK).mem, μ.size = 2 ∧ μ.δ = 1) ∧
    (∀ o : n2T.Out 2 n2τ, o = n2oK ∨ o = n2oSpl ∨ o = n2oIn) ∧
    (n2oK ≠ n2oSpl ∧ n2oK ≠ n2oIn ∧ n2oSpl ≠ n2oIn) ∧
    (∀ τ : n2T.State 2, τ = n2τ) ∧
    (∀ τ τ' : n2T.State 1, τ = τ') ∧
    (∀ (τ : n2T.State 1) (o : n2T.Out 1 τ),
      routeOf (n2T.odata 1 τ o) = .termFin ∧ (n2T.odata 1 τ o).verdicts = {n2v11}) :=
  by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩⟩
  · decide
  · show ∀ o : Fin 3, o = n2oK ∨ o = n2oSpl ∨ o = n2oIn
    decide
  · show (0 : Fin 3) ≠ 1 ∧ (0 : Fin 3) ≠ 2 ∧ (1 : Fin 3) ≠ 2
    decide

end LeanUrat.MovesS
