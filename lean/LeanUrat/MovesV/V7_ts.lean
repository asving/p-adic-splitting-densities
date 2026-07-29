/-  MovesV unit V7-3a `tableShape_inst` (odata CONSTRUCTIBLE REV 5, Codex-2)
    — the `MovesS.TableShape n` instance from `CtsFamily`.  [E-PHASE FORM:
    theorem-under-data (Fintype/DecidableEq instance arguments explicit; the
    odata map's omem_size casts + route_eq clause are the ∃-bound content) —
    the full field-by-field construction is the prover's; MANIFEST
    deviations.] -/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesV.V2_cells

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

/-- the block-e CTS state carrier. -/
def StateOf (n : ℕ) (e : ℕ) : Type :=
  {p : Σ s : Skeleton n, PUnit // skBlk p.1 = e}

theorem tableShape_inst {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∃ T : MovesS.TableShape n,
      Nonempty (T.VType ≃ VLabel n) ∧
      ∀ e (τ : T.State e) (o : T.Out e τ), (T.odata e τ o).mem ≠ [] := by
  classical
  haveI := hfin
  -- Fintype on the state carrier (finite skeletons ⟹ finite block-e cells).
  haveI hSt : ∀ e, Fintype (StateOf n e) := by
    intro e
    have : Finite (StateOf n e) := by unfold StateOf; infer_instance
    exact Fintype.ofFinite _
  -- Fintype on VLabel n via the bound e ≤ e·f ≤ n.
  haveI hVL : Fintype (VLabel n) := by
    apply Fintype.ofInjective
      (β := Fin (n + 1) × Fin (n + 1))
      (fun v : VLabel n =>
        (⟨(v.1.1 : ℕ), by
            have h1 : ((v.1.1 : ℕ)) ≤ (v.1.1 : ℕ) * (v.1.2 : ℕ) :=
              Nat.le_mul_of_pos_right _ v.1.2.pos
            have := v.2; omega⟩,
         ⟨(v.1.2 : ℕ), by
            have h2 : ((v.1.2 : ℕ)) ≤ (v.1.1 : ℕ) * (v.1.2 : ℕ) :=
              Nat.le_mul_of_pos_left _ v.1.1.pos
            have := v.2; omega⟩))
    intro a b hab
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hab
    apply Subtype.ext
    apply Prod.ext
    · exact PNat.coe_injective hab.1
    · exact PNat.coe_injective hab.2
  refine ⟨{
    State := StateOf n
    fin := hSt
    deq := fun e => Classical.decEq _
    VType := VLabel n
    deqV := inferInstance
    finV := hVL
    vdeg := fun v => v.1.1 * v.1.2
    vEquiv := Equiv.refl _
    vdeg_spec := by intro v; simp [PNat.mul_coe]
    Out := fun _ τ => Σ m : (C.bd τ.1.1).Letter, (C.bd τ.1.1).Outc m
    finO := by
      intro e τ
      haveI := (C.bd τ.1.1).finL
      haveI := (C.bd τ.1.1).finO
      infer_instance
    odata := fun _ τ o =>
      { mem := ((C.bd τ.1.1).omem o.1 o.2).attach.map (fun x =>
          { size := x.1.size
            δ := x.1.δ
            status := match hs : x.1.status with
              | Sum.inl v => Sum.inl v
              | Sum.inr sk => Sum.inr
                  ⟨⟨sk, PUnit.unit⟩,
                    (C.bd τ.1.1).omem_size o.1 o.2 x.1 x.2 sk hs⟩ })
        hm := by
          have hne := (C.bd τ.1.1).omem_ne o.1 o.2
          intro hcontra
          apply hne
          simpa using hcontra }
    Wloc := fun _ _ _ => 0
    Wstate := fun _ _ => 0 }, ?_, ?_⟩
  · exact ⟨Equiv.refl _⟩
  · intro e τ o
    exact (MovesS.TableShape.odata _ e τ o).hm

end LeanUrat.MovesV
