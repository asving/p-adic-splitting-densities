/-  MovesV unit V7-3a `tableShape_inst` (odata CONSTRUCTIBLE REV 5, Codex-2;
    M1 PIN STRENGTHENING at the round-4 ratification verdict, 2026-07-29) —
    the `MovesS.TableShape n` instance from `CtsFamily`, with the named
    TABLE-SIDE PIN BUNDLE `TablePins` proved at the witness.
    ROUND-4 M1 REPAIR (option (a), table side — the verdict: "the supposedly
    pinned carrier … omits the required CTS `CellIdx`" / "`tableShape_inst`
    still installs `Wloc := 0`, `Wstate := 0`"):
    (i) `StateOf` now CARRIES the CTS cell index — the carrier is
        `{p : Σ s, (C.bd s).CellIdx // skBlk p.1 = e}`, the block-e slice of
        the CTS step-cell carrier (`CtsMeasured.toStepCells`' codomain);
    (ii) the witness installs the REAL bounds `Wloc := C.Wloc`,
        `Wstate := (C.bd s).Wstate` (the CTS degree-bound data);
    (iii) the conclusion is the named `TablePins C T`: VType/State equivs +
        Wstate/Wloc transport + the per-outcome odata member-list tie in
        (size, δ, status-with-target-skeleton) through the equivs.
    NOT tied by `TablePins` (honest inventory, boundary-record rule): the
    target CELL INDEX inside a continuing member's status payload (a
    dependent-type equality across `hst`; the witness's index is the
    `tcellM`-transported one via `memberTgtCell`), the `odata.hm` proof
    (proof-irrelevant), and `vdeg`/`vEquiv` (law-pinned by `TableShape`'s own
    `vdeg_spec` at the pinned `VType`). -/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesV.V2_cells

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1600000

namespace LeanUrat.MovesV

/-- the block-e CTS state carrier — M1-STRENGTHENED (round 4): the pair
(skeleton, CTS cell index) with block size e; the block-e slice of the CTS
step-cell carrier `Σ s, (C.bd s).CellIdx`. -/
def StateOf (n : ℕ) (C : CtsFamily n) (e : ℕ) : Type :=
  {p : Σ s : Skeleton n, (C.bd s).CellIdx // skBlk p.1 = e}

/-- a continuing roster member's TARGET CELL INDEX, read through `tcellM` at
a roster position realizing the member (choice over `List.mem_iff_get`) from
the source cell index `α`. -/
noncomputable def memberTgtCell {n : ℕ} (C : CtsFamily n) {s : Skeleton n}
    {m : (C.bd s).Letter} {o : (C.bd s).Outc m} (α : (C.bd s).CellIdx)
    (mu : OMember n) (hmem : mu ∈ (C.bd s).omem m o) {sk : Skeleton n}
    (hs : mu.status = Sum.inr sk) : (C.bd sk).CellIdx :=
  C.tcellM s m o (List.mem_iff_get.mp hmem).choose sk
    (by rw [(List.mem_iff_get.mp hmem).choose_spec]; exact hs) α

/-- M1 (round 4): THE TABLE-SIDE PIN BUNDLE — exactly the clauses tying a
`TableShape` witness to the CTS family `C`, no more and no less:
(1) `VType ≃ VLabel n`; (2) per-block `State e ≃ StateOf n C e` (the
CellIdx-carrying CTS carrier); (3) `Wstate` transports the block bound;
(4) per (e, τ): `Out ≃ Σ letter, outcome` over τ's skeleton, `Wloc`
transports `C.Wloc`, and the odata member list equals the CTS `omem` roster
in (size, δ, status) — statuses compared after projecting a continuing
member's table-side state payload to its SKELETON (its cell-index component
is NOT tied here; see the file header's inventory). -/
def TablePins {n : ℕ} (C : CtsFamily n) (T : MovesS.TableShape n) : Prop :=
  ∃ (hv : T.VType ≃ VLabel n) (hst : ∀ e, T.State e ≃ StateOf n C e),
    (∀ e (τ : T.State e), T.Wstate e τ = (C.bd ((hst e) τ).1.1).Wstate) ∧
    (∀ e (τ : T.State e),
      ∃ hout : T.Out e τ ≃ Σ m : (C.bd ((hst e) τ).1.1).Letter,
          (C.bd ((hst e) τ).1.1).Outc m,
        (∀ o : T.Out e τ, T.Wloc e τ o = C.Wloc ((hst e) τ).1.1 (hout o).1) ∧
        (∀ o : T.Out e τ,
          (T.odata e τ o).mem.map (fun μ =>
              (μ.size, μ.δ, Sum.map hv (fun σ => ((hst μ.size) σ).1.1) μ.status))
            = ((C.bd ((hst e) τ).1.1).omem (hout o).1 (hout o).2).map
                (fun mu => (mu.size, mu.δ, mu.status))))

theorem tableShape_inst {n : ℕ} (C : CtsFamily n)
    (hfin : Finite (Skeleton n)) :
    ∃ T : MovesS.TableShape n,
      TablePins C T ∧
      ∀ e (τ : T.State e) (o : T.Out e τ), (T.odata e τ o).mem ≠ [] := by
  classical
  haveI := hfin
  -- Fintype on the state carrier (finite skeletons ⟹ finite block-e cells).
  haveI hSt : ∀ e, Fintype (StateOf n C e) := by
    intro e
    have : Finite (StateOf n C e) := by unfold StateOf; infer_instance
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
    State := StateOf n C
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
                  ⟨⟨sk, memberTgtCell C τ.1.2 x.1 x.2 hs⟩,
                    (C.bd τ.1.1).omem_size o.1 o.2 x.1 x.2 sk hs⟩ })
        hm := by
          have hne := (C.bd τ.1.1).omem_ne o.1 o.2
          intro hcontra
          apply hne
          simpa using hcontra }
    Wloc := fun _ τ o => C.Wloc τ.1.1 o.1
    Wstate := fun _ τ => (C.bd τ.1.1).Wstate }, ?_, ?_⟩
  · -- TablePins at the literal witness: every equiv is `Equiv.refl`, the
    -- weight ties are `rfl`, the odata tie computes through the attach map.
    refine ⟨Equiv.refl _, fun e => Equiv.refl _, fun e τ => rfl,
      fun e τ => ⟨Equiv.refl _, fun o => rfl, fun o => ?_⟩⟩
    simp only [Equiv.coe_refl, id_eq]
    show (((C.bd τ.1.1).omem o.1 o.2).attach.map _).map _ = _
    rw [List.map_map]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_attach]; rfl
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_attach, Function.comp_apply]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      -- the status component: cases on the roster member's status
      split
      · next v heq => simp only [Sum.map_inl, id_eq]; exact heq.symm
      · next sk heq => simp only [Sum.map_inr]; exact heq.symm
  · intro e τ o
    exact (MovesS.TableShape.odata _ e τ o).hm

end LeanUrat.MovesV
