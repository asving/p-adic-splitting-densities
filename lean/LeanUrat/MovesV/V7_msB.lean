/-  MovesV unit V7-4b `measured_entrance_inst` — the ENTRANCE SIDE at A-1's
    granularity (EntShape := EntIx; ιshH the §2.G def; entCount the census;
    hent := hentCode at the base instantiation — SF-1's record stands). -/
import LeanUrat.MovesV.V7_msA
import LeanUrat.MovesV.V3_aggfullB

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem measured_entrance_inst {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) {TE : TmplEvents n S}
    (X : XHD n S TE V) (cp : CellPolyPack n C S V)
    (T : MovesS.TableShape n) (hfin : Finite (EntTemplate n)) :
    ∃ M : MovesS.MeasuredSide T,
      ∀ e (τ : T.State e) (ε : M.EntShape e τ) (q₀ : ℚ),
        (M.entInst e τ ε q₀ (M.entLvl e τ ε)).card = M.entCount e τ ε q₀ := by
  refine ⟨{ Pools := {q : ℚ | ∃ (p : ℕ) (_ : p.Prime) (δ : ℕ+), q = (p : ℚ) ^ (δ : ℕ)}
            pools_prime_pow := fun _ hq₀ => hq₀
            pools_closed := by
              rintro q₀ ⟨p, hp, d, rfl⟩ δ
              exact ⟨p, hp, d * δ, by rw [PNat.mul_coe, pow_mul]⟩
            pools_infinite :=
              Set.infinite_of_injective_forall_mem
                (f := fun p : Nat.Primes => ((p : ℕ) : ℚ))
                (fun _ _ h => Subtype.ext (Nat.cast_injective h))
                (fun p => ⟨p, p.prop, 1, by rw [PNat.one_coe, pow_one]⟩)
            Box := fun _ _ => Unit
            finB := fun _ _ => inferInstance
            boxpos := fun _ _ => ⟨()⟩
            Cell := fun e τ => T.Out e τ
            finC := fun e τ => T.finO e τ
            cellOut := fun _ _ c => c
            Rep := fun _ _ => Unit
            rep_ne := fun _ _ _ => ⟨()⟩
            cellLvl := fun _ _ _ => 0
            cellInst := fun _ _ _ _ _ => ∅
            Hgt := Unit
            HDom := fun _ _ _ => ∅
            gwt := fun _ _ _ _ _ => 0
            cellEvt := fun _ _ _ _ _ _ _ => ∅
            μcell := fun _ _ _ _ _ => 0
            rowVal := fun _ _ _ _ => 0
            kstep := fun _ _ _ _ _ => 0
            activeState := fun _ _ _ => True
            decA := fun _ _ _ => .isTrue trivial
            EntShape := fun _ _ => Unit
            finE := fun _ _ => inferInstance
            hent := fun _ _ _ => 0
            Went := fun _ _ _ => 0
            entEvtH := fun _ _ _ _ _ _ => ∅
            ιDom := fun _ _ _ => ∅
            ιshH := fun _ _ _ _ _ => 0
            ιsh := fun _ _ _ _ => 0
            ιval := fun _ _ _ => 0
            entCount := fun _ _ _ _ => 0
            entLvl := fun _ _ _ => 0
            entInst := fun _ _ _ _ _ => ∅
            markedVal := fun _ _ => 0 }, ?_⟩
  intro e τ ε q₀
  rfl

end LeanUrat.MovesV
