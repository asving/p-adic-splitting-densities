/-
Unit Sp.fullUnique — moves_ref: "(i) At each fixed (tag, D, w, W) there is AT
MOST ONE full letter … every field determined."
deps: Sp.fullForcing. sketch: Species.ext; every remaining field pinned by
full_forces + (G2)/(G3) + sel = some (1, W). difficulty: easy.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP4_fullForcing   -- dep Sp.fullForcing: full_forces

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem full_unique {n} {s s' : Species} (hcs : Coherent s)
    (hbs : Budget n s) (hcs' : Coherent s') (hbs' : Budget n s') (hf : IsFull s)
    (hf' : IsFull s') (htag : s.tag = s'.tag) (hD : s.D = s'.D) (hw : s.w = s'.w)
    (hW : s.W = s'.W) : s = s' := by
  -- full_forces pins every remaining field of each full letter to (D, w, W).
  obtain ⟨he, hell, ha, hs0, hlam, hlf, hrf, hslots⟩ := full_forces hcs hbs hf
  obtain ⟨he', hell', ha', hs0', hlam', hlf', hrf', hslots'⟩ := full_forces hcs' hbs' hf'
  -- (G3) pins d = ℓ + 1; IsFull pins sel = (1, W).
  have hd : s.d = s.ell + 1 := hcs.2.2.2.1.2
  have hd' : s'.d = s'.ell + 1 := hcs'.2.2.2.1.2
  have hf1 : s.sel = some (1, s.W) := hf
  have hf1' : s'.sel = some (1, s'.W) := hf'
  -- Field-by-field equalities, all mediated by hW.
  have heE : s.e = s'.e := by rw [he, he']
  have hs0E : s.s0 = s'.s0 := by rw [hs0, hs0']
  have haE : s.a = s'.a := by rw [ha, ha']
  have hellE : s.ell = s'.ell := by rw [hell, hell', hW]
  have hdE : s.d = s'.d := by rw [hd, hd', hellE]
  have hslotsE : s.slots = s'.slots := by rw [hslots, hslots', hW]
  have hlamE : s.lam = s'.lam := by rw [hlam, hlam', hW]
  have hselE : s.sel = s'.sel := by rw [hf1, hf1', hW]
  have hlfE : s.lflank = s'.lflank := by rw [hlf, hlf']
  have hrfE : s.rflank = s'.rflank := by rw [hrf, hrf']
  cases s
  cases s'
  simp only [Species.mk.injEq]
  exact ⟨htag, hD, hw, hW, heE, hs0E, hellE, haE, hdE, hslotsE, hlamE, hselE, hlfE, hrfE⟩

end LeanUrat.MovesSp
