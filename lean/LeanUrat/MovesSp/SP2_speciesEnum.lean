/-
Unit Sp.speciesEnumComplete — moves_ref: "𝒮_n^raw injects into the encoded set
((G1)–(G6) only shrink it)" [here: the generated candidate list].
deps: Sp.compEnumComplete, Sp.lamEnumComplete. sketch: coherence pins a/d/slots
from (s0, e, ℓ) ((G2)/(G3)); budget pins every generator range ((B1)–(B5));
membership by product-list mem lemmas. difficulty: medium-hard.
-/
import LeanUrat.MovesSp.DefsEnum
import LeanUrat.MovesSp.SP2_compEnum
import LeanUrat.MovesSp.SP2_lamEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem speciesEnum_complete {n : ℕ} {s : Species} (hc : Coherent s)
    (hb : Budget n s) : s ∈ speciesEnum n := by
  obtain ⟨tag, D, w, W, e, s0, ell, a, d, slots, lam, sel, lflank, rflank⟩ := s
  simp only [Coherent, WellTyped, IsComposition, Species.wraw] at hc
  simp only [Budget, Species.wraw] at hb
  obtain ⟨⟨hD1, hw1, hW1, he1, hell1, hlampos⟩,
          ⟨⟨hlfpos, hlfsum⟩, hspan, hrfpos⟩, hG2, ⟨hslots, hd⟩,
          ⟨hG4sum, hG4sel⟩, hG6⟩ := hc
  obtain ⟨hDn, hwn, ⟨hB3a, hB3b, hB3c, hWdiv⟩, hB4,
          hen, helln, hs0n, hdn, hWn, hlambd, heraw, haraw⟩ := hb
  obtain ⟨D0, rfl⟩ : ∃ D0, D = D0 + 1 := ⟨D - 1, by omega⟩
  obtain ⟨w0, rfl⟩ : ∃ w0, w = w0 + 1 := ⟨w - 1, by omega⟩
  obtain ⟨W0, rfl⟩ : ∃ W0, W = W0 + 1 := ⟨W - 1, by omega⟩
  obtain ⟨e0, rfl⟩ : ∃ e0, e = e0 + 1 := ⟨e - 1, by omega⟩
  obtain ⟨ell0, rfl⟩ : ∃ ell0, ell = ell0 + 1 := ⟨ell - 1, by omega⟩
  subst hG2 hslots hd
  -- (G4) + (B5): `lam` is realized by a canonical sorted list `lamL` in the enum's aux list.
  have hlam_mem : lam ∈ lamEnum n (ell0 + 1) := (lamEnum_complete hlampos hlambd).mp hG4sum
  simp only [lamEnum, List.map_id', List.mem_flatMap, List.mem_singleton,
    List.bind_eq_flatMap, List.pure_def] at hlam_mem
  obtain ⟨lamL, hlamL_mem, hlamL_eq0⟩ := hlam_mem
  have hlamL_eq := hlamL_eq0.symm
  -- Thread membership through the eleven nested binders of `speciesEnum`.
  simp only [speciesEnum, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons]
  refine ⟨tag, ?_, D0, ?_, w0, ?_, W0, ?_, e0, ?_, ell0, ?_, s0, ?_, lamL, hlamL_mem,
    sel, ?_, lflank, ?_, rflank, ?_, ?_⟩
  · cases tag <;> simp
  · omega
  · omega
  · omega
  · omega
  · -- ℓ ≤ W / e  ((B3): e·ℓ = w′ ≤ W)
    have key : (e0 + 1) * (ell0 + 1) ≤ W0 + 1 := by omega
    have hle : ell0 + 1 ≤ (W0 + 1) / (e0 + 1) := by
      rw [Nat.le_div_iff_mul_le (Nat.succ_pos e0), Nat.mul_comm]
      exact key
    omega
  · omega
  · -- selection ∈ {⊥} ∪ (some '' λ)
    rcases eq_or_ne sel none with h | h
    · exact Or.inl h
    · obtain ⟨gm, hgm⟩ := Option.ne_none_iff_exists'.mp h
      refine Or.inr ⟨gm, ?_, hgm.symm⟩
      have hmem : gm ∈ lam := hG4sel gm hgm
      rw [← hlamL_eq] at hmem
      exact Multiset.mem_coe.mp hmem
  · -- left flank is a composition of s₀′  ((G1))
    exact compEnum_complete.mp ⟨hlfpos, hlfsum⟩
  · -- right flank is a composition of W − s₀′ − w′  ((G1))
    refine compEnum_complete.mp ⟨hrfpos, ?_⟩
    omega
  · -- the built node equals `s`: only the `lam` field needs the list→multiset bridge
    rw [hlamL_eq]

end LeanUrat.MovesSp
