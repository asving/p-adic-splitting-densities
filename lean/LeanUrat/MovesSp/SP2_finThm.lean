/-
Unit Sp.finThm — moves_ref: "Theorem SP-FIN. 𝒮_n^raw is FINITE and INDEPENDENT
of p, with the explicit (crude) bound |𝒮_n^raw| ≤ (n+2)^{n² + 3n + 12}."
deps: Sp.memCoherent, Sp.encodeInj, Sp.encodeCard. sketch: SnRaw ⊆ the coherent-
admissible set; encode injective there; `Set.Finite.of_finite_image`/
`Nat.card_le_card_of_injective`.
p-INDEPENDENCE: discharged BY TYPING (blueprint §0) — `SnRaw : ℕ → Set Species`
mentions no prime ("no field of the datum ... mentions p — the same list serves
every prime"); recorded here as the faithfulness witness, no clause.
difficulty: medium.
-/
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesSp.SP0_memCoherent   -- dep Sp.memCoherent: InCatalogue.coherent_budget
import LeanUrat.MovesSp.SP2_encodeInj     -- dep Sp.encodeInj: encode, encode_inj
import LeanUrat.MovesSp.SP2_encodeCard    -- dep Sp.encodeCard: code_card

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

/-- p-INDEPENDENCE is discharged BY TYPING (blueprint §0): `SnRaw : ℕ → Set Species`
mentions no prime — the same catalogue serves every prime — so the theorem is stated
for the single p-free list and carries no explicit p-clause. -/
theorem SP_FIN (n : ℕ) (hn : 1 ≤ n) : (SnRaw n).Finite ∧
    Nat.card (SnRaw n) ≤ (n+2)^(n^2 + 3*n + 12) := by
  -- `Code n = Fin (n²+3n+12) → Fin (n+2)` is a finite type.
  haveI hfin : Finite (Code n) := by unfold Code; infer_instance
  -- The SP-FIN encoding is injective on catalogue members (each is coherent and
  -- budget-admissible via `InCatalogue.coherent_budget`), so it injects `SnRaw n`
  -- into the finite code type.
  have hinj : Function.Injective (fun s : SnRaw n => encode n hn s.val) := by
    rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    exact Subtype.ext
      (encode_inj (InCatalogue.coherent_budget hs) (InCatalogue.coherent_budget hs') h)
  refine ⟨Set.finite_coe_iff.mp (Finite.of_injective _ hinj), ?_⟩
  calc Nat.card (SnRaw n)
      ≤ Nat.card (Code n) := Nat.card_le_card_of_injective _ hinj
    _ = (n+2)^(n^2 + 3*n + 12) := code_card n

end LeanUrat.MovesSp
