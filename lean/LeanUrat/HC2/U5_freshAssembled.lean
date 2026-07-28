/-
Unit U5.mkFresh_assembled  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC round-5 header "exact geometric fresh-clause identification";
`JetSetup.fresh_assembled` field type, verbatim at `mkFresh`.
deps: D6, C1.TYP_toClause (PROVED), IsValueSupport.  difficulty: medium (iff bookkeeping).
hypothesis_fields: the emitted values `vOf` (R4.B.2 boundary — free parameters here).
RESTATED-POST-DEFS-REPAIR (2026-07-27): statement stands on the REPAIRED ZCSeedLaws.downsets_literal (chart-coverage guard added; box-truncation refuted by scratch_U9_presentSeed_false — blueprint §2.2 DC-1). Sorries retained for the next fleet round.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- Local re-proof of `Defs.card_fin_fun` (that one is `private`): the digit alphabet
`Fin k → ZMod p` has `Nat.card = p ^ k`. Only used to feed `C1_TYP_toClause`'s `hcard`
argument, which is a `Prop` — so by proof irrelevance the resulting `.choose` coincides
(definitionally) with the one baked into `valueClause`. -/
private lemma card_fin_fun' (p k : ℕ) [Fact p.Prime] :
    Nat.card (Fin k → ZMod p) = p ^ k := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- The three `Exists.choose_spec` facts of `valueClause`, stated syntactically about
`valueClause` (so downstream `rw`s can fire). The `C1_TYP_toClause` term differs from the one
inside `valueClause`'s definition only in the `hcard` proof, an irrelevant `Prop` argument, so
`Classical.choose` — hence every projection below — agrees definitionally; `exact` discharges
it by defeq. -/
private lemma valueClause_spec {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) (j : ℕ) (hsp : (H.nodes[i]'hi).spanSlot j) :
    (valueClause H n N S vOf i hi j hsp).support = levelSet H n N i (H.nodes[i]'hi) j ∧
    (valueClause H n N S vOf i hi j hsp).codim = (levelSet H n N i (H.nodes[i]'hi) j).card ∧
    ∀ x, (valueClause H n N S vOf i hi j hsp).sat x ↔
      (S.typObj i hi (levelSet H n N i (H.nodes[i]'hi) j)
        ⟨j, hsp, fun c => Iff.intro (fun hc => (Finset.mem_filter.mp hc).2)
          (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩).φ x
        = vOf i j (levelSet H n N i (H.nodes[i]'hi) j) := by
  have h := (C1_TYP_toClause
    (S.typObj i hi (levelSet H n N i (H.nodes[i]'hi) j)
      ⟨j, hsp, fun c => Iff.intro (fun hc => (Finset.mem_filter.mp hc).2)
        (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩)
    (vOf i j (levelSet H n N i (H.nodes[i]'hi) j))
    (levelSet H n N i (H.nodes[i]'hi) j).card (card_fin_fun' p _)).choose_spec
  exact h

/-- The VALUE branch of `fresh_assembled` for a single rostered value clause: its support IS a
recorded span slot's exact-valuation level set (`IsValueSupport`), its codimension equals the
support cardinality, and its constraint is the seed's `TypObject` surjection at the emitted
value. -/
private lemma valueClause_isValue {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) (j : ℕ) (hsp : (H.nodes[i]'hi).spanSlot j) :
    IsValueSupport H (boxChart n N) i (H.nodes[i]'hi)
        (valueClause H n N S vOf i hi j hsp).support ∧
      (valueClause H n N S vOf i hi j hsp).codim =
        (valueClause H n N S vOf i hi j hsp).support.card ∧
      ∃ (T : TypObject p (n * N) (valueClause H n N S vOf i hi j hsp).support
            (Fin (valueClause H n N S vOf i hi j hsp).codim → ZMod p))
          (v : Fin (valueClause H n N S vOf i hi j hsp).codim → ZMod p),
        ∀ x, ((valueClause H n N S vOf i hi j hsp).sat x ↔ T.φ x = v) := by
  obtain ⟨hsupp, hcodim, hsat⟩ := valueClause_spec H n N S vOf i hi j hsp
  refine ⟨?_, ?_, ?_⟩
  · -- IsValueSupport: the support is levelSet j, whose membership IS the value-position law
    rw [hsupp]
    exact ⟨j, hsp, fun c => Iff.intro (fun hc => (Finset.mem_filter.mp hc).2)
      (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩
  · -- codim = support.card
    rw [hcodim, hsupp]
  · -- the TypObject/value witnesses
    rw [hsupp, hcodim]
    exact ⟨S.typObj i hi (levelSet H n N i (H.nodes[i]'hi) j)
        ⟨j, hsp, fun c => Iff.intro (fun hc => (Finset.mem_filter.mp hc).2)
          (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩,
      vOf i j (levelSet H n N i (H.nodes[i]'hi) j), hsat⟩

/-- The `fresh_assembled` disjunction for `mkFresh` — strips carry the ¬IsValueCoord tag
from their roster; value clauses carry `IsValueSupport`, `codim = card`, and the
TypObject/`v` witnesses of D6's own data. -/
theorem mkFresh_assembled {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ cl ∈ (mkFresh H n N S vOf i hi).clauses,
      (∃ c : Fin (n * N), cl.support = {c} ∧ cl.codim = 1 ∧
        (∀ x, (cl.sat x ↔ x c = 0)) ∧
        ¬ IsValueCoord H (boxChart n N) i (H.nodes[i]'hi) c) ∨
      (IsValueSupport H (boxChart n N) i (H.nodes[i]'hi) cl.support ∧
        cl.codim = cl.support.card ∧
        ∃ (T : TypObject p (n * N) cl.support (Fin cl.codim → ZMod p))
          (v : Fin cl.codim → ZMod p), ∀ x, (cl.sat x ↔ T.φ x = v)) := by
  classical
  intro cl hcl
  -- `(mkFresh …).clauses` is definitionally `mkFreshClauses …`
  have hcl2 : cl ∈ mkFreshClauses H n N S vOf i hi := hcl
  unfold mkFreshClauses at hcl2
  rw [List.mem_append] at hcl2
  rcases hcl2 with hstrip | hvalue
  · -- STRIP clause: `(C1_stripClause c).choose` at a non-value band coordinate `c`
    rw [List.mem_map] at hstrip
    obtain ⟨c, hc, hceq⟩ := hstrip
    rw [Finset.mem_toList] at hc
    unfold stripSet at hc
    rw [Finset.mem_filter] at hc
    obtain ⟨-, -, hnval⟩ := hc
    obtain ⟨hs, hcod, hsat⟩ := (C1_stripClause (p := p) c).choose_spec
    subst hceq
    exact Or.inl ⟨c, hs, hcod, hsat, hnval⟩
  · -- VALUE clause: `valueClause …` at a rostered span slot `jh.1`
    rw [List.mem_map] at hvalue
    obtain ⟨jh, -, hjeq⟩ := hvalue
    subst hjeq
    exact Or.inr (valueClause_isValue H n N S vOf i hi jh.1 (valueSlots_spanSlot jh.2))

end LeanUrat.MovesJ
