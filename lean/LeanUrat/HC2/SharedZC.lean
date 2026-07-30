/-
LeanUrat.HC2.SharedZC  (HC-2 campaign — shared (ZC) per-coordinate assignment kernel)

The strip/value pin-attachment ASSIGNMENT KERNEL consumed by BOTH U7
(`freshAttach_exists`/`mkSigma_recursion_*`, U7_sigmaRec.lean) and U9 (the ⊇/interior
legs of `zc_root`, U9_zcRoot.lean): hoisted from the two byte-identical file-private
copies (C4 hoist, SYNTHESIS_PASS1_2026-07-30 + golf HC2#106; executed 2026-07-30,
BEFORE BP2 Block Z — whose U10 units prove "one level up from U9" and would otherwise
mint copy #3).  HOIST RECORD: all four lemmas below are VERBATIM hoists from
U7_sigmaRec.lean (the original; U9's copies were byte-identical modulo one deleted
comment) — statements unchanged, `private` dropped, no other edits.  Contents:
* `clause_assign` — a `LevelClause` with `codim = |support|` is a per-coordinate
  assignment on its support (`LevelClause.count` leaves exactly ONE supported
  satisfier; `dep` extends the characterization to all points);
* `card_fin_fun'` — `Nat.card (Fin k → ZMod p) = p ^ k` (the digit-alphabet count;
  Defs' `card_fin_fun` is `private` AND UPSTREAM of this file, so its copy stays —
  the two `choose`s agree by proof irrelevance, the U9a precedent);
* `valueClause_codim` — every constructed value clause has `codim = |support|`
  (`C1_TYP_toClause` at the level set's card);
* `mkFresh_codim` — every fresh clause of `mkFresh` has `codim = |support|`
  (strips: 1 = |{c}|; value clauses: `valueClause_codim`).
Together these feed `freshAttach_exists`'s `hasg` leg: every fresh clause pins its
whole support.  Exposure is namespace-fenced: everything lives under
`LeanUrat.MovesJ.SharedZC`; consuming units `open SharedZC`.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ.SharedZC
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- A clause whose codimension is its FULL support is a per-coordinate assignment:
`LevelClause.count` at `codim = |support|` forces a unique supported satisfier `u`, and
`dep` extends the characterization to all points. -/
lemma clause_assign {m : ℕ} (cl : LevelClause p m)
    (hcodim : cl.codim = cl.support.card) :
    ∃ u : Fin m → ZMod p, ∀ x : Fin m → ZMod p,
      cl.sat x ↔ ∀ c ∈ cl.support, x c = u c := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcount := cl.count
  rw [hcodim] at hcount
  have hone : Nat.card {y : Fin m → ZMod p // cl.sat y ∧ ∀ c ∉ cl.support, y c = 0} = 1 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos hp _) (by rw [hcount, one_mul])
  obtain ⟨y₀, hy₀⟩ := Nat.card_eq_one_iff_exists.mp hone
  refine ⟨y₀.1, fun x => ⟨fun hx c hc => ?_, fun hx => ?_⟩⟩
  · -- the support-restriction of x is a supported satisfier, hence IS y₀
    have hres : cl.sat (fun c' => if c' ∈ cl.support then x c' else 0) := by
      refine (cl.dep x _ ?_).mp hx
      intro c' hc'
      rw [if_pos hc']
    have hz : (⟨fun c' => if c' ∈ cl.support then x c' else 0, hres,
        fun c' hc' => if_neg hc'⟩ :
        {y : Fin m → ZMod p // cl.sat y ∧ ∀ c ∉ cl.support, y c = 0}) = y₀ := hy₀ _
    have hzc : (if c ∈ cl.support then x c else 0) = y₀.1 c :=
      congrFun (congrArg Subtype.val hz) c
    rw [if_pos hc] at hzc
    exact hzc
  · exact (cl.dep x y₀.1 fun c hc => hx c hc).mpr y₀.2.1

/-- `Nat.card` of a digit alphabet (Defs' private `card_fin_fun`, replicated — the two
`choose`s agree by proof irrelevance, the U9a precedent). -/
lemma card_fin_fun' (k : ℕ) : Nat.card (Fin k → ZMod p) = p ^ k := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- A constructed value clause has `codim = |support|` (`C1_TYP_toClause` at the level
set's card; support = the level set). -/
lemma valueClause_codim {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) (j : ℕ) (hsp : (H.nodes[i]'hi).spanSlot j) :
    (valueClause H n N S vOf i hi j hsp).codim
      = (valueClause H n N S vOf i hi j hsp).support.card := by
  classical
  have h := (C1_TYP_toClause
    (S.typObj i hi (levelSet H n N i (H.nodes[i]'hi) j)
      ⟨j, hsp, fun c => Iff.intro
        (fun hc => (Finset.mem_filter.mp hc).2)
        (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩)
    (vOf i j (levelSet H n N i (H.nodes[i]'hi) j))
    (levelSet H n N i (H.nodes[i]'hi) j).card
    (card_fin_fun' _)).choose_spec
  exact h.2.1.trans (congrArg Finset.card h.1).symm

/-- Every fresh clause of `mkFresh` has `codim = |support|`. -/
lemma mkFresh_codim {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ cl ∈ (mkFresh H n N S vOf i hi).clauses, cl.codim = cl.support.card := by
  intro cl hcl
  have hcl' : cl ∈ ((stripSet H n N i (H.nodes[i]'hi)).toList.map
        (fun c => (C1_stripClause (p := p) c).choose))
      ++ ((valueSlots H n N i (H.nodes[i]'hi)).attach.toList.map
        (fun jh => valueClause H n N S vOf i hi jh.1 (valueSlots_spanSlot jh.2))) := hcl
  rcases List.mem_append.mp hcl' with hstrip | hval
  · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hstrip
    have h := (C1_stripClause (p := p) c).choose_spec
    rw [h.2.1, h.1, Finset.card_singleton]
  · obtain ⟨jh, -, rfl⟩ := List.mem_map.mp hval
    exact valueClause_codim S vOf i hi jh.1 (valueSlots_spanSlot jh.2)

end LeanUrat.MovesJ.SharedZC
