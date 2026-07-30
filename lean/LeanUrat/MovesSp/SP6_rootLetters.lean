/-
Unit Sp.n3rootLetters [REV 2, F16 — ONE statement, the membership equivalence
the note asserts; multiplicity content carried by n3card53's Nodup, so duplicate
enum candidates (repeated equal λ-factors in the generator) are harmless] —
moves_ref: "GROUP R — ROOT, stage (D, w, W) = (1, 1, 3): 21 letters." + "per
stage, the (G1)–(G6)+(B1)–(B5corrected) letters are exactly the displayed rows".
deps: Sp.speciesEnumComplete, Sp.reflSucc (rootAdmissibleB_iff). sketch: (→)
RootAdmissible ⇒ Coherent ∧ Budget ⇒ s ∈ speciesEnum 3 (enumComplete), then
root3_enum_check reads off membership; (←) groupR_admissible + the reflection
iff. difficulty: medium (perf).

PERF NOTE (Fable): `speciesEnum` is well-founded-recursive (`compEnum`/`lamEnumAux`
carry `decreasing_by`), so its kernel unfolding is `unseal`ed for the enum `decide`.
The enum emits each `lam` multiset in the generator's canonical (ascending pair-index)
order, whereas `groupR`'s hand-written rows list some multisets in a different order
(e.g. R6's `{(1,2),(1,1)}`). Deciding that a reordered `Multiset` field is EQUAL
inside the AUTO-DERIVED `DecidableEq Species` does not kernel-reduce (a known
`deriving DecidableEq` × `Quotient` stall — the standalone `Multiset.decidableEq`
reduces fine, but the derived structure eq does not), which stalls `groupR.contains s`
for those elements. The membership test is therefore routed through the field-wise
Bool comparator `beqFast` (proved equal to the derived `==`), which DOES reduce; the
statement is unchanged. No `native_decide` (axiom fence).
-/
import LeanUrat.MovesSp.DefsN3
import LeanUrat.MovesSp.SP0_reflSucc
import LeanUrat.MovesSp.SP2_speciesEnum

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace LeanUrat.MovesSp

/-- Field-wise Bool equality on `Species`. Each field compares via a top-level
`decide (a.f = b.f)`; in particular the `Multiset` field `lam` goes through
`Multiset.decidableEq` DIRECTLY, which kernel-reduces even on reordered multisets —
unlike the auto-derived `DecidableEq Species`, which stalls in that case. -/
def beqFast (a b : Species) : Bool :=
  decide (a.tag = b.tag) && decide (a.D = b.D) && decide (a.w = b.w) && decide (a.W = b.W) &&
  decide (a.e = b.e) && decide (a.s0 = b.s0) && decide (a.ell = b.ell) && decide (a.a = b.a) &&
  decide (a.d = b.d) && decide (a.slots = b.slots) && decide (a.lam = b.lam) &&
  decide (a.sel = b.sel) && decide (a.lflank = b.lflank) && decide (a.rflank = b.rflank)

/-- Soundness of `beqFast`: it is `true` exactly on equal species. -/
theorem beqFast_iff (a b : Species) : beqFast a b = true ↔ a = b := by
  unfold beqFast
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩
    cases a; cases b; simp_all
  · rintro rfl; simp

/-- `beqFast` agrees with the derived `BEq`/`==` on `Species`, as Bools. -/
theorem beqFast_eq_beq (a b : Species) : beqFast a b = (a == b) := by
  rw [show (a == b) = decide (a = b) from rfl]
  rcases hb : beqFast a b with _ | _
  · simp only [Bool.false_eq]
    rw [decide_eq_false_iff_not]
    intro h; rw [← beqFast_iff] at h; rw [h] at hb; exact absurd hb (by simp)
  · symm; rw [decide_eq_true_eq]; rw [← beqFast_iff]; exact hb

-- decide fact 1 [REV 4, Codex-6].
unseal compEnum lamEnumAux in
theorem root3_enum_check : ((speciesEnum 3).all fun s =>
    rootAdmissibleB 3 s == groupR.contains s) = true := by
  have hrw : ∀ s : Species, groupR.contains s = groupR.any (fun g => beqFast s g) := by
    intro s
    simp only [beqFast_eq_beq]
    rfl
  simp only [hrw]
  decide

/-- decide fact 2. -/
theorem groupR_admissible : (groupR.all (rootAdmissibleB 3)) = true := by decide

theorem rootAdmissible3_iff (s : Species) :
    RootAdmissible 3 s ↔ s ∈ groupR := by
  constructor
  · intro h
    have hmem : s ∈ speciesEnum 3 := speciesEnum_complete h.2.1 h.2.2
    have hcheck := (List.all_eq_true.mp root3_enum_check) s hmem
    rw [beq_iff_eq] at hcheck
    have hrb : rootAdmissibleB 3 s = true := (rootAdmissibleB_iff 3 s).mpr h
    rw [hrb] at hcheck
    exact List.mem_of_elem_eq_true hcheck.symm
  · intro h
    have hrb : rootAdmissibleB 3 s = true := (List.all_eq_true.mp groupR_admissible) s h
    exact (rootAdmissibleB_iff 3 s).mp hrb

end LeanUrat.MovesSp
