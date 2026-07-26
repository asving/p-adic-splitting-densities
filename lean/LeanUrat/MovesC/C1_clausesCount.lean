/-
Unit C1.clausesCount  (MovesC, layer 1; deps: none)
moves_ref: §C.1.5'(1) "pairwise disjoint: the factors multiply" — the joint fresh cut on the full box

The multi-clause fresh-count engine consumed by C4.conditionalMass.  A `FreshData` is a
finite list of `LevelClause`s with pairwise-disjoint supports; each clause `cl` cuts EXACTLY
codimension `cl.codim` on its support (its division-free `count` law).  Because the supports
are disjoint the factors multiply, giving `#{x | fd.sat x} · p^{Σ codim} = p^m`.

Proof shape (bottom-up):
* `card_supported_eq`  — #{functions supported on `S`} = p^|S|.
* `card_split`         — for an `S`-measurable `f` and an `Sᶜ`-measurable `g`, the joint count
                          factors through the product decomposition on `S` / `Sᶜ`.
* `card_split_right`   — the `f = True` specialisation: #{g} = p^|S| · #{g, zero on S}.
* `crux`               — one clause: #{cl.sat ∧ R} · p^codim = #{R} for `Sᶜ`-measurable `R`
                          (`card_split` + `card_split_right` + the clause `count` law).
* `list_count`         — induction on the clause list; the head clause's `crux` peels one
                          factor, the tail's disjointness makes the tail predicate
                          `cl.supportᶜ`-measurable.

Works for every `p : ℕ` (incl. p = 0, 1) via `Nat.card`: the `count` law is self-policing.
Trusted base is Lean core only (no axioms beyond propext/Classical.choice/Quot.sound).
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false

namespace LeanUrat.MovesC

variable {p : ℕ}

/-- Number of functions `Fin m → ZMod p` supported on `S` is `p ^ |S|` (valid for all `p`). -/
private theorem card_supported_eq {m : ℕ} (S : Finset (Fin m)) :
    Nat.card {x : Fin m → ZMod p // ∀ c ∉ S, x c = 0} = p ^ S.card := by
  classical
  have e : {x : Fin m → ZMod p // ∀ c ∉ S, x c = 0} ≃ (S → ZMod p) :=
  { toFun := fun x i => x.1 i
    invFun := fun g => ⟨fun i => if h : i ∈ S then g ⟨i, h⟩ else 0, by intro c hc; simp [hc]⟩
    left_inv := by
      rintro ⟨x, hx⟩; apply Subtype.ext; funext i
      by_cases h : i ∈ S
      · simp [h]
      · simp [h, hx i h]
    right_inv := by intro g; funext i; simp [i.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_finsetCard]

/-- Product decomposition of the joint count: if `f` reads only `S` and `g` reads only `Sᶜ`,
the count of `{f ∧ g}` factors as (count of `f`, zero off `S`) · (count of `g`, zero on `S`). -/
private theorem card_split {m : ℕ} (S : Finset (Fin m)) (f g : (Fin m → ZMod p) → Prop)
    (hf : ∀ x y : Fin m → ZMod p, (∀ c ∈ S, x c = y c) → (f x ↔ f y))
    (hg : ∀ x y : Fin m → ZMod p, (∀ c ∉ S, x c = y c) → (g x ↔ g y)) :
    Nat.card {x : Fin m → ZMod p // f x ∧ g x}
      = Nat.card {x : Fin m → ZMod p // f x ∧ ∀ c ∉ S, x c = 0}
        * Nat.card {x : Fin m → ZMod p // g x ∧ ∀ c ∈ S, x c = 0} := by
  classical
  rw [← Nat.card_prod]
  refine Nat.card_congr {
    toFun := fun x =>
      (⟨fun i => if i ∈ S then x.1 i else 0, by
          refine ⟨(hf _ x.1 (by intro c hc; simp [hc])).mpr x.2.1, ?_⟩
          intro c hc; simp [hc]⟩,
       ⟨fun i => if i ∈ S then 0 else x.1 i, by
          refine ⟨(hg _ x.1 (by intro c hc; simp [hc])).mpr x.2.2, ?_⟩
          intro c hc; simp [hc]⟩)
    invFun := fun ab =>
      ⟨fun i => if i ∈ S then ab.1.1 i else ab.2.1 i, by
          refine ⟨(hf _ ab.1.1 (by intro c hc; simp [hc])).mpr ab.1.2.1,
                  (hg _ ab.2.1 (by intro c hc; simp [hc])).mpr ab.2.2.1⟩⟩
    left_inv := by
      rintro ⟨x, hx⟩; apply Subtype.ext; funext i
      by_cases h : i ∈ S <;> simp [h]
    right_inv := by
      rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · funext i; by_cases h : i ∈ S
        · simp [h]
        · simp [h, ha.2 i h]
      · funext i; by_cases h : i ∈ S
        · simp [h, hb.2 i h]
        · simp [h] }

/-- The `f = True` specialisation of `card_split`: an `Sᶜ`-measurable predicate's count is
`p^|S|` times its count among the functions vanishing on `S`. -/
private theorem card_split_right {m : ℕ} (S : Finset (Fin m)) (R : (Fin m → ZMod p) → Prop)
    (hR : ∀ x y : Fin m → ZMod p, (∀ c ∉ S, x c = y c) → (R x ↔ R y)) :
    Nat.card {x : Fin m → ZMod p // R x}
      = p ^ S.card * Nat.card {x : Fin m → ZMod p // R x ∧ ∀ c ∈ S, x c = 0} := by
  have h := card_split (p := p) S (fun _ => True) R (fun _ _ _ => Iff.rfl) hR
  simp only [true_and] at h
  rw [card_supported_eq] at h
  exact h

/-- One clause peels a `p^codim` factor: for an `cl.supportᶜ`-measurable `R`,
`#{cl.sat ∧ R} · p^cl.codim = #{R}`.  Uses the two splits and the clause `count` law. -/
private theorem crux {m : ℕ} (cl : LevelClause p m) (R : (Fin m → ZMod p) → Prop)
    (hR : ∀ x y : Fin m → ZMod p, (∀ c ∉ cl.support, x c = y c) → (R x ↔ R y)) :
    Nat.card {x : Fin m → ZMod p // cl.sat x ∧ R x} * p ^ cl.codim
      = Nat.card {x : Fin m → ZMod p // R x} := by
  rw [card_split cl.support cl.sat R cl.dep hR, card_split_right cl.support R hR,
      mul_right_comm, cl.count]

/-- The clause-list engine: induction on the list; disjoint supports let the factors multiply. -/
private theorem list_count {m : ℕ} (L : List (LevelClause p m))
    (hdisj : L.Pairwise (fun c₁ c₂ => Disjoint c₁.support c₂.support)) :
    Nat.card {x : Fin m → ZMod p // ∀ cl ∈ L, cl.sat x} * p ^ (L.map LevelClause.codim).sum
      = p ^ m := by
  induction L with
  | nil =>
    have e : {x : Fin m → ZMod p // ∀ cl ∈ ([] : List (LevelClause p m)), cl.sat x}
        ≃ (Fin m → ZMod p) := Equiv.subtypeUnivEquiv (fun x => by simp)
    simp only [List.map_nil, List.sum_nil, pow_zero, mul_one]
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  | cons cl L' ih =>
    obtain ⟨hcl_disj, hL'_disj⟩ := List.pairwise_cons.mp hdisj
    have ihres := ih hL'_disj
    have hR : ∀ x y : Fin m → ZMod p, (∀ c ∉ cl.support, x c = y c) →
        ((∀ c' ∈ L', c'.sat x) ↔ (∀ c' ∈ L', c'.sat y)) := by
      intro x y hxy
      have agree : ∀ c' ∈ L', ∀ c ∈ c'.support, x c = y c := by
        intro c' hc' c hc
        exact hxy c (Finset.disjoint_right.mp (hcl_disj c' hc') hc)
      constructor
      · intro h c' hc'; exact (c'.dep x y (agree c' hc')).mp (h c' hc')
      · intro h c' hc'; exact (c'.dep x y (agree c' hc')).mpr (h c' hc')
    have hcrux := crux cl (fun x => ∀ c' ∈ L', c'.sat x) hR
    rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => List.forall_mem_cons)),
        List.map_cons, List.sum_cons, pow_add, ← mul_assoc, hcrux]
    exact ihres

theorem C1_clausesCount {m : ℕ} (fd : FreshData p m) : Nat.card {x : Fin m → ZMod p // fd.sat x} * p ^ fd.mstar = p ^ m :=
  list_count fd.clauses fd.disj

end LeanUrat.MovesC
