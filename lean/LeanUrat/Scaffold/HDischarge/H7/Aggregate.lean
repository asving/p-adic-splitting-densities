/-
HDISCHARGE_H7 §3.3 — `H7/Aggregate.lean`: the IT-4 abstract aggregation kernels
(unit W1b: H7-C1a `uniform_on_union` [MED], H7-C1b `sib_of_uniform_words`
[MED-HARD]).  Statements transcribed VERBATIM from
`lean/blueprints/HDISCHARGE_H7.md` §3.3; proofs filled by prover H7-C1a/C1b.
Dependencies: Mathlib only.
-/
import Mathlib

namespace LeanUrat.Scaffold.HDischarge.H7

open Finset in
/-- H7-C1a [MED; Tier S-abstract but genuinely mathematical]: words uniform on each
part of a partition (per-part multiplicity may vary) are uniform on the union — the
aggregation half of IT-4. Review-CONFIRMED valid as stated. Proof plan: U := Σ u_C;
count each ω-fiber by `Finset.card_biUnion` over the ∃!-disjoint parts. -/
theorem uniform_on_union {X W : Type*} [Fintype X] [DecidableEq X] [Fintype W]
    [DecidableEq W] (P : Finset (Finset X)) (w : X → W)
    (hcover : ∀ x : X, ∃! C, C ∈ P ∧ x ∈ C)
    (hunif : ∀ C ∈ P, ∃ u : ℕ, ∀ ω : W, (C.filter (fun x => w x = ω)).card = u) :
    ∃ U : ℕ, ∀ ω : W, (univ.filter (fun x : X => w x = ω)).card = U := by
  choose u hu using hunif
  refine ⟨∑ C ∈ P.attach, u C.1 C.2, fun ω => ?_⟩
  have hsplit : univ.filter (fun x : X => w x = ω)
      = P.biUnion (fun C => C.filter (fun x => w x = ω)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · intro hw
      obtain ⟨C, ⟨hCP, hxC⟩, -⟩ := hcover x
      exact ⟨C, hCP, hxC, hw⟩
    · rintro ⟨C, -, -, hw⟩
      exact hw
  have hdisj : ∀ C₁ ∈ P, ∀ C₂ ∈ P, C₁ ≠ C₂ →
      Disjoint (C₁.filter (fun x => w x = ω)) (C₂.filter (fun x => w x = ω)) := by
    intro C₁ h₁ C₂ h₂ hne
    rw [Finset.disjoint_left]
    intro a ha₁ ha₂
    obtain ⟨C, -, huniq⟩ := hcover a
    exact hne ((huniq C₁ ⟨h₁, (mem_filter.mp ha₁).1⟩).trans
      (huniq C₂ ⟨h₂, (mem_filter.mp ha₂).1⟩).symm)
  rw [hsplit, card_biUnion hdisj,
    ← Finset.sum_attach P (fun C => (C.filter (fun x => w x = ω)).card)]
  exact Finset.sum_congr rfl fun C _ => hu C.1 C.2 ω

open Finset in
/-- H7-C1b [MED-HARD]: exactly-uniform joint words on a product alphabet satisfy the
(SIB) count identity for componentwise events — the positive twin of
`MovesU.SibRouteA.sib_diag_break`. `hm : 1 ≤ m` REQUIRED (REV 2, review finding 12:
the m = 0 instance is FALSE — empty product 1 vs #X). Proof plan: both sides equal
U^m · (∏_j #E_j) · (∏_j #A_j)^{m−1}. -/
theorem sib_of_uniform_words {X : Type*} [Fintype X] [DecidableEq X]
    {m : ℕ} (hm : 1 ≤ m) {A : Fin m → Type*} [∀ j, Fintype (A j)]
    [∀ j, DecidableEq (A j)]
    (w : X → ∀ j, A j) {U : ℕ}
    (hU : ∀ ω : ∀ j, A j, (univ.filter (fun x => w x = ω)).card = U)
    (E : ∀ j, Finset (A j)) :
    (univ.filter (fun x : X => ∀ j, w x j ∈ E j)).card
        * (Fintype.card X) ^ (m - 1)
      = ∏ j, (univ.filter (fun x : X => w x j ∈ E j)).card := by
  -- (0) generic fiber count over any target set S of joint words
  have key : ∀ S : Finset (∀ j, A j),
      (univ.filter (fun x : X => w x ∈ S)).card = U * S.card := by
    intro S
    have hmem : ∀ x ∈ univ.filter (fun x : X => w x ∈ S), w x ∈ S :=
      fun x hx => (mem_filter.mp hx).2
    rw [Finset.card_eq_sum_card_fiberwise hmem]
    have hfib : ∀ ω ∈ S,
        ((univ.filter (fun x : X => w x ∈ S)).filter (fun x => w x = ω)).card
          = U := by
      intro ω hω
      rw [Finset.filter_filter,
        Finset.filter_congr (fun x _ => show (w x ∈ S ∧ w x = ω) ↔ w x = ω from
          ⟨And.right, fun h => ⟨h ▸ hω, h⟩⟩)]
      exact hU ω
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  -- (1) total count: #X = U · ∏_j #A_j
  have hX : Fintype.card X = U * ∏ j, Fintype.card (A j) := by
    have h := key univ
    simpa [Fintype.card_pi] using h
  -- (2) joint-event count: U · ∏_j #E_j
  have hJoint : (univ.filter (fun x : X => ∀ j, w x j ∈ E j)).card
      = U * ∏ j, (E j).card := by
    rw [Finset.filter_congr
        (fun x _ => (Fintype.mem_piFinset (f := w x) (t := E)).symm),
      key, Fintype.card_piFinset]
  -- (3) per-coordinate count: U · #E_j · ∏_{k ≠ j} #A_k
  have hCoord : ∀ j : Fin m, (univ.filter (fun x : X => w x j ∈ E j)).card
      = U * ((E j).card * ∏ k ∈ univ.erase j, Fintype.card (A k)) := by
    intro j
    have hset : (univ.filter (fun x : X => w x j ∈ E j))
        = univ.filter (fun x : X =>
            w x ∈ Fintype.piFinset (fun k => if k = j then E k else univ)) := by
      refine Finset.filter_congr fun x _ => ?_
      rw [Fintype.mem_piFinset]
      constructor
      · intro hj k
        by_cases hk : k = j
        · subst hk; simpa using hj
        · simp [hk]
      · intro h
        simpa using h j
    rw [hset, key, Fintype.card_piFinset]
    congr 1
    rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ j)]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun k hk => ?_
      rw [if_neg (Finset.mem_erase.mp hk).1]
      exact Finset.card_univ
  -- (4) exponent identity: ∏_j ∏_{k ≠ j} #A_k = (∏_k #A_k)^{m−1}
  have hT : ∏ j : Fin m, ∏ k ∈ univ.erase j, Fintype.card (A k)
      = (∏ k, Fintype.card (A k)) ^ (m - 1) := by
    rw [Finset.prod_comm' (t' := univ) (s' := fun k => univ.erase k)
      (fun a b => by
        simp only [mem_univ, mem_erase, ne_eq, and_true, true_and]
        exact ne_comm),
      ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k),
      Finset.card_univ, Fintype.card_fin]
  -- (5) assemble: both sides = U^m · (∏_j #E_j) · (∏_k #A_k)^{m−1}
  have hprod : ∏ j, (univ.filter (fun x : X => w x j ∈ E j)).card
      = U ^ m * ((∏ j, (E j).card) * (∏ k, Fintype.card (A k)) ^ (m - 1)) := by
    calc ∏ j, (univ.filter (fun x : X => w x j ∈ E j)).card
        = ∏ j, (U * ((E j).card * ∏ k ∈ univ.erase j, Fintype.card (A k))) :=
          Finset.prod_congr rfl fun j _ => hCoord j
      _ = (∏ _j : Fin m, U)
            * ∏ j, ((E j).card * ∏ k ∈ univ.erase j, Fintype.card (A k)) :=
          Finset.prod_mul_distrib
      _ = U ^ m * ((∏ j, (E j).card)
            * ∏ j, ∏ k ∈ univ.erase j, Fintype.card (A k)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_mul_distrib]
      _ = U ^ m * ((∏ j, (E j).card)
            * (∏ k, Fintype.card (A k)) ^ (m - 1)) := by rw [hT]
  rw [hJoint, hX, hprod]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  simp only [Nat.add_sub_cancel]
  ring

end LeanUrat.Scaffold.HDischarge.H7
