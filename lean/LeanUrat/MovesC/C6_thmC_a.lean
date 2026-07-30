/-
Unit C6.thmC_a — moves_ref: §C.2 THEOREM C(a), ROUND 3 (audit R2 F35/45/blocker 58)

`S(H,Z) := JetSetup.SHZ` is the INDEPENDENTLY-defined transported system `T(H,Z)` (the ∃-chain
over the recorded moves — no image, no `Sigma`). This unit PROVES:
  (i)   `Ψ_H` is bijective (composite of unitriangular moves);
  (ii)  `S(H,Z)` EQUALS the `Ψ_H`-image of the final joint locus `Σ_len ∩ locus(Z)`;
  (iii) the two have equal cardinality.

Deps `C6.psiBij` / `C6.transportedSystem` are re-derived inline here (`unitri_bij`+`seg_bij`
for (i); `bridge` for the transported-system iff), so this file imports only `Defs`.

UNUSED-HYPOTHESIS CAVEAT (2026-07-30 verify-2 fold-in): the hypothesis
`hZ : AdmissibleZ (J.Sigma H.nodes.length) Z` is NOT used in the proof of clauses
(i)–(iii) below — the proof closes via `unitri_bij`/`bridge`/`seg`-folding/image
congruence without touching admissibility. `hZ` is retained for quantifier fidelity
with rev-14 Theorem C(a)'s statement (the statement is fenced; do NOT remove it), and
admissibility IS genuinely consumed on the C(b) side via `C6_transportedAdmissible`.
-/
import LeanUrat.MovesC.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Polynomial LeanUrat.Moves

namespace LeanUrat.MovesC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- A unitriangular self-map of `Fin m → ZMod p` is bijective: injective by strong induction
on the coordinate (the diagonal is the identity, the correction depends only on earlier
coordinates), hence bijective since the domain is finite. -/
private lemma unitri_bij {m : ℕ} {Θ : (Fin m → ZMod p) → (Fin m → ZMod p)}
    (hΘ : IsUnitriangular Θ) : Function.Bijective Θ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hinj : Function.Injective Θ := by
    intro x y hxy
    have key : ∀ (D : ℕ) (i : Fin m), i.val = D → x i = y i := by
      intro D
      induction D using Nat.strong_induction_on with
      | _ D ihD =>
        intro i hiD
        obtain ⟨corr, hcorr⟩ := hΘ i
        have h1 : Θ x i = Θ y i := congrFun hxy i
        rw [hcorr x, hcorr y] at h1
        have hc : (fun (j : Fin m) (_ : j < i) => x j) = (fun (j : Fin m) (_ : j < i) => y j) := by
          funext j hj
          exact ihD j.val (by rw [← hiD]; exact hj) j rfl
        rw [hc] at h1
        exact add_right_cancel h1
    funext i
    exact key i.val i rfl
  exact (Finite.injective_iff_bijective).mp hinj

/-- `seg j j = id` (pointwise): the empty composite. -/
private lemma seg_diag {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (j : ℕ)
    (w : Fin m → ZMod p) : J.seg j j w = w := by
  cases j with
  | zero => rfl
  | succ j' =>
    simp only [JetSetup.seg]
    rw [if_neg (by omega : ¬ j' + 1 ≤ j')]
    rfl

/-- **Left-peel of the move composite** (`seg i k = Θ_i ∘ seg (i+1) k`): the recursion appends
`Θ_{k-1}` on the right, so peeling `Θ_i` off the left is a derived identity, proved by induction
on the length `k`. -/
private lemma seg_peel {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) :
    ∀ (k' i : ℕ), i < k' → ∀ w, J.seg i k' w = J.Theta i (J.seg (i + 1) k' w) := by
  intro k'
  induction k' with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k'' ih =>
    intro i hi w
    have hik : i ≤ k'' := Nat.lt_succ_iff.mp hi
    simp only [JetSetup.seg]
    rw [if_pos hik]
    rcases lt_or_eq_of_le hik with hlt | heq
    · rw [if_pos (by omega : i + 1 ≤ k'')]
      simp only [Function.comp_apply]
      exact ih i hlt (J.Theta k'' w)
    · subst heq
      rw [if_neg (by omega : ¬ i + 1 ≤ i)]
      simp only [Function.comp_apply, id_eq]
      rw [seg_diag J i (J.Theta i w)]

/-- **The transported-system iff** (`C6.transportedSystem` content, folded through the state
recursion): for any chain `y` satisfying the recorded move equations, `y t` solves the state
`Σ_t` exactly when every earlier fresh clause is satisfied along the chain. Proved by induction
on the prefix length `t`, using `recursion` (state step) and `inh_implied` (on the cylinder the
stratum reduces to its fresh clauses). -/
private lemma bridge {n N m : ℕ} {H : History p F} (J : JetSetup H n N m)
    (y : ℕ → (Fin m → ZMod p))
    (hchain : ∀ i, i < H.nodes.length → y i = J.Theta i (y (i + 1))) :
    ∀ t, t ≤ H.nodes.length →
      ((J.Sigma t).IsSolution (y t) ↔ ∀ i, i < t → (J.fresh i).sat (y i)) := by
  intro t
  induction t with
  | zero =>
    intro _
    constructor
    · intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro _ c hc
      simp [J.init c] at hc
  | succ t ih =>
    intro ht
    have ht' : t < H.nodes.length := ht
    have htle : t ≤ H.nodes.length := le_of_lt ht'
    have hyt : y t = J.Theta t (y (t + 1)) := hchain t ht'
    have hrec := J.recursion t ht' (y (t + 1))
    rw [← hyt] at hrec
    rw [hrec]
    constructor
    · rintro ⟨hsig, hstr⟩ i hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
      · exact (ih htle).mp hsig i hlt
      · rw [heq]; exact (J.inh_implied t ht' (y t) hsig).mp hstr
    · intro hall
      have hsig : (J.Sigma t).IsSolution (y t) :=
        (ih htle).mpr (fun i hi => hall i (Nat.lt_succ_of_lt hi))
      exact ⟨hsig, (J.inh_implied t ht' (y t) hsig).mpr (hall t (Nat.lt_succ_self t))⟩

/-- **The chain folds to the move composite**: if `y` satisfies the recorded move equations then
`Ψ_H(y k) = y 0`, i.e. `seg 0 k (y k) = y 0` (downward fold on the length via `seg_peel`). -/
private lemma seg_fold {n N m : ℕ} {H : History p F} (J : JetSetup H n N m)
    (y : ℕ → (Fin m → ZMod p)) (k : ℕ)
    (hchain : ∀ i, i < k → y i = J.Theta i (y (i + 1))) :
    J.seg 0 k (y k) = y 0 := by
  have foldAux : ∀ d, d ≤ k → J.seg (k - d) k (y k) = y (k - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using seg_diag J k (y k)
    | succ d ih =>
      intro hd
      have hlt : k - (d + 1) < k := by omega
      have hstep : k - (d + 1) + 1 = k - d := by omega
      have hdle : d ≤ k := by omega
      rw [seg_peel J k (k - (d + 1)) hlt (y k), hstep, ih hdle, ← hstep]
      exact (hchain (k - (d + 1)) hlt).symm
  have h := foldAux k (le_refl k)
  simpa using h

/-- **THEOREM C(a)** — see the module header. -/
theorem C6_thmC_a {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (Z : Locus p m) (hZ : AdmissibleZ (J.Sigma H.nodes.length) Z) : Function.Bijective (J.Psi H.nodes.length) ∧ J.SHZ Z = (J.Psi H.nodes.length) '' {x : Fin m → ZMod p | (J.Sigma H.nodes.length).IsSolution x ∧ Z.IsSolution x} ∧ Nat.card (J.SHZ Z) = Nat.card {x : Fin m → ZMod p // (J.Sigma H.nodes.length).IsSolution x ∧ Z.IsSolution x} := by
  classical
  -- (i) Ψ_H is bijective
  have hbij : Function.Bijective (J.Psi H.nodes.length) := by
    show Function.Bijective (J.seg 0 H.nodes.length)
    -- seg 0 len is a composite of unitriangular moves
    have seg_bij : ∀ (i k : ℕ), Function.Bijective (J.seg i k) := by
      intro i k
      induction k with
      | zero => simpa only [JetSetup.seg] using Function.bijective_id
      | succ k ih =>
        simp only [JetSetup.seg]
        by_cases h : i ≤ k
        · rw [if_pos h]; exact ih.comp (unitri_bij (J.Theta_uni k))
        · rw [if_neg h]; exact Function.bijective_id
    exact seg_bij 0 H.nodes.length
  -- (ii) the set equality
  have hset : J.SHZ Z = (J.Psi H.nodes.length) ''
      {x : Fin m → ZMod p | (J.Sigma H.nodes.length).IsSolution x ∧ Z.IsSolution x} := by
    ext x
    simp only [JetSetup.SHZ, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨y, hy0, hchain, hfresh, hZsol⟩
      refine ⟨y H.nodes.length, ⟨?_, hZsol⟩, ?_⟩
      · exact (bridge J y hchain H.nodes.length (le_refl _)).mpr hfresh
      · show J.Psi H.nodes.length (y H.nodes.length) = x
        rw [JetSetup.Psi, ← hy0]
        exact seg_fold J y H.nodes.length hchain
    · rintro ⟨w, ⟨hwsig, hwZ⟩, hwx⟩
      refine ⟨fun i => J.seg i H.nodes.length w, ?_, ?_, ?_, ?_⟩
      · show J.seg 0 H.nodes.length w = x
        exact hwx
      · intro i hi
        exact seg_peel J H.nodes.length i hi w
      · intro i hi
        have hchain' : ∀ j, j < H.nodes.length →
            (fun j => J.seg j H.nodes.length w) j
              = J.Theta j ((fun j => J.seg j H.nodes.length w) (j + 1)) :=
          fun j hj => seg_peel J H.nodes.length j hj w
        have hsig : (J.Sigma H.nodes.length).IsSolution
            ((fun j => J.seg j H.nodes.length w) H.nodes.length) := by
          show (J.Sigma H.nodes.length).IsSolution (J.seg H.nodes.length H.nodes.length w)
          rw [seg_diag J H.nodes.length w]; exact hwsig
        exact (bridge J (fun j => J.seg j H.nodes.length w) hchain'
          H.nodes.length (le_refl _)).mp hsig i hi
      · show Z.IsSolution (J.seg H.nodes.length H.nodes.length w)
        rw [seg_diag J H.nodes.length w]; exact hwZ
  -- (iii) equal cardinality (image under an injection)
  refine ⟨hbij, hset, ?_⟩
  rw [hset]
  exact Nat.card_congr (Equiv.Set.image (J.Psi H.nodes.length)
    {x : Fin m → ZMod p | (J.Sigma H.nodes.length).IsSolution x ∧ Z.IsSolution x}
    hbij.1).symm

end LeanUrat.MovesC
