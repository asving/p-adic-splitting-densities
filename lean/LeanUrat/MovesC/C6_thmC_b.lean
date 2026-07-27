/-
Unit C6.thmC_b — moves_ref: §C.2 THEOREM C(b): #S(H,Z)·p^{Σm*+|pins Z|} = p^{nN}
  ROUND 3 (audit R2 F36/53/blocker 57): stated on the INDEPENDENT SHZ, and totalPins' summands
  (J.fresh i).mstar are PINNED to the D.11 species inventory by J.mstar_eq (the fresh-band count
  from node data), so the RHS is §C(b)'s actual product, not a presentation artifact.

  ASSEMBLY unit. The box identity is assembled from four deps:
    · C6.thmC_a (iii)          : Nat.card (SHZ Z) = Nat.card (final joint locus Σ_len ∧ Z)
    · C6.transportedAdmissible : Nat.card (joint) · p^{|pins Z|} = mass(Σ_len)
    · C5.massCodim (k = len)   : mass(Σ_len) = p^{m − Σ m*}
    · C5.massRec   (k = len)   : numPinned(Σ_len) = Σ m*      (⇒ Σ m* ≤ m via numPinned ≤ m)
  then p^{m−Σm*} · p^{Σm*} = p^m by Σ m* ≤ m.

  DEP NOTE: the dep unit file `C6_thmC_a.lean` is a RETYPE unit not yet present in the repo, so
  its statement (byte-copied from MANIFEST) is PROVED LOCALLY below as the private lemma
  `dep_thmC_a`, from C6.thmC_a's OWN manifest deps — `C6.psiBij` (clause (i)) and
  `C6.transportedSystem` (clauses (ii)/(iii)) — following the manifest sketch for C6.thmC_a:
  the SHZ ∃-chain of a point is exactly the seg-composite chain of a final joint-locus point
  (⊇: `y i := seg i len x₀`; ⊆: the chain equations fold to `y i = seg i len (y len)`), and the
  image count under the injective `Psi` is the source count. This unit is therefore fully
  machine-checked with NO interface stub. WHEN `C6_thmC_a.lean` lands, `dep_thmC_a` may be
  replaced by `import LeanUrat.MovesC.C6_thmC_a` + renaming the call site.
-/
import LeanUrat.MovesC.Defs
import LeanUrat.MovesC.C6_psiBij
import LeanUrat.MovesC.C6_transportedSystem
import LeanUrat.MovesC.C6_transportedAdmissible
import LeanUrat.MovesC.C5_massCodim
import LeanUrat.MovesC.C5_massRec

namespace LeanUrat.MovesC

open LeanUrat.Moves

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The empty segment composite is the identity: `seg i i = id`. -/
private lemma seg_self' {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (i : ℕ) :
    J.seg i i = id := by
  cases i with
  | zero => rfl
  | succ j =>
    have h : ¬ (j + 1 ≤ j) := by omega
    simp [JetSetup.seg, h]

/-- Peeling the FIRST move off a segment composite: for `i < k`,
`seg i k x = Θ_i (seg (i+1) k x)`. -/
private lemma seg_succ_apply {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) :
    ∀ k i : ℕ, i < k → ∀ x : Fin m → ZMod p,
      J.seg i k x = J.Theta i (J.seg (i + 1) k x) := by
  intro k
  induction k with
  | zero => intro i hi x; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro i hi x
    rcases Nat.lt_or_ge i k with hlt | hge
    · have h1 : i ≤ k := le_of_lt hlt
      have h2 : i + 1 ≤ k := hlt
      simp only [JetSetup.seg, if_pos h1, if_pos h2, Function.comp_apply]
      exact ih i hlt (J.Theta k x)
    · have heq : i = k := by omega
      subst heq
      have h2 : ¬ (i + 1 ≤ i) := by omega
      simp [JetSetup.seg, h2, seg_self']

set_option linter.unusedVariables false in
/-- LOCAL PROOF of dep unit `C6.thmC_a` (its file is not yet in the repo); statement
byte-identical to MANIFEST. (i) is `C6.psiBij`. (ii) ⊆: a chain `y` for `x` folds to
`y i = seg i len (y len)` (downward induction on the chain equations), so `x = Psi len (y len)`
and `y len` solves `Σ_len` by `C6.transportedSystem` (the chain supplies exactly the transported
fresh predicates) and `Z` directly. ⊇: a final joint-locus point `x₀` yields the chain
`y i := seg i len x₀` (fresh-sat again by `C6.transportedSystem`; terminal `Z` at
`seg len len = id`). (iii): image count under the injective `Psi` = source count.
(`hZ` is part of the byte-copied MANIFEST statement; clauses (i)–(iii) hold without it,
so the unused-variable linter is silenced rather than the statement altered.) -/
private lemma dep_thmC_a {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (Z : Locus p m)
    (hZ : AdmissibleZ (J.Sigma H.nodes.length) Z) :
    Function.Bijective (J.Psi H.nodes.length) ∧
      J.SHZ Z = (J.Psi H.nodes.length) '' {x : Fin m → ZMod p |
        (J.Sigma H.nodes.length).IsSolution x ∧ Z.IsSolution x} ∧
      Nat.card (J.SHZ Z) = Nat.card {x : Fin m → ZMod p //
        (J.Sigma H.nodes.length).IsSolution x ∧ Z.IsSolution x} := by
  have hbij : Function.Bijective (J.Psi H.nodes.length) := C6_psiBij J H.nodes.length
  have himg : J.SHZ Z = (J.Psi H.nodes.length) '' {x : Fin m → ZMod p |
      (J.Sigma H.nodes.length).IsSolution x ∧ Z.IsSolution x} := by
    ext x
    simp only [JetSetup.SHZ, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨y, hy0, hchain, hfresh, hZsol⟩
      -- the chain equations fold to the seg composite: `y i = seg i len (y len)`
      have hkey : ∀ j : ℕ, j ≤ H.nodes.length →
          y (H.nodes.length - j)
            = J.seg (H.nodes.length - j) H.nodes.length (y H.nodes.length) := by
        intro j
        induction j with
        | zero => intro _; simp [seg_self']
        | succ j ihj =>
          intro hj
          have hj' : j ≤ H.nodes.length := by omega
          have hi : H.nodes.length - (j + 1) < H.nodes.length := by omega
          have hsucc : H.nodes.length - (j + 1) + 1 = H.nodes.length - j := by omega
          calc y (H.nodes.length - (j + 1))
              = J.Theta (H.nodes.length - (j + 1)) (y (H.nodes.length - (j + 1) + 1)) :=
                hchain _ hi
            _ = J.Theta (H.nodes.length - (j + 1)) (y (H.nodes.length - j)) := by
                rw [hsucc]
            _ = J.Theta (H.nodes.length - (j + 1))
                  (J.seg (H.nodes.length - j) H.nodes.length (y H.nodes.length)) := by
                rw [ihj hj']
            _ = J.Theta (H.nodes.length - (j + 1))
                  (J.seg (H.nodes.length - (j + 1) + 1) H.nodes.length
                    (y H.nodes.length)) := by
                rw [hsucc]
            _ = J.seg (H.nodes.length - (j + 1)) H.nodes.length (y H.nodes.length) :=
                (seg_succ_apply J H.nodes.length (H.nodes.length - (j + 1)) hi
                  (y H.nodes.length)).symm
      have hchainSeg : ∀ i : ℕ, i ≤ H.nodes.length →
          y i = J.seg i H.nodes.length (y H.nodes.length) := by
        intro i hile
        have h := hkey (H.nodes.length - i) (by omega)
        have hii : H.nodes.length - (H.nodes.length - i) = i := by omega
        rwa [hii] at h
      refine ⟨y H.nodes.length, ⟨?_, hZsol⟩, ?_⟩
      · -- `y len` solves `Σ_len`: the chain supplies exactly the transported fresh predicates
        rw [C6_transportedSystem J H.nodes.length (le_refl _) (y H.nodes.length)]
        intro i hi
        rw [← hchainSeg i (le_of_lt hi)]
        exact hfresh i hi
      · -- `Psi len (y len) = y 0 = x`
        rw [← hy0]
        exact (hchainSeg 0 (Nat.zero_le _)).symm
    · rintro ⟨x₀, ⟨hsol, hZsol⟩, hpsi⟩
      refine ⟨fun i => J.seg i H.nodes.length x₀, hpsi, ?_, ?_, ?_⟩
      · -- chain equations: peel the first move
        intro i hi
        exact seg_succ_apply J H.nodes.length i hi x₀
      · -- fresh-sat along the chain, by the transported system
        intro i hi
        exact (C6_transportedSystem J H.nodes.length (le_refl _) x₀).mp hsol i hi
      · -- terminal `Z` at `seg len len = id`
        simpa [seg_self'] using hZsol
  refine ⟨hbij, himg, ?_⟩
  rw [himg, Nat.card_image_of_injective hbij.injective]
  rfl

-- `numPinned` never exceeds the number of coordinates (local copy of the private lemma in
-- `C6_transportedAdmissible`, needed to bound `Σ m* ≤ m`).
omit [Fact p.Prime] in
private lemma numPinned_le' {m : ℕ} (D : Locus p m) : D.numPinned ≤ m := by
  rw [DigitSystem.numPinned]
  calc (Finset.univ.filter (fun i => D.pinned i)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = m := by rw [Finset.card_univ, Fintype.card_fin]

theorem C6_thmC_b {n N m : ℕ} {H : History p F} (J : JetSetup H n N m) (Z : Locus p m) (hZ : AdmissibleZ (J.Sigma H.nodes.length) Z) : Nat.card (J.SHZ Z) * p ^ totalPins J Z = boxMass p m := by
  -- (iii): the classifier locus count equals the final joint-locus count
  obtain ⟨_, _, hcardSHZ⟩ := dep_thmC_a J Z hZ
  -- admissible Z peels a factor p^{|pins Z|} off the final state mass
  have htrans := C6_transportedAdmissible (J.Sigma H.nodes.length) Z hZ
  -- the final state mass is p^{m − Σ m*}
  have hcodim := C5_massCodim J H.nodes.length (le_refl _)
  -- and its pin count is exactly Σ m*, hence Σ m* ≤ m
  have hrec := C5_massRec J H.nodes.length (le_refl _)
  have hSm : (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar) ≤ m := by
    have hle := numPinned_le' (J.Sigma H.nodes.length)
    rwa [hrec] at hle
  -- assemble: card(SHZ)·p^{Σm*+|pinsZ|} = (card(joint)·p^{|pinsZ|})·p^{Σm*}
  --         = mass·p^{Σm*} = p^{m−Σm*}·p^{Σm*} = p^m
  simp only [boxMass, totalPins]
  rw [hcardSHZ, pow_add, ← mul_assoc, mul_right_comm, htrans, hcodim, ← pow_add,
    Nat.sub_add_cancel hSm]

end LeanUrat.MovesC
