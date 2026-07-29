/-  MovesV unit V6-1c `rootTable_census` (NINE POINTS, CHAR-FREE — C20/A-4) —
    the COUNT SEMANTICS via the char-free divisibility multiplicity (no
    derivative, no discriminant).  [The classifier defs are CLOSED here.]
    STATEMENT REPAIR 2026-07-29 (adjudicated; machine-verified refutation from
    the prover fleet): the E-phase middle conjunct mis-keyed profile (2,2) to
    TH12 — the (1,1) class's polynomial (linear × irreducible quadratic,
    q²(q−1)/2) — refuted at ZMod 3: classCount (ZMod 3) (2,2) = 6 ≠ 9 =
    TH12.eval 3, while classCount (1,1) = 9 = TH12.eval 3 nails the swap.
    Re-keyed (2,2) ↦ T21 per the blueprint V6-1 table. Blueprint rows
    (MOVESV_LEAN_BLUEPRINT_2026-07-28.md): V6-1c "classifying monic cubics
    z³+az²+bz+c by (root count, max multiplicity): the five class counts equal
    the closed forms' values"; the keying is fixed by V6-1a's count face
    "(q³−3q²+2q)/6 + (3q³−3q²)/6 + (2q³−2q)/6 + (6q²−6q)/6 + 6q/6 = q³" —
    TH3 = (q³−3q²+2q)/6 ↦ (3,1); TH12 = (3q³−3q²)/6 ↦ (1,1);
    TH3c = (2q³−2q)/6 ↦ (0,0); T21 = q²−q ↦ (2,2); T3 = q ↦ (1,3). The
    blueprint table is consistent with its own nine-point census (no
    bracket-correction needed); only this file's keying was wrong.
    PROVED for EVERY finite field F (the statement's generic-F form is the
    E-phase's own; the nine-point roster consumes it by instantiation):
    char-free root-block arguments — tri/dbl pointwise factorizations,
    Vieta-from-three-roots, and card bijections onto F, offDiag F, and the
    3-subsets of F. -/
import LeanUrat.MovesV.V6_a1eval

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesV

/-- r is a root of z³+az²+bz+c. -/
def isRoot3 {F : Type*} [Field F] [DecidableEq F] (a b c r : F) : Bool :=
  decide (r ^ 3 + a * r ^ 2 + b * r + c = 0)

/-- (z−r)² divides (with cofactor z−s, s := −a−2r): the char-free test. -/
def isDbl3 {F : Type*} [Field F] [DecidableEq F] (a b c r : F) : Bool :=
  decide (b = r * r + 2 * r * (-a - 2 * r) ∧ c = -(r * r * (-a - 2 * r)))

/-- (z−r)³ divides: the char-free test. -/
def isTri3 {F : Type*} [Field F] [DecidableEq F] (a b c r : F) : Bool :=
  decide (a = -(3 * r) ∧ b = 3 * r ^ 2 ∧ c = -(r ^ 3))

open Classical in
/-- the (root count, max multiplicity) profile of z³+az²+bz+c. -/
noncomputable def rootProfile {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (a b c : F) : ℕ × ℕ :=
  ((Finset.univ.filter (fun r => isRoot3 a b c r)).card,
   Finset.univ.sup (fun r =>
     if isTri3 a b c r then 3
     else if isRoot3 a b c r && isDbl3 a b c r then 2
     else if isRoot3 a b c r then 1 else 0))

open Classical in
noncomputable def classCount (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (pr : ℕ × ℕ) : ℕ :=
  (Finset.univ.filter
    (fun t : F × F × F => rootProfile t.1 t.2.1 t.2.2 = pr)).card

/-! ### The char-free root-block toolbox (A-4's divisibility multiplicity) -/

section Toolbox
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private lemma isRoot3_iff (a b c x : F) :
    isRoot3 a b c x = true ↔ x ^ 3 + a * x ^ 2 + b * x + c = 0 := by
  simp [isRoot3]

/-- tri pins the whole cubic: pointwise (·−r)³. -/
private lemma tri_eval {a b c r : F} (h : isTri3 a b c r = true) (x : F) :
    x ^ 3 + a * x ^ 2 + b * x + c = (x - r) ^ 3 := by
  obtain ⟨ha, hb, hc⟩ := by simpa [isTri3] using h
  subst ha; subst hb; subst hc; ring

/-- under tri, every root IS r (char-free). -/
private lemma tri_root {a b c r : F} (h : isTri3 a b c r = true) {x : F}
    (hx : x ^ 3 + a * x ^ 2 + b * x + c = 0) : x = r := by
  have h3 : (x - r) ^ 3 = 0 := by rw [← tri_eval h x, hx]
  have := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h3
  exact sub_eq_zero.mp this

/-- dbl pins the cubic pointwise: (·−r)²·(·−s₀), s₀ := −a−2r. -/
private lemma dbl_eval {a b c r : F} (h : isDbl3 a b c r = true) (x : F) :
    x ^ 3 + a * x ^ 2 + b * x + c = (x - r) ^ 2 * (x - (-a - 2 * r)) := by
  obtain ⟨hb, hc⟩ := by simpa [isDbl3] using h
  subst hb; subst hc; ring

/-- under dbl, every root lies in {r, s₀} (char-free). -/
private lemma dbl_root {a b c r : F} (h : isDbl3 a b c r = true) {x : F}
    (hx : x ^ 3 + a * x ^ 2 + b * x + c = 0) : x = r ∨ x = -a - 2 * r := by
  have h2 : (x - r) ^ 2 * (x - (-a - 2 * r)) = 0 := by rw [← dbl_eval h x, hx]
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact Or.inl (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'))
  · exact Or.inr (sub_eq_zero.mp h')

/-- Vieta from three distinct roots (the E1/E2 elimination, char-free). -/
private lemma vieta_of_roots {a b c r s t : F} (hrs : r ≠ s) (hrt : r ≠ t)
    (hst : s ≠ t)
    (hr : r ^ 3 + a * r ^ 2 + b * r + c = 0)
    (hs : s ^ 3 + a * s ^ 2 + b * s + c = 0)
    (ht : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    a = -(r + s + t) ∧ b = r * s + r * t + s * t ∧ c = -(r * s * t) := by
  have e1 : r ^ 2 + r * s + s ^ 2 + a * (r + s) + b = 0 := by
    have h' : (r - s) * (r ^ 2 + r * s + s ^ 2 + a * (r + s) + b) = 0 := by
      linear_combination hr - hs
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (sub_eq_zero.mp h'') hrs
    · exact h''
  have e2 : r ^ 2 + r * t + t ^ 2 + a * (r + t) + b = 0 := by
    have h' : (r - t) * (r ^ 2 + r * t + t ^ 2 + a * (r + t) + b) = 0 := by
      linear_combination hr - ht
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (sub_eq_zero.mp h'') hrt
    · exact h''
  have ha : a = -(r + s + t) := by
    have h' : (s - t) * (r + s + t + a) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (sub_eq_zero.mp h'') hst
    · linear_combination h''
  have hb : b = r * s + r * t + s * t := by
    linear_combination e1 - (r + s) * ha
  have hc : c = -(r * s * t) := by
    linear_combination hr - r ^ 2 * ha - r * hb
  exact ⟨ha, hb, hc⟩

/-- Vieta evaluation: the cubic with symmetric coefficients factors pointwise. -/
private lemma vieta_eval (r s t x : F) :
    x ^ 3 + (-(r + s + t)) * x ^ 2 + (r * s + r * t + s * t) * x + (-(r * s * t))
      = (x - r) * (x - s) * (x - t) := by ring

end Toolbox

/-! ### The three profile computations -/

section Profiles
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private lemma profile_tri (r : F) :
    rootProfile (-(3 * r)) (3 * r ^ 2) (-(r ^ 3)) = (1, 3) := by
  classical
  have htri : isTri3 (-(3 * r)) (3 * r ^ 2) (-(r ^ 3)) r = true := by
    simp [isTri3]
  have hself : isRoot3 (-(3 * r)) (3 * r ^ 2) (-(r ^ 3)) r = true := by
    rw [isRoot3_iff]; ring
  unfold rootProfile
  refine Prod.ext ?_ ?_
  · -- root filter = {r}
    have : (Finset.univ.filter
        (fun x : F => isRoot3 (-(3 * r)) (3 * r ^ 2) (-(r ^ 3)) x)) = {r} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hx; exact tri_root htri ((isRoot3_iff _ _ _ _).mp hx)
      · rintro rfl; exact hself
    rw [this, Finset.card_singleton]
  · -- sup = 3
    refine le_antisymm (Finset.sup_le fun x _ => by split_ifs <;> omega) ?_
    have hle := Finset.le_sup (f := fun x : F =>
      if isTri3 (-(3 * r)) (3 * r ^ 2) (-(r ^ 3)) x then 3
      else if isRoot3 (-(3 * r)) (3 * r ^ 2) (-(r ^ 3)) x
          && isDbl3 (-(3 * r)) (3 * r ^ 2) (-(r ^ 3)) x then 2
      else if isRoot3 (-(3 * r)) (3 * r ^ 2) (-(r ^ 3)) x then 1 else 0)
      (Finset.mem_univ r)
    simpa [htri] using hle

private lemma profile_dblpair {r s : F} (hrs : r ≠ s) :
    rootProfile (-(2 * r + s)) (r * r + 2 * r * s) (-(r * r * s)) = (2, 2) := by
  classical
  set a := -(2 * r + s) with hadef
  set b := r * r + 2 * r * s with hbdef
  set c := -(r * r * s) with hcdef
  have hs0 : -a - 2 * r = s := by rw [hadef]; ring
  have hdbl : isDbl3 a b c r = true := by
    simp only [isDbl3, decide_eq_true_eq]
    constructor
    · rw [hbdef, hs0]
    · rw [hcdef, hs0]
  have heval : ∀ x : F, x ^ 3 + a * x ^ 2 + b * x + c = (x - r) ^ 2 * (x - s) := by
    intro x
    rw [hadef, hbdef, hcdef]; ring
  have hroot_iff : ∀ x : F, isRoot3 a b c x = true ↔ (x = r ∨ x = s) := by
    intro x
    rw [isRoot3_iff, heval x]
    constructor
    · intro hx
      rcases mul_eq_zero.mp hx with h' | h'
      · exact Or.inl (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'))
      · exact Or.inr (sub_eq_zero.mp h')
    · rintro (rfl | rfl) <;> ring
  have hnotri : ∀ x : F, ¬ isTri3 a b c x = true := by
    intro x htri
    have hxr : r = x := tri_root htri (by rw [heval r]; ring)
    have hxs : s = x := tri_root htri (by rw [heval s]; ring)
    exact hrs (hxr.trans hxs.symm)
  unfold rootProfile
  refine Prod.ext ?_ ?_
  · -- root filter = {r, s}
    have : (Finset.univ.filter (fun x : F => isRoot3 a b c x)) = {r, s} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact hroot_iff x
    rw [this, Finset.card_insert_of_notMem (by simpa using hrs),
      Finset.card_singleton]
  · -- sup = 2
    refine le_antisymm (Finset.sup_le fun x _ => ?_) ?_
    · split_ifs with h1 h2 h3
      · exact absurd h1 (hnotri x)
      · omega
      · omega
      · omega
    · have hle := Finset.le_sup (f := fun x : F =>
        if isTri3 a b c x then 3
        else if isRoot3 a b c x && isDbl3 a b c x then 2
        else if isRoot3 a b c x then 1 else 0) (Finset.mem_univ r)
      have hterm : (if isTri3 a b c r then 3
          else if isRoot3 a b c r && isDbl3 a b c r then 2
          else if isRoot3 a b c r then 1 else 0) = 2 := by
        rw [if_neg (by simpa using hnotri r), if_pos]
        rw [Bool.and_eq_true]
        exact ⟨(hroot_iff r).mpr (Or.inl rfl), hdbl⟩
      omega

private lemma profile_distinct {r s t : F} (hrs : r ≠ s) (hrt : r ≠ t)
    (hst : s ≠ t) :
    rootProfile (-(r + s + t)) (r * s + r * t + s * t) (-(r * s * t)) = (3, 1) := by
  classical
  set a := -(r + s + t) with hadef
  set b := r * s + r * t + s * t with hbdef
  set c := -(r * s * t) with hcdef
  have heval : ∀ x : F, x ^ 3 + a * x ^ 2 + b * x + c
      = (x - r) * (x - s) * (x - t) := by
    intro x; rw [hadef, hbdef, hcdef]; ring
  have hroot_iff : ∀ x : F, isRoot3 a b c x = true ↔ (x = r ∨ x = s ∨ x = t) := by
    intro x
    rw [isRoot3_iff, heval x]
    constructor
    · intro hx
      rcases mul_eq_zero.mp hx with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact Or.inl (sub_eq_zero.mp h'')
        · exact Or.inr (Or.inl (sub_eq_zero.mp h''))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h'))
    · rintro (rfl | rfl | rfl) <;> ring
  have hroots : isRoot3 a b c r = true ∧ isRoot3 a b c s = true
      ∧ isRoot3 a b c t = true :=
    ⟨(hroot_iff r).mpr (Or.inl rfl), (hroot_iff s).mpr (Or.inr (Or.inl rfl)),
     (hroot_iff t).mpr (Or.inr (Or.inr rfl))⟩
  have hnotri : ∀ x : F, ¬ isTri3 a b c x = true := by
    intro x htri
    have h1 : r = x := tri_root htri ((isRoot3_iff _ _ _ _).mp hroots.1)
    have h2 : s = x := tri_root htri ((isRoot3_iff _ _ _ _).mp hroots.2.1)
    exact hrs (h1.trans h2.symm)
  have hnodbl : ∀ x : F, ¬ isDbl3 a b c x = true := by
    intro x hdbl
    have h1 := dbl_root hdbl ((isRoot3_iff _ _ _ _).mp hroots.1)
    have h2 := dbl_root hdbl ((isRoot3_iff _ _ _ _).mp hroots.2.1)
    have h3 := dbl_root hdbl ((isRoot3_iff _ _ _ _).mp hroots.2.2)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      rcases h3 with h3 | h3 <;>
      first
        | exact hrs (h1.trans h2.symm)
        | exact hrt (h1.trans h3.symm)
        | exact hst (h2.trans h3.symm)
  unfold rootProfile
  refine Prod.ext ?_ ?_
  · -- root filter = {r, s, t}
    have : (Finset.univ.filter (fun x : F => isRoot3 a b c x)) = {r, s, t} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      exact hroot_iff x
    rw [this]
    rw [Finset.card_insert_of_notMem (by simp [hrs, hrt]),
      Finset.card_insert_of_notMem (by simpa using hst),
      Finset.card_singleton]
  · -- sup = 1
    refine le_antisymm (Finset.sup_le fun x _ => ?_) ?_
    · split_ifs with h1 h2 h3
      · exact absurd h1 (hnotri x)
      · rw [Bool.and_eq_true] at h2
        exact absurd h2.2 (hnodbl x)
      · omega
      · omega
    · have hle := Finset.le_sup (f := fun x : F =>
        if isTri3 a b c x then 3
        else if isRoot3 a b c x && isDbl3 a b c x then 2
        else if isRoot3 a b c x then 1 else 0) (Finset.mem_univ r)
      have hterm : (if isTri3 a b c r then 3
          else if isRoot3 a b c r && isDbl3 a b c r then 2
          else if isRoot3 a b c r then 1 else 0) = 1 := by
        rw [if_neg (by simpa using hnotri r),
          if_neg (by rw [Bool.and_eq_true]; exact fun h => hnodbl r h.2),
          if_pos hroots.1]
      omega

end Profiles

/-! ### The three class counts (card bijections onto F, offDiag F, 3-subsets) -/

section Counts
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private lemma count_13 : classCount F (1, 3) = Fintype.card F := by
  classical
  unfold classCount
  rw [← Finset.card_univ (α := F)]
  symm
  refine Finset.card_bij
    (fun r _ => ((-(3 * r), 3 * r ^ 2, -(r ^ 3)) : F × F × F)) ?_ ?_ ?_
  · intro r _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact profile_tri r
  · intro r₁ _ r₂ _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨ha, hb, hc⟩ := heq
    have h3 : (r₂ - r₁) ^ 3 = 0 := by
      linear_combination -(r₁ * r₂) * ha + hc
    exact (sub_eq_zero.mp (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h3)).symm
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    unfold rootProfile at hy
    simp only [Prod.mk.injEq] at hy
    obtain ⟨x, -, hx3⟩ := (Finset.le_sup_iff (show (0 : ℕ) < 3 by norm_num)).mp hy.2.ge
    split_ifs at hx3 with h1 h2 h3
    · obtain ⟨ha, hb, hc⟩ := by simpa [isTri3] using h1
      exact ⟨x, Finset.mem_univ x, Prod.ext ha.symm (Prod.ext hb.symm hc.symm)⟩
    · omega
    · omega
    · omega

private lemma count_22 :
    classCount F (2, 2) = Fintype.card F * Fintype.card F - Fintype.card F := by
  classical
  unfold classCount
  rw [← Finset.card_univ (α := F), ← Finset.offDiag_card]
  symm
  refine Finset.card_bij (fun p _ =>
    ((-(2 * p.1 + p.2), p.1 * p.1 + 2 * p.1 * p.2, -(p.1 * p.1 * p.2)) : F × F × F))
    ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact profile_dblpair (Finset.mem_offDiag.mp hp).2.2
  · intro p₁ h₁ p₂ h₂ heq
    have hne₁ : p₁.1 ≠ p₁.2 := (Finset.mem_offDiag.mp h₁).2.2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨ha, hb, hc⟩ := heq
    have hroot : (p₂.1 - p₁.1) ^ 2 * (p₂.1 - p₁.2) = 0 := by
      linear_combination (p₂.1 ^ 2) * ha + p₂.1 * hb + hc
    have hp1 : p₂.1 = p₁.1 := by
      rcases mul_eq_zero.mp hroot with h' | h'
      · exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h')
      · exfalso
        have hcase : p₂.1 = p₁.2 := sub_eq_zero.mp h'
        have hsq : (p₁.1 - p₁.2) ^ 2 = 0 := by
          linear_combination hb + 2 * p₁.2 * ha
            + (-(2 * p₁.2) + (p₂.1 - p₁.2) + 2 * p₂.2) * hcase
        exact hne₁ (sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq))
    have hp2 : p₂.2 = p₁.2 := by linear_combination ha - 2 * hp1
    exact Prod.ext hp1.symm hp2.symm
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    unfold rootProfile at hy
    simp only [Prod.mk.injEq] at hy
    obtain ⟨hcard, hsup⟩ := hy
    obtain ⟨x, -, hx2⟩ := (Finset.le_sup_iff (show (0 : ℕ) < 2 by norm_num)).mp hsup.ge
    have hcard_le_one_of_tri : isTri3 y.1 y.2.1 y.2.2 x = true → False := by
      intro htri
      have hsub : (Finset.univ.filter (fun r : F => isRoot3 y.1 y.2.1 y.2.2 r))
          ⊆ {x} := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        simp only [Finset.mem_singleton]
        exact tri_root htri ((isRoot3_iff _ _ _ _).mp hz)
      have hle := Finset.card_le_card hsub
      rw [hcard, Finset.card_singleton] at hle
      omega
    split_ifs at hx2 with h1 h2 h3
    · exact absurd h1 hcard_le_one_of_tri
    · rw [Bool.and_eq_true] at h2
      obtain ⟨hb, hc⟩ := by simpa [isDbl3] using h2.2
      refine ⟨(x, -y.1 - 2 * x), Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩, ?_⟩
      · intro hxeq
        refine hcard_le_one_of_tri ?_
        simp only [isTri3, decide_eq_true_eq]
        refine ⟨?_, ?_, ?_⟩
        · linear_combination hxeq
        · linear_combination hb - 2 * x * hxeq
        · linear_combination hc + x ^ 2 * hxeq
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · change -(2 * x + (-y.1 - 2 * x)) = y.1
          ring
        · exact hb.symm
        · exact hc.symm
    · omega
    · omega

private lemma count_31 : classCount F (3, 1) = (Fintype.card F).choose 3 := by
  classical
  unfold classCount
  rw [← Finset.card_univ (α := F), ← Finset.card_powersetCard]
  refine Finset.card_bij (fun y _ =>
    Finset.univ.filter (fun x : F => isRoot3 y.1 y.2.1 y.2.2 x)) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    unfold rootProfile at hy
    simp only [Prod.mk.injEq] at hy
    exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hy.1⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₁
    unfold rootProfile at hy₁
    simp only [Prod.mk.injEq] at hy₁
    obtain ⟨r, s, t, hrs, hrt, hst, hS⟩ := Finset.card_eq_three.mp hy₁.1
    have hmem : ∀ z ∈ ({r, s, t} : Finset F),
        z ^ 3 + y₁.1 * z ^ 2 + y₁.2.1 * z + y₁.2.2 = 0
          ∧ z ^ 3 + y₂.1 * z ^ 2 + y₂.2.1 * z + y₂.2.2 = 0 := by
      intro z hz
      rw [← hS] at hz
      constructor
      · exact (isRoot3_iff _ _ _ _).mp (Finset.mem_filter.mp hz).2
      · rw [heq] at hz
        exact (isRoot3_iff _ _ _ _).mp (Finset.mem_filter.mp hz).2
    have hr := hmem r (by simp)
    have hs := hmem s (by simp)
    have ht := hmem t (by simp)
    obtain ⟨ha₁, hb₁, hc₁⟩ := vieta_of_roots hrs hrt hst hr.1 hs.1 ht.1
    obtain ⟨ha₂, hb₂, hc₂⟩ := vieta_of_roots hrs hrt hst hr.2 hs.2 ht.2
    exact Prod.ext (ha₁.trans ha₂.symm)
      (Prod.ext (hb₁.trans hb₂.symm) (hc₁.trans hc₂.symm))
  · intro S hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨r, s, t, hrs, hrt, hst, rfl⟩ := Finset.card_eq_three.mp hcard
    refine ⟨((-(r + s + t), r * s + r * t + s * t, -(r * s * t)) : F × F × F),
      ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact profile_distinct hrs hrt hst
    · change Finset.univ.filter (fun x : F =>
        isRoot3 (-(r + s + t)) (r * s + r * t + s * t) (-(r * s * t)) x)
          = {r, s, t}
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      rw [isRoot3_iff, vieta_eval]
      constructor
      · intro hx
        rcases mul_eq_zero.mp hx with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact Or.inl (sub_eq_zero.mp h'')
          · exact Or.inr (Or.inl (sub_eq_zero.mp h''))
        · exact Or.inr (Or.inr (sub_eq_zero.mp h'))
      · rintro (rfl | rfl | rfl) <;> ring

end Counts

/-! ### The census, generic-F (the nine-point roster consumes by instantiation) -/

/-- the census at ONE point (the nine-point roster instantiates F at
ZMod 2/3/5/7/11/13 and F4/F8/F9 — §8's decide budget). REPAIRED middle
conjunct: (2,2) ↦ T21 (was TH12, the (1,1) polynomial — see file header);
PROVED for every finite field F. -/
theorem rootTable_census (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (q : ℚ) (hq : (Fintype.card F : ℚ) = q) :
    (classCount F (3, 1) : ℚ) = TH3.eval q ∧
    (classCount F (2, 2) : ℚ) = T21.eval q ∧
    (classCount F (1, 3) : ℚ) = T3.eval q := by
  classical
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have h1 : 1 ≤ Fintype.card F := by omega
  have c1 : ((Fintype.card F - 1 : ℕ) : ℚ) = q - 1 := by
    rw [Nat.cast_sub h1, hq, Nat.cast_one]
  have c2 : ((Fintype.card F - 2 : ℕ) : ℚ) = q - 2 := by
    rw [Nat.cast_sub h2, hq, Nat.cast_ofNat]
  refine ⟨?_, ?_, ?_⟩
  · have h6 : 6 * classCount F (3, 1)
        = Fintype.card F * (Fintype.card F - 1) * (Fintype.card F - 2) := by
      rw [count_31]
      have hd := Nat.descFactorial_eq_factorial_mul_choose (Fintype.card F) 3
      have hfact : Nat.factorial 3 = 6 := by norm_num [Nat.factorial]
      rw [hfact] at hd
      rw [← hd]
      simp [Nat.descFactorial]
      ring
    have hcast : (6 : ℚ) * (classCount F (3, 1) : ℚ) = q * (q - 1) * (q - 2) := by
      calc (6 : ℚ) * (classCount F (3, 1) : ℚ)
          = ((6 * classCount F (3, 1) : ℕ) : ℚ) := by push_cast; ring
        _ = ((Fintype.card F * (Fintype.card F - 1) * (Fintype.card F - 2) : ℕ) : ℚ) := by
            rw [h6]
        _ = q * (q - 1) * (q - 2) := by rw [Nat.cast_mul, Nat.cast_mul, c1, c2, hq]
    have hTH3 : TH3.eval q = 1 / 6 * (q * (q - 1) * (q - 2)) := by simp [TH3]
    rw [hTH3]; linarith
  · have hcast : (classCount F (2, 2) : ℚ) = q * q - q := by
      rw [count_22, Nat.cast_sub (Nat.le_mul_of_pos_left _ (by omega)),
        Nat.cast_mul, hq]
    have hT21 : T21.eval q = q * (q - 1) := by simp [T21]
    rw [hcast, hT21]; ring
  · rw [count_13, hq]
    simp [T3]

end LeanUrat.MovesV
