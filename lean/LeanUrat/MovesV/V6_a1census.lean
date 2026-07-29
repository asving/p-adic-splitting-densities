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
    3-subsets of F.
    M3 COMPLETION (round-4 ratification verdict, 2026-07-29): the census is
    now SEMANTICALLY COMPLETE — `rootTable_census_TH12` ((1,1): one simple
    root × root-free quadratic, via the product bijection over the
    quadratic root-count partition), `rootTable_census_TH3c` ((0,0):
    rootless cubics, via `profile_mem_five` exhaustiveness + the
    `census_partition` complement), and the five-conjunct wrapper
    `rootTable_census_complete`; all generic-F, no numeric roster cited. -/
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

/-! ### The remaining two classes: (1,1) ↦ TH12 and (0,0) ↦ TH3c
(M3, round-4 ratification verdict 2026-07-29 — "the sealed census claim is
still not represented semantically in both directions"): the FOURTH count
(profile (1,1) = one simple root × root-free quadratic cofactor) via the
(root, root-free quadratic) product bijection, and the FIFTH (profile
(0,0) = rootless cubics) via PROFILE EXHAUSTIVENESS + the partition
complement.  With `rootTable_census` the five-class census is semantically
COMPLETE (`rootTable_census_complete`), for EVERY finite field F.
BOUNDARY RECORD: the nine-point numeric roster (the campaign's "178 exact
checks" family) remains EXTERNAL EVIDENCE ONLY — nothing at this semantic
layer cites it, and it certifies nothing here; these theorems are
generic-F kernel content. -/

open Classical in
/-- the number of ROOT-FREE monic quadratics z² + bz + c over F (the
char-free irreducibility count at the census's root level). -/
private noncomputable def quadNRCount (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] : ℕ :=
  (Finset.univ.filter
    (fun p : F × F => ∀ x : F, x ^ 2 + p.1 * x + p.2 ≠ 0)).card

section CountsB
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- tri at x forces x to be a root (char-free). -/
private lemma isTri3_isRoot3 {a b c x : F} (h : isTri3 a b c x = true) :
    isRoot3 a b c x = true := by
  obtain ⟨h1, h2, h3⟩ := by simpa [isTri3] using h
  rw [isRoot3_iff, h1, h2, h3]; ring

/-- dbl at r whose cofactor root collapses onto r is tri (char-free). -/
private lemma tri_of_dbl_self {a b c r : F} (hs : -a - 2 * r = r)
    (hdbl : isDbl3 a b c r = true) : isTri3 a b c r = true := by
  obtain ⟨hb', hc'⟩ := by simpa [isDbl3] using hdbl
  simp only [isTri3, decide_eq_true_eq]
  refine ⟨by linear_combination -hs, ?_, ?_⟩
  · rw [hb']; linear_combination (2 * r) * hs
  · rw [hc']; linear_combination (-(r ^ 2)) * hs

/-- a monic quadratic has at most two roots (char-free). -/
private lemma quad_roots_le_two (b c : F) :
    (Finset.univ.filter (fun x : F => x ^ 2 + b * x + c = 0)).card ≤ 2 := by
  by_contra h
  rw [not_le, Finset.two_lt_card_iff] at h
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
  have e1 : x + y + b = 0 := by
    have h' : (x - y) * (x + y + b) = 0 := by linear_combination hx - hy
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (sub_eq_zero.mp h'') hxy
    · exact h''
  have e2 : x + z + b = 0 := by
    have h' : (x - z) * (x + z + b) = 0 := by linear_combination hx - hz
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd (sub_eq_zero.mp h'') hxz
    · exact h''
  exact hyz (by linear_combination e1 - e2)

/-- the quadratic root-count partition: q² = (root-free) + (double) + (split).
Char-free: the double-root fiber is parametrized by F (u ↦ (z−u)²), the
two-root fiber by the 2-subsets of F (Vieta). -/
private lemma quad_card :
    Fintype.card F * Fintype.card F
      = quadNRCount F + Fintype.card F + (Fintype.card F).choose 2 := by
  classical
  have H := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (F × F)))
    (t := ({0, 1, 2} : Finset ℕ))
    (f := fun p : F × F =>
      (Finset.univ.filter (fun x : F => x ^ 2 + p.1 * x + p.2 = 0)).card)
    (fun p _ => by
      have h := quad_roots_le_two (F := F) p.1 p.2
      have h3 : (Finset.univ.filter
            (fun x : F => x ^ 2 + p.1 * x + p.2 = 0)).card = 0
          ∨ (Finset.univ.filter
            (fun x : F => x ^ 2 + p.1 * x + p.2 = 0)).card = 1
          ∨ (Finset.univ.filter
            (fun x : F => x ^ 2 + p.1 * x + p.2 = 0)).card = 2 := by omega
      simpa using h3)
  rw [Finset.card_univ, Fintype.card_prod] at H
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at H
  -- fiber 0 IS the root-free count
  have h0 : (Finset.univ.filter (fun p : F × F =>
      (Finset.univ.filter (fun x : F => x ^ 2 + p.1 * x + p.2 = 0)).card
        = 0)).card = quadNRCount F := by
    unfold quadNRCount
    congr 1
    ext p
    simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  -- fiber 1 ↔ F (the double root)
  have h1 : (Finset.univ.filter (fun p : F × F =>
      (Finset.univ.filter (fun x : F => x ^ 2 + p.1 * x + p.2 = 0)).card
        = 1)).card = Fintype.card F := by
    rw [← Finset.card_univ (α := F)]
    symm
    refine Finset.card_bij (fun u _ => ((-(2 * u), u * u) : F × F)) ?_ ?_ ?_
    · intro u _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hfil : (Finset.univ.filter
          (fun x : F => x ^ 2 + (-(2 * u)) * x + u * u = 0)) = {u} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro hx
          have h2 : (x - u) ^ 2 = 0 := by linear_combination hx
          exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
        · rintro rfl; ring
      rw [hfil, Finset.card_singleton]
    · intro u₁ _ u₂ _ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hb, hc⟩ := heq
      have h2 : (u₁ - u₂) ^ 2 = 0 := by linear_combination hc + u₂ * hb
      exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hp
      have hur : u ^ 2 + p.1 * u + p.2 = 0 := by
        have hm : u ∈ Finset.univ.filter
            (fun x : F => x ^ 2 + p.1 * x + p.2 = 0) := by
          rw [hu]; exact Finset.mem_singleton_self u
        exact (Finset.mem_filter.mp hm).2
      have hv : (-p.1 - u) ^ 2 + p.1 * (-p.1 - u) + p.2 = 0 := by
        linear_combination hur
      have hvu : -p.1 - u = u := by
        have hm : (-p.1 - u) ∈ Finset.univ.filter
            (fun x : F => x ^ 2 + p.1 * x + p.2 = 0) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hv
        rw [hu] at hm; simpa using hm
      refine ⟨u, Finset.mem_univ u, Prod.ext ?_ ?_⟩
      · show -(2 * u) = p.1; linear_combination hvu
      · show u * u = p.2; linear_combination -hur - u * hvu
  -- fiber 2 ↔ the 2-subsets (Vieta)
  have h2c : (Finset.univ.filter (fun p : F × F =>
      (Finset.univ.filter (fun x : F => x ^ 2 + p.1 * x + p.2 = 0)).card
        = 2)).card = (Fintype.card F).choose 2 := by
    rw [← Finset.card_univ (α := F), ← Finset.card_powersetCard]
    refine Finset.card_bij (fun p _ =>
      Finset.univ.filter (fun x : F => x ^ 2 + p.1 * x + p.2 = 0)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hp⟩
    · intro p₁ h₁ p₂ h₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁
      obtain ⟨x, y, hxy, hS⟩ := Finset.card_eq_two.mp h₁
      have hmem : ∀ z ∈ ({x, y} : Finset F),
          (z ^ 2 + p₁.1 * z + p₁.2 = 0) ∧ (z ^ 2 + p₂.1 * z + p₂.2 = 0) := by
        intro z hz
        rw [← hS] at hz
        refine ⟨(Finset.mem_filter.mp hz).2, ?_⟩
        rw [heq] at hz
        exact (Finset.mem_filter.mp hz).2
      have hx := hmem x (by simp)
      have hy := hmem y (by simp)
      have hb1 : p₁.1 = -(x + y) := by
        have h' : (x - y) * (x + y + p₁.1) = 0 := by
          linear_combination hx.1 - hy.1
        rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd (sub_eq_zero.mp h'') hxy
        · linear_combination h''
      have hb2 : p₂.1 = -(x + y) := by
        have h' : (x - y) * (x + y + p₂.1) = 0 := by
          linear_combination hx.2 - hy.2
        rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd (sub_eq_zero.mp h'') hxy
        · linear_combination h''
      have hc1 : p₁.2 = x * y := by linear_combination hx.1 - x * hb1
      have hc2 : p₂.2 = x * y := by linear_combination hx.2 - x * hb2
      exact Prod.ext (hb1.trans hb2.symm) (hc1.trans hc2.symm)
    · intro S hS
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      have hfil : (Finset.univ.filter
          (fun w : F => w ^ 2 + (-(x + y)) * w + x * y = 0)) = {x, y} := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hw
          have h0' : (w - x) * (w - y) = 0 := by linear_combination hw
          rcases mul_eq_zero.mp h0' with h' | h'
          · exact Or.inl (sub_eq_zero.mp h')
          · exact Or.inr (sub_eq_zero.mp h')
        · rintro (rfl | rfl) <;> ring
      refine ⟨((-(x + y), x * y) : F × F), ?_, hfil⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hfil, Finset.card_insert_of_notMem (by simpa using hxy),
        Finset.card_singleton]
  rw [h0, h1, h2c] at H
  omega

/-- profile of (z−r)·(root-free quadratic): exactly (1, 1) — the (1,1)-class
membership half of the product bijection. -/
private lemma profile_one_simple {r b' c' : F}
    (hnr : ∀ x : F, x ^ 2 + b' * x + c' ≠ 0) :
    rootProfile (b' - r) (c' - r * b') (-(r * c')) = (1, 1) := by
  classical
  have heval : ∀ x : F,
      x ^ 3 + (b' - r) * x ^ 2 + (c' - r * b') * x + (-(r * c'))
        = (x - r) * (x ^ 2 + b' * x + c') := by intro x; ring
  have hroot_iff : ∀ x : F,
      isRoot3 (b' - r) (c' - r * b') (-(r * c')) x = true ↔ x = r := by
    intro x
    rw [isRoot3_iff, heval x]
    constructor
    · intro hx
      rcases mul_eq_zero.mp hx with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' (hnr x)
    · rintro rfl; ring
  have hnotri : ∀ x : F,
      ¬ isTri3 (b' - r) (c' - r * b') (-(r * c')) x = true := by
    intro x htri
    have hxr : x = r := (hroot_iff x).mp (isTri3_isRoot3 htri)
    subst hxr
    obtain ⟨h1, h2, -⟩ := by simpa [isTri3] using htri
    apply hnr x
    have hb'' : b' = -(2 * x) := by linear_combination h1
    have hc'' : c' = x ^ 2 := by linear_combination h2 + x * hb''
    rw [hb'', hc'']; ring
  have hnodbl : ¬ isDbl3 (b' - r) (c' - r * b') (-(r * c')) r = true := by
    intro hdbl
    obtain ⟨h1, -⟩ := by simpa [isDbl3] using hdbl
    exact hnr r (by linear_combination h1)
  unfold rootProfile
  refine Prod.ext ?_ ?_
  · have hfil : (Finset.univ.filter
        (fun x : F => isRoot3 (b' - r) (c' - r * b') (-(r * c')) x)) = {r} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      exact hroot_iff x
    rw [hfil, Finset.card_singleton]
  · refine le_antisymm (Finset.sup_le fun x _ => ?_) ?_
    · split_ifs with h1 h2 h3
      · exact absurd h1 (hnotri x)
      · rw [Bool.and_eq_true] at h2
        have hxr : x = r := (hroot_iff x).mp h2.1
        subst hxr
        exact absurd h2.2 hnodbl
      · exact le_refl 1
      · omega
    · have hle := Finset.le_sup (f := fun x : F =>
        if isTri3 (b' - r) (c' - r * b') (-(r * c')) x then 3
        else if isRoot3 (b' - r) (c' - r * b') (-(r * c')) x
            && isDbl3 (b' - r) (c' - r * b') (-(r * c')) x then 2
        else if isRoot3 (b' - r) (c' - r * b') (-(r * c')) x then 1 else 0)
        (Finset.mem_univ r)
      have hterm : (if isTri3 (b' - r) (c' - r * b') (-(r * c')) r then 3
          else if isRoot3 (b' - r) (c' - r * b') (-(r * c')) r
              && isDbl3 (b' - r) (c' - r * b') (-(r * c')) r then 2
          else if isRoot3 (b' - r) (c' - r * b') (-(r * c')) r
            then 1 else 0) = 1 := by
        rw [if_neg (by simpa using hnotri r),
          if_neg (by rw [Bool.and_eq_true]; exact fun h => hnodbl h.2),
          if_pos ((hroot_iff r).mpr rfl)]
      omega

/-- the (1,1) class counts as (root) × (root-free quadratic). -/
private lemma count_11 :
    classCount F (1, 1) = Fintype.card F * quadNRCount F := by
  classical
  unfold classCount quadNRCount
  rw [← Finset.card_univ (α := F), ← Finset.card_product]
  symm
  refine Finset.card_bij (fun rp _ =>
    ((rp.2.1 - rp.1, rp.2.2 - rp.1 * rp.2.1, -(rp.1 * rp.2.2)) : F × F × F))
    ?_ ?_ ?_
  · rintro ⟨r, b', c'⟩ hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact profile_one_simple hp
  · rintro ⟨r₁, b₁, c₁⟩ h₁ ⟨r₂, b₂, c₂⟩ h₂ heq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and] at h₁ h₂
    simp only [Prod.mk.injEq] at heq
    obtain ⟨ha, hb, hc⟩ := heq
    -- r₁ is a root of both cubics; cubic₂'s only root is r₂
    have hr1root : r₁ ^ 3 + (b₂ - r₂) * r₁ ^ 2 + (c₂ - r₂ * b₂) * r₁
        + (-(r₂ * c₂)) = 0 := by
      rw [← ha, ← hb, ← hc]; ring
    have hfac : (r₁ - r₂) * (r₁ ^ 2 + b₂ * r₁ + c₂) = 0 := by
      linear_combination hr1root
    have hr12 : r₁ = r₂ := by
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' (h₂ r₁)
    subst hr12
    have hb12 : b₁ = b₂ := by linear_combination ha
    subst hb12
    have hc12 : c₁ = c₂ := by linear_combination hb
    subst hc12
    rfl
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    unfold rootProfile at hy
    simp only [Prod.mk.injEq] at hy
    obtain ⟨hcard, hsup⟩ := hy
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
    have hroot : isRoot3 y.1 y.2.1 y.2.2 r = true := by
      have hm : r ∈ Finset.univ.filter
          (fun x : F => isRoot3 y.1 y.2.1 y.2.2 x) := by
        rw [hr]; exact Finset.mem_singleton_self r
      simpa using (Finset.mem_filter.mp hm).2
    have hroot' := (isRoot3_iff _ _ _ _).mp hroot
    refine ⟨(r, (y.1 + r, y.2.1 + r * y.1 + r ^ 2)), ?_, ?_⟩
    · -- the cofactor is root-free: a cofactor root forces a double root at r,
      -- contradicting sup = 1
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and]
      intro x hx
      have hxroot : isRoot3 y.1 y.2.1 y.2.2 x = true := by
        rw [isRoot3_iff]
        linear_combination (x - r) * hx + hroot'
      have hxr : x = r := by
        have hm : x ∈ Finset.univ.filter
            (fun w : F => isRoot3 y.1 y.2.1 y.2.2 w) := by
          simp [hxroot]
        rw [hr] at hm; simpa using hm
      subst hxr
      have hdbl : isDbl3 y.1 y.2.1 y.2.2 x = true := by
        simp only [isDbl3, decide_eq_true_eq]
        exact ⟨by linear_combination hx, by linear_combination hroot' - x * hx⟩
      have hge : 2 ≤ Finset.univ.sup (fun w : F =>
          if isTri3 y.1 y.2.1 y.2.2 w then 3
          else if isRoot3 y.1 y.2.1 y.2.2 w && isDbl3 y.1 y.2.1 y.2.2 w then 2
          else if isRoot3 y.1 y.2.1 y.2.2 w then 1 else 0) := by
        have hle := Finset.le_sup (f := fun w : F =>
          if isTri3 y.1 y.2.1 y.2.2 w then 3
          else if isRoot3 y.1 y.2.1 y.2.2 w && isDbl3 y.1 y.2.1 y.2.2 w then 2
          else if isRoot3 y.1 y.2.1 y.2.2 w then 1 else 0) (Finset.mem_univ x)
        by_cases htri : isTri3 y.1 y.2.1 y.2.2 x = true
        · rw [if_pos htri] at hle; omega
        · rw [if_neg htri,
            if_pos (by rw [Bool.and_eq_true]; exact ⟨hroot, hdbl⟩)] at hle
          exact hle
      rw [hsup] at hge
      omega
    · refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show y.1 + r - r = y.1; ring
      · show y.2.1 + r * y.1 + r ^ 2 - r * (y.1 + r) = y.2.1; ring
      · show -(r * (y.2.1 + r * y.1 + r ^ 2)) = y.2.2
        linear_combination -hroot'

/-- a monic cubic has at most three roots (char-free, via Vieta). -/
private lemma roots_card_le_three (a b c : F) :
    (Finset.univ.filter (fun x : F => isRoot3 a b c x)).card ≤ 3 := by
  by_contra hgt
  rw [not_le] at hgt
  have h2lt : 2 < (Finset.univ.filter (fun x : F => isRoot3 a b c x)).card := by
    omega
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp h2lt
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
  obtain ⟨ha, hb, hc⟩ := vieta_of_roots hxy hxz hyz
    ((isRoot3_iff _ _ _ _).mp hx) ((isRoot3_iff _ _ _ _).mp hy)
    ((isRoot3_iff _ _ _ _).mp hz)
  have hsub : (Finset.univ.filter (fun w : F => isRoot3 a b c w))
      ⊆ ({x, y, z} : Finset F) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hw' := (isRoot3_iff _ _ _ _).mp hw
    rw [ha, hb, hc, vieta_eval] at hw'
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases mul_eq_zero.mp hw' with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact Or.inl (sub_eq_zero.mp h'')
      · exact Or.inr (Or.inl (sub_eq_zero.mp h''))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h'))
  have hle := Finset.card_le_card hsub
  have h3 : ({x, y, z} : Finset F).card ≤ 3 := by
    apply le_trans (Finset.card_insert_le _ _)
    have := Finset.card_insert_le y ({z} : Finset F)
    simp only [Finset.card_singleton] at this
    omega
  omega

/-- PROFILE EXHAUSTIVENESS: every monic cubic's (root count, max
multiplicity) profile is one of the five census classes. -/
private lemma profile_mem_five (a b c : F) :
    rootProfile a b c
      ∈ ({((0 : ℕ), (0 : ℕ)), (1, 1), (2, 2), (3, 1), (1, 3)}
          : Finset (ℕ × ℕ)) := by
  classical
  have hle3 := roots_card_le_three a b c
  have hcases : (Finset.univ.filter (fun x : F => isRoot3 a b c x)).card = 0
      ∨ (Finset.univ.filter (fun x : F => isRoot3 a b c x)).card = 1
      ∨ (Finset.univ.filter (fun x : F => isRoot3 a b c x)).card = 2
      ∨ (Finset.univ.filter (fun x : F => isRoot3 a b c x)).card = 3 := by
    omega
  rcases hcases with hc0 | hc1 | hc2 | hc3
  · -- (0, 0): no roots, sup = 0
    have hempty := Finset.card_eq_zero.mp hc0
    have hnoroot : ∀ x : F, ¬ isRoot3 a b c x = true := by
      intro x hx
      have hm : x ∈ Finset.univ.filter (fun w : F => isRoot3 a b c w) := by
        simp [hx]
      rw [hempty] at hm
      exact absurd hm (Finset.notMem_empty x)
    have hpr : rootProfile a b c = (0, 0) := by
      unfold rootProfile
      refine Prod.ext hc0 ?_
      refine le_antisymm (Finset.sup_le fun x _ => ?_) (Nat.zero_le _)
      split_ifs with h1 h2 h3
      · exact absurd (isTri3_isRoot3 h1) (hnoroot x)
      · rw [Bool.and_eq_true] at h2; exact absurd h2.1 (hnoroot x)
      · exact absurd h3 (hnoroot x)
      · exact le_refl 0
    rw [hpr]; decide
  · -- one root r: (1, 3) if tri, else (1, 1); the dbl-only case collapses to tri
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hc1
    have hroot_r : isRoot3 a b c r = true := by
      have hm : r ∈ Finset.univ.filter (fun w : F => isRoot3 a b c w) := by
        rw [hr]; exact Finset.mem_singleton_self r
      simpa using (Finset.mem_filter.mp hm).2
    have huniq : ∀ x : F, isRoot3 a b c x = true → x = r := by
      intro x hx
      have hm : x ∈ Finset.univ.filter (fun w : F => isRoot3 a b c w) := by
        simp [hx]
      rw [hr] at hm; simpa using hm
    by_cases htri : isTri3 a b c r = true
    · have hpr : rootProfile a b c = (1, 3) := by
        unfold rootProfile
        refine Prod.ext hc1 ?_
        refine le_antisymm (Finset.sup_le fun x _ => by split_ifs <;> omega) ?_
        have hle := Finset.le_sup (f := fun x : F =>
          if isTri3 a b c x then 3
          else if isRoot3 a b c x && isDbl3 a b c x then 2
          else if isRoot3 a b c x then 1 else 0) (Finset.mem_univ r)
        simpa [htri] using hle
      rw [hpr]; decide
    · have hnodbl : ¬ isDbl3 a b c r = true := by
        intro hdbl
        have hs₀root : isRoot3 a b c (-a - 2 * r) = true := by
          rw [isRoot3_iff, dbl_eval hdbl]; ring
        exact htri (tri_of_dbl_self (huniq _ hs₀root) hdbl)
      have hnotri : ∀ x : F, ¬ isTri3 a b c x = true := by
        intro x htrix
        have hxr : x = r := huniq x (isTri3_isRoot3 htrix)
        rw [hxr] at htrix
        exact htri htrix
      have hpr : rootProfile a b c = (1, 1) := by
        unfold rootProfile
        refine Prod.ext hc1 ?_
        refine le_antisymm (Finset.sup_le fun x _ => ?_) ?_
        · split_ifs with h1 h2 h3
          · exact absurd h1 (hnotri x)
          · rw [Bool.and_eq_true] at h2
            have hxr : x = r := huniq x h2.1
            rw [hxr] at h2
            exact absurd h2.2 hnodbl
          · exact le_refl 1
          · omega
        · have hle := Finset.le_sup (f := fun x : F =>
            if isTri3 a b c x then 3
            else if isRoot3 a b c x && isDbl3 a b c x then 2
            else if isRoot3 a b c x then 1 else 0) (Finset.mem_univ r)
          have hterm : (if isTri3 a b c r then 3
              else if isRoot3 a b c r && isDbl3 a b c r then 2
              else if isRoot3 a b c r then 1 else 0) = 1 := by
            rw [if_neg (by simpa using htri),
              if_neg (by rw [Bool.and_eq_true]; exact fun h => hnodbl h.2),
              if_pos hroot_r]
          omega
      rw [hpr]; decide
  · -- two roots: the third Vieta root collapses onto one of them → (2, 2)
    obtain ⟨x, y, hxy, hS⟩ := Finset.card_eq_two.mp hc2
    have hxr : isRoot3 a b c x = true := by
      have hm : x ∈ Finset.univ.filter (fun w : F => isRoot3 a b c w) := by
        rw [hS]; simp
      simpa using (Finset.mem_filter.mp hm).2
    have hyr : isRoot3 a b c y = true := by
      have hm : y ∈ Finset.univ.filter (fun w : F => isRoot3 a b c w) := by
        rw [hS]; simp
      simpa using (Finset.mem_filter.mp hm).2
    have hx' := (isRoot3_iff _ _ _ _).mp hxr
    have hy' := (isRoot3_iff _ _ _ _).mp hyr
    have e1 : x ^ 2 + x * y + y ^ 2 + a * (x + y) + b = 0 := by
      have h' : (x - y) * (x ^ 2 + x * y + y ^ 2 + a * (x + y) + b) = 0 := by
        linear_combination hx' - hy'
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd (sub_eq_zero.mp h'') hxy
      · exact h''
    have htr : isRoot3 a b c (-a - x - y) = true := by
      rw [isRoot3_iff]
      have heval : (-a - x - y) ^ 3 + a * (-a - x - y) ^ 2 + b * (-a - x - y)
          + c = ((-a - x - y) - x) * ((-a - x - y) - y)
            * ((-a - x - y) - (-a - x - y)) := by
        linear_combination ((-a - x - y) - x) * e1 + hx'
      rw [heval]; ring
    have htmem : -a - x - y = x ∨ -a - x - y = y := by
      have hm : (-a - x - y) ∈ Finset.univ.filter
          (fun w : F => isRoot3 a b c w) := by
        simp [htr]
      rw [hS] at hm
      simpa using hm
    rcases htmem with ht | ht
    · have ha' : a = -(2 * x + y) := by linear_combination -ht
      subst ha'
      have hb' : b = x * x + 2 * x * y := by linear_combination e1
      subst hb'
      have hc' : c = -(x * x * y) := by linear_combination hx'
      subst hc'
      rw [profile_dblpair hxy]; decide
    · have ha' : a = -(2 * y + x) := by linear_combination -ht
      subst ha'
      have hb' : b = y * y + 2 * y * x := by linear_combination e1
      subst hb'
      have hc' : c = -(y * y * x) := by linear_combination hx'
      subst hc'
      rw [profile_dblpair (Ne.symm hxy)]; decide
  · -- three roots: Vieta → (3, 1)
    obtain ⟨x, y, z, hxy, hxz, hyz, hS⟩ := Finset.card_eq_three.mp hc3
    have hmem : ∀ w ∈ ({x, y, z} : Finset F),
        w ^ 3 + a * w ^ 2 + b * w + c = 0 := by
      intro w hw
      rw [← hS] at hw
      have := (Finset.mem_filter.mp hw).2
      exact (isRoot3_iff _ _ _ _).mp (by simpa using this)
    obtain ⟨ha', hb', hc'⟩ := vieta_of_roots hxy hxz hyz
      (hmem x (by simp)) (hmem y (by simp)) (hmem z (by simp))
    subst ha'; subst hb'; subst hc'
    rw [profile_distinct hxy hxz hyz]; decide

/-- THE FIVE-CLASS PARTITION: the census classes exhaust the q³ cubics. -/
theorem census_partition (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    classCount F (0, 0) + classCount F (1, 1) + classCount F (2, 2)
      + classCount F (3, 1) + classCount F (1, 3) = Fintype.card F ^ 3 := by
  classical
  have hcc : ∀ pr : ℕ × ℕ, (Finset.univ.filter
      (fun a : F × F × F => rootProfile a.1 a.2.1 a.2.2 = pr)).card
        = classCount F pr := by
    intro pr
    unfold classCount
    refine Finset.card_bij (fun a _ => a) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha
    · intro a _ b _ h
      exact h
    · intro b hb
      refine ⟨b, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact hb
  have H := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (F × F × F)))
    (t := ({((0 : ℕ), (0 : ℕ)), (1, 1), (2, 2), (3, 1), (1, 3)}
        : Finset (ℕ × ℕ)))
    (f := fun y : F × F × F => rootProfile y.1 y.2.1 y.2.2)
    (fun y _ => profile_mem_five y.1 y.2.1 y.2.2)
  rw [Finset.card_univ,
    show Fintype.card (F × F × F) = Fintype.card F ^ 3 from by
      rw [Fintype.card_prod, Fintype.card_prod]; ring] at H
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at H
  simp only [hcc] at H
  omega

end CountsB

/-- (M3, round 4) THE FOURTH SEMANTIC CLASS COUNT — profile (1,1), one
simple root × root-free (irreducible) quadratic cofactor: equals TH12,
for every finite field F. -/
theorem rootTable_census_TH12 (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (q : ℚ) (hq : (Fintype.card F : ℚ) = q) :
    (classCount F (1, 1) : ℚ) = TH12.eval q := by
  classical
  have hcnt := count_11 (F := F)
  have hquad := quad_card (F := F)
  have h1le : 1 ≤ Fintype.card F := Fintype.card_pos
  -- 2·choose 2 = q(q−1) in ℚ
  have hch : 2 * ((Fintype.card F).choose 2)
      = Fintype.card F * (Fintype.card F - 1) := by
    have hd := Nat.descFactorial_eq_factorial_mul_choose (Fintype.card F) 2
    have hfact : Nat.factorial 2 = 2 := by norm_num [Nat.factorial]
    rw [hfact] at hd
    rw [← hd]
    simp [Nat.descFactorial]
    ring
  have hsub : ((Fintype.card F - 1 : ℕ) : ℚ) = q - 1 := by
    rw [Nat.cast_sub h1le, hq, Nat.cast_one]
  have hchcast : 2 * (((Fintype.card F).choose 2 : ℕ) : ℚ) = q * (q - 1) := by
    calc 2 * (((Fintype.card F).choose 2 : ℕ) : ℚ)
        = ((2 * (Fintype.card F).choose 2 : ℕ) : ℚ) := by push_cast; ring
      _ = ((Fintype.card F * (Fintype.card F - 1) : ℕ) : ℚ) := by rw [hch]
      _ = q * (q - 1) := by rw [Nat.cast_mul, hsub, hq]
  have hcast := congrArg (fun k : ℕ => (k : ℚ)) hquad
  push_cast at hcast
  rw [hq] at hcast
  -- 2·NR = q² − q
  have h2 : 2 * ((quadNRCount F : ℕ) : ℚ) = q ^ 2 - q := by
    linear_combination -2 * hcast - hchcast
  have hc11 : (classCount F (1, 1) : ℚ) = q * ((quadNRCount F : ℕ) : ℚ) := by
    rw [hcnt]
    push_cast
    rw [hq]
  rw [hc11]
  have hTH12 : TH12.eval q = 1 / 2 * (q ^ 2 * (q - 1)) := by simp [TH12]
  rw [hTH12]
  linear_combination (q / 2) * h2

/-- (M3, round 4) THE FIFTH SEMANTIC CLASS COUNT — profile (0,0), the
rootless (irreducible) cubics: equals TH3c, for every finite field F, by
the partition complement against the four proved counts. -/
theorem rootTable_census_TH3c (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (q : ℚ) (hq : (Fintype.card F : ℚ) = q) :
    (classCount F (0, 0) : ℚ) = TH3c.eval q := by
  classical
  obtain ⟨h31, h22, h13⟩ := rootTable_census F q hq
  have h11 := rootTable_census_TH12 F q hq
  have hpart := census_partition F
  have hcast := congrArg (fun k : ℕ => (k : ℚ)) hpart
  push_cast at hcast
  rw [hq] at hcast
  have hid := congrArg (fun P : Polynomial ℚ => P.eval q) rootTable_identities
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X] at hid
  linarith [hcast, hid, h31, h22, h13, h11]

/-- (M3, round 4) THE FIVE-CLASS CENSUS, COMPLETE: every class count equals
its blueprint polynomial, for every finite field F — TH3 ↦ (3,1),
TH12 ↦ (1,1), TH3c ↦ (0,0), T21 ↦ (2,2), T3 ↦ (1,3); the classes partition
the q³ cubics (`census_partition`). -/
theorem rootTable_census_complete (F : Type*) [Field F] [Fintype F]
    [DecidableEq F] (q : ℚ) (hq : (Fintype.card F : ℚ) = q) :
    (classCount F (3, 1) : ℚ) = TH3.eval q ∧
    (classCount F (1, 1) : ℚ) = TH12.eval q ∧
    (classCount F (0, 0) : ℚ) = TH3c.eval q ∧
    (classCount F (2, 2) : ℚ) = T21.eval q ∧
    (classCount F (1, 3) : ℚ) = T3.eval q :=
  ⟨(rootTable_census F q hq).1, rootTable_census_TH12 F q hq,
   rootTable_census_TH3c F q hq, (rootTable_census F q hq).2.1,
   (rootTable_census F q hq).2.2⟩

end LeanUrat.MovesV
