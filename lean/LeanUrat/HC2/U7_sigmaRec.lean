/-
Unit U7.mkSigma_init_rec  (HC-2 campaign, E-phase — blueprint §5 Layer A; two lemmas)
moves_ref: MovesC `JetSetup.init`/`recursion` field types.
deps: D7, C0.pinTransport (PROVED), S.Theta_uni.  difficulty: medium.
hypothesis_fields: none.
sketch: init is definitional (`topLocus`); recursion = the ∃-witness for `IsFreshAttach`
(pinTransport's solution-set law + the strip/value pin-attachment constructor — the value
clause pins its whole support to the unique solution, by `LevelClause.count` at
codim = |support|) + `pinTransportSystem_spec`.
RESTATED-POST-DEFS-REPAIR DC-2 (2026-07-28; statement byte-unchanged): `IsFreshAttach`'s
solution-set clause repaired `fd.sat x → fd.sat (Θ x)` per the blueprint §9 F-7
authorization.
DC-3 RECORD (2026-07-28, K2 kernel round; statement byte-unchanged): the post-DC-2
machine refutation (`scratch_U7_recursion_false.lean` — U27's inert gate seed + the
constant unitriangular shift) fired on `IsFreshAttach` clauses (1)+(3) JOINTLY: clause
(3) demanded LITERAL-zero solves in the NEW coordinates where the frozen
`JetSetup.recursion` keying (everything at `Θ x`) and the PROVED `C0_pinTransport`
transported-solve shape demand zeros OF THE Θ-IMAGE — the same untransported-coordinate
bug DC-2 fixed in clause (1), one clause over; an E-phase Defs deviation, NOT the
blueprint's D7 (carrier-only) display. Clauses (3)/(4) repaired to the Θ-composed form
(Defs, DC-3); the refutation no longer elaborates, and its exact instance (i = 0) is now
the PROVED `mkSigma_recursion_zero` below — the compiled closure record.
POST-DC-3 STATUS of `mkSigma_recursion` (the ∀-i form): the ∃-obligation is DISCHARGED
by the pin-attachment constructor `freshAttach_exists` below UNDER the blueprint's own
pre-named per-step condition — "fresh clauses cut freshly = their supports are UNPINNED
on the prior state" (D5 zcSeed docstring; a fresh-band/floor consequence at the U-layer,
needing hcoh/hreal + (ZC)) — carried here as `mkSigma_recursion_of_unpinned`. At i = 0
the condition is free (no pins): `mkSigma_recursion_zero`. The BARE ∀-i statement
(hypothesis_fields: none) is NOT provable from a raw seed: at i > 0 a junk history can
overlap read-i's band with earlier fresh supports, and a conflicting transported
equation makes `Θ*(Σ_i) ∩ fresh` non-representable as a digit system with the spec's
pins (cardinality/emptiness mismatch) — the junk branch then falsifies the iff. This is
NOT the dead countermodel's bug: it is the statement quantifying over histories/seeds
the note's C.1.5 (conditional on (ZC) + realizability) never claims.
K2 SIGN-OFF EXECUTED (2026-07-28, definition-change authority — the disposition ruled):
`mkSigma_recursion` RESTATED with the named hypothesis `hunp : SeedFreshUnpinned` (Defs
K2 addendum; the U25 hypothesis-add pattern) and PROVED (one line from
`mkSigma_recursion_of_unpinned`); the bare ∀-i form is RETIRED. Consumers re-keyed:
U13 gains the `hunp` binder and threads it into the frozen `JetSetup.recursion` field;
U15/U16 thread the corresponding per-class form. UNIT NOW SORRY-FREE.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.SharedZC

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD SharedZC

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- INITIALIZATION: nothing is pinned before the root read (`JetSetup.init`'s type). -/
theorem mkSigma_init {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)) :
    ∀ c : Fin (n * N), (mkSigma H n N S vOf 0).pinned c = false := by
  intro c; rfl

/-! ### The strip/value pin-attachment constructor (the blueprint D7's named obligation)

`clause_assign`: a `LevelClause` with `codim = |support|` is a PER-COORDINATE ASSIGNMENT
on its support — `LevelClause.count` leaves exactly ONE supported satisfier (the
blueprint U7 sketch's "the value clause pins its whole support to the unique solution").
`mkFresh_codim`: every constructed fresh clause has `codim = |support|` (strips: 1 = |{c}|;
value clauses: `C1_TYP_toClause` at the level set's card).
C4 HOIST RECORD (2026-07-30, SYNTHESIS_PASS1 + golf HC2#106): `clause_assign`,
`card_fin_fun'`, `valueClause_codim`, `mkFresh_codim` — formerly file-private HERE (the
original copies) and duplicated byte-identically in U9_zcRoot — now live in
`LeanUrat.HC2.SharedZC` (verbatim hoist; consumed via `open SharedZC`).
`freshAttach_exists`: the spec witness, built C0_pinTransport-style (transported old
equations, solve = target − corr) with the fresh per-coordinate assignments attached
through Θ — REQUIRES the fresh supports UNPINNED on the prior state (the D5-docstring
per-step condition; free at i = 0). -/

/-- Pairwise-disjoint supports: the clause through a coordinate is unique (hand-rolled
list induction; duplicates with nonempty support are excluded by self-disjointness). -/
private lemma pairwise_clause_unique {m : ℕ} :
    ∀ (l : List (LevelClause p m)),
      l.Pairwise (fun c₁ c₂ => Disjoint c₁.support c₂.support) →
      ∀ {c : Fin m} {cl₁ cl₂ : LevelClause p m}, cl₁ ∈ l → cl₂ ∈ l →
        c ∈ cl₁.support → c ∈ cl₂.support → cl₁ = cl₂ := by
  intro l hpw
  induction l with
  | nil => intro c cl₁ cl₂ h₁ _ _ _; exact absurd h₁ (List.not_mem_nil)
  | cons hd tl ih =>
    rw [List.pairwise_cons] at hpw
    intro c cl₁ cl₂ h₁ h₂ hc₁ hc₂
    rcases List.mem_cons.mp h₁ with rfl | h₁t
    · rcases List.mem_cons.mp h₂ with rfl | h₂t
      · rfl
      · exact absurd hc₂ (Finset.disjoint_left.mp (hpw.1 cl₂ h₂t) hc₁)
    · rcases List.mem_cons.mp h₂ with rfl | h₂t
      · exact absurd hc₁ (Finset.disjoint_left.mp (hpw.1 cl₁ h₁t) hc₂)
      · exact ih hpw.2 h₁t h₂t hc₁ hc₂

/-- **The strip/value PIN-ATTACHMENT CONSTRUCTOR** (post-DC-3): the fresh-attachment
spec has a witness whenever (a) every fresh clause is a per-coordinate assignment on its
support (`hasg` — true of `mkFresh` via `clause_assign` + `mkFresh_codim`) and (b) the
fresh supports are UNPINNED on the prior state (`hdisj` — the blueprint's pre-named
per-step condition, D5 zcSeed docstring: "fresh clauses cut freshly = their supports are
UNPINNED on the prior state"; free at i = 0, (ZC)/DOM geometry at the induction steps).
Construction: C0_pinTransport-style — pins = old ∨ fresh supports; solve = (fresh target
`U c`, else the transported old equation) − corr; every clause of the spec is then
direct. -/
theorem freshAttach_exists {m : ℕ} (D : Locus p m)
    {Θ : (Fin m → ZMod p) → (Fin m → ZMod p)} (hΘ : IsUnitriangular Θ)
    (fd : FreshData p m)
    (hasg : ∀ cl ∈ fd.clauses, ∃ u : Fin m → ZMod p,
      ∀ x, cl.sat x ↔ ∀ c ∈ cl.support, x c = u c)
    (hdisj : ∀ c : Fin m, D.pinned c = true → ¬ ∃ cl ∈ fd.clauses, c ∈ cl.support) :
    ∃ D' : Locus p m, IsFreshAttach D Θ fd D' := by
  classical
  choose corr hcorr using hΘ
  choose u hu using hasg
  -- the combined fresh target: the value the (unique) clause through c assigns
  have hex : ∀ c : Fin m, ∃ v : ZMod p,
      ∀ (cl : LevelClause p m) (hcl : cl ∈ fd.clauses), c ∈ cl.support → u cl hcl c = v := by
    intro c
    by_cases h : ∃ cl ∈ fd.clauses, c ∈ cl.support
    · obtain ⟨cl₀, hcl₀, hc₀⟩ := h
      refine ⟨u cl₀ hcl₀ c, fun cl hcl hc => ?_⟩
      cases pairwise_clause_unique fd.clauses fd.disj hcl hcl₀ hc hc₀
      rfl
    · exact ⟨0, fun cl hcl hc => absurd ⟨cl, hcl, hc⟩ h⟩
  choose U hU using hex
  -- the fresh locus, per-coordinate form
  have hsatU : ∀ y : Fin m → ZMod p, fd.sat y ↔
      (∀ c : Fin m, (∃ cl ∈ fd.clauses, c ∈ cl.support) → y c = U c) := by
    intro y
    constructor
    · rintro hy c ⟨cl, hcl, hc⟩
      rw [← hU c cl hcl hc]
      exact ((hu cl hcl y).mp (hy cl hcl)) c hc
    · intro hy cl hcl
      rw [hu cl hcl y]
      intro c hc
      rw [hU c cl hcl hc]
      exact hy c ⟨cl, hcl, hc⟩
  -- Θ-at-a-coordinate reads only ≤-coordinates (C0_pinTransport's `key`)
  have key : ∀ (i : Fin m) (g₁ g₂ : Fin m → ZMod p),
      (∀ k : Fin m, k ≤ i → g₁ k = g₂ k) → Θ g₁ i = Θ g₂ i := by
    intro i g₁ g₂ hag
    rw [hcorr i g₁, hcorr i g₂, hag i le_rfl]
    have harg : (fun j (_ : j < i) => g₁ j) = (fun j (_ : j < i) => g₂ j) := by
      funext k hk
      exact hag k hk.le
    rw [harg]
  have correq : ∀ (i : Fin m) (x : Fin m → ZMod p),
      corr i (fun j _ => x j) = Θ x i - x i := by
    intro i x
    rw [hcorr i x]; ring
  have argeq : ∀ (i : Fin m) (x : Fin m → ZMod p),
      D.solve i (fun j (_ : j < i) => Θ (fun k => if hk : k < i then x k else 0) j)
        = D.solve i (fun j _ => Θ x j) := by
    intro i x
    congr 1
    funext j hj
    apply key j
    intro k hk
    have hki : k < i := lt_of_le_of_lt hk hj
    simp only [dif_pos hki]
  -- THE WITNESS
  set D' : Locus p m :=
    ⟨fun c => D.pinned c || (if (∃ cl ∈ fd.clauses, c ∈ cl.support) then true else false),
     fun c g =>
      (if (∃ cl ∈ fd.clauses, c ∈ cl.support) then U c
       else D.solve c (fun j (_ : j < c) => Θ (fun k => if hk : k < c then g k hk else 0) j))
      - corr c g⟩ with hD'
  have hpin' : ∀ c : Fin m, D'.pinned c = true ↔
      (D.pinned c = true ∨ ∃ cl ∈ fd.clauses, c ∈ cl.support) := by
    intro c
    show (D.pinned c || (if (∃ cl ∈ fd.clauses, c ∈ cl.support) then true else false))
        = true ↔ _
    rw [Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ?_
        by_contra hn
        rw [if_neg hn] at h
        exact Bool.noConfusion h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by rw [if_pos h])
  -- the solved-coordinate equation, transported form
  have hsolve' : ∀ (x : Fin m → ZMod p) (c : Fin m),
      (x c = D'.solve c (fun j _ => x j)) ↔
      Θ x c = (if (∃ cl ∈ fd.clauses, c ∈ cl.support) then U c
          else D.solve c (fun j _ => Θ x j)) := by
    intro x c
    show (x c = (if (∃ cl ∈ fd.clauses, c ∈ cl.support) then U c
        else D.solve c (fun j (_ : j < c) => Θ (fun k => if hk : k < c then x k else 0) j))
      - corr c (fun j _ => x j)) ↔ _
    rw [argeq c x, correq c x]
    constructor <;> intro h <;> linear_combination h
  refine ⟨D', ?_, hpin', ?_, ?_⟩
  · -- clause (1): exact solution set
    intro x
    constructor
    · intro hx
      constructor
      · intro c hc
        have hnf : ¬ ∃ cl ∈ fd.clauses, c ∈ cl.support := hdisj c hc
        have hxc := hx c ((hpin' c).mpr (Or.inl hc))
        rw [hsolve' x c, if_neg hnf] at hxc
        exact hxc
      · rw [hsatU]
        intro c hcf
        have hxc := hx c ((hpin' c).mpr (Or.inr hcf))
        rw [hsolve' x c, if_pos hcf] at hxc
        exact hxc
    · rintro ⟨hxD, hxf⟩
      intro c hcp
      rw [hsolve' x c]
      by_cases hcf : ∃ cl ∈ fd.clauses, c ∈ cl.support
      · rw [if_pos hcf]
        exact (hsatU (Θ x)).mp hxf c hcf
      · rw [if_neg hcf]
        rcases (hpin' c).mp hcp with hc | hc
        · exact hxD c hc
        · exact absurd hc hcf
  · -- clause (3'): a strip coordinate's solved value zeroes the Θ-image
    rintro c ⟨cl, hcl, hsupp, hsat⟩ x hxc
    have hcs : c ∈ cl.support := by rw [hsupp]; exact Finset.mem_singleton_self c
    have hcf : ∃ cl ∈ fd.clauses, c ∈ cl.support := ⟨cl, hcl, hcs⟩
    have hU0 : U c = 0 := by
      have hsatu : cl.sat (fun _ => u cl hcl c) := by
        rw [hu cl hcl]
        intro c' hc'
        have hcc : c' = c := by rw [hsupp] at hc'; exact Finset.mem_singleton.mp hc'
        subst hcc
        rfl
      have hu0 : u cl hcl c = 0 := (hsat (fun _ => u cl hcl c)).mp hsatu
      rw [← hU c cl hcl hcs]
      exact hu0
    have hth := (hsolve' x c).mp hxc
    rw [if_pos hcf, hU0] at hth
    exact hth
  · -- clause (4'): an old literal zero's solved value zeroes the Θ-image
    intro c hcpin hczero x hxc
    have hnf : ¬ ∃ cl ∈ fd.clauses, c ∈ cl.support := hdisj c hcpin
    have hth := (hsolve' x c).mp hxc
    rw [if_neg hnf, hczero] at hth
    exact hth

/-! ### The recursion law: conditional form + the unconditional root instance -/

/-- **The recursion law under the blueprint's per-step condition** (post-DC-3): the
`JetSetup.recursion`-shaped iff holds at read `i` whenever the fresh supports are
UNPINNED on the prior state — the D5 zcSeed docstring's pre-named "fresh clauses cut
freshly" condition (free at i = 0; (ZC)+band geometry at the induction's steps — U10's
supply). -/
theorem mkSigma_recursion_of_unpinned {n N : ℕ} {H : History p F}
    {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length)
    (hunpinned : ∀ c : Fin (n * N), (mkSigma H n N S vOf i).pinned c = true →
      ¬ ∃ cl ∈ (mkFresh H n N S vOf i hi).clauses, c ∈ cl.support) :
    ∀ x : Fin (n * N) → ZMod p,
      (mkSigma H n N S vOf (i+1)).IsSolution x ↔
        ((mkSigma H n N S vOf i).IsSolution (S.Theta i x) ∧
          mkStratum H n N S vOf i (S.Theta i x)) := by
  classical
  have hasg : ∀ cl ∈ (mkFresh H n N S vOf i hi).clauses, ∃ u : Fin (n * N) → ZMod p,
      ∀ x, cl.sat x ↔ ∀ c ∈ cl.support, x c = u c :=
    fun cl hcl => clause_assign cl (mkFresh_codim S vOf i hi cl hcl)
  have hEx : ∃ D' : Locus p (n * N),
      IsFreshAttach (mkSigma H n N S vOf i) (S.Theta i) (mkFresh H n N S vOf i hi) D' :=
    freshAttach_exists (mkSigma H n N S vOf i) (S.Theta_uni i)
      (mkFresh H n N S vOf i hi) hasg hunpinned
  have hspec := pinTransportSystem_spec (mkSigma H n N S vOf i) (S.Theta i)
    (mkFresh H n N S vOf i hi) hEx
  have hstep : mkSigma H n N S vOf (i+1)
      = pinTransportSystem (mkSigma H n N S vOf i) (S.Theta i)
          (mkFresh H n N S vOf i hi) := by
    show (if hi' : i < H.nodes.length then
        pinTransportSystem (mkSigma H n N S vOf i) (S.Theta i) (mkFresh H n N S vOf i hi')
      else mkSigma H n N S vOf i) = _
    rw [dif_pos hi]
  intro x
  rw [hstep, hspec.1 x]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun _ => h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 hi⟩

/-- **The root-instance recursion, UNCONDITIONAL** (i = 0: nothing is pinned before the
root read, so the per-step condition is free). THE DC-3 COMPILED CLOSURE RECORD: this
instance subsumes the dead countermodel's exact site (`scratch_U7_recursion_false.lean`
fired at i = 0 against the pre-DC-3 spec) — the statement it falsified is now a theorem
for EVERY seed. -/
theorem mkSigma_recursion_zero {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N)) (h0 : 0 < H.nodes.length) :
    ∀ x : Fin (n * N) → ZMod p,
      (mkSigma H n N S vOf 1).IsSolution x ↔
        ((mkSigma H n N S vOf 0).IsSolution (S.Theta 0 x) ∧
          mkStratum H n N S vOf 0 (S.Theta 0 x)) := by
  refine mkSigma_recursion_of_unpinned S vOf 0 h0 ?_
  intro c hc
  rw [show (mkSigma H n N S vOf 0).pinned c = false from rfl] at hc
  exact Bool.noConfusion hc

/-- THE STRATUM RECURSION (`JetSetup.recursion`'s type at `mkStratum`), RESTATED AT THE
K2 SIGN-OFF (2026-07-28) with the named per-step hypothesis `SeedFreshUnpinned` (Defs K2
addendum) — the hypothesis addition per the U25 pattern: the constructed chain satisfies
`Σ_{i+1} = Θ_i*(Σ_i ∩ stratum(ν_i))` solution-setwise whenever the fresh supports are
unpinned on the prior state.
K2 DISPOSITION RECORD: the former BARE ∀-i form (hypothesis_fields: none) was
refuted-as-underivable — at i > 0 a junk history can overlap read-i's band with earlier
fresh supports, where a conflicting transported equation makes the spec's solution set
non-representable at the spec's pins; the statement quantified over histories/seeds the
note's C.1.5 (conditional on (ZC) + realizability) never claims. It is RETIRED; its
consumers are re-keyed: U13 threads `hunp` (this theorem partially applied fills the
frozen `JetSetup.recursion` field), U9b consumes `freshAttach_exists` directly, U10's
steps consume `mkSigma_recursion_of_unpinned` (the per-step discharge of `hunp` at i > 0
is exactly U10's (ZC)+DOM geometry; free at i = 0 — `mkSigma_recursion_zero`). -/
theorem mkSigma_recursion {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hunp : SeedFreshUnpinned H n N S vOf)
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ x : Fin (n * N) → ZMod p,
      (mkSigma H n N S vOf (i+1)).IsSolution x ↔
        ((mkSigma H n N S vOf i).IsSolution (S.Theta i x) ∧
          mkStratum H n N S vOf i (S.Theta i x)) :=
  mkSigma_recursion_of_unpinned S vOf i hi (hunp i hi)

end LeanUrat.MovesJ
