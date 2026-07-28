/-
Unit U6.mkFresh_mstar  (HC-2 campaign, E-phase — blueprint §5 Layer A)
moves_ref: MovesC `mstar_eq` docstring ("the presented fresh codimension sum equals the
FRESH-BAND count computed from node data").
deps: U2–U5.  difficulty: medium.  hypothesis_fields: none.
sketch: mstar = Σ codim = |non-value band| + |value band| (supports PARTITION the band by
U2/U3/U4); finish by `Finset.card_biUnion`.

PROOF NOTE (P-phase): the partition-count is carried out through the list-union `unionSupp`
(private helpers below) rather than `Finset.card_biUnion`, avoiding a Fin-index detour.
The four ingredients are sourced as follows:
* codim = |support| per clause  — DERIVED inline from `C1_stripClause`/`C1_TYP_toClause`
  (so U5 `mkFresh_assembled` is not imported);
* pairwise-disjoint supports     — the `.disj` field of `mkFresh` (= `mkFreshClauses_disj`,
  the Defs D6 obligation = U2's content), taken directly;
* every support ⊆ band           — DERIVED inline (U3 `mkFresh_band`'s content);
* every band coord is covered     — IMPORTED as `mkFresh_cover` (U4), the one genuinely deep
  half (the roster's (γ)-crossing self-truncation).
RESTATED-POST-DEFS-REPAIR (2026-07-27): statement stands on the REPAIRED ZCSeedLaws.downsets_literal (chart-coverage guard added; box-truncation refuted by scratch_U9_presentSeed_false — blueprint §2.2 DC-1). Sorries retained for the next fleet round.
N-6 THREADING (2026-07-28): gains `hcoh`/`hreal` binders, threaded to the N-6-restated
`mkFresh_cover` (whose value case now needs them — the no-straddle repair); proof
otherwise byte-unchanged, still closes.
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U4_freshCover

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-! ### Private counting helpers (address-free list of level-clause supports) -/

/-- The union of a list of level-clause supports, as a `Finset` of the box. -/
private def unionSupp {p m : ℕ} (L : List (LevelClause p m)) : Finset (Fin m) :=
  L.foldr (fun cl s => cl.support ∪ s) ∅

private lemma mem_unionSupp {p m : ℕ} (L : List (LevelClause p m)) (c : Fin m) :
    c ∈ unionSupp L ↔ ∃ cl ∈ L, c ∈ cl.support := by
  induction L with
  | nil => simp [unionSupp]
  | cons hd tl ih =>
      have hcons : unionSupp (hd :: tl) = hd.support ∪ unionSupp tl := rfl
      rw [hcons, Finset.mem_union, ih]
      constructor
      · rintro (h | ⟨cl, hcl, hc⟩)
        · exact ⟨hd, List.mem_cons_self, h⟩
        · exact ⟨cl, List.mem_cons_of_mem _ hcl, hc⟩
      · rintro ⟨cl, hcl, hc⟩
        rcases List.mem_cons.mp hcl with rfl | hcl'
        · exact Or.inl hc
        · exact Or.inr ⟨cl, hcl', hc⟩

private lemma disjoint_unionSupp {p m : ℕ} (a : Finset (Fin m)) (L : List (LevelClause p m))
    (h : ∀ cl ∈ L, Disjoint a cl.support) : Disjoint a (unionSupp L) := by
  induction L with
  | nil => simp [unionSupp]
  | cons hd tl ih =>
      have hcons : unionSupp (hd :: tl) = hd.support ∪ unionSupp tl := rfl
      rw [hcons, Finset.disjoint_union_right]
      exact ⟨h hd (List.mem_cons_self),
        ih (fun cl hcl => h cl (List.mem_cons_of_mem _ hcl))⟩

/-- The partition-count identity: for a pairwise-disjoint clause list with each clause's
codimension equal to its support size, the codimension sum is the size of the support union. -/
private lemma sum_codim_eq_card_unionSupp {p m : ℕ} (L : List (LevelClause p m))
    (hpw : L.Pairwise (fun a b => Disjoint a.support b.support))
    (hcard : ∀ cl ∈ L, cl.codim = cl.support.card) :
    (L.map LevelClause.codim).sum = (unionSupp L).card := by
  induction L with
  | nil => simp [unionSupp]
  | cons hd tl ih =>
      rw [List.pairwise_cons] at hpw
      have hcons : unionSupp (hd :: tl) = hd.support ∪ unionSupp tl := rfl
      rw [List.map_cons, List.sum_cons, hcons,
          Finset.card_union_of_disjoint
            (disjoint_unionSupp hd.support tl (fun cl hcl => hpw.1 cl hcl)),
          hcard hd (List.mem_cons_self),
          ih hpw.2 (fun cl hcl => hcard cl (List.mem_cons_of_mem _ hcl))]

/-! ### The unit -/

/-- `m*` of the constructed fresh data IS the fresh-band count (verbatim
`JetSetup.mstar_eq`'s field type at `mkFresh`). -/
theorem mkFresh_mstar {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (n N : ℕ) {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H)
    (i : ℕ) (hi : i < H.nodes.length) :
    (mkFresh H n N S vOf i hi).mstar
      = Nat.card {c : Fin (n * N) //
          inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c} := by
  classical
  -- the digit-alphabet count (the private `card_fin_fun`'s content, re-proved so it can be
  -- supplied by name as `C1_TYP_toClause`'s proof-arg — the value determines the And-nav).
  have hcardfun : ∀ k : ℕ, Nat.card (Fin k → ZMod p) = p ^ k := by
    intro k
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    simp [Nat.card_eq_fintype_card, ZMod.card]
  -- value-clause data: codim and support read off `C1_TYP_toClause`'s spec.
  have hvc : ∀ (j : ℕ) (hsp : (H.nodes[i]'hi).spanSlot j),
      (valueClause H n N S vOf i hi j hsp).codim
          = (levelSet H n N i (H.nodes[i]'hi) j).card ∧
      (valueClause H n N S vOf i hi j hsp).support
          = levelSet H n N i (H.nodes[i]'hi) j := by
    intro j hsp
    refine ⟨?_, ?_⟩
    · unfold valueClause
      exact (C1_TYP_toClause _ _ _ (hcardfun _)).choose_spec.2.1
    · unfold valueClause
      exact (C1_TYP_toClause _ _ _ (hcardfun _)).choose_spec.1
  -- (1) each clause's codimension equals its support size.
  have hcard : ∀ cl ∈ mkFreshClauses H n N S vOf i hi, cl.codim = cl.support.card := by
    intro cl hcl
    unfold mkFreshClauses at hcl
    rw [List.mem_append] at hcl
    rcases hcl with hstrip | hval
    · -- strip clause: support = {c₀}, codim = 1.
      simp only [List.mem_map, Finset.mem_toList] at hstrip
      obtain ⟨c₀, _, hc₀eq⟩ := hstrip
      have hspec := (C1_stripClause (p := p) c₀).choose_spec
      rw [← hc₀eq, hspec.2.1, hspec.1, Finset.card_singleton]
    · -- value clause: support = levelSet, codim = |levelSet|.
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and] at hval
      obtain ⟨jh, hjheq⟩ := hval
      rw [← hjheq, (hvc jh.1 (valueSlots_spanSlot jh.2)).1,
          (hvc jh.1 (valueSlots_spanSlot jh.2)).2]
  -- (2) pairwise-disjoint supports — free from the FreshData carrier.
  have hpw : (mkFreshClauses H n N S vOf i hi).Pairwise
      (fun a b => Disjoint a.support b.support) :=
    mkFreshClauses_disj H n N S vOf i hi
  -- (3) every support lies inside the band (U3's content, inline).
  have hband : ∀ cl ∈ mkFreshClauses H n N S vOf i hi, ∀ c ∈ cl.support,
      inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c := by
    intro cl hcl c hc
    unfold mkFreshClauses at hcl
    rw [List.mem_append] at hcl
    rcases hcl with hstrip | hval
    · simp only [List.mem_map, Finset.mem_toList] at hstrip
      obtain ⟨c₀, hc₀mem, hc₀eq⟩ := hstrip
      have hspec := (C1_stripClause (p := p) c₀).choose_spec
      rw [← hc₀eq, hspec.1, Finset.mem_singleton] at hc
      subst hc
      simp only [stripSet, Finset.mem_filter, Finset.mem_univ, true_and] at hc₀mem
      exact hc₀mem.1
    · simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and] at hval
      obtain ⟨jh, hjheq⟩ := hval
      rw [← hjheq, (hvc jh.1 (valueSlots_spanSlot jh.2)).2] at hc
      have hj := jh.2
      simp only [valueSlots, Finset.mem_filter, Finset.mem_range] at hj
      exact hj.2.2.2 c hc
  -- (4) the support union equals the band, as a Finset.
  have hunion : unionSupp (mkFreshClauses H n N S vOf i hi)
      = Finset.univ.filter
          (fun c => inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c) := by
    ext c
    rw [mem_unionSupp, Finset.mem_filter]
    constructor
    · rintro ⟨cl, hcl, hc⟩
      exact ⟨Finset.mem_univ c, hband cl hcl c hc⟩
    · rintro ⟨-, hQ⟩
      exact mkFresh_cover H n N S vOf hcoh hreal i hi c hQ
  -- assemble.
  calc (mkFresh H n N S vOf i hi).mstar
      = ((mkFreshClauses H n N S vOf i hi).map LevelClause.codim).sum := rfl
    _ = (unionSupp (mkFreshClauses H n N S vOf i hi)).card :=
        sum_codim_eq_card_unionSupp _ hpw hcard
    _ = (Finset.univ.filter
          (fun c => inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c)).card := by rw [hunion]
    _ = Nat.card {c : Fin (n * N) //
          inFreshBand H n (boxChart n N) i (H.nodes[i]'hi) c} := by
        rw [Nat.card_eq_fintype_card]
        exact (Fintype.card_subtype _).symm

end LeanUrat.MovesJ
