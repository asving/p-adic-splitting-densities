/-
H7 FORGE DEPTH 2 — the HK23/HK25 depth-2 transplant onto the forge: ATTEMPTED, and the
transplant leg REFUTED at the box, with the narrowed true layer landed (wave-18 unit 3;
charter `docs/SYNTHESIS_PASS8_2026-08-08.md` §S4 item 3; depth-1 instance + residual
list `lean/notes/openmath/H7FORGE_2026-08-08.md` §6.1).

# What this file proves

**THE COMPILED OBSTRUCTION (the headline).** The HK23/HK25 mechanism — coherent 2-node
histories with a root read whose (S-a) leg fires — does NOT transplant to the forge's
ambient (p, F) = (2, ZMod 2).  Machine-checked chain:

* `node_g_eq_one` — over the PRIME-FIELD ambient ZMod 2, EVERY node has descend degree
  g = 1: `hzbarRoot` demands a root of the irreducible ψ in the ambient field, and an
  irreducible of degree ≥ 2 over (a subfield of) F₂ has none.  (HK23's ν₀ram evades
  this over F4 only because ψ₂ = z² + z + 1 has its root r₀ IN F4 — genuine residue
  growth, unavailable here.)
* `sa_leg_false` — the (S-a) transition leg is UNSATISFIABLE at any parent over
  (2, ZMod 2): the leg's own RG-2 fence gives e = 1, so with g = 1 the recorded
  `IsNodeLift` keeps the key degree (Φ̂ = Φ + t₀, deg t₀ < deg Φ); but
  `TransitionCoreL.base.child_reps` puts the parent key on the child's rep list and
  `Stage.hreps` forces deg Φ < deg Φ̂ — the S9 corner refutation
  (`HC1.S9_ungated_corner_refuted` genre) fires at EVERY forge parent.
* `twoNode_coherent_false` — hence over (2, ZMod 2) EVERY `HistoryCoherent` history
  has length 1: NO depth-2 history exists at all.
* `no_depth2_member` — hence NO `TreeModel` over (2, ZMod 2) — the forge's or any
  depth-2 extension — can realize ANY 2-node chain (`mem_realizable` forces coherence).
  The sides-2 site's continuations are UNREALIZABLE at this box; realizing them needs
  an ambient with residue growth (the F4 relocation), a NEW unit, not this one.

**THE NARROWED TRUE LAYER (everything short of the refuted leg).** The two hull-slope
clauses of the sides-2 site's split (`forgeSplitJ`: slopes 1 < 2) each get a LAWFUL
child node continuing the joint site's chain `fHj = [fNodeJ]`:

* `fChildS0`/`fChildS1` — recentering-species reads (the HK25 ν₁rec genre; increment
  species is unlawful at e·g = 1 by `hspecInc`), slope-keyed to the hull:
  slope(child of side j) = slope(fNodeJ) + hullSlope j, i.e. 4 = 3 + 1 and 5 = 3 + 2
  (`child_slope_keyed`, `child_steepening`).  The S2 CENTER-distinction genre is
  UNAVAILABLE here: `hspecRecCenter` + the trivial unit group of ZMod 2 force
  center = z̄ = 1 at every recentering — the children are h/slope-distinguished
  instead (`fChildS0_ne_fChildS1`).
* `fHjC0`/`fHjC1` — the 2-node histories `fHj.snoc fChild*`, with, PER NODE, exactly
  the depth-1 law layer: the first three `HistoryCoherent` conjunct families
  (`pernode_fHjC0/1` — root frame degree, slope law, γ-tie), FULL realizability
  (`realizable_fHjC0/1` via `TransitionAdmissible` against the computed transported
  vertex `vtx_fNodeJ : fNodeJ.vtx = 1` — (NA) vacuous, (HV) exact, (SAE) strict
  6 < 7/8, vertex equality 3 = 3), the canonical presentation
  (`canonpres_fHjC0/1`), and `InBox 2`.
* `transition_leg_data_fHjC0/1` — every NON-(S-a) conjunct of the coherence
  transition leg holds at the instance (RG-2 e₀ = 1, window 0+1 ≤ 1 = μ₀, width chain
  D₁ = 1 = childWidth₀, strict steepening); `sa_leg_fHjC0_false` pins the failure to
  EXACTLY the (S-a) existential.  `coherent_fHjC0_false`, `fHj_snoc_never_coherent`
  are the instance negations.

# Honesty displays

* The depth-2 analogues of the three non-diagonality certificates are NOT stated:
  they would key on realized depth-2 sites, and `no_depth2_member` proves that class
  EMPTY over this box — the reads do not extend.  Recorded as obstructed, not dodged.
* Nothing here discharges (H7); (H7) stays [M].  H7-W3a remains the Tier-M
  obligation.  The forge stays depth-1 (H7FORGE §4's display stands, now with the
  depth-2 residual CLOSED NEGATIVELY at this box: residual 1 of H7FORGE §6 converts
  from "open transplant" to "refuted at (2, ZMod 2); relocation to F4 required").
* New declarations only; `H7Forge.lean` (the committed 15 decls) is consumed
  read-only; no existing statement modified.  In-file `#print axioms` census at EOF.

Unit record: `lean/notes/openmath/H7DEPTH2_2026-08-08.md`.
-/
import Mathlib
import LeanUrat.Scaffold.HDischarge.H7.H7Forge

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanUrat.Scaffold.HDischarge.H7

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD LeanUrat.MovesT
open Classical

/-! ### §O — THE GENERAL OBSTRUCTION: no coherent 2-node history over (2, ZMod 2).

The refutation chain is ambient-field structural: prime-field ambient ⇒ g = 1 at every
node ⇒ (with the leg's own RG-2 fence e = 1) the recorded lift keeps the key degree ⇒
the child stage's rep list forces a strict degree increase.  This is the compiled
transplant wall: HK23/HK25's positive gates live over F4 exactly because their root
read has g = 2 there. -/

/-- ZMod 2 has one unit: every unit evaluates to 1. -/
lemma zmod2_unit_val (u : (ZMod 2)ˣ) : ((u : (ZMod 2)ˣ) : ZMod 2) = 1 := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) ((u : (ZMod 2)ˣ) : ZMod 2) with h | h
  · exact absurd h (Units.ne_zero u)
  · exact h

/-- **The prime-field descend collapse**: over the ambient ZMod 2, EVERY node has
g = 1.  `hzbarRoot` puts a root of ψ in the ambient field (necessarily 1, the only
unit); ψ irreducible with a root is linear. -/
theorem node_g_eq_one (ν : Node 2 (ZMod 2)) : ν.g = 1 := by
  have hroot := ν.hzbarRoot
  rw [zmod2_unit_val ν.zbar, Polynomial.eval₂_at_one] at hroot
  have heval : ν.ψ.eval 1 = 0 :=
    ν.σ.K.subtype.injective (hroot.trans (map_zero ν.σ.K.subtype).symm)
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr heval
  rcases ν.hψirr.isUnit_or_isUnit hq with hu | hu
  · exact absurd hu (Polynomial.not_isUnit_X_sub_C 1)
  · have hq0 : q ≠ 0 := hu.ne_zero
    have hdeg := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero 1) hq0,
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_eq_zero_of_isUnit hu] at hdeg
    rw [← ν.hψdeg, hdeg]

/-- **The (S-a) leg refutation at any parent over (2, ZMod 2)** — the transplant wall,
node-level: given the leg's own data (RG-2 fence `e = 1`, the regrade, the recorded
lift onto the child key, the transition record at the child pair), derive `False`.
With g = 1 (forced, `node_g_eq_one`) and e = 1, `IsNodeLift` gives
Φ̂ = Φ + t₀ with deg t₀ < deg Φ, so deg Φ̂ = deg Φ; but `child_reps` puts the parent
key Φ on the child's rep list and `Stage.hreps` demands deg Φ < deg Φ̂. -/
theorem sa_leg_false (ν₀ ν₁ : Node 2 (ZMod 2)) (he1 : ν₀.e = 1)
    (σV : Stage 2 (ZMod 2)) (hreg : RegradeOf ν₀.σ ν₀.e ν₀.h σV)
    (hlift : IsNodeLift ν₀ ν₁.σ.Φ)
    (htcl : TransitionCoreL σV ν₁.σ ν₁.σ.Φ ν₁.e ν₁.h ν₀.zbar) : False := by
  obtain ⟨tt, htt0, httk, hΦeq⟩ := hlift
  have hg1 : ν₀.g = 1 := node_g_eq_one ν₀
  rw [he1, hg1] at hΦeq
  simp only [one_mul, pow_one, Finset.sum_range_one, pow_zero, mul_one] at hΦeq
  -- hΦeq : ν₁.σ.Φ = ν₀.σ.Φ + tt 0
  have hΦ0ne : ν₀.σ.Φ ≠ 0 := ν₀.σ.hmonic.ne_zero
  have httlt : (tt 0).degree < ν₀.σ.Φ.degree := by
    by_cases h0 : tt 0 = 0
    · rw [h0, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (fun hb => hΦ0ne (Polynomial.degree_eq_bot.mp hb))
    · have hc : ν₀.ψ.coeff 0 ≠ 0 := fun hcz => h0 (htt0 0 hcz)
      exact (httk 0 (by rw [hg1]; omega) hc).2.1
  have hdeg1 : ν₁.σ.Φ.degree = ν₀.σ.Φ.degree := by
    rw [hΦeq]
    exact Polynomial.degree_add_eq_left_of_degree_lt httlt
  have hmem : σV.Φ ∈ ν₁.σ.reps := by
    rw [htcl.base.child_reps]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hlt : σV.Φ.degree < ν₁.σ.Φ.degree := (ν₁.σ.hreps σV.Φ hmem).2
  rw [hreg.1, hdeg1] at hlt
  exact lt_irrefl _ hlt

/-- **THE DEPTH-2 WALL**: over (2, ZMod 2) every coherent history is ONE-NODE — the
first transition (whose parent is the root read, species root ≠ recentering, so the
(S-a) leg fires) is unsatisfiable by `sa_leg_false`. -/
theorem twoNode_coherent_false (H : History 2 (ZMod 2))
    (hlen : 1 < H.nodes.length) : ¬ HistoryCoherent H := by
  rintro ⟨-, -, -, htrans⟩
  have hi : 0 + 1 < H.nodes.length := by omega
  obtain ⟨-, hsa, -⟩ := htrans 0 hi
  have hner : (H.nodes[0]'(by omega)).species ≠ ReadSpecies.recentering := by
    intro hc
    exact ReadSpecies.noConfusion
      (((H.root_iff 0 (by omega)).mpr rfl).symm.trans hc)
  obtain ⟨he1, σV, hreg, hlift, htcl⟩ := hsa hner
  exact sa_leg_false _ _ he1 σV hreg hlift htcl

/-- Model-level corollary: NO `TreeModel` over (2, ZMod 2) — at ANY box parameters,
the forge's or a would-be depth-2 extension's — realizes a 2-node chain
(`mem_realizable` forces coherence).  The sides-2 site's continuations are
unrealizable at this ambient; the residual relocates to an ambient with residue
growth (F4), out of this unit's additive-only scope. -/
theorem no_depth2_member {n N m : ℕ} {pol : CanonPolicy 2 (ZMod 2)}
    (T : TreeModel 2 (ZMod 2) n N m pol) (H : History 2 (ZMod 2))
    (hlen : 1 < H.nodes.length) (x : Box 2 m) : ¬ T.mem (some H) x :=
  fun hmem => twoNode_coherent_false H hlen (T.mem_realizable H x hmem).1

/-! ### §C — the two hull-slope child nodes (the narrowed true layer).

Recentering species (the HK25 `ν₁rec` genre — increment is unlawful at e·g = 1 by
`hspecInc`), continuing the joint site's chain below its window vertex μ₀ = 1,
slope-keyed to the split's hull sides: child of side j reads at slope
slope(fNodeJ) + hullSlope j.  Adjacency: s0 + wSide = 1 = μ₀; both lines pass through
the standing vertex (base index 1, height 3).  Center-distinction is UNAVAILABLE
(recentering over ZMod 2 forces center = z̄ = 1); the children are h-distinguished. -/

/-- **Child of hull side 0 (slope 1)**: the recentering read at slope 4 = 3 + 1 —
`e = g = 1`, `h = 4`, `ψ = X − C 1` at center 1, `z̄ = 1`, side `s0 = 0, wSide = 1`,
`line = ⟨7, 4⟩` (through the vertex: 7 − 4 = 3), `u* = 3`, `γ = 7 = 1·3 + 1·4`. -/
noncomputable def fChildS0 : Node 2 (ZMod 2) where
  species := ReadSpecies.recentering
  σ := toyStage
  e := 1
  h := 4
  s := 1
  t := 0
  g := 1
  μ := 1
  a := 0
  s0 := 0
  wSide := 1
  Dwidth := 1
  line := ⟨7, 4⟩
  ustar := 3
  gam := 7
  zbar := 1
  center := 1
  lift := Polynomial.X
  ψ := X - Polynomial.C 1
  pat := fun _ => 1
  Ranch := 1 + X
  he := le_refl 1
  hh := by norm_num
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := le_refl 1
  hμ := le_refl 1
  hEdvd := one_dvd 1
  hDwidth := by
    rw [show toyStage.Φ = (Polynomial.X : Polynomial ℤ_[2]) from rfl,
      Polynomial.natDegree_X]
  hψmonic := monic_X_sub_C 1
  hψdeg := natDegree_X_sub_C 1
  hψirr := irreducible_X_sub_C 1
  hRanch := by norm_num [Finset.sum_range_succ]
  hpat0 := one_ne_zero
  hpatTop := one_ne_zero
  hAnchor := by norm_num
  hLineU := by norm_num [Line.at]
  hOrd := by
    constructor
    · exact toyK_leaf_ord.dvd
    · intro hdvd
      have hne : (1 + X : Polynomial ↥toyStage.K) ≠ 0 := by
        rw [← toyK_leaf_ord]
        exact pow_ne_zero 1 (Polynomial.X_sub_C_ne_zero 1)
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      have h2 : ((X - Polynomial.C 1 : Polynomial ↥toyStage.K) ^ (1 + 1)).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, natDegree_X_sub_C]
      have h1 : (1 + X : Polynomial ↥toyStage.K).natDegree ≤ 1 := by
        apply le_trans (Polynomial.natDegree_add_le _ _)
        simp
      omega
  hzbarRoot := by simp
  hspecInc := by intro h; simp at h
  hspecRec := fun _ => ⟨rfl, rfl⟩
  hspecRecCenter := fun _ => ⟨rfl, by simp⟩

/-- **Child of hull side 1 (slope 2)**: the recentering read at slope 5 = 3 + 2 —
as `fChildS0` with `h = 5`, `line = ⟨8, 5⟩` (through the vertex: 8 − 5 = 3),
`γ = 8 = 1·3 + 1·5`. -/
noncomputable def fChildS1 : Node 2 (ZMod 2) where
  species := ReadSpecies.recentering
  σ := toyStage
  e := 1
  h := 5
  s := 1
  t := 0
  g := 1
  μ := 1
  a := 0
  s0 := 0
  wSide := 1
  Dwidth := 1
  line := ⟨8, 5⟩
  ustar := 3
  gam := 8
  zbar := 1
  center := 1
  lift := Polynomial.X
  ψ := X - Polynomial.C 1
  pat := fun _ => 1
  Ranch := 1 + X
  he := le_refl 1
  hh := by norm_num
  hcop := by norm_num
  hbez := by norm_num
  hbezCanon := by norm_num
  hg := le_refl 1
  hμ := le_refl 1
  hEdvd := one_dvd 1
  hDwidth := by
    rw [show toyStage.Φ = (Polynomial.X : Polynomial ℤ_[2]) from rfl,
      Polynomial.natDegree_X]
  hψmonic := monic_X_sub_C 1
  hψdeg := natDegree_X_sub_C 1
  hψirr := irreducible_X_sub_C 1
  hRanch := by norm_num [Finset.sum_range_succ]
  hpat0 := one_ne_zero
  hpatTop := one_ne_zero
  hAnchor := by norm_num
  hLineU := by norm_num [Line.at]
  hOrd := by
    constructor
    · exact toyK_leaf_ord.dvd
    · intro hdvd
      have hne : (1 + X : Polynomial ↥toyStage.K) ≠ 0 := by
        rw [← toyK_leaf_ord]
        exact pow_ne_zero 1 (Polynomial.X_sub_C_ne_zero 1)
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne
      have h2 : ((X - Polynomial.C 1 : Polynomial ↥toyStage.K) ^ (1 + 1)).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, natDegree_X_sub_C]
      have h1 : (1 + X : Polynomial ↥toyStage.K).natDegree ≤ 1 := by
        apply le_trans (Polynomial.natDegree_add_le _ _)
        simp
      omega
  hzbarRoot := by simp
  hspecInc := by intro h; simp at h
  hspecRec := fun _ => ⟨rfl, rfl⟩
  hspecRecCenter := fun _ => ⟨rfl, by simp⟩

lemma fChildS0_nonroot : fChildS0.species ≠ ReadSpecies.root :=
  fun h => ReadSpecies.noConfusion h

lemma fChildS1_nonroot : fChildS1.species ≠ ReadSpecies.root :=
  fun h => ReadSpecies.noConfusion h

/-- The children are distinct — by `h` (the S2 CENTER-distinction genre is unavailable:
both centers are forced to the unique unit 1 by `hspecRecCenter`). -/
lemma fChildS0_ne_fChildS1 : fChildS0 ≠ fChildS1 := fun h => by
  have h2 : (4 : ℕ) = 5 := congrArg Node.h h
  omega

/-! ### §H2 — the two depth-2 candidate histories on the joint site's chain. -/

noncomputable def fHjC0 : History 2 (ZMod 2) := fHj.snoc fChildS0 fChildS0_nonroot
noncomputable def fHjC1 : History 2 (ZMod 2) := fHj.snoc fChildS1 fChildS1_nonroot

lemma fHjC0_nodes : fHjC0.nodes = [fNodeJ, fChildS0] := rfl
lemma fHjC1_nodes : fHjC1.nodes = [fNodeJ, fChildS1] := rfl
lemma fHjC0_len : fHjC0.nodes.length = 2 := rfl
lemma fHjC1_len : fHjC1.nodes.length = 2 := rfl
lemma fHjC0_str0 : fHjC0.strFrame 0 = 1 := rfl
lemma fHjC0_str1 : fHjC0.strFrame 1 = 1 := rfl
lemma fHjC1_str0 : fHjC1.strFrame 0 = 1 := rfl
lemma fHjC1_str1 : fHjC1.strFrame 1 = 1 := rfl

/-! ### §PN — the PER-NODE coherence layer ("as at depth 1"): the first three
`HistoryCoherent` conjunct families, stated VERBATIM and proved at both histories.
The FOURTH family (the transition leg) is the refuted one — §X below. -/

/-- Per-node coherence at `fHjC0`: root frame degree, absolute-scale slope law,
γ-tie — the exact non-transition conjuncts of `HistoryCoherent`. -/
theorem pernode_fHjC0 :
    (∀ hj : 0 < fHjC0.nodes.length, (fHjC0.nodes[0]'hj).σ.Φ.natDegree = 1) ∧
    (∀ (i : ℕ) (hi : i < fHjC0.nodes.length),
      (fHjC0.nodes[i]'hi).line.slope *
          (((fHjC0.nodes[i]'hi).e : ℚ) * (fHjC0.strFrame i : ℚ) * ((fHjC0.nodes[i]'hi).Dwidth : ℚ))
        = ((fHjC0.nodes[i]'hi).h : ℚ)) ∧
    (∀ (i : ℕ) (hi : i < fHjC0.nodes.length),
      (((fHjC0.nodes[i]'hi).gam : ℤ) : ℚ)
        = ((fHjC0.nodes[i]'hi).e : ℚ) * ((fHjC0.strFrame i : ℚ) * (fHjC0.nodes[i]'hi).ustar)
          + ((((fHjC0.nodes[i]'hi).s0 + (fHjC0.nodes[i]'hi).wSide) : ℕ) : ℚ)
            * ((fHjC0.nodes[i]'hi).h : ℚ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hj
    show (Polynomial.X : Polynomial ℤ_[2]).natDegree = 1
    exact Polynomial.natDegree_X
  · intro i hi
    have hi2 : i < 2 := fHjC0_len ▸ hi
    interval_cases i
    · show (3 : ℚ) * (((1 : ℕ) : ℚ) * ((fHjC0.strFrame 0 : ℕ) : ℚ) * ((1 : ℕ) : ℚ))
          = ((3 : ℕ) : ℚ)
      rw [fHjC0_str0]
      norm_num
    · show (4 : ℚ) * (((1 : ℕ) : ℚ) * ((fHjC0.strFrame 1 : ℕ) : ℚ) * ((1 : ℕ) : ℚ))
          = ((4 : ℕ) : ℚ)
      rw [fHjC0_str1]
      norm_num
  · intro i hi
    have hi2 : i < 2 := fHjC0_len ▸ hi
    interval_cases i
    · show (((6 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((fHjC0.strFrame 0 : ℕ) : ℚ) * (3 : ℚ))
          + (((0 + 1 : ℕ)) : ℚ) * ((3 : ℕ) : ℚ)
      rw [fHjC0_str0]
      norm_num
    · show (((7 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((fHjC0.strFrame 1 : ℕ) : ℚ) * (3 : ℚ))
          + (((0 + 1 : ℕ)) : ℚ) * ((4 : ℕ) : ℚ)
      rw [fHjC0_str1]
      norm_num

/-- Per-node coherence at `fHjC1` (slope 5, γ = 8 leg). -/
theorem pernode_fHjC1 :
    (∀ hj : 0 < fHjC1.nodes.length, (fHjC1.nodes[0]'hj).σ.Φ.natDegree = 1) ∧
    (∀ (i : ℕ) (hi : i < fHjC1.nodes.length),
      (fHjC1.nodes[i]'hi).line.slope *
          (((fHjC1.nodes[i]'hi).e : ℚ) * (fHjC1.strFrame i : ℚ) * ((fHjC1.nodes[i]'hi).Dwidth : ℚ))
        = ((fHjC1.nodes[i]'hi).h : ℚ)) ∧
    (∀ (i : ℕ) (hi : i < fHjC1.nodes.length),
      (((fHjC1.nodes[i]'hi).gam : ℤ) : ℚ)
        = ((fHjC1.nodes[i]'hi).e : ℚ) * ((fHjC1.strFrame i : ℚ) * (fHjC1.nodes[i]'hi).ustar)
          + ((((fHjC1.nodes[i]'hi).s0 + (fHjC1.nodes[i]'hi).wSide) : ℕ) : ℚ)
            * ((fHjC1.nodes[i]'hi).h : ℚ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hj
    show (Polynomial.X : Polynomial ℤ_[2]).natDegree = 1
    exact Polynomial.natDegree_X
  · intro i hi
    have hi2 : i < 2 := fHjC1_len ▸ hi
    interval_cases i
    · show (3 : ℚ) * (((1 : ℕ) : ℚ) * ((fHjC1.strFrame 0 : ℕ) : ℚ) * ((1 : ℕ) : ℚ))
          = ((3 : ℕ) : ℚ)
      rw [fHjC1_str0]
      norm_num
    · show (5 : ℚ) * (((1 : ℕ) : ℚ) * ((fHjC1.strFrame 1 : ℕ) : ℚ) * ((1 : ℕ) : ℚ))
          = ((5 : ℕ) : ℚ)
      rw [fHjC1_str1]
      norm_num
  · intro i hi
    have hi2 : i < 2 := fHjC1_len ▸ hi
    interval_cases i
    · show (((6 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((fHjC1.strFrame 0 : ℕ) : ℚ) * (3 : ℚ))
          + (((0 + 1 : ℕ)) : ℚ) * ((3 : ℕ) : ℚ)
      rw [fHjC1_str0]
      norm_num
    · show (((8 : ℤ) : ℚ)) = ((1 : ℕ) : ℚ) * (((fHjC1.strFrame 1 : ℕ) : ℚ) * (3 : ℚ))
          + (((0 + 1 : ℕ)) : ℚ) * ((5 : ℕ) : ℚ)
      rw [fHjC1_str1]
      norm_num

end LeanUrat.Scaffold.HDischarge.H7
