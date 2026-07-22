/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.OM.QpTypeChainAll
import LeanUrat.OM.OmLeafFaithful
import LeanUrat.OM.Order0Alpha

/-!
# FullFaithful — the assembled faithfulness theorem for EVERY fiber of the full `n = 2` model
(Wild Wave 6c task C2, `notes/WILD_WAVE6C_BLUEPRINT_2026-07-22.md` §0, §1.4, §2-W6c-c;
blueprint Codex-verified)

**The scope-#5 payoff.** Wave 6's capstone (`SeriesAssembly.montes_unconditional_n2_full`)
certified the FULL per-type `n = 2` densities at `p = M9.realP = 2`, counting
`decidedCount6 σ N = sepCount6 σ N + chainCount6 σ N` over exactly three fiber families on the
coefficient pair box: the order-0 separable cells `SepSplitCell`/`SepInertCell` and the
translated chain fibers `TransChain c ms leaf` (`c ∈ {0,1}`, `ms ∈ msMenu N N`,
`leaf ∈ chainLeaves N σ`). Its honest-limits block recorded that the σ-keying of some of those
fibers was still DEFINITIONAL. THIS module closes that gap:

* `W6Fiber` / `fiberPred` / `keyedType` / `W6FiberOK` — the fiber-family index, matching
  `decidedCount6`'s summands EXACTLY (correspondence lemmas `sepCount6_split_eq_card` /
  `sepCount6_inert_eq_card` / `chainCount6_eq_sum_card`, all definitional).
* `fullFiber_hasType` — **THE theorem**: every genuine monic quadratic `f : ℤ_[2][X]` whose
  coefficient box pair lies in ANY decided fiber of the full model's per-type count has a
  genuine ℚ_2-factorization certificate of the keyed type σ. Footprint: Lean core +
  `om_leaf_faithful` EXACTLY.
* `fullFiber_split_hasType_axfree` — the split-keyed legs (order-0 `sepSplit` + every
  chain-`split`) packaged AXIOM-FREE (Lean-core footprint), per blueprint §1.4 (families whose
  certificate is proved outright by the (S)/(S0) masters).
* the sep-inert glue (`sepInert_classify_glue` → `sepInertCell_hasType`) — the one
  previously-uncertain leg: the order-0 inert cell (`2 ∤ a₀, 2 ∤ a₁`, residual `x² + x + 1`)
  is fed to the axiom through the BANKED order-0 fiber characterization
  `Order0.classify_eq_sepShape_iff` (γ5+γ6) at the shape `sepShape 2 (indiscrete 2)`, whose
  menu membership + `inertType2`-keying are proved here; existence then fires through the
  landed W2 consumer `OmLeafFaithful.menuFiber_hasType`.

**Honest scope** (unchanged by this module): with `fullFiber_hasType`, every fiber of the W6
full model's decided count now carries Montes-faithful σ-keying — modulo the ONE axiom
`om_leaf_faithful` (its scope-#5 form; the axiom contributes only `LocalFactorData` existence
on the irreducible legs, machine-guarded by the axiom-free W6c-a/b forcing masters). The
capstone's OTHER conditionality is untouched: palindromy still sits behind `htameFE`, and no
counting/density statement changes here. The axiom-free forcing facts
(`transChainFiber_ram_forced` / `transChainFiber_inert_forced` / `sepInertCell_forced`) are
NOT consumed by this theorem — they are the machine guards for the W6c-d mutation probes.

Discipline: purely ADDITIVE module (no existing file modified); no `sorry`, no new axiom;
AxCheck census at bottom — `fullFiber_hasType` and its two axiom-route helpers = Lean core +
`om_leaf_faithful` exactly; everything else core-only.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1600000

namespace LeanUrat.OM.FullFaithful

open Polynomial
open LeanUrat LeanUrat.OM
open LeanUrat.OM.CellMenu
open LeanUrat.OM.QpTypeChain LeanUrat.OM.QpTypeChainLeaves LeanUrat.OM.QpTypeLeafMasters
open LeanUrat.OM.QpTypeChainAll

/-! ## Block 1 — the fiber-family index (the summands of `decidedCount6`, as data)

`decidedCount6 σ N = sepCount6 σ N + chainCount6 σ N` sums `Nat.card`s of exactly these
predicates on the pair box: `SepSplitCell N` (when `σ = splitType2`), `SepInertCell N` (when
`σ = inertType2`), and `TransChain c ms leaf N` over `c ∈ {0,1}`,
`(ms, leaf) ∈ msMenu N N ×ˢ chainLeaves N σ`. `W6Fiber` indexes the families, `fiberPred`
recovers the counted predicate, `keyedType` the type the family is keyed by, and `W6FiberOK`
mirrors the summation index set. -/

/-- The fiber-family index of the full `n = 2` model's decided count. -/
inductive W6Fiber where
  | sepSplit : W6Fiber
  | sepInert : W6Fiber
  | chain (c : ℕ) (ms : List ℕ) (leaf : ChainMenu.ChainLeaf) : W6Fiber

/-- The counted fiber predicate of a family, on the level-`N` coefficient pair box —
literally the predicate under the corresponding `Nat.card` summand of `decidedCount6`. -/
def fiberPred : W6Fiber → (N : ℕ) → SeriesAssembly.pairBox N → Prop
  | .sepSplit, N, a => SeriesAssembly.SepSplitCell N a
  | .sepInert, N, a => SeriesAssembly.SepInertCell N a
  | .chain c ms leaf, N, a => SeriesAssembly.TransChain c ms leaf N a

/-- The factorization type a family is keyed by in `decidedCount6`. -/
def keyedType : W6Fiber → FactorizationType
  | .sepSplit => ChainMenu.splitType2
  | .sepInert => ChainMenu.inertType2
  | .chain _ _ leaf => ChainMenu.leafType leaf

/-- Well-formedness of a family for the type-σ count: the EXACT summation index set of
`decidedCount6 σ N` (the separable cells contribute only at their own σ; the chain fibers
range over `c ∈ {0,1}`, `ms ∈ msMenu N N`, `leaf ∈ chainLeaves N σ`). -/
def W6FiberOK : W6Fiber → ℕ → FactorizationType → Prop
  | .sepSplit, _, σ => σ = ChainMenu.splitType2
  | .sepInert, _, σ => σ = ChainMenu.inertType2
  | .chain c ms leaf, N, σ =>
      c ∈ ({0, 1} : Finset ℕ) ∧ ms ∈ ChainMenu.msMenu N N
        ∧ leaf ∈ ChainMenu.chainLeaves N σ

@[simp] theorem fiberPred_sepSplit (N : ℕ) (a : SeriesAssembly.pairBox N) :
    fiberPred W6Fiber.sepSplit N a = SeriesAssembly.SepSplitCell N a := rfl

@[simp] theorem fiberPred_sepInert (N : ℕ) (a : SeriesAssembly.pairBox N) :
    fiberPred W6Fiber.sepInert N a = SeriesAssembly.SepInertCell N a := rfl

@[simp] theorem fiberPred_chain (c : ℕ) (ms : List ℕ) (leaf : ChainMenu.ChainLeaf)
    (N : ℕ) (a : SeriesAssembly.pairBox N) :
    fiberPred (W6Fiber.chain c ms leaf) N a = SeriesAssembly.TransChain c ms leaf N a := rfl

@[simp] theorem keyedType_sepSplit : keyedType W6Fiber.sepSplit = ChainMenu.splitType2 := rfl

@[simp] theorem keyedType_sepInert : keyedType W6Fiber.sepInert = ChainMenu.inertType2 := rfl

@[simp] theorem keyedType_chain (c : ℕ) (ms : List ℕ) (leaf : ChainMenu.ChainLeaf) :
    keyedType (W6Fiber.chain c ms leaf) = ChainMenu.leafType leaf := rfl

@[simp] theorem W6FiberOK_sepSplit (N : ℕ) (σ : FactorizationType) :
    W6FiberOK W6Fiber.sepSplit N σ = (σ = ChainMenu.splitType2) := rfl

@[simp] theorem W6FiberOK_sepInert (N : ℕ) (σ : FactorizationType) :
    W6FiberOK W6Fiber.sepInert N σ = (σ = ChainMenu.inertType2) := rfl

@[simp] theorem W6FiberOK_chain (c : ℕ) (ms : List ℕ) (leaf : ChainMenu.ChainLeaf)
    (N : ℕ) (σ : FactorizationType) :
    W6FiberOK (W6Fiber.chain c ms leaf) N σ
      = (c ∈ ({0, 1} : Finset ℕ) ∧ ms ∈ ChainMenu.msMenu N N
          ∧ leaf ∈ ChainMenu.chainLeaves N σ) := rfl

/-- A well-formed family's keyed type IS the σ it counts for (the keying alignment). -/
theorem keyedType_eq_of_OK {F : W6Fiber} {N : ℕ} {σ : FactorizationType}
    (hOK : W6FiberOK F N σ) : keyedType F = σ := by
  cases F with
  | sepSplit => exact hOK.symm
  | sepInert => exact hOK.symm
  | chain c ms leaf => exact (ChainMenu.of_mem_chainLeaves hOK.2.2).2

/-! ### The definitional correspondence with `decidedCount6`'s summands

`decidedCount6 σ N = sepCount6 σ N + chainCount6 σ N` (`SeriesAssembly.decidedCount6`), and
each summand is the `Nat.card` of a `fiberPred` fiber of a `W6FiberOK`-indexed family: -/

/-- `sepCount6` at the split type IS the `sepSplit` family's fiber count. -/
theorem sepCount6_split_eq_card (N : ℕ) :
    SeriesAssembly.sepCount6 ChainMenu.splitType2 N
      = (Nat.card {a : SeriesAssembly.pairBox N // fiberPred W6Fiber.sepSplit N a} : ℚ) := by
  unfold SeriesAssembly.sepCount6
  rw [if_pos rfl]
  rfl

/-- `sepCount6` at the inert type IS the `sepInert` family's fiber count. -/
theorem sepCount6_inert_eq_card (N : ℕ) :
    SeriesAssembly.sepCount6 ChainMenu.inertType2 N
      = (Nat.card {a : SeriesAssembly.pairBox N // fiberPred W6Fiber.sepInert N a} : ℚ) := by
  unfold SeriesAssembly.sepCount6
  rw [if_neg SeriesAssembly.inert_ne_split, if_pos rfl]
  rfl

/-- `chainCount6` IS the sum of the `chain` families' fiber counts over the `W6FiberOK`
index rectangle (`c ∈ {0,1}`, `(ms, leaf) ∈ msMenu N N ×ˢ chainLeaves N σ`). -/
theorem chainCount6_eq_sum_card (σ : FactorizationType) (N : ℕ) :
    SeriesAssembly.chainCount6 σ N
      = ∑ c ∈ ({0, 1} : Finset ℕ),
          ∑ x ∈ ChainMenu.msMenu N N ×ˢ ChainMenu.chainLeaves N σ,
            ((Nat.card {a : SeriesAssembly.pairBox N //
                fiberPred (W6Fiber.chain c x.1 x.2) N a} : ℕ) : ℚ) := rfl

/-! ## Block 2 — the sep-inert glue (blueprint §2-W6c-c, the preferred route)

`SepInertCell` (`2 ∤ a₀ ∧ 2 ∤ a₁` on the level-`N` box) forces the mod-2 reduction of `f` to
be `x² + x + 1` — the unique irreducible monic quadratic over `F₂` (root-free: `noRootPairs 2`
membership by `decide`). The BANKED order-0 fiber characterization
`Order0.classify_eq_sepShape_iff` (γ5 + γ6, `OM/Order0Alpha.lean`) then pins the genuine
classifier fiber: `B.classify 2 2 N (toBox f) = sepShape 2 (indiscrete 2)` — the order-0
separable shape at the one-part partition `{2}`, whose `unramType` is `inertType2` and which
sits on the W1 menu `WildMenu.omMenuW 2 inertType2`. Existence then fires through the landed
W2 consumer `OmLeafFaithful.menuFiber_hasType` (routed through the re-scoped axiom). -/

/-- The order-0 separable shape at the one-part partition is keyed to the inert type:
`unramType 2 (indiscrete 2) = ⟨{(1,2)}⟩ = inertType2`. -/
theorem unramType_indiscrete_two :
    Order0.unramType 2 (Nat.Partition.indiscrete 2) = ChainMenu.inertType2 := by
  unfold Order0.unramType ChainMenu.inertType2
  rw [Nat.Partition.indiscrete_parts (by norm_num), Multiset.map_singleton]

/-- The order-0 inert shape `sepShape 2 (indiscrete 2)` is on the W1 σ-keyed menu at its own
unramified type (the `sepShapesOf` leg of `WildMenu.omMenuW`). -/
theorem sepShape_indiscrete2_mem_omMenuW :
    Order0.sepShape 2 (Nat.Partition.indiscrete 2)
      ∈ WildMenu.omMenuW 2 (Order0.unramType 2 (Nat.Partition.indiscrete 2)) := by
  rw [WildMenu.omMenuW]
  refine Finset.mem_union_left _ ?_
  rw [Order0.sepShapesOf, Finset.mem_image]
  exact ⟨Nat.Partition.indiscrete 2,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩

/-- **The sep-inert classify glue** (the previously-uncertain item, landed via the banked
order-0 characterization): a genuine monic quadratic whose box pair lies in `SepInertCell N`
is sent by the genuine level-`N` classifier to the order-0 inert shape
`sepShape 2 (indiscrete 2)`. Route: the odd–odd digit reads decode to nonzero mod-2 residues
(`toZMod_ne_of_box_not_dvd`), the residual `x² + x + 1` is root-free hence irreducible
(`residual_irreducible` at the `noRootPairs 2` membership), and irreducible-monic-quadratic
membership in the level-1 separable stratum `sepStratum (ZMod 2) 2 (indiscrete 2)` (pattern
`{2}` via `normalizedFactors_irreducible`) converts through
`Order0.classify_eq_sepShape_iff` (mpr). AXIOM-FREE. -/
theorem sepInert_classify_glue {N : ℕ} (hN : 0 < N) {f : Polynomial ℤ_[M9.realP]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : SeriesAssembly.SepInertCell N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    B.classify M9.realP 2 N (PadicLift.toBox M9.realP 2 N hN f hf hdeg)
      = Order0.sepShape 2 (Nat.Partition.indiscrete 2) := by
  obtain ⟨hd0, hd1⟩ := hfib
  have hw₀ : PadicInt.toZMod (f.coeff 0) ≠ 0 := toZMod_ne_of_box_not_dvd M9.realP hN hd0
  have hw₁ : PadicInt.toZMod (f.coeff 1) ≠ 0 := toZMod_ne_of_box_not_dvd M9.realP hN hd1
  have hone : ∀ x : ZMod M9.realP, x ≠ 0 → x = 1 := by decide
  have hmem : (PadicInt.toZMod (f.coeff 0), PadicInt.toZMod (f.coeff 1))
      ∈ ChainMenu.noRootPairs M9.realP := by
    rw [ChainMenu.mem_noRootPairs]
    show ∀ r : ZMod M9.realP,
      r ^ 2 + PadicInt.toZMod (f.coeff 1) * r + PadicInt.toZMod (f.coeff 0) ≠ 0
    rw [hone _ hw₁, hone _ hw₀]
    decide
  -- the mod-2 reduction of `f` is irreducible (it is the root-free residual quadratic)
  have hirr : Irreducible (f.map (PadicInt.toZMod (p := M9.realP))) := by
    rw [monic_quadratic_eq M9.realP hf hdeg]
    exact residual_irreducible M9.realP hmem
  have hdegmap : (f.map (PadicInt.toZMod (p := M9.realP))).natDegree = 2 := by
    rw [hf.natDegree_map, hdeg]
  -- the two-step reduction (level N, then mod p) IS the direct mod-p reduction
  have hhom : (ZMod.castHom (dvd_pow_self M9.realP hN.ne') (ZMod M9.realP)).comp
      (PadicInt.toZModPow (p := M9.realP) N) = (PadicInt.toZMod (p := M9.realP)) := by
    refine RingHom.ext fun w => ?_
    rw [RingHom.comp_apply, ZMod.castHom_apply, ← ZMod.natCast_val,
      ← toZMod_eq_val_toZModPow M9.realP hN w]
  refine (Order0.classify_eq_sepShape_iff M9.realP 2 N hN (by norm_num)
    (Nat.Partition.indiscrete 2) _).mpr ?_
  rw [PadicLift.toBox_val, Polynomial.map_map, hhom]
  refine ⟨hf.map _, hdegmap, hirr.squarefree, ?_, ?_⟩
  · -- `X ∤` (unit constant coefficient)
    intro hdvd
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_map] at hdvd
    exact hw₀ hdvd
  · -- factor-degree pattern `{2}` (one irreducible factor of degree 2)
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr,
      (hf.map _).normalize_eq_self, Multiset.map_singleton, hdegmap,
      Nat.Partition.indiscrete_parts (by norm_num)]

/-- **The order-0 inert cell has the genuine certificate of the inert type** — the sep-inert
EXISTENCE leg of the assembled theorem (footprint: core + `om_leaf_faithful`, through the
landed W2 consumer `menuFiber_hasType`; the matching all-bundle FORCING guard is the
axiom-free `QpTypeChainAll.sepInertCell_forced`). -/
theorem sepInertCell_hasType {N : ℕ} (hN : 0 < N) {f : Polynomial ℤ_[M9.realP]}
    (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : SeriesAssembly.SepInertCell N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    ∃ Fc : QpType.QpFactorization M9.realP f,
      QpType.qpType M9.realP Fc = ChainMenu.inertType2 := by
  obtain ⟨Fc, hFc⟩ := OmLeafFaithful.menuFiber_hasType M9.realP 2 N hN
    (Order0.unramType 2 (Nat.Partition.indiscrete 2))
    (Order0.sepShape 2 (Nat.Partition.indiscrete 2))
    sepShape_indiscrete2_mem_omMenuW f hf hdeg
    (sepInert_classify_glue hN hf hdeg hfib)
  exact ⟨Fc, hFc.trans unramType_indiscrete_two⟩

/-! ## Block 3 — the chain axiom route (existence on ANY translated chain fiber with
menu-side data)

The `TransChain ĉ` fiber of `f` is the `ChainPair` fiber of the genuine translate
`g = f(x + ĉ)` (`transChain_fiber_iff`); that pair-level fiber IS the `ChainCell` box fiber of
`g` (the `toBox` coefficients are `toZModPow` of `g`'s — the `chainStep_decode` unfold
pattern), i.e. the `fiberOf5` fiber of the chain literal `chainLit ms leaf`
(`fiberOf5_chain` + exact decode); the literal is on the scope-#5 menu `omMenu6 2 N N σ`
(depth-0 literals via `chainShapes0`, depth-`≥ 1` via `chainShapes` into `omMenu5 ⊆ omMenu6`);
the re-scoped axiom hands `g` a certificate of type σ, and the PROVED pure translation
transport (`qpType_translate_rescale` at `a = 1`, relation `translate_rel`) carries it to `f`.
Per (P4d), NO translation form enters the axiom — the translate is derived. -/

/-- **Existence on any translated chain fiber, through the menu** (footprint: core +
`om_leaf_faithful`). Consumed by the `ram`/`inert` legs of `fullFiber_hasType`; note NO
budget hypothesis — below the budget the fiber is empty and the statement vacuous, above it
the axiom's menu instance fires; the axiom route needs neither case. -/
theorem transChain_menuFiber_hasType {N : ℕ} (hN : 0 < N) {σ : FactorizationType}
    (c : ℕ) {ms : List ℕ} {leaf : ChainMenu.ChainLeaf}
    (hms : ms ∈ ChainMenu.msMenu N N) (hleaf : leaf ∈ ChainMenu.chainLeaves N σ)
    {f : Polynomial ℤ_[M9.realP]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : SeriesAssembly.TransChain c ms leaf N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    ∃ Fc : QpType.QpFactorization M9.realP f, QpType.qpType M9.realP Fc = σ := by
  -- the genuine translate `g = f(x + c)` and its fiber
  have hg : (f.comp (X + C (c : ℤ_[M9.realP]))).Monic :=
    comp_translate_monic M9.realP hf hdeg _
  have hgdeg : (f.comp (X + C (c : ℤ_[M9.realP]))).natDegree = 2 :=
    comp_translate_natDegree M9.realP hf hdeg _
  have hfib' := (transChain_fiber_iff ms leaf hf hdeg c N).mp hfib
  -- the pair-level fiber IS the `ChainCell` box fiber of `g` (the `chainStep_decode` pattern)
  have hcoeff : ∀ i,
      ((PadicLift.toBox M9.realP 2 N hN (f.comp (X + C (c : ℤ_[M9.realP]))) hg hgdeg).1).coeff i
        = PadicInt.toZModPow N ((f.comp (X + C (c : ℤ_[M9.realP]))).coeff i) := by
    intro i
    rw [PadicLift.toBox_val, Polynomial.coeff_map]
  have hcell : ChainMenu.ChainCell M9.realP ms leaf
      (PadicLift.toBox M9.realP 2 N hN (f.comp (X + C (c : ℤ_[M9.realP]))) hg hgdeg) := by
    unfold ChainMenu.ChainCell
    rw [hcoeff 0, hcoeff 1]
    exact hfib'
  -- i.e. the `fiberOf5` fiber of the chain literal
  have hfib5 : OmLeafFaithful.fiberOf5 M9.realP 2 N hN (ChainMenu.chainLit ms leaf)
      (f.comp (X + C (c : ℤ_[M9.realP]))) hg hgdeg := by
    rw [OmLeafFaithful.fiberOf5_chain M9.realP 2 N hN
        (ChainMenu.headOrd_chainLit ms leaf) _ hg hgdeg,
      ChainMenu.decodeMs_chainLit, ChainMenu.decodeLeaf_chainLit]
    exact hcell
  -- the literal is on the scope-#5 menu (depth 0 via `chainShapes0`, else via `omMenu5`)
  have hT : ChainMenu.chainLit ms leaf ∈ ChainMenu6.omMenu6 2 N N σ := by
    by_cases hnil : ms = []
    · subst hnil
      exact ChainMenu6.mem_omMenu6_cases.mpr (Or.inr ⟨rfl, leaf, hleaf, rfl⟩)
    · refine ChainMenu6.omMenu5_subset_omMenu6 2 N N σ ?_
      rw [ChainMenu.omMenu5]
      exact Finset.mem_union_right _
        (ChainMenu.mem_chainShapes.mpr ⟨rfl, ms, leaf, hms, hnil, hleaf, rfl⟩)
  -- the axiom hands `g` a certificate; the proved pure translation carries it to `f`
  obtain ⟨Fg, hFg⟩ := OmLeafFaithful.om_leaf_faithful M9.realP 2 N hN σ
    (ChainMenu.chainLit ms leaf) N N hT (f.comp (X + C (c : ℤ_[M9.realP]))) hg hgdeg hfib5
  obtain ⟨Fc, hFc⟩ := qpType_translate_rescale M9.realP (1 : ℤ_[M9.realP]) (c : ℤ_[M9.realP])
    one_ne_zero (translate_rel M9.realP f (c : ℤ_[M9.realP])) Fg
  exact ⟨Fc, hFc.trans hFg⟩

/-! ## Block 4 — THE assembled theorem (blueprint §2-W6c-c, the wave's payoff) -/

/-- **THE full-model faithfulness theorem** (`fullFiber_hasType`, scope-#5 payoff): every
genuine monic quadratic `f : ℤ_[2][X]` whose coefficient box pair lies in ANY decided fiber
of the full `n = 2` model's per-type count (`decidedCount6 σ N` — index mirrored by
`W6FiberOK`) has a genuine ℚ_2-factorization certificate of the keyed type σ.

Per-family route (blueprint §1.4 table): `sepSplit` — the (S0) master, AXIOM-FREE
(`sepSplitCell_hasType`); `sepInert` — the banked order-0 classify glue + the axiom via the
W2 consumer (`sepInertCell_hasType`); chain-`split` — the (S) master through the unwind +
translate, AXIOM-FREE above the budget (`transChainFiber_split_hasType`), fiber EMPTY below
it (`chainPair_empty`); chain-`ram`/`inert` — the axiom on the translated polynomial through
the scope-#5 menu (`transChain_menuFiber_hasType`). Footprint: Lean core + `om_leaf_faithful`
EXACTLY (the census). -/
theorem fullFiber_hasType {N : ℕ} (hN : 0 < N) {σ : FactorizationType} {F : W6Fiber}
    (hOK : W6FiberOK F N σ)
    {f : Polynomial ℤ_[M9.realP]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : fiberPred F N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    ∃ Fc : QpType.QpFactorization M9.realP f, QpType.qpType M9.realP Fc = σ := by
  cases F with
  | sepSplit =>
      have hσ : σ = ChainMenu.splitType2 := hOK
      subst hσ
      exact sepSplitCell_hasType hN hf hdeg hfib
  | sepInert =>
      have hσ : σ = ChainMenu.inertType2 := hOK
      subst hσ
      exact sepInertCell_hasType hN hf hdeg hfib
  | chain c ms leaf =>
      obtain ⟨-, hms, hleaf⟩ := hOK
      cases leaf with
      | ram H => exact transChain_menuFiber_hasType hN c hms hleaf hf hdeg hfib
      | inert m => exact transChain_menuFiber_hasType hN c hms hleaf hf hdeg hfib
      | split k =>
          have hms1 : ∀ m ∈ ms, 1 ≤ m :=
            fun m hm => (((ChainMenu.mem_msMenu N N ms).mp hms).2 m hm).1
          by_cases hbud :
              2 * ms.sum + ChainMenu.leafNeed (ChainMenu.ChainLeaf.split k) ≤ N
          · obtain ⟨Fc, hFc⟩ := transChainFiber_split_hasType hms1 hbud hf hdeg hfib
            have hσ : ChainMenu.splitType2 = σ := by
              rw [← ChainMenu.leafType_split k]
              exact (ChainMenu.of_mem_chainLeaves hleaf).2
            exact ⟨Fc, hFc.trans hσ⟩
          · -- below the budget the fiber is EMPTY: contradiction with membership
            have hfib' : ChainMenu.ChainPair M9.realP ms (ChainMenu.ChainLeaf.split k) N N
                (SeriesAssembly.transMap c N
                  (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :=
              hfib
            exact absurd hfib' (ChainMenu.chainPair_empty M9.realP ms
              (ChainMenu.ChainLeaf.split k) N N (by omega) _)

/-- **The split-keyed legs, packaged AXIOM-FREE** (the census corollary): on the two
split-keyed fiber families of the model — order-0 `sepSplit` and every chain-`split` — the
certificate of `fullFiber_hasType` is PROVED outright (the (S0)/(S) masters through the
unwind and translate; emptiness below the budget). Footprint: Lean core ONLY. -/
theorem fullFiber_split_hasType_axfree {N : ℕ} (hN : 0 < N) {F : W6Fiber}
    (hOK : W6FiberOK F N ChainMenu.splitType2)
    (hsplit : F = W6Fiber.sepSplit
      ∨ ∃ c ms k, F = W6Fiber.chain c ms (ChainMenu.ChainLeaf.split k))
    {f : Polynomial ℤ_[M9.realP]} (hf : f.Monic) (hdeg : f.natDegree = 2)
    (hfib : fiberPred F N
      (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :
    ∃ Fc : QpType.QpFactorization M9.realP f,
      QpType.qpType M9.realP Fc = ChainMenu.splitType2 := by
  rcases hsplit with rfl | ⟨c, ms, k, rfl⟩
  · exact sepSplitCell_hasType hN hf hdeg hfib
  · obtain ⟨-, hms, -⟩ := hOK
    have hms1 : ∀ m ∈ ms, 1 ≤ m :=
      fun m hm => (((ChainMenu.mem_msMenu N N ms).mp hms).2 m hm).1
    by_cases hbud : 2 * ms.sum + ChainMenu.leafNeed (ChainMenu.ChainLeaf.split k) ≤ N
    · exact transChainFiber_split_hasType hms1 hbud hf hdeg hfib
    · have hfib' : ChainMenu.ChainPair M9.realP ms (ChainMenu.ChainLeaf.split k) N N
          (SeriesAssembly.transMap c N
            (PadicInt.toZModPow N (f.coeff 0), PadicInt.toZModPow N (f.coeff 1))) :=
        hfib
      exact absurd hfib' (ChainMenu.chainPair_empty M9.realP ms
        (ChainMenu.ChainLeaf.split k) N N (by omega) _)

/-! ## Block 5 — axiom census

Expected footprints: `fullFiber_hasType` / `transChain_menuFiber_hasType` /
`sepInertCell_hasType` = Lean core + `LeanUrat.OM.OmLeafFaithful.om_leaf_faithful` EXACTLY;
EVERYTHING ELSE (the `W6Fiber` machinery, the `decidedCount6` correspondence lemmas, the
sep-inert classify glue, `fullFiber_split_hasType_axfree`) = Lean core only
(`propext, Classical.choice, Quot.sound`). Any OTHER axiom appearing anywhere is a FAILURE. -/

section AxCheck

#print axioms LeanUrat.OM.FullFaithful.fiberPred
#print axioms LeanUrat.OM.FullFaithful.keyedType
#print axioms LeanUrat.OM.FullFaithful.W6FiberOK
#print axioms LeanUrat.OM.FullFaithful.fiberPred_sepSplit
#print axioms LeanUrat.OM.FullFaithful.fiberPred_sepInert
#print axioms LeanUrat.OM.FullFaithful.fiberPred_chain
#print axioms LeanUrat.OM.FullFaithful.keyedType_sepSplit
#print axioms LeanUrat.OM.FullFaithful.keyedType_sepInert
#print axioms LeanUrat.OM.FullFaithful.keyedType_chain
#print axioms LeanUrat.OM.FullFaithful.W6FiberOK_sepSplit
#print axioms LeanUrat.OM.FullFaithful.W6FiberOK_sepInert
#print axioms LeanUrat.OM.FullFaithful.W6FiberOK_chain
#print axioms LeanUrat.OM.FullFaithful.keyedType_eq_of_OK
#print axioms LeanUrat.OM.FullFaithful.sepCount6_split_eq_card
#print axioms LeanUrat.OM.FullFaithful.sepCount6_inert_eq_card
#print axioms LeanUrat.OM.FullFaithful.chainCount6_eq_sum_card
#print axioms LeanUrat.OM.FullFaithful.unramType_indiscrete_two
#print axioms LeanUrat.OM.FullFaithful.sepShape_indiscrete2_mem_omMenuW
#print axioms LeanUrat.OM.FullFaithful.sepInert_classify_glue
#print axioms LeanUrat.OM.FullFaithful.sepInertCell_hasType
#print axioms LeanUrat.OM.FullFaithful.transChain_menuFiber_hasType
#print axioms LeanUrat.OM.FullFaithful.fullFiber_hasType
#print axioms LeanUrat.OM.FullFaithful.fullFiber_split_hasType_axfree

end AxCheck

end LeanUrat.OM.FullFaithful
