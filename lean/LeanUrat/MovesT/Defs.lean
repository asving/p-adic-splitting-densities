/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesSp.Defs
import LeanUrat.MovesS.Interfaces
import LeanUrat.MovesS.EvalReDef
import LeanUrat.HC2.Defs

/-!
# MovesT/Defs — shared vocabulary for §T-ASSEMBLY (the branch-to-tree mass assembly)

E-PHASE elaboration of `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md` §2 (REV 9,
CLOSING). Every displayed §2 definition, in the blueprint's NORMATIVE declaration
order (§2.5's order note). Elaboration deviations are recorded in `MANIFEST.json`
("deviations") and flagged `[E-DEV n]` in docstrings. Zero `sorry`, zero axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesT

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-! ### §2.1 (VP-1) — the verdict alphabet -/

/-- (VP-1) VERDICT ALPHABET: "V := { finite multisets v of pairs (E, F) ∈ ℕ_{≥1}² }"
(MOVES 7061–7063). -/
def VerdictOK (v : Multiset (ℕ × ℕ)) : Prop := ∀ ef ∈ v, 1 ≤ ef.1 ∧ 1 ≤ ef.2

abbrev Vd : Type := {v : Multiset (ℕ × ℕ) // VerdictOK v}

/-- Σ_{(E,F) ∈ v} E·F — a τ-halted leaf of a degree-d cluster carries v with deg = d
(7062–7063; "Theorem U's σ is the whole-f instance, d = n"). -/
def Vd.deg (v : Vd) : ℕ := (v.1.map fun ef => ef.1 * ef.2).sum

/-- the degree-d slice (the finite alphabet actually carried by degree-d clusters). -/
abbrev VdAt (d : ℕ) : Type := {v : Vd // v.deg = d}

/-- (τ-hen) verdict: v = {(1, g)} (7072–7073). -/
def henVerdict (g : ℕ) (hg : 1 ≤ g) : Vd :=
  ⟨{(1, g)}, by
    intro ef hef
    rw [Multiset.mem_singleton.mp hef]
    exact ⟨le_refl 1, hg⟩⟩

/-- (τ-irr) verdict: v = {(E, F)} at the branch's accumulated invariants (7074–7077). -/
def irrVerdict (E F : ℕ) (hE : 1 ≤ E) (hF : 1 ≤ F) : Vd :=
  ⟨{(E, F)}, by
    intro ef hef
    rw [Multiset.mem_singleton.mp hef]
    exact ⟨hE, hF⟩⟩

/-- (τ-ns) verdict: v = μ·{(E(Φ̂), F(Φ̂))} (7083). -/
def nsVerdict (μ E F : ℕ) (hE : 1 ≤ E) (hF : 1 ≤ F) : Vd :=
  ⟨Multiset.replicate μ (E, F), by
    intro ef hef; rw [Multiset.eq_of_mem_replicate hef]; exact ⟨hE, hF⟩⟩

/-! ### §2.2 accumulated invariants, the τ-irr firing datum, node-data lawfulness
(+ the §2.11 carrier/species helpers, HOISTED per the declaration-order note (1)) -/

/-- E := ∏_r e_r over the branch's reads (7075). -/
def accE (H : History p F) : ℕ := (H.nodes.map fun ν => ν.e).prod
/-- F := ∏_r g_r over the branch's reads (7075). -/
def accF (H : History p F) : ℕ := (H.nodes.map fun ν => ν.g).prod

/-- the snoc side condition (the built `History.snoc`/`mem_snoc` take exactly this —
MovesD/Defs: `hν : ν.species ≠ ReadSpecies.root`). §2.11. -/
def NodeExtends (H : History p F) (ν : Node p F) : Prop :=
  ν.species ≠ ReadSpecies.root

/-- the root-species predicate `readOf`'s monicTop guard reads. §2.11. -/
def IsRootSpecies (s : ReadSpecies) : Prop := s = ReadSpecies.root

instance : DecidablePred IsRootSpecies := fun s =>
  inferInstanceAs (Decidable (s = ReadSpecies.root))

/-- a site's child ROOT datum: at the model root, a root-species node (the track's
first window read); at a state, a snoc-extension datum. §2.11. -/
def ChildRoot : Option (History p F) → Node p F → Prop
  | none, ν => ν.species = ReadSpecies.root
  | some H, ν => NodeExtends H ν

/-- the child HISTORY of a site (the one-node history at the root — the
anonymous-constructor form the built `mem_single` itself displays — and the snoc at a
state). §2.11 [E-phase: the two `⟨…⟩` proof slots, filled]. -/
def childHist : ∀ (o : Option (History p F)) (ν : Node p F), ChildRoot o ν → History p F
  | none, ν, h =>
    ⟨[ν], by simp, by
      intro j hj
      have hj0 : j = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using hj)
      subst hj0
      have h' : ν.species = ReadSpecies.root := h
      simpa using h'⟩
  | some H, ν, h => H.snoc ν h

/-- the one-node history at a root child. §2.11. -/
def oneNode (ν : Node p F) (h : ChildRoot none ν) : History p F :=
  childHist none ν h

/-- the length-k nonempty prefix of H, as an Option (consumed by `chainReads`). §2.11
[E-phase: the take-proofs, filled]. -/
def prefixAt (H : History p F) (k : ℕ) : Option (History p F) :=
  if h : 0 < k ∧ k ≤ H.nodes.length then
    some ⟨H.nodes.take k,
      List.ne_nil_of_length_pos (by rw [List.length_take]; omega),
      by
        intro j hj
        rw [List.length_take] at hj
        have hjlt : j < H.nodes.length := by omega
        have := H.root_iff j hjlt
        simpa [List.getElem_take] using this⟩
  else none

open Classical in
/-- H's read list strictly above its ν-headed child root (`SubtreeTransport`'s
"same prescribed subtree" comparator). §2.11 [E-DEV: classical `decide` supplies the
Bool predicate — `Node` carries no `DecidableEq`]. -/
noncomputable def stripAbove (ν : Node p F) (H : History p F) : List (Node p F) :=
  (H.nodes.dropWhile (fun ν' => decide (ν' ≠ ν))).drop 1

/-- the built clause carrier under this corpus's name (§2.11; the built carrier is
`LevelClause`, MovesC/Defs 297). -/
abbrev FreshClause (p m : ℕ) := LeanUrat.MovesC.LevelClause p m

/-- per-node lawfulness — each read has e, g, μ ≥ 1 and its K-carrier card a p-power
(L3/§B2-DEF ledger data). Owner HC-2 (node-ledger content). -/
def NodeDataLawful (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) : Prop :=
  ∀ ν ∈ H.nodes, 1 ≤ ν.e ∧ 1 ≤ ν.g ∧ 1 ≤ ν.μ ∧
    Nat.card ↥ν.σ.K = p ^ ((Nat.card ↥ν.σ.K).factorization p)

/-- REV 3/4/5: **the KEYING-CONSTANT-FREE FRAGMENT of history lawfulness** — T-V8's
premise (§2.2's displayed 12-clause ShapeWF roster + 13-conjunct Matches roster live in
the blueprint; the fragment below is the NORMATIVE clause list). FENCED CONDITIONALITY
(§0 row): `HistoryCoherent` alone does NOT imply this; discharge is QUEUED ON Q1 (§4) —
until then `hlaw : HistLawful p n H` is an explicit hypothesis. -/
def HistLawful (p : ℕ) [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (n : ℕ) (H : History p F) : Prop :=
  NodeDataLawful p H ∧
  (∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).σ.Φ.natDegree = 1) ∧
  (∀ hj : 0 < H.nodes.length, Nat.card ↥((H.nodes[0]'hj).σ.K) = p) ∧      -- w₀ = 1
  (∀ (i : ℕ) (hi : i < H.nodes.length),                                    -- slope tie
    (H.nodes[i]'hi).line.slope *
        (((H.nodes[i]'hi).e : ℚ) * (H.strFrame i : ℚ) * ((H.nodes[i]'hi).Dwidth : ℚ))
      = ((H.nodes[i]'hi).h : ℚ)) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length),                                    -- γ-tie
    (((H.nodes[i]'hi).gam : ℤ) : ℚ)
      = ((H.nodes[i]'hi).e : ℚ) * ((H.strFrame i : ℚ) * (H.nodes[i]'hi).ustar)
        + ((((H.nodes[i]'hi).s0 + (H.nodes[i]'hi).wSide) : ℕ) : ℚ) * ((H.nodes[i]'hi).h : ℚ)) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length),                                    -- anchor/edvd/gmu
    ((H.nodes[i]'hi).e : ℤ) * (H.nodes[i]'hi).a
        = ((H.nodes[i]'hi).s0 : ℤ) - bezT (H.nodes[i]'hi).e (H.nodes[i]'hi).h * (H.nodes[i]'hi).gam ∧
      (H.nodes[i]'hi).e ∣ (H.nodes[i]'hi).wSide ∧
      (H.nodes[i]'hi).g * (H.nodes[i]'hi).μ
        ≤ (H.nodes[i]'hi).wSide / (H.nodes[i]'hi).e) ∧   -- REV 4: node-side len
  (∀ (i : ℕ) (hi : i + 1 < H.nodes.length),                                -- chain clauses
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide ≤ (H.nodes[i]'(by omega)).μ) ∧
    ((H.nodes[i+1]'hi).Dwidth = (H.nodes[i]'(by omega)).childWidth) ∧
    ((H.nodes[i]'(by omega)).line.slope < (H.nodes[i+1]'hi).line.slope) ∧
    (Nat.card ↥((H.nodes[i+1]'hi).σ.K)                    -- REV 4: W-MULTIPLICATIVITY
      = Nat.card ↥((H.nodes[i]'(by omega)).σ.K) ^ (H.nodes[i]'(by omega)).g)) ∧
  (∀ h0 : 0 < H.nodes.length, ((H.nodes[0]'h0).s0 + (H.nodes[0]'h0).wSide ≤ n)) ∧
  (∀ h0 : 0 < H.nodes.length,                              -- REV 5: MONIC-LEAD (§0.5)
    (H.nodes[0]'h0).s0 + (H.nodes[0]'h0).wSide = n →
      (H.nodes[0]'h0).sideDigit ((H.nodes[0]'h0).wSide / (H.nodes[0]'h0).e) = 1)

/-- (τ-irr) FIRES — the note's rule VERBATIM (REV 4): the saturation EQUATION
accE·accF = childWidth·μ at the latest read (7074–7080). Pure node/cell data: no box
input, no f. -/
def IrrHalts (H : History p F) : Prop :=
  H.nodes ≠ [] ∧
  (H.nodes.getLast?).elim False
    (fun ν => accE H * accF H = ν.childWidth * ν.μ)

/-- the (τ-irr) leaf's verdict — total via junk 1s off the lawful domain (T-V8's
`acc_pos` proves the guards dead under `NodeDataLawful`). -/
noncomputable def irrVerdictOf (H : History p F) : Vd :=
  irrVerdict (max (accE H) 1) (max (accF H) 1) (le_max_right _ _) (le_max_right _ _)

/-- REV 2 (Codex 3): the (τ-ns) leaf's verdict VALUE — v = μ·{(E(Φ̂), F(Φ̂))} (7083). -/
noncomputable def nsVerdictOf (H : History p F) : Vd :=
  nsVerdict ((H.nodes.getLast?).elim 1 fun ν => ν.μ)
    (max (accE H) 1) (max (accF H) 1) (le_max_right _ _) (le_max_right _ _)

/-! ### §2.3 the root reduction datum and (τ-hen) -/

/-- the level-0 reduction f̄ of a box member, through an injective level-0 chart χ:
monic degree-n over F_p = ZMod p (7069–7071; (JC-root) 7464–7466). -/
noncomputable def redPoly (χ : Fin n → Fin m) (x : Box p m) : Polynomial (ZMod p) :=
  Polynomial.X ^ n + ∑ b : Fin n, Polynomial.C (x (χ b)) * Polynomial.X ^ (b : ℕ)

/-- the level-0 cell {f : f̄ = g} ((JC-root), 7464). -/
def rootCell (χ : Fin n → Fin m) (g : Fin n → ZMod p) : Set (Box p m) :=
  {x | ∀ b : Fin n, x (χ b) = g b}

/-- the Hensel-track degrees of x: degrees of the SIMPLE (multiplicity-1) monic
irreducible factors of f̄ (7071–7073). -/
noncomputable def henDegrees (χ : Fin n → Fin m) (x : Box p m) : Multiset ℕ :=
  ((UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)).toFinset.filter
    (fun ψ => Multiset.count ψ
      (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)) = 1)).val.map
    Polynomial.natDegree

/-- the (τ-hen) verdict payload of x. [E-phase note carried: `max g 1` guard —
irreducible factors have degree ≥ 1, the guard is dead; the def stays total.] -/
noncomputable def henPayload (χ : Fin n → Fin m) (x : Box p m) : Multiset Vd :=
  (henDegrees χ x).map (fun g => henVerdict (max g 1) (le_max_right _ _))

/-! ### §2.4 τ over the model, pruning, decidedness (KB-TOT lands after §2.5a) -/

/-- (τ-ns) FIRES at (o, x): the state is realized and its branch set at x is EMPTY —
"CELLS whose window admits no side (J(f) = ∅)" (7081–7083). DEFINITIONAL FACE ONLY
(rev 3): its Theorem-B faithfulness is `KBTot.ns_lumps` below. -/
def NsHalts (T : TreeModel p F n N m pol) (o : Option (History p F)) (x : Box p m) :
    Prop :=
  T.mem o x ∧ ∀ ν : Node p F, ¬ T.child o ν x

/-- the per-child SATURATE-OR-CONTINUE law (the (a)-leg of KB-TOT): "each branch of the
branch set then either saturates (μ = 1: τ-irr halt) or has μ ≥ 2 and CONTINUES"
(7114–7118). -/
def BranchDichotomy (T : TreeModel p F n N m pol) : Prop :=
  ∀ (H : History p F) (x : Box p m), T.mem (some H) x →
    ∀ (ν : Node p F) (hν : NodeExtends H ν), T.child (some H) ν x →
      (ν.μ = 1 ∧ IrrHalts (H.snoc ν hν)) ∨
      (2 ≤ ν.μ ∧ T.mem (some (H.snoc ν hν)) x)

/-- τ-PRUNED membership: H ∈ T_can^τ(x) — realized, and NO proper NONEMPTY prefix
τ-halts (7086–7088). REV 2 (Codex 2): the `H'.nodes ≠ []` guard is IN the quantifier. -/
def PrunedMem (T : TreeModel p F n N m pol) (H : History p F) (x : Box p m) : Prop :=
  T.mem (some H) x ∧
  ∀ H' : History p F, H'.IsPrefixOf H → H' ≠ H → H'.nodes ≠ [] →
    ¬ IrrHalts H' ∧ ¬ NsHalts T (some H') x

/-! ### §2.5 tail, HOISTED per the declaration order (2): readOf / shapeOfH / shapeExp -/

/-- [E-DEV] junk `ShapeRead` powering `Inhabited` (the blueprint's `shapeOfH` uses
`default`; the built `ShapeRead` carries proof fields, so a concrete junk value is
supplied — all-1 data, `.root` species, `monicTop := false`). -/
def junkRead : ShapeRead :=
  { species := ReadSpecies.root, e := 1, h := 1, g := 1, μ := 1, a := 0, s0 := 0,
    wSide := 0, Dwidth := 1, ustar := 0, gam := 0, w := 1, monicTop := false,
    he := le_refl 1, hg := le_refl 1, hμ := le_refl 1, hw := le_refl 1,
    hDw := le_refl 1, hh := le_refl 1, hcop := by norm_num,
    hspecInc := by intro h; simp at h,
    hspecRec := fun _ => ⟨rfl, rfl⟩,
    hmonicRoot := by intro h; rfl }

instance : Inhabited ShapeRead := ⟨junkRead⟩

/-- the retained ShapeRead of a node (the L3 dictionary, node → shape side),
componentwise (§2.5): species/e/h/g/μ/a/s0/wSide/Dwidth/ustar/gam copy ν's like-named
fields; the REV-4 junk guards `w := max … 1` and the monicTop root-species conjunct are
displayed IN the value, each DEAD on the lawful domain (T-V8's `readOf_guards_dead`).
[E-DEV: the built `ShapeRead` additionally demands `hDw : 1 ≤ Dwidth`, so the value
carries the THIRD junk guard `Dwidth := max ν.Dwidth 1` — dead on the lawful domain
(root Φ-degree 1 + the Dwidth chain give Dwidth ≥ 1), same genre as the two displayed
guards; recorded in MANIFEST.] -/
noncomputable def readOf (ν : Node p F) (r : ℕ) (n : ℕ) : ShapeRead :=
  { species := ν.species, e := ν.e, h := ν.h, g := ν.g, μ := ν.μ, a := ν.a,
    s0 := ν.s0, wSide := ν.wSide, Dwidth := max ν.Dwidth 1, ustar := ν.ustar,
    gam := ν.gam, w := max ((Nat.card ↥ν.σ.K).factorization p) 1,
    monicTop := decide (r = 0 ∧ ν.s0 + ν.wSide = n ∧ IsRootSpecies ν.species),
    he := ν.he, hg := ν.hg, hμ := ν.hμ, hw := le_max_right _ _,
    hDw := le_max_right _ _, hh := ν.hh, hcop := ν.hcop,
    hspecInc := ν.hspecInc, hspecRec := ν.hspecRec,
    hmonicRoot := fun h => (of_decide_eq_true h).2.2 }

/-- the shape of a history (unit T-V8 proves MatchesHist + ShapeWF via SW1). -/
noncomputable def shapeOfH (H : History p F) (n : ℕ) : ShapePrefix :=
  ⟨(List.range H.nodes.length).map fun r => (H.nodes[r]?).elim default
    (fun ν => readOf ν r n)⟩

open Classical in
/-- the L3 dictionary's PER-READ FRESH EXPONENT carrier — REV 7 (Codex-6 #7): CLOSED
over the BUILT MovesD band apparatus (`ShapePrefix.bandS`, `Nshape`). The fresh
coordinates (level, base) of R's LAST read's band system. -/
noncomputable def bandFresh (R : ShapePrefix) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range R.Nshape ×ˢ Finset.range n).filter
    (fun c => R.bandS n (R.reads.length - 1) c)

/-- the per-read fresh exponent of a shape prefix (T-E10's `hdict` carrier; the
NORMATIVE mstar clause rides in the blueprint §2.5). -/
noncomputable def shapeExp (R : ShapePrefix) (n : ℕ) : ℕ := (bandFresh R n).card

/-! ### §2.5 site vocabulary, part 1: state events + the ENTRANCE carrier (order (3)) -/

/-- the STATE EVENT of a site — the event that x realizes the site's entrance state.
At the root this is the ambient box (`TreeModel.root_mem` makes it `univ`). -/
def stateEvent (T : TreeModel p F n N m pol) (o : Option (History p F)) :
    Set (Box p m) := {x | T.mem o x}

/-- **the ENTRANCE-STATE carrier** — REV 3 (Codex-2 #8). Three constructors: the
ambient box, a REDUCTION CELL (keyed by the level-0 datum g WITH the track's reduction
factor ψ), a realized chain state. [E-DEV: the carrier takes the instance binders
`[Fact p.Prime] [Field F] [Finite F]` — the `.st` constructor stores a `History`.] -/
inductive EntSt (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] (n : ℕ) where
  | amb : EntSt p F n
  | red (g : Fin n → ZMod p) (ψ : Polynomial (ZMod p)) : EntSt p F n
  | st (H : History p F) : EntSt p F n

/-- the entrance EVENT: what a site's charge law conditions on. -/
def entEvent (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) :
    EntSt p F n → Set (Box p m)
  | .amb => Set.univ
  | .red g _ => rootCell χ g
  | .st H => stateEvent T (some H)

/-- the Option-state embedding (the rev-2 vocabulary is the .amb/.st sub-family). -/
def embE : Option (History p F) → EntSt p F n
  | none => .amb
  | some H => .st H

/-- the Option-state under child events (§2.6): .st H ↦ some H; .amb/.red ↦ none
(first window reads are `T.child none` children). -/
def stOf : EntSt p F n → Option (History p F)
  | .st H => some H
  | _ => none

/-! ### §2.9 part 1 (order (3)): the cell layer — `CellData`, the bundled `CellAssign`,
cell events, eligibility, the root laws -/

/-- the joint-cell assignment DATA layer — MovesT's cell vocabulary (the W4-1/W4-2
re-keying target). REV 8 (Codex-7 #1, the rename): the former `CellAssign` field
roster; the W4-1 INTERFACE `CellAssign` is the bundled structure below. REV 6
(Fable-5 CRIT-1): `child_cell` is SCOPED TO SOME-STATES (§0 record 13). -/
structure CellData (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (T : TreeModel p F n N m pol) where
  Cell : Type
  hCellFin : Finite Cell
  cellOf : EntSt p F n → Box p m → Cell
  cellLevel : EntSt p F n → ℕ
  levelOf : Fin m → ℕ
  cell_local : ∀ (es : EntSt p F n) (x x' : Box p m),
    (∀ c : Fin m, levelOf c < cellLevel es → x c = x' c) → cellOf es x = cellOf es x'
  branchSetOf : Cell → Finset (Node p F)
  child_cell : ∀ (H : History p F) (ν : Node p F) (x : Box p m),
    T.mem (some H) x →
    (T.child (some H) ν x ↔ ν ∈ branchSetOf (cellOf (.st H) x))
  child_root_sub : ∀ (ν : Node p F) (x : Box p m),
    T.child none ν x → ν ∈ branchSetOf (cellOf .amb x)
  child_cell_red : ∀ (χ : Fin n → Fin m) (g : Fin n → ZMod p)
      (ψ : Polynomial (ZMod p)) (ν : Node p F) (x : Box p m),
    x ∈ rootCell χ g → ν ∈ branchSetOf (cellOf (.red g ψ) x) → T.child none ν x
  /-- **the ROOT-CELL-UNIFORMITY law** — ADJUDICATED ADDITION (2026-07-30, the
  assembly-spine statement-repair round: the E5/E8 countermodels exploited a STRAY
  `T.child none` child realized at a single point of one root reduction cell, which
  no displayed law forbade). `T.child none` is `cellOf`-CONSTANT on root cells: two
  points of ONE root reduction cell (one `cellOf (.red g ψ)` fiber) have the same
  child-none behavior. WARRANT: the §5 W4-1/ChildCover row + the (c2) covering
  display (MOVES 7112–7119, "fix f and a live track. At level 0, m_i = 1 gives
  τ-hen and m_i ≥ 2 opens the window — total"): the level-0 case analysis is
  PER-TRACK data of the reduction cell, never of the individual box point — the
  window either opens on the whole cell or on none of it. -/
  child_red_uniform : ∀ (g : Fin n → ZMod p) (ψ : Polynomial (ZMod p))
      (x y : Box p m),
    cellOf (.red g ψ) x = cellOf (.red g ψ) y →
    ∀ ν : Node p F, T.child none ν x ↔ T.child none ν y
  /-- **THE MEMBER-KEYED SITE READ** — THE SITE-ENTRANCE KEYING (2026-08-01, the
  T re-ratification REJECT-M repair; verdict: "for two co-realized sibling sites
  with the same `parentSt`, `state_cell` … forces their exact cells—and hence
  state events—to coincide whenever they share a fiber witness … the carrier
  still lacks the site/branch/frame index needed to represent distinct sibling
  reads"). ADJUDICATED FIX (orchestrator): the branch taken is part of the child
  site's entrance datum — the note's TREE-EXP recursion has each child recurse
  FROM the joint cell WITH its member index (MOVES 7503–7515; the (SIB)
  conditioning is Σ_c THEN the branch). `branchCellOf es ν` is the site read map
  Ψ_s of the site whose entrance is `es` and whose own branch node is ν — the
  note's per-site Ψ in jvol(c_s │ Σ) = μ(Ψ^{−1}(c_s) │ Σ) (7448–7449). Sibling
  sites ν ≠ ν' key DIFFERENT read maps on the SAME entrance event: distinct site
  cells no longer force equal (or disjoint) state events. -/
  branchCellOf : EntSt p F n → Node p F → Box p m → Cell
  /-- the site read is JOINT-CELL DATA: it factors through the entrance-keyed
  joint read `cellOf es` — the member-index projection of the joint children
  read ("[the joint cell is] in general FINER than any single branch's
  (side, ψ) node stratum", MOVES 7447–7448). This law is what keeps the re-keyed
  site cell event EXACT (a union of exact joint-read fibers selected by the
  site's own cell value), never free data. -/
  branch_cell_joint : ∀ (es : EntSt p F n) (ν : Node p F) (x y : Box p m),
    cellOf es x = cellOf es y → branchCellOf es ν x = branchCellOf es ν y

/-- THE CELL EVENT Σ_c — the note's conditioning object (7290–7292), DEFINED. -/
def cellEvent (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (o : Option (History p F)) (c : CA.Cell) : Set (Box p m) :=
  {x | T.mem o x ∧ CA.cellOf (embE o) x = c}

/-- the ENTRANCE form of the cell event (REV 3) — serves the reduction-cell entrances. -/
def cellEventE (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (c : CA.Cell) : Set (Box p m) :=
  {x | x ∈ entEvent T χ es ∧ CA.cellOf es x = c}

/-- the site's OWN node — the last node of its chain (the read datum the site carries;
the E8-adjudication vocabulary, 2026-07-30). -/
def _root_.LeanUrat.MovesC.History.lastNode (H : History p F) : Node p F :=
  H.nodes.getLast H.nonempty

/-- **THE PER-SITE CELL EVENT, SITE-ENTRANCE-KEYED EXACT-CELL FORM** — RE-KEYED at
the T RE-RATIFICATION (2026-08-01; verdict, material finding: "`siteCellEvent` is
keyed only by `es` and `c` … For two co-realized sibling sites with the same
`parentSt`, `state_cell` forces their exact cells—and hence state events—to
coincide whenever they share a fiber witness … the carrier still lacks the
site/branch/frame index needed to represent distinct sibling reads"). THE FIX:
the event gains the site's own BRANCH NODE ν as an argument — the entrance datum
of a site is (entrance state, member index), per the note's TREE-EXP recursion
(each child recurses from the joint cell WITH its member index, MOVES 7503–7515).
The event is the exact fiber Ψ_s^{−1}(c) over the entrance event, Ψ_s :=
`CA.branchCellOf es ν` the SITE's own read map (MOVES 7448–7449: "Write
jvol(c_s │ Σ) := μ(Ψ^{−1}(c_s) │ Σ)" — the note's Ψ is per-site, never shared
across siblings), `c` the site's own full joint cell (`SiteLedger.cellAt`).
The 2026-07-29 [date corrected 2026-07-30; original record mis-dated 2026-07-31]
form (Ψ keyed by the entrance alone) is superseded; its sibling
shared-cell forcing is now structurally dead — see `f1_two_leaf_discharge`
(T-E8) for the displayed check. -/
def siteCellEvent (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (ν : Node p F) (c : CA.Cell) :
    Set (Box p m) :=
  {x | x ∈ entEvent T χ es ∧ CA.branchCellOf es ν x = c}

/-- W4-1's re-keyed `eligible` — a DEFINED predicate over the cell/branch-set
vocabulary (cell data BY CONSTRUCTION; T-D1). -/
def eligibleT (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (o : Option (History p F)) (ν : Node p F)
    (x : Box p m) : Prop :=
  ν ∈ CA.branchSetOf (CA.cellOf (embE o) x)

/-- the root-cell tie: the root state's cell datum IS the reduction f̄ read through χ
((JC-root) 7464–7466). -/
def RootCellsOf (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) : Prop :=
  ∀ x y : Box p m, CA.cellOf .amb x = CA.cellOf .amb y ↔ ∀ b : Fin n, x (χ b) = y (χ b)

/-- **the reduction-cell branch PARTITION** — REV 4/5: the root's all-and-only law,
ANCHORED to each child's OWN root track through the shared `trackOf` accessor. -/
def RedCellPartition (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (trackOf : Node p F → Polynomial (ZMod p)) : Prop :=
  ∀ (g : Fin n → ZMod p) (x : Box p m), x ∈ rootCell χ g →
    (∀ ν : Node p F, T.child none ν x →
      trackOf ν ∈ (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)).toFinset
        ∧ ν ∈ CA.branchSetOf (CA.cellOf (.red g (trackOf ν)) x)
        ∧ ∀ ψ : Polynomial (ZMod p),
            ν ∈ CA.branchSetOf (CA.cellOf (.red g ψ) x) → ψ = trackOf ν) ∧
    (∀ (ψ : Polynomial (ZMod p)) (ν : Node p F),
      ν ∈ CA.branchSetOf (CA.cellOf (.red g ψ) x) → T.child none ν x)

/-- **the (c2) COVERING clause AT THE W4-1 INTERFACE** — REV 7 (ruling 1): at a
realized window-opening read (a repeated reduction factor ψ), a root child EXISTS
carrying that track's data, in the track-ψ reduction cell's own branch set.
Owner HC-2/D4R0K (L1 totality) — NEVER proved here. -/
def ChildCover (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (trackOf : Node p F → Polynomial (ZMod p)) : Prop :=
  ∀ (g : Fin n → ZMod p) (x : Box p m), x ∈ rootCell χ g →
    ∀ ψ : Polynomial (ZMod p),
      ψ ∈ UniqueFactorizationMonoid.normalizedFactors (redPoly χ x) →
      2 ≤ Multiset.count ψ
        (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)) →
      ∃ ν : Node p F, trackOf ν = ψ ∧ T.child none ν x ∧
        ν ∈ CA.branchSetOf (CA.cellOf (.red g ψ) x)

/-- **THE W4-1 INTERFACE, BUNDLED** — REV 8 (Codex-7 #1): `CellData` PLUS the mandatory
per-track covering field, at the designated chart and the shared L1 track accessor.
CONSUMPTION CONVENTION (REV 9, Codex-8 crit 6): displayed Lean writes `CA.toCellData`
EXPLICITLY at every `CellData` position; no `Coe` instance is declared. -/
structure CellAssign (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (trackOf : Node p F → Polynomial (ZMod p))
    extends CellData p F n N m pol T where
  child_cover : ChildCover T toCellData χ trackOf

/-! ### §2.5 finite pruned trees, fibers, sites, the site vocabulary, thresholds -/

/-- maximality in a chain set (leaf = no strict extension present). -/
def IsMaximalIn (S : Set (History p F)) (H : History p F) : Prop :=
  ∀ H' ∈ S, H.IsPrefixOf H' → H' = H

/-- A COMPLETE FINITE (canonical, τ-pruned) TREE — the (TGT) summation object
(7017–7024). -/
structure VTree (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  chains : Set (History p F)
  hfin : chains.Finite
  hne_nodes : ∀ H ∈ chains, H.nodes ≠ []
  hclosed : ∀ H ∈ chains, ∀ H' : History p F,
    H'.IsPrefixOf H → H'.nodes ≠ [] → H' ∈ chains
  henV : Multiset Vd
  hhen : ∀ v ∈ henV, ∃ g : ℕ, 1 ≤ g ∧ v.1 = {(1, g)}
  leafV : History p F → Option Vd
  hleaf : ∀ H, (leafV H).isSome ↔ (H ∈ chains ∧ IsMaximalIn chains H)
  nsLeaf : History p F → Prop
  hns_leaf : ∀ H, nsLeaf H → H ∈ chains ∧ IsMaximalIn chains H

/-- typemult(T) := ⊎_{leaves ℓ} v(ℓ) ⊎ henV (7024–7025); non-leaves contribute 0
through `leafV`'s `none`. -/
noncomputable def VTree.typemult (Tr : VTree p F) : Multiset (ℕ × ℕ) :=
  (Tr.henV.map Subtype.val).sum
    + ∑ H ∈ Tr.hfin.toFinset, ((Tr.leafV H).elim 0 Subtype.val)

/-- the tree's HEAD chains (REV 4, Codex-3 #2): the length-1 chains. -/
noncomputable def VTree.heads (Tr : VTree p F) : Finset (History p F) :=
  Tr.hfin.toFinset.filter (fun H => H.nodes.length = 1)

open Classical in
/-- the PER-TRACK leaf-degree total (REV 4, Codex-3 #2). -/
noncomputable def VTree.trackDeg (Tr : VTree p F) (H₀ : History p F) : ℕ :=
  ∑ H ∈ Tr.hfin.toFinset,
    if H₀.IsPrefixOf H then ((Tr.leafV H).elim 0 Vd.deg) else 0

/-- THE TREE FIBER {x : T_can^τ(x) = T}, graph-equality form — clauses (i)–(vi) per
the blueprint §2.5 (REV 4's per-track completeness clause (vi) included). -/
def VTree.fiberAt (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : Box p m) : Prop :=
  (∀ H : History p F, H ∈ Tr.chains ↔ (H.nodes ≠ [] ∧ PrunedMem T H x)) ∧
  (∀ H ∈ Tr.chains, IsMaximalIn Tr.chains H →
    ((IrrHalts H ∧ ¬ Tr.nsLeaf H ∧ Tr.leafV H = some (irrVerdictOf H)) ∨
     (NsHalts T (some H) x ∧ ¬ IrrHalts H ∧ Tr.nsLeaf H ∧
       Tr.leafV H = some (nsVerdictOf H)))) ∧
  Tr.henV = henPayload χ x ∧
  (∀ H ∈ Tr.chains, ¬ IsMaximalIn Tr.chains H →
    ¬ IrrHalts H ∧ ¬ NsHalts T (some H) x) ∧
  ((Tr.typemult.map fun ef => ef.1 * ef.2).sum = n) ∧
  (Tr.heads.val.map Tr.trackDeg
    = ((UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)).toFinset.filter
        (fun ψ => 2 ≤ Multiset.count ψ
          (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x)))).val.map
        (fun ψ => Multiset.count ψ
          (UniqueFactorizationMonoid.normalizedFactors (redPoly χ x))
            * ψ.natDegree))

/-- DECIDED at x := some complete finite tree fibers x (7580, 7586–7589). -/
def Decided (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) (x : Box p m) : Prop :=
  ∃ Tr : VTree p F, Tr.fiberAt T χ x

/-- REALIZABILITY of a tree — "for every complete finite REALIZABLE canonical tree T"
(7449–7451); REV 3 (Fable-2 CRIT-1): threaded as `hreal` on T-E5/E8/E11. -/
def Realizes (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (Tr : VTree p F) : Prop := ∃ x, Tr.fiberAt T χ x

/-- EXTENSIONAL EQUALITY of trees — the (chains, henV, leafV, nsLeaf) tuple (REV 3,
Codex-2 #24). -/
def VTree.ext (Tr Tr' : VTree p F) : Prop :=
  Tr.chains = Tr'.chains ∧ Tr.henV = Tr'.henV ∧
  ∀ H ∈ Tr.chains, Tr.leafV H = Tr'.leafV H ∧ (Tr.nsLeaf H ↔ Tr'.nsLeaf H)

/-- the tree-shape equivalence (REV 3, Codex-2 #14): a prefix-order isomorphism of
chain sets matching per-chain shapes and the hen payload. -/
def ShapeEquiv (n : ℕ) (Tr Tr' : VTree p F) : Prop :=
  Tr.henV = Tr'.henV ∧
  ∃ φ : {H // H ∈ Tr.chains} → {H // H ∈ Tr'.chains}, Function.Bijective φ ∧
    (∀ H H', H.1.IsPrefixOf H'.1 ↔ (φ H).1.IsPrefixOf (φ H').1) ∧
    (∀ H, shapeOfH (φ H).1 n = shapeOfH H.1 n) ∧
    (∀ H, (Tr.nsLeaf H.1 ↔ Tr'.nsLeaf (φ H).1))

/-- READ SITES of T (7441–7448): the root site plus every chain of T. -/
def VTree.sites (Tr : VTree p F) : Set (Option (History p F)) :=
  insert none (some '' Tr.chains)

/-- the WINDOW sites (every site but the root). -/
def VTree.windowSites (Tr : VTree p F) : Set (Option (History p F)) :=
  some '' Tr.chains

/-- the henflip record-update (T-G1's gate). §2.11. -/
def VTree.withHenV (Tr : VTree p F) (v : Multiset Vd)
    (hv : ∀ w ∈ v, ∃ g : ℕ, 1 ≤ g ∧ w.1 = {(1, g)}) : VTree p F :=
  { Tr with henV := v, hhen := hv }

/-- REV 2/3: the jet-site tie, NAMED — the site's cell event IS the transported
system's stratum, over the ENTRANCE carrier. Owner of instances: HC-2.
RE-KEYED at the T RE-RATIFICATION (2026-08-01, the site-entrance keying): the
presented face equates the site's exact cell event (`siteCellEvent es ν c` — ν
the site's own branch node, c its own full joint cell) with the presented
stratum — the note's Ψ_s^{−1}(c_s) over Σ. -/
def SitePresents (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (ν : Node p F) (c : CA.Cell)
    (Sigma : Locus p m) (fd : FreshData p m) : Prop :=
  siteCellEvent T CA χ es ν c = {x | Sigma.IsSolution x ∧ fd.sat x}
  ∧ entEvent T χ es = {x | Sigma.IsSolution x}

/-- REV 2: the level-separation premise for spectator events, EXPLICIT. -/
def SpectatorFor (fresh : Finset (Fin m)) (E : Set (Box p m)) : Prop :=
  ∀ x x' : Box p m, (∀ i : Fin m, i ∉ fresh → x i = x' i) → (x ∈ E ↔ x' ∈ E)

/-- REV 3/4/5: the SIDE DECOMPOSITION of a presented cell — per-side systems a
PARTITION of the presented system's OWN clauses, side SPANS disjoint, and the REV-5
POLYGON tie (`hullSlope`/`hslope`/`hside_read`). REV 9 (Codex-8 crit 4): `fd.clauses`
is a LIST — the partition's RHS is its membership set. -/
structure SideSplit (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (c : CA.Cell) (fd : FreshData p m) where
  k : ℕ
  sideOf : Node p F → Fin k
  side_ne : ∀ j : Fin k, ∃ ν ∈ CA.branchSetOf c, sideOf ν = j
  clausesOf : Fin k → Finset (FreshClause p m)
  hpartition : (⋃ j : Fin k, (clausesOf j : Set (FreshClause p m)))
      = {cl | cl ∈ fd.clauses} ∧
    Pairwise (Function.onFun Disjoint clausesOf)
  sideSpan : Fin k → Finset (Fin m)
  hspan_disj : Pairwise (Function.onFun Disjoint sideSpan)
  hsupport : ∀ j, ∀ cl ∈ clausesOf j, ∀ cIdx ∈ cl.support, cIdx ∈ sideSpan j
  hullSlope : Fin k → ℚ
  hslope : StrictMono hullSlope
  hside_read : ∀ ν ∈ CA.branchSetOf c, ν.line.slope = hullSlope (sideOf ν)

/-- the per-side exponent: the side subsystem's equation count. -/
def SideSplit.sideExp {T : TreeModel p F n N m pol} {CA : CellData p F n N m pol T}
    {c : CA.Cell} {fd : FreshData p m} (ss : SideSplit T CA c fd) (j : Fin ss.k) : ℕ :=
  (ss.clausesOf j).card

/-- a MULTI-SIDE site: its window hull has ≥ 2 sides (7473–7483). -/
def IsMultiSideSite (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (c : CA.Cell) {fd : FreshData p m} (ss : SideSplit T CA c fd) : Prop := 2 ≤ ss.k

/-- **(JC-multi), PER-SITE** — REV 2/3: the display 7473–7483 division-free, cell and
entrance events the DEFINED conditioning objects. OPEN obligation; NEVER proved here.
RE-KEYED at the T RE-RATIFICATION (2026-08-01, the site-entrance keying): the
priced event is the site's exact cell event under its OWN read map — `es` the
entrance, `ν` the site's own branch node, `c` the side split's own cell — "at a
site whose window hull has k ≥ 2 sides … the CLAIMED mass is the side product
jvol(c_s │ Σ) = ∏_sides vol_nom(E_fresh(ν_side))" (MOVES 7473–7483): c_s the
SITE's joint cell (the `SideSplit`'s c), its side systems the site's OWN
presented `fd`'s clauses. -/
def JCmultiAt (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (ν : Node p F) {c : CA.Cell}
    {fd : FreshData p m} (ss : SideSplit T CA c fd) : Prop :=
  Nat.card ↥(siteCellEvent T CA χ es ν c) * p ^ (∑ j : Fin ss.k, ss.sideExp j)
    = Nat.card ↥(entEvent T χ es)

/-- the per-site B(iii)/Scale level: level 1 at the root (7564), the shape-side band
level at a window site. -/
noncomputable def siteLevel (n : ℕ) : Option (History p F) → ℕ
  | none => 1
  | some H => (shapeOfH H n).NPband n

/-- REV 2/3/4/5: the SITE LEDGER — the typed carrier of the per-site jet/system data
(HC-2's presented faces): `hparent`'s `.st` leg is the IMMEDIATE parent (REV 4,
Codex-3 #16); `state_cell` is the STATE↔CELL tie FIELD (§0 row, owner HC-2, fenced
Q2); `hsplit_k` ties the exhibited decomposition to the hull-side count (REV 5). -/
structure SiteLedger (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m) where
  sys : History p F → Locus p m × FreshData p m
  /-- `cellAt H` is the site's OWN FULL JOINT CELL c_s (MOVES 7443–7448) — a VALUE
  of the site's own read map `branchCellOf (parentSt H) H.lastNode` (THE
  SITE-ENTRANCE KEYING, 2026-08-01), the note's complete realized stratum datum of
  the site's read. It keys the site's exact cell event (`presents`/`state_cell`
  below), its side split (`splitAt`), the JC charges, AND the scaffold's split
  frames (`TreeScaffold.hframe_cell` — the note's single per-site cell datum, the
  2026-07-29 [date corrected 2026-07-30; original record mis-dated 2026-07-31]
  c/cSplit two-keying REMOVED per the re-ratification verdict: "an
  arbitrary split-cell roster can be attached to an unrelated exact conditioning
  cell … statement mismatch / under-connected scaffold; M"). -/
  cellAt : History p F → CA.Cell
  parentSt : History p F → EntSt p F n
  hparent : ∀ H ∈ Tr.chains, match parentSt H with
    | .amb => False
    | .red _ _ => H.nodes.length = 1
    | .st H' => H'.IsPrefixOf H ∧ H'.nodes.length + 1 = H.nodes.length ∧ H' ∈ Tr.chains
  /-- the presented face equates the site's exact cell event Ψ_s^{−1}(c_s) ∩ Σ with
  the transported system's stratum — Ψ_s the site's own read map (site-entrance
  keyed by `H.lastNode`, 2026-08-01). -/
  presents : ∀ H ∈ Tr.chains,
    SitePresents T CA χ (parentSt H) H.lastNode (cellAt H) (sys H).1 (sys H).2
  sides : History p F → ℕ
  hsides : ∀ H ∈ Tr.chains, 1 ≤ sides H
  /-- **the STATE↔CELL tie — the EXACT Σ_c law, SITE-ENTRANCE KEYED** (2026-08-01,
  the re-ratification repair). THE SCAFFOLD LAW, asserted where the note asserts
  it: "each conditional on the state left by the recursion above it" (MOVES
  7454–7456) with jvol(c_s │ Σ) = μ(Ψ_s^{−1}(c_s) │ Σ) (7448–7449) — the state a
  site's read leaves IS the exact fiber of its own joint cell c_s under its OWN
  read map Ψ_s = `branchCellOf (parentSt H) H.lastNode`. Owner of instances: HC-2
  (presented-face genre). THE FORMER OBSTRUCTION IS DEAD: under the 2026-07-29
  [date corrected 2026-07-30; original record mis-dated 2026-07-31]
  keying (Ψ shared across siblings) co-realized sibling sites with distinct pins
  were FORCED to equal state events (`shared_split_state_forced`, bracketed at
  T-E8) — the re-ratification verdict's central finding. Sibling sites now key
  DIFFERENT read maps (ν₁ ≠ ν₂), so distinct cells at a shared fiber witness are
  representable; the F1 two-leaf configuration discharges — the displayed check is
  `f1_two_leaf_discharge` (T-E8). The pinned G1 toys discharge the law with the
  degenerate diagonal read (`branchCellOf es ν := cellOf es`; their sibling leaf
  states coincide by table). The former `sides H = 1` guard remains dropped. -/
  state_cell : ∀ H ∈ Tr.chains,
    stateEvent T (some H)
      = siteCellEvent T CA χ (parentSt H) H.lastNode (cellAt H)
  splitAt : ∀ H ∈ Tr.chains, 2 ≤ sides H → SideSplit T CA (cellAt H) (sys H).2
  hsplit_k : ∀ H (hH : H ∈ Tr.chains) (h2 : 2 ≤ sides H),
    (splitAt H hH h2).k = sides H
  /-- **the SIDE-UNION exponent tie** — NEW at the T RATIFICATION (2026-07-29
  [date corrected 2026-07-30; original record mis-dated 2026-07-31];
  verdict §4's consumption demand): "the joint cell's literal system is the union
  of the k per-side systems over DISJOINT slot spans" (MOVES 7476–7479) — the side
  decomposition's total equation count IS the site's own fresh charge, so the
  (JC-multi) row prices exactly the site's `siteExp`. Owner HC-2 (presented-face
  genre, with `presents`/`hcard`). -/
  hsplit_exp : ∀ H (hH : H ∈ Tr.chains) (h2 : 2 ≤ sides H),
    (∑ j : Fin (splitAt H hH h2).k, (splitAt H hH h2).sideExp j)
      = (sys H).2.mstar
  free : ∀ H ∈ Tr.chains, ∀ cl ∈ (sys H).2.clauses, ∀ cIdx ∈ cl.support,
    (sys H).1.pinned cIdx = false
  freshCoords : History p F → Finset (Fin m)
  hfresh : ∀ H ∈ Tr.chains, ∀ cl ∈ (sys H).2.clauses, ∀ cIdx ∈ cl.support,
    cIdx ∈ freshCoords H
  /-- **the SPECTATOR law for the Σ-solve coordinates** — ADJUDICATED ADDITION
  (2026-07-30, the assembly-spine statement-repair round: the E6 countermodel built a
  presented `Locus` whose PINNED coordinate was `solve`d VALUE-DEPENDENTLY off a fresh
  coordinate, so the state locus failed to be a spectator of the site's own fresh
  coordinates and the relativized (JC-single) count broke). The presented system's
  solution set `{Σsol}` is `SpectatorFor (freshCoords H)`: membership depends only on
  the coordinates OUTSIDE the site's fresh roster — the C.1.5 level-separation of the
  entrance state from the site's fresh digits (the `free` law's set-level companion:
  `free` frees the CLAUSE supports of Σ's pins; this frees Σ's SOLVED VALUES of the
  fresh coordinates). Owner HC-2 (presented-face content, same genre as `presents`). -/
  spectator_sol : ∀ H ∈ Tr.chains,
    SpectatorFor (freshCoords H) {x : Box p m | (sys H).1.IsSolution x}
  hcard : ∀ H ∈ Tr.chains, (freshCoords H).card = (sys H).2.mstar

/-- the per-site fresh exponent, off the ledger. -/
def SiteLedger.siteExp {Tr : VTree p F} {T : TreeModel p F n N m pol}
    {CA : CellData p F n N m pol T} {χ : Fin n → Fin m}
    (L : SiteLedger Tr T CA χ) (H : History p F) : ℕ := (L.sys H).2.mstar

/-- A(T) as an exponent (7540: "A(T̂) := n + Σ_{window sites} A(s)"). -/
noncomputable def AofTr (Tr : VTree p F) {T : TreeModel p F n N m pol}
    {CA : CellData p F n N m pol T} {χ : Fin n → Fin m}
    (L : SiteLedger Tr T CA χ) : ℕ :=
  n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H

/-- thr(T) (7562–7566): the join over T's chains of the §D4-R L12/D4R.4 thresholds
with the joint-cell levels, and 1 (the root's level). -/
noncomputable def VTree.thr (Tr : VTree p F) (n : ℕ) : ℕ :=
  Tr.hfin.toFinset.sup
    (fun H => (shapeOfH H n).Nshape ⊔ siteLevel n (some H)) ⊔ 1

/-! ### §2.11 jet-chart accessors (HOISTED with (4)) — over the BUILT `JetSetup`
(`coordOf`/`Sigma`/`fresh`) and the built `htH`/`floorH` chart -/

/-- the last read's rim threshold μ·D (the window-interior bound, (ZC)'s
"base index < μ·D"). -/
noncomputable def lastRim (H : History p F) : ℕ :=
  (H.nodes.getLast?).elim 0 (fun ν => ν.μ * ν.Dwidth)

def baseOf {H : History p F} (J : JetSetup H n N m) (j : Fin m) : ℕ :=
  (J.coordOf j).2

noncomputable def heightOf {H : History p F} (J : JetSetup H n N m)
    (j : Fin m) : ℚ := H.htH H.nodes.length (J.coordOf j)

noncomputable def floorAt {H : History p F} (J : JetSetup H n N m)
    (j : Fin m) : ℚ := WithBot.unbotD 0 (H.floorH H.nodes.length (baseOf J j))

noncomputable def interiorBase {H : History p F} (J : JetSetup H n N m)
    (j : Fin m) : Bool := decide (baseOf J j < lastRim H)

noncomputable def interiorIdx {H : History p F} (J : JetSetup H n N m) :
    Finset (Fin m) := Finset.univ.filter (fun j => interiorBase J j = true)

def pinnedOnState {H : History p F} (J : JetSetup H n N m) (j : Fin m) :
    Prop := (J.Sigma H.nodes.length).pinned j = true

/-- a DIG lead index: the chart-order lead of some clause of J's fresh system. §2.11
[E-phase caveat carried: bind to a designated lead accessor if MovesC exposes one]. -/
def digLead {H : History p F} (J : JetSetup H n N m) (j : Fin m) : Prop :=
  ∃ i ≤ H.nodes.length, ∃ cl ∈ (J.fresh i).clauses,
    j ∈ cl.support ∧ ∀ j' ∈ cl.support, j' ≤ j

/-- the CAP-M INTERIOR FRESH ROSTER: interior-base chart coordinates whose height sits
strictly above the floor and at most M (`NsLumpFamily`'s carrier). -/
noncomputable def interiorFreshIdx {H : History p F} (J : JetSetup H n N m)
    (M : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => interiorBase J j = true ∧
    floorAt J j < heightOf J j ∧ heightOf J j ≤ (M : ℚ))

def digitAt (x : Box p m) (j : Fin m) : ZMod p := x j

/-- the level's Scale value READ OFF J's OWN CHART (jet-side; `ScaleFaithful` ties it
to the H-side `hScale`). -/
noncomputable def scaleTop {H : History p F} (J : JetSetup H n N m)
    (N' : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin m =>
      (J.coordOf j).1 < N' ∧ interiorBase J j = true)).sup
    (fun j => ⌈heightOf J j⌉₊)

open Classical in
/-- the ENTRANCE RESOLUTION read off J's own state locus: the largest Σ-pinned slot-0
height (jet-side; `ScaleFaithful` ties it to `hRes`). -/
noncomputable def M₀ {H : History p F} (J : JetSetup H n N m) : ℕ :=
  (Finset.univ.filter (fun j : Fin m =>
      pinnedOnState J j ∧ baseOf J j = 0)).sup (fun j => ⌈heightOf J j⌉₊)

/-- Z's pins count. -/
noncomputable def pinCount (Z : Locus p m) : ℕ :=
  (Finset.univ.filter (fun c : Fin m => Z.pinned c = true)).card

/-- Z is EXACTLY the cap-M lump system (T-C5's carriers) — BOTH conjuncts (REV 9,
Codex-8 crit 5): the pin ROSTER and the (ZC-a) LITERAL-ZERO values. -/
def IsLumpLocus {H : History p F} (J : JetSetup H n N m) (M : ℕ)
    (Z : Locus p m) : Prop :=
  (∀ c : Fin m, Z.pinned c = true ↔ c ∈ interiorFreshIdx J M) ∧
  (∀ c : Fin m, c ∈ interiorFreshIdx J M →
    ∀ f : (j : Fin m) → j < c → ZMod p, Z.solve c f = 0)

/-- tower truncation: below the shallower level the two jets' charts and state pins
agree (under the coordinate match). -/
def SystemTruncatesTo {H : History p F} {N₁ N₂ m₁ m₂ : ℕ}
    (J₂ : JetSetup H n N₂ m₂) (J₁ : JetSetup H n N₁ m₁) : Prop :=
  (∀ j₁ : Fin m₁, ∃ j₂ : Fin m₂, J₂.coordOf j₂ = J₁.coordOf j₁ ∧
    ((J₂.Sigma H.nodes.length).pinned j₂
      = (J₁.Sigma H.nodes.length).pinned j₁)) ∧
  (∀ j₂ : Fin m₂, (J₂.coordOf j₂).1 < N₁ → ∃ j₁ : Fin m₁,
    J₁.coordOf j₁ = J₂.coordOf j₂)

/-- the (level, base) support of J's pinned equations at Z (T-D7's own Finset). REV 9
(Codex-8 crit 4): `FreshData.clauses` is a LIST — the List-safe fold of the mapped
supports. [STATEMENT REPAIR 2026-07-29, adjudicated (round-3 item 1, TWO independent
finders): the read range is `Finset.range H.nodes.length` — every `JetSetup` fresh law
(`fresh_band`/`fresh_cover`/`mstar_eq`/`fresh_assembled`, MovesC/Defs) guards
`i < H.nodes.length`, so `fresh H.nodes.length` is unconstrained junk data; the former
`range (H.nodes.length + 1)` swept it into the support. Cone rebuilt: T-D7 `np_id`,
T-C2 `le_sup_of_transported`.] -/
noncomputable def transportedLevels {H : History p F}
    (J : JetSetup H n N m) (Z : Locus p m) : Finset (ℕ × ℕ) :=
  ((((Finset.range H.nodes.length).biUnion (fun r =>
      ((J.fresh r).clauses.map (fun cl => cl.support)).foldr (· ∪ ·) ∅)).filter
    (fun j => Z.pinned j = false)).image J.coordOf)

/-- "N(η′,⊤) = 1 + the largest base level among T(η′,⊤)'s finitely many equations"
(7178–7180 — T-C2's capIrrOf reads this). -/
noncomputable def jetTopLevel {H : History p F} (J : JetSetup H n N m) : ℕ :=
  1 + (transportedLevels J (topLocus p m)).sup Prod.fst

/-! ### §2.5a the (ns) lump family (the B(iii) carrier, non-circular) -/

/-- M(N) := the largest window height with base level < N — C.1.5's Scale map read off
J's chart (7205–7207). HOISTED from T-C7 at REV 4. -/
noncomputable def Mlev {H : History p F} (J : JetSetup H n N m) (N' : ℕ) : ℕ :=
  scaleTop J N'

/-- H's window-block (height, base level) roster — REV 7 (Codex-6 #4): CLOSED over the
BUILT MovesC history chart (`History.htH`). -/
noncomputable def windowBlockHts (H : History p F) (N' : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range N' ×ˢ
      Finset.range ((H.nodes.getLast?).elim 0 fun ν => ν.μ * ν.Dwidth)).image
    (fun c => (⌈H.htH H.nodes.length c⌉₊, c.1)))

/-- the level's own SCALE value, H-SIDE, CLOSED (REV 6/7): the sup of H's window-block
heights whose base level sits below the cap. -/
noncomputable def hScale (H : History p F) (N' : ℕ) : ℕ :=
  ((windowBlockHts H N').filter (fun bh => bh.2 < N')).sup (fun bh => bh.1)

/-- the ENTRANCE RESOLUTION, H-SIDE, CLOSED (REV 6/7): the slot-0 floor value at H's
full prefix, on the built `History.floorH`. EXACTNESS SCOPE (REV 8): the `unbot'` is
claimed exact on LAWFUL histories only; the accessor stays closed and total. -/
noncomputable def hRes (H : History p F) : ℕ :=
  ⌈WithBot.unbotD 0 (H.floorH H.nodes.length 0)⌉₊

/-- SCALE FAITHFULNESS of a jet — NEW at REV 5 (Codex-4 #1): the cap accessors read
off J's chart must equal the LEVEL'S OWN (H, N)-determined values. -/
def ScaleFaithful {H : History p F} (J : JetSetup H n N m) (N' : ℕ) : Prop :=
  Mlev J N' = hScale H N' ∧ M₀ J = hRes H

/-- the capped lumps L_M of a no-side track, AS DATA WITH THEIR DEFINING SHAPE
(7203–7209, 7216–7224). `tie` is B(iii)'s reading — the standing-perimeter hypothesis
(owner D4R0K), carried as a FIELD, never re-proved; `slot0` is the REV-4 CAPPED
ladder. -/
structure NsLumpFamily (T : TreeModel p F n N m pol) {H : History p F}
    (J : JetSetup H n N m) where
  L : ℕ → Set (Box p m)
  vanish : ∀ (M : ℕ) (x : Box p m),
    x ∈ L M ↔ ∀ bl ∈ interiorFreshIdx J M, digitAt x bl = 0
  interior_mono : ∀ M M', M ≤ M' → interiorFreshIdx J M ⊆ interiorFreshIdx J M'
  tie : ∀ x : Box p m, T.mem (some H) x →
    ((∀ ν : Node p F, ¬ T.child (some H) ν x) ↔ ∀ M, x ∈ L M)
  slot0 : ∀ M, M₀ J ≤ M → M ≤ Mlev J N → M - M₀ J ≤ (interiorFreshIdx J M).card

/-- the (ZC) hypothesis package of a jet — REV 3 (Codex-2 #6), clauses = the display
7216–7224; the accessor names are the §2.11 closed accessors (the structure's clause
roster is normative). -/
structure ZCPack {H : History p F} (J : JetSetup H n N m) : Prop where
  inclusive_top : ∀ bl, bl ∈ interiorIdx J →
    (pinnedOnState J bl ↔ heightOf J bl ≤ floorAt J bl)
  rim_sep : ∀ bl, digLead J bl → interiorBase J bl = false
  slot0_grid : ∀ ht, M₀ J ≤ ht → ht ≤ Mlev J N →
    ∃ bl, bl ∈ interiorIdx J ∧ heightOf J bl = ht ∧ baseOf J bl = 0

/-! ### T-C7's tower carriers (HOISTED at (5)) + §2.4's KB-TOT bundle -/

/-- the jet family is a LEVEL TOWER (REV 3, Codex-2 #7(b)). -/
def JetTower {H : History p F} {N₀ : ℕ}
    (Jat : ∀ N', N₀ ≤ N' → JetSetup H n N' (n * N')) : Prop :=
  ∀ (N' N'' : ℕ) (h' : N₀ ≤ N') (h'' : N₀ ≤ N''), N' ≤ N'' →
    SystemTruncatesTo (Jat N'' h'') (Jat N' h')

open Classical in
/-- the truncated state count at level N'. [E-DEV: junk-total `dite` on `N₀ ≤ N'` —
the blueprint's `Jat N' _` needs the tower bound; every consumer quantifies `∀ N' h`,
so the junk branch (∅) is never read on the lawful domain.] -/
noncomputable def stateTruncAt {H : History p F} {N₀ : ℕ}
    (Jat : ∀ N', N₀ ≤ N' → JetSetup H n N' (n * N')) (N' : ℕ) :
    Set (Box p (n * N')) :=
  if h : N₀ ≤ N' then (Jat N' h).SHZ (topLocus p (n * N')) else ∅

open Classical in
/-- state ∩ lump L_{M(N)} at level N'. [E-DEV: same junk-total `dite`.] -/
noncomputable def nsTruncAt {H : History p F} {N₀ : ℕ}
    {Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol}
    (Jat : ∀ N', N₀ ≤ N' → JetSetup H n N' (n * N'))
    (Lat : ∀ N' h, NsLumpFamily (Tat N' h) (Jat N' h)) (N' : ℕ) :
    Set (Box p (n * N')) :=
  if h : N₀ ≤ N' then
    stateTruncAt Jat N' ∩ (Lat N' h).L (Mlev (Jat N' h) N')
  else ∅

/-- **KB-TOT, the full hypothesis bundle** — Theorem B's structural totality
(D4R.0-K(a)+(b)); leg (a) = `BranchDichotomy`, leg (b) = `ns_lumps` with the REV-4
capped ladder + the REV-5 `ScaleFaithful` pin. Owner HC-2/D4R0K; NEVER proved here. -/
structure KBTot (T : TreeModel p F n N m pol) : Prop where
  dichotomy : BranchDichotomy T
  ns_lumps : ∀ (H : History p F), (∃ x, T.mem (some H) x) →
    ∃ J : JetSetup H n N m, ScaleFaithful J N ∧ M₀ J ≤ Mlev J N ∧
      Nonempty (NsLumpFamily T J)

/-- **KB-TOT ALONG THE PINNED LEVEL FAMILY** — REV 5/6/7: per-level faces + the
PER-TRACK level-0 covering `root_total` (ruling 2) + the Scale-gap growth. This is
what `VPPinned.covering` consumes. Owner HC-2/D4R0K; NEVER proved here.
[QUEUE ITEM 1 EXECUTED 2026-07-31 (Asvin sign-off; the ratified chi-at guard
repair, commit 89b2f7f's adjudication "+ same-pattern sweep of
KBTotTower/TreeExpNs"): the chart carrier `χat` is GUARDED (`∀ N' (h' : N₀ ≤ N'),
…`) — the unguarded carrier `∀ N', Fin n → Fin (n * N')` is UNINHABITED at n ≥ 1
via N' = 0 (compiled witness `tv_b1_chart_carrier_uninhabited`, TV_B1.lean), so
the unguarded structure was uninstantiable at n ≥ 1. Same guard shape as
`ReadLocality` (header resolution 1).] -/
structure KBTotTower (pol : CanonPolicy p F) {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N' (h' : N₀ ≤ N'), Fin n → Fin (n * N'))
    (trackOf : Node p F → Polynomial (ZMod p)) : Prop where
  perLevel : ∀ N' h, KBTot (Tat N' h)
  root_total : ∀ N' (h : N₀ ≤ N') (x : Box p (n * N')),
    ∀ ψ : Polynomial (ZMod p),
      ψ ∈ UniqueFactorizationMonoid.normalizedFactors (redPoly (χat N' h) x) →
      2 ≤ Multiset.count ψ
        (UniqueFactorizationMonoid.normalizedFactors (redPoly (χat N' h) x)) →
    ∃ ν : Node p F, trackOf ν = ψ ∧ (Tat N' h).child none ν x
  scale_grow : ∀ (H : History p F),
    (∀ N' h, ∃ x, (Tat N' h).mem (some H) x) →
    ∃ Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'),
      JetTower Jat ∧ (∀ N' h, ScaleFaithful (Jat N' h) N') ∧
      Filter.Tendsto
        (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
        Filter.atTop Filter.atTop

/-! ### §2.6 (SIB) — the joint sibling kernel, COUNT FACE (hypothesis, NEVER proved
here). The conditioning event is THE CELL EVENT (7290–7292). -/

/-- the event that branch (o, ν)'s continuation realizes the PRESCRIBED finite
subtree — (SIB)'s S_j quantifier (7287–7290): the rooted analogue of `fiberAt`'s
clauses (i)/(ii)/(iv), root = o·ν; no hen clause; prefix duties scoped STRICTLY ABOVE
the child root. -/
def ContFiber (T : TreeModel p F n N m pol) (o : Option (History p F))
    (ν : Node p F) (hν : ChildRoot o ν) (Tsub : Set (History p F))
    (leafSpec : History p F → Option Vd) (nsSpec : History p F → Prop)
    (x : Box p m) : Prop :=
  (∀ H' : History p F, H' ∈ Tsub ↔
      ((childHist o ν hν).IsPrefixOf H' ∧ T.mem (some H') x ∧
        ∀ H'' : History p F, (childHist o ν hν).IsPrefixOf H'' →
          H''.IsPrefixOf H' → H'' ≠ H' → ¬ IrrHalts H'' ∧ ¬ NsHalts T (some H'') x)) ∧
  (∀ H' ∈ Tsub, IsMaximalIn Tsub H' →
    ((IrrHalts H' ∧ ¬ nsSpec H' ∧ leafSpec H' = some (irrVerdictOf H')) ∨
     (NsHalts T (some H') x ∧ ¬ IrrHalts H' ∧ nsSpec H' ∧
       leafSpec H' = some (nsVerdictOf H')))) ∧
  (∀ H' ∈ Tsub, ¬ IsMaximalIn Tsub H' → ¬ IrrHalts H' ∧ ¬ NsHalts T (some H') x)

/-- `SubFiber` — REV 3 (Codex-2 #23): ContFiber's three clauses over a DESIGNATED
chain subset headed at a root child — T-E5's per-track event body. -/
def SubFiber (T : TreeModel p F n N m pol) (chainSet : Set (History p F))
    (ν₀ : Node p F) (hν : ChildRoot none ν₀)
    (leafSpec : History p F → Option Vd) (nsSpec : History p F → Prop)
    (x : Box p m) : Prop :=
  (∀ H' : History p F, H' ∈ chainSet ↔
      ((childHist none ν₀ hν).IsPrefixOf H' ∧ T.mem (some H') x ∧
        ∀ H'' : History p F, (childHist none ν₀ hν).IsPrefixOf H'' →
          H''.IsPrefixOf H' → H'' ≠ H' → ¬ IrrHalts H'' ∧ ¬ NsHalts T (some H'') x)) ∧
  (∀ H' ∈ chainSet, IsMaximalIn chainSet H' →
    ((IrrHalts H' ∧ ¬ nsSpec H' ∧ leafSpec H' = some (irrVerdictOf H')) ∨
     (NsHalts T (some H') x ∧ ¬ IrrHalts H' ∧ nsSpec H' ∧
       leafSpec H' = some (nsVerdictOf H')))) ∧
  (∀ H' ∈ chainSet, ¬ IsMaximalIn chainSet H' → ¬ IrrHalts H' ∧ ¬ NsHalts T (some H') x)

/-- **(SIB), COUNT FACE, tree-indexed — REV 2/3/6.** THE CENTRAL HYPOTHESIS of this
corpus: OPEN (CL-10), consumed by TREE-EXP at every branching cell, NEVER proved.
REV 6 (Codex-5 #3): the `Tsub.Finite` conjunct — the note's S_j subtrees are
PRESCRIBED FINITE. -/
def SibCount (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) : Prop :=
  ∀ (es : EntSt p F n) (c : CA.Cell) (S : Node p F → Set (Box p m)),
    2 ≤ (CA.branchSetOf c).card →
    (∀ ν ∈ CA.branchSetOf c,
      (∃ hν Tsub leafSpec nsSpec, Tsub.Finite ∧
        S ν = {x | ContFiber T (stOf es) ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
    Nat.card ↥(cellEventE T CA χ es c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * (Nat.card ↥(cellEventE T CA χ es c)) ^ ((CA.branchSetOf c).card - 1)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEventE T CA χ es c ∩ S ν)

/-- (SIB)'s COUNT face ACROSS SHALLOW SPLITS — the `Wsh17Package.sib_count` field's
value (§5 S-8): the same kernel restricted to the SHALLOW entrances (never .st). -/
def SibCountShallow (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m) : Prop :=
  ∀ (es : EntSt p F n), (∀ H, es ≠ .st H) →
    ∀ (c : CA.Cell) (S : Node p F → Set (Box p m)),
    2 ≤ (CA.branchSetOf c).card →
    (∀ ν ∈ CA.branchSetOf c,
      (∃ hν Tsub leafSpec nsSpec, Tsub.Finite ∧
        S ν = {x | ContFiber T none ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ) →
    Nat.card ↥(cellEventE T CA χ es c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
        * (Nat.card ↥(cellEventE T CA χ es c)) ^ ((CA.branchSetOf c).card - 1)
      = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(cellEventE T CA χ es c ∩ S ν)

/-- **(SIB) AT A REALIZED SITE, the count face — ONE CELL** — RE-KEYED at the T
RE-RATIFICATION (2026-08-01; verdict, material finding: "The note uses one cell
`c` both for `Σ_c` and for its branch set. Lean now defines `SibCountAt … (c
cSplit : CA.Cell)` … There is deliberately no equality between them … an
arbitrary split-cell roster can be attached to an unrelated exact conditioning
cell — statement mismatch / under-connected scaffold; M"). The 2026-07-29
[date corrected 2026-07-30; original record mis-dated 2026-07-31]
c/cSplit two-keying is REMOVED: the note's (SIB) has ONE cell — "Let η be a
realized prefix with state cylinder Σ, c a digit cell of Σ with branch set
{b₁, …, b_m} … conditionally on the cell event Σ_c" (MOVES 7283–7292) — so the
conditioning event AND the product roster both key the SAME cell `c`, the site's
own joint cell (`SiteLedger.cellAt`, tied to the scaffold frame by
`TreeScaffold.hframe_cell`). The conditioning event is the site's exact cell
event under its own read map (`ν` the site's branch node — the site-entrance
keying); the ledger's `state_cell` law ties it to the state event the recursion
decomposes. OPEN obligation (the (SIB) kernel, CL-10 genre); NEVER proved here —
consumed as TREE-EXP's `hsibT` row at THIS tree's branching sites; the root
instances (T-E5's `.amb` application) stay on `SibCount`. F1-censused at the head
site (CASE_SIB P3, MOVES 7516–7528: 78,125² = 15,625 · 390,625 over the 14-pin
Σ_c). -/
def SibCountAt (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) (es : EntSt p F n) (ν₀ : Node p F) (c : CA.Cell)
    (S : Node p F → Set (Box p m)) : Prop :=
  Nat.card ↥(siteCellEvent T CA χ es ν₀ c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν)
      * (Nat.card ↥(siteCellEvent T CA χ es ν₀ c)) ^ ((CA.branchSetOf c).card - 1)
    = ∏ ν ∈ CA.branchSetOf c, Nat.card ↥(siteCellEvent T CA χ es ν₀ c ∩ S ν)

/-- (SIB-STEP)'s stage carrier (7382–7388) — def ONLY, consumed by NOTHING in wave 4. -/
structure JointStage (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (o : Option (History p F)) (c : CA.Cell) where
  active : Finset (Node p F)
  hactive : active ⊆ CA.branchSetOf c
  past : Set (Box p m)
  hpast : past ⊆ cellEvent T CA o c
  nextW : Node p F → Box p m → ℕ
  alpha : Node p F → ℕ
  halpha : ∀ ν ∈ active, 1 ≤ alpha ν

/-- `StageRealized` — REV 3 (Codex-2 #23/Fable-2 GAP-2): the TYPE pins the content;
the wave-5 filtration lemma owns the final refinement. Consumed by NOTHING in wave 4. -/
def StageRealized (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    {o : Option (History p F)} {c : CA.Cell} (st : JointStage T CA o c) : Prop :=
  (∃ rd : Node p F → Set (History p F),
    (∀ ν ∈ st.active, ∀ H' ∈ rd ν, ∃ hν : ChildRoot o ν,
      (childHist o ν hν).IsPrefixOf H') ∧
    st.past = cellEvent T CA o c ∩ ⋂ ν ∈ st.active, ⋂ H' ∈ rd ν,
      stateEvent T (some H')) ∧
  (∀ ν ∈ st.active, ∀ x ∈ st.past, st.nextW ν x < st.alpha ν)

/-- (SIB-STEP), stacked-vector form (7382–7388) — def ONLY; its ⟹(SIB) filtration
lemma is the note's own open remainder (§T.5(1)), a wave-5 obligation. -/
def SibStep (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T) : Prop :=
  ∀ (o : Option (History p F)) (c : CA.Cell) (st : JointStage T CA o c),
    StageRealized T CA st →
    ∀ a a' : Node p F → ℕ,
      (∀ ν ∈ st.active, a ν < st.alpha ν) → (∀ ν ∈ st.active, a' ν < st.alpha ν) →
      Nat.card ↥{x ∈ st.past | ∀ ν ∈ st.active, st.nextW ν x = a ν}
        = Nat.card ↥{x ∈ st.past | ∀ ν ∈ st.active, st.nextW ν x = a' ν}

/-- `SubtreeTransport` — REV 4 (Fable-3 GAP-1 = Codex-3 #20): the "SAME PRESCRIBED
SUBTREE read at the two entrances" — prefix-order isomorphic chain sets with IDENTICAL
read lists strictly above the shared child root ν. -/
def SubtreeTransport (TsubAt : EntSt p F n → Set (History p F))
    (es es' : EntSt p F n) (ν : Node p F) : Prop :=
  ∃ φ : {H // H ∈ TsubAt es} → {H // H ∈ TsubAt es'}, Function.Bijective φ ∧
    (∀ H H', H.1.IsPrefixOf H'.1 ↔ (φ H).1.IsPrefixOf (φ H').1) ∧
    (∀ H, stripAbove ν H.1 = stripAbove ν (φ H).1)

/-- PCI (parent-context independence — 7406–7413); stated, proved nowhere, consumed by
nothing in MovesT. REV 6 (Codex-5 #3): the transported subtrees are PRESCRIBED FINITE. -/
def PCI (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) : Prop :=
  ∀ (es es' : EntSt p F n) (c c' : CA.Cell) (ν : Node p F),
    ν ∈ CA.branchSetOf c → ν ∈ CA.branchSetOf c' →
    ∀ (hν : ChildRoot (stOf es) ν) (hν' : ChildRoot (stOf es') ν)
      (TsubAt : EntSt p F n → Set (History p F))
      (leafSpec : History p F → Option Vd) (nsSpec : History p F → Prop),
      (TsubAt es).Finite → (TsubAt es').Finite →
      SubtreeTransport TsubAt es es' ν →
      Nat.card ↥(cellEventE T CA χ es c ∩
          {x | ContFiber T (stOf es) ν hν (TsubAt es) leafSpec nsSpec x})
        * Nat.card ↥(cellEventE T CA χ es' c')
      = Nat.card ↥(cellEventE T CA χ es' c' ∩
          {x | ContFiber T (stOf es') ν hν' (TsubAt es') leafSpec nsSpec x})
        * Nat.card ↥(cellEventE T CA χ es c)

/-! ### §2.7 VP-SOUND's two declared citations (typed, hypothesis-only) -/

/-- the two extension invariants, CLOSED — REV 9 (Codex-8 crit 2): HONEST JUNK-TOTAL
DISPATCH — classically decide the local-ring Prop-class, junk 0 off it; the REAL value
is read only on the local domain (§9 IP-1 supplies `IsLocalRing (AdjoinRoot g)` for
monic irreducible g over ℤ_p). [E-DEV: `Ideal.ramificationIdx` is projection-style in
the pinned Mathlib — no `algebraMap` argument.] -/
noncomputable def ramIdx (g : Polynomial ℤ_[p]) : ℕ :=
  open Classical in
  if h : IsLocalRing (AdjoinRoot g) then
    letI := h
    Ideal.ramificationIdx
      (IsLocalRing.maximalIdeal ℤ_[p]) (IsLocalRing.maximalIdeal (AdjoinRoot g))
  else 0

/-- residue degree, same junk-total dispatch (§2.7). -/
noncomputable def resDeg (g : Polynomial ℤ_[p]) : ℕ :=
  open Classical in
  if h : IsLocalRing (AdjoinRoot g) then
    letI := h
    (IsLocalRing.maximalIdeal ℤ_[p]).inertiaDeg
      (IsLocalRing.maximalIdeal (AdjoinRoot g))
  else 0

/-- (E, F)-at-degree-d, DISPLAYED (REV 9, Codex-8 crit 1) — the unramified read-off
`HenLift` concludes: ramification index 1, residue degree d. -/
def UnramifiedOfDeg (g : Polynomial ℤ_[p]) (d : ℕ) : Prop :=
  ramIdx g = 1 ∧ resDeg g = d

/-- (HEN-LIFT) (7254–7261): coprime-factor Hensel over ℤ_p, full statement. Valid at
ALL primes incl. wild. NO mass unit consumes it. -/
def HenLift (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ f : Polynomial ℤ_[p], f.Monic →
    ∀ ψ hb : Polynomial (ZMod p), ψ.Monic → Irreducible ψ → IsCoprime ψ hb →
      f.map (PadicInt.toZMod) = ψ * hb →
      ∃! gh : Polynomial ℤ_[p] × Polynomial ℤ_[p],
        gh.1.Monic ∧ gh.2.Monic ∧ f = gh.1 * gh.2 ∧
        gh.1.map PadicInt.toZMod = ψ ∧ gh.2.map PadicInt.toZMod = hb ∧
        Irreducible gh.1 ∧ UnramifiedOfDeg gh.1 ψ.natDegree

/-- the TRACK-FACTOR relation, DISPLAYED — REV 5/6/7: fη is a monic factor of exactly
H's cluster degree of SOME `ReadsOf`-realized monic degree-n f, its reduction is its
OWN track's factor power, and the head's track value is monic ∧ irreducible ∧
degree-dividing ∧ a member of the REALIZED factor roster. -/
def ClusterFactorOf (n : ℕ) (trackOf : Node p F → Polynomial (ZMod p))
    (H : History p F) (fη : Polynomial ℤ_[p]) : Prop :=
  ∃ hne : H.nodes ≠ [],
    (trackOf (H.nodes.head hne)).Monic ∧
    Irreducible (trackOf (H.nodes.head hne)) ∧
    (trackOf (H.nodes.head hne)).natDegree ∣ fη.natDegree ∧
    1 ≤ fη.natDegree ∧
    fη.Monic ∧
    fη.natDegree = ((H.nodes.getLast?).elim 0 fun ν => ν.childWidth * ν.μ) ∧
    fη.map PadicInt.toZMod
      = trackOf (H.nodes.head hne)
          ^ (fη.natDegree / (trackOf (H.nodes.head hne)).natDegree) ∧
    ∃ f : Polynomial ℤ_[p], f.Monic ∧ f.natDegree = n ∧ fη ∣ f ∧
      LeanUrat.MovesJ.ReadsOf p F n f H ∧
      trackOf (H.nodes.head hne)
        ∈ (UniqueFactorizationMonoid.normalizedFactors
            (f.map PadicInt.toZMod)).toFinset

/-- (OM-SAT) (7262–7273): the Ore–Montes certificate — a saturated branch's cluster
factor is irreducible with e = E, f = F. CONSUMED as a cite (GMN/Montes). -/
def OmSat (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] (n : ℕ)
    (trackOf : Node p F → Polynomial (ZMod p)) : Prop :=
  ∀ (H : History p F) (fη : Polynomial ℤ_[p]),
    ClusterFactorOf n trackOf H fη → IrrHalts H →
    Irreducible fη ∧ ramIdx fη = accE H ∧ resDeg fη = accF H

/-- **(OM-SAT), the TOTALITY direction** — NEW at REV 8 (Codex-7 #2 = Fable-7 GAP-1):
every `ReadsOf`-realized saturated history HAS an fη carrying the full
`ClusterFactorOf` package dividing ITS OWN realizing f. Consumed as
`VPPinned.om_total`. -/
def OmSatTot (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] (n : ℕ)
    (trackOf : Node p F → Polynomial (ZMod p)) : Prop :=
  ∀ (H : History p F) (f : Polynomial ℤ_[p]),
    f.Monic → f.natDegree = n → LeanUrat.MovesJ.ReadsOf p F n f H →
    IrrHalts H →
    ∃ fη : Polynomial ℤ_[p], ClusterFactorOf n trackOf H fη ∧ fη ∣ f

/-! ### §2.8 pre-halt marks and the dictionary carriers (ONE-F) -/

/-- PRE-HALT (7595–7598) — REV 2 (Codex 17): BOX-FREE, "a property of η's OWN cell
data". Unit T-F0 proves the equivalence with the model-side pruning predicate. -/
def PreHalt (H : History p F) : Prop :=
  ∀ H' : History p F, H'.IsPrefixOf H → H' ≠ H → H'.nodes ≠ [] → ¬ IrrHalts H'

/-- the length-ℓ chains of a tree T of shape P̂ (the dictionary's per-tree count,
7601–7603). -/
noncomputable def VTree.chainCount (Tr : VTree p F) (n : ℕ) (P : Shape n) : ℕ :=
  Nat.card {H : History p F // H ∈ Tr.chains ∧ (P : ShapePrefix).MatchesHist H}

/-! ### §2.9 remainder (order (7)): the HC-2 bridge surfaces + the verdict model -/

/-- RUN-KEY, NAMED (REV 2): the HC-2 bridge surface — THE ∀-JET QUANTIFIER SITS
OUTSIDE THE IFF. -/
def RunKey (T : TreeModel p F n N m pol) (P : Shape n) : Prop :=
  ∀ (H : History p F), H ∈ PrefSet n pol P →
    ∀ (x : Box p m) (J : JetSetup H n N m),
      x ∈ J.SHZ (topLocus p m) ↔ T.mem (some H) x

/-- H lies in class i: its η-datum IS the class value (§2.11 class helper). -/
def SameClass {P : Shape n} {pol : CanonPolicy p F}
    (i : PrefIdx n pol P) (H : History p F) : Prop :=
  etaData (P : ShapePrefix) H = i.1

/-- the class-level prefix relation (§2.11). -/
def ClassPrefixOf {P' P : Shape n} {pol : CanonPolicy p F}
    (i' : PrefIdx n pol P') (i : PrefIdx n pol P) : Prop :=
  ∃ (H' H : History p F), H' ∈ PrefSet n pol P' ∧ H ∈ PrefSet n pol P ∧
    SameClass i' H' ∧ SameClass i H ∧ H'.IsPrefixOf H ∧ H' ≠ H

/-- prefix-closed address sets (§2.11). -/
def PrefixClosed {pol : CanonPolicy p F}
    (addrs : Finset (Σ P : Shape n, PrefIdx n pol P)) : Prop :=
  ∀ a ∈ addrs, ∀ a' : Σ P : Shape n, PrefIdx n pol P,
    ClassPrefixOf a'.2 a.2 → a' ∈ addrs

/-- maximal addresses (§2.11). -/
def MaximalAddr {pol : CanonPolicy p F}
    (addrs : Finset (Σ P : Shape n, PrefIdx n pol P))
    (a : Σ P : Shape n, PrefIdx n pol P) : Prop :=
  ∀ a' ∈ addrs, ClassPrefixOf a.2 a'.2 → False

/-- ETA-LOC, NAMED: tree membership is η-CLASS data. Owner HC-2. -/
def EtaLoc (T : TreeModel p F n N m pol) (P : Shape n) : Prop :=
  ∀ (i : PrefIdx n pol P) (H : History p F), H ∈ PrefSet n pol P → SameClass i H →
    ∀ x : Box p m, T.mem (some H) x ↔ T.mem (some (reprOf i)) x

/-- CHAIN-LOC's box face (REV 2, Fable GAP-5): realized chains are in-box. Owner HC-2. -/
def InBoxOfMem (T : TreeModel p F n N m pol) (n : ℕ) : Prop :=
  ∀ (H : History p F) (x : Box p m), T.mem (some H) x → InBox n H

/-- Wall A reconciliation, pinned at the REAL predicate (REV 3, Codex-2 #19): the
BUILT `ReadsOf` (HC2/Defs.lean 283 — [E-DEV: the built name is
`LeanUrat.MovesJ.ReadsOf`; the file `HC2/Defs.lean` declares namespace
`LeanUrat.MovesJ`]) consumed BY NAME, with HC-2's chart section `dec` the ONE
remaining parameter. FENCE NOTE: spec-only — NO mass unit premises this Prop. -/
def WallAReconciled (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T)
    (dec : Box p m → Polynomial ℤ_[p]) : Prop :=
  ∀ (H : History p F) (ν : Node p F) (hν : NodeExtends H ν) (x : Box p m),
    T.mem (some H) x →
    (ν ∈ CA.branchSetOf (CA.cellOf (embE (some H)) x) ↔
      LeanUrat.MovesJ.ReadsOf p F n (dec x) (H.snoc ν hν))

/-- the digit level of a box coordinate under the standard layout (m = n·N):
coordinate c sits at level ⌊c/n⌋ + 1. [E-DEV: `n` is not inferable from the argument —
use sites pass it by name, `levelIdx (n := n) c`.] -/
def levelIdx {n : ℕ} (c : Fin m) : ℕ := (c : ℕ) / n + 1

/-- **the cross-level per-class cap LAW** — REV 3/4: one cap per class across ALL
presented N AND all presented box sizes (Codex-3 #5's growing-box strengthening). -/
def CapIrrLaw (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n : ℕ) (pol : CanonPolicy p F)
    (cap : ∀ {P : Shape n}, PrefIdx n pol P → ℕ) : Prop :=
  ∀ {P : Shape n} (i : PrefIdx n pol P), IrrHalts (reprOf i) →
    ∀ (N' m' : ℕ) (S : Presented p F n N' m' pol P) (x x' : Box p m'),
      (∀ c : Fin m', levelIdx (n := n) c < cap i → x c = x' c) →
      (x ∈ S.fiber i ↔ x' ∈ S.fiber i)

/-- `VerdictModelT` — W4-2's re-derivation, ALL fields (REV 2, Codex 20/21), declared
IN THIS CORPUS from VP-1/VP-2 + TB-CAP. NO ns cap field (§0 refutation record). -/
structure VerdictModelT (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m) where
  vdict : Option (History p F) → Box p m → Option Vd
  halt_iff : ∀ (H : History p F) (x : Box p m), T.mem (some H) x →
    ((vdict (some H) x).isSome ↔ (IrrHalts H ∨ NsHalts T (some H) x))
  vdict_irr : ∀ H x, T.mem (some H) x → IrrHalts H →
    vdict (some H) x = some (irrVerdictOf H)
  vdict_ns : ∀ H x, T.mem (some H) x → ¬ IrrHalts H → NsHalts T (some H) x →
    vdict (some H) x = some (nsVerdictOf H)
  vdict_cell : ∀ o x x', T.mem o x → T.mem o x' →
    CA.cellOf (embE o) x = CA.cellOf (embE o) x' → vdict o x = vdict o x'
  rootVdict : Box p m → Multiset Vd
  rootVdict_law : ∀ x, rootVdict x = henPayload χ x
  rootVdict_cell : ∀ x x', (∀ b, x (χ b) = x' (χ b)) → rootVdict x = rootVdict x'
  capHen : ℕ
  capHen_law : capHen = 1 ∧
    ∀ x x' : Box p m, (∀ b : Fin n, x (χ b) = x' (χ b)) → rootVdict x = rootVdict x'
  capIrr : ∀ {P : Shape n}, PrefIdx n pol P → ℕ
  capIrr_law : CapIrrLaw p F n pol capIrr

/-- the WITHDRAWN uniform cap-envelope locality — DISPLAYED at REV 4.
[STATEMENT REPAIR 2026-07-29: the planned T-D4 falsifier is REFUTED — this Prop
HOLDS for every `T`, `CA` at finite `m` (cap := `sup(levelOf) + 1` trivializes
the premise); T-D4 now proves `capEnvelope_cellLocal_holds`. Withdrawn because
CONTENT-FREE, not because refutable.] -/
def CapEnvelopeCellLocal (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) : Prop :=
  ∃ cap : ℕ, ∀ (es : EntSt p F n) (x x' : Box p m),
    (∀ c : Fin m, CA.levelOf c < cap → x c = x' c) → CA.cellOf es x = CA.cellOf es x'

/-- the cap DATA package T-D3 consumes — REV 3 (Codex-2 #17). -/
structure CapData (T : TreeModel p F n N m pol) (CA : CellData p F n N m pol T)
    (χ : Fin n → Fin m) where
  capIrrOf : ∀ {P : Shape n}, PrefIdx n pol P → ℕ
  cap_law : CapIrrLaw p F n pol capIrrOf

/-! ### structural carriers HOISTED per the declaration order (8) -/

/-- T-V5's carrier (REV 2, Codex 7 / Fable CRIT-5). -/
def IrrHaltsAsChild (T : TreeModel p F n N m pol) (o : Option (History p F))
    (ν : Node p F) (x : Box p m) : Prop :=
  T.mem o x ∧ T.child o ν x ∧ ν.μ = 1

/-- the (τ-ns) class of a state (T-C3). -/
def nsClass (T : TreeModel p F n N m pol) (H : History p F) : Set (Box p m) :=
  {x | NsHalts T (some H) x}

/-- T-C2's cap: the jet cutoff N(η′,⊤) (7178–7180). -/
noncomputable def capIrrOf {H : History p F}
    (J : JetSetup H n N m) : ℕ := jetTopLevel J

open Classical in
/-- T-D7's shape-side band-level grid — REV 7 (Codex-6 g2): CLOSED over the BUILT
MovesD band vocabulary (`bandS`/`NPband`). -/
noncomputable def bandLevels (R : ShapePrefix) (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range ((R.NPband n)) ×ˢ Finset.range n).filter
    (fun c => ∃ r < R.reads.length, R.bandS n r c)

/-- T-E5's root decomposition datum (REV 3/4): the constructive head roster. -/
structure RootSplitData (Tr : VTree p F) (g : Fin n → ZMod p) where
  t : ℕ
  trackChains : Fin t → Set (History p F)
  hpart : (⋃ i, trackChains i) = Tr.chains ∧
    Pairwise (Function.onFun Disjoint trackChains)
  headOf : Fin t → Node p F
  hhead : ∀ i, ∀ H ∈ trackChains i, H.nodes.head? = some (headOf i)
  hinj : Function.Injective headOf
  hne : ∀ i, (trackChains i).Nonempty
  hcov : ∀ i, ∃ h : ChildRoot none (headOf i),
    oneNode (headOf i) h ∈ Tr.chains

/-- the per-track event of T-E5. -/
def trackEvent (Tr : VTree p F) (T : TreeModel p F n N m pol) {g : Fin n → ZMod p}
    (htracks : RootSplitData Tr g) (i : Fin htracks.t)
    (hcr : ChildRoot none (htracks.headOf i)) : Set (Box p m) :=
  {x | SubFiber T (htracks.trackChains i) (htracks.headOf i) hcr Tr.leafV Tr.nsLeaf x}

/-- ENTRANCE SCOPE, DISPLAYED — REV 6 (Codex-5 gap #9): H' sits strictly below the
entrance; the `.red` case is per-TRACK through the shared accessor. -/
def belowEnt (trackOf : Node p F → Polynomial (ZMod p)) :
    EntSt p F n → History p F → Prop
  | .st H₀ => fun H' => H₀.IsPrefixOf H' ∧ H₀ ≠ H'
  | .red _ ψ => fun H' => ∃ hne : H'.nodes ≠ [], trackOf (H'.nodes.head hne) = ψ
  | .amb => fun H' => H'.nodes ≠ []

/-- the SUBTREE FIBER at an entrance — NEW at REV 5 (Codex-4 #3): the recursion
frame's own priced event over a DESIGNATED chain subset. -/
def SubtreeFiber (T : TreeModel p F n N m pol)
    (trackOf : Node p F → Polynomial (ZMod p))
    (es : EntSt p F n) (C : Set (History p F))
    (leafSpec : History p F → Option Vd) (nsSpec : History p F → Prop)
    (x : Box p m) : Prop :=
  (∀ H' : History p F, H' ∈ C ↔
      (belowEnt trackOf es H' ∧ T.mem (some H') x ∧
        ∀ H'' : History p F, belowEnt trackOf es H'' → H''.IsPrefixOf H' →
          H'' ≠ H' → ¬ IrrHalts H'' ∧ ¬ NsHalts T (some H'') x)) ∧
  (∀ H' ∈ C, IsMaximalIn C H' →
    ((IrrHalts H' ∧ ¬ nsSpec H' ∧ leafSpec H' = some (irrVerdictOf H')) ∨
     (NsHalts T (some H') x ∧ ¬ IrrHalts H' ∧ nsSpec H' ∧
       leafSpec H' = some (nsVerdictOf H')))) ∧
  (∀ H' ∈ C, ¬ IsMaximalIn C H' → ¬ IrrHalts H' ∧ ¬ NsHalts T (some H') x)

/-- T-E7's split-site frame (REV 3/5/6): the frame prices its OWN `scope`.
RE-KEYED at the T RATIFICATION (2026-07-29 [date corrected 2026-07-30; original
record mis-dated 2026-07-31]; verdict §§3–4): the frame sits AT THE
SITE (`es = .st H` via `hframe`, so `entEvent es` is the site's state event — tied
to the note's exact Σ_c by the ledger's `state_cell` law, MOVES 7503–7510: "Charge
jvol(c │ Σ) … then by (SIB) at c: μ(fiber T │ Σ) = jvol(c │ Σ) · ∏_j μ(S_{T_j} │
Σ_c)"); its `c` is the SPLIT cell — the CHILDREN-read joint cell whose
`branchSetOf` is the roster the recursion partitions (see the `TreeScaffold`
disclosure). `stOf es = some H` roots the children's continuations at H. The `hbr`
guard stays dropped: the frame is UNIFORM over all sites (k = 0 leaves: the ⋂ is
`univ` and `hdecomp` says the site's state has no realized continuations; k = 1
unbranched runs never consume (SIB) — MOVES 7482–7483). -/
structure SplitSiteData (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m) where
  es : EntSt p F n
  c : CA.Cell
  jointExp : ℕ
  S : Node p F → Set (Box p m)
  hS : ∀ ν ∈ CA.branchSetOf c, (∃ hν Tsub leafSpec nsSpec, Tsub.Finite ∧
    S ν = {x | ContFiber T (stOf es) ν hν Tsub leafSpec nsSpec x}) ∨ S ν = Set.univ
  scope : Set (Box p m)
  hdecomp : scope ∩ entEvent T χ es
    = entEvent T χ es ∩ ⋂ ν ∈ CA.branchSetOf c, S ν

/-- the multi-side sites of a tree, off the ledger's hull datum (T-E8). -/
def multiSites (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ) : Set (History p F) :=
  {H | H ∈ Tr.chains ∧ 2 ≤ L.sides H}

/-- the RECURSION SCAFFOLD — REV 3 (Codex-2 #13), with the REV-4 exponent tie
`hframe`, the REV-5 scope tie `hscope`, and the REV-6 `trackOf` threading. Owner of
instances: HC-2's presented faces.

RE-KEYED at the T RE-RATIFICATION (2026-08-01): the frame's cell `c` IS the
ledger's `cellAt H` — the NEW tie `hframe_cell` below. The 2026-07-29
[date corrected 2026-07-30; original record mis-dated 2026-07-31] "DISCLOSED
DEVIATION" (the note's single per-site joint-cell datum split across two entrance
keyings — conditioning cell `cellAt H` vs roster cell `(splitFrame H hH).c`) is
REMOVED per the verdict's material finding ("an arbitrary split-cell roster can
be attached to an unrelated exact conditioning cell … statement mismatch /
under-connected scaffold; M"): the note has ONE cell per site — its branch set is
the roster the recursion partitions AND the cell (SIB) conditions on (MOVES
7283–7292, 7503–7510). Frames stay UNIFORM over the tree's chains and sit AT THE
SITE (`hframe`: `es = .st H`; `jointExp = siteExp H` ties the frame to the site's
own charge). `subtree_part` pins each realized child's prescribed subtree
EXTENSIONALLY to the tree's own child cone (the per-chain accounting needs the
cone partition). Three clauses are owner faces of the note's own proof steps
(MOVES 7503–7515):
* `hcover` — "the segment ends at a site whose joint cell c has branch set
  {b₁,…,b_m} … carrying in T the member-indexed subtrees" — every strict extension
  of a chain passes through a roster child with a prescribed (non-univ) subtree;
* `hglue`/`hglue_root` — REL.2's identification, "each continuing child's factor is,
  after REL.2(a)/(b)/(d)'s identification of b_j's continuation as REL.1 theory over
  O_{δ_j}, the fiber mass of the strictly smaller tree T_j" (7511–7513): the child's
  prescribed-subtree event equals its own state event ∩ its own strict-below subtree
  fiber — the frame-to-frame glue of the recursion;
* `hent_root` — the head chains' ledger entrance is THE root reduction cell of this
  tree's `g` on the head's own track ((JC-root) scope, 7485–7489). -/
structure TreeScaffold (Tr : VTree p F) (T : TreeModel p F n N m pol)
    (CA : CellData p F n N m pol T) (χ : Fin n → Fin m)
    (L : SiteLedger Tr T CA χ)
    (trackOf : Node p F → Polynomial (ZMod p)) where
  g : Fin n → ZMod p
  hg : ∀ x, Tr.fiberAt T χ x → x ∈ rootCell χ g
  root : RootSplitData Tr g
  hcr : ∀ i, ChildRoot none (root.headOf i)
  splitFrame : ∀ H, H ∈ Tr.chains → SplitSiteData Tr T CA χ
  hframe : ∀ H (hH : H ∈ Tr.chains),
    (splitFrame H hH).es = EntSt.st H ∧
    (splitFrame H hH).jointExp = L.siteExp H
  /-- **the ONE-CELL tie** — NEW at the T RE-RATIFICATION (2026-08-01): the frame's
  cell is the site's OWN joint cell (the ledger's `cellAt H`) — the note's single
  D4R.0 datum, closing the c/cSplit two-keying the verdict rejected. -/
  hframe_cell : ∀ H (hH : H ∈ Tr.chains), (splitFrame H hH).c = L.cellAt H
  hscope : ∀ H (hH : H ∈ Tr.chains),
    (splitFrame H hH).scope
    = {x | SubtreeFiber T trackOf (EntSt.st H)
        {H' | H' ∈ Tr.chains ∧ belowEnt trackOf (EntSt.st H : EntSt p F n) H'}
        Tr.leafV Tr.nsLeaf x}
  subtree_part : ∀ H (hH : H ∈ Tr.chains),
    ∀ ν ∈ CA.branchSetOf (splitFrame H hH).c,
    (splitFrame H hH).S ν = Set.univ ∨
    ∃ hν : ChildRoot (some H) ν,
      childHist (some H) ν hν ∈ Tr.chains ∧
      (splitFrame H hH).S ν
        = {x | ContFiber T (some H) ν hν
            {H' | H' ∈ Tr.chains ∧ (childHist (some H) ν hν).IsPrefixOf H'}
            Tr.leafV Tr.nsLeaf x}
  hcover : ∀ H (hH : H ∈ Tr.chains), ∀ H' ∈ Tr.chains,
    H.IsPrefixOf H' → H ≠ H' →
    ∃ ν ∈ CA.branchSetOf (splitFrame H hH).c, ∃ hν : ChildRoot (some H) ν,
      (childHist (some H) ν hν).IsPrefixOf H' ∧
      (splitFrame H hH).S ν ≠ Set.univ
  hglue : ∀ H (hH : H ∈ Tr.chains), ∀ (ν : Node p F) (hν : ChildRoot (some H) ν),
    childHist (some H) ν hν ∈ Tr.chains →
    {x | ContFiber T (some H) ν hν
        {H' | H' ∈ Tr.chains ∧ (childHist (some H) ν hν).IsPrefixOf H'}
        Tr.leafV Tr.nsLeaf x}
      = stateEvent T (some (childHist (some H) ν hν))
        ∩ {x | SubtreeFiber T trackOf (EntSt.st (childHist (some H) ν hν))
            {H' | H' ∈ Tr.chains
              ∧ belowEnt trackOf
                  (EntSt.st (childHist (some H) ν hν) : EntSt p F n) H'}
            Tr.leafV Tr.nsLeaf x}
  hglue_root : ∀ (ν : Node p F) (hν : ChildRoot none ν),
    oneNode ν hν ∈ Tr.chains →
    {x | SubFiber T {H' | H' ∈ Tr.chains ∧ (oneNode ν hν).IsPrefixOf H'}
        ν hν Tr.leafV Tr.nsLeaf x}
      = stateEvent T (some (oneNode ν hν))
        ∩ {x | SubtreeFiber T trackOf (EntSt.st (oneNode ν hν))
            {H' | H' ∈ Tr.chains
              ∧ belowEnt trackOf (EntSt.st (oneNode ν hν) : EntSt p F n) H'}
            Tr.leafV Tr.nsLeaf x}
  hent_root : ∀ H (hH : H ∈ Tr.chains), H.nodes.length = 1 →
    L.parentSt H = EntSt.red g (trackOf H.lastNode)

/-- ns-free trees (T-E10). -/
def NsFree (Tr : VTree p F) : Prop := ∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H

/-- the shape class of a representative tree (T-E10). -/
def shapeClass (Tr₀ : VTree p F) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) : Set (VTree p F) :=
  {Tr | ShapeEquiv n Tr Tr₀ ∧ NsFree Tr ∧ Realizes T χ Tr}

open Classical in
/-- T-D10's class-tree carrier — REV 4/5: the ns-MARK a component, `leafV` a
key-unique `Finset` (order-canonical), the root payload its own component. [E-DEV:
classical `DecidableEq` supplies the `Finset.image` instance — the sigma address type
carries none.] -/
structure ClassTree (n : ℕ) (pol : CanonPolicy p F) where
  addrs : Finset (Σ P : Shape n, PrefIdx n pol P)
  haddr : PrefixClosed addrs
  leafV : Finset ((Σ P : Shape n, PrefIdx n pol P) × Vd)
  hkeys : (leafV.image Prod.fst).card = leafV.card ∧
    ∀ av ∈ leafV, av.1 ∈ addrs ∧ MaximalAddr addrs av.1
  nsMark : Finset (Σ P : Shape n, PrefIdx n pol P)
  hns : ∀ a ∈ nsMark, ∃ v, (a, v) ∈ leafV
  rootV : Multiset Vd
  hroot : ∀ v ∈ rootV, ∃ g : ℕ, 1 ≤ g ∧ v.1 = {(1, g)}

/-- the contract's ReadLedger carrier, DECLARED VERBATIM (T-D14; MovesS §W4-SYNC
ReadLedger roster). -/
structure ReadLedgerT where
  L : ℕ
  fe : ℕ
  hfe : fe ≤ L
  charge : ℕ → ℝ
  Wcharge : ℝ
  βcharge : ℝ

open Classical in
/-- the reads along a chain H of Tr (T-D14). [E-DEV: classical `ite` supplies the
membership filter — `Tr.chains` is a `Set`.] -/
noncomputable def chainReads (Tr : VTree p F) (H : History p F) :
    List (History p F) :=
  (List.range H.nodes.length).filterMap fun r =>
    match prefixAt H (r + 1) with
    | none => none
    | some H' => if H' ∈ Tr.chains then some H' else none

/-- the CONSTRUCTED per-entered-path ledger (T-D14; the S-6 value) with the REV-4
(BDY) index convention: L = the LAST READ INDEX = length − 1. -/
noncomputable def readLedgerOf (Tr : VTree p F) {T : TreeModel p F n N m pol}
    {CA : CellData p F n N m pol T} {χ : Fin n → Fin m}
    (L : SiteLedger Tr T CA χ) (H : History p F)
    (fe : ℕ) (hfe : fe ≤ (chainReads Tr H).length - 1) : ReadLedgerT :=
  { L := (chainReads Tr H).length - 1, fe := fe, hfe := hfe,
    charge := fun r => ((chainReads Tr H)[r]?).elim 0
      (fun H' => ((p : ℝ) ^ (L.siteExp H' : ℤ))⁻¹),
    Wcharge := ∑ r ∈ Finset.Icc 0 fe, ((chainReads Tr H)[r]?).elim 0
      (fun H' => ((p : ℝ) ^ (L.siteExp H' : ℤ))⁻¹),
    βcharge := ∑ r ∈ Finset.Icc (fe + 1) ((chainReads Tr H).length - 1),
      ((chainReads Tr H)[r]?).elim 0 (fun H' => ((p : ℝ) ^ (L.siteExp H' : ℤ))⁻¹) }

/-- the S-11 carrier core (T-D13's target). [E-DEV: the carrier fields are
universe-polymorphic `Type*` — the blueprint's `Type` cannot host `↥𝒯` over the
standing `F : Type*` binder; recorded in MANIFEST.] -/
structure TreeIfaceCore where
  Tree : Type*
  TNode : Type*
  onPath : Tree → TNode → TNode → Prop
  path_refl : ∀ t ν, onPath t ν ν
  path_trans : ∀ t ν₁ ν₂ ν₃, onPath t ν₁ ν₂ → onPath t ν₂ ν₃ → onPath t ν₁ ν₃
  path_antisymm : ∀ t ν₁ ν₂, onPath t ν₁ ν₂ → onPath t ν₂ ν₁ → ν₁ = ν₂
  finN : ∀ t : Tree, Finite {ν : TNode // ∃ ν', onPath t ν ν'}
  node_ne : ∀ t : Tree, ∃ ν : TNode, onPath t ν ν

/-! ### §2.10 THE SEAM-VALUE DEFS — every package field a TYPED STATEMENT (order (9)) -/

/-- TREE-EXP (finite face), ∀-closed — the value of `RS1GivenPackage.tree_exp_fin`.
REV 8: the FULL `CellAssign`; the site vocabulary reads `CA.toCellData` EXPLICITLY.
RE-KEYED at the T RE-RATIFICATION (2026-08-01, the site-entrance keying + the
one-cell tie): the `hjcm` row prices the site's exact cell event under its own
read map (per-site `JCmultiAt` at `H.lastNode`), and the (SIB) consumption at
THIS tree's branching sites rides as the ONE-CELL `SibCountAt` row — conditioning
AND roster cell both `L.cellAt H` (= the frame's cell by `hframe_cell`), the
exact Σ_c tied to the state by `state_cell`. The global `SibCount` row stays —
the root step's cross-track application. -/
def TreeExpFin (T : TreeModel p F n N m pol) (χ : Fin n → Fin m)
    (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N m pol T χ trackOf) : Prop :=
  ∀ (Tr : VTree p F) (L : SiteLedger Tr T CA.toCellData χ),
    Function.Injective χ →
    RootCellsOf T CA.toCellData χ →
    RedCellPartition T CA.toCellData χ trackOf →
    SibCount T CA.toCellData χ → Realizes T χ Tr →
    ∀ (sc : TreeScaffold Tr T CA.toCellData χ L trackOf),
    (∀ H (hH : H ∈ Tr.chains) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA.toCellData χ
        (L.parentSt H) H.lastNode (L.splitAt H hH h2)) →
    (∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S) →
    (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) →
    -- [QUEUE ITEM 5 (E5 hoist ripple 2, TV-A4 shape) 2026-07-31: the ∀-g (U)∧(R)
    --  row, appended last — the formulas are `TrackUniqOn`/`TrackRepOn` (TV_A1)
    --  INLINED (TV_A1 imports this file, so the names cannot be used here).]
    (∀ g : Fin n → ZMod p,
      (∀ y ∈ rootCell χ g, ∀ ν ν' : Node p F, T.child none ν y →
        T.child none ν' y → trackOf ν = trackOf ν' → ν = ν') ∧
      (∀ y ∈ rootCell χ g, ∀ ν : Node p F, T.child none ν y →
        2 ≤ Multiset.count (trackOf ν)
          (UniqueFactorizationMonoid.normalizedFactors (redPoly χ y)))) →
    Nat.card ↥{x | Tr.fiberAt T χ x}
        * p ^ (n + ∑ H ∈ Tr.hfin.toFinset, L.siteExp H) = p ^ m

/-- TREE-N, ∀-closed (`RS1GivenPackage.tree_n`, mass leg) — T-E11's statement.
RE-KEYED at the T RE-RATIFICATION (2026-08-01): same row changes as `TreeExpFin`.
The `Tr.thr n ≤ N'` row is the SEAM's declared threshold gate (the contract
shape); the mass identity itself is proved threshold-free (T-E11's `treeN`), and
the note's CROSS-LEVEL stability content is the SEPARATE seam leg
`TreeNStableStmt` below — CARRIED BY `RS1GivenPackage.tree_n` since 2026-08-01
(the re-ratification integration note: "the stability statement exists but is not
carried by the advertised RS.1 package"). -/
def TreeNStmt (pol : CanonPolicy p F) : Prop :=
  ∀ (N' : ℕ) (T : TreeModel p F n N' (n * N') pol)
    (χ : Fin n → Fin (n * N')) (trackOf : Node p F → Polynomial (ZMod p))
    (CA : CellAssign p F n N' (n * N') pol T χ trackOf),
    ∀ (Tr : VTree p F) (L : SiteLedger Tr T CA.toCellData χ),
    Function.Injective χ → RootCellsOf T CA.toCellData χ →
    RedCellPartition T CA.toCellData χ trackOf →
    ∀ (sc : TreeScaffold Tr T CA.toCellData χ L trackOf),
    SibCount T CA.toCellData χ → Realizes T χ Tr →
    (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) →
    (∀ H (hH : H ∈ Tr.chains) (h2 : 2 ≤ L.sides H),
      JCmultiAt T CA.toCellData χ
        (L.parentSt H) H.lastNode (L.splitAt H hH h2)) →
    (∀ H (hH : H ∈ Tr.chains),
      2 ≤ (CA.toCellData.branchSetOf (L.cellAt H)).card →
      SibCountAt T CA.toCellData χ (L.parentSt H) H.lastNode (L.cellAt H)
        (sc.splitFrame H hH).S) →
    Tr.thr n ≤ N' →
    -- [QUEUE ITEM 5 (E5 hoist ripple 2, TV-A4 shape) 2026-07-31: the ∀-g (U)∧(R)
    --  row, appended last (`TrackUniqOn`/`TrackRepOn` INLINED — import direction).]
    (∀ g : Fin n → ZMod p,
      (∀ y ∈ rootCell χ g, ∀ ν ν' : Node p F, T.child none ν y →
        T.child none ν' y → trackOf ν = trackOf ν' → ν = ν') ∧
      (∀ y ∈ rootCell χ g, ∀ ν : Node p F, T.child none ν y →
        2 ≤ Multiset.count (trackOf ν)
          (UniqueFactorizationMonoid.normalizedFactors (redPoly χ y)))) →
    Nat.card ↥{x : Box p (n * N') | Tr.fiberAt T χ x} * p ^ AofTr Tr L = p ^ (n * N')

/-- **TREE-N's CROSS-LEVEL STABILITY, TYPED** — the note's displayed theorem (MOVES
7559–7574; verdict §5 of the 2026-07-29 ratification [date corrected 2026-07-30;
original record mis-dated 2026-07-31] demanded the statement; the
2026-08-01 re-ratification demanded its INTEGRATION into the RS.1 package). Over a
pinned level tower of models/charts: for every N above the tree's threshold
`thr(T)` and every working level N' ≥ N, the tree fiber reads ONLY the level-<N
digit block — "the fiber is a FINITE intersection of finite-level digit-cell
conditions … hence an exact union of level-N residue classes" (7566–7570). Under
the standard layout (m = n·N', coordinate c at level ⌊c/n⌋ + 1) the level-<N block
is the first n·N coordinates. [Hoisted from T-E11 at the 2026-08-01 integration —
the ∀-closure `TreeNStableStmt` below is the `RS1GivenPackage.tree_n` rider.] -/
def TreeNStable {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N')) (Tr : VTree p F) : Prop :=
  ∀ N : ℕ, Tr.thr n ≤ N →
    ∀ (N' : ℕ) (h' : N₀ ≤ N'), N ≤ N' →
      ∀ x x' : Box p (n * N'),
        (∀ c : Fin (n * N'), (c : ℕ) < n * N → x c = x' c) →
        (Tr.fiberAt (Tat N' h') (χat N') x ↔ Tr.fiberAt (Tat N' h') (χat N') x')

/-- TREE-N's stability leg, ∀-closed — the second conjunct of
`RS1GivenPackage.tree_n` (2026-08-01 integration; the premise row = T-E11b
`treeN_stable`'s own, the note's declared inputs). OPEN — owner HC-2/D4R0K
(T-E11b carries the honest `sorry` with the owner tag).
[QUEUE ITEM 1 ADAPTER 2026-07-31: `KBTotTower`'s chart carrier is now guarded, so
the premise reads it through `fun N' _ => χat N'`. This closure's OWN ∀-χat binder
stays unguarded — its vacuity at n ≥ 1 is the RECORDED TV-B1 fence (consequence 2)
whose repair is the B7 EXECUTION (TV_B7's hoisted rows + guard collapse), a
cluster-B unit outside item 1's scope. Do NOT discharge by the vacuity.] -/
def TreeNStableStmt (pol : CanonPolicy p F) : Prop :=
  ∀ {N₀ : ℕ} (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (trackOf : Node p F → Polynomial (ZMod p)),
    KBTotTower pol Tat (fun N' _ => χat N') trackOf →
    ∀ Tr : VTree p F,
      (∀ H ∈ Tr.chains, ¬ Tr.nsLeaf H) →
      (∀ N' (h' : N₀ ≤ N'), Realizes (Tat N' h') (χat N') Tr) →
      TreeNStable Tat χat Tr

/-- TREE-EXP's (ns) face, ∀-closed (`tree_exp_ns`) — T-E12's statement, finite-face
rider binding (§5 S-2).
[QUEUE ITEM 1 EXECUTED 2026-07-31 (the ratified chi-at guard repair, same-pattern
sweep): the ∀-quantified chart carrier `χat` is GUARDED — the unguarded quantifier
made this closure VACUOUSLY TRUE at n ≥ 1 (compiled witness
`tv_b1_chart_carrier_uninhabited`, TV_B1.lean). T-E12's theorem `treeN_ns` still
binds the unguarded carrier at HEAD; its re-key rides the B-cluster guard collapse
(recorded, QUEUE_EXECUTION_2026-07-31.md).] -/
def TreeExpNs (pol : CanonPolicy p F) : Prop :=
  ∀ (Tr : VTree p F) (H : History p F), (H ∈ Tr.chains ∧ Tr.nsLeaf H) →
    ∀ (N₀ : ℕ) (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
      (χat : ∀ N' (h : N₀ ≤ N'), Fin n → Fin (n * N'))
      (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
      (Lat : ∀ N' h, NsLumpFamily (Tat N' h) (Jat N' h)), JetTower Jat →
      (∀ N' h, ZCPack (Jat N' h)) →
      (∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N') →
      Filter.Tendsto
        (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
        Filter.atTop Filter.atTop →
      (∀ N' (h : N₀ ≤ N'), (stateTruncAt Jat N').Nonempty) →
      (∀ N' (h : N₀ ≤ N'), {x : Box p (n * N') | Tr.fiberAt (Tat N' h) (χat N' h) x}
        ⊆ nsTruncAt Jat Lat N') →
      Filter.Tendsto (fun N' : {k // N₀ ≤ k} =>
          (Nat.card ↥{x : Box p (n * N'.1) |
              Tr.fiberAt (Tat N'.1 N'.2) (χat N'.1 N'.2) x} : ℝ)
            / (p : ℝ) ^ (n * N'.1))
        Filter.atTop (nhds 0)

/-- ONE-F, ∀-closed (`one_f`) — T-F1's statement over the extensional quotient. -/
def OneFStmt (T : TreeModel p F n N m pol) (χ : Fin n → Fin m) : Prop :=
  ∀ x : Box p m, Decided T χ x →
    ∃ Tr : VTree p F, Tr.fiberAt T χ x ∧
      ∀ Tr' : VTree p F, Tr'.fiberAt T χ x → Tr.ext Tr'

/-- TB-CAP as amended, pinned (`tb_cap`): the (hen) cap-1 law + its finite-union face
(T-C1) and the (irr) per-class cross-level cap law (T-C2). NO (ns) leg (§0). -/
def TBCapPinned (pol : CanonPolicy p F) (m : ℕ) : Prop :=
  (∀ (χ : Fin n → Fin m), Function.Injective χ → ∀ x x' : Box p m,
    (∀ b : Fin n, x (χ b) = x' (χ b)) → henPayload χ x = henPayload χ x') ∧
  (∀ (χ : Fin n → Fin m), Function.Injective χ → ∀ v₀ : Multiset Vd,
    ∃ G : Finset (Fin n → ZMod p),
      {x : Box p m | henPayload χ x = v₀} = ⋃ g ∈ G, rootCell χ g) ∧
  (∃ cap : ∀ {P : Shape n}, PrefIdx n pol P → ℕ, CapIrrLaw p F n pol cap)

/-- the (ns) amendment pair, pinned: leg 1 = T-C3's conclusion ∀-closed; leg 2 =
T-C7's truncated-ratio statement ∀-closed. FINITE-FACE RIDER binding. -/
def NsAmendedPair (pol : CanonPolicy p F) : Prop :=
  (∀ (N' m' : ℕ) (T : TreeModel p F n N' m' pol) (H : History p F)
    (J : JetSetup H n N' m') (Lf : NsLumpFamily T J),
    (∀ M M', M ≤ M' → Lf.L M' ⊆ Lf.L M) ∧
    nsClass T H = {x | T.mem (some H) x} ∩ ⋂ M, Lf.L M) ∧
  (∀ (H : History p F) (N₀ : ℕ) (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' h, NsLumpFamily (Tat N' h) (Jat N' h)), JetTower Jat →
    (∀ N' h, ZCPack (Jat N' h)) →
    (∀ N' h, M₀ (Jat N' h) ≤ Mlev (Jat N' h) N') →
    Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} => Mlev (Jat N'.1 N'.2) N'.1 - M₀ (Jat N'.1 N'.2))
      Filter.atTop Filter.atTop →
    (∀ N' (h : N₀ ≤ N'), (stateTruncAt Jat N').Nonempty) →
    Filter.Tendsto (fun N' : {k // N₀ ≤ k} =>
        (Nat.card ↥(nsTruncAt Jat Lat N'.1) : ℝ) / (Nat.card ↥(stateTruncAt Jat N'.1)))
      Filter.atTop (nhds 0))

/-- the REAL finite-level conditional cap mass (T1: DEFINED, never a field). -/
noncomputable def capMassAt {H : History p F} {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' h, NsLumpFamily (Tat N' h) (Jat N' h))
    (N' : ℕ) (h : N₀ ≤ N') (M : ℕ) : ℝ :=
  (Nat.card ↥{x | x ∈ stateTruncAt Jat N' ∧ x ∈ (Lat N' h).L M} : ℝ)
    / (Nat.card ↥(stateTruncAt Jat N'))

/-- the REAL pinned-coordinate count |Z_M| (T1: DEFINED, never a field). -/
noncomputable def nsZAt {H : History p F} {N₀ : ℕ}
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (N' : ℕ) (h : N₀ ≤ N') (M : ℕ) : ℕ :=
  (interiorFreshIdx (Jat N' h) M).card

/-- **NS-PRICING (OPEN — owner MovesS wave 5 / [2b])**: the C(b) pricing equality AT
THE REAL CARRIERS — `capMassAt = p^{−nsZAt}` on the resolved cap range. -/
def NsPricing (pol : CanonPolicy p F) : Prop :=
  ∀ (H : History p F) (N₀ : ℕ)
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N'))
    (Lat : ∀ N' h, NsLumpFamily (Tat N' h) (Jat N' h)),
    (∀ N' h, ZCPack (Jat N' h)) →
    (∀ N' (h : N₀ ≤ N'), (stateTruncAt Jat N').Nonempty) →
    ∀ (N' : ℕ) (h : N₀ ≤ N') (M : ℕ),
      M₀ (Jat N' h) ≤ M → M ≤ Mlev (Jat N' h) N' →
      capMassAt Tat Jat Lat N' h M = ((p : ℝ) ^ (nsZAt Jat N' h M : ℕ))⁻¹

/-- **NS-GROWTH (OPEN — owner MovesS wave 5 / [2b])**: the REAL diagonal Z diverges
along the tower, scoped to the mechanism's own class (`Realizable H` +
`ScaleFaithful` — the C7-3 genre disclosure rides in the blueprint). -/
def NsGrowth (pol : CanonPolicy p F) : Prop :=
  ∀ (H : History p F) (N₀ : ℕ)
    (Jat : ∀ N' (h : N₀ ≤ N'), JetSetup H n N' (n * N')),
    LeanUrat.MovesC.Realizable H →
    JetTower Jat → (∀ N' h, ZCPack (Jat N' h)) →
    (∀ N' h, ScaleFaithful (Jat N' h) N') →
    Filter.Tendsto
      (fun N' : {k // N₀ ≤ k} =>
        nsZAt Jat N'.1 N'.2 (Mlev (Jat N'.1 N'.2) N'.1))
      Filter.atTop Filter.atTop

/-- **the pure-analysis leg — PROVED IN-CORPUS** (T1): pricing + growth +
continuity-from-above force the limit to 0. The owner applies it AT μcap := the
`capMassAt` data, Z := the `nsZAt` data, μclass := its own profinite class mass. -/
theorem nsNull_of_pricing_growth (μcap : ℕ → ℝ) (μclass : ℝ) (Z : ℕ → ℕ)
    (hprice : ∀ M : ℕ, μcap M = ((p : ℝ) ^ (Z M : ℕ))⁻¹)
    (hgrow : Filter.Tendsto Z Filter.atTop Filter.atTop)
    (hcont : Filter.Tendsto μcap Filter.atTop (nhds μclass)) :
    μclass = 0 := by
  have hp : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpow : Filter.Tendsto (fun k : ℕ => (p : ℝ) ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hp
  have hZ : Filter.Tendsto (fun M : ℕ => (p : ℝ) ^ (Z M)) Filter.atTop Filter.atTop :=
    hpow.comp hgrow
  have h0 : Filter.Tendsto (fun M : ℕ => ((p : ℝ) ^ (Z M))⁻¹) Filter.atTop (nhds 0) :=
    hZ.inv_tendsto_atTop
  have hμ : Filter.Tendsto μcap Filter.atTop (nhds 0) := by
    have : μcap = fun M => ((p : ℝ) ^ (Z M))⁻¹ := funext hprice
    rw [this]; exact h0
  exact tendsto_nhds_unique hcont hμ

/-- VP pinned (`vp`): (c1)/(c3-a) inhabited cell-data verdict models per level, (c2)
the tower-keyed KB-TOT closure, VP-SOUND's two cites + the REV-8 totality leg.
[QUEUE ITEM 1 ADAPTER 2026-07-31: `covering` reads the guarded `KBTotTower` through
`fun N' _ => χat N'`. This structure's OWN unguarded χat parameter shares the TV-B1
disease (uninstantiable at n ≥ 1); its guard is the same B-cluster collapse as
`TreeNStableStmt`'s (recorded), outside item 1's named scope.] -/
structure VPPinned (pol : CanonPolicy p F) {N₀ : ℕ}
    (Tat : ∀ N', N₀ ≤ N' → TreeModel p F n N' (n * N') pol)
    (χat : ∀ N', Fin n → Fin (n * N'))
    (trackOf : Node p F → Polynomial (ZMod p))
    (CAat : ∀ N' h,
      CellAssign p F n N' (n * N') pol (Tat N' h) (χat N') trackOf) :
    Prop where
  model : ∀ N' h,
    Nonempty (VerdictModelT (Tat N' h) (CAat N' h).toCellData (χat N'))
  covering : KBTotTower pol Tat (fun N' _ => χat N') trackOf
  hen_lift : HenLift p
  om_sat : OmSat p F n trackOf
  om_total : OmSatTot p F n trackOf

/-- the finite decided-slice partition premise (T-F3) — displayed (Fable-2 GAP-2). -/
def PartitionsDecided (𝒯 : Finset (VTree p F)) (T : TreeModel p F n N m pol)
    (χ : Fin n → Fin m) : Prop :=
  (∀ Tr ∈ 𝒯, ∀ Tr' ∈ 𝒯, ¬ VTree.ext Tr Tr' →
    Disjoint {x | VTree.fiberAt Tr T χ x} {x | VTree.fiberAt Tr' T χ x}) ∧
  (∀ x : Box p m, Decided T χ x → ∃ Tr ∈ 𝒯, VTree.fiberAt Tr T χ x)

/-- pre-halt is η-CLASS data (T-F2's `hph`; §0 row) — owner HC-2. -/
def PreHaltClassData {P : Shape n} (pol : CanonPolicy p F) : Prop :=
  ∀ (i : PrefIdx n pol P) (H : History p F), H ∈ PrefSet n pol P → SameClass i H →
    (PreHalt H ↔ PreHalt (reprOf i))

/-- prefix-coherent representative choice (T-D11's premise) — owner HC-2. -/
def PrefixCoherentRepr (n : ℕ) (pol : CanonPolicy p F) : Prop :=
  ∀ {P P' : Shape n} (i : PrefIdx n pol P) (i' : PrefIdx n pol P'),
    ClassPrefixOf i' i → (reprOf i').IsPrefixOf (reprOf i)

/-- REPRESENTATIVE-KEY INJECTIVITY — NEW at REV 6 (Codex-5 gap #10). Owner HC-2. -/
def ReprInj (n : ℕ) (pol : CanonPolicy p F) : Prop :=
  ∀ {P P' : Shape n} (i : PrefIdx n pol P) (i' : PrefIdx n pol P'),
    reprOf i = reprOf i' →
    (⟨P, i⟩ : Σ P : Shape n, PrefIdx n pol P) = ⟨P', i'⟩

/-- CLASS COVER — NEW at REV 5 (Codex-4 #9): every realized chain is CLASSIFIED, with
the representative transporting the chain's tree data. Owner HC-2. Consumed by
T-D11's `fibOf_partition` ONLY. -/
def ClassCover (T : TreeModel p F n N m pol) : Prop :=
  ∀ (H : History p F), (∃ x, T.mem (some H) x) →
    ∃ (P : Shape n) (i : PrefIdx n pol P), H ∈ PrefSet n pol P ∧ SameClass i H ∧
      (∀ y, T.mem (some H) y ↔ T.mem (some (reprOf i)) y) ∧
      (∀ (ν : Node p F) (y : Box p m),
        T.child (some H) ν y ↔ T.child (some (reprOf i)) ν y) ∧
      (IrrHalts H ↔ IrrHalts (reprOf i)) ∧
      irrVerdictOf H = irrVerdictOf (reprOf i) ∧
      nsVerdictOf H = nsVerdictOf (reprOf i) ∧
      (∀ H' : History p F, H'.IsPrefixOf H → H'.nodes ≠ [] →
        ∃ (P' : Shape n) (i' : PrefIdx n pol P'),
          H' ∈ PrefSet n pol P' ∧ SameClass i' H' ∧ ClassPrefixOf i' i)

/-! ### §2.10 S-3's re-keyed premise, over the IMPORTED MovesS objects -/

/-- XRB's CONCLUSION equality — the `hxrb` premise the S-3 contract prescribes,
stated over the REAL imported `MovesS.RS1Meas.βmeas` (h-independence at pools). -/
def hxrbStmt {n' : ℕ} (T' : MovesS.TableShape n') (M : MovesS.MeasuredSide T')
    (B₀ : MovesS.RS1Meas T' M) : Prop :=
  ∀ e (he : e ∈ Finset.Icc 1 n') (h h' : ℕ) (τ : T'.State e)
    (σ' : Multiset T'.VType) (q₀ : ℚ), q₀ ∈ M.Pools →
    B₀.βmeas e he h τ σ' q₀ = B₀.βmeas e he h' τ σ' q₀

/-- W3_recursion, RE-KEYED per the S-3 demand: premise row = the GIVEN list + the REAL
IMPORTED `MovesS.LedgerIV` (REV 4, Codex-3 #18) + `hxrbStmt` — never the bare
`W2_xrb` implication. -/
def w3Rekeyed {n' : ℕ} {T' : MovesS.TableShape n'} {M : MovesS.MeasuredSide T'}
    (RB : MovesS.RatBurdens T' M) (hdc : MovesS.DegCons T')
    (given : Prop)
    (B₀ : MovesS.RS1Meas T' M) : Prop :=
  given → MovesS.LedgerIV T' M → hxrbStmt T' M B₀ →
  ∀ e (he : e ∈ Finset.Icc 1 n') (τ : T'.State e) (σ' : Multiset T'.VType)
    (q₀ : ℚ) (hq : q₀ ∈ M.Pools), M.activeState q₀ e τ →
    ∀ h_ent, B₀.βmeas e he h_ent τ σ' q₀
      = MovesS.evalRe T' M RB hdc e he τ σ' q₀ (fun e' he' => B₀.βmeas e' he' h_ent)

/-! ### §2.11 gate plumbing (the CLOSED toy names; node/tree literals live at T-G1) -/

/-- the constant-lift toy policy. [IP-4 DISCHARGED: the built `CanonPolicy` carries
exactly the two fields `liftOf`/`blind` (MovesD/Defs 345) — the constant lift closes
BOTH; no residual field, no MANIFEST deviation needed.] -/
noncomputable def polTriv : CanonPolicy 2 (ZMod 2) :=
  { liftOf := fun _ => Polynomial.X, blind := fun _ _ => rfl }

def toyχ : Fin 2 → Fin 9 := fun b => ⟨(b : ℕ), by omega⟩

def toyG : Fin 2 → ZMod 2 := fun _ => 0

/-- REV 8: the toys' constant track binding — the one live track (f̄ = x², X repeated). -/
noncomputable def toyTrackOf : Node 2 (ZMod 2) → Polynomial (ZMod 2) :=
  fun _ => Polynomial.X

def toyN : ℕ := 2
def toyN3 : ℕ := 3

end LeanUrat.MovesT







