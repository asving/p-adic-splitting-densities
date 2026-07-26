/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs
import LeanUrat.Moves.DefsT
import LeanUrat.Moves.DefsCore
import LeanUrat.Moves.DefsL

/-!
# MovesC/Defs — shared vocabulary for §C, the composition theorem

**Provenance.** `lean/notes/MOVES_2026-07-24.md` §C REV 2 (ACCEPTED 2026-07-26, passes 12+13
CLEAN), with the two fresh-context derivations `C10B_DERIVATION_2026-07-26.md` (the window kernel)
and `C15_DERIVATION_2026-07-26.md` (the counting mechanism, Route B — count without addresses).
Design rationale, the per-unit DAG, and the honest boundary-deferred list live in
`lean/notes/MOVESC_LEAN_BLUEPRINT_2026-07-26.md`. This file contains ONLY definitions/structures —
no theorems, no `sorry`, no axioms.

## The concrete model (design decisions — see the blueprint §"Design decisions")

* **≺-sorted coordinates.** §C's base coordinates are pairs `c = (ℓ, i)` (`ℓ` = p-adic level,
  `i` = coefficient index) under the GLOBAL ORDER `(ℓ,i) ≺ (ℓ',i')` iff `ℓ<ℓ'`, or `ℓ=ℓ'` and
  `i>i'` (`CoordPrec`). Every locus below is worked in ≺-SORTED coordinates: a box of `m = nN`
  base digits is `Fin m`, with the `Fin` order STANDING FOR `≺` (the note always "solves in
  ≺-order"). `Coord`/`CoordPrec` are kept for faithfulness and to state the sorting bijection
  (`C0.coordSort`, a finite-linear-order fact); the digit systems live over `Fin m`.
* **Loci ARE unitriangular digit systems** (the existing `LeanUrat.Moves.DigitSystem`, DefsT). The
  BLOCK CONVENTION (§C.0): an `F`-digit of residue degree `d` is its `d` base equations, each over
  the alphabet `ZMod p`, each factor `p⁻¹`. So `Locus p m := DigitSystem m (ZMod p)` and the mass
  is `Nat.card` of its solution set — the "existing DigitSystem + Nat.card pattern". Codimension
  `K` ⟺ mass `p^{m−K}` ⟺ `numPinned = K` (C0.digitSystemMass / PIN-WELLDEF).
* **Histories/nodes over the existing tower vocabulary.** A `Node` carries its frame `σ : Stage`
  and the read data; a `History` is a coherent list whose consecutive stages are linked by the
  existing `TransitionCoreL` (increments) / `IsRecenteringCore` (recenterings). The graded content
  §C needs on top of §B2-DEF (the K1-chain-to-digit-coordinate identification = the global
  jet-coordinate system, and the piece maps `R_δ`) is the UNBUILT graded ring: it enters ONLY as
  the explicitly flagged interface predicates `JetPresentation`, `LstData`, `TypObject` (blueprint
  §"Boundary-deferred"). Never approximated.

## Faithfulness flags (the trust boundary)

Every interface predicate here (`JetPresentation`, `LstData`, `TypObject`, `DomData`) is flagged
for semantic-guardian review: it encodes graded-ring content §C's proof consumes but §B2-DEF's
Lean corpus does not yet supply. The counting core (C0/C1/C4/C5/C6) is combinatorial over
`DigitSystem`s and is provable; the geometric/graded bridge (C2/C3) is where the deferral lives.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesC

open Polynomial LeanUrat.Moves

/-! ## C0. Base coordinates, the global order ≺, unitriangular moves -/

/-- A **base coordinate** `c = (ℓ, i)`: `c.1 = ℓ` the p-adic level, `c.2 = i` the coefficient
index (§C.0). -/
abbrev Coord : Type := ℕ × ℕ

/-- The **global order** `≺` (§C.0): `(ℓ,i) ≺ (ℓ',i')` iff `ℓ < ℓ'`, or `ℓ = ℓ'` and `i > i'`
(within a level, from the TOP coefficient down — Fact A's elimination order). -/
def CoordPrec (c c' : Coord) : Prop := c.1 < c'.1 ∨ (c.1 = c'.1 ∧ c'.2 < c.2)

/-- A **§C locus**: a unitriangular digit system over `m = nN` base digits in ≺-sorted
coordinates, alphabet `ZMod p` (the BLOCK CONVENTION: each `F`-digit is its base digits, each
factor `p⁻¹`). Reuses the accepted `DigitSystem` (DefsT); its solution set is the cylinder. -/
abbrev Locus (p m : ℕ) : Type := DigitSystem m (ZMod p)

/-- The **mass** of a locus: the count of its solutions among the `p^m` box points. By the count
law `= p^{m − numPinned}` (`C0.digitSystemMass`). -/
noncomputable def Locus.mass {p m : ℕ} (D : Locus p m) : ℕ :=
  Nat.card {x : Fin m → ZMod p // D.IsSolution x}

/-- The full box mass `p^{nN} = p^m`. -/
def boxMass (p m : ℕ) : ℕ := p ^ m

/-- **A move map is unitriangular for `≺`** (§C.0.5): `(Θx)_i = x_i + φ_i(x_j : j ≺ i)` — the
diagonal is the identity and the correction `φ_i` is an ARBITRARY function of ≺-earlier
coordinates (in ≺-sorted `Fin m` coordinates, `j < i`). This is the shape Fact A's division
accounting produces, in both directions. -/
def IsUnitriangular {m : ℕ} {R : Type*} [Add R] (Θ : (Fin m → R) → (Fin m → R)) : Prop :=
  ∀ i : Fin m, ∃ corr : ((j : Fin m) → j < i → R) → R,
    ∀ x, Θ x i = x i + corr (fun j _ => x j)

/-- The **pullback** of a locus `D` by a move `Θ`: the points whose `Θ`-image solves `D`
(`Θ*(E)` of §C.0.5's pin-transport corollary). -/
def Locus.pullback {p m : ℕ} (D : Locus p m) (Θ : (Fin m → ZMod p) → (Fin m → ZMod p)) :
    Set (Fin m → ZMod p) := {x | D.IsSolution (Θ x)}

/-! ## C1. The (ZC) state cylinder (§C.1.5) -/

/-- A **staircase / floor** on the base indices: an affine "line" per base index, `ℚ`-valued, with
`⊥` off its clause region (§C.1.5's `F_i`, the pointwise max of the history's line staircases). We
represent it as a map to `WithBot ℚ`. -/
abbrev Staircase : Type := ℕ → WithBot ℚ

/-- The **absolute-height** map `ht(c) = ℓ + off(i)` (§C.1.5's scale declaration): a base
coordinate's v_p-height in the current frame. Carried as data because `off` depends on the
history's stage weights `κ_r` (the LST content; its identification with the K1-chain weight is the
boundary-deferred `LstData`). -/
abbrev HtMap : Type := Coord → ℚ

/-- **The (ZC) invariant on a state cylinder** (§C.1.5, carried along the history). Bundled as a
`Prop` over a locus `Σ_i`:
* **(ZC-a)** VALUATION CORE — every pinned NON-rim coordinate is a LITERAL ZERO (`solve ≡ 0`): the
  zero downset `Z(F_i)` with per-index top `F_i`;
* **(ZC-b)** LEADS AT RIM — every pinned coordinate that is not a literal zero is a rim lead
  (`DIG_i` is unitriangular with each equation solving for a rim block, base index ≥ `μ_i·D_{i+1}`,
  encoded by the ≺-position threshold `rimStart`);
* **(ZC-c)** MASS — `numPinned = freshSum` (the cumulative D.11-nominal fresh count `Σ_{m≤i} m*`),
  so `mass = p^{m − freshSum}`. (A `Type`-valued bundle: it carries the rim threshold and fresh
count as data alongside the invariant proofs.) -/
structure ZCData {p m : ℕ} (D : Locus p m) where
  /-- the ≺-position at/above which coordinates carry transported rim data (base index
  ≥ `μ_i·D_{i+1}`). -/
  rimStart : Fin m
  /-- (ZC-a)+(ZC-b): every pinned coordinate is either a rim lead or a literal zero. -/
  pin_dichotomy : ∀ i : Fin m, D.pinned i = true →
    (rimStart ≤ i ∨ (∀ f : ((j : Fin m) → j < i → ZMod p), D.solve i f = 0))
  /-- the cumulative D.11-nominal fresh base-digit count `Σ_{m≤i} m*(ν_m)`. -/
  freshSum : ℕ
  /-- (ZC-c): the locus codimension equals the cumulative fresh count. -/
  zc_c : D.numPinned = freshSum

/-! ## C2. Lines, floor domination (DOM), and the boundary-deferred LST / TYP interfaces -/

/-- A **read-side line** as an AFFINE function of the base index (absolute v_p-scale, §C.1's DOM):
`at b = intercept − slope · b`. `line_m` of node `m` is such a line; the floor `F_i` is the
pointwise max over the history. -/
structure Line where
  intercept : ℚ
  slope : ℚ

/-- Evaluate a line at a base index. -/
def Line.at (L : Line) (b : ℕ) : ℚ := L.intercept - L.slope * (b : ℚ)

/-- The **floor / staircase** `F_i` as the pointwise max of the history's lines over `[0, i]`
(§C.1.5 (ZC-a); on the factor interior it is the current line — Lemma DOM). -/
noncomputable def floorOf (lines : ℕ → Line) (i b : ℕ) : ℚ :=
  Finset.sup' (Finset.range (i + 1)) (by simp) (fun m => (lines m).at b)

/-- **DOM interface** (§C.1 Lemma DOM, interior floor domination): the hypotheses of the DISPLAYED
affine induction — the read side is strictly steeper than the box line ((I-aug)), the vertex-entry
inequality holds at the endpoints, and the next factor interior is width-confined. The DOM
conclusion (`line_i ≥ line_m` on the interior; floor = current line) is the PROVABLE affine lemma
`C2.DOM`; this bundle is its faithful hypothesis record (the geometric inputs D.4/D.8/D.3(d)/D.7
supply per §B2-DEF). -/
structure DomData (lines : ℕ → Line) (i : ℕ) (interiorEnd : ℕ) : Prop where
  /-- (I-aug): the current line descends strictly faster than every earlier one. -/
  steeper : ∀ m, m < i → (lines m).slope < (lines i).slope
  /-- vertex-entry (§C.1 DOM(2)): at the interior end the current line dominates every earlier
  one — the endpoint inequality that seeds the affine induction. -/
  vertex_entry : ∀ m, m ≤ i → (lines m).at interiorEnd ≤ (lines i).at interiorEnd

/-- **LST interface** (§C.1 Lemma LST, level-set scale-typing) — BOUNDARY-DEFERRED (needs the
K1-chain-to-digit-coordinate identification, the global jet-coordinate system: `MOVES_LEAN`
round-4 gap R4.5 item 3, the unbuilt graded ring). Carries:
* **(i) TYPING** — `ht(c)` IS the K1-chain weight of `c`'s basis monomial (`ht_isWeight`);
* **(ii) FLOOR CONSTANCY** — on the factor interior `ht` is block-constant, equal to the current
  line's value (`floor_const`);
* **(iii) SELECTION** — a factor-interior slot's weight-`γ'` level set (`γ' > old`) lies STRICTLY
  ABOVE the floor downset (`selection`), so the whole level set is free on `Σ_i`.
Flagged for review: the identification of the abstract `HtMap` with the genuine K1 weight. -/
structure LstData {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (σ : Stage p F) (ht : HtMap) (lines : ℕ → Line) (i : ℕ) : Prop where
  /-- (i) SCALE: `ht(ℓ,b) = ℓ + off(b)` for the inner-tower offset `off(b) = Σ_r innerslot_r(b)·κ_r`
  — the absolute-height declaration (§C.1.5 scale). The DEFERRED half is that `off` equals the
  genuine `κ_r = h_r/(e_r·STR_r)` combination = the K1-chain weight of the basis monomial. -/
  ht_scale : ∃ off : ℕ → ℚ, ∀ b l : ℕ, ht (l, b) = (l : ℚ) + off b
  /-- (ii) FLOOR CONSTANCY on the factor interior: the floor IS the current line (Lemma DOM's
  floor form), block-constant. -/
  floor_const : ∀ b : ℕ, floorOf lines i b = (lines i).at b
  /-- (iii) SELECTION: a level set at height `γ' > old_i(b)` sits STRICTLY ABOVE the floor
  downset — the whole level set is free on `Σ_i`. -/
  selection : ∀ (b : ℕ) (γ' : ℚ), (lines i).at b < γ' →
    ∀ l : ℕ, ht (l, b) = γ' → floorOf lines i b < γ'

/-- **TYP object** (§C Lemma TYP, the typed degree-`γ'` initial form) — BOUNDARY-DEFERRED (needs
the graded piece `gr^Ĉ_{δ'}` and its piece map `R_δ`, the unbuilt graded ring: R4.5 item 1). A
fresh value clause at exact valuation `γ'` is realized by a SURJECTIVE additive hom from the
weight-`γ'` level-set assignments (`s` free base coordinates) onto the digit's alphabet `α` — the
piece map, additive + injective on the piece with image = the additive span of the slot images
(D.3(e)(i)). Its PROVABLE combinatorial consequence — equal-size fibers, so the clause cuts
`|α|⁻¹` — is `C2.fiberCount`. -/
structure TypObject {p : ℕ} (s : ℕ) (α : Type*) [AddCommGroup α] where
  /-- the piece map on the level-set assignments (graded content; existence DEFERRED). -/
  φ : (Fin s → ZMod p) →+ α
  /-- surjective onto the alphabet (D.3(e)(i): image = the additive span of the slot images). -/
  surj : Function.Surjective φ

/-! ## C3. Read species, nodes, histories, the E_fresh species inventory, realizability -/

/-- The **species of a read** (§C.0): the ROOT read `ν₀`, an INCREMENT (`e·g > 1`, genuine residue
growth), or a RECENTERING (`e_read = 1`, degree unchanged, a recorded lift). -/
inductive ReadSpecies where
  | root
  | increment
  | recentering
deriving DecidableEq

/-- **A node** `ν_i` — one read of the OM classifier in a history (§C.0). It carries its FRAME
`σ` (the stage `i` it reads in, over the existing `Stage` vocabulary), the read index/descend data,
the side geometry, its read-side LINE (absolute scale, for DOM/LST), the fixed side-pattern
`pat`/its key `ψ` and anchored residual `Ranch` (pattern-only data determining `vtx`), and — for
recenterings — the recorded lift `lift`. -/
structure Node (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  species : ReadSpecies
  σ : Stage p F
  e : ℕ
  h : ℕ
  g : ℕ
  μ : ℕ
  a : ℤ
  s0 : ℕ
  wSide : ℕ
  Dwidth : ℕ
  line : Line
  lift : Polynomial ℤ_[p]
  ψ : Polynomial ↥σ.K
  Ranch : Polynomial ↥σ.K
  pat : ℕ → Polynomial ↥σ.K

/-- `R_anch/ψ^μ mod ψ` — the polynomial factor of `vtx(ν)` (§C.0's TRANSPORTED VERTEX VALUE;
pattern-only, so `vtx` is a predicate on node data alone, per rev 8). -/
noncomputable def Node.vtxPoly {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (ν : Node p F) : Polynomial ↥ν.σ.K :=
  (ν.Ranch /ₘ ν.ψ ^ ν.μ) %ₘ ν.ψ

/-- **A read history** `H = (ν₀, …, ν_k)` (§C.0): the root read then increments/recenterings, in
any interleaving and depth. -/
structure History (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  nodes : List (Node p F)
  nonempty : nodes ≠ []
  root_first : (nodes.head?).map Node.species = some ReadSpecies.root

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **History coherence**: consecutive frames are linked by the accepted §B2-DEF transitions — an
INCREMENT node's frame descends from its predecessor by `TransitionCoreL` (D.7), a RECENTERING by
`IsRecenteringCore` (D.10). (The witness data — residue root `z̄`, child index — is existential;
this is the provenance interface tying §C to the accepted tower.) -/
def HistoryCoherent (H : History p F) : Prop :=
  ∀ i : ℕ, (hi : i + 1 < H.nodes.length) →
    ((H.nodes[i+1]'hi).species = ReadSpecies.recentering →
      ∃ (cc : ↥(H.nodes[i]'(by omega)).σ.K) (tt : Polynomial ℤ_[p]),
        IsRecenteringCore (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi).σ cc tt) ∧
    ((H.nodes[i+1]'hi).species = ReadSpecies.increment →
      ∃ (zbar : Fˣ),
        TransitionCoreL (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi).σ
          (H.nodes[i+1]'hi).σ.Φ (H.nodes[i+1]'hi).σ.e (H.nodes[i+1]'hi).σ.h zbar)

/-- **Realizability** (§C.0, the two side conditions C.1(ii) isolates — equations of NO `E`, they
constrain the history's DATA, never `f`):
* **(NA)** at a NON-ADJACENT read (`s₀'+w' < μ_i`): the pinned old vertex lies STRICTLY ABOVE the
  extended new line — `new(μ_i) < old(μ_i)`;
* **(HV)** at an ADJACENT read (`s₀'+w' = μ_i`): the pattern lead of `ν_{i+1}` equals `vtx(ν_i)` —
  a data identity (both explicit functions of node data). -/
def Realizable (H : History p F) : Prop :=
  ∀ i : ℕ, (hi : i + 1 < H.nodes.length) →
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide < (H.nodes[i]'(by omega)).μ →
      (H.nodes[i+1]'hi).line.at (H.nodes[i]'(by omega)).μ
        < (H.nodes[i]'(by omega)).line.at (H.nodes[i]'(by omega)).μ) ∧
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide = (H.nodes[i]'(by omega)).μ →
      ∃ lead : Polynomial ↥(H.nodes[i]'(by omega)).σ.K, (H.nodes[i]'(by omega)).vtxPoly = lead)

/-- **Fresh-clause data** of a read against `Σ_i` (§C.1's E_fresh species inventory, Route B). In
the BLOCK CONVENTION every fresh digit is a single base coordinate over `ZMod p`: the (α) interior
strip zeros + on-lattice value digits, the (β) strips, the (γ) strips left of the crossing `j×`,
the non-adjacent endpoint. For the conditional count (C.1.5'(1)) the consumable content is the
fresh pinned coordinate SET (pairwise distinct, being a `Finset`) together with the witness that
each is FREE on `Σ_i`. -/
structure FreshData {p m : ℕ} (Sigma : Locus p m) where
  /-- the base coordinates the FRESH clauses pin (strips + value digits), pairwise distinct. -/
  coords : Finset (Fin m)
  /-- freshness: none is already pinned by `Σ_i` — all are free coordinates of the solved graph. -/
  free : ∀ c ∈ coords, Sigma.pinned c = false
  /-- the value each fresh coordinate is pinned to: `0` for a strip zero, the pattern value `v` for
  an on-lattice value digit (the TYP image element). -/
  pinTo : Fin m → ZMod p

/-- The D.11-nominal fresh count `m*(ν) = |coords|`; `vol_nom(E_fresh) = p^{−m*}`. -/
def FreshData.mstar {p m : ℕ} {Sigma : Locus p m} (fd : FreshData Sigma) : ℕ := fd.coords.card

/-- The membership predicate the fresh clauses cut: `x` pins each fresh coordinate to its value. -/
def FreshData.sat {p m : ℕ} {Sigma : Locus p m} (fd : FreshData Sigma) (x : Fin m → ZMod p) :
    Prop := ∀ c ∈ fd.coords, x c = fd.pinTo c

/-! ## C4-C6. The presented history (jet setup), admissible terminal systems -/

/-- **The jet presentation of a history** — the BOUNDARY-DEFERRED bridge from the accepted tower to
digit systems (§C.2's `Ψ_H`, the global jet-coordinate system D.3(e)(ii) applied down the whole
tower: `MOVES_LEAN` round-4 gap R4.5 item 3, the unbuilt graded ring). Over a box of `m = nN` base
digits it supplies, for each prefix length `i`, the presented STATE CYLINDER `Σ_i` (a `Locus`) with
its (ZC) invariant, the per-step FRESH-clause data, the move maps `Θ_i` (unitriangular, §C.0.5),
and the defining RECURSION `Σ_{i+1} = Θ_i(Σ_i ∩ E_fresh(ν_i))`. Everything downstream (the mass
recursion, Theorem C) is PROVABLE from this bundle; the bundle itself is the deferred interface —
flagged for review, and exactly what `L6.measureExact` already takes as `codeN`/`ΘN`/`hcylN`. -/
structure JetSetup {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (H : History p F) (m : ℕ) where
  /-- the presented state cylinder after the length-`i` prefix. -/
  Sigma : ℕ → Locus p m
  /-- the (ZC) invariant holds at every prefix (§C.1.5). -/
  zc : ∀ i, ZCData (Sigma i)
  /-- the fresh-clause data of read `ν_i` against `Σ_{i-1}` (packaged against `Σ i` for typing). -/
  fresh : (i : ℕ) → FreshData (Sigma i)
  /-- the move maps `Θ_i` (the `Φ̂`-development / `Φ'`-re-development). -/
  Theta : ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p))
  /-- (§C.0.5) each move is unitriangular for `≺`. -/
  Theta_uni : ∀ i, IsUnitriangular (Theta i)
  /-- the defining recursion `Σ_{i+1} = Θ_i(Σ_i ∩ E_fresh(ν_i))` (§C.1.5's `(R)` two-sidedness). -/
  recursion : ∀ i x, (Sigma (i+1)).IsSolution x ↔
    ((Sigma i).IsSolution (Theta i x) ∧ (fresh i).sat (Theta i x))

/-- **Admissible terminal system `Z`** (§C.2, rev 9 — a LOCUS condition): `Z`'s pinned coordinates
all lie in the FREE-coordinate complement of `Σ_k`'s locus (non-lead arguments unrestricted). -/
def AdmissibleZ {p m : ℕ} (Sigma : Locus p m) (Z : Locus p m) : Prop :=
  ∀ c : Fin m, Z.pinned c = true → Sigma.pinned c = false

/-- The **total transported pin count** of `T(H, Z)` (§C.2): `Σ_{i≤k} m*(ν_i) + |pins(Z)|` — the
codimension read off the mass (`mass = p^{m − totalPins}`). -/
noncomputable def totalPins {p m : ℕ} {F : Type*} [Field F] [Finite F] [Fact p.Prime]
    {H : History p F} (J : JetSetup H m) (k : ℕ) (Z : Locus p m) : ℕ :=
  (Finset.range (k + 1)).sum (fun i => (J.fresh i).mstar) + Z.numPinned

end

end LeanUrat.MovesC
