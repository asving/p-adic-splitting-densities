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
# MovesC/Defs — shared vocabulary for §C, the composition theorem  [ROUND 2]

**Provenance.** `lean/notes/MOVES_2026-07-24.md` §C REV 2 (ACCEPTED 2026-07-26, passes 12+13
CLEAN), derivations `C10B_DERIVATION_2026-07-26.md` / `C15_DERIVATION_2026-07-26.md` (Route B).
ROUND-2 rebuild after the round-1 STOP-THE-LINE audit
`lean/notes/MOVES_LEAN_SEMAUDIT_MOVESC_2026-07-26.md`. Point-by-point answers:
blueprint `MOVESC_LEAN_BLUEPRINT_2026-07-26.md` § ROUND 2. Definitions only — no theorems,
no `sorry`, no axioms.

## What round 2 changes (the audit's five principal failures)

1. **`Node`/`History` now ENFORCE the §C meanings as `Prop` fields**: `Ranch` is literally the
   anchored residual `Σ_k pat(k)·z^k` (stride positions collapse to consecutive powers since
   `e·s + h·t = 1`); `ψ` is monic of degree `g` with `ord_ψ(Ranch) = μ` exactly; species
   constraints (`increment → e·g > 1`, `recentering → e = g = 1`, `ψ = z − center`); the frame
   link `Dwidth = deg Φ`; the residue root `z̄` is a genuine root of `ψ`. `HistoryCoherent` keys
   the transition on the PARENT node's recorded data (`IsStandardLift` of the recorded `ψ, g` +
   `TransitionCoreL` at the recorded `e, h, z̄`; `IsRecenteringCore` at the RECORDED lift — no
   free existentials), adds window containment `s₀'+w' ≤ μ`, the (I-aug) slope chain, the width
   chain `D_{i+1} = e·g·D_i`, the absolute-scale slope law `slope·(e·STR·D) = h`, and the root
   frame `deg Φ₀ = 1`. Later `root` species are excluded by `History.root_iff`.
2. **`Realizable` is the genuine (NA)/(HV)**: (NA) compares the two lines at the BASE index
   `μ_i·D_{i+1}` (the audit's slot/base mismatch fixed); (HV) is the data IDENTITY
   `pattern lead of ν_{i+1} = vtx(ν_i)` with the FULL transported vertex value
   `vtx = z̄^{a−μ·m̂}·((Ranch/ψ^μ) mod ψ)(z̄) ∈ F` — scalar factors included, valued through the
   ambient field (the round-1 `∃ lead, vtxPoly = lead` tautology is gone).
3. **The counting layer is ADDRESS-FREE (Route B / rev 9)**: `FreshData` no longer assigns
   coordinate values. A fresh clause is a `LevelClause` — a constraint carried by a SUPPORT
   (the weight-γ′ level set / strip region), a codimension, and an EXACT-FIBER-COUNT law
   (division-free: `#{supported y | sat y}·p^codim = p^{|support|}`) — exactly what TYP(b)'s
   kernel-coset argument supplies (`TypObject → LevelClause` is a manifest unit). The state is
   loci + masses + the (ZC) invariant; no pin address is data anywhere.
4. **`JetSetup` is re-indexed and LINKED**: `Sigma 0` is the FULL BOX `Σ_{−1}` (field `init`),
   `fresh i` is consumed once, between `Sigma i` and `Sigma (i+1)` (the audit's k = 0
   countermodel is unbuildable); all recursion/invariant fields are bounded by
   `H.nodes.length`; it carries `HistoryCoherent` + `Realizable` (so every consuming theorem
   consumes them), the ≺-SORTED coordinate chart `coordOf` (`Fin`-order ⟺ `CoordPrec`, range
   the `n×N` box — `m = n·N` enforced), the height map `ht`, and the NODE-TIED (ZC) data:
   per-prefix `ZCData` whose floor is the HISTORY's staircase max `floorH` and whose rim
   threshold is the recorded `μ_i·D_{i+1}`; fresh supports are pinned strictly above the floor
   and inside the previous read's factor interior. Freshness-on-`Σ` is now a THEOREM
   (`C2.freshFree`) consuming these links, not an assumed field.
5. **The final statements are Theorem C**: C(b) counts `S(H,Z)` — the `Ψ_H`-image of
   `Σ_k ∩ locus(Z)` under the RECORDED move composite `JetSetup.Psi` — against
   `p^{nN}·∏vol(E_fresh)·vol(Z)` in division-free pin arithmetic; C(a) is the bijective
   carriage with equal mass; `AdmissibleZ` is checked against the FINAL state `Sigma len`.

## The honest boundary (deferred, never approximated)

The EXISTENCE of a `JetSetup` for a real classifier history — the global jet-coordinate
presentation (Fact A down the tower, D.3(e)(ii)), the K1-height reading of `ht`, the graded
piece maps behind each fresh `LevelClause`, and (ZC) persistence — is the unbuilt graded ring
(§B2-DEF gap R4.5 items 1&3). It enters ONLY as the `JetSetup`/`TypObject` hypotheses, exactly
as `L6.measureExact` takes `codeN`/`ΘN`/`hcylN`. Everything in the manifest is provable from
the interface. Flagged for semantic-guardian review throughout.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MovesC

open Polynomial LeanUrat.Moves

/-! ## C0. Base coordinates, the global order ≺, loci, unitriangular moves -/

/-- A **base coordinate** `c = (ℓ, i)`: `c.1 = ℓ` the p-adic level, `c.2 = i` the coefficient
(base) index (§C.0). -/
abbrev Coord : Type := ℕ × ℕ

/-- The **global order** `≺` (§C.0): `(ℓ,i) ≺ (ℓ',i')` iff `ℓ < ℓ'`, or `ℓ = ℓ'` and `i > i'`
(within a level, from the TOP coefficient down — Fact A's elimination order). -/
def CoordPrec (c c' : Coord) : Prop := c.1 < c'.1 ∨ (c.1 = c'.1 ∧ c'.2 < c.2)

/-- A **§C locus**: a unitriangular digit system over `m = n·N` base digits in ≺-SORTED
coordinates (`Fin m`-order = `≺`, witnessed by `JetSetup.coordOf_sorted`), alphabet `ZMod p`
(the BLOCK CONVENTION: an `F`-digit of residue degree `d` is its `d` base equations, each a
factor `p⁻¹`). Reuses the accepted `DigitSystem` (DefsT); its solution set is the cylinder. -/
abbrev Locus (p m : ℕ) : Type := DigitSystem m (ZMod p)

/-- The **mass** of a locus: the number of its solutions among the `p^m` box points
(`= p^{m−numPinned}`, `C0.digitSystemMass`). -/
noncomputable def Locus.mass {p m : ℕ} (D : Locus p m) : ℕ :=
  Nat.card {x : Fin m → ZMod p // D.IsSolution x}

/-- The full box mass `p^{nN} = p^m`. -/
def boxMass (p m : ℕ) : ℕ := p ^ m

/-- **A move map is unitriangular for `≺`** (§C.0.5): `(Θx)_i = x_i + φ_i(x_j : j ≺ i)` — the
diagonal is the identity and the correction is an arbitrary function of ≺-earlier coordinates
(in ≺-sorted `Fin m` coordinates, `j < i`). This is the shape Fact A's division accounting
produces, in both directions. -/
def IsUnitriangular {m : ℕ} {R : Type*} [Add R] (Θ : (Fin m → R) → (Fin m → R)) : Prop :=
  ∀ i : Fin m, ∃ corr : ((j : Fin m) → j < i → R) → R,
    ∀ x, Θ x i = x i + corr (fun j _ => x j)

/-- The **pullback** of a locus `D` by a move `Θ` (`Θ*(E)` of the §C.0.5 pin-transport
corollary): the points whose `Θ`-image solves `D`. `C0.pinTransport` re-presents it as a
digit system with the SAME pinned coordinates (per-coordinate status, rev-9 PIN-WELLDEF). -/
def Locus.pullback {p m : ℕ} (D : Locus p m) (Θ : (Fin m → ZMod p) → (Fin m → ZMod p)) :
    Set (Fin m → ZMod p) := {x | D.IsSolution (Θ x)}

/-! ## C1. Lines, staircases, heights (absolute v_p-scale, §C.1.5 scale declaration) -/

/-- A **read-side line** as an AFFINE function of the base index, absolute v_p-scale (§C DOM):
`at b = intercept − slope·b` with `slope > 0` in genuine instances (lines DESCEND). -/
structure Line where
  intercept : ℚ
  slope : ℚ

/-- Evaluate a line at a base index. -/
def Line.at (L : Line) (b : ℕ) : ℚ := L.intercept - L.slope * (b : ℚ)

/-- The **absolute-height** map `ht(ℓ, i) = ℓ + off(i)` (§C.1.5 scale declaration): a base
coordinate's v_p-height in the current frame. DEFERRED CONTENT (flag): that a `JetSetup`'s `ht`
is the genuine K1-chain weight of the coordinate's basis monomial (`off(i) = Σ_r innerslot·κ_r`,
κ current — LST(i)) is the unbuilt jet-coordinate bridge. -/
abbrev HtMap : Type := Coord → ℚ

/-- The pointwise max of a family of lines over `[0, i]` (§C DOM's floor of RAW lines; the
step-function floor of a history is `History.floorH` below). -/
noncomputable def floorOf (lines : ℕ → Line) (i b : ℕ) : ℚ :=
  Finset.sup' (Finset.range (i + 1)) (by simp) (fun m => (lines m).at b)

/-- **DOM interface** (§C Lemma DOM): the two displayed inputs of the affine induction — the
(I-aug) strict-steepness chain and the vertex-entry endpoint inequality. `HistoryCoherent`
supplies `steeper` for the history's recorded lines (`C3.steeperChain`); `vertex_entry` is
D.8/D.4 geometry (per-instance input). `C2.DOM` derives interior domination; `C2.DOM_floorForm`
the floor form. -/
structure DomData (lines : ℕ → Line) (i : ℕ) (interiorEnd : ℕ) : Prop where
  /-- (I-aug): the current line descends strictly faster than every earlier one. -/
  steeper : ∀ m, m < i → (lines m).slope < (lines i).slope
  /-- vertex-entry (§C DOM(2)): at the interior end the current line dominates every earlier
  one — the endpoint inequality that seeds the affine induction. -/
  vertex_entry : ∀ m, m ≤ i → (lines m).at interiorEnd ≤ (lines i).at interiorEnd

/-! ## C2. The address-free clause layer (Route B, §C.1.5′/rev 9)

A fresh clause never names a pin address. It is carried by a SUPPORT (the strip region or the
weight-γ′ level set), a CODIMENSION, and an exact-fiber-count law — the only three statistics
the counting consumes (C15 S4b). Strip zeros are the `codim = 1`, singleton-support case;
fresh VALUE clauses come from `TypObject` (the graded piece map) via `C1.TYP_toClause`. -/

/-- **A level-set clause** (§C.1.5′ fresh content, address-free): a constraint `sat` that
(i) depends only on the coordinates of its `support` (`dep`), and (ii) cuts EXACTLY
`p^{−codim}` among the support assignments (`count`, division-free on the supported
representatives). The `count` law is self-policing: it forces satisfiability and exactness, so
no vacuous clause instance exists. -/
structure LevelClause (p m : ℕ) where
  /-- the constrained coordinate set: a strip region or a weight-γ′ level set. -/
  support : Finset (Fin m)
  /-- the D.11-nominal codimension this clause cuts (`log_p` of the digit alphabet). -/
  codim : ℕ
  /-- the constraint itself (e.g. `R_δ'(level set) = v`); never a coordinate assignment. -/
  sat : (Fin m → ZMod p) → Prop
  /-- `sat` reads only the support coordinates. -/
  dep : ∀ x y : Fin m → ZMod p, (∀ c ∈ support, x c = y c) → (sat x ↔ sat y)
  /-- EXACT CONDITIONAL VOLUME (TYP(b)'s kernel-coset count, division-free):
  `#{y supported in support | sat y} · p^codim = p^{|support|}`. -/
  count : Nat.card {y : Fin m → ZMod p // sat y ∧ ∀ c ∉ support, y c = 0} * p ^ codim
    = p ^ support.card

/-- **The fresh data of one read** (§C.1(ii)'s species inventory, address-free): the finite
clause list (α-strips/value digits, β-strips, γ-strips left of `j×`, the non-adjacent endpoint —
after BLOCK-CONVENTION expansion), with pairwise-DISJOINT supports (one clause per slot/level
region; §C.1.5′ "pairwise disjoint: the factors multiply"). Freeness on the state cylinder is
NOT a field: it is the theorem `C2.freshFree`, derived from the (ZC) floor exactness and the
above-floor/interior placement links of `JetSetup`. -/
structure FreshData (p m : ℕ) where
  clauses : List (LevelClause p m)
  disj : clauses.Pairwise (fun c₁ c₂ => Disjoint c₁.support c₂.support)

/-- The D.11-nominal fresh base-digit count `m*(ν) = Σ codim`; `vol_nom(E_fresh) = p^{−m*}`. -/
def FreshData.mstar {p m : ℕ} (fd : FreshData p m) : ℕ :=
  (fd.clauses.map LevelClause.codim).sum

/-- The joint membership predicate of the fresh clauses. -/
def FreshData.sat {p m : ℕ} (fd : FreshData p m) (x : Fin m → ZMod p) : Prop :=
  ∀ cl ∈ fd.clauses, cl.sat x

/-- **TYP object** (§C Lemma TYP, the typed degree-γ′ initial form) — BOUNDARY-DEFERRED (needs
the graded piece `gr^Ĉ_{δ'}` and its piece map `R_δ`, the unbuilt graded ring). The fresh value
digit of a slot coefficient is an ADDITIVE map of exactly the weight-γ′ level set `S`, SURJECTIVE
onto the digit alphabet (image = the additive span of the slot images, D.3(e)(i)). Its provable
consequences: equal kernel-coset fibers (`C1.TYP_fiberCount`), hence a `LevelClause` of the
alphabet's codimension (`C1.TYP_toClause`). -/
structure TypObject (p m : ℕ) (S : Finset (Fin m)) (α : Type*) [AddCommGroup α] where
  /-- the piece map `R_δ'` composed with the level-set assignment (graded content; DEFERRED). -/
  φ : (Fin m → ZMod p) →+ α
  /-- `φ` reads only the level-set coordinates `S` (LST/TYP support typing). -/
  dep : ∀ x y : Fin m → ZMod p, (∀ c ∈ S, x c = y c) → φ x = φ y
  /-- surjective onto the alphabet (D.3(e)(i): the emitted value lies in the image). -/
  surj : Function.Surjective φ

/-! ## C3. Read species and nodes (§C.0), with the §C meanings as Prop fields -/

/-- The **species of a read** (§C.0): the ROOT read `ν₀`, an INCREMENT (`e·g > 1`, genuine
stage growth), or a RECENTERING (`e_read = 1`, `g = 1`, degree unchanged, recorded lift). -/
inductive ReadSpecies where
  | root
  | increment
  | recentering
deriving DecidableEq

/-- **A node** `ν` — one read of the OM classifier (§C.0). Frame `σ : Stage p F` (the stage it
reads in), read side `(e, h)` on slots `[s0, s0+wSide]`, descend data `(ψ, g, μ)`, anchor `a`,
the fixed side-pattern digits `pat` (D.3(c): `pat k` at stride position `k` past the anchor —
consecutive `z`-powers, since consecutive lattice slots differ by `e·s + h·t = 1`), the anchored
residual `Ranch`, the read-side `line` (absolute v_p-scale), the residue root `zbar` selected by
the read (D.6/D.7 witness), the recentering `center`/`lift` (D.10), and the frame block width
`Dwidth = deg Φ`. The `Prop` fields make every recorded datum carry its §C meaning (round-1
audit: "many appropriately named fields … not enforced"). -/
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
  zbar : Fˣ
  center : ↥σ.K
  lift : Polynomial ℤ_[p]
  ψ : Polynomial ↥σ.K
  pat : ℕ → ↥σ.K
  Ranch : Polynomial ↥σ.K
  /-- the read side is a genuine polygon side: `e, h ≥ 1`, coprime (lowest terms). -/
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  /-- the descend data are genuine: `g ≥ 1`, `μ ≥ 1` (the read DESCENDS into `ψ`). -/
  hg : 1 ≤ g
  hμ : 1 ≤ μ
  /-- the side width is a whole number of lattice cells: `e ∣ wSide` (`deg R_S = wSide/e`). -/
  hEdvd : e ∣ wSide
  /-- FRAME LINK: `Dwidth` IS the frame's block width `deg Φ` (C.1.0(a)). -/
  hDwidth : Dwidth = σ.Φ.natDegree
  /-- `ψ` is monic of degree `g` (D.3(c)). -/
  hψmonic : ψ.Monic
  hψdeg : ψ.natDegree = g
  /-- ANCHORED RESIDUAL (§C.0, rev 8): `Ranch = Σ_k pat(k)·z^k`, `k ≤ wSide/e` — the pattern
  DETERMINES `Ranch` (pattern-only data; the anchor `a` locates it: absolute position `a + k`). -/
  hRanch : Ranch = ∑ k ∈ Finset.range (wSide / e + 1), Polynomial.C (pat k) * Polynomial.X ^ k
  /-- polygon conventions: the endpoint digits are nonzero (anchor exact, side width exact). -/
  hpat0 : pat 0 ≠ 0
  hpatTop : pat (wSide / e) ≠ 0
  /-- `ord_ψ(Ranch) = μ` EXACTLY (D.3(c): `ψ^μ ∥ Ranch`). -/
  hOrd : OrdPsiPoly ψ Ranch μ
  /-- `zbar` is a genuine root of `ψ` in the ambient field (D.6: `F' = K(z̄)`, `ψ(z̄) = 0`). -/
  hzbarRoot : Polynomial.eval₂ σ.K.subtype ((zbar : Fˣ) : F) ψ = 0
  /-- SPECIES (§C.0): an increment grows the stage, `e·g > 1`. -/
  hspecInc : species = ReadSpecies.increment → 1 < e * g
  /-- SPECIES (§C.0/D.10): a recentering has `e_read = 1` and degree unchanged (`g = 1`). -/
  hspecRec : species = ReadSpecies.recentering → e = 1 ∧ g = 1
  /-- SPECIES (D.10): a recentering consumes the linear factor `ψ = z − c̃` at its recorded
  center, and its residue "root" is the center itself (no field growth). -/
  hspecRecCenter : species = ReadSpecies.recentering →
    ψ = Polynomial.X - Polynomial.C center ∧ ((zbar : Fˣ) : F) = ((center : ↥σ.K) : F)

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The CHILD frame's block width `D_{i+1} = e·g·D_i` (C.1.0(a); recenterings: `e = g = 1`,
unchanged). `HistoryCoherent` pins the successor node's `Dwidth` to this. -/
def Node.childWidth (ν : Node p F) : ℕ := ν.e * ν.g * ν.Dwidth

/-- The D.8 normalization exponent `m̂ = −t·h·g` of the read's frame (the vertex unit
`z̄^{−μm̂}` of D.8's (VERTEX); cf. `LandingCylinderL`'s `T(j·m̂ − a)` factors). -/
def Node.mhat (ν : Node p F) : ℤ := -ν.σ.t * (ν.σ.h : ℤ) * (ν.g : ℤ)

/-- The polynomial factor `(Ranch/ψ^μ) mod ψ` of the transported vertex value — pattern-only
data (§C.0 rev 8: the descend stratum fixes the side-digit tuple, which determines `Ranch`;
D.8's split is a factorization OF this fixed polynomial). Nonzero by `hOrd`
(`C3.vtxPolyNe`). -/
noncomputable def Node.vtxPoly (ν : Node p F) : Polynomial ↥ν.σ.K :=
  (ν.Ranch /ₘ ν.ψ ^ ν.μ) %ₘ ν.ψ

/-- **The transported vertex value** `vtx(ν) := z̄^{a−μ·m̂}·((Ranch/ψ^μ) mod ψ)(z̄) ∈ F`
(§C.0, rev 8) — ALL scalar factors included, valued in the ambient field (which contains
`F_{i+1} = K(z̄)`). An explicit function of node data alone, so (HV) below is a predicate on
the history. [Round-1 audit: `vtxPoly` "omits the scalar factors … valued in the parent
field" — repaired.] -/
noncomputable def Node.vtx (ν : Node p F) : F :=
  (((ν.zbar ^ (ν.a - (ν.μ : ℤ) * ν.mhat)) : Fˣ) : F) *
    Polynomial.eval₂ ν.σ.K.subtype ((ν.zbar : Fˣ) : F) ν.vtxPoly

/-- The node's **line staircase** (§C (ZC-a)/DOM floor form): on its factor interior
`[0, μ·D_{i+1})`, the line's value at the LEFT EDGE of the base index's frame-`(i+1)` block;
`⊥` outside (its clause region contributes no floor beyond the interior). -/
noncomputable def Node.staircase (ν : Node p F) (b : ℕ) : WithBot ℚ :=
  if b < ν.μ * ν.childWidth
    then ((ν.line.at ((b / ν.childWidth) * ν.childWidth) : ℚ) : WithBot ℚ)
    else ⊥

end

/-! ## C4. Histories: coherence (tower provenance) and realizability ((NA)/(HV)) -/

/-- **A read history** `H = (ν₀, …, ν_k)` (§C.0): nonempty, the root read FIRST and ONLY first
(round-1 audit: "a later node may have species root" — excluded by `root_iff`). -/
structure History (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  nodes : List (Node p F)
  nonempty : nodes ≠ []
  root_iff : ∀ (j : ℕ) (hj : j < nodes.length),
    (nodes[j]'hj).species = ReadSpecies.root ↔ j = 0

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The accumulated stretch `STR_i = ∏_{m<i} e_m` of frame `i`'s valuation over `v_p`
(C.1.0(c)/the scale declaration: each transition stretches coefficient weights by its read's
`e`). -/
def History.strFrame (H : History p F) (i : ℕ) : ℕ := ((H.nodes.take i).map Node.e).prod

/-- **The cumulative floor** `F_{i−1}` carried by the prefix of length `i` (§C.1.5 (ZC-a)): the
pointwise max of the first `i` nodes' line staircases over their factor interiors, as a step
function of the base index. `floorH 0 = ⊥` (the root reads against an empty floor:
`E_fresh(ν₀) = E(ν₀)`). -/
noncomputable def History.floorH (H : History p F) (i b : ℕ) : WithBot ℚ :=
  ((H.nodes.take i).map (fun ν => ν.staircase b)).foldr max ⊥

/-- **History coherence** (§C.0 + C.1.0): the recorded frames are linked by the ACCEPTED
§B2-DEF transitions AT THE RECORDED NODE DATA — no free existentials (round-1 audit repairs:
the increment transition consumes the PARENT node's recorded `ψ, g, e, h, zbar` through
`IsStandardLift` + `TransitionCoreL`; the recentering consumes the RECORDED `center`/`lift`
through `IsRecenteringCore`; the root frame is the base frame `deg Φ₀ = 1`; windows are
contained (`s₀'+w' ≤ μ`); the width chain `D_{i+1} = e_i·g_i·D_i` holds; lines steepen along
the history ((I-aug), absolute scale) and obey the absolute-scale slope law
`slope_i·(e_i·STR_i·D_i) = h_i`). -/
def HistoryCoherent (H : History p F) : Prop :=
  (∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).σ.Φ.natDegree = 1) ∧
  (∀ (i : ℕ) (hi : i < H.nodes.length),
    (H.nodes[i]'hi).line.slope *
        (((H.nodes[i]'hi).e : ℚ) * (H.strFrame i : ℚ) * ((H.nodes[i]'hi).Dwidth : ℚ))
      = ((H.nodes[i]'hi).h : ℚ)) ∧
  ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
    ((H.nodes[i]'(by omega)).species = ReadSpecies.recentering →
      IsRecenteringCore (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi).σ
        (H.nodes[i]'(by omega)).center (H.nodes[i]'(by omega)).lift) ∧
    ((H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering →
      IsStandardLift (H.nodes[i]'(by omega)).σ (H.nodes[i]'(by omega)).ψ
          (H.nodes[i]'(by omega)).g (H.nodes[i+1]'hi).σ.Φ ∧
        TransitionCoreL (H.nodes[i]'(by omega)).σ (H.nodes[i+1]'hi).σ
          (H.nodes[i+1]'hi).σ.Φ (H.nodes[i]'(by omega)).e (H.nodes[i]'(by omega)).h
          (H.nodes[i]'(by omega)).zbar) ∧
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide ≤ (H.nodes[i]'(by omega)).μ) ∧
    ((H.nodes[i+1]'hi).Dwidth = (H.nodes[i]'(by omega)).childWidth) ∧
    ((H.nodes[i]'(by omega)).line.slope < (H.nodes[i+1]'hi).line.slope)

/-- **Realizability** (§C.0, the two data-side conditions C.1(ii) isolates — equations of NO
`E`; a history failing either has EMPTY joint stratum and Theorem C's quantifier excludes it):
* **(NA)** at a NON-ADJACENT read (`s₀'+w' < μ_i`): the pinned old vertex lies STRICTLY ABOVE
  the extended new line, compared at the vertex's BASE index `μ_i·D_{i+1}` (round-1 audit:
  the slot/base-index mismatch — repaired via `childWidth`);
* **(HV)** at an ADJACENT read (`s₀'+w' = μ_i`): the pattern LEAD of `ν_{i+1}` (its endpoint
  digit `pat(wSide/e)`, the vertex digit) EQUALS the transported vertex value `vtx(ν_i)` — a
  genuine identity of node data in `F` (round-1 audit: the `∃ lead` tautology — repaired). -/
def Realizable (H : History p F) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide < (H.nodes[i]'(by omega)).μ →
      (H.nodes[i+1]'hi).line.at ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)
        < (H.nodes[i]'(by omega)).line.at
            ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)) ∧
    ((H.nodes[i+1]'hi).s0 + (H.nodes[i+1]'hi).wSide = (H.nodes[i]'(by omega)).μ →
      (((H.nodes[i+1]'hi).pat ((H.nodes[i+1]'hi).wSide / (H.nodes[i+1]'hi).e) :
          ↥(H.nodes[i+1]'hi).σ.K) : F) = (H.nodes[i]'(by omega)).vtx)

end

/-! ## C5. The (ZC) invariant and the presented history (jet setup) -/

/-- **The (ZC) invariant on a state cylinder** (§C.1.5), against a coordinate chart `coordOf`,
a height map `ht`, the cumulative floor `floor` (a step function of the base index), and the
rim threshold `rimIdx = μ_i·D_{i+1}` (a BASE-INDEX region — round-1 audit: a rim condition "is
not a suffix of the global order"; the `rimStart : Fin m` encoding and its `rimStart := 0`
vacuity are gone, and `m = 0` is unproblematic):
* **(ZC-a) EXACT DOWNSET** — at interior base indices (`< rimIdx`), a coordinate is pinned IFF
  its height is at most the floor (BOTH directions: the round-1 `pin_dichotomy` allowed
  under-pinning);
* **(ZC-a) LITERAL ZEROS** — interior pins solve to the constant `0` (the zero downset
  `Z(F_i)`);
* **(ZC-b) LEADS AT RIM** — every other pin is at a rim base index; its `solve` is
  unrestricted (`DIG_i`: unitriangular, non-lead arguments free). [The finer §C statement that
  each `DIG_i` equation solves for one rim-block LEVEL SET is presentation content of the
  deferred jet bridge; the counting consumes rim-ness of the leads only — C15 S4c.] -/
structure ZCData {p m : ℕ} (D : Locus p m) (coordOf : Fin m → Coord) (ht : HtMap)
    (floor : ℕ → WithBot ℚ) (rimIdx : ℕ) : Prop where
  downset_exact : ∀ j : Fin m, (coordOf j).2 < rimIdx →
    (D.pinned j = true ↔ ((ht (coordOf j) : ℚ) : WithBot ℚ) ≤ floor (coordOf j).2)
  interior_zero : ∀ j : Fin m, (coordOf j).2 < rimIdx → D.pinned j = true →
    ∀ f : (j' : Fin m) → j' < j → ZMod p, D.solve j f = 0

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **The jet presentation of a history** — the BOUNDARY-DEFERRED bridge from the accepted
tower to digit systems (§C.2's `Ψ_H`; the global jet-coordinate system D.3(e)(ii) down the
whole tower, at a fixed level cutoff `N ≥ N(H, Z)` — largeness of `N` is a condition on the
EXISTENCE of the presentation, recorded here by `hm`/`coordOf` tying the box to `n·N`).
Indexing (round-1 audit's off-by-one repaired): `Sigma 0` is `Σ_{−1}` = the FULL BOX (`init`);
read `ν_i` is consumed ONCE, between `Sigma i` and `Sigma (i+1)` (`recursion`, `i < len`);
the final state is `Sigma H.nodes.length`. Every field about reads is bounded by
`H.nodes.length`; values beyond the bound are junk and no theorem consumes them.
The presentation is LINKED to the history (round-1 audit: "unrelated to the nodes of `H`"):
it contains `HistoryCoherent`/`Realizable`; the (ZC) floor is the HISTORY's `floorH`; the rim
threshold is the recorded `μ_i·childWidth`; fresh supports sit strictly above the floor
(`fresh_above`, LST(iii)'s selection) and inside the previous read's factor interior
(`fresh_interior`, C.1's rim bullet). FLAGGED for semantic review: the existence of this
bundle for a real history is the unbuilt graded ring (R4.5 items 1&3). -/
structure JetSetup (H : History p F) (n N m : ℕ) where
  /-- the box is the `n·N` coefficient box (BLOCK CONVENTION, base digits). -/
  hm : m = n * N
  /-- the ≺-SORTED coordinate chart: `Fin m`-order IS the global order `≺`. -/
  coordOf : Fin m → Coord
  coordOf_sorted : ∀ j j' : Fin m, j < j' ↔ CoordPrec (coordOf j) (coordOf j')
  /-- the chart lands in the box: levels `< N`, base indices `< n`. -/
  coordOf_lt : ∀ j : Fin m, (coordOf j).1 < N ∧ (coordOf j).2 < n
  /-- the absolute-height map (DEFERRED: = the K1-chain weight, LST(i)). -/
  ht : HtMap
  /-- the presented history is coherent (consumed by every downstream theorem). -/
  coherent : HistoryCoherent H
  /-- and realizable ((NA)/(HV); §C's quantifier ranges over realizable histories only). -/
  realizable : Realizable H
  /-- the state cylinder before read `i`: `Sigma i = Σ_{i−1}` in frame-`i` coordinates. -/
  Sigma : ℕ → Locus p m
  /-- INITIALIZATION: `Σ_{−1}` is the full box — nothing is pinned before the root read. -/
  init : ∀ c : Fin m, (Sigma 0).pinned c = false
  /-- the fresh clause data of read `ν_i` (§C.1(ii)'s species inventory, address-free). -/
  fresh : ℕ → FreshData p m
  /-- the move maps `Θ_i` (the `Φ̂`-development / `Φ'`-re-development, child-to-parent
  coordinate reading). -/
  Theta : ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p))
  /-- (§C.0.5) each move is unitriangular for `≺` (Fact A's division accounting; DEFERRED). -/
  Theta_uni : ∀ i : ℕ, IsUnitriangular (Theta i)
  /-- the defining recursion `Σ_i = Θ_i(Σ_{i−1} ∩ E_fresh(ν_i))` (D.8/D.10 two-sidedness with
  C.1(i)'s inherited-implication absorbed — the stratum meets `Σ_{i−1}` in its FRESH content;
  this absorption is part of the deferred presentation, flagged). -/
  recursion : ∀ i : ℕ, i < H.nodes.length → ∀ x : Fin m → ZMod p,
    (Sigma (i+1)).IsSolution x ↔
      ((Sigma i).IsSolution (Theta i x) ∧ (fresh i).sat (Theta i x))
  /-- the (ZC) invariant at every prefix, at the HISTORY's floor and the RECORDED rim
  threshold (§C.1.5; node-tied — round-1 audit repair). -/
  zc : ∀ (i : ℕ) (hi : i < H.nodes.length),
    ZCData (Sigma (i+1)) coordOf ht (H.floorH (i+1))
      ((H.nodes[i]'hi).μ * (H.nodes[i]'hi).childWidth)
  /-- fresh content sits STRICTLY ABOVE the cumulative floor (LST(iii) selection /
  §C.1(ii)). -/
  fresh_above : ∀ i : ℕ, i < H.nodes.length → ∀ cl ∈ (fresh i).clauses, ∀ c ∈ cl.support,
    H.floorH i (coordOf c).2 < ((ht (coordOf c) : ℚ) : WithBot ℚ)
  /-- fresh content is FACTOR-INTERIOR: no fresh clause ever constrains a rim coordinate of
  the previous read (C.1's rim bullet / rim domination; base indices `< μ_i·D_{i+1}`). -/
  fresh_interior : ∀ (i : ℕ) (hi : i + 1 < H.nodes.length),
    ∀ cl ∈ (fresh (i+1)).clauses, ∀ c ∈ cl.support,
      (coordOf c).2 < (H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth

/-- The partial move composite `seg i k = Θ_i ∘ Θ_{i+1} ∘ … ∘ Θ_{k−1}` (frame-`k` coordinates
down to frame-`i` coordinates); `seg 0 k` is `Ψ_H^{−1}` up to prefix `k`. -/
def JetSetup.seg {H : History p F} {n N m : ℕ} (J : JetSetup H n N m) (i : ℕ) :
    ℕ → ((Fin m → ZMod p) → (Fin m → ZMod p))
  | 0 => id
  | k + 1 => if i ≤ k then J.seg i k ∘ J.Theta k else id

/-- **The recorded move composite** `Ψ_H^{−1}`-side: `Psi k = Θ_0 ∘ … ∘ Θ_{k−1}` carries the
final-frame presentation back to `f`-coordinates (§C.2: `S(H,Z) = Ψ_H^{−1}(Σ_k ∩ locus Z)`,
stated in `C6.thmC_a/b` about THIS composite — round-1 audit: "no history move composition"). -/
def JetSetup.Psi {H : History p F} {n N m : ℕ} (J : JetSetup H n N m) (k : ℕ) :
    (Fin m → ZMod p) → (Fin m → ZMod p) := J.seg 0 k

/-- **Admissible terminal system `Z`** (§C.2, rev 9 — a LOCUS condition): `Z` solves only for
coordinates FREE on the FINAL state cylinder (round-1 audit: admissibility was checked against
the wrong prefix in the `k = 0` countermodel; consumers instantiate `Sigma := J.Sigma
H.nodes.length`). -/
def AdmissibleZ {p m : ℕ} (Sigma Z : Locus p m) : Prop :=
  ∀ c : Fin m, Z.pinned c = true → Sigma.pinned c = false

/-- The **total pin count** of `T(H, Z)`: `Σ_{i<len} m*(ν_i) + |pins(Z)|` — the codimension of
the joint locus, read off the mass (PIN-WELLDEF; division-free form `mass·p^K = p^{nN}`). -/
def totalPins {H : History p F} {n N m : ℕ} (J : JetSetup H n N m)
    (Z : Locus p m) : ℕ :=
  (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar) + Z.numPinned

end

end LeanUrat.MovesC
