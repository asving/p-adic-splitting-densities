/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesC.Defs

/-!
# MovesD/Defs — shared vocabulary for §D4-R (the per-shape-prefix mass law)

E-phase transcription of `lean/notes/MOVESD_LEAN_BLUEPRINT_2026-07-28.md` (REV 9, the seam
split), §3 in the §3.0 NORMATIVE declaration order (groups (1)–(5), `strS` hoisted into
group (1) per REV 8 / Codex#6 g.4). This corpus CONSUMES MovesC: `History`/`Node`/
`JetSetup`/`SHZ`/`Realizable`/`HistoryCoherent` and (in the units) `C6_thmC_b`.
Definitions only — no `sorry`, no axioms; the only proofs are the mechanical constructor
obligations of `History.snoc` and the blueprint-addendum lemma `Shape.mbar_pos` (powering
`encIdx`'s totality).

SEAM DECLARATION [REV 9, §2.5 W4-SYNC — NOT BUILT AT E-PHASE]:
* `TreeModel`'s semantic layer (`eligible`/`child_iff` — W4-1) is ABSENT below: only the
  STRUCTURAL counting fields (mem/child/root_mem/mem_single/mem_snoc/mem_realizable) are
  declared, per the §2.5 core-side declaration ("the mass laws never touch `eligible`,
  `vdict`, `Cell`, or `D4R_CYL`"). [W4-SYNC delta 10, 2026-07-29]: the §2.5 W4-1 row now
  carries the (c2) per-track COVERING clause (MovesT REV-7 ruling 1; MOVES 7112–7119),
  frozen at the structural typed form `W41ChildCover` — re-keys as `MovesT.ChildCover`.
* `VerdictModel` (W4-2 — the ENTIRE structure) is NOT DECLARED; its rev-8 typed form is
  frozen in the blueprint's §2.5 contract as the negotiating position (rev-8 `cell_local`
  WITHDRAWN per Codex#7 c.6). It re-keys and builds in wave 4 with MovesT.
* D15 (W4-3, the D4R_CYL consumer side) has NO unit file; the pinned Props `D4R_CYL` and
  `ClassFiberWelldef` are declared below in their §3.4 typed forms — consumed by NOTHING
  in the E-phase core.
* NP-ID (W4-4): TYPED at `NPIDPin` (unit NPv_npid, ratification repair D5 2026-07-28) —
  the ledger pin is now a Lean object; `D4R4_all_noteRange` restates D4R4_all on L12's own
  range through it. The pin's DISCHARGE (NPband = max-η N(η,⊤)) remains wave-4/HC-2.
* POL-PIN (W4-5, ratification repair D2 2026-07-28): the note's ONE lift rule — the (S6b)
  OFFSET-P-LIFT realizer (note 4646–4651) — now has the typed consumer-side pin
  `OffsetPPin` (unit PolPin). Its `Realizes` field is the seam residue (weight/residue
  reduction = §B2-DEF/HC-1 vocabulary); the here-statable laws (L1 totality + genuine
  realizers) are typed. Consumers: NO existing theorem changed; `CD_canonical` (PolPin)
  is the pinned specialization.

E-phase elaboration deviations are catalogued in `MANIFEST.json` ("deviations").
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD

open Polynomial LeanUrat.Moves LeanUrat.MovesC

/-! ## §3.0 group (1) — Box, top locus, shape reads, the wf certificate, the subtype -/

/-- The level-`N` coefficient box (`m = n·N` frame-0 base digits). -/
abbrev Box (p m : ℕ) : Type := Fin m → ZMod p

/-- Z = ⊤ (§D4-R L6: "no constraint, vol(⊤) = 1"). -/
def topLocus (p m : ℕ) : Locus p m := { pinned := fun _ => false, solve := fun _ _ => 0 }

/-- One read of a shape-prefix — §D4-R L3 rev 9 retained fields: species, (e,h,g,μ,a),
side data (s0, wSide, Dwidth), the height PAIR (h, u*) [pass-10 F1 CRITICAL], γ, pool
degree w (Q_r = p^w, w ≥ 1), and `monicTop` — whether the side's top slot is the box's
monic lead (§0.5; the stride-position/slot-set datum of L3, reduced to its one degree of
freedom: all other positions always carry tuple digits). Values and lifts forgotten.
[REV 7, Codex#5 c.1 — certificate completion, per-read part]: `hh`/`hcop` are Node's
"genuine polygon side: e, h ≥ 1, coprime (lowest terms)"; `hspecInc`/`hspecRec` the §C.0
species laws. [REV 4, Codex#2 f.1 partial concession]: `hmonicRoot` — the monic lead
exists only at the ROOT read. -/
structure ShapeRead where
  species : ReadSpecies
  e : ℕ
  h : ℕ
  g : ℕ
  μ : ℕ
  a : ℤ
  s0 : ℕ
  wSide : ℕ
  Dwidth : ℕ
  ustar : ℚ
  gam : ℤ
  w : ℕ
  monicTop : Bool
  he : 1 ≤ e
  hg : 1 ≤ g
  hμ : 1 ≤ μ
  hw : 1 ≤ w
  hDw : 1 ≤ Dwidth
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  hspecInc : species = ReadSpecies.increment → 1 < e * g
  hspecRec : species = ReadSpecies.recentering → e = 1 ∧ g = 1
  hmonicRoot : monicTop = true → species = ReadSpecies.root

/-- `ℓ_r = deg R_anch,r` — the side's normalized horizontal length. -/
def ShapeRead.len (R : ShapeRead) : ℕ := R.wSide / R.e

/-- `d_r` (the tuple size). [REV 5, reconciliation (4)]: the Boolean is EXACT because at
most ONE slot per read is off-box (the degree-n monic slot, root only), and `monicTop` is
SEMANTICALLY TIED by `ShapePrefix.MonicTie` (a `ShapeWF` component since REV 6). -/
def ShapeRead.d (R : ShapeRead) : ℕ := R.len + (if R.monicTop then 0 else 1)

/-- `m̄_r = ⌊ℓ_r/(g_r·μ_r)⌋` (Nat division IS the floor). -/
def ShapeRead.mbar (R : ShapeRead) : ℕ := R.len / (R.g * R.μ)

/-- The shape-side child frame width `e·g·Dwidth` (C.1.0(a)'s width chain). -/
def ShapeRead.childWidthS (R : ShapeRead) : ℕ := R.e * R.g * R.Dwidth

/-- A shape-prefix: the retained read list. The note's universe is the SUBTYPE `Shape n`
below (REV 6 — the domain ruling); raw `ShapePrefix` is encoding material only. -/
structure ShapePrefix where
  reads : List ShapeRead

/-- `W(P̂) = Σ_r w_r·d_r` — the pool-weighted digit count (L11's exponent). -/
def ShapePrefix.W (P : ShapePrefix) : ℕ := (P.reads.map (fun R => R.w * R.d)).sum

/-- `M(P̂) = ∏_r m̄_r` — the factor-selection bound (L11). -/
def ShapePrefix.Mfac (P : ShapePrefix) : ℕ := (P.reads.map ShapeRead.mbar).prod

/-- Shape wellformedness over the degree-n box — "deg R_anch,r ≤ n ALWAYS", shape-side.
A THEOREM over the subtype (unit W1′). -/
def ShapePrefix.Wellformed (P : ShapePrefix) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (hr : r < P.reads.length), (P.reads[r]'hr).len ≤ n

/-- [REV 8 HOIST, Codex#6 g.4 — `ShapeWF.gamTie` consumes it] the accumulated shape
stretch `STR_i = ∏_{m<i} e_m` (L9's "SHAPE data"). -/
def ShapePrefix.strS (P : ShapePrefix) (i : ℕ) : ℕ := ((P.reads.take i).map ShapeRead.e).prod

/-- [REV 5, reconciliation (4)] **The monic-slot tie**: `monicTop` is true EXACTLY at the
root read whose side's top slot is the box's degree-n coefficient position (root frame
width 1: slot index = base index). Both directions: faking monicTop (omitting a genuine
digit, shrinking W) AND hiding it (inflating W past the box) violate the tie. A `ShapeWF`
COMPONENT since REV 6 — violating shapes are NOT SHAPES. -/
def ShapePrefix.MonicTie (P : ShapePrefix) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (hr : r < P.reads.length),
    (P.reads[r]'hr).monicTop = true ↔ (r = 0 ∧ (P.reads[r]'hr).s0 + (P.reads[r]'hr).wSide = n)

/-- [REV 7] THE canonical Bézout coefficient `t ∈ [0, e)` of a read side (rev 14's `t^B`;
MovesC `hbezCanon`: unique in the window, a FUNCTION of (e, h) — mirrored shape-side; junk
when gcd ≠ 1, excluded by `ShapeRead.hcop`). At e = 1: t = 0 (D.5's (P2) base — the
γ-blind case that forced u*'s retention, L3 rev 9). -/
def bezT (e h : ℕ) : ℤ := (((Nat.xgcd e h).2 % (e : ℤ)) + (e : ℤ)) % (e : ℤ)

/-- [REV 6 — THE DOMAIN-SUBTYPE RULING] **The shape wf-certificate**: the
L3-dictionary-image laws expressible on shape data — what a note shape-prefix IS. A
malformed encoding is not a valid shape-prefix (Codex#4 f.1, now the design). The
certificate variant is chosen over the literal ∃-Node-chain image to stay non-circular
and checkable; `ShapeWF_of_matches` (unit SW1) proves every matched coherent in-box
history's shape carries it — nothing of the note's universe is lost.
[REV 8, Codex#6 c.1]: `w0`/`wchain` — the RESIDUE-DEGREE laws (w₀ = 1; w_{r+1} = w_r·g_r).
[REV 7, Codex#5 c.1]: `gamTie` (the γ-tie at the chain stretch — mirrors
`HistoryCoherent`'s clause verbatim; [REV 9, Codex#7 c.1 PUSHBACK]: the STR factor IS
MovesC round-4 finding 11 role (ii), stage scale = STR × absolute, C.1.0(c); flagged for
the ratification pass — the gate has strS = 1 throughout. RATIFICATION RULING 2026-07-28:
finding D1 OVERRULED — the note's L3 display "γ_r := e_r·u*_r + j*_r·h_r" (note 4707) is at
STAGE scale (§C C.0 marks γ_i "(augmented scale)", note 3461) while `ustar` is recorded
ABSOLUTE (MovesC Node, C.1.0(c) Scale declaration, note 3635–3645: stage = STR × absolute),
so the STR factor here is the scale conversion, not a deviation; the machine-checked
coherence seal is unit SW2_scaleCoherence) and `anchorTie` (Node.hAnchor
at THE canonical Bézout coefficient `bezT`, D.3(c)'s stride anchor). -/
structure ShapeWF (n : ℕ) (P : ShapePrefix) : Prop where
  species_iff : ∀ (r : ℕ) (hr : r < P.reads.length),
    (P.reads[r]'hr).species = ReadSpecies.root ↔ r = 0
  root_box : ∀ h0 : 0 < P.reads.length, (P.reads[0]'h0).s0 + (P.reads[0]'h0).wSide ≤ n
  window : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
    (P.reads[r+1]'hr).s0 + (P.reads[r+1]'hr).wSide ≤ (P.reads[r]'(by omega)).μ
  gmu : ∀ (r : ℕ) (hr : r < P.reads.length),
    (P.reads[r]'hr).g * (P.reads[r]'hr).μ ≤ (P.reads[r]'hr).len
  edvd : ∀ (r : ℕ) (hr : r < P.reads.length), (P.reads[r]'hr).e ∣ (P.reads[r]'hr).wSide
  dchain0 : ∀ h0 : 0 < P.reads.length, (P.reads[0]'h0).Dwidth = 1
  dchain : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
    (P.reads[r+1]'hr).Dwidth = (P.reads[r]'(by omega)).childWidthS
  monic : P.MonicTie n
  w0 : ∀ h0 : 0 < P.reads.length, (P.reads[0]'h0).w = 1
  wchain : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
    (P.reads[r+1]'hr).w = (P.reads[r]'(by omega)).w * (P.reads[r]'(by omega)).g
  gamTie : ∀ (r : ℕ) (hr : r < P.reads.length),
    (((P.reads[r]'hr).gam : ℤ) : ℚ)
      = ((P.reads[r]'hr).e : ℚ) * ((P.strS r : ℚ) * (P.reads[r]'hr).ustar)
        + ((((P.reads[r]'hr).s0 + (P.reads[r]'hr).wSide) : ℕ) : ℚ) * ((P.reads[r]'hr).h : ℚ)
  anchorTie : ∀ (r : ℕ) (hr : r < P.reads.length),
    ((P.reads[r]'hr).e : ℤ) * (P.reads[r]'hr).a
      = ((P.reads[r]'hr).s0 : ℤ) - bezT (P.reads[r]'hr).e (P.reads[r]'hr).h * (P.reads[r]'hr).gam

/-- **THE NOTE'S SHAPE UNIVERSE, BY TYPE** [REV 6]: every shape-quantified unit binds
`{P : Shape p F n}` (coercion `↑P : ShapePrefix`; certificate `P.2`) — the mass laws hold
UNCONDITIONALLY over exactly the note's shapes ("always" verbatim); junk data is not in
the domain of quantification. -/
abbrev Shape (n : ℕ) : Type := {P : ShapePrefix // ShapeWF n P}

/-! ## §3.0 group (2) — the remaining shape replicas (§3.3: the ledger exponent A, Nshape,
the N-free A′, NPband) -/

/-- The shape-side read line: slope `h/(e·STR·D)`, intercept pinned through `(j*, u*)`
(L9 rev 9 — u* enters HERE, through the intercept). Junk `⟨0,0⟩` beyond the prefix. -/
noncomputable def ShapePrefix.lineS (P : ShapePrefix) (r : ℕ) : Line :=
  (P.reads[r]?).elim ⟨0, 0⟩ (fun R =>
    let sl : ℚ := (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ) * (R.Dwidth : ℚ))
    ⟨R.ustar + sl * (((R.s0 + R.wSide) * R.Dwidth : ℕ) : ℚ), sl⟩)

/-- Level-`r` weight `κ_r = h_r/(e_r·STR_r)` — shape data (L9). -/
noncomputable def ShapePrefix.kappaS (P : ShapePrefix) (r : ℕ) : ℚ :=
  (P.reads[r]?).elim 0 (fun R => (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ)))

/-- Level-`r` inner slot of base index `b`, on the retained width chain (L9). -/
def ShapePrefix.innerslotS (P : ShapePrefix) (r b : ℕ) : ℕ :=
  (P.reads[r]?).elim 0 (fun R => (b % R.childWidthS) / R.Dwidth)

/-- The K1-chain height, shape-side (mirrors `History.htH`). -/
noncomputable def ShapePrefix.htS (P : ShapePrefix) (i : ℕ) (c : Coord) : ℚ :=
  (c.1 : ℚ) + (Finset.range i).sum (fun r => (P.innerslotS r c.2 : ℚ) * P.kappaS r)

/-- The (ZC-a) line staircase, shape-side (mirrors `Node.staircase`). -/
noncomputable def ShapeRead.staircaseS (R : ShapeRead) (L : Line) (b : ℕ) : WithBot ℚ :=
  if b < R.μ * R.childWidthS then ((L.at ((b / R.childWidthS) * R.childWidthS) : ℚ) : WithBot ℚ) else ⊥

/-- The cumulative floor, shape-side (mirrors `History.floorH`). -/
noncomputable def ShapePrefix.floorS (P : ShapePrefix) (i b : ℕ) : WithBot ℚ :=
  ((List.range i).map (fun r => (P.reads[r]?).elim ⊥ (fun R => R.staircaseS (P.lineS r) b))).foldr max ⊥

/-- Read `i`'s rim threshold, shape-side (mirrors `History.prevRim`). -/
def ShapePrefix.prevRimS (P : ShapePrefix) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => (P.reads[i]?).elim n (fun R => R.μ * R.childWidthS)

/-- The fresh band, shape-side (mirrors `inFreshBand`, fine-slot boundary — MovesC ROUND 6). -/
noncomputable def ShapePrefix.bandS (P : ShapePrefix) (n r : ℕ) (c : Coord) : Prop :=
  c.2 < P.prevRimS n r ∧ P.floorS r c.2 < ((P.htS r c : ℚ) : WithBot ℚ) ∧
  (P.reads[r]?).elim False (fun R => P.htS r c ≤ (P.lineS r).at ((c.2 / R.Dwidth) * R.Dwidth))

open Classical in
/-- The ledger exponent `A(P̂, n, N)` — the per-read fresh-band grid count (L9/D9). -/
noncomputable def ShapePrefix.A (P : ShapePrefix) (n N : ℕ) : ℕ :=
  (Finset.range P.reads.length).sum (fun r =>
    ((Finset.range N ×ˢ Finset.range n).filter (fun c => P.bandS n r c)).card)

/-- The a-priori SHAPE bound on the band's levels (L12: "an a priori shape bound on N(P̂)
is available"): 1 + max over reads of ⌈intercept of lineS⌉₊. -/
noncomputable def ShapePrefix.Nshape (P : ShapePrefix) : ℕ :=
  1 + ((List.range P.reads.length).map (fun r => ⌈(P.lineS r).intercept⌉.toNat)).foldr max 0

/-- **The N-FREE ledger exponent A′(P̂, n)** (finding 5): A at the stabilization level. -/
noncomputable def ShapePrefix.A' (P : ShapePrefix) (n : ℕ) : ℕ := P.A n (P.Nshape)

open Classical in
/-- The GEOMETRIC threshold: 1 + the largest constrained (band) level. -/
noncomputable def ShapePrefix.NPband (P : ShapePrefix) (n : ℕ) : ℕ :=
  1 + ((Finset.range P.Nshape ×ˢ Finset.range n).filter
        (fun c => ∃ r < P.reads.length, P.bandS n r c)).sup (fun c => c.1)

/-- The named net exponent `A_net(P̂) := A(P̂) − W(P̂)` (Corollary D4R.2). -/
noncomputable def ShapePrefix.Anet (P : ShapePrefix) (n : ℕ) : ℤ := (P.A' n : ℤ) - (P.W : ℤ)

/-! ## §3.0 group (3) — pool, enumeration, transported eligibility, rank (§3.4) -/

/-- The pool: THE order-p^w root set in F (units E1–E3 identify it with every matched
frame field's image). -/
def pool (p w : ℕ) (F : Type*) [Field F] : Set F := {x : F | x ^ (p ^ w) = x}

/-- A classically-fixed enumeration of F — the shared "fixed residue bases" order
(D.3(e)) for the rank; one choice for the whole corpus. -/
noncomputable def fieldEnum (F : Type*) [Finite F] : F ≃ Fin (Nat.card F) :=
  Finite.equivFin F

/-- Coefficient-lex strict order through the fixed enumeration (the D.3(e)-order
substitute; the encoding bound is order-invariant — Fable#2 §3.8). [E-PHASE ELABORATION:
the convention is highest-differing-coefficient-dominant — see MANIFEST deviations.] -/
def lexLt {F : Type*} [Field F] [Finite F] (en : F ≃ Fin (Nat.card F)) (q q' : Polynomial F) : Prop :=
  ∃ k : ℕ, en (q.coeff k) < en (q'.coeff k) ∧ ∀ j : ℕ, k < j → q.coeff j = q'.coeff j

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- [REV 4, Fable#2 G1 ≈ Codex#2 f.3] `R_anch`, read on F-coefficient images (through the
frame field's inclusion). -/
noncomputable def RanchImage (ν : Node p F) : Polynomial F := ν.Ranch.map ν.σ.K.subtype

/-- `ψ`, read on F-coefficient images. -/
noncomputable def ψImage (ν : Node p F) : Polynomial F := ν.ψ.map ν.σ.K.subtype

end

open Classical in
/-- `pool p w F` as a subfield (Frobenius-power fixed points — closed under the field
operations in char p). [E-PHASE DEVIATION, see MANIFEST: at this signature the pool need
not be additively closed (that needs char F = p, not available on the raw binders), so the
blueprint's anonymous-constructor display is elaborated as THE subfield whose carrier is
the pool WHENEVER ONE EXISTS (every matched use site — E3's identification supplies it),
and junk `⊥` otherwise. On C-carrying territory the two readings coincide exactly. -/
noncomputable def poolSubfield (p w : ℕ) (F : Type*) [Field F] : Subfield F :=
  if h : ∃ S : Subfield F, (S : Set F) = pool p w F then h.choose else ⊥

/-- **The transported eligibility predicate** (the note's "{ψ monic irreducible :
deg ψ = g_r, ord_ψ R_anch = μ_r}", read on F-images): q is monic of degree g with
ord_q(Rq) = μ AND q is the image of an IRREDUCIBLE polynomial over the POOL SUBFIELD
(equivalently: coefficients in the pool + irreducible over it — never over F). -/
def EligibleImage (p w g μ : ℕ) {F : Type*} [Field F] (Rq q : Polynomial F) : Prop :=
  q.Monic ∧ q.natDegree = g ∧ OrdPsiPoly q Rq μ ∧
  ∃ q₀ : Polynomial ↥(poolSubfield p w F),
    Irreducible q₀ ∧ q₀.map (poolSubfield p w F).subtype = q

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The rank of ψ among the eligible same-shape factors of Ranch (L11's s_r), via the
shared enumeration — DEFINED, not data. Stated on F-coefficient images so classes compare
across members (units E6–E8 give rank < m̄ and rank-injectivity). -/
noncomputable def selRank (w : ℕ) (ν : Node p F) : ℕ :=
  Nat.card {q : {q : Polynomial F // EligibleImage p w ν.g ν.μ (RanchImage ν) q} //
    lexLt (fieldEnum F) q.1 (ψImage ν)}

/-- A node's side digit at pattern position k, in the AMBIENT field. -/
def _root_.LeanUrat.MovesC.Node.sideDigit (ν : Node p F) (k : ℕ) : F :=
  ((ν.pat k : ↥ν.σ.K) : F)

end

/-! ## §3.0 group (4) — Matches, the canonical policy, PrefSet, η-classes, the family -/

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- `R.Matches ν` — field equalities on the retained data (heights INCLUDED), the pool
card, and the ONE scoped monic tie (§0.5): `monicTop → sideDigit(ℓ_r) = 1`. -/
def ShapeRead.Matches (R : ShapeRead) (ν : Node p F) : Prop :=
  ν.species = R.species ∧ ν.e = R.e ∧ ν.h = R.h ∧ ν.g = R.g ∧ ν.μ = R.μ ∧
  ν.a = R.a ∧ ν.s0 = R.s0 ∧ ν.wSide = R.wSide ∧ ν.Dwidth = R.Dwidth ∧
  ν.ustar = R.ustar ∧ ν.gam = R.gam ∧ Nat.card ↥ν.σ.K = p ^ R.w ∧
  (R.monicTop = true → ν.sideDigit R.len = 1)

/-- Shape-match of a whole history (lengths equal, reads match nodewise). -/
def ShapePrefix.MatchesHist (P : ShapePrefix) (H : History p F) : Prop :=
  ∃ hlen : H.nodes.length = P.reads.length,
    ∀ (r : ℕ) (hr : r < H.nodes.length), (P.reads[r]'(hlen ▸ hr)).Matches (H.nodes[r]'hr)

end

/-- **The canonical-lift policy** [REV 3, finding 2]: a DETERMINISTIC per-node lift rule —
L1's defining law "the digits t_k are FUNCTIONS of the node data … the policy is
deterministic", as structure. `liftOf` reads the node MINUS its lift (`blind`), so a
policy can never encode "no history is canonical": `IsCanon pol` is per-node,
automatically prefix-monotone and total on lift-assignments — the lawless
`Canon := fun _ => False` is NOT expressible as any `IsCanon pol`. WHICH policy (the
(S6b) offset-P formula) is the open parameter, pinned by §B2-DEF/HC-1 (POL-PIN, §2). -/
structure CanonPolicy (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  liftOf : Node p F → Polynomial ℤ_[p]
  blind : ∀ (ν : Node p F) (t : Polynomial ℤ_[p]), liftOf { ν with lift := t } = liftOf ν

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Canonical lifts at every node (L1's determinism, per-node — prefix-monotone free). -/
def CanonPolicy.IsCanon (pol : CanonPolicy p F) (H : History p F) : Prop :=
  ∀ (r : ℕ) (hr : r < H.nodes.length), (H.nodes[r]'hr).lift = pol.liftOf (H.nodes[r]'hr)

open Classical in
/-- [REV 4, Fable#2 C1] The canonical RESIDUE-ROOT of a node: the `fieldEnum`-least root
of `ψImage ν` in F (junk 0 if none — realizable nodes always have one, `hzbarRoot`). The
presentation-normalization twin of the lift rule. -/
noncomputable def canonRoot (ν : Node p F) : F :=
  WithBot.recBotCoe 0 (fun j => (fieldEnum F).symm j)
    ((((ψImage ν).roots.toFinset.image (fieldEnum F)).min))

/-- **The CANONICAL PRESENTATION class** [REV 4, Fable#2 C1 — the η-granularity rebuild,
§0.6]: canonical lifts (the policy) AND the canonical residue root at every read. Each η
has exactly ONE normalized presentation class (PRESENT-NORM, §2 ledger, HC-2). -/
noncomputable def CanonPolicy.IsCanonPres (pol : CanonPolicy p F) (H : History p F) : Prop :=
  pol.IsCanon H ∧
  ∀ (r : ℕ) (hr : r < H.nodes.length),
    (((H.nodes[r]'hr).zbar : Fˣ) : F) = canonRoot (H.nodes[r]'hr)

/-- The root read's side fits the degree-n box (part of "§C history of the degree-n box"
— the note's ambient setting; powers W1's ℓ_r ≤ n chain). -/
def InBox (n : ℕ) (H : History p F) : Prop :=
  ∀ hj : 0 < H.nodes.length, (H.nodes[0]'hj).s0 + (H.nodes[0]'hj).wSide ≤ n

/-- **The LITERAL Lean Pref(P̂)** (L3: shape-match + realizable + canonical presentation,
in the degree-n box). [REV 6]: the domain is `Shape n`. -/
def PrefSet (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Set (History p F) :=
  {H | (P : ShapePrefix).MatchesHist H ∧ HistoryCoherent H ∧ Realizable H ∧
       InBox n H ∧ pol.IsCanonPres H}

/-- [REV 5, reconciliations (2)+(6)] The POLICY-FREE realizable prefix set — the
reference set for the typed dictionary pin `PresentNorm`. -/
def PrefSetAny (n : ℕ) (P : Shape n) : Set (History p F) :=
  {H | (P : ShapePrefix).MatchesHist H ∧ HistoryCoherent H ∧ Realizable H ∧ InBox n H}

end

/-- **The η-class data** — the note's η-granularity [REV 3]: per read, the side-digit
tuple AND ψ's coefficient tuple, ambient-field-valued. Everything else in the note's η is
shape-pinned (Matches), derived, or policy-determined (lifts, L1). A FINITE type: L8 is
structural, and C is N-free. -/
def EtaData (F : Type*) (P : ShapePrefix) : Type _ :=
  ∀ r : Fin P.reads.length,
    (Fin ((P.reads.get r).len + 1) → F) × (Fin ((P.reads.get r).g + 1) → F)

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- The η-class of a history (junk 0-tuples beyond the history's length). -/
noncomputable def etaData (P : ShapePrefix) (H : History p F) : EtaData F P :=
  fun r => ((H.nodes[(r : ℕ)]?).elim (fun _ => 0) (fun ν k => ν.sideDigit (k : ℕ)),
            (H.nodes[(r : ℕ)]?).elim (fun _ => 0) (fun ν k => ((ν.ψ.coeff (k : ℕ) : ↥ν.σ.K) : F)))

/-- Coordinatewise field-automorphism action on η-class data (the Galois relation between
conjugate presentations — Fable#2 C1's witness action). -/
def EtaGalEq {P : ShapePrefix} (d d' : EtaData F P) : Prop :=
  ∃ φ : F ≃+* F, ∀ r : Fin P.reads.length,
    ((d' r).1 = fun k => φ ((d r).1 k)) ∧ ((d' r).2 = fun k => φ ((d r).2 k))

/-- **The canonical index of Pref(P̂)**: the η-classes of PrefSet. C_P̂(p) counts THESE.
N-FREE. -/
abbrev PrefIdx (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Type _ :=
  ↥(etaData (P : ShapePrefix) '' PrefSet n pol P)

open Classical in
/-- [REV 7, Codex#5 c.2 — the PIECEWISE form, L12 QUOTED: "N(P̂) := max_{η ∈ Pref(P̂)}
N(η,⊤) if Pref(P̂) ≠ ∅, N(P̂) := 1 if Pref(P̂) = ∅"]. On the NONEMPTY branch, NPband's
alignment with max_η N(η,⊤) is the SEAM pin **NP-ID** (§2.5 W4-4); the corpus-CONSUMED
content is only NP_stab + the range (NPu, D4R4_all). `PrefIdx` is pol-dependent, hence so
is NP — as is L12's own Pref-conditional. ∅-shape routing: Lean PrefIdx(∅) is empty (the
History type has no empty chain — F3's displayed deviation), ELSE branch, value 1;
NPband(∅) = 1 too — all routes give L12's N(∅) = 1, value-exact. -/
noncomputable def Shape.NP {n : ℕ} (P : Shape n) (pol : CanonPolicy p F) : ℕ :=
  if Nonempty (PrefIdx n pol P) then (P : ShapePrefix).NPband n else 1

/-- **PRESENT-NORM, TYPED** [REV 5]: the two-sided dictionary between the note's η's and
the normalized classes. (i) TOTALITY (L1 kernel-(a) totality + the L6-corollary +
conjugation equivariance): every POLICY-FREE realizable prefix has a normalized class-mate
up to Galois; (ii) UNIQUENESS (embedding rigidity): Galois-related normalized classes
coincide. Math status: note-supported; Lean discharge = HC-2. Carried as the FIELD
`Presented.hnorm`. -/
def PresentNorm (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Prop :=
  (∀ H : History p F, H ∈ PrefSetAny n P → ∃ i : PrefIdx n pol P,
     EtaGalEq (etaData (P : ShapePrefix) H) i.1) ∧
  (∀ H H', H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
    EtaGalEq (etaData (P : ShapePrefix) H) (etaData (P : ShapePrefix) H') →
      etaData (P : ShapePrefix) H = etaData (P : ShapePrefix) H')

/-- The classical representative section (a DEF, not a field — finding 3). -/
noncomputable def reprOf {n : ℕ} {pol : CanonPolicy p F} {P : Shape n}
    (i : PrefIdx n pol P) : History p F := i.2.choose

open Classical in
/-- The corpus C with the note's η = ∅ dispatch baked in at the note's own definition
level (Pref(∅) = {∅} — §D4-R L12/D4R.1: "present iff P̂ = ∅"). -/
noncomputable def Shape.CD {n : ℕ} (P : Shape n) (pol : CanonPolicy p F) : ℕ :=
  if (P : ShapePrefix).reads = [] then 1 else Nat.card (PrefIdx n pol P)

/-- [REV 5, reconciliation (3)] The OPTION-LEVEL Pref: the note's chain ontology with the
empty prefix as a first-class member (`none` = the empty chain ∅). F3 proves
`Pref(∅) = {∅}` LITERALLY on this object. -/
def PrefOpt (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) :
    Set (Option (History p F)) :=
  {c | match c with
       | none => (P : ShapePrefix).reads = []
       | some H => H ∈ PrefSet n pol P ∧ (P : ShapePrefix).reads ≠ []}

/-- Option-level class data (none ↦ none — the η = ∅ class). -/
noncomputable def etaDataO (P : ShapePrefix) :
    Option (History p F) → Option (EtaData F P)
  | none => none
  | some H => some (etaData P H)

end

/-- S(∅,⊤) — §C C.0's EMPTY HISTORY clause at Z = ⊤ (the FULL BOX; never Thm C(b)). -/
def emptyFiber (p m : ℕ) : Set (Box p m) := Set.univ

/-- **The presented family** [REV 3, finding 3]: everything is CONSTRUCTED from `PrefSet`
except the two genuinely-open data — the HC-2 presentations (`jet`) and the typed
dictionary pin (`hnorm`). REPRESENTATIVE CAVEAT (displayed for the audit): `fiber i` below
is the chosen representative's `SHZ ⊤`; that all representatives of one η-class present
the SAME classifier locus is HC-2 semantic content (`ClassFiberWelldef`). -/
structure Presented (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (P : Shape n) where
  jet : (i : PrefIdx n pol P) → JetSetup (reprOf i) n N m
  hnorm : PresentNorm n pol P

/-- [REV 5, reconciliation (5)] **The note's threshold, as data.** [REV 6]: NP is the
DEFINED `Shape.NP` (piecewise since REV 7), so the ONLY field left is `jets` —
presentations at EVERY level ≥ NP (§C C.2, HC-2). Stability from NP on is DERIVED (NPu);
`NP ≤ Nshape` is DERIVED (NPu); TW constructs `Threshold` from PRESENT-EXIST. -/
structure Threshold (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n : ℕ) (pol : CanonPolicy p F) (P : Shape n) where
  jets : ∀ N : ℕ, P.NP pol ≤ N → Presented p F n N (n * N) pol P

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F} {P : Shape n}

/-- The per-class fiber: the representative's classifier locus at Z = ⊤. -/
def Presented.fiber (S : Presented p F n N m pol P) (i : PrefIdx n pol P) :
    Set (Box p m) := (S.jet i).SHZ (topLocus p m)

open Classical in
/-- [RATIFICATION REPAIR D4″, 2026-07-29 — the ∅ dispatch wired INTO the note-designated
object; the round-1 parallel `eventO` is DELETED] **The event S(P̂,⊤)** — L5 (note
~4788–4800): the EMPTY prefix η = ∅ is INCLUDED, "S(∅,⊤) = the box (§C C.0's EMPTY
HISTORY clause T(∅, Z) := Z, at Z = ⊤: no constraint, vol 1) — this empty case is the
base of L6's induction". The Lean `PrefIdx` is History-indexed and the History type has
no empty chain (F3's displayed deviation), so the bare iUnion is ∅ at `reads = []`; THIS
definition therefore dispatches on `reads = []` exactly as `Shape.CD` does: FULL BOX on
the empty shape, the (multiplicity-weighted-cover) union of the class fibers otherwise
(`event_empty_shape` / `event_of_ne` below). ONE semantics — no parallel object. -/
def Presented.event (S : Presented p F n N m pol P) : Set (Box p m) :=
  if (P : ShapePrefix).reads = [] then Set.univ else ⋃ i, S.fiber i

open Classical in
/-- [RATIFICATION REPAIR D4″, 2026-07-29 — dispatch wired in; `multO` DELETED] **The
multiplicity mult_P̂(f)** — L5/L6/L12: "Pref(∅) = {∅}", so mult_∅(f) =
#{η ∈ {∅} : η ∈ T_can(f)} ≡ 1 (the root's presence is L2's law, `TreeModel.root_mem`);
on every nonempty shape it is #{classes whose fiber contains f}. Same `reads = []`
dispatch as `Shape.CD`/`event` (`mult_empty_shape` / `mult_of_ne` below). -/
noncomputable def Presented.mult (S : Presented p F n N m pol P) (x : Box p m) : ℕ :=
  if (P : ShapePrefix).reads = [] then 1
  else Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i}

/-- Unfolding law (nonempty shape): `event` is the union of the class fibers. -/
theorem Presented.event_of_ne (S : Presented p F n N m pol P)
    (hne : (P : ShapePrefix).reads ≠ []) : S.event = ⋃ i, S.fiber i := by
  rw [Presented.event, if_neg hne]

/-- Unfolding law (nonempty shape): `mult` is the incidence count. -/
theorem Presented.mult_of_ne (S : Presented p F n N m pol P)
    (hne : (P : ShapePrefix).reads ≠ []) (x : Box p m) :
    S.mult x = Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i} := by
  rw [Presented.mult, if_neg hne]

/-- L5's empty base on the designated object: S(∅,⊤) = the FULL BOX. -/
theorem Presented.event_empty_shape (S : Presented p F n N m pol P)
    (hP : (P : ShapePrefix).reads = []) : S.event = Set.univ := by
  rw [Presented.event, if_pos hP]

/-- L5/L12's empty base on the designated object: mult_∅ ≡ 1 (Pref(∅) = {∅}). -/
theorem Presented.mult_empty_shape (S : Presented p F n N m pol P)
    (hP : (P : ShapePrefix).reads = []) (x : Box p m) : S.mult x = 1 := by
  rw [Presented.mult, if_pos hP]

end

/-! ## §3.0 group (5) — the encoding target, snoc/prefix, the tree, the pinned Props -/

/-- The L11 encoding target (pool-valued digit tuples of the RETAINED sizes d_r +
selection indices). -/
def EncTargetP (p : ℕ) (F : Type*) [Field F] (P : ShapePrefix) : Type _ :=
  ∀ r : Fin P.reads.length,
    ((Fin (P.reads.get r).d → ↥(pool p (P.reads.get r).w F)) × Fin (P.reads.get r).mbar)

open Classical in
/-- [E9 Defs addendum — elaboration helper] junk-safe projection into the pool: the
identity on pool members (E1's territory — every counted digit), junk 1 otherwise
(1 ∈ pool always: 1^(p^w) = 1). -/
noncomputable def poolProj (p w : ℕ) (F : Type*) [Field F] (x : F) : ↥(pool p w F) :=
  if h : x ∈ pool p w F then ⟨x, h⟩ else ⟨1, by simp [pool]⟩

/-- [E9 Defs addendum — elaboration helper] every read of a SHAPE has m̄ ≥ 1: the
certificate's `gmu` (g·μ ≤ ℓ) with g, μ ≥ 1. Powers `encIdx`'s total selection index. -/
lemma Shape.mbar_pos {n : ℕ} (P : Shape n) (r : Fin (P : ShapePrefix).reads.length) :
    0 < ((P : ShapePrefix).reads.get r).mbar := by
  rw [List.get_eq_getElem]
  exact Nat.div_pos (P.2.gmu r.1 r.2)
    (Nat.mul_pos ((P : ShapePrefix).reads[r.1]'r.2).hg ((P : ShapePrefix).reads[r.1]'r.2).hμ)

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

open Classical in
/-- [E9 Defs addendum] the L11 encoding map: per read, the d_r counted side digits
(pool-projected) and the selection index (selRank, mod-collapsed into `Fin m̄` — the
collapse is the identity on members, where E7 gives selRank < m̄; both junk branches are
never taken on `PrefIdx`, which is E9's domain). -/
noncomputable def encIdx {n : ℕ} {pol : CanonPolicy p F} {P : Shape n}
    (i : PrefIdx n pol P) : EncTargetP p F (P : ShapePrefix) :=
  fun r =>
    ⟨fun k => poolProj p ((P : ShapePrefix).reads.get r).w F
        (((reprOf i).nodes[(r : ℕ)]?).elim 0 (fun ν => ν.sideDigit (k : ℕ))),
     ⟨(((reprOf i).nodes[(r : ℕ)]?).elim 0
          (fun ν => selRank ((P : ShapePrefix).reads.get r).w ν))
        % ((P : ShapePrefix).reads.get r).mbar,
      Nat.mod_lt _ (Shape.mbar_pos P r)⟩⟩

/-- Appending a non-root node to a history (for the tree's child laws). -/
def _root_.LeanUrat.MovesC.History.snoc (H : History p F) (ν : Node p F)
    (hν : ν.species ≠ ReadSpecies.root) : History p F where
  nodes := H.nodes ++ [ν]
  nonempty := by simp
  root_iff := by
    intro j hj
    rcases Nat.lt_or_ge j H.nodes.length with hlt | hge
    · rw [List.getElem_append_left hlt]
      exact H.root_iff j hlt
    · have hj1 : j < H.nodes.length + 1 := by simpa using hj
      have hj0 : j = H.nodes.length := by omega
      subst hj0
      have hv : (H.nodes ++ [ν])[H.nodes.length]'hj = ν := by simp
      rw [hv]
      have hne : H.nodes.length ≠ 0 := by simpa using H.nonempty
      exact ⟨fun hsp => absurd hsp hν, fun h0 => absurd h0 hne⟩

/-- History prefix order (nodewise list prefix). -/
def _root_.LeanUrat.MovesC.History.IsPrefixOf (H H' : History p F) : Prop :=
  H.nodes <+: H'.nodes

end

/-- **T_can(f) with L2's STRUCTURAL layer** [REV 3 gap 8; REV 5 reconciliation (1): the
node carrier is `Option (History p F)` — `none` IS the empty chain ∅, a first-class tree
node; THE ROOT'S PRESENCE IS A LAW (`root_mem`), and NO law forces `some`-chains (L5's
(ns) case)]. ==== SEAM (W4-SYNC W4-1; NOT built at E-phase) ====: L2's ALL-AND-ONLY law
(`eligible` + `child_iff`) is ABSENT here — its typed form is frozen as the §2.5 W4-1
negotiating position (tie-demand union + re-keying charge there). The E-phase core
consumes ONLY the structural counting fields below. [W4-SYNC delta 10, 2026-07-29 — MovesT
REV-7 ruling 1]: this §2.5 W4-1 row now ABSORBS the (c2) per-track COVERING clause (a
window-opening repeated reduction factor forces a root child carrying that track's data;
MOVES 7112–7119); its MovesD-side frozen typed form is `W41ChildCover` below, re-keying in
wave 4 as `MovesT.ChildCover`. -/
structure TreeModel (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) where
  mem : Option (History p F) → Box p m → Prop
  child : Option (History p F) → Node p F → Box p m → Prop
  /-- **THE ROOT'S PRESENCE IS A LAW** (L2: "its root is the empty chain ∅"). It may be a
  LEAF (no children — L5's (ns) case), so NO nonempty-chain inhabitation is forced. -/
  root_mem : ∀ x : Box p m, mem none x
  mem_single : ∀ (ν : Node p F)
      (h1 : ([ν] : List (Node p F)) ≠ [] ∧
        ∀ (j : ℕ) (hj : j < ([ν] : List (Node p F)).length),
          ((([ν] : List (Node p F))[j]'hj).species = ReadSpecies.root ↔ j = 0))
      (x : Box p m),
    mem (some ⟨[ν], h1.1, h1.2⟩) x ↔ child none ν x
  mem_snoc : ∀ (H : History p F) (ν : Node p F) (hν : ν.species ≠ ReadSpecies.root)
      (x : Box p m),
    mem (some (H.snoc ν hν)) x ↔ (mem (some H) x ∧ child (some H) ν x)
  mem_realizable : ∀ (H : History p F) (x : Box p m), mem (some H) x →
    HistoryCoherent H ∧ Realizable H ∧ pol.IsCanonPres H

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- L6's (D4R-CYL), as the PINNED Prop [REV 3, finding 7]: S(η,⊤) = {f : η ∈ T_can(f)}
for every enumerated class. Note-PROVED (kernel (a)+(b) dual-verified-discharged + Thm
C(a)); its LEAN proof is EXPLICITLY DEFERRED to the wave-4/HC-2 tree corpus. [REV 9,
SEAM W4-3]: the consumer side (D15) is NOT built at E-phase; this def is consumed by
NOTHING in the core. -/
def D4R_CYL {n N m : ℕ} {pol : CanonPolicy p F} {P : Shape n}
    (S : Presented p F n N m pol P) (T : TreeModel p F n N m pol) : Prop :=
  ∀ (i : PrefIdx n pol P) (x : Box p m), x ∈ S.fiber i ↔ T.mem (some (reprOf i)) x

/-- **the (c2) per-track COVERING clause AT THE W4-1 INTERFACE — MovesD-side frozen typed
form** [W4-SYNC delta 10, `lean/notes/W4_SYNC_DELTAS_2026-07-29.md`: MovesT REV-7 ruling 1,
the W4-1 five-round adjudication (the fourth-round BDY hold OVERTURNED); warrant (c2)'s L1
totality D4R.0-K(a), MOVES 7112–7119]. Absorbs into MovesD's §2.5 W4-1 row the orchestrator
ruling that W4-1 (`eligible`/`child_iff`) GAINS a covering duty: at a realized window-opening
read (a reduction factor `ψ` REPEATED in the level-0 reduction `redOf x`, multiplicity
m_i ≥ 2), a root child EXISTS carrying that track's data — `T.child none ν x` with
`trackOf ν = ψ`. This is the STRUCTURAL half expressible over MovesD's `TreeModel`; the
semantic-layer placement ("… in the track-`ψ` reduction cell's own branch set") re-keys in
wave 4 as `MovesT.ChildCover` over `CellData`/`branchSetOf`/`cellOf` (with `redOf := redPoly χ`
at the designated chart). Fence-free (no `HistoryCoherent` content). Owner HC-2/D4R.0-K (L1
totality) — NEVER proved here; consumed by NOTHING in the E-phase core (a frozen negotiating
position alongside `D4R_CYL`/`ClassFiberWelldef`). The in-corpus falsifier is MovesT-side
(`constFalse_childCover_false`, T-D2): the constant-false-child / unit-cell model is FALSE at
this interface. -/
def W41ChildCover {n N m : ℕ} {pol : CanonPolicy p F}
    (T : TreeModel p F n N m pol)
    (redOf : Box p m → Polynomial (ZMod p))
    (trackOf : Node p F → Polynomial (ZMod p)) : Prop :=
  ∀ (x : Box p m) (ψ : Polynomial (ZMod p)),
    ψ ∈ UniqueFactorizationMonoid.normalizedFactors (redOf x) →
    2 ≤ Multiset.count ψ
      (UniqueFactorizationMonoid.normalizedFactors (redOf x)) →
    ∃ ν : Node p F, trackOf ν = ψ ∧ T.child none ν x

end

/-- [REV 5, reconciliation (7)] Representative independence: one η-class, one classifier
locus, over ALL representatives and ALL jets (§C L4's semantic content). Deferred to the
wave-4/HC-2 tree corpus together with `D4R_CYL`; [REV 9, SEAM W4-3]: its consumer (D15's
`hwd`) is NOT built at E-phase — declared, consumed by nothing in the core. -/
def ClassFiberWelldef (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (pol : CanonPolicy p F) (P : Shape n) : Prop :=
  ∀ (H H' : History p F), H ∈ PrefSet n pol P → H' ∈ PrefSet n pol P →
    etaData (P : ShapePrefix) H = etaData (P : ShapePrefix) H' →
    ∀ (J : JetSetup H n N m) (J' : JetSetup H' n N m),
      J.SHZ (topLocus p m) = J'.SHZ (topLocus p m)

/-! ## SEAM (W4-SYNC W4-2) — `VerdictModel` is NOT DECLARED at E-phase.

The kernel-(c)/VP surface (alphabet V, vdict, halt_iff, rootVdict, levelOf, cap laws,
Cell/cellOf ties) is a §2.5 contract entry, ENTIRE: its rev-8 typed form is the frozen
negotiating position (with `cell_local` WITHDRAWN from core strength per Codex#7 c.6's
kernel-(b)/(c)-conflation finding), the tie-demand union is recorded both directions
(no degenerate satisfiability AND no over-factoring), and the structure re-keys and
builds in wave 4 from §T-ASSEMBLY's VP-1/VP-2 + TB-CAP with MovesT. Nothing in MovesD
consumes it. -/

end LeanUrat.MovesD
