/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps

/-!
# Scaffold/DictIII/O2aOrder1 — O-2a §§2/3/5 order-≤1 layer (BP_III units III-A1, III-A4, III-A6b, III-A6c, III-A7, III-A8, III-A9)

BLOCKED-record file (prover III-A4, 2026-08-01; prover III-A7, 2026-08-01;
prover III-A8, 2026-08-01)
EXTENDED with the landed unit III-A1 (prover III-A1, 2026-08-01:
`recoverNode`/`recoverEHist`, the Lemma R recovery map — see the section
header below the BLOCKED records), the landed unit III-A6c (prover
III-A6c, 2026-08-01: the positive order-1 reader gate `o2aGate*`), and the
landed unit III-A6b (prover III-A6b, 2026-08-01: `sideRead`/`gmnReaderOrder1`
+ the reader-law and reader-uniqueness lemmas — the `GMNReader` construction
from the order-1 polygon API rows `OL5`/`OL3min`;
its section header records the honest III-A6a dependency seam), and the
landed unit III-A9 (prover III-A9, 2026-08-01: the OL-6 order-≤1 instance
probe — binding leg `ol6_of_consF` + the one-node run gate `ol6Gate*`, last
section of this file).  The BLOCKED units III-A4 (pre-split
III-A4a level-0 / III-A4b Lemma B), III-A7 (O2a §5 Theorem 2(B) fired from
the `GMNCor120_38` literature row), and III-A8 (O2a §5 Theorem 2(D), the
no-phantom/CU-2 content composed with III-A7) cannot
be transcribed, on independent grounds recorded below.  Convention as in
`GDOrder1.lean`'s BLOCKED(III-G3a/G4/G5/G6) records: verbatim locus, exact
failure, no weakened or invented statement.  The imports pin the layer the
eventual statements will consume (`Carriers`/`GMNReader`/`Hyps` via `Hyps`:
`ChainData`, `Theta`, `LiftFn`, `OL1`, `KeyPkg`, `ConsF`), so this record file
compiles against the as-built Wave-0 interface.
-/

namespace LeanUrat.Scaffold.DictIII

/- BLOCKED(III-A4): NO Lean statement exists in `lean/blueprints/BP_III.md`
for this unit, so there is nothing to transcribe — and statement invention
is forbidden (transcription must be VERBATIM; changes forbidden a fortiori).

Locus audit (probed 2026-08-01 against BP_III.md at HEAD, 1011 lines):
1. §1 "THE STATEMENT LAYER (exact Lean signature sketches)" enumerates
   modules 1.1–1.10 (`Carriers`, `GMNReader`, `Hyps`, `GDOrder1`, `Devid`,
   `Locality`, `Window`, `CU1`, `CU2t`, `O14apMap`).  There is NO module
   block for `Scaffold/DictIII/O2aOrder1.lean`, and no displayed signature
   anywhere in §1 for O-2a §3 Theorem 1, the D4 representative property
   ("Lift₀ is a Def-2.12 representative"), or the order-1 family bridge
   (Lemma B).  Wave-2 sibling units III-A1/A2/A3 are likewise absent from
   §1 (grep `recoverEHist`: only the §2 table row, line 764).
2. The ONLY III-A4 text is the §2 unit-table prose row (line 767):
   "Theorem 1 order ≤ 1 (D4: Lift₀ is a Def-2.12 representative; order-1
   family bridge Lemma B) | KEY-g supplies the representative property at
   level 0/1 | III-G12 | HARD (pre-split: A4a level-0, A4b Lemma B) |
   O2a §3 Thm 1 + Lemma B" — prose, not a Lean statement.
3. Neither `A4a` nor `A4b` has a statement anywhere in the blueprint
   (grep hits: the line-767 row, the §2 accounting note line 842, the §4
   wave plan line 921 only).

Exact failure mode, per the unit charge's own escalation clause: the charge
presupposes "its Lean statement is there VERBATIM"; the premise is false, so
the "transcribe EXACTLY" step cannot fire.  There is no compile error to
report because there is no display to compile.  Cure = architect adds a §1
module block for `O2aOrder1.lean` displaying the III-A4a and III-A4b
signatures over the as-built Wave-0 carriers (`LiftFn p F`, `OL1`,
`ChainData`/`Theta`, and the KEY-g/`KeyPkg` layer named by the proof-sketch
column), after which A4a→A4b re-run as scheduled. -/

/- BLOCKED(III-A4, second and independent ground — dependency not landed):
the row's sole dependency III-G12 ("KEY-g remaining: the (KPa) block at
order 1 + `KeyPkg` instance at order ≤ 1") has NO landed declaration in the
corpus (probed 2026-08-01: no G11/G12 declarations exist under
`Scaffold/DictIII/`; `KeyPkg` exists only as the III-H8 hypothesis row in
`Hyps.lean`, with no order-≤1 instance).  Upstream cause, per the standing
BLOCKED(III-G5) record in `GDOrder1.lean`: `gaussW_keyBlock`'s §1.4 display
is ill-typed downstream of III-G3a (`gaussW` never landed — its display
needs `Algebra ℤ (WithTop ℤ)`, unsynthesizable since `WithTop ℤ` is not a
semiring) AND stays mathematically FALSE under the intended Gauss-valuation
reading (countermodel `B = 1`, `Φ = X`: both Gauss values are `0`); that
record's closing line already names this consumer: the display "needs an
architect restatement … before III-G5 and its consumer III-G12 can land".
So the proof-sketch column's supply ("KEY-g supplies the representative
property at level 0/1") is not available at HEAD even if the III-A4
signatures were displayed today.  This ground clears automatically when the
III-G3a/G5 architect repair lands and III-G11/G12 complete. -/

/- BLOCKED(III-A7): Theorem 2(B) ("stmt + proof from `GMNCor120_38` + `ConsF`
+ `OL1` — fire the literature row along the chain"; deps III-C9/III-H6/III-H9;
src O2a r5 §5 Thm 2(B)) cannot be landed, on grounds probed 2026-08-01 at this
site (Lean 4.31, this pin):

1. Like III-A4 above, III-A7 has NO §1 display in BP_III.md — the only Lean
   rendering of Theorem 2(B)'s content anywhere in the blueprint is the
   `irrationalBranch` row of the `GMNCor120_38` §1.3 display
   (`DecIrr H → ConsF f H D R →
     MovesT.accE H.nodes * MovesT.accF H.nodes = f.natDegree`),
   which the unit row directs this unit to fire, and which is itself BLOCKED
   and unlanded at III-H9 (`DictIII/Hyps.lean`, bottom block).

2. The faithful composition of that only-on-record rendering,

     theorem thm2B_saturation {f : Polynomial ℤ_[p]} {H : EHist p F}
         {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
         (hcor : GMNCor120_38 p F) (hdec : DecIrr H)
         (hcons : ConsF f H D R)
         (hlift : LiftFn p F) (hOL1 : OL1 (Theta H) hlift) :
         MovesT.accE H.nodes * MovesT.accF H.nodes = f.natDegree :=
       hcor.irrationalBranch hdec hcons

   was elaborated against the as-built corpus and fails with, exactly:

   (a) NOT curable by dependency landing — III-H9's ground (1) reproduced at
       the III-A7 conclusion itself: `MovesT.accE`/`MovesT.accF` are corpus
       functions `MovesC.History p F → ℕ` (pinned as-is by the BP_III §1
       preamble + §3 corpus map) applied here to `H.nodes : List ENodeData`:
         Application type mismatch: The argument
           H.nodes
         has type
           List ENodeData
         but is expected to have type
           MovesC.History ?m.48 ?m.50
         in the application
           MovesT.accE H.nodes
       (and the same at `MovesT.accF H.nodes`).  No coercion exists; a
       list-domain overload or an `ENodeData → MovesC.Node` dressing would be
       a NEW definition changing the row's meaning — architect ruling needed
       (same seam as III-H9's).
   (b) Dependency-curable: "Unknown identifier `GMNCor120_38`" (III-H9
       blocked, row never landed) and "Unknown identifier `DecIrr`" (owned by
       §1.9 / III-S1a, `CU2t.lean`, not yet in the corpus).  `ConsF`, `OL1`,
       `LiftFn`, `Theta`, `GMNData`, `GMNReader` all resolve (deps III-C9,
       III-H6 landed).

Disposition: no declaration landed (per the III-H9/III-A4 precedent — the
SIGNATURE itself does not elaborate, so there is no statement to carry a
`sorry`).  Downstream inheritors: III-A8 (consumes A7) and III-S5b (fires the
same literature row).  Unblock order: architect ruling on the accE/accF
carrier seam → land III-H9 → land III-S1a (`DecIrr`) → transcribe III-A7 here
and fire `hcor.irrationalBranch hdec hcons`. -/

/- BLOCKED(III-A8): Theorem 2(D) ("no-phantom = CU-2 content, stmt over rows;
proof = composition Thm 2(D) ∘ ι as displayed"; sole dep III-A7; src O2a §5
Thm 2(D) + CUC §1) cannot be landed, on three independent grounds probed
2026-08-01 (BP_III.md at HEAD, 1011 lines; Lean 4.31, this pin):

1. NO Lean statement exists in the blueprint for this unit, so there is
   nothing to transcribe (statement invention forbidden; the charge's
   "its Lean statement is there VERBATIM" premise is false — the III-A4
   failure class above).  Grep audit: `III-A8`/`2(D)` hit exactly the §2
   unit-table prose row (line 773), the §3.6 CU-relabel note (line 899,
   "CU-2 = III-A8 (O-2a Thm 2(D) ∘ ι)"), the §4 wave-plan row (line 921),
   and the §5 sync-duty row (line 952) — all prose, none a signature; §1's
   module blocks 1.1–1.10 contain no `O2aOrder1.lean` block.

2. Sole dependency III-A7 is BLOCKED (record immediately above): the
   composition's ι-leg does not exist as a landed declaration, and its only
   on-record rendering is ill-typed at the accE/accF carrier seam (NOT
   curable by dependency landing; architect ruling needed).  III-A8 composes
   with exactly that conclusion, so it inherits the seam verbatim.

3. Independent of 1–2, the 2(D) statement itself has no renderable
   quantifier at HEAD: its content (O2a verifybrief rev 5 §5, clause (D) —
   "Every history emitted by the engine's stage flow on f is a well-formed
   element of 𝔈 (OL-4) satisfying Cons_f", over the row list
   OL-1 + OL-2-min + OL-3-min + OL-4 + OL-5 + OL-6 after the REV-5/V25
   OL-3-min cut) quantifies over ENGINE-EMITTED histories.  No
   engine-emission predicate (stage-flow run ↦ `EHist p F`) exists in the
   Wave-0 scaffold: the landed `OL4`/`OL5`/`OL6` rows in `Hyps.lean`
   (unit III-H7b/c) are chain-level Props over `(f, c, D, R)` with no
   run/emission carrier, and the corpus-side bridge (`machineProj`,
   §1.8/III-U1) is Wave-4, unlanded.  Rendering "emitted by the engine's
   stage flow" would be a NEW definition, not a transcription.

SYNC-DUTY note (BP §5, carried by this unit's charge): pass P(O-2a r5) is
pending; if it forces a 2(D)-scope repair, this statement re-lands — any
architect display must state (D) over the post-r5 row list (OL-3 cut to its
minimal core, V25).  Cure = architect adds the §1 module block for
`O2aOrder1.lean` displaying the III-A7/III-A8 signatures over the as-built
rows (incl. the emission carrier ruling of ground 3 and the accE/accF seam
ruling of the III-A7/III-H9 records), after which A7→A8 re-run as
scheduled. -/

/-! ## Unit III-A1 — the Lemma R recovery map `recoverEHist` (O-2a rev-5 §2)

Unit III-A1 (BP_III wave 2, table row line 764): "recovery map
`recoverEHist (f c)` def — the displayed field-by-field recipe — deps III-C9
— src O2a §2 Lemma R pf".  Unlike III-A4/III-A7 above, this unit's charge
sanctions transcription FROM THE SOURCE NOTE ("No §1-displayed signature;
transcribe from O2a §2 Lemma R pf"), and the unit is a DEFINITION, so there
is a display to render: O-2a rev-5 §2, Lemma R *Proof.*: "Displayed recovery
map: given (f, 𝔠), 𝔠 = Θ(𝐇), set ψ̂₀ := the level-0 datum of 𝔠;
a₀ := ord_{ψ̂₀}(f̄) ((c0)); for i = 1, …, k' (:= length of 𝔠):
(e_i, h_i) := the lowest-terms data of λ_i (from 𝔠); S_i := the UNIQUE side
of N_i^−(f) of slope λ_i (a polygon has at most one side of a given slope;
the side exists by (c1)); ℓ_i := d(S_i); (s_i, u_i) := the initial point of
S_i in the order-i integer frame ((c1)'s positional clause); ψ̂_i := the
level-i datum of 𝔠; g_i := deg ψ̂_i; μ_i := ord_{ψ̂_i}(R_{λ_i}(f)) ((c2));
inc_i := 1 iff e_i·g_i ≥ 2 (W2)."

The Lean rendering below is this unit's (no blueprint signature exists) —
flagged for division-lead review, not fenced.  Design notes:

* **Reads through the reader (III-C9 language).** The recipe's GMN reads are
  rendered by the `GMNReader` rows exactly as in `ConsF`: "the UNIQUE side of
  N_i^−(f) of slope λ_i" is `R.side i` (`side_spec`/`side_unique` carry the
  existence-by-(c1) and at-most-one-side-per-slope steps, consumed by unit
  III-A2), `ord_{ψ̂_i}(R_{λ_i}(f))` is `R.resOrd i`, and `ord_{ψ̂₀}(f̄)` is
  `R.rootOrd` ((c0) ties it to a₀).  Indexing is `ConsF`'s list convention:
  Lean node index `i` (0-based) ↔ the display's level i+1.
* **Totalized with `Option`; guards = the facts the displayed proof invokes.**
  The display defines the map on Θ(𝔈°_f), where (c0)/(c1)/(c2) and the
  carrier laws hold.  The Lean rendering is total: each read is an `Option`
  bind, and the `ENodeData`/`EHist` carrier laws (e, h ≥ 1 coprime, ℓ ≥ 1,
  g, μ ≥ 1, μ·g ≤ ℓ, a₀ ≥ 1) form one decidable guard.  That the map returns
  `some` and reproduces every field on Θ(𝔈°_f) under `ConsF` is unit
  III-A2's content (Lemma R proper), not claimed here.
* **`hpsihat` argument.** 𝔗-membership in the source carries the dressing
  laws (monic irreducible ≠ z) for every listed level; the Lean `ChainData`
  carries them in-range only (`hdress`), while `EHist.hpsihat` requires them
  at ALL indices (off-range junk included).  The recovery map takes the
  all-index law as the explicit argument `hpsihat`; at `c = Theta H` it is
  `H.hpsihat` verbatim, so no field of the recovered history deviates from
  the display. -/

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- Unit III-A1, node step: the level-(i+1) line of the displayed recipe
(O-2a rev-5 §2 Lemma R pf; section header above).  Field-by-field:
`(e, h)` := the lowest-terms slope datum from 𝔠 (`c.slopes[i]?`); `S` := the
side of slope λ_i read off `R.side i`; `ℓ := d(S)`; `(s, u)` := the initial
point of `S`; `g := deg ψ̂_i` (`c.psihat i`, the level-i datum of 𝔠);
`μ := ord_{ψ̂_i}(R_{λ_i}(f))` (`R.resOrd i`, (c2)); `sel := some (g, μ)`;
`inc := 1 iff e·g ≥ 2` (W2).  The guard bundle is exactly the `ENodeData`
carrier laws. -/
def recoverNode (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) (R : GMNReader f c D) (i : ℕ) : Option ENodeData := do
  let eh ← c.slopes[i]?              -- (e_i, h_i) := the lowest-terms data of λ_i, from 𝔠
  let S ← R.side i                   -- S_i := the unique side of N_i^−(f) of slope λ_i ((c1))
  let g := (c.psihat i).natDegree    -- g_i := deg ψ̂_i (level-i datum of 𝔠)
  let μ := R.resOrd i                -- μ_i := ord_{ψ̂_i}(R_{λ_i}(f)) ((c2))
  if hok : 1 ≤ eh.1 ∧ 1 ≤ eh.2 ∧ Nat.gcd eh.1 eh.2 = 1 ∧
      1 ≤ S.ℓ ∧ 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ S.ℓ then
    pure
      { e := eh.1, h := eh.2
        ℓ := S.ℓ                     -- ℓ_i := d(S_i)
        s := S.s, u := S.u           -- (s_i, u_i) := the initial point of S_i
        sel := some (g, μ)
        inc := decide (2 ≤ eh.1 * g) -- inc_i := 1 iff e_i·g_i ≥ 2 (W2)
        he := hok.1
        hh := hok.2.1
        hcop := hok.2.2.1
        hl := hok.2.2.2.1
        hsel := by
          rintro gμ hgμ
          obtain rfl : (g, μ) = gμ := by simpa using hgμ
          exact ⟨hok.2.2.2.2.1, hok.2.2.2.2.2.1, hok.2.2.2.2.2.2⟩ }
  else none

/-- Unit III-A1: the Lemma R recovery map (O-2a rev-5 §2 Lemma R pf,
transcribed field-by-field; section header above).  Given (f, 𝔠):
ψ̂₀ := the level-0 datum of 𝔠 (`c.psi0`, with `c.base`/`c.fld`/`c.psihat`
carried as the tower data of 𝔠); a₀ := ord_{ψ̂₀}(f̄) read off `R.rootOrd`
((c0)); one node per i < k' := length of 𝔠 by `recoverNode` (the displayed
per-level line).  `hpsihat` is the all-index dressing law of the section
header's third design note; the a₀ ≥ 1 carrier law is the remaining guard. -/
def recoverEHist (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) (R : GMNReader f c D)
    (hpsihat : ∀ i, (c.psihat i).Monic ∧ Irreducible (c.psihat i) ∧
      c.psihat i ≠ Polynomial.X) :
    Option (EHist p F) :=
  -- `Option.bind` rather than `do`: the recovered node list lives in `Type 0`
  -- while `EHist p F` lives in `F`'s universe, and `do` would pin one monad.
  ((List.range c.slopes.length).mapM (recoverNode f c D R)).bind fun nodes =>
  if ha0 : 1 ≤ R.rootOrd then
    some
      { base := c.base
        psi0 := c.psi0               -- ψ̂₀ := the level-0 datum of 𝔠
        hpsi0 := c.hpsi0
        a0 := R.rootOrd              -- a₀ := ord_{ψ̂₀}(f̄) ((c0))
        ha0 := ha0
        nodes := nodes
        fld := c.fld
        psihat := c.psihat           -- ψ̂_i := the level-i datum of 𝔠
        hpsihat := hpsihat }
  else none

/-! ## Unit III-A6c — the positive order-1 reader gate at p = 2 (D-R2 non-vacuity)

Unit III-A6c (BP_III §2 wave-2 table row, line 771): "positive order-1 reader
gate at `p = 2`, `c.slopes.length = 1` | construct data; prove a side is
returned and laws are non-vacuous | III-A6b | MED | O2a (C4) non-vacuity" —
design risk D-R2's concrete non-vacuity gate (BP §5: "III-A6c is the concrete
non-vacuity gate").

Adjudication of the transcription rule (division-lead review flag, per the
III-A1 precedent above): like every wave-2 unit, III-A6c has NO §1-displayed
signature.  Unlike the BLOCKED theorem-statement units III-A4/A7/A8, this row
is a GATE: its §2 proof-sketch column IS the specification ("construct data;
prove ..."), and the blueprint's own gate discipline (III-U8's row, template
`HK23_twoNodeGatePos` per BP §3.3) has the prover construct concrete data —
no pre-displayed statement can exist for data the gate itself builds.  Every
structure instantiated below (`ChainData`, `SideDatum`, `GMNData`,
`GMNReader`, `HasRequestedSlope`) is the landed III-C5/III-C8 statement layer
VERBATIM, unmodified — nothing is redeclared, weakened, or invented at the
interface level.  Dependency note: III-A6a/III-A6b (the general order-≤1
constructions from the corpus polygon API) are NOT landed at HEAD; the gate
is self-contained ahead of them, exactly as its proof-sketch column
prescribes, and does not discharge or subsume either.

Gate content (all sorry-free, Lean-core expected):
* `o2aGateChain : ChainData 2 (ZMod 2)` with `slopes = [(1,1)]` — genuine
  order-1 data at `p = 2` (`o2aGate_slopes_length`);
* `o2aGateData` — a `GMNData` for `f = X ∈ ℤ_[2][x]`, ONE principal side
  `o2aGateSide = (e,h,ℓ,s,u) = (1,1,1,0,0)`, finite slope;
* `o2aGateReader` — a `GMNReader` for that data: D-R2's interface is
  SATISFIABLE (each of the five laws proved, none vacuously);
* the positive theorems: a side IS returned (`o2aGate_side_returned`), and
  every reader law fires on that genuine witness (`o2aGate_law_fires`,
  `o2aGate_side_unique`, `o2aGate_resOrd`, `o2aGate_rootOrd`,
  `o2aGate_resDeg`), with the polygon honestly non-empty
  (`o2aGate_principalSides_ne_nil`). -/

/-- The gate's dressing/root polynomial `X + 1` over the top subfield of
    `ZMod 2`: monic, irreducible (degree one), and ≠ `X` — everything
    `ChainData.hpsi0`/`ChainData.hdress` ask for. -/
noncomputable def o2aGatePoly : Polynomial ↥(⊤ : Subfield (ZMod 2)) :=
  Polynomial.X + Polynomial.C 1

theorem o2aGatePoly_monic : o2aGatePoly.Monic :=
  Polynomial.monic_X_add_C 1

theorem o2aGatePoly_irreducible : Irreducible o2aGatePoly :=
  o2aGatePoly_monic.irreducible_of_degree_eq_one (Polynomial.degree_X_add_C 1)

theorem o2aGatePoly_ne_X : o2aGatePoly ≠ Polynomial.X := by
  intro h
  have h0 := congrArg (fun q => Polynomial.coeff q 0) h
  simp [o2aGatePoly] at h0

/-- The gate chain 𝔠 at `p = 2`: base = the top subfield of `ZMod 2`, a single
    slope `(e, h) = (1, 1)` in lowest terms, constant dressing `X + 1`.  This
    is III-A6c's `c.slopes.length = 1` instance. -/
noncomputable def o2aGateChain : ChainData 2 (ZMod 2) where
  base := ⊤
  psi0 := o2aGatePoly
  hpsi0 := ⟨o2aGatePoly_monic, o2aGatePoly_irreducible⟩
  slopes := [(1, 1)]
  hcop := by
    intro eh heh
    have h : eh = (1, 1) := by simpa using heh
    subst h
    exact ⟨le_rfl, le_rfl, rfl⟩
  fld := fun _ => ⊤
  psihat := fun _ => o2aGatePoly
  hdress := fun _ _ =>
    ⟨o2aGatePoly_monic, o2aGatePoly_irreducible, o2aGatePoly_ne_X⟩

/-- III-A6c gate, order-1 restriction: the chain has EXACTLY one slope. -/
theorem o2aGate_slopes_length : o2aGateChain.slopes.length = 1 := rfl

/-- The gate's single polygon side: `(e, h, ℓ, s, u) = (1, 1, 1, 0, 0)`,
    finite slope (`isNegInfty = false`), matching the chain's requested slope
    `(1, 1)` at level 0. -/
def o2aGateSide : SideDatum :=
  ⟨1, 1, 1, 0, 0, false⟩

/-- The gate's semantic GMN datum over `f = X ∈ ℤ_[2][x]`: one principal side
    per level, residual order/degree 1, root order 1. -/
def o2aGateData : GMNData (Polynomial.X : Polynomial ℤ_[2]) o2aGateChain where
  principalSides := fun _ => [o2aGateSide]
  residualOrder := fun _ => 1
  residualDegree := fun _ => 1
  rootOrder := 1

/-- III-A6c: the reader for `o2aGateData`.  `side` answers at level 0 exactly;
    all five `GMNReader` laws are PROVED from the concrete data — D-R2's
    interface is satisfiable, not vacuously consistent. -/
def o2aGateReader :
    GMNReader (Polynomial.X : Polynomial ℤ_[2]) o2aGateChain o2aGateData where
  side := fun i => if i = 0 then some o2aGateSide else none
  side_spec := by
    intro i S
    cases i with
    | zero =>
      constructor
      · intro h
        have h' : some o2aGateSide = some S := h
        injection h' with hS
        subst hS
        exact ⟨by simp [o2aGateData], rfl⟩
      · rintro ⟨hmem, -⟩
        have hS : S = o2aGateSide := by simpa [o2aGateData] using hmem
        simp [hS]
    | succ n =>
      constructor
      · intro h
        simp at h
      · rintro ⟨-, hslope⟩
        simp [HasRequestedSlope, requestedSlope, o2aGateChain] at hslope
  side_unique := by
    intro i S T hS hT _ _
    have hS' : S = o2aGateSide := by simpa [o2aGateData] using hS
    have hT' : T = o2aGateSide := by simpa [o2aGateData] using hT
    rw [hS', hT']
  resOrd := fun _ => 1
  resOrd_spec := fun _ => rfl
  rootOrd := 1
  rootOrd_spec := rfl
  resDeg_eq_sideDeg := by
    intro i S h
    cases i with
    | zero =>
      have h' : some o2aGateSide = some S := h
      injection h' with hS
      subst hS
      rfl
    | succ n =>
      simp at h

/-- III-A6c gate: a side IS returned at the (unique) level 0. -/
theorem o2aGate_side_returned :
    o2aGateReader.side 0 = some o2aGateSide := rfl

/-- III-A6c gate: the `side_spec` law fires on a genuine witness — the
    returned side lies on the polygon AND carries the requested slope. -/
theorem o2aGate_law_fires :
    o2aGateSide ∈ o2aGateData.principalSides 0 ∧
      HasRequestedSlope o2aGateChain 0 o2aGateSide :=
  (o2aGateReader.side_spec 0 o2aGateSide).mp o2aGate_side_returned

/-- III-A6c gate: the `side_unique` law fires — any polygon side carrying the
    requested slope IS the returned side. -/
theorem o2aGate_side_unique (S : SideDatum)
    (hmem : S ∈ o2aGateData.principalSides 0)
    (hslope : HasRequestedSlope o2aGateChain 0 S) :
    S = o2aGateSide :=
  o2aGateReader.side_unique 0 S o2aGateSide hmem o2aGate_law_fires.1
    hslope o2aGate_law_fires.2

/-- III-A6c gate: the `resOrd_spec` law fires with value 1. -/
theorem o2aGate_resOrd : o2aGateReader.resOrd 0 = 1 :=
  (o2aGateReader.resOrd_spec 0).trans rfl

/-- III-A6c gate: the `rootOrd_spec` law fires with value 1. -/
theorem o2aGate_rootOrd : o2aGateReader.rootOrd = 1 :=
  o2aGateReader.rootOrd_spec.trans rfl

/-- III-A6c gate: the `resDeg_eq_sideDeg` law fires — the residual degree at
    level 0 equals the returned side's `ℓ`. -/
theorem o2aGate_resDeg :
    o2aGateData.residualDegree 0 = o2aGateSide.ℓ :=
  o2aGateReader.resDeg_eq_sideDeg 0 o2aGateSide o2aGate_side_returned

/-- III-A6c gate: the polygon is honestly non-empty at the read level — no
    `∈`-hypothesis anywhere in the gate is vacuous. -/
theorem o2aGate_principalSides_ne_nil :
    o2aGateData.principalSides 0 ≠ [] := by
  simp [o2aGateData]

/-! ## Unit III-A6b — the `GMNReader` from the order-1 polygon API (O-2a (C4) level 1; GD23 §3)

Unit III-A6b (BP_III §2 wave-2 table row, line 770): "`GMNReader` for that
data, including `side_spec`, uniqueness, and residual-degree law | prove from
the order-1 polygon API | III-A6a | HARD | O2a (C4) level 1; GD23 §3".

Adjudication of the transcription rule (division-lead review flag, per the
III-A1/III-A6c precedents above): like every wave-2 unit, III-A6b has no
§1-displayed THEOREM signature — but unlike the BLOCKED units III-A4/A7/A8,
its target TYPE is itself a §1 display: the deliverable is a term of
`GMNReader f c D` (§1.2, landed VERBATIM by unit III-C8), whose five rows —
`side_spec`, `side_unique` (the row the table calls "uniqueness"),
`resOrd_spec`, `rootOrd_spec`, `resDeg_eq_sideDeg` (the "residual-degree
law") — are exactly the laws the table row names.  Nothing at the interface
level is redeclared, weakened, or invented.

Honest dependency seam (III-A6a).  The concrete `GMNData` construction from
the `OM/` polygon modules (unit III-A6a, this unit's sole dependency) is NOT
landed at HEAD: no `GMNData` value built from the corpus polygon API exists
(probed 2026-08-01; the only landed `GMNData` instance anywhere is III-A6c's
hand-made gate datum below).  The order-1 polygon API named by the
proof-sketch column IS on record, as the NAMED §1.3 rows of
`DictIII/Hyps.lean` (unit III-H7b): `OL5` (= GD-5, at most one principal
side carries the requested slope — the uniqueness leg) and `OL3min` (= GD-3,
the residual degree reads off any principal side's ℓ — the residual-degree
law); per their docstrings the order-≥2 content of these rows routes through
`GRB`, i.e. at order ≤ 1 they are exactly what III-A6a proves outright for
its data.  This unit therefore lands the reader as the builder
`gmnReaderOrder1 : OL5 f c D → OL3min f c D → GMNReader f c D` — all five
reader laws PROVED, the two API rows consumed as HYPOTHESES (not discharged,
not axioms, per the [M]-row discipline) — so III-A6a's concrete data
instantiates it by one application at the III-A6a→III-A6c seam.

Contents:
* `sideRead` — the lookup: the first principal side carrying the requested
  slope (`List.find?` under the decidable slope test);
* `sideRead_mem_and_slope` / `sideRead_eq_some` — the two directions of
  `side_spec` (the backward direction consumes `OL5`; "first" is immaterial);
* `gmnReaderOrder1` — THE unit: `side := sideRead`, `side_spec` proved,
  `side_unique` = the `OL5` row, `resOrd`/`rootOrd` read the data with `rfl`
  specs, `resDeg_eq_sideDeg` from `OL3min`;
* `requestedSlope_eq_none` / `GMNReader.side_eq_none_of_length_le` /
  `gmnReaderOrder1_side_eq_none` — the order-1 shape: under III-A6a's
  restriction `c.slopes.length ≤ 1`, every read at `i ≥ 1` is `none` (the
  single live level is `i = 0`);
* `GMNReader.laws_pin_fields` — reader uniqueness: the laws pin every field,
  so any two readers on the same data agree on `side`, `resOrd`, `rootOrd`;
* gate tie-in `o2aGateData_OL5`/`o2aGateData_OL3min`/
  `gmnReaderOrder1_gate_side`/`gmnReaderOrder1_gate_agrees` — the builder
  fired on III-A6c's concrete order-1 data returns the side (positive
  self-test, non-vacuous) and agrees with the hand-made gate reader. -/

/-- The requested-slope test is decidable: `HasRequestedSlope c i S` is by
    definition an equality in `Option (ℕ × ℕ)`. -/
instance {c : ChainData p F} {i : ℕ} {S : SideDatum} :
    Decidable (HasRequestedSlope c i S) :=
  inferInstanceAs (Decidable (requestedSlope c i = some (S.e, S.h)))

/-- III-A6b lookup: the first principal side at level `i` carrying the
    requested slope `(e_i, h_i)`.  Under `OL5` "first" is immaterial — see
    `sideRead_eq_some`. -/
def sideRead (f : Polynomial ℤ_[p]) (c : ChainData p F) (D : GMNData f c)
    (i : ℕ) : Option SideDatum :=
  (D.principalSides i).find? fun S => decide (HasRequestedSlope c i S)

/-- `side_spec`, forward direction (no API row consumed): a returned side is
    a principal side carrying the requested slope. -/
theorem sideRead_mem_and_slope (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) {i : ℕ} {S : SideDatum}
    (h : sideRead f c D i = some S) :
    S ∈ D.principalSides i ∧ HasRequestedSlope c i S := by
  unfold sideRead at h
  have hdec := List.find?_some h
  simp only [decide_eq_true_eq] at hdec
  exact ⟨List.mem_of_find?_eq_some h, hdec⟩

/-- `side_spec`, backward direction, from the API uniqueness row `OL5`: any
    principal side carrying the requested slope IS the returned one. -/
theorem sideRead_eq_some {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (h5 : OL5 f c D) {i : ℕ} {S : SideDatum}
    (hmem : S ∈ D.principalSides i) (hslope : HasRequestedSlope c i S) :
    sideRead f c D i = some S := by
  unfold sideRead
  cases hfind : (D.principalSides i).find?
      (fun S => decide (HasRequestedSlope c i S)) with
  | none =>
      exact absurd (decide_eq_true hslope)
        (by simpa using List.find?_eq_none.mp hfind S hmem)
  | some T =>
      have hdec := List.find?_some hfind
      simp only [decide_eq_true_eq] at hdec
      exact congrArg some
        (h5 i T S (List.mem_of_find?_eq_some hfind) hmem hdec hslope)

/-- **Unit III-A6b.**  The order-≤1 `GMNReader`, built for any `GMNData`
    from the two order-1 polygon API rows: `OL5` (GD-5, uniqueness) and
    `OL3min` (GD-3, the residual-degree law).  All five reader laws are
    PROVED: `side_spec` via `sideRead`, `side_unique` is the `OL5` row
    itself, `resOrd_spec`/`rootOrd_spec` by `rfl`, `resDeg_eq_sideDeg` from
    `OL3min`.  III-A6a's concrete data instantiates this by one
    application. -/
def gmnReaderOrder1 {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (h5 : OL5 f c D) (h3 : OL3min f c D) :
    GMNReader f c D where
  side := sideRead f c D
  side_spec := fun _ _ =>
    ⟨fun h => sideRead_mem_and_slope _ _ _ h,
     fun h => sideRead_eq_some h5 h.1 h.2⟩
  side_unique := h5
  resOrd := D.residualOrder
  resOrd_spec := fun _ => rfl
  rootOrd := D.rootOrder
  rootOrd_spec := rfl
  resDeg_eq_sideDeg := fun i S h =>
    h3 i S (sideRead_mem_and_slope f c D h).1

/-- Beyond the chain length there is no requested slope. -/
theorem requestedSlope_eq_none {c : ChainData p F} {i : ℕ}
    (hi : c.slopes.length ≤ i) : requestedSlope c i = none := by
  simp [requestedSlope, List.getElem?_eq_none hi]

/-- Any lawful reader returns `none` beyond the chain length: `side_spec`
    forces it, since a returned side would carry a nonexistent requested
    slope. -/
theorem GMNReader.side_eq_none_of_length_le {f : Polynomial ℤ_[p]}
    {c : ChainData p F} {D : GMNData f c} (R : GMNReader f c D) {i : ℕ}
    (hi : c.slopes.length ≤ i) : R.side i = none := by
  cases h : R.side i with
  | none => rfl
  | some S =>
      have hslope : requestedSlope c i = some (S.e, S.h) :=
        ((R.side_spec i S).mp h).2
      rw [requestedSlope_eq_none hi] at hslope
      simp at hslope

/-- The order-1 shape of the III-A6b reader: under III-A6a's restriction
    `c.slopes.length ≤ 1`, every read at `i ≥ 1` returns `none` — the single
    live level is `i = 0`. -/
theorem gmnReaderOrder1_side_eq_none {f : Polynomial ℤ_[p]}
    {c : ChainData p F} {D : GMNData f c} (h5 : OL5 f c D)
    (h3 : OL3min f c D) (h1 : c.slopes.length ≤ 1) {i : ℕ} (hi : 1 ≤ i) :
    (gmnReaderOrder1 h5 h3).side i = none :=
  (gmnReaderOrder1 h5 h3).side_eq_none_of_length_le (h1.trans hi)

/-- Reader uniqueness (the table row's "uniqueness", reader-level face): the
    `GMNReader` laws pin every field, so any two readers on the same data
    agree on `side`, `resOrd`, and `rootOrd` — in particular
    `gmnReaderOrder1` is THE reader for its data. -/
theorem GMNReader.laws_pin_fields {f : Polynomial ℤ_[p]}
    {c : ChainData p F} {D : GMNData f c} (R R' : GMNReader f c D) :
    R.side = R'.side ∧ R.resOrd = R'.resOrd ∧ R.rootOrd = R'.rootOrd := by
  refine ⟨funext fun i => ?_,
    funext fun i => (R.resOrd_spec i).trans (R'.resOrd_spec i).symm,
    R.rootOrd_spec.trans R'.rootOrd_spec.symm⟩
  cases h : R'.side i with
  | none =>
      cases h' : R.side i with
      | none => rfl
      | some S =>
          have : R'.side i = some S :=
            (R'.side_spec i S).mpr ((R.side_spec i S).mp h')
          rw [h] at this
          simp at this
  | some S =>
      exact (R.side_spec i S).mpr ((R'.side_spec i S).mp h)

/-- III-A6c's gate data satisfies the `OL5` API row (uniqueness leg). -/
theorem o2aGateData_OL5 :
    OL5 (Polynomial.X : Polynomial ℤ_[2]) o2aGateChain o2aGateData := by
  intro i S T hS hT _ _
  have hS' : S = o2aGateSide := by simpa [o2aGateData] using hS
  have hT' : T = o2aGateSide := by simpa [o2aGateData] using hT
  rw [hS', hT']

/-- III-A6c's gate data satisfies the `OL3min` API row (residual-degree
    law). -/
theorem o2aGateData_OL3min :
    OL3min (Polynomial.X : Polynomial ℤ_[2]) o2aGateChain o2aGateData := by
  intro i S hS
  have hS' : S = o2aGateSide := by simpa [o2aGateData] using hS
  rw [hS']
  rfl

/-- Positive self-test of the III-A6b builder on III-A6c's concrete order-1
    data: the built reader RETURNS the gate side at level 0 — the builder's
    laws are non-vacuous on genuine data. -/
theorem gmnReaderOrder1_gate_side :
    (gmnReaderOrder1 o2aGateData_OL5 o2aGateData_OL3min).side 0 =
      some o2aGateSide := by
  show sideRead (Polynomial.X : Polynomial ℤ_[2]) o2aGateChain o2aGateData 0 =
    some o2aGateSide
  exact sideRead_eq_some o2aGateData_OL5 (S := o2aGateSide)
    (by simp [o2aGateData]) rfl

/-- The III-A6b builder agrees with III-A6c's hand-made gate reader on every
    read — the two units meet at the gate, as `laws_pin_fields` predicts. -/
theorem gmnReaderOrder1_gate_agrees :
    (gmnReaderOrder1 o2aGateData_OL5 o2aGateData_OL3min).side =
      o2aGateReader.side :=
  ((gmnReaderOrder1 o2aGateData_OL5 o2aGateData_OL3min).laws_pin_fields
    o2aGateReader).1

/-! ## Unit III-A9 — the OL-6 order-≤1 instance probe (run decomposition +
chain binding at one node)

Unit III-A9 (BP_III §2 wave-2 table row, line 774): "OL-6 order-≤1 instance
probe (run decomposition + chain binding at one node) | quarry
`U19_runCoherent`/`U24_runCanon`; gate-style | III-H7c, corpus HC2 | MED |
O2a §4 OL-6; CU1 §0′".

Adjudication of the transcription rule (division-lead review flag, per the
III-A6c precedent above): III-A9 has NO §1-displayed signature, and like
III-A6c it is a GATE row — the §2 proof-sketch column is the specification,
and the object the unit instantiates is the landed III-H7c row `OL6`
(`DictIII/Hyps.lean`), consumed VERBATIM and not redeclared.  The quarry
`U19_runCoherent`/`U24_runCanon` (BP §3.3: "pattern for III-A9 (OL-6
order-≤1 probe)") is the HC2 PROJECTION pattern — `readsOf_coherent`/
`readsOf_canonical` project a recorded conjunct out of the run predicate
and read a law off it; the binding leg below does exactly that at `ConsF`.
Dependency note: corpus HC2 enters as the proof-pattern quarry only (per
§3.3) — no HC2 declaration is consumed; `OL6`'s carrier layer
(III-C5/C8/C9, III-H7c) is landed.

Gate content (all sorry-free, Lean-core expected):
* `ol6_of_consF` — run decomposition + chain binding, the general leg: a
  `ConsF` binding (O-2a (C4)) yields `OL6` at `Theta H` outright — the run
  returns a side at every requested level (run decomposition), and the
  reader law `side_spec` binds it into the polygon's principal-side list
  (chain binding);
* `ol6_at_o2aGate` — OL-6 fired directly at the landed III-A6c order-1
  carrier (`o2aGateChain`/`o2aGateData`/`o2aGateReader`);
* the one-node run gate: `ol6GateNode`/`ol6GateHist` (a ONE-continuing-node
  𝔈-history at `p = 2`, order ≤ 1), `ol6GateData`/`ol6GateReader` over the
  run's chain `Theta ol6GateHist`, the compiled binding `ol6Gate_consF` at
  that node, and the fired instance `ol6Gate_fired` with its non-vacuity
  displays (`ol6Gate_slopes_length`, `ol6Gate_side_returned`,
  `ol6Gate_conclusion_fires`): the `OL6` quantifier genuinely fires at
  level 0.  Satisfiability certificate ONLY (D-R2/D-R3 caveat, as at the
  III-A6c and `gd3_min_gate` precedents). -/

/-- III-A9, binding leg (run decomposition + chain binding): a `ConsF`
    binding returns a side at every requested level of `Theta H` — the
    level count of `Theta H` is the continuing-node count, the run clause
    of `ConsF` returns THE side at each such node (run decomposition), and
    the reader law `side_spec` reads that side back into the principal-side
    list (chain binding) — so the landed III-H7c row `OL6` holds outright
    at any `ConsF` binding.  Proof pattern quarried from the HC2
    `U19_runCoherent`/`U24_runCanon` projections (project the recorded
    conjunct out of the run predicate, then read the law off it). -/
theorem ol6_of_consF {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hcons : ConsF f H D R) : OL6 f (Theta H) D R := by
  intro i hi
  obtain ⟨-, hbind⟩ := (hcons : _ ∧ _)
  have hlen : i < H.continuingPart.nodes.length := by
    have hmap : (Theta H).slopes.length = H.continuingPart.nodes.length := by
      simp [Theta]
    omega
  obtain ⟨S, hS, -, -⟩ :=
    hbind i (H.continuingPart.nodes[i]'hlen) (List.getElem?_eq_getElem hlen)
  exact ⟨S, hS, ((R.side_spec i S).mp hS).1⟩

/-- III-A9: OL-6 fired directly at the landed III-A6c order-1 carrier — the
    reader returns a principal side at the (unique) requested level. -/
theorem ol6_at_o2aGate :
    OL6 (Polynomial.X : Polynomial ℤ_[2]) o2aGateChain o2aGateData
      o2aGateReader := by
  intro i hi
  have h1 : o2aGateChain.slopes.length = 1 := rfl
  have hi' : i = 0 := by omega
  subst hi'
  exact ⟨o2aGateSide, o2aGate_side_returned, o2aGate_law_fires.1⟩

/-- The gate's single node ν = (e,h,ℓ,s,u,sel,inc)
    = (1,1,1,0,0, some (1,1), false): continuing (`sel ≠ none`, so `Theta`
    keeps it), a T4 row, W1b/W2-consistent (e·g = 1 < 2 forces
    `inc = false`), carrier laws discharged concretely. -/
def ol6GateNode : ENodeData where
  e := 1
  h := 1
  ℓ := 1
  s := 0
  u := 0
  sel := some (1, 1)
  inc := false
  he := le_rfl
  hh := le_rfl
  hcop := Nat.gcd_self 1
  hl := le_rfl
  hsel := by
    rintro gμ hgμ
    obtain rfl : ((1 : ℕ), (1 : ℕ)) = gμ := by simpa using hgμ
    decide

/-- The gate's one-node 𝔈-history at `p = 2`: base/tower = the top subfield
    of `ZMod 2` at every level, root datum ψ̂₀ = `o2aGatePoly` with a₀ = 1,
    constant dressing `o2aGatePoly` (monic, irreducible, ≠ X — the landed
    III-A6c lemmas), single continuing node `ol6GateNode`. -/
noncomputable def ol6GateHist : EHist 2 (ZMod 2) where
  base := ⊤
  psi0 := o2aGatePoly
  hpsi0 := ⟨o2aGatePoly_monic, o2aGatePoly_irreducible⟩
  a0 := 1
  ha0 := le_rfl
  nodes := [ol6GateNode]
  fld := fun _ => ⊤
  psihat := fun _ => o2aGatePoly
  hpsihat := fun _ =>
    ⟨o2aGatePoly_monic, o2aGatePoly_irreducible, o2aGatePoly_ne_X⟩

/-- III-A9 gate, order-≤1 restriction: the run's chain `Theta ol6GateHist`
    has EXACTLY one requested level — the single node is continuing, so
    `Theta` keeps it. -/
theorem ol6Gate_slopes_length : (Theta ol6GateHist).slopes.length = 1 := rfl

/-- The gate's semantic GMN datum over `f = X ∈ ℤ_[2][x]`, keyed to the
    run's chain `Theta ol6GateHist`: one principal side (`o2aGateSide`,
    matching `ol6GateNode` fieldwise) per level, residual order/degree 1,
    root order 1 = `ol6GateHist.a0`. -/
def ol6GateData :
    GMNData (Polynomial.X : Polynomial ℤ_[2]) (Theta ol6GateHist) where
  principalSides := fun _ => [o2aGateSide]
  residualOrder := fun _ => 1
  residualDegree := fun _ => 1
  rootOrder := 1

/-- III-A9: the reader for `ol6GateData` — `side` answers at level 0
    exactly; all five `GMNReader` laws are PROVED from the concrete data
    (the III-A6c reader pattern, re-keyed to the run's chain
    `Theta ol6GateHist`). -/
def ol6GateReader :
    GMNReader (Polynomial.X : Polynomial ℤ_[2]) (Theta ol6GateHist)
      ol6GateData where
  side := fun i => if i = 0 then some o2aGateSide else none
  side_spec := by
    intro i S
    cases i with
    | zero =>
      constructor
      · intro h
        have h' : some o2aGateSide = some S := h
        injection h' with hS
        subst hS
        exact ⟨by simp [ol6GateData], rfl⟩
      · rintro ⟨hmem, -⟩
        have hS : S = o2aGateSide := by simpa [ol6GateData] using hmem
        simp [hS]
    | succ n =>
      constructor
      · intro h
        simp at h
      · rintro ⟨-, hslope⟩
        have hcontra : (none : Option (ℕ × ℕ)) = some (S.e, S.h) := hslope
        exact Option.noConfusion hcontra
  side_unique := by
    intro i S T hS hT _ _
    have hS' : S = o2aGateSide := by simpa [ol6GateData] using hS
    have hT' : T = o2aGateSide := by simpa [ol6GateData] using hT
    rw [hS', hT']
  resOrd := fun _ => 1
  resOrd_spec := fun _ => rfl
  rootOrd := 1
  rootOrd_spec := rfl
  resDeg_eq_sideDeg := by
    intro i S h
    cases i with
    | zero =>
      have h' : some o2aGateSide = some S := h
      injection h' with hS
      subst hS
      rfl
    | succ n =>
      simp at h

/-- III-A9, the compiled binding at the gate's one node (O-2a (C4)): the
    root order ties (`rootOrd = a₀ = 1`), and at level 0 the run returns
    `o2aGateSide`, whose (e,h,ℓ,s,u) matches `ol6GateNode` fieldwise, with
    `resOrd 0 = μ = 1`. -/
theorem ol6Gate_consF :
    ConsF (Polynomial.X : Polynomial ℤ_[2]) ol6GateHist ol6GateData
      ol6GateReader := by
  refine (⟨rfl, ?_⟩ : _ ∧ _)
  intro i ν hν
  have hnodes : ol6GateHist.continuingPart.nodes = [ol6GateNode] := rfl
  rw [hnodes] at hν
  cases i with
  | zero =>
    rw [List.getElem?_cons_zero] at hν
    injection hν with hν'
    subst hν'
    refine ⟨o2aGateSide, rfl, rfl, ?_⟩
    intro g μ hgμ
    have h : some ((1 : ℕ), (1 : ℕ)) = some (g, μ) := hgμ
    injection h with h'
    injection h' with _h1 h2
    subst h2
    rfl
  | succ n =>
    simp at hν

/-- Unit III-A9 gate, FIRED: `OL6` (the landed III-H7c row) holds at the
    compiled one-node run instance — the binding leg `ol6_of_consF` applied
    to the compiled binding `ol6Gate_consF`. -/
theorem ol6Gate_fired :
    OL6 (Polynomial.X : Polynomial ℤ_[2]) (Theta ol6GateHist) ol6GateData
      ol6GateReader :=
  ol6_of_consF ol6Gate_consF

/-- III-A9 non-vacuity display: the run's reader really returns THE side at
    level 0 — the fired `OL6` is not vacuously satisfied. -/
theorem ol6Gate_side_returned :
    ol6GateReader.side 0 = some o2aGateSide := rfl

/-- III-A9 non-vacuity display: the fired `OL6` conclusion at level 0,
    extracted from the gate — the ∃ is inhabited, machine-checked. -/
theorem ol6Gate_conclusion_fires :
    ∃ S, ol6GateReader.side 0 = some S ∧
      S ∈ ol6GateData.principalSides 0 :=
  ol6Gate_fired 0 (by rw [ol6Gate_slopes_length]; exact Nat.zero_lt_one)

end LeanUrat.Scaffold.DictIII

-- Footprint audit (unit III-A1 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.recoverNode
#print axioms LeanUrat.Scaffold.DictIII.recoverEHist

-- Footprint audit (unit III-A6c gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.o2aGateReader
#print axioms LeanUrat.Scaffold.DictIII.o2aGate_side_returned
#print axioms LeanUrat.Scaffold.DictIII.o2aGate_law_fires

-- Footprint audit (unit III-A6b): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.gmnReaderOrder1
#print axioms LeanUrat.Scaffold.DictIII.gmnReaderOrder1_side_eq_none
#print axioms LeanUrat.Scaffold.DictIII.GMNReader.laws_pin_fields
#print axioms LeanUrat.Scaffold.DictIII.gmnReaderOrder1_gate_side
#print axioms LeanUrat.Scaffold.DictIII.gmnReaderOrder1_gate_agrees

-- Footprint audit (unit III-A9): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.ol6_of_consF
#print axioms LeanUrat.Scaffold.DictIII.ol6_at_o2aGate
#print axioms LeanUrat.Scaffold.DictIII.ol6Gate_fired
#print axioms LeanUrat.Scaffold.DictIII.ol6Gate_conclusion_fires
