/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.OM.ResidualPolynomial

/-!
# Scaffold/DictIII/O2aOrder1 — O-2a §§2/3/5 order-≤1 layer (BP_III units III-A1, III-A4, III-A6a, III-A6b, III-A6c, III-A7, III-A8, III-A9)

BLOCKED-record file (prover III-A4, 2026-08-01; prover III-A7, 2026-08-01;
prover III-A8, 2026-08-01)
EXTENDED with the landed unit III-A1 (prover III-A1, 2026-08-01:
`recoverNode`/`recoverEHist`, the Lemma R recovery map — see the section
header below the BLOCKED records), the landed unit III-A6c (prover
III-A6c, 2026-08-01: the positive order-1 reader gate `o2aGate*`), and the
landed unit III-A6b (prover III-A6b, 2026-08-01: `sideRead`/`gmnReaderOrder1`
+ the reader-law and reader-uniqueness lemmas — the `GMNReader` construction
from the order-1 polygon API rows `OL5`/`OL3min`;
its section header records the honest III-A6a dependency seam), the
landed unit III-A9 (prover III-A9, 2026-08-01: the OL-6 order-≤1 instance
probe — binding leg `ol6_of_consF` + the one-node run gate `ol6Gate*`), and
the landed unit III-A6a (prover III-A6a, 2026-08-01: `gmnDataOrder1` — the
`GMNData` construction from the corpus polygon API (`npSides` over
`valSupport` + `residualPoly`/`residualDeg`) restricted by
`c.slopes.length ≤ 1`, with the ι-parameters and the `sideRead` coherence
seam recorded in its section header, last section of this file; this CLOSES
the III-A6b seam note).  The BLOCKED units III-A4 (pre-split
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
        simp at hcontra
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
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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

/-! ## Unit III-A3 — Lemma R terminal NON-recovery: the compiled two-witness gate
((1,1,1,0,0,⊥,0) vs (1,2,1,0,0,⊥,0))

Unit III-A3 (BP_III §2 wave-2 table row, line 766): "Lemma R terminal
NON-recovery: compiled two-witness gate ((1,1,1,0,0,⊥,0) vs (1,2,1,0,0,⊥,0))
| `decide`-style witness pair | III-C9 | MECH | O2a §2 Lemma R pf end".
Style template (BP §3.5): `U1_negWitness`/`retiredKeysExist_false` — the
compiled negation-witness STYLE is imitated, never the content.

Adjudication of the transcription rule (division-lead review flag, per the
III-A1/III-A6c/III-A9 precedents above): like every wave-2 unit, III-A3 has
NO §1-displayed signature — but like III-A6c/III-A9 it is a GATE, whose §2
row IS the specification (the two witness tuples are displayed IN the row),
and whose source display is the Lemma R proof end
(O2a_phaseB_verifybrief_rev5.md §2):

  "Non-recovery of a terminal node: if ν = (e, h, ℓ, s, u, ⊥, inc) is
  terminal and (𝐇°; ν) is well-formed and Cons_f, then so is (𝐇°; ν′) for
  ANY other well-formed terminal ν′ — e.g. ν = (1,1,1,0,0,⊥,0) vs
  ν′ = (1,2,1,0,0,⊥,0) — since W1/W2/W4 constrain only sel ≠ ⊥ nodes,
  W3/W5 see only the position, and Cons_f constrains no terminal field;
  both have image Θ(𝐇°)."

Every clause of the quote is compiled, over the landed III-C1/C2b/C3/C6b/C9
carriers VERBATIM (nothing redeclared or weakened at the interface level):

* `nuT1`, `nuT2` — THE WITNESS PAIR, `decide`-style Prop rows;
  `nuT1_ne_nuT2` (distinct), `nuT1_isT5`/`nuT2_isT5` (terminal).
* `snocTerm` — the (𝐇°; ν) surgery: append one node record.
* `theta_snocTerm` / `theta_snocTerm_pair` / `snocTerm_pair_ne` — "both have
  image Θ(𝐇°)": Θ discards the appended terminal node, so the two DISTINCT
  extensions collide.
* `ewf_snocTerm_congr` — "W1/W2/W4 constrain only sel ≠ ⊥ nodes, W3/W5 see
  only the position": `EWF` of (𝐇°; ν) transports to (𝐇°; ν′), any terminal
  ν, ν′ (machine-checked terminal-field independence).
* `consF_snocTerm_congr` / `consF_snocTerm_exists` — "Cons_f constrains no
  terminal field": a `ConsF` witness for (𝐇°; ν) yields one for (𝐇°; ν′).
* `TerminalRecoveryStmt` — the over-claim Lemma R explicitly does NOT make
  (its displayed NON-claim): a recovery map `(f, Θ(𝐇)) ↦ 𝐇` on well-formed
  `ConsF` histories INCLUDING those with a terminal last node.  (Lemma R's
  true claim — unit III-A2 — restricts to 𝔈°_f, every node continuing;
  nothing here weakens it.)
* `terminalRecovery_false_of_witness` — the gate fires from ANY inhabitant
  of the witness class.
* `A3Gate.terminalRecovery_false` — THE DISCHARGE, unconditional at p = 2,
  F = ZMod 2: the class is inhabited concretely (root-only 𝐇° with a₀ = 2
  over the top subfield, dressing `o2aGatePoly`; empty-polygon reader), so
  `¬ TerminalRecoveryStmt 2 (ZMod 2)` holds outright — no honesty perimeter
  left open.  Expected footprint: Lean core only (audited at the foot). -/

/-- `takeWhile` ignores an appended element that fails the predicate
    (III-A3 helper). -/
private theorem takeWhile_concat_of_neg {α : Type*} {P : α → Bool} {a : α}
    (ha : P a = false) : ∀ l : List α, (l ++ [a]).takeWhile P = l.takeWhile P
  | [] => by simp [List.takeWhile_cons, ha]
  | x :: xs => by
    by_cases hx : P x
    · simp [List.takeWhile_cons, hx, takeWhile_concat_of_neg ha xs]
    · simp [List.takeWhile_cons, hx]

/-- A successful lookup in `l ++ [a]` is a lookup in `l`, or the appended `a`
    (III-A3 helper). -/
private theorem concat_lookup {α : Type*} {l : List α} {a : α} {i : ℕ} {x : α}
    (h : (l ++ [a])[i]? = some x) :
    l[i]? = some x ∨ (i = l.length ∧ x = a) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · left
    rwa [List.getElem?_append_left hi] at h
  · right
    rw [List.getElem?_append_right hi] at h
    rcases hk : i - l.length with _ | j
    · rw [hk] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨by omega, h.symm⟩
    · rw [hk] at h
      simp at h

/-- A successful lookup in `l` survives appending (III-A3 helper). -/
private theorem concat_lookup_left {α : Type*} {l : List α} {a : α} {i : ℕ}
    {x : α} (h : l[i]? = some x) : (l ++ [a])[i]? = some x := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp h).1
  rwa [List.getElem?_append_left hi]

/-- First witness of the III-A3 pair: ν = (e,h,ℓ,s,u,sel,inc)
    = (1,1,1,0,0,⊥,0). -/
def nuT1 : ENodeData :=
  { e := 1, h := 1, ℓ := 1, s := 0, u := 0, sel := none, inc := false
    he := by decide
    hh := by decide
    hcop := by decide
    hl := by decide
    hsel := by simp }

/-- Second witness: ν′ = (1,2,1,0,0,⊥,0) — differs from `nuT1` only in `h`. -/
def nuT2 : ENodeData :=
  { e := 1, h := 2, ℓ := 1, s := 0, u := 0, sel := none, inc := false
    he := by decide
    hh := by decide
    hcop := by decide
    hl := by decide
    hsel := by simp }

/-- Both witnesses are terminal (row T5: `sel = none`). -/
theorem nuT1_isT5 : nuT1.isT5 := rfl

theorem nuT2_isT5 : nuT2.isT5 := rfl

/-- The witnesses are DISTINCT (they differ in the `h` field: 1 ≠ 2). -/
theorem nuT1_ne_nuT2 : nuT1 ≠ nuT2 := by
  intro h
  exact absurd (congrArg ENodeData.h h) (by decide)

/-- The (𝐇°; ν) surgery: append one node record to a history. -/
def snocTerm (H : EHist p F) (ν : ENodeData) : EHist p F :=
  { H with nodes := H.nodes ++ [ν] }

/-- The appended node IS the last node of the extended history. -/
theorem snocTerm_getLast (H : EHist p F) (ν : ENodeData) :
    (snocTerm H ν).nodes.getLast? = some ν :=
  List.getLast?_concat

/-- Appending a TERMINAL node does not change the continuing part 𝐇°. -/
theorem continuingPart_snocTerm (H : EHist p F) {ν : ENodeData}
    (hν : ν.sel = none) : (snocTerm H ν).continuingPart = H.continuingPart :=
  congrArg (fun l => ({ H with nodes := l } : EHist p F))
    (takeWhile_concat_of_neg (by rw [hν]; rfl) H.nodes)

/-- "Both have image Θ(𝐇°)": Θ discards an appended terminal node. -/
theorem theta_snocTerm (H : EHist p F) {ν : ENodeData} (hν : ν.sel = none) :
    Theta (snocTerm H ν) = Theta H := by
  rw [theta_continuing (snocTerm H ν), continuingPart_snocTerm H hν,
    ← theta_continuing H]

/-- THE Θ-COLLISION at the witness pair: (𝐇°; nuT1) and (𝐇°; nuT2) have the
    same Θ image, for EVERY history 𝐇°. -/
theorem theta_snocTerm_pair (H : EHist p F) :
    Theta (snocTerm H nuT1) = Theta (snocTerm H nuT2) := by
  rw [theta_snocTerm H (rfl : nuT1.sel = none),
    theta_snocTerm H (rfl : nuT2.sel = none)]

/-- The two extended histories are DISTINCT (the appended nodes differ). -/
theorem snocTerm_pair_ne (H : EHist p F) :
    snocTerm H nuT1 ≠ snocTerm H nuT2 := by
  intro h
  have hn : H.nodes ++ [nuT1] = H.nodes ++ [nuT2] := congrArg EHist.nodes h
  have h1 : ([nuT1] : List ENodeData) = [nuT2] := List.append_cancel_left hn
  injection h1 with h2 _
  exact nuT1_ne_nuT2 h2

/-- "W1/W2/W4 constrain only sel ≠ ⊥ nodes, W3/W5 see only the position":
    well-formedness of (𝐇°; ν) transports to (𝐇°; ν′) for ANY terminal
    ν, ν′ — the machine-checked terminal-field independence of `EWF`. -/
theorem ewf_snocTerm_congr (H : EHist p F) {ν ν' : ENodeData}
    (hν : ν.sel = none) (hν' : ν'.sel = none)
    (hwf : EWF (snocTerm H ν)) : EWF (snocTerm H ν') := by
  -- lookup transport: (𝐇°; ν′)-lookups are 𝐇°-lookups or the appended ν′;
  -- 𝐇°-lookups transport into (𝐇°; ν).
  have toNu : ∀ {i : ℕ} {μ : ENodeData}, H.nodes[i]? = some μ →
      (snocTerm H ν).nodes[i]? = some μ := fun h => concat_lookup_left h
  have split : ∀ {i : ℕ} {μ : ENodeData}, (snocTerm H ν').nodes[i]? = some μ →
      H.nodes[i]? = some μ ∨ (i = H.nodes.length ∧ μ = ν') :=
    fun h => concat_lookup h
  have hlen : (snocTerm H ν').nodes.length = H.nodes.length + 1 := by
    simp [snocTerm]
  have hlen' : (snocTerm H ν).nodes.length = H.nodes.length + 1 := by
    simp [snocTerm]
  refine { w1a := ?_, w1b := ?_, w2 := ?_, w3 := ⟨?_, ?_⟩, w5 := ?_,
           w4dress := ?_, towerBase := hwf.towerBase,
           towerStep := hwf.towerStep,
           towerBaseDegree := hwf.towerBaseDegree, towerStepDegree := ?_ }
  · intro i μ hg hsel hl he2
    rcases split hg with hg' | ⟨-, rfl⟩
    · exact hwf.w1a i μ (toNu hg') hsel hl he2
    · exact absurd hν' hsel
  · intro i μ hg hsel hl he1
    rcases split hg with hg' | ⟨-, rfl⟩
    · exact hwf.w1b i μ (toNu hg') hsel hl he1
    · exact absurd hν' hsel
  · intro i μ g m hg hsel
    rcases split hg with hg' | ⟨-, rfl⟩
    · exact hwf.w2 i μ g m (toNu hg') hsel
    · rw [hν'] at hsel
      exact Option.noConfusion hsel
  · intro i μ hi hg gμ hmem
    rw [hlen] at hi
    rcases split hg with hg' | ⟨heq, rfl⟩
    · have hi' : i + 1 < (snocTerm H ν).nodes.length := by
        rw [hlen']
        omega
      exact hwf.w3.1 i μ hi' (toNu hg') gμ hmem
    · omega
  · intro _
    refine hwf.w3.2 ?_
    intro h0
    exact absurd (congrArg List.length h0) (by simp [snocTerm])
  · intro i μ hi hg
    rw [hlen] at hi
    rcases split hg with hg' | ⟨heq, rfl⟩
    · have hi' : i + 1 < (snocTerm H ν).nodes.length := by
        rw [hlen']
        omega
      exact hwf.w5 i μ hi' (toNu hg')
    · omega
  · intro i μ g m hg hsel
    rcases split hg with hg' | ⟨-, rfl⟩
    · exact hwf.w4dress i μ g m (toNu hg') hsel
    · rw [hν'] at hsel
      exact Option.noConfusion hsel
  · intro i μ g m hg hsel
    rcases split hg with hg' | ⟨-, rfl⟩
    · exact hwf.towerStepDegree i μ g m (toNu hg') hsel
    · rw [hν'] at hsel
      exact Option.noConfusion hsel

/-- "Cons_f constrains no terminal field": `ConsF` reads only the reader's
    DATA fields (`side`, `resOrd`, `rootOrd`), the root multiplicity `a0`,
    and the CONTINUING part — all invariant under swapping the appended
    terminal node.  Stated cast-free over any two readers with equal data
    fields. -/
theorem consF_snocTerm_congr (f : Polynomial ℤ_[p]) (H : EHist p F)
    {ν ν' : ENodeData} (hν : ν.sel = none) (hν' : ν'.sel = none)
    {D : GMNData f (Theta (snocTerm H ν))}
    {R : GMNReader f (Theta (snocTerm H ν)) D}
    {D' : GMNData f (Theta (snocTerm H ν'))}
    {R' : GMNReader f (Theta (snocTerm H ν')) D'}
    (hside : R'.side = R.side) (hres : R'.resOrd = R.resOrd)
    (hroot : R'.rootOrd = R.rootOrd)
    (hc : ConsF f (snocTerm H ν) D R) : ConsF f (snocTerm H ν') D' R' := by
  obtain ⟨h0, h1⟩ := hc
  refine ⟨by rw [hroot]; exact h0, ?_⟩
  intro i μ hg
  rw [continuingPart_snocTerm H hν'] at hg
  have hg' : (snocTerm H ν).continuingPart.nodes[i]? = some μ := by
    rw [continuingPart_snocTerm H hν]
    exact hg
  obtain ⟨S, hS, hfields, hresid⟩ := h1 i μ hg'
  exact ⟨S, by rw [hside]; exact hS, hfields,
    fun g m hsel => by rw [hres]; exact hresid g m hsel⟩

/-- Transport a (data, reader) pair along an equality of chain data
    (III-A3 helper). -/
private def readerTransport {f : Polynomial ℤ_[p]} {c c' : ChainData p F}
    (h : c = c') {D : GMNData f c} (R : GMNReader f c D) :
    Σ' D' : GMNData f c', GMNReader f c' D' := by
  subst h
  exact ⟨D, R⟩

private theorem readerTransport_side {f : Polynomial ℤ_[p]}
    {c c' : ChainData p F} (h : c = c') {D : GMNData f c}
    (R : GMNReader f c D) : (readerTransport h R).2.side = R.side := by
  cases h; rfl

private theorem readerTransport_resOrd {f : Polynomial ℤ_[p]}
    {c c' : ChainData p F} (h : c = c') {D : GMNData f c}
    (R : GMNReader f c D) : (readerTransport h R).2.resOrd = R.resOrd := by
  cases h; rfl

private theorem readerTransport_rootOrd {f : Polynomial ℤ_[p]}
    {c c' : ChainData p F} (h : c = c') {D : GMNData f c}
    (R : GMNReader f c D) : (readerTransport h R).2.rootOrd = R.rootOrd := by
  cases h; rfl

/-- Existential form of terminal-field blindness: a `ConsF` witness for
    (𝐇°; ν) yields one for (𝐇°; ν′), any terminal ν, ν′. -/
theorem consF_snocTerm_exists (f : Polynomial ℤ_[p]) (H : EHist p F)
    {ν ν' : ENodeData} (hν : ν.sel = none) (hν' : ν'.sel = none)
    {D : GMNData f (Theta (snocTerm H ν))}
    {R : GMNReader f (Theta (snocTerm H ν)) D}
    (hc : ConsF f (snocTerm H ν) D R) :
    ∃ (D' : GMNData f (Theta (snocTerm H ν')))
      (R' : GMNReader f (Theta (snocTerm H ν')) D'),
      ConsF f (snocTerm H ν') D' R' := by
  have hθ : Theta (snocTerm H ν) = Theta (snocTerm H ν') := by
    rw [theta_snocTerm H hν, theta_snocTerm H hν']
  exact ⟨(readerTransport hθ R).1, (readerTransport hθ R).2,
    consF_snocTerm_congr f H hν hν' (readerTransport_side hθ R)
      (readerTransport_resOrd hθ R) (readerTransport_rootOrd hθ R) hc⟩

/-- The OVER-claim Lemma R explicitly does NOT make (its displayed NON-claim,
    O2a r5 §2): a recovery map `(f, Θ(𝐇)) ↦ 𝐇` defined on well-formed `ConsF`
    histories INCLUDING those with a terminal last node.  (Lemma R's true
    claim — unit III-A2 — restricts to 𝔈°_f, every node continuing.) -/
def TerminalRecoveryStmt (p : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Finite F] : Prop :=
  ∃ recover : Polynomial ℤ_[p] → ChainData p F → EHist p F,
    ∀ (f : Polynomial ℤ_[p]) (H : EHist p F), EWF H →
      (∃ (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D),
        ConsF f H D R) →
      (∃ ν, H.nodes.getLast? = some ν ∧ ν.sel = none) →
      recover f (Theta H) = H

/-- **THE TWO-WITNESS GATE** (unit III-A3): given ANY 𝐇° whose
    nuT1-extension is well-formed and `ConsF`, the terminal-recovery
    over-claim is FALSE — (𝐇°; nuT1) and (𝐇°; nuT2) are distinct members of
    the recovery class with the same Θ image, so no recovery map splits Θ
    there. -/
theorem terminalRecovery_false_of_witness (H : EHist p F)
    (f : Polynomial ℤ_[p]) (hwf : EWF (snocTerm H nuT1))
    (D : GMNData f (Theta (snocTerm H nuT1)))
    (R : GMNReader f (Theta (snocTerm H nuT1)) D)
    (hc : ConsF f (snocTerm H nuT1) D R) : ¬ TerminalRecoveryStmt p F := by
  rintro ⟨recover, hrec⟩
  have h1 : recover f (Theta (snocTerm H nuT1)) = snocTerm H nuT1 :=
    hrec f (snocTerm H nuT1) hwf ⟨D, R, hc⟩
      ⟨nuT1, snocTerm_getLast H nuT1, rfl⟩
  have h2 : recover f (Theta (snocTerm H nuT2)) = snocTerm H nuT2 :=
    hrec f (snocTerm H nuT2)
      (ewf_snocTerm_congr H rfl rfl hwf)
      (consF_snocTerm_exists f H rfl rfl hc)
      ⟨nuT2, snocTerm_getLast H nuT2, rfl⟩
  rw [theta_snocTerm_pair H] at h1
  exact snocTerm_pair_ne H (h1.symm.trans h2)

namespace A3Gate

/-- The concrete 𝐇° of the discharge: root-only (no nodes), a₀ = 2 (so the
    W3 root law holds after appending), everything over the top subfield of
    `ZMod 2`; root datum and dressing both `o2aGatePoly = X + 1` (monic,
    irreducible, ≠ X — the landed III-A6c lemmas). -/
noncomputable def H0 : EHist 2 (ZMod 2) :=
  { base := ⊤
    psi0 := o2aGatePoly
    hpsi0 := ⟨o2aGatePoly_monic, o2aGatePoly_irreducible⟩
    a0 := 2
    ha0 := one_le_two
    nodes := []
    fld := fun _ => ⊤
    psihat := fun _ => o2aGatePoly
    hpsihat := fun _ =>
      ⟨o2aGatePoly_monic, o2aGatePoly_irreducible, o2aGatePoly_ne_X⟩ }

/-- Every node of (𝐇⁰; nuT1) is nuT1. -/
private theorem mem_snoc0 {μ : ENodeData} {i : ℕ}
    (hg : (snocTerm H0 nuT1).nodes[i]? = some μ) : μ = nuT1 := by
  have hg' : (([] : List ENodeData) ++ [nuT1])[i]? = some μ := hg
  rcases concat_lookup hg' with h | ⟨-, rfl⟩
  · simp at h
  · rfl

/-- (𝐇⁰; nuT1) is well-formed: W1/W2/W4 are vacuous at the terminal node,
    W3/W5 see no interior position, a₀ = 2 meets the root law, and the
    constant-⊤ tower satisfies the degree laws (deg ψ̂₀ = 1). -/
theorem hwf0 : EWF (snocTerm H0 nuT1) := by
  refine { w1a := ?_, w1b := ?_, w2 := ?_, w3 := ⟨?_, fun _ => le_refl 2⟩,
           w5 := ?_, w4dress := ?_, towerBase := le_refl _,
           towerStep := fun _ => le_refl _, towerBaseDegree := ?_,
           towerStepDegree := ?_ }
  · intro i μ hg hsel _ _
    cases mem_snoc0 hg
    exact absurd rfl hsel
  · intro i μ hg hsel _ _
    cases mem_snoc0 hg
    exact absurd rfl hsel
  · intro i μ g m hg hsel
    cases mem_snoc0 hg
    have hcontra : (none : Option (ℕ × ℕ)) = some (g, m) := hsel
    exact Option.noConfusion hcontra
  · intro i μ hi _ _ _
    have h1 : i + 1 < 1 := hi
    omega
  · intro i μ hi _
    have h1 : i + 1 < 1 := hi
    omega
  · intro i μ g m hg hsel
    cases mem_snoc0 hg
    have hcontra : (none : Option (ℕ × ℕ)) = some (g, m) := hsel
    exact Option.noConfusion hcontra
  · show Nat.card ↥(⊤ : Subfield (ZMod 2)) =
      Nat.card ↥(⊤ : Subfield (ZMod 2)) ^ o2aGatePoly.natDegree
    rw [show o2aGatePoly.natDegree = 1 from Polynomial.natDegree_X_add_C 1,
      pow_one]
  · intro i μ g m hg hsel
    cases mem_snoc0 hg
    have hcontra : (none : Option (ℕ × ℕ)) = some (g, m) := hsel
    exact Option.noConfusion hcontra

/-- Any concrete polynomial serves; the empty-polygon reader below never
    consults it. -/
noncomputable def f0 : Polynomial ℤ_[2] := Polynomial.X

/-- Empty-polygon GMN data with root order 2 (= a₀ of 𝐇⁰). -/
noncomputable def D0 : GMNData f0 (Theta (snocTerm H0 nuT1)) :=
  { principalSides := fun _ => []
    residualOrder := fun _ => 0
    residualDegree := fun _ => 0
    rootOrder := 2 }

/-- The trivial reader for the empty polygon: all laws hold vacuously. -/
noncomputable def R0 : GMNReader f0 (Theta (snocTerm H0 nuT1)) D0 :=
  { side := fun _ => none
    side_spec := by
      intro i S
      constructor
      · intro h
        exact Option.noConfusion h
      · rintro ⟨hS, -⟩
        exact absurd hS List.not_mem_nil
    side_unique := by
      intro i S T hS _ _ _
      exact absurd hS List.not_mem_nil
    resOrd := fun _ => 0
    resOrd_spec := fun _ => rfl
    rootOrd := 2
    rootOrd_spec := rfl
    resDeg_eq_sideDeg := by
      intro i S h
      exact Option.noConfusion h }

/-- (𝐇⁰; nuT1) is `ConsF`: (c0) reads a₀ = 2 = rootOrd, and the continuing
    part is empty (nuT1 is terminal), so (c1)/(c2) are vacuous. -/
theorem hc0 : ConsF f0 (snocTerm H0 nuT1) D0 R0 := by
  refine ⟨rfl, ?_⟩
  intro i μ hg
  have hg' : (([] : List ENodeData))[i]? = some μ := hg
  simp at hg'

/-- **THE DISCHARGE** (unit III-A3, unconditional): the terminal-recovery
    over-claim is FALSE at p = 2, F = ZMod 2.  Lemma R's terminal
    non-recovery is now a compiled non-claim, not a prose remark. -/
theorem terminalRecovery_false : ¬ TerminalRecoveryStmt 2 (ZMod 2) :=
  terminalRecovery_false_of_witness H0 f0 hwf0 D0 R0 hc0

/-- The two-witness collision, exhibited at the concrete 𝐇⁰: distinct
    extensions, equal Θ images. -/
theorem witness_pair_gate :
    snocTerm H0 nuT1 ≠ snocTerm H0 nuT2 ∧
      Theta (snocTerm H0 nuT1) = Theta (snocTerm H0 nuT2) :=
  ⟨snocTerm_pair_ne H0, theta_snocTerm_pair H0⟩

end A3Gate

/-! ## Unit III-A6a — the `GMNData` construction from the OM polygon API (O-2a (C4) level 1; GD23 §3)

Unit III-A6a (BP_III §2 wave-2 table row, line 769): "`GMNData` construction
restricted by `c.slopes.length ≤ 1` | Newton-polygon side list and residual
data from `OM/` | III-G21a | HARD | O2a (C4) level 1; GD23 §3" — the
REV2-finding-18 restriction, D-R2's concrete data supply, and the sole
dependency of the landed III-A6b builder above (whose section-header seam
note "III-A6a ... NOT landed at HEAD", probed 2026-08-01, THIS section now
closes).

Adjudication of the transcription rule (division-lead review flag, per the
III-A1/III-A6b/III-A6c precedents above): like every wave-2 unit, III-A6a has
no §1-displayed signature — but its target TYPE is itself a §1 display: the
deliverable is a term of `GMNData f c` (§1.2, landed VERBATIM by unit
III-C8), under the row's displayed restriction hypothesis
`c.slopes.length ≤ 1`, built from the §3.3-directed corpus polygon API
(`rg "NP|polygon" LeanUrat/OM`: `OM/NewtonPolygon` + `OM/ResidualPolynomial`
+ `OM/PadicValuation`).  Nothing at the interface level is redeclared,
weakened, or invented.  Completion ledger (the III-G21a convention),
field by field against O-2a (C4)'s objects `(N_i^−(f), R_{λ_i}(f))`:

* **`principalSides` = the genuine Newton-polygon side list.**  The corpus
  lower-hull scan `NewtonPolygon.npSides` over the valuation support
  `M2.valSupport f` (the proved GLUE-5 polygon, NOT a reimplementation),
  restricted to sides of NEGATIVE slope — GMN's principal polygon `N^−(f)` —
  and mapped to the §1.2 `SideDatum` shape by `sideToDatum`:
  `e := S.e` (= `Rat.den` of the slope, reduced), `h := S.h.natAbs` (the GMN
  magnitude convention λ = −h/e of `ChainData.slopes`; on a negative side
  `S.h < 0` this is exact, see `matchedSideAt_spec`), `ℓ := M4.residualDeg S`
  (= `S.length / S.e`, the residual degree the `resDeg_eq_sideDeg` law
  reads), `(s, u) := (S.i₀, S.v₀)` (the side's initial point, Lemma R's
  positional clause).  Level keying: the polygon of `f` itself at level 0,
  `[]` at every other level — under the row's restriction
  `c.slopes.length ≤ 1` the single live level is `i = 0` (the III-A6b
  order-1 shape `gmnReaderOrder1_side_eq_none` above).
* **`isNegInfty := false` on every constructed datum** (scope note): the
  corpus polygon API carries FINITE sides only (`valSupport` collects the
  nonzero coefficients; the slope-−∞ side of GMN Def 1.1 has no `npSides`
  representative).  A −∞ side can never carry a requested slope
  (`requestedSlope` returns a finite lowest-terms pair with `h ≥ 1`,
  `ChainData.hcop`), so no reader law is affected; recorded for the eventual
  order-≥2 layer.
* **`residualDegree` — keyed to the requested side** (`matchedDatum`, ONE
  lookup path): `d(S_i) = ℓ` of the unique principal side carrying the
  requested slope `(e_i, h_i)`, `0` (junk) when no side matches or the level
  is beyond the chain.  `gmnDataOrder1_residualDegree` is the keyed
  residual-degree law — exactly the shape `resDeg_eq_sideDeg` consumes.
  SEAM NOTE for the division lead (III-A6b tie): the §1.3 row `OL3min`
  quantifies over ALL principal sides (`∀ S ∈ D.principalSides i,
  D.residualDegree i = S.ℓ`); on the genuine multi-side polygon distinct
  sides carry distinct `ℓ`, so OL3min is genuinely STRONGER than the keyed
  law and is NOT provable for this data in general (it holds exactly when
  the live level's polygon is single-sided, e.g. the III-A6c gate).  The
  III-A6b builder `gmnReaderOrder1` consumes `OL5`/`OL3min` as hypothesis
  rows, so this is a row-strength observation, not a defect of either unit;
  the coherence lemma `sideRead_gmnDataOrder1` below ties the builder's
  lookup to this data's without any row.
* **`residualOrder` = `ord_{ψ̂₀}(R_λ(f))` — the genuine residual read.**
  `R_λ(f)` is the corpus residual polynomial `M4.residualPoly` (GMN
  Def 2.21) instantiated at the CONCRETE `ℤ_[p]` residue datum
  `padicCoeffData` (GMN Def 2.20: the `ZMod p` residue of the unit part
  `a_i/p^{v(a_i)}` of each on-line coefficient, `0` off the line —
  `PadicInt.unitCoeff`/`toZMod`, de-opaquing exactly the datum
  `M4.residualPoly`'s header documents as "opaque in the skeleton", and
  mirroring `Classifier.boxCoeffData` at the `ℤ_[p]` carrier).  The order is
  Mathlib's `multiplicity` of the level-0 dressing `c.psihat 0` in `R_λ(f)`
  read into the chain's residue world THROUGH ι (§1.2's preamble: "Cons_f
  reads GMN objects THROUGH ι") — see the ι note below.
* **`rootOrder` = `ord_{ψ̂₀}(f̄)`** ((c0)): `multiplicity` of `c.psi0` in the
  mod-p reduction `f.map PadicInt.toZMod`, read through ι at the base.
* **The ι-interface enters as two explicit DATA parameters**
  (`ιb : ZMod p →+* ↥c.base`, `ι0 : ZMod p →+* ↥(c.fld 0)`): the §1.2 header
  makes ι the reading interface, and no identification of the abstract
  chain-side residue tower (`Subfield F`, `F` arbitrary) with the concrete
  `ℤ_[p]` residue world (`ZMod p`) exists in the Wave-0 carriers — nor can
  one exist unconditionally (`F` need not have characteristic `p`).  They
  are inputs of the construction, NOT axioms, NOT discharged, asserted
  about nothing ([M]-row discipline); the III-A6c world (`p = 2`,
  `F = ZMod 2`) instantiates both concretely.  Flagged for division-lead
  review as this unit's one design decision beyond the row text.

Status honesty: the construction and its four transport lemmas are PROVED
OUTRIGHT (no sorry, Lean-core expected — see the footprint audit).  NOT
claimed here: `OL5` for this data (side-slope distinctness of the genuine
hull — convexity work, the III-A2 "side-of-slope uniqueness" seam),
`OL2min`/`OL4` (side existence at live levels needs (c1)-style hypotheses on
`f`), and every reader law (unit III-A6b above, already landed as a builder).
Dependency III-G21a is landed (`Devid.lean`, `gd3_min` + gate); its graded
carrier is not consumed here — the level-0 residual read is direct, per the
unit row's own proof column ("Newton-polygon side list and residual data
from `OM/`"). -/

open LeanUrat.OM in
/-- III-A6a residue datum (GMN Def 2.20 at the `ℤ_[p]` carrier): `c_t` is the
    `ZMod p` residue of the unit part of the coefficient at abscissa
    `i₀ + t·e` when its valuation sits ON the side line `v₀ + t·h`, else `0`.
    This is `Classifier.boxCoeffData`'s recipe at infinite precision — the
    concrete instantiation of the datum `M4.residualPoly` consumes. -/
noncomputable def padicCoeffData (f : Polynomial ℤ_[p])
    (S : NewtonPolygon.Side) : ℕ → ZMod p := fun t =>
  if h : f.coeff (S.i₀ + t * S.e) ≠ 0 ∧
      ((f.coeff (S.i₀ + t * S.e)).valuation : ℤ) = (S.v₀ : ℤ) + t * S.h then
    PadicInt.toZMod (PadicInt.unitCoeff h.1 : ℤ_[p])
  else 0

open LeanUrat.OM in
/-- III-A6a datum dressing: a corpus polygon side as a §1.2 `SideDatum` —
    `(e, h, ℓ, s, u) = (e_S, |h_S|, d(S), i₀, v₀)`, finite slope (ledger
    items 1–2 of the section header). -/
noncomputable def sideToDatum (S : NewtonPolygon.Side) : SideDatum :=
  ⟨S.e, S.h.natAbs, M4.residualDeg S, S.i₀, S.v₀, false⟩

open LeanUrat.OM in
/-- The corpus Newton-polygon side list of `f` (GLUE-5 `npSides` over the
    valuation support), `[]` for `f = 0` (empty support). -/
noncomputable def sideList (f : Polynomial ℤ_[p]) :
    List NewtonPolygon.Side :=
  if h : (M2.valSupport p f).Nonempty then
    NewtonPolygon.npSides (M2.valSupport p f) h
  else []

open LeanUrat.OM in
/-- The PRINCIPAL side list `N^−(f)`: the negative-slope sides (GMN's
    principal polygon; `S.h < 0` ⟺ slope < 0 since `e = Rat.den > 0`). -/
noncomputable def principalSideList (f : Polynomial ℤ_[p]) :
    List NewtonPolygon.Side :=
  (sideList f).filter fun S => decide (S.h < 0)

/-- III-A6a: the principal side list in `SideDatum` dress — the value of
    `principalSides` at the live level. -/
noncomputable def principalData (f : Polynomial ℤ_[p]) : List SideDatum :=
  (principalSideList f).map sideToDatum

open LeanUrat.OM in
/-- The unique-side lookup at a requested lowest-terms slope `(e, h)`
    (λ = −h/e): the first — under slope distinctness, the only — principal
    side with `e_S = e` and `h_S = −h`. -/
noncomputable def matchedSide (f : Polynomial ℤ_[p]) (eh : ℕ × ℕ) :
    Option NewtonPolygon.Side :=
  (principalSideList f).find? fun S => decide (S.e = eh.1 ∧ S.h = -(eh.2 : ℤ))

open LeanUrat.OM in
/-- The side the chain requests at level `i` (`none` beyond the chain or
    when the polygon carries no such side) — the construction's ONE lookup
    path (ledger item 3). -/
noncomputable def matchedSideAt (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (i : ℕ) : Option NewtonPolygon.Side :=
  (requestedSlope c i).bind (matchedSide f)

/-- `matchedSideAt` in `SideDatum` dress. -/
noncomputable def matchedDatum (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (i : ℕ) : Option SideDatum :=
  (matchedSideAt f c i).map sideToDatum

open LeanUrat.OM in
/-- III-A6a residual order at the live level: `ord_{ψ̂₀}(R_λ(f))` — the
    `multiplicity` of the level-0 dressing in the corpus residual polynomial
    of the requested side, read through `ι0` (ledger items 4 and 6); `0`
    (junk) when no side is requested or matched. -/
noncomputable def residualOrder0 (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (ι0 : ZMod p →+* ↥(c.fld 0)) : ℕ :=
  match matchedSideAt f c 0 with
  | some S =>
      multiplicity (c.psihat 0)
        ((M4.residualPoly (padicCoeffData f S) S).map ι0)
  | none => 0

/-- III-A6a root order ((c0)): `ord_{ψ̂₀}(f̄)` — the `multiplicity` of `c.psi0`
    in the mod-p reduction of `f`, read through `ιb` (ledger items 5–6). -/
noncomputable def rootOrder0 (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (ιb : ZMod p →+* ↥c.base) : ℕ :=
  multiplicity c.psi0 ((f.map (PadicInt.toZMod)).map ιb)

/-- **Unit III-A6a.**  The `GMNData` construction restricted by
    `c.slopes.length ≤ 1`, from the corpus Newton-polygon side list and
    residual data (section-header ledger): the genuine principal polygon of
    `f` at the single live level 0, the keyed residual degree, the genuine
    residual order and root order read through the ι parameters.  The
    restriction hypothesis is the row's displayed perimeter — the data is
    order-≤1-meaningful only (`principalSides` answers the level-0 polygon
    alone), which is exactly what the restriction certifies. -/
noncomputable def gmnDataOrder1 (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (ιb : ZMod p →+* ↥c.base) (ι0 : ZMod p →+* ↥(c.fld 0))
    (_hlen : c.slopes.length ≤ 1) : GMNData f c where
  principalSides := fun i => if i = 0 then principalData f else []
  residualOrder := fun i => if i = 0 then residualOrder0 f c ι0 else 0
  residualDegree := fun i => ((matchedDatum f c i).map SideDatum.ℓ).getD 0
  rootOrder := rootOrder0 f c ιb

open LeanUrat.OM in
/-- Transport 1: a matched side is a principal side and its datum carries
    the requested slope — the corpus-side face of `HasRequestedSlope`
    (`h_S = −h` on a negative side reads back as `natAbs`). -/
theorem matchedSideAt_spec {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {i : ℕ} {S : NewtonPolygon.Side} (h : matchedSideAt f c i = some S) :
    S ∈ principalSideList f ∧ requestedSlope c i = some (S.e, S.h.natAbs) := by
  simp only [matchedSideAt, matchedSide, Option.bind_eq_some_iff] at h
  rcases h with ⟨⟨e₀, h₀⟩, heh, hfind⟩
  have hmem := List.mem_of_find?_eq_some hfind
  have hp := List.find?_some hfind
  have hpred : S.e = e₀ ∧ S.h = -(h₀ : ℤ) := of_decide_eq_true hp
  refine ⟨hmem, ?_⟩
  rw [heh, hpred.1, hpred.2, Int.natAbs_neg, Int.natAbs_natCast]

/-- Transport 2: the matched DATUM is a member of the constructed
    `principalData` and satisfies the §1.2 lookup predicate
    `HasRequestedSlope` — the two `side_spec`-shaped facts of this data. -/
theorem matchedDatum_spec {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {i : ℕ} {T : SideDatum} (h : matchedDatum f c i = some T) :
    T ∈ principalData f ∧ HasRequestedSlope c i T := by
  simp only [matchedDatum, Option.map_eq_some_iff] at h
  rcases h with ⟨S, hS, rfl⟩
  rcases matchedSideAt_spec hS with ⟨hmem, hslope⟩
  exact ⟨List.mem_map_of_mem hmem, hslope⟩

/-- Transport 3 (the KEYED residual-degree law, ledger item 3): the
    constructed `residualDegree` reads the matched side's `ℓ` — the exact
    shape `resDeg_eq_sideDeg` consumes on any reader whose lookup agrees
    with `matchedDatum` (see `sideRead_gmnDataOrder1`). -/
theorem gmnDataOrder1_residualDegree {f : Polynomial ℤ_[p]}
    {c : ChainData p F} {ιb : ZMod p →+* ↥c.base}
    {ι0 : ZMod p →+* ↥(c.fld 0)} {hlen : c.slopes.length ≤ 1} {i : ℕ}
    {T : SideDatum} (h : matchedDatum f c i = some T) :
    (gmnDataOrder1 f c ιb ι0 hlen).residualDegree i = T.ℓ := by
  simp [gmnDataOrder1, h]

open LeanUrat.OM in
/-- Transport 4: every constructed datum descends from a genuine
    negative-slope corpus side — nothing in `principalData` is invented. -/
theorem mem_principalData {f : Polynomial ℤ_[p]} {T : SideDatum}
    (h : T ∈ principalData f) :
    ∃ S ∈ sideList f, S.h < 0 ∧ T = sideToDatum S := by
  rcases List.mem_map.mp h with ⟨S, hS, rfl⟩
  rcases List.mem_filter.mp hS with ⟨hmem, hneg⟩
  exact ⟨S, hmem, of_decide_eq_true hneg, rfl⟩

/-- `List.find?` congruence on members (local helper; not in the pinned
    Mathlib — probed 2026-08-01, `List.find?_congr` unknown). -/
theorem find?_congr_of_mem {α : Type*} {l : List α} {q r : α → Bool}
    (h : ∀ a ∈ l, q a = r a) : l.find? q = l.find? r := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases hra : r a = true
    · rw [List.find?_cons_of_pos _ (by rw [h a (List.mem_cons_self ..)]; exact hra),
        List.find?_cons_of_pos _ hra]
    · rw [List.find?_cons_of_neg _ (by rw [h a (List.mem_cons_self ..)]; exact hra),
        List.find?_cons_of_neg _ hra]
      exact ih fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- **The III-A6a → III-A6b coherence seam** (no OL row consumed): on the
    constructed data, the landed III-A6b lookup `sideRead` computes exactly
    this unit's `matchedDatum` — the two find-first passes agree because on
    a NEGATIVE side the datum slope pair `(e, natAbs h)` determines and is
    determined by the corpus pair `(e, h)`.  With
    `gmnDataOrder1_residualDegree` this gives the keyed residual-degree law
    for any reader built on `sideRead` over this data, independent of the
    `OL3min` row strength (section-header seam note). -/
theorem sideRead_gmnDataOrder1 {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {ιb : ZMod p →+* ↥c.base} {ι0 : ZMod p →+* ↥(c.fld 0)}
    (hlen : c.slopes.length ≤ 1) (i : ℕ) :
    sideRead f c (gmnDataOrder1 f c ιb ι0 hlen) i = matchedDatum f c i := by
  by_cases hi : i = 0
  · subst hi
    show (principalData f).find? (fun S => decide (HasRequestedSlope c 0 S))
      = matchedDatum f c 0
    cases heh : requestedSlope c 0 with
    | none =>
      rw [List.find?_eq_none.mpr fun T _ hT => by
        have : requestedSlope c 0 = some (T.e, T.h) := of_decide_eq_true hT
        rw [heh] at this
        exact Option.noConfusion this]
      simp [matchedDatum, matchedSideAt, heh]
    | some eh =>
      unfold matchedDatum matchedSideAt matchedSide
      rw [heh, Option.some_bind, principalData, List.find?_map]
      refine congrArg (Option.map sideToDatum) (find?_congr_of_mem ?_)
      intro S hS
      have hneg : S.h < 0 :=
        of_decide_eq_true (List.mem_filter.mp hS).2
      simp only [Function.comp]
      rw [decide_eq_decide]
      unfold HasRequestedSlope
      rw [heh]
      constructor
      · intro hsome
        have : eh = ((sideToDatum S).e, (sideToDatum S).h) :=
          Option.some_injective _ hsome
        have he : eh.1 = S.e := by rw [this]
        have hh : eh.2 = S.h.natAbs := by rw [this]
        exact ⟨he.symm, by omega⟩
      · rintro ⟨he, hh⟩
        have hnat : S.h.natAbs = eh.2 := by omega
        have : ((sideToDatum S).e, (sideToDatum S).h) = eh := by
          show (S.e, S.h.natAbs) = eh
          rw [he, hnat]
        rw [this]
  · have hle : c.slopes.length ≤ i := hlen.trans (by omega)
    show ((gmnDataOrder1 f c ιb ι0 hlen).principalSides i).find? _ = _
    simp [gmnDataOrder1, hi, matchedDatum, matchedSideAt,
      requestedSlope_eq_none hle]

/-! ## Unit III-A2 — Lemma R proper: recovery + injectivity on 𝔈°_f (O-2a rev-5 §2)

Unit III-A2 (BP_III §2 wave-2 table row, line 765): "Lemma R injectivity on
𝔈°_f | side-of-slope uniqueness (GMNReader row) + W2 | III-A1 | MED |
O2a §2 Lemma R".

Statement provenance (division-lead review flag, per the III-A1 section note
above and the III-C3 precedent in `Carriers.lean`): like every wave-2 unit,
III-A2 has NO §1-displayed signature; the source statement is O-2a rev-5 §2:
"**Lemma R (recovery; the exact injectivity statement).** Let f be monic with
disc f ≠ 0. On 𝔈°_f := {𝐇 ∈ 𝔈 : Cons_f(𝐇), every node continuing}, 𝐇 is a
function of (f, Θ(𝐇)) — i.e. Θ is injective on 𝔈°_f (at orders ≥ 2 granting
OL-1 for the well-definedness of the objects read)."  Rendered as TWO
theorems over the landed carriers:

* `lemmaR_recovers` — "𝐇 is a function of (f, Θ(𝐇))": unit III-A1's
  `recoverEHist` returns `some 𝐇` on 𝔈°_f.  This also discharges the III-A1
  section note's forward assignment ("That the map returns `some` and
  reproduces every field on Θ(𝔈°_f) under `ConsF` is unit III-A2's content").
  Every displayed recipe line is consumed: the side exists by (c1) (`ConsF`
  supplies the very side `recoverNode` reads), ℓ/s/u are that side's data,
  g = deg ψ̂_i (W4's dressing degree law), μ = the residual order ((c2) +
  `resOrd_spec`), a₀ = the root order ((c0) + `rootOrd_spec`), inc = 1 iff
  e·g ≥ 2 (W2).
* `lemmaR_theta_injective` — "i.e. Θ is injective on 𝔈°_f": the two-history
  form, proved by the row's own sketch — side-of-slope uniqueness (the
  `GMNReader.side_unique` row: the two certificates' sides at level i carry
  the SAME requested slope on the SAME polygon, hence coincide — "a polygon
  has at most one side of a given slope") + W2 for `inc`, with W4's degree
  law tying `g` through the shared dressing.

Carrier reading of "the same GMN read" (`GMNData.SameRead` below): the
brief's GMN objects (N_i^−(f), R_{λ_i}(f)) are canonical in (f, chain); the
scaffold carries them as a PARAMETER (BP_III §1.2 note: constructed at order
≤ 1 by III-A6, supplied at orders ≥ 2 by OL-1 — the brief's parenthetical
"at orders ≥ 2 granting OL-1").  Injectivity is relative to both consistency
certificates reading THE data of f along the common chain Θ(𝐇₁) = Θ(𝐇₂);
`SameRead` renders that fieldwise (avoiding any cast across the type equality
`GMNData f (Theta H₁) = GMNData f (Theta H₂)`); its `residualDegree` clause
completes "the same read" (only `principalSides`/`residualOrder`/`rootOrder`
are consumed here).

The brief's "monic, disc f ≠ 0" preamble is not consumed at the carrier
level (it feeds the SEMANTIC construction of the read, units III-A6/OL-1),
so it is not hypothesized — both statements are the stronger unconditional
forms. -/

/-- 𝔈° membership (O2a rev-5 §2 Lemma R): every node of `H` is continuing
    (`sel ≠ none`).  Together with `ConsF` this carves 𝔈°_f out of 𝔈. -/
def EHist.AllContinuing (H : EHist p F) : Prop :=
  ∀ ν ∈ H.nodes, ν.sel ≠ none

/-- On an all-continuing history, `continuingPart` keeps every node. -/
theorem EHist.continuingPart_nodes_of_allContinuing {H : EHist p F}
    (hc : H.AllContinuing) : H.continuingPart.nodes = H.nodes :=
  List.takeWhile_eq_self_iff.mpr fun ν hν =>
    Option.isSome_iff_ne_none.mpr (hc ν hν)

/-- The two consistency certificates read the SAME GMN data of `f` (fieldwise;
    section note above). -/
def GMNData.SameRead {f : Polynomial ℤ_[p]} {c₁ c₂ : ChainData p F}
    (D₁ : GMNData f c₁) (D₂ : GMNData f c₂) : Prop :=
  D₁.principalSides = D₂.principalSides ∧
  D₁.residualOrder = D₂.residualOrder ∧
  D₁.residualDegree = D₂.residualDegree ∧
  D₁.rootOrder = D₂.rootOrder

/-- Helper: two `ENodeData` with equal data fields are equal (the Prop rows
    ride by proof irrelevance). -/
theorem ENodeData.ext_fields {ν₁ ν₂ : ENodeData}
    (he : ν₁.e = ν₂.e) (hh : ν₁.h = ν₂.h) (hl : ν₁.ℓ = ν₂.ℓ)
    (hs : ν₁.s = ν₂.s) (hu : ν₁.u = ν₂.u) (hsel : ν₁.sel = ν₂.sel)
    (hinc : ν₁.inc = ν₂.inc) : ν₁ = ν₂ := by
  cases ν₁; cases ν₂
  dsimp only at he hh hl hs hu hsel hinc
  subst he hh hl hs hu hsel hinc
  rfl

/-- Helper: two `EHist` with equal data fields are equal (the Prop rows ride
    by proof irrelevance; `psi0`/`psihat` cross `base`/`fld` as `HEq`). -/
theorem EHist.ext_fields {H₁ H₂ : EHist p F}
    (hbase : H₁.base = H₂.base) (hpsi0 : HEq H₁.psi0 H₂.psi0)
    (ha0 : H₁.a0 = H₂.a0) (hnodes : H₁.nodes = H₂.nodes)
    (hfld : H₁.fld = H₂.fld) (hpsihat : HEq H₁.psihat H₂.psihat) :
    H₁ = H₂ := by
  cases H₁; cases H₂
  dsimp only at hbase hpsi0 ha0 hnodes hfld hpsihat
  subst hbase ha0 hnodes hfld
  obtain rfl := eq_of_heq hpsi0
  obtain rfl := eq_of_heq hpsihat
  rfl

/-- Helper: equal towers + `HEq`-equal dressings give equal dressing degrees
    (stated over VARIABLE tower functions so `subst` applies; instantiated at
    `EHist.fld`/`EHist.psihat`). -/
theorem psihat_natDegree_congr {f₁ f₂ : ℕ → Subfield F} (hf : f₁ = f₂)
    {g₁ : (i : ℕ) → Polynomial ↥(f₁ i)} {g₂ : (i : ℕ) → Polynomial ↥(f₂ i)}
    (hg : HEq g₁ g₂) (i : ℕ) : (g₁ i).natDegree = (g₂ i).natDegree := by
  subst hf
  rw [eq_of_heq hg]

/-- Helper: `mapM` over `Option` returns exactly the pointwise-forced list. -/
private theorem mapM_eq_some_of_pointwise {α β : Type} (g : α → Option β) :
    ∀ (l : List α) (l' : List β), l.length = l'.length →
      (∀ (i : ℕ) (x : α) (y : β), l[i]? = some x → l'[i]? = some y →
        g x = some y) →
      l.mapM g = some l'
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | a :: t, b :: t', hlen, hpt => by
    have h0 : g a = some b := hpt 0 a b rfl rfl
    have htail : t.mapM g = some t' :=
      mapM_eq_some_of_pointwise g t t' (by simpa using hlen)
        (fun i x y hx hy => hpt (i + 1) x y
          (by simpa using hx) (by simpa using hy))
    simp [List.mapM_cons, h0, htail]

/-- **Unit III-A2, recovery half — Lemma R's "𝐇 is a function of (f, Θ(𝐇))"**
(O-2a rev-5 §2 Lemma R, first clause; section note above).

On 𝔈°_f (well-formed, all-continuing, `ConsF`-consistent), unit III-A1's
recovery map reproduces the history: every field of every node — the
displayed recipe line by line ((c0) for a₀, (c1) + the side data for
(e,h,ℓ,s,u), W4's degree law for g, (c2) for μ, W2 for inc). -/
theorem lemmaR_recovers (f : Polynomial ℤ_[p]) {H : EHist p F}
    (hwf : EWF H) (hc : H.AllContinuing)
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hcons : ConsF f H D R) :
    recoverEHist f (Theta H) D R H.hpsihat = some H := by
  have hcp := EHist.continuingPart_nodes_of_allContinuing hc
  have hslopes_eq : (Theta H).slopes = H.nodes.map (fun ν => (ν.e, ν.h)) := by
    have h0 : (Theta H).slopes
        = H.continuingPart.nodes.map (fun ν => (ν.e, ν.h)) := rfl
    rw [h0, hcp]
  have hslen : (Theta H).slopes.length = H.nodes.length := by
    rw [hslopes_eq, List.length_map]
  -- Pointwise node recovery: the displayed per-level recipe line.
  have hpoint : ∀ (i : ℕ) (hi : i < H.nodes.length),
      recoverNode f (Theta H) D R i = some (H.nodes[i]'hi) := by
    intro i hi
    set ν := H.nodes[i]'hi with hν_def
    have hν : H.nodes[i]? = some ν := List.getElem?_eq_getElem hi
    obtain ⟨S, hS, hfields, hres⟩ := hcons.2 i ν (by rw [hcp]; exact hν)
    simp only [Prod.mk.injEq] at hfields
    obtain ⟨hSe, hSh, hSl, hSs, hSu⟩ := hfields
    obtain ⟨⟨g, μ⟩, hsel⟩ :=
      Option.ne_none_iff_exists.mp (hc ν (List.mem_of_getElem? hν))
    -- g = deg ψ̂_i (W4's dressing degree law).
    have hgdeg : ((Theta H).psihat i).natDegree = g :=
      (hwf.w4dress i ν g μ hν hsel.symm).2.2.1
    -- μ = the residual order ((c2) + `resOrd_spec` is packaged in `ConsF`).
    have hμ : R.resOrd i = μ := hres g μ hsel.symm
    -- The slope lookup: level i requests exactly (ν.e, ν.h).
    have hsl : (Theta H).slopes[i]? = some (ν.e, ν.h) := by
      rw [hslopes_eq, List.getElem?_map, hν]; rfl
    obtain ⟨hg1, hμ1, hμg⟩ := ν.hsel (g, μ) (Option.mem_def.mpr hsel.symm)
    have w2 := hwf.w2 i ν g μ hν hsel.symm
    -- Run the recovery recipe.
    simp only [recoverNode, hsl, hS, Option.bind_some]
    rw [dif_pos ⟨ν.he, ν.hh, ν.hcop,
      by rw [hSl]; exact ν.hl,
      by rw [hgdeg]; exact hg1,
      by rw [hμ]; exact hμ1,
      by rw [hμ, hgdeg, hSl]; exact hμg⟩]
    rw [Option.pure_def]
    refine congrArg some (ENodeData.ext_fields rfl rfl hSl hSs hSu ?_ ?_)
    · -- sel: some (deg ψ̂_i, resOrd i) = ν.sel
      show some (((Theta H).psihat i).natDegree, R.resOrd i) = ν.sel
      rw [hgdeg, hμ]
      exact hsel
    · -- inc: decide (2 ≤ e·g) = ν.inc (W2)
      show decide (2 ≤ ν.e * ((Theta H).psihat i).natDegree) = ν.inc
      have hP : (2 ≤ ν.e * ((Theta H).psihat i).natDegree)
          ↔ (2 ≤ ν.e * g) := by rw [hgdeg]
      cases hb : ν.inc with
      | true => exact decide_eq_true (hP.mpr (w2.mp hb))
      | false =>
        exact decide_eq_false fun hp =>
          absurd (w2.mpr (hP.mp hp)) (by simp [hb])
  -- Assemble the node list, then the history.
  have hmapM : (List.range (Theta H).slopes.length).mapM
      (recoverNode f (Theta H) D R) = some H.nodes := by
    apply mapM_eq_some_of_pointwise
    · rw [List.length_range, hslen]
    · intro i x y hx hy
      obtain ⟨hi, rfl⟩ : i < (Theta H).slopes.length ∧ x = i := by
        rcases Nat.lt_or_ge i (Theta H).slopes.length with h | h
        · exact ⟨h, by simpa [List.getElem?_range h] using hx.symm⟩
        · rw [List.getElem?_eq_none (by simpa using h)] at hx
          exact absurd hx (by simp)
      have hi' : x < H.nodes.length := hslen ▸ hi
      have hy' : H.nodes[x]'hi' = y := by
        have := List.getElem?_eq_getElem hi'
        rw [this] at hy
        exact Option.some.inj hy
      rw [hpoint x hi', hy']
  have hroot : 1 ≤ R.rootOrd := by rw [hcons.1]; exact H.ha0
  simp only [recoverEHist]
  rw [hmapM, Option.bind_some, dif_pos hroot]
  exact congrArg some
    (EHist.ext_fields rfl HEq.rfl hcons.1 rfl rfl HEq.rfl)

/-- **Unit III-A2 — Lemma R, injectivity on 𝔈°_f** (O-2a rev-5 §2 Lemma R,
"i.e." clause).

On all-continuing well-formed histories consistent with `f` over the same GMN
read, `Θ` is injective: `Θ(𝐇₁) = Θ(𝐇₂) → 𝐇₁ = 𝐇₂`.  Proof = the unit row's
sketch: `base`/`psi0`/`fld`/`psihat` ride on `Θ` directly; `a0` is the shared
root order ((c0)); each node's `(e, h)` is the slope datum; `(ℓ, s, u)` ride
the side, unique BY THE `side_unique` ROW among sides of the requested slope
("a polygon has at most one side of a given slope"); `μ` is the shared
residual order ((c2)); `g = deg ψ̂_i` (W4's degree law along the shared
dressing); `inc = 1 iff e·g ≥ 2` (W2). -/
theorem lemmaR_theta_injective (f : Polynomial ℤ_[p]) {H₁ H₂ : EHist p F}
    (hwf₁ : EWF H₁) (hwf₂ : EWF H₂)
    (hc₁ : H₁.AllContinuing) (hc₂ : H₂.AllContinuing)
    {D₁ : GMNData f (Theta H₁)} {R₁ : GMNReader f (Theta H₁) D₁}
    {D₂ : GMNData f (Theta H₂)} {R₂ : GMNReader f (Theta H₂) D₂}
    (hread : D₁.SameRead D₂)
    (hcons₁ : ConsF f H₁ D₁ R₁) (hcons₂ : ConsF f H₂ D₂ R₂)
    (hTheta : Theta H₁ = Theta H₂) : H₁ = H₂ := by
  -- Θ components: base, psi0, fld, psihat ride directly.
  have hbase : H₁.base = H₂.base := congrArg ChainData.base hTheta
  have hfld : H₁.fld = H₂.fld := congrArg ChainData.fld hTheta
  have hpsi0 : HEq H₁.psi0 H₂.psi0 := by
    have h : HEq (Theta H₁).psi0 (Theta H₂).psi0 := by rw [hTheta]
    exact h
  have hpsihat : HEq H₁.psihat H₂.psihat := by
    have h : HEq (Theta H₁).psihat (Theta H₂).psihat := by rw [hTheta]
    exact h
  have hslopes : (Theta H₁).slopes = (Theta H₂).slopes :=
    congrArg ChainData.slopes hTheta
  -- The 𝔈° restriction: continuing parts are the whole node lists.
  have hcp₁ := EHist.continuingPart_nodes_of_allContinuing hc₁
  have hcp₂ := EHist.continuingPart_nodes_of_allContinuing hc₂
  have hmap : H₁.nodes.map (fun ν => (ν.e, ν.h))
      = H₂.nodes.map (fun ν => (ν.e, ν.h)) := by
    have e₁ : (Theta H₁).slopes
        = H₁.continuingPart.nodes.map (fun ν => (ν.e, ν.h)) := rfl
    have e₂ : (Theta H₂).slopes
        = H₂.continuingPart.nodes.map (fun ν => (ν.e, ν.h)) := rfl
    rw [← hcp₁, ← hcp₂, ← e₁, ← e₂]
    exact hslopes
  have hlen : H₁.nodes.length = H₂.nodes.length := by
    have := congrArg List.length hmap
    simpa using this
  -- a₀ recovery: (c0) + `rootOrd_spec` through the shared root order.
  have ha0 : H₁.a0 = H₂.a0 := by
    have h₁ := hcons₁.1
    have h₂ := hcons₂.1
    rw [R₁.rootOrd_spec] at h₁
    rw [R₂.rootOrd_spec] at h₂
    rw [← h₁, ← h₂, hread.2.2.2]
  -- Node-by-node recovery.
  have hnodes : H₁.nodes = H₂.nodes := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < H₁.nodes.length
    · obtain ⟨ν₁, hν₁⟩ : ∃ ν, H₁.nodes[i]? = some ν :=
        ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨ν₂, hν₂⟩ : ∃ ν, H₂.nodes[i]? = some ν :=
        ⟨_, List.getElem?_eq_getElem (by omega : i < H₂.nodes.length)⟩
      rw [hν₁, hν₂]
      -- (c1) at index i, for both histories.
      obtain ⟨S₁, hS₁, hfields₁, hres₁⟩ :=
        hcons₁.2 i ν₁ (by rw [hcp₁]; exact hν₁)
      obtain ⟨S₂, hS₂, hfields₂, hres₂⟩ :=
        hcons₂.2 i ν₂ (by rw [hcp₂]; exact hν₂)
      obtain ⟨hmem₁, hslope₁⟩ := (R₁.side_spec i S₁).mp hS₁
      obtain ⟨hmem₂, hslope₂⟩ := (R₂.side_spec i S₂).mp hS₂
      -- Transport side 2 into reader 1's frame (same polygon, same chain).
      have hmem₂' : S₂ ∈ D₁.principalSides i := by
        rw [hread.1]; exact hmem₂
      have hslope₂' : HasRequestedSlope (Theta H₁) i S₂ := by
        unfold HasRequestedSlope requestedSlope at hslope₂ ⊢
        rw [hslopes]; exact hslope₂
      -- SIDE-OF-SLOPE UNIQUENESS: the `side_unique` row.
      have hSS : S₁ = S₂ :=
        R₁.side_unique i S₁ S₂ hmem₁ hmem₂' hslope₁ hslope₂'
      simp only [Prod.mk.injEq] at hfields₁ hfields₂
      obtain ⟨hSe₁, hSh₁, hSl₁, hSs₁, hSu₁⟩ := hfields₁
      obtain ⟨hSe₂, hSh₂, hSl₂, hSs₂, hSu₂⟩ := hfields₂
      -- Continuing selections: both `sel`s are `some`.
      obtain ⟨⟨g₁, μ₁⟩, hsel₁⟩ :=
        Option.ne_none_iff_exists.mp (hc₁ ν₁ (List.mem_of_getElem? hν₁))
      obtain ⟨⟨g₂, μ₂⟩, hsel₂⟩ :=
        Option.ne_none_iff_exists.mp (hc₂ ν₂ (List.mem_of_getElem? hν₂))
      -- g = deg ψ̂_i (W4's degree law) along the shared dressing.
      have hg : g₁ = g₂ := by
        have d₁ : (H₁.psihat i).natDegree = g₁ :=
          (hwf₁.w4dress i ν₁ g₁ μ₁ hν₁ hsel₁.symm).2.2.1
        have d₂ : (H₂.psihat i).natDegree = g₂ :=
          (hwf₂.w4dress i ν₂ g₂ μ₂ hν₂ hsel₂.symm).2.2.1
        rw [← d₁, ← d₂]
        exact psihat_natDegree_congr hfld hpsihat i
      -- μ = the residual order ((c2)) through the shared read.
      have hμ : μ₁ = μ₂ := by
        have m₁ := hres₁ g₁ μ₁ hsel₁.symm
        have m₂ := hres₂ g₂ μ₂ hsel₂.symm
        rw [R₁.resOrd_spec] at m₁
        rw [R₂.resOrd_spec] at m₂
        rw [← m₁, ← m₂, hread.2.1]
      -- Data fields, one by one.
      have he : ν₁.e = ν₂.e := by rw [← hSe₁, ← hSe₂, hSS]
      have hh : ν₁.h = ν₂.h := by rw [← hSh₁, ← hSh₂, hSS]
      have hl : ν₁.ℓ = ν₂.ℓ := by rw [← hSl₁, ← hSl₂, hSS]
      have hs : ν₁.s = ν₂.s := by rw [← hSs₁, ← hSs₂, hSS]
      have hu : ν₁.u = ν₂.u := by rw [← hSu₁, ← hSu₂, hSS]
      have hsel : ν₁.sel = ν₂.sel := by
        rw [← hsel₁, ← hsel₂, hg, hμ]
      -- inc = 1 iff e·g ≥ 2 (W2), with e and g already tied.
      have hinc : ν₁.inc = ν₂.inc := by
        have w₁ := hwf₁.w2 i ν₁ g₁ μ₁ hν₁ hsel₁.symm
        have w₂ := hwf₂.w2 i ν₂ g₂ μ₂ hν₂ hsel₂.symm
        rw [he, hg] at w₁
        exact Bool.eq_iff_iff.mpr (w₁.trans w₂.symm)
      exact congrArg some
        (ENodeData.ext_fields he hh hl hs hu hsel hinc)
    · rw [List.getElem?_eq_none (le_of_not_gt hi),
        List.getElem?_eq_none (by omega : H₂.nodes.length ≤ i)]
  exact EHist.ext_fields hbase hpsi0 ha0 hnodes hfld hpsihat

end LeanUrat.Scaffold.DictIII

-- Footprint audit (unit III-A1 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.recoverNode
#print axioms LeanUrat.Scaffold.DictIII.recoverEHist

-- Footprint audit (unit III-A6c gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.o2aGateReader
#print axioms LeanUrat.Scaffold.DictIII.o2aGate_side_returned
#print axioms LeanUrat.Scaffold.DictIII.o2aGate_law_fires

-- Footprint audit (unit III-A2 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.lemmaR_recovers
#print axioms LeanUrat.Scaffold.DictIII.lemmaR_theta_injective

-- Footprint audit (unit III-A6b): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.gmnReaderOrder1
#print axioms LeanUrat.Scaffold.DictIII.gmnReaderOrder1_side_eq_none
#print axioms LeanUrat.Scaffold.DictIII.GMNReader.laws_pin_fields
#print axioms LeanUrat.Scaffold.DictIII.gmnReaderOrder1_gate_side
#print axioms LeanUrat.Scaffold.DictIII.gmnReaderOrder1_gate_agrees

-- Footprint audit (unit III-A9): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.ol6_of_consF

-- Footprint audit (unit III-A3 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.terminalRecovery_false_of_witness
#print axioms LeanUrat.Scaffold.DictIII.A3Gate.terminalRecovery_false
#print axioms LeanUrat.Scaffold.DictIII.A3Gate.witness_pair_gate
#print axioms LeanUrat.Scaffold.DictIII.ol6_at_o2aGate
#print axioms LeanUrat.Scaffold.DictIII.ol6Gate_fired
#print axioms LeanUrat.Scaffold.DictIII.ol6Gate_conclusion_fires

-- Footprint audit (unit III-A6a): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.gmnDataOrder1
#print axioms LeanUrat.Scaffold.DictIII.matchedSideAt_spec
#print axioms LeanUrat.Scaffold.DictIII.matchedDatum_spec
#print axioms LeanUrat.Scaffold.DictIII.gmnDataOrder1_residualDegree
#print axioms LeanUrat.Scaffold.DictIII.mem_principalData
#print axioms LeanUrat.Scaffold.DictIII.sideRead_gmnDataOrder1
