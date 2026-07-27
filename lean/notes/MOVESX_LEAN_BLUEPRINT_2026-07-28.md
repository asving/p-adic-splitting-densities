# MOVES §X-EXHAUST — Lean formalization blueprint (MovesX corpus, 2026-07-28)

*Blueprint deliverable for the campaign (LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md §2 format).
Source of truth: the DUAL-ACCEPTED §X-EXHAUST rev 8 (`lean/notes/MOVES_2026-07-24.md`
lines ~10947–11555; acceptance record at "§X-EXHAUST: DUAL-ACCEPTED (2026-07-27)").
Consumes MovesSp per the campaign DAG; MovesSp is being blueprinted in parallel, so all
species names below are PLANNED names cited generically (`MovesSp.Letter`, …) — exact-name
sync at the Defs round. Written Protocol-L: verbatim names, statements re-bound at use.*

Discipline: NO new axioms except the already-allowed GMN index theorem (rides here as an
INTERFACE, §D6, so this corpus itself declares nothing). The campaign kernels of this note
— (X1a-ALIGN)=(ALIGN-inc)/(ALIGN-rec), WEIGHT-CHARGE, PROGRESS=(X2-AFF)/(X2-BRIDGE)/(X2-CAP),
(X2-TAILS), VP-SOUND, (ns-null) — are HYPOTHESIS STRUCTURES, never axioms, never silently
strengthened or dropped. `sorry`-free ≠ non-vacuous; statement-fence applies.

---

## 0. What §X-EXHAUST is, and what is formalizable NOW

The note is the exhaustion tie-in in four layers: **X.1a** a per-species INDEX TABLE
(rows T0–T5 keyed by the §M-SPECIES letter fields e, h, ℓ, selection) turning certified
classifier depth into GMN index, hence into v_p(disc f) — pointwise, measure-free,
conditional exactly on (X1a-ALIGN); **X.1b** the WEIGHT-CHARGE budget for uncertified
nodes (OPEN kernel; only its two-step REDUCTION display is derived); **X.2** the
quantitative dichotomy (kernel OPEN; only (X2-HYP)'s √N shape is derived given
(X2-AFF)∧(X2-CAP)); **X.3** the density form (TGT) consumes, assembled from X.1a + the
ELEMENTARY DISCRIMINANT TAIL (3b) with every conditionality tagged.

Formalizable-now split (the MovesC pattern):
- **DERIVED layer (provable outright):** the row classification + selection constraint;
  the (P1)-pin lattice counts and per-row increments; the T3 degree charge; the (CD)
  definition and its d_cert ≡ 0 consequence; the four-population partition; the X.1b
  reduction ARITHMETIC; (X2-HYP)'s counting + product dichotomy; the (τ-ns)-FREE
  predicate and cap TOTALITY conventions; the elementary tail (3b) (the one genuinely
  new mathematical content — §1 D5 for the Mathlib design); X.3's assembly LOGIC.
- **HYPOTHESIS layer (statements only, faithful):** the ALIGN sub-clauses, WEIGHT-CHARGE
  (full + T4-restricted), (X2-AFF), (X2-CAP), (X2-BRIDGE), (X2-TAILS), the X.2 linear
  target, VP-SOUND, (ns-null) tag, and the tree/measure interfaces owed by MovesD/MovesT
  (which MovesX may not import — campaign DAG: MovesX consumes MovesSp ONLY).

---

## 1. Design decisions

**D1 — Nodes = planned MovesSp letters + retained height pair.** §M-SPECIES strikes
heights from the letter; the X table needs (e, h, ℓ, selection). So
`XNode := { letter : MovesSp.Letter n, h : ℕ, hpos : 1 ≤ h, hcop : Nat.Coprime e h, … }`
(fields via planned MovesSp projections `MovesSp.Letter.eRead/ell/selection`; the raw
side left endpoint s₀′ and height base u ride as ℕ fields for the region model). A
history is `H : List (XNode n)`; `Continuing ν := ν.selection ≠ ⊥`. NO tree object is
built here — T_can, strata, Undec ride in interface structures (D7), keeping the campaign
DAG honest (MovesD/MovesT come later).

**D2 — DOUBLED index, division-free.** All table values carry a factor ½; we store
`ind2 : ℕ` (twice the index): T1 ↦ ℓ·(e·h·ℓ − e − h + 1), T2 ↦ (e−1)·(h−1), T3/T4 ↦ 0.
The chain (X.1a) becomes `v_p(disc f) ≥ Σ ind2` — literally the note's
`v_p(disc f) ≥ 2·CUM(j)` (X.5(i)). No ℚ anywhere in the table layer.

**D3 — The (P1) region as a Finset.** `p1Region (s u e h ℓ)` := the lattice points
on-or-below the side segment, strictly above the horizontal line L through the last
point, strictly beyond the vertical line L′ through the initial point (Remark 4.14
conventions, PINNED — the on-or-below clause is load-bearing: T1's witness sits ON S).
Defined as a `Finset (ℕ × ℕ)` by decidable inequalities on a bounding box. Per-row
lemmas are `Finset.card` facts; the (IND) identity is `2 · card = ℓ(ehℓ−e−h+1)` (§3 LAT
units). Witness-membership lemmas are `decide`-shaped memberships plus arithmetic.

**D4 — (CD) as a discharge-state-indexed count.** `AlignState := {inc : Bool, rec : Bool}`
(the two separately-dischargeable sub-clauses). `dCert st H` counts continuing T1/T2
nodes whose sub-clause flag per st is set ((ALIGN-inc) for increments+T2, (ALIGN-rec)
additionally for T1 recenterings). `dCert ⟨false,false⟩ H = 0` is a THEOREM (today's
honest state); `dUnc := dTotal − dCert`. No `d_gen^sem` is ever defined (note's fence).

**D5 — Mathlib discriminant decision (THE design decision).** Mathlib HAS
`Polynomial.resultant` (Sylvester det, `RingTheory/Polynomial/Resultant/Basic.lean`,
~186-lemma API incl. `resultant_eq_prod_roots_sub`, `resultant_eq_zero_iff`) and
`Polynomial.discr` (sign-adjusted `sylvesterDeriv` det) with `resultant_deriv`:
`Res(f, f′) = (−1)^{n(n−1)/2}·lc(f)·discr f`. DECISION: the corpus discriminant is
**`Polynomial.discr` over ℤ_p (`PadicInt`), compared to `resultant f f.derivative`
via `resultant_deriv`** (monic ⟹ lc = 1 ⟹ equal valuations; sign is a unit). The
tail (3b) is stated at FINITE LEVEL, division-free: counting `a : Fin n → ZMod (p^D)`
with `discr (polyOf a) = 0` in `ZMod (p^D)` — legal because discr is a ℤ-polynomial in
the coefficients, so the event `v_p(disc f) ≥ D` is a level-D cylinder (the map-
commutation unit XF.1). The analytic core (roots of f′) lives over a splitting field L
of f′ with an absolute value extending |·|_p — packaged as ONE interface `ValExt`
(PROV/IF: Mathlib's `spectralNorm` + `Krasner.lean` machinery is the discharge route;
if the fleet finds it heavy the interface rides, flagged). NO p-adic Haar measure is
used anywhere: all masses are `Nat.card` box fractions (MovesC M4 pattern).

**D6 — The GMN index apparatus as an interface.** (P1)/(P2)/Thm 4.18(1)/Cor 4.19 are
published (GMN_citations.md); the ALLOWED-axiom route exists, but MovesX stays
axiom-clean by bundling exactly what X.1a consumes into `IndexApparatus` (§2): `ind`,
`vdisc`, the (P2) inequality `vdisc f ≥ 2·ind f`, and the per-order sum lower bound.
Declaring the actual GMN axiom (+ faithfulness entry + guardian audit) is HC-2's/a
later designer's call; the chain theorem here is conditional on the structure either way.

**D7 — Owed-elsewhere objects as interface structures.** Strata/T_can/Undec(N)/TB-CAP
caps/(τ-ns) tracks are MovesD/MovesT property. MovesX types against them through
`XTreeInterface` (finitely-branching menus, branch membership, per-node cell-data
`nsTrack` predicate with a Decidable instance, detection cells + caps) and
`XMassInterface` (level-N box fractions in ℚ, antitone Undec via N-stability, the
detection and ns-null fields). Every field is quoted against its note display in §4.

---

## 2. Proposed Defs skeleton (`lean/LeanUrat/MovesX/Defs.lean`)

```lean
import LeanUrat.Moves.Defs            -- Stage vocabulary (accepted)
-- import LeanUrat.MovesSp.Defs       -- at Defs-sync round: MovesSp.Letter etc.
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace LeanUrat.MovesX

/-! §A  Nodes and rows (X.0 + THE INDEX TABLE) -/

/-- A branch node: a planned `MovesSp.Letter` with the height pair the catalogue
    forgets restored, plus the raw frame coordinates the (P1) region needs.
    PLACEHOLDER FIELDS until the MovesSp Defs sync; keyed fields are final. -/
structure XNode (n : ℕ) where
  e   : ℕ           -- side stride e_read (lowest-terms slope denominator)
  h   : ℕ           -- slope height h_r (RETAINED here; not a letter field)
  ell : ℕ           -- normalized side length ℓ = w′/e
  sel : Option (ℕ × ℕ)   -- selection (g, μ) or ⊥  [MovesSp.Letter.selection]
  isIncrement : Bool     -- D.8 increment (true) vs D.10 recentering (false)
  s0  : ℕ           -- raw left endpoint of the side (region model)
  u0  : ℕ           -- raw height of the side's LAST point (region model)
  epos : 1 ≤ e
  hpos : 1 ≤ h
  ellpos : 1 ≤ ell
  hcop : Nat.Coprime e h
  selBound : ∀ g μ, sel = some (g, μ) → 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ ell

abbrev XHistory (n : ℕ) := List (XNode n)

def XNode.continuing (ν : XNode n) : Bool := ν.sel.isSome

/-- The T1–T5 row classification (T0 is NOT a node — level-0 openings excluded
    upstream by the history type itself; (P3)(iii)). -/
inductive Row | T1 | T2 | T3 | T4 | T5 deriving DecidableEq, Repr

def rowOf (ν : XNode n) : Row :=
  if ν.sel = none then .T5
  else if 2 ≤ ν.ell then .T1
  else if 2 ≤ ν.e then (if 2 ≤ ν.h then .T2 else .T3)
  else .T4

/-! §B  The (P1) region and the doubled index table (D2/D3) -/

/-- Remark 4.14's counted set for the side from (s0, u0 + h·ell) to
    (s0 + e·ell, u0): on-or-below S, strictly above L (y > u0), strictly
    beyond L′ (x > s0).  On-or-below S ⟺ h·(x − s0) + e·(y − u0) ≤ e·h·ell. -/
def p1Region (s0 u0 e h ell : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc s0 (s0 + e * ell) ×ˢ Finset.Ioc u0 (u0 + h * ell)).filter
    (fun q => h * (q.1 - s0) + e * (q.2 - u0) ≤ e * h * ell)

def XNode.region (ν : XNode n) : Finset (ℕ × ℕ) :=
  p1Region ν.s0 ν.u0 ν.e ν.h ν.ell

/-- The DOUBLED table value (D2): T1 ↦ ℓ(ehℓ−e−h+1), T2 ↦ (e−1)(h−1), else 0. -/
def ind2 (ν : XNode n) : ℕ :=
  match rowOf ν with
  | .T1 => ν.ell * (ν.e * ν.h * ν.ell + 1 - ν.e - ν.h)
  | .T2 => (ν.e - 1) * (ν.h - 1)
  | _   => 0

/-! §C  (CD) certified depth and the four populations (X.0 + X.3(a)) -/

/-- The two separately-dischargeable (X1a-ALIGN) sub-clauses. -/
structure AlignState where
  inc : Bool    -- (ALIGN-inc) discharged?
  rec : Bool    -- (ALIGN-rec) discharged?

def certified (st : AlignState) (ν : XNode n) : Bool :=
  ν.continuing &&
    match rowOf ν with
    | .T1 => (ν.isIncrement && st.inc) || (!ν.isIncrement && st.rec)
    | .T2 => st.inc          -- T2 is increment-only (g = μ = 1, key ×e)
    | _   => false           -- T3/T4: permanently NOT-CERT; T5 not counted

def dTotal (H : XHistory n) : ℕ := (H.filter (·.continuing)).length
def dCert (st : AlignState) (H : XHistory n) : ℕ := (H.filter (certified st)).length
def dUnc (st : AlignState) (H : XHistory n) : ℕ := dTotal H - dCert st H

/-- The four-population partition of continuing nodes (X.3(a)). -/
inductive Pop | incT12 | recT1 | t3 | t4 deriving DecidableEq
def popOf? (ν : XNode n) : Option Pop := … -- none on T5/non-continuing

def maxH (H : XHistory n) : ℕ := (H.map (·.h)).foldr max 0   -- max h(∅) = 0
```

```lean
/-! §D  (τ-ns)-FREE and the cap conventions (X.2 DOMAIN CONVENTIONS, rev 4/5) -/

/-- The tree-side data MovesX types against but does not build (D7).
    Every field is a note display; see §4 audit table. -/
structure XTreeInterface (n : ℕ) where
  Branch    : Type                          -- finite branches/prefixes of T_can^τ
  hist      : Branch → XHistory n           -- its read history
  nsTrack   : XNode n → Prop                -- per-node cell-data predicate (VP clauses)
  nsDec     : DecidablePred nsTrack
  capDetectable : Branch → Prop             -- ≥1 window read reaching a (τ-irr) cell
  capDec    : DecidablePred capDetectable
  detCap    : Branch → ℕ                    -- TB-CAP cap of H's OWN cells (τ-irr side)
  complete  : Branch → Prop                 -- finite branch of a complete τ-halted tree

variable {n : ℕ} (I : XTreeInterface n)

/-- (τ-ns)-FREE: no node of H lies on a (τ-ns) track — the membership
    predicate ITSELF excludes them (rev 5: unions do not route). -/
def NsFree (b : I.Branch) : Prop := ∀ ν ∈ I.hist b, ¬ I.nsTrack ν
instance : DecidablePred (NsFree I) := …   -- List.decidableBAll via nsDec

/-- The FOURTH-PIECE FAMILY predicate (X.2 rev 5). -/
def FourthPiece (b : I.Branch) : Prop := I.complete b ∧ NsFree I b

/-- cap(H), TOTAL by the DOMAIN CONVENTIONS: genuine cap on cap-detectable
    branches, 0 on hen/no-window branches. -/
def capH (b : I.Branch) : ℕ := if I.capDetectable b then I.detCap b else 0

/-! §E  The named kernel/hypothesis structures (statements ONLY; §X.4 perimeter) -/

structure IndexApparatus (n : ℕ) (p : ℕ) where      -- D6 (GMN (P2) + Thm 4.18(1))
  Poly    : Type                                     -- monic separable deg-n f over ℤ_p
  vdisc   : Poly → ℕ                                 -- v_p(disc f) (disc ≠ 0 side)
  ind     : Poly → ℕ
  p2      : ∀ f, 2 * ind f ≤ vdisc f                 -- (P2), reducible case included
  inStratum : Poly → XHistory n → Prop               -- f ∈ stratum(H)

structure X1aAlign (n p : ℕ) (A : IndexApparatus n p) (st : AlignState) : Prop … :=
  -- the ONE transported consequence X.1a consumes (assembly paragraph):
  (transport : ∀ f H, A.inStratum f H → dCert st H ≤ A.ind f)

structure WeightChargeT4 (n p : ℕ) (A : IndexApparatus n p) where   -- X.3(a1) burden
  s : ℕ                                              -- s(n), explicit
  bound : ∀ f H, A.inStratum f H → countPop H .t4 ≤ s * A.vdisc f

structure WeightChargeFull (n p : ℕ) (A : IndexApparatus n p) where -- X.1b kernel
  s : ℕ
  bound : ∀ f H, A.inStratum f H →
    countPop H .recT1 + countPop H .t4 ≤ s * A.vdisc f

structure X2Aff (n : ℕ) (I : XTreeInterface n) where       -- (X2-AFF), OPEN
  c0 : ℕ ; c0pos : 1 ≤ c0
  bound : ∀ b, threshold I b ≤ 1 + c0 * sumH I b            -- Σ over ALL reads

structure X2Cap (n : ℕ) (I : XTreeInterface n) where        -- (X2-CAP), OPEN
  ccap : ℕ
  bound : ∀ b, FourthPiece I b → capH I b ≤ ccap * (1 + sumH I b)

structure X2Bridge (n : ℕ) (I : XTreeInterface n) (M : XMassInterface n) : Prop …
  -- Undec(N) ⊆ {disc=0} ∪ (𝒯^ns fibers) ∪ {infinite branch} ∪
  --            {∃ (τ-ns)-FREE finite branch, threshold + cap > N}   (level-relative)

structure X2Tails (n p : ℕ) (M : XMassInterface n) where    -- [2b]-owed, hypothesis
  CT cT : ℕ ; cTpos : 1 ≤ cT
  bound : ∀ N hstar, M.tallFrac N hstar * (p : ℚ)^(cT * hstar) ≤ CT * 1

structure X2Progress (n : ℕ) (I : XTreeInterface n) where   -- the X.2 linear target
  cd cd' ch ch' : ℕ ; cdpos : 1 ≤ cd ; chpos : 1 ≤ ch
  dichotomy : ∀ b N, FourthPiece I b → N < threshold I b + capH I b →
    cd * N ≤ dTotal (I.hist b) + cd' ∨ ch * N ≤ maxH (I.hist b) + ch'

/-! §F  The discriminant model (D5) + the mass interface -/

def polyOfCoeffs (R) [CommRing R] (n : ℕ) (a : Fin n → R) : Polynomial R :=
  X^n + ∑ i, C (a i) * X^(i : ℕ)                     -- the monic box polynomial

-- level-D tail event, division-free (D5):
def tailCount (p n D : ℕ) : ℕ :=
  Nat.card {a : Fin n → ZMod (p^D) // Polynomial.discr (polyOfCoeffs _ n a) = 0}

structure XMassInterface (n : ℕ) where                -- D7, MovesT/MovesD-owed
  undecFrac : ℕ → ℚ                                   -- μ(Undec(N)), box fraction
  undecAntitone : Antitone undecFrac                  -- Thm 2.1 N-stability
  nonneg : ∀ N, 0 ≤ undecFrac N
  deepFrac  : ℕ → ℕ → ℚ                               -- μ{d_total ≥ d}, per level
  tallFrac  : ℕ → ℕ → ℚ                               -- μ{max h ≥ h*}, per level
  nsNull : Prop                                        -- (ns-null) TAG (closed at [3t];
                                                       --  displayed per (NS-c) rule)
  detection : Prop                                     -- X.3(b): 𝒯^fin f exits at thr(T)
  vpSound : Prop                                       -- VP-SOUND (HEN-LIFT)/(OM-SAT)

end LeanUrat.MovesX
```

(`threshold I b`, `sumH I b` := Σ_{reads of b} h_r, `countPop` are Defs-level
abbreviations over `XTreeInterface`/`XHistory`; elaboration round makes the `…`
Prop-structures literal. The skeleton COMPILING with placeholder `Prop` fields is
the E-gate entry criterion.)

---

## 3. The units (id · statement · moves_ref · deps · sketch · difficulty · hypothesis_fields)

Files: `lean/LeanUrat/MovesX/<id>.lean`, each importing `MovesX.Defs` + deps.

### Layer A — the index table (X.1a's DERIVED core)

**XA.1 rowTotal** — `theorem rowTotal (ν : XNode n) : ν.continuing → (rowOf ν = .T1 ↔ 2 ≤ ν.ell) ∧ (rowOf ν = .T5 ↔ False) ∧ …` (the exactly-one-row trichotomy, stated as the three defining iffs).
moves_ref: "Every continuing node of every history falls in exactly one row (ℓ ≥ 2 vs ℓ = 1; then e, h…)". deps: Defs. sketch: `rowOf` is an if-chain; `unfold` + `omega`/`decide`. EASY. hyp_fields: none.

**XA.2 selForce** — `theorem selForce (ν : XNode n) (g μ) (hs : ν.sel = some (g,μ)) (h2 : 2 ≤ μ ∨ 2 ≤ g) : 2 ≤ ν.ell` (hence rowOf = T1).
moves_ref: "the selection constraint μ·g ≤ d(S) = ℓ forces every μ ≥ 2 or g ≥ 2 selection onto an ℓ ≥ 2 side". deps: Defs. sketch: from `selBound`: μ·g ≤ ℓ with the other factor ≥ 1; `nlinarith`/`omega`. EASY. hyp: none.

**XA.3 t1Witness** — `theorem t1Witness (ν) (h1 : rowOf ν = .T1) : (ν.s0 + ν.e, ν.u0 + (ν.ell − 1) * ν.h) ∈ ν.region ∧ 1 ≤ ν.region.card`.
moves_ref: T1 row, witness "(s+e, u+(ℓ−1)h): ON S one e-step from its initial point; strictly above L …; strictly beyond L′". deps: Defs. sketch: membership = three inequalities: x > s0 (e ≥ 1); y − u0 = (ℓ−1)h ≥ h ≥ 1 > 0 (ℓ ≥ 2); on S: h·e + e·(ℓ−1)h = ehℓ ✓ (ON-OR-BELOW pin — equality case included by design, D3). `Finset.card_pos` via nonempty. EASY. hyp: none. WATCH: this witness is exactly the (P1) on-or-below convention; a strictly-below region def would break HERE — the audit must check `p1Region`'s `≤`.

**XA.4 t1Arith** — `theorem t1Arith (e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 2 ≤ ell) : h * (ell − 1) ≤ e * h * ell + 1 − e − h ∧ 1 ≤ ell * (e * h * ell + 1 − e − h)` plus the ℕ-subtraction guard `e + h ≤ e * h * ell + 1`.
moves_ref: T1 ind column "½ℓ(ehℓ−e−h+1) ≥ ½ℓ·h(ℓ−1) ≥ 1 [e ≥ 1: ehℓ−e−h+1 = e(hℓ−1)−(h−1) ≥ h(ℓ−1)]". deps: none. sketch: `nlinarith` on the bracket identity; the guard makes T1's `ind2` truncation-free. EASY. hyp: none.

**XA.5 t2Witness** — `theorem t2Witness (ν) (h2 : rowOf ν = .T2) : (ν.s0 + 1, ν.u0 + 1) ∈ ν.region ∧ 2 ≤ (ν.e − 1) * (ν.h − 1) ∧ 2 ∣ (ν.e − 1) * (ν.h − 1)`.
moves_ref: T2 "explicit witness (s+1, u+1) … strictly below S ⟺ (e−1)(h−1) > 1 — true since e, h ≥ 2 and gcd(e,h) = 1 excludes (2,2)"; value "(e−1)(h−1)/2 ≥ 1". deps: Defs. sketch: membership: h·1 + e·1 ≤ eh ⟺ (e−1)(h−1) ≥ 1; ≥ 2 and evenness: e,h ≥ 2 coprime ⟹ not both even ⟹ (e−1)(h−1) even; (2,2) killed by coprimality. `omega` + `Nat.Coprime` parity case split. EASY-MEDIUM. hyp: none.

**XA.6 lat1** (the coprime lattice count) — `theorem lat1 (s0 u0 e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.Coprime e h) : 2 * (p1Region s0 u0 e h 1).card = (e − 1) * (h − 1)`.
moves_ref: "(P1), Remark 4.14 … Pick-style split: strict-interior count (EH − E − H − d)/2 + 1, on-side non-vertex count d − 1" at ℓ = 1 (interior only; both endpoints excluded, no on-segment points by gcd). deps: Defs. sketch: the classical coprime-triangle count: pair (x,y) ↔ (e−x, h−y) is an involution on the open rectangle (1..e−1)×(1..h−1) swapping below-S and above-S; coprimality ⟹ no lattice point ON the open segment; so 2·#below = (e−1)(h−1). Finset bijection (`Finset.card_nbij`), no Mathlib Pick exists. HARD. hyp: none.

**XA.7 latGen** (the (IND) identity) — `theorem latGen (s0 u0 e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 1 ≤ ell) (hcop : Nat.Coprime e h) : 2 * (p1Region s0 u0 e h ell).card = ell * (e * h * ell + 1 − e − h)`. The region's card is (IND)'s full count — strict-interior (EH−E−H−d)/2 + 1 PLUS the d−1 on-side non-vertex points (each ON S, hence IN the on-or-below region). Sanity anchors carried as `example`s: ℓ = 1 reduces to XA.6 ((e−1)(h−1), since ℓ(ehℓ+1−e−h) = eh+1−e−h); e = h = ℓ = 1 gives 0.
moves_ref: "(IND) ind(S) = ½(EH − E − H + d) = ½·ℓ·(ehℓ − e − h + 1)". deps: XA.6. sketch: slice the length-eℓ side into ℓ coprime segments (XA.6 each), add the ℓ−1 interior stride vertices ON S and the sub-rectangles between slices; assemble by `Finset` disjoint-union arithmetic. HARD (the corpus's hardest derived unit; split further at elaboration if > 40 lines: XA.7a slicing partition, XA.7b arithmetic). hyp: none.

**XA.8 t34Zero** — `theorem t34Zero (ν) (h34 : rowOf ν = .T3 ∨ rowOf ν = .T4) : ν.region.card = 0 ∧ ind2 ν = 0`.
moves_ref: T3 "interior count (e−1)·0/2 = 0; endpoints excluded"; T4 "only the two endpoints are lattice points on S (gcd(e,h) = 1); both excluded". deps: XA.6 (or direct). sketch: ℓ = 1 and (h = 1 or e = 1) ⟹ (e−1)(h−1) = 0 ⟹ card = 0 by XA.6; `ind2` matches by `rfl`-cases. EASY given XA.6. hyp: none. NOTE (finding-1 semantics, carried in the docstring verbatim): "0" = NO positive per-side bound certified — NEVER "actual ind_r = 0".

**XA.9 ind2Region** — `theorem ind2Region (ν) (hc : ν.continuing) : ind2 ν ≤ 2 * ν.region.card ∧ (rowOf ν = .T1 ∨ rowOf ν = .T2 → 1 ≤ ind2 ν)`.
moves_ref: the table's ind(S) column as REGION counts (rows T1/T2 positive, T3/T4 zero). deps: XA.3–XA.8. sketch: per-row case split; T1 via XA.7 (drop the +(ℓ−1) slack) + XA.4; T2 via XA.6 + XA.5; T3/T4 via XA.8. MEDIUM. hyp: none.

### Layer B — (CD), populations, degree charge

**XB.1 dCertZero** — `theorem dCertZero (H : XHistory n) : dCert ⟨false, false⟩ H = 0 ∧ ∀ st, dCert st H ≤ dTotal H`.
moves_ref: "At today's discharge state (neither sub-clause displayed) d_cert ≡ 0"; d_unc = d_total − d_cert. deps: Defs. sketch: `certified ⟨false,false⟩ ν = false` by cases; filter-length monotone. EASY. hyp: none (this THEOREM is the honesty display: (X.1a) at zero discharge is trivially true).

**XB.2 dCertMono** — `theorem dCertMono (H) : dCert ⟨true, false⟩ H = countPop H .incT12 ∧ dCert ⟨true, true⟩ H = countPop H .incT12 + countPop H .recT1`.
moves_ref: "given (ALIGN-inc): d_cert = #T1-increments + #T2; given both: also the T1 recenterings". deps: Defs. sketch: filter/count case analysis on `rowOf`+`isIncrement`. EASY. hyp: none.

**XB.3 fourPop** — `theorem fourPop (H) : dTotal H = countPop H .incT12 + countPop H .recT1 + countPop H .t3 + countPop H .t4`.
moves_ref: "the four-population decomposition {T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}". deps: Defs. sketch: `popOf?` is total on continuing nodes (XA.1 trichotomy + T2-is-increment from selection (1,1) + `isIncrement` coherence field); List count partition. EASY-MEDIUM. hyp: none. AUDIT FLAG: T2 nodes must land in `incT12` — the Defs must pin `rowOf ν = .T2 → ν.isIncrement` as an XNode coherence field (T2 is increment-only per the table; carried as `t2inc` field, MovesSp-owed at sync).

**XB.4 t3Charge** — `theorem t3Charge (H) (hdeg : degCharge H n) : countPop H .t3 ≤ Nat.log 2 n` where `degCharge H n : Prop := 2 ^ (countPop H .t3) ≤ n` is a Defs abbreviation delivered by the species side (each T3 multiplies key degree by e ≥ 2, degree ≤ n).
moves_ref: "each T3 node multiplies the key degree by e ≥ 2, so #T3 per branch ≤ ⌊log₂ n⌋ (derived; charged additively, never absorbed)". deps: Defs. sketch: `Nat.log` bridge: 2^k ≤ n → k ≤ Nat.log 2 n (`Nat.pow_le_iff_le_log`, n ≥ 1). EASY. hyp_fields: `degCharge` — the ∏e ≤ n ladder is MovesSp/MovesD-owed (planned cite `MovesSp.degProd_le`); until sync it is this unit's named hypothesis.

### Layer C — the X.1a chain and the X.1b reduction (conditional theorems)

**XC.1 x1aChain** — `theorem x1aChain (A : IndexApparatus n p) (st : AlignState) (AL : X1aAlign n p A st) : ∀ f H, A.inStratum f H → 2 * dCert st H ≤ A.vdisc f`.
moves_ref: "(X.1a) stratum(H) ⊆ Desc_{d_cert(H)} ⊆ { v_p(disc f) ≥ 2·d_cert(H) } … conditional exactly on the sub-clauses certifying the counted nodes". deps: Defs. sketch: `AL.transport` gives dCert ≤ ind f; `A.p2` gives 2·ind ≤ vdisc; chain. EASY (glue by design: the whole GMN/ALIGN weight sits in the two structures). hyp_fields: `X1aAlign` (the (X1a-ALIGN) kernel — its `transport` field IS the note's assembly paragraph conclusion "ind(f) ≥ d_cert(H) for EACH branch"; the per-order/distinct-orders mechanism stays INSIDE the hypothesis, never re-derived here), `IndexApparatus` ((P2) + Thm 4.18(1), published — D6).

**XC.2 x1aTrivial** — `theorem x1aTrivial (A) : ∀ f H, A.inStratum f H → 2 * dCert ⟨false,false⟩ H ≤ A.vdisc f`.
moves_ref: "at zero discharge d_cert ≡ 0 and (X.1a) is trivially true". deps: XB.1. sketch: rewrite by dCertZero; `Nat.zero_le`. EASY. hyp: none — the corpus's honest UNCONDITIONAL instance of (X.1a), the d_cert ≡ 0 display.

**XC.3 x1bReduction** — `theorem x1bReduction (A) (AL : X1aAlign n p A ⟨true,false⟩) (WC : WeightChargeFull n p A) (f H) (hf : A.inStratum f H) (hdeg : degCharge H n) : 2 * dTotal H ≤ (2 * WC.s + 1) * A.vdisc f + 2 * Nat.log 2 n`.
moves_ref: "d_total ≤ [v_p(disc f)/2 + ⌊log₂ n⌋] + s(n)·v_p(disc f) ⟹ v_p(disc f) ≥ (d_total(H) − ⌊log₂ n⌋)/(s(n) + 1/2)" (the rev-2 two-step reduction, additive T3 offset). deps: XB.2, XB.3, XB.4, XC.1. sketch: fourPop splits dTotal; incT12 ≤ vdisc/2 via XC.1 at st=⟨true,false⟩ (doubled form avoids the /2); recT1 + t4 ≤ s·vdisc via WC; t3 ≤ log via XB.4; `omega`. MEDIUM. hyp_fields: X1aAlign(inc) AND WeightChargeFull — the note's finding 11 verbatim: "X.1b ALONE discharges nothing"; the division-free form `2·dTotal ≤ (2s+1)·v + 2·log` IS the display `v ≥ (dTotal − log)/(s + ½)` cleared of denominators (audit: check the algebra is the same inequality).

**XC.4 x1bReductionT4** — same statement with `WeightChargeT4` and conclusion restricted to the (a1)-route population count: `countPop H .t4 ≤ WC.s * A.vdisc f ∧ (st := ⟨true,true⟩ …) 2 * dTotal H ≤ (2 * WC.s + 1) * A.vdisc f + 2 * Nat.log 2 n`.
moves_ref: X.3(a1) "#T1/T2 = d_cert ≤ v_p(disc f)/2 by (X.1a) …; #T3 ≤ ⌊log₂ n⌋ …; #T4 ≤ s(n)·v_p(disc f) by WEIGHT-CHARGE RESTRICTED to the T4 population". deps: XB.2–4, XC.1. sketch: as XC.3 with st = ⟨true,true⟩ covering recT1 inside dCert. MEDIUM. hyp_fields: X1aAlign(both) ∧ WeightChargeT4 — route (a1)'s exact tag.

### Layer D — the (τ-ns)-FREE predicate, cap conventions, (X2-HYP)

**XD.1 nsFreeDec** — `instance (I : XTreeInterface n) : DecidablePred (NsFree I)` + `theorem capTotal (I) (b) : (¬ I.capDetectable b → capH I b = 0) ∧ (I.capDetectable b → capH I b = I.detCap b)` + `theorem maxHNil : maxH ([] : XHistory n) = 0`.
moves_ref: "the membership predicate itself excludes them"; "cap(H) := 0 for every hen/no-window branch"; "max h(∅) := 0 … no empty max is ever taken". deps: Defs. sketch: `List.decidableBAll`; `if` splits; `rfl`. EASY. hyp: interface fields only.

**XD.2 x2hypCount** — `theorem x2hypCount (I) (b) : sumH I b ≤ (dTotal (I.hist b) + 1) * maxH (I.hist b) ∨ I.hist b = []` — with `sumH` counting ALL reads (continuing + ≤ 1 terminal).
moves_ref: "H's reads are its d_total continuing nodes PLUS at most one terminal read … Σ_{r∈H} h_r ≤ (d_total(H) + 1)·max h(H); the d_total = 0 lone-terminal-read history is carried by the +1". deps: Defs. sketch: each h_r ≤ maxH; #reads ≤ dTotal + 1 needs the history WELL-FORMEDNESS field (at most one terminal, terminal last — an `XHistory` invariant `wf : atMostOneTerminal` added to Defs; audit flag). List induction + `Nat.sum_le_card_nsmul`-style. MEDIUM. hyp: the `wf` invariant (MovesSp/MovesD-owed: branches read terminals last).

**XD.3 x2hypDichotomy** — `theorem x2hypDichotomy (M d m : ℕ) (h : M < (d + 1) * m) : M < (d + 1)^2 ∨ M < m^2`.
moves_ref: "(d_total+1)·max h > (N−1−c_cap)/c₀⁺ ⟹ d_total + 1 ≥ √(…) OR max h ≥ √(…) — square-root, NOT linear". deps: none. sketch: contrapositive: (d+1)² ≤ M ∧ m² ≤ M ⟹ ((d+1)·m)² ≤ M² ⟹ (d+1)·m ≤ M; `nlinarith`. EASY. (√-free integer form; audit: the note's √ display is the same statement squared.)

**XD.4 x2hypAssembled** — `theorem x2hypAssembled (I) (AF : X2Aff n I) (CP : X2Cap n I) (b) (hb : FourthPiece I b) (N) (hN : N < threshold I b + capH I b) : (N − 1 − CP.ccap) < (AF.c0 + CP.ccap) * (dTotal (I.hist b) + 1)^2 ∨ (N − 1 − CP.ccap) < (AF.c0 + CP.ccap) * maxH (I.hist b)^2` (ℕ-truncated subtraction; c₀⁺ := c0 + ccap kept multiplied through, division-free).
moves_ref: "(X2-HYP) The hyperbolic dichotomy (DERIVED given (X2-AFF) ∧ (X2-CAP) …): threshold(H) + cap(H) > N ⟹ Σ h_r > (N−1−c_cap)/c₀⁺ ⟹ (d_total+1)·max h > (N−1−c_cap)/c₀⁺ ⟹ …". deps: XD.1–XD.3. sketch: AF.bound + CP.bound price both terms in Σ h_r; combine, then XD.2, then XD.3. MEDIUM. hyp_fields: X2Aff, X2Cap (both OPEN kernels, owned by PROGRESS — consumed by name, exactly the note's tag).

### Layer E — kernel statements only (the E-gate compiles them; NO proofs ever asked)

**XE.1 kernelDefs** — the Defs §E structures themselves elaborate (`X1aAlign`, `WeightChargeT4/Full`, `X2Aff`, `X2Cap`, `X2Bridge`, `X2Tails`, `X2Progress`) + one NONVACUITY smoke instance each over a toy 1-node interface (fields inhabited with trivial data — vacuity guard, MovesC discipline).
moves_ref: X.4's OPEN-KERNEL list verbatim (one docstring per structure quoting its display). deps: Defs. EASY (elaboration). hyp: these ARE the hypotheses.

**XE.2 envelopeStatement** — `def EnvBound (M : XMassInterface n) (p : ℕ) (K : EnvKernels) : Prop := ∀ N, M.undecFrac N * (p : ℚ)^(K.c4 * N) ≤ K.c3` (division-free ℚ form of env(N) ≤ c₃·p^{−c₄N}). STATEMENT-ONLY def + the tag-trace docstring (c₃, c₄ traced to s(n), c₀, C_T, c_T, c_cap).
moves_ref: "env(N) ≤ c₃(n)·p^{−c₄(n)·N}, with c₃, c₄ traced to s(n) (X.1b), c₀ ((X2-AFF)), C_T, c_T ((X2-TAILS)), c_cap ((X2-CAP))". deps: Defs. EASY (statement). hyp: EnvKernels bundles ALL X.2 tags — the CONDITIONALITY SUMMARY as a structure; no unit proves it (SQ-side consumption is MovesU's).

### Layer F — the ELEMENTARY DISCRIMINANT TAIL (3b), designed against Mathlib (D5)

Target display (rev 8): `(3b) μ{ f monic deg n : v_p(disc f) ≥ D } ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉} → 0`, corollary `μ{disc f = 0} = 0`. Lean form (finite-level, division-free): with `D' := ⌈(D − n·(padicValNat p n))/(n−1)⌉` (ℕ-ceiling; the bound is trivial when D ≤ n·v_p(n)):
> `(3b-LEAN)  tailCount p n D * p^(D') ≤ (n−1) * p^(n*D)`  — fraction form `tailCount/p^{nD} ≤ (n−1)·p^{−D'}`.

**XF.1 discCylinder** — `theorem discCylinder (p n D) (f : Polynomial ℤ_[p]) (hm : f.Monic) (hd : f.natDegree = n) : (∀ i, (f.coeff i).appr D = coeffs-of-a) → ((p:ℤ_[p])^D ∣ Polynomial.discr f ↔ Polynomial.discr (polyOfCoeffs (ZMod (p^D)) n a) = 0)`.
moves_ref: Lemma 3.3's proof-shape premise — the event {v_p(disc f) ≥ D} is coefficient-cylinder data (implicit in "union bound + Fubini" over the box). deps: Defs. sketch: `discr` is a det of coefficient matrix entries; ring-hom map `ℤ_[p] → ZMod (p^D)` commutes with det (`RingHom.map_det`) and with `derivative`/`sylvester` entries; needs a `discr_map` helper (natDegree preserved by monic: leading coeff 1 ≠ 0 in both). MEDIUM. hyp: none. Mathlib gap flagged: no `Polynomial.discr_map` lemma exists yet — the unit proves it for the monic case (natDegree-stable maps).

**XF.2 discResBridge** — `theorem discResBridge (f : Polynomial ℤ_[p]) (hm : f.Monic) (h1 : 1 ≤ f.natDegree) : ‖Polynomial.discr f‖ = ‖f.resultant f.derivative‖` (valuation form: equal v_p).
moves_ref: "(P2); reducible case via Def 4.11 + disc(PQ) = …" — here only the disc↔Res(f,f′) normalization for monic f. deps: Defs. sketch: Mathlib `Polynomial.resultant_deriv`: Res(f,f′) = (−1)^{n(n−1)/2}·lc·discr; lc = 1 (monic); ‖±x‖ = ‖x‖. EASY-MEDIUM (arg wrangling: `natDegree`-defaults of `resultant`). hyp: none.

**XF.3 valExt** — the interface + its discharge attempt: `structure ValExt (p) (g : Polynomial ℚ_[p]) where L : Type; [field : Field L]; [alg : Algebra ℚ_[p] L]; w : AbsoluteValue L ℝ; ext : ∀ x : ℚ_[p], w (algebraMap _ L x) = ‖x‖; splits : Polynomial.Splits (algebraMap ℚ_[p] L) g` — and `def valExtOf (g) : ValExt p g` via SplittingField + spectral norm.
moves_ref: Lemma 3.3 "Res(f, f′) over the n−1 roots of f′" — the roots need a valued home; no note display beyond the accepted proof-on-record. deps: Defs. sketch (discharge route): `g.SplittingField` is finite over ℚ_[p] (complete, nonarch); `spectralNorm ℚ_[p] L` is a power-multiplicative norm extending ‖·‖ and multiplicative on finite extensions of a complete rank-1 valued field (Mathlib `Analysis/Normed/Unbundled/SpectralNorm.lean` + `SpectralMulAlgNorm`); package as `AbsoluteValue`. HARD (Mathlib-archaeology unit; if the mult-instance is missing for ℚ_[p], the interface RIDES and the unit delivers only the structure + a flagged `sorry`-free statement holder). hyp: itself when undischarged.

**XF.4 resRootSum** — `theorem resRootSum (V : ValExt p (fPoly a).derivative) (a : Fin n → ℤ_[p]) (h2 : 2 ≤ n) : ‖resultant (fPoly a) (fPoly a).derivative‖ = ‖(n : ℚ_[p])‖^n * ∏ θ ∈ ((fPoly a).derivative.roots-in-L), V.w (aeval θ (fPoly a))` (multiset product over roots with multiplicity, n−1 of them).
moves_ref: "Res(f, f′) over the n−1 roots of f′" with the n·v_p(n) offset — X.3's (3b) exponent "(D − n·v_p(n))/(n−1)". deps: XF.3. sketch: map Res to L (`resultant_map`? exists for `natDegree`-stable maps — check; else prove); over L use Res(f,g) = (−1)^{deg f·deg g}·lc(g)^{deg f}·∏_{g(θ)=0} f(θ) — Mathlib has `resultant_eq_prod_roots_sub` + eval-product helpers (`map_sub_sprod_roots_eq_prod_map_eval`); lc(f′) = n, deg f = n gives ‖n‖^n. HARD. hyp: ValExt.

**XF.5 pigeonMax** — `theorem pigeonMax (m : Multiset ℚ) (hm : m ≠ 0) (K : ℚ) (h : K ≤ m.sum) : ∃ v ∈ m, K ≤ (m.card : ℚ) * v` — max ≥ average, division-free, applied to the VALUATIONS vᵢ := −log_p(V.w(f(θᵢ))) of the n−1 root terms (ℚ-valued: w takes rational p-powers on algebraic elements): Σ vᵢ ≥ D − n·v_p(n) gives some (n−1)·vᵢ ≥ D − n·v_p(n).
moves_ref: the max-term step inside Lemma 3.3 ("some θᵢ has v_p(f(θᵢ)) ≥ (D − n·v_p(n))/(n−1)"). deps: none (pure `Finset.exists_le_of_sum_le` arithmetic). EASY. hyp: none. AUDIT FLAG: terms may be NEGATIVE (non-integral roots make w(f(θ)) > 1); max ≥ average needs no sign hypothesis — the statement must NOT assume vᵢ ≥ 0.

**XF.6 ballCover** (pairwise-congruence form — centers live in L, so no ℚ_[p]-center is ever claimed; the covering is consumed only through this congruence) — `theorem ballCover (p n D) (h2 : 2 ≤ n) (aTail : Fin (n−1) → ℤ_[p]) (V : ValExt p (fTail aTail).derivative) : ∃ idx : ℤ_[p] → Fin (n−1), ∀ a0 b0 : ℤ_[p], Event D a0 → Event D b0 → idx a0 = idx b0 → (p : ℤ_[p])^(D' ) ∣ (a0 − b0)` — where `Event D a0` := `(p:ℤ_[p])^D ∣ discr (fPoly (Fin.cons a0 aTail))`, `idx` assigns each event point a root index of f′, and D' is the XF.5 threshold.
moves_ref: "the a₀-translation, union bound + Fubini" (Lemma 3.3's proof on record): f(θ) = a₀ + c(θ) with c a₀-independent. deps: XF.2, XF.4, XF.5. sketch: f′ is a₀-independent (derivative kills the constant term — THE a₀-translation), so its root multiset in V.L is one fixed object; for an event point, XF.2+XF.4+XF.5 give a root θᵢ with w(a₀ + c(θᵢ)) ≤ p^{−D'} — set idx a0 := that i; two event points at the same i are p^{−D'}-close to the same −c(θᵢ), hence to each other (ultrametric), and w extends ‖·‖_p on ℚ_[p] (V.ext), giving the ℤ_[p]-divisibility. MEDIUM-HARD. hyp: ValExt.

**XF.7 tailCount** — `theorem tailCountBound (p n D) (hp : p.Prime) (h2 : 2 ≤ n) : tailCount p n D * p^(D') ≤ (n−1) * p^(n*D)` (D' as in (3b-LEAN); the degenerate D ≤ n·v_p(n) and n = 1 faces stated as trivial clauses).
moves_ref: "(3b) μ{…} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉}" — THE display. deps: XF.1, XF.6. sketch: fiber the count over aTail ∈ (ZMod p^D)^{n−1} (lift each fiber to ℤ_p, XF.1); within a fiber, XF.6's pairwise congruence puts all event-a₀'s into ≤ n−1 classes mod p^{D'}, each of ≤ p^{D−D'} residues mod p^D; sum: ≤ (n−1)·p^{D−D'}·p^{(n−1)D}. `Nat.card` fiber arithmetic = the MovesC M4 pattern. MEDIUM-HARD. hyp: ValExt (via XF.6).

**XF.8 tailZero** — `theorem tailZero (p n) (hp) (h2 : 2 ≤ n) : Filter.Tendsto (fun D => (tailCount p n D : ℚ) / p^(n*D)) Filter.atTop (nhds 0)` + corollary `discZeroNull`: the disc-vanishing locus has fraction ≤ every (3b) bound (the μ{disc f = 0} = 0 reading at finite level).
moves_ref: "→ 0 as D → ∞; corollary μ{disc f = 0} = 0". deps: XF.7. sketch: D' → ∞ linearly in D; geometric decay; `Tendsto` squeeze over ℚ→ℝ. MEDIUM. hyp: ValExt (inherited).

### Layer G — X.3's qualitative assembly (the conditional theorem, tags displayed)

The route tag is a Defs-level disjunction type, so no route is ever silently preferred:
```lean
/-- X.3(a)'s hypothesis alternatives — the CONDITIONALITY SUMMARY verbatim:
    [(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)]. -/
inductive X3aRoute (n p : ℕ) (A : IndexApparatus n p)
  | a1 (al : X1aAlign n p A ⟨true, true⟩)  (wc : WeightChargeT4 n p A)
  | a2 (al : X1aAlign n p A ⟨true, false⟩) (wc : WeightChargeFull n p A)
```

**XG.1 branchLenBound** — `theorem branchLenBound (A) (R : X3aRoute n p A) (f H) (hf : A.inStratum f H) (hdeg : degCharge H n) : dTotal H ≤ (2 * R.s + 1) * A.vdisc f + Nat.log 2 n` (with `R.s` the route's s(n); statement identical on both routes — the PROOF differs per route).
moves_ref: X.3(a) "EITHER route gives every branch finite pointwise, by the four-population decomposition {T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}: (a1) … OR (a2) …". deps: XB.3, XB.4, XC.3, XC.4. sketch: case on R; (a1): dCert⟨true,true⟩ covers incT12 + recT1 ≤ vdisc/2 (doubled), t4 ≤ s·vdisc, t3 ≤ log; (a2): XC.3 verbatim. `omega` assembly. MEDIUM. hyp_fields: X3aRoute (BOTH disjuncts carry X.1b's T4 leg — the note: "NO route avoids X.1b").

**XG.2 koenigFinite** — `theorem koenigFinite (I : XTreeInterface n) (hfb : FinBranching I) (hlen : ∀ b : I.Branch, dTotal (I.hist b) ≤ B) : TreeFinite I B` — with `FinBranching`/`TreeFinite` Defs-level interface predicates (finite child menus; finitely many branches, all of bounded length).
moves_ref: "TREE-FINITE BRIDGE [rev 2, finding 12]: T_can(f) is FINITELY BRANCHING — … §M-SPECIES' finite letter menus — so König's lemma upgrades 'every branch finite' to 'T_can(f) finite'". deps: Defs. sketch: bounded-depth + finitely-branching ⟹ finite by induction on B (the bounded form avoids full König: XG.1 gives a UNIFORM per-f bound, so no infinite-path compactness is needed — König cited by the note, but the formal route is the bounded one; audit: this is a WEAKER premise-use, not a statement change). deps on MovesSp finite-menu cite (planned `MovesSp.menuFinite`). MEDIUM. hyp: interface + finite menus.

**XG.3 x3Density** — the capstone statement:
```lean
theorem x3Density (n p) (A : IndexApparatus n p) (I : XTreeInterface n)
    (M : XMassInterface n)
    (R : X3aRoute n p A)                  -- X.3(a)'s displayed tag
    (hns : M.nsNull)                      -- (ns-null): CLOSED at [3t]; tag DISPLAYED
    (hdet : M.detection)                  -- X.3(b): Thm 2.1 + TB-CAP (MovesT-owed)
    (hvp : M.vpSound)                     -- VP-SOUND: (HEN-LIFT)/(OM-SAT), inherited
    (hlink : MassLink A I M)              -- the (a)+(c) ⟹ intersection-null glue field
    : Filter.Tendsto M.undecFrac Filter.atTop (nhds 0)
```
moves_ref: "Statement (X.3) … the undecided complement has mass 0; equivalently μ(Undec(N)) → 0 (N → ∞)" + the CONDITIONALITY SUMMARY line (rev 3). deps: XG.1, XG.2, XD.1. sketch: `M.undecAntitone` + `M.nonneg` give convergence to the inf; `MassLink` (the interface field carrying "the intersection has mass 0" from (a)+(c) pointwise finiteness + (3b)'s corollary + countable-ns — the MEASURE-side glue MovesX cannot build without MovesD fibers, stated as: inf undecFrac = 0 given the pointwise pieces) closes it. MEDIUM (the analysis is elementary once MassLink is typed; the WEIGHT sits in the hypothesis fields — by design, this is [5]'s qualitative clause, not a proof of the kernels). hyp_fields: X3aRoute, nsNull, detection, vpSound, MassLink — one-to-one with the note's tag list; the audit MUST check nothing extra and nothing missing.

**XG.4 x3Series** — statement-only: `def X3SeriesIdentity (M) (σ …) : Prop := HasSum (fun T : M.FinTree σ => M.fiberFrac T) (M.densityσ σ)` — the per-σ tree-fiber series display, typed over interface fields (`FinTree`, `fiberFrac`, `densityσ` — MovesD/MovesT-owed; the 𝒯^ns fibers' 0 dropped with the (ns-null) tag in the docstring).
moves_ref: "for each type σ the tree-fiber series sums the full density: Σ … = density_σ(p), with the 𝒯^ns fibers' total contribution dropped as 0 [(ns-null) tag displayed per (NS-c)]". deps: Defs. EASY (statement; the (3e)/Tonelli regrouping PROOF is RS-side, MovesS/MovesU territory — the note's ONE-cite-point discipline: X.3 is where [3]/(TGT)/E0 cite, and the X.4 consumer map "NOTHING here feeds RS.1, SQ.1, or RS.3" is reproduced in the file docstring). hyp: interface.

---

## 4. Audit table (trust surface for the Codex semantic gate)

| object | note display it must match | class |
|---|---|---|
| `p1Region`'s `≤` (on-or-below) | (P1)/Remark 4.14 pin + "T1 witness … ON S" + endpoint rulings | DEF — the corpus's sharpest trap; strictly-below would zero every e = 1 event |
| `rowOf` | table rows T1–T5 keyed (ℓ ≥ 2; ℓ = 1 by e, h; sel = ⊥) | DEF |
| `ind2` | (IND) doubled; T3/T4 ↦ 0 with finding-1 semantics in docstring | DEF |
| `certified`/`dCert` | (CD) verbatim incl. T2-inc-only; `dCertZero` = "d_cert ≡ 0 today" | DEF+THM |
| `X1aAlign.transport` | X.1a assembly paragraph's conclusion (ind ≥ d_cert) | HYP (kernel) |
| `WeightChargeT4/Full` | the boxed WEIGHT-CHARGE display, T4 vs full burden (rev 3) | HYP (kernel) |
| `X2Aff/X2Cap/X2Bridge/X2Tails/X2Progress` | (X2-AFF)/(X2-CAP)/(X2-BRIDGE)/(X2-TAILS)/(X.2) displays | HYP (kernels) |
| `NsFree`/`FourthPiece`/`capH`/`maxH ∅ = 0` | X.2 DOMAIN CONVENTIONS (rev 4/5) | DEF |
| `tailCount` + (3b-LEAN) | Lemma 3.3's (3b), finite-level division-free transcription | DEF+THM — audit the ⌈·⌉ arithmetic and the n·v_p(n) offset |
| `ValExt` | (no note display — Lemma 3.3's proof apparatus) | IF (flag: NOT a note object; must never strengthen (3b)'s statement) |
| `IndexApparatus` | (P2) + Thm 4.18(1) via D.12 dictionary (GMN pins) | IF (published; axiom candidate at HC-2) |
| `XTreeInterface`/`XMassInterface`/`MassLink` | §D4-R/§T-ASSEMBLY objects X.3 types against | IF (MovesD/MovesT-owed; re-audited at wave 4 sync) |
| `X3aRoute` | "[(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)]" | DEF (tag structure) |

## 5. Census and counts

**35 units.** EASY 16 (XA.1–4, XA.8, XB.1, XB.2, XB.4, XC.1, XC.2, XD.1, XD.3, XE.1, XE.2, XF.5, XG.4 — of which XE.1/XE.2/XG.4 are statement-only by design), MEDIUM 13 (XA.5, XA.9, XB.3, XC.3, XC.4, XD.2, XD.4, XF.1, XF.2, XF.8, XG.1, XG.2, XG.3), HARD 6 (XA.6, XA.7 — the two lattice-count units; XF.3, XF.4 — the ValExt/Mathlib-archaeology units; XF.6, XF.7 — the covering/Fubini pair, scored medium-hard). [Re-scored at E-gate; the escalation-risk set is exactly the six HARD ids; XA.7 pre-authorized to split (XA.7a/b).]
Sealed-gate X.5 layers (census runs) are NOT Lean units — runtime artifacts, out of corpus.
NOT formalized (statements exist upstream or nowhere): X.1b's kernel derivation (OPEN),
X.2's kernel (OPEN), the STALL-probe, (X2-TAILS)'s derivation ([2b]-owed), the envelope's
SQ-side consumption (MovesU). This matches X.4's DERIVED-vs-OPEN perimeter line by line.
