# MOVES §X-EXHAUST — Lean formalization blueprint (MovesX corpus)
# REV 4 (post-Fable-audit: the 4 rev-3 residue findings repaired; surgical)
# + XE.2/XE.3 RESTATED POST-REFUTATION (2026-07-27, stuck-rule adjudication; §7)

*Rev 4, 2026-07-28. Repairs the 4 residue findings of the fresh-Fable audit
`lean/notes/MOVESX_AUDIT_FABLE_2026-07-28.md` (REJECT 2 crit / 2 gap; all 13 rev-3 repairs
verified GENUINE, all arithmetic and derivation chains independently re-derived clean).
ONLY the four flagged objects changed: X2BridgeP's witness, vdisc's signature, the
ℤ_[p]→ℚ_[p] hom name, fTail/Event's Fin arity. Cumulative findings→repairs table in §6.
Ground truth unchanged: DUAL-ACCEPTED §X-EXHAUST rev 8 (`MOVES_2026-07-24.md`
~10947–11555). Protocol-L. Next: parallel dual confirmation (Codex final + fresh Fable).*

**ORCHESTRATOR RULINGS APPLIED (verbatim scope):**
- **RULING 1 (findings 6/4/5/2, structural):** kernels are PROPS OVER THE CONCRETE
  CONTEXT. One shared corpus parameter — `XFamily n` bundling, for every prime p, the
  concrete monic box `MonicBox n p` (a DEFINED type over `ℤ_[p]`, with `vdisc`/`discZero`
  DEFINED via `Polynomial.discr`), the tree context `XCtx n p`, and the GMN interface.
  Every kernel (X2-*, WEIGHT-CHARGE, ALIGN) is a `Prop` parameterized by `(X : XFamily n)`
  and n-only constants: asserting the kernel = asserting the note's condition about THE
  objects; no kernel carries its own F/branch/frac data, so degenerate self-inhabitation
  is impossible by construction. The tall event is a DEFINED set (`TallEvent`), not a free
  field; `frac Set.univ = 1` is a context field; (X2-CAP)'s quantifier sits inside the
  ns-free fourth-piece family.
- **RULING 2 (finding 9):** the note's (3b) and X.3 displays are UNCONDITIONAL (given p
  prime, n ≥ 2) — so XF.7/XF.8/XF.10/XG.3 carry NO `ValExt` argument. The valuation-
  extension content lives only INSIDE the tail-derivation internals (XF.4/XF.6), discharged
  by D8's construction (XF.3) within XF.7's proof. If the construction genuinely cannot be
  completed, that is a STUCK report to the orchestrator, never a silent hypothesis rider.
  (XF.9 is DELETED — its role is absorbed; finding 8 thereby closed.)

Discipline: NO new axioms; open kernels are named Props consumed by name; accepted/owed
interface fields are each ONE note-cited input (never an in-section conclusion — findings
11/12); `sorry`-free ≠ non-vacuous; statement-fence applies.

---

## 0. What §X-EXHAUST is, and what is formalizable NOW

Four layers: **X.1a** the index table (T0–T5 by letter fields) → GMN index → v_p(disc),
pointwise, conditional exactly on (X1a-ALIGN); **X.1b** WEIGHT-CHARGE (OPEN; reduction
DISPLAY derived); **X.2** the dichotomy (OPEN; (X2-HYP) derived given (X2-AFF)∧(X2-CAP));
**X.3** the density form from X.1a + the elementary tail (3b), every tag displayed.

DERIVED in-corpus (rev 3 expands this list per findings 7/11/12): the full A/B layers
(unchanged; arithmetic independently confirmed); the X.1a chain and reduction; (X2-HYP);
the tail (3b) UNCONDITIONAL (Ruling 2); the envelope theorems (exponential AND √N
fallback) as ∃-statements GIVEN the tag set (finding 7); X.3(a) pointwise tree-finiteness,
X.3(b) finite-level detection, the (d)-trichotomy intersection inclusion, König, and the
per-σ series — all UNITS now, not fields (findings 10/11/12).
HYPOTHESIS layer (kernel Props over `XFamily n`, one unit each): (ALIGN-inc)/(ALIGN-rec),
WEIGHT-CHARGE (T4/full), (X2-AFF), (X2-CAP), (X2-BRIDGE), (X2-TAILS), (X2-PROGRESS),
(ns-null) tag, VP-SOUND — plus the accepted/owed CONTEXT FIELDS of `XCtx` (each one
note-cited local input: Thm 2.1 per-branch detection, TB-CAP caps, the Undec definition,
(NS-c) indexing, box-content laws), audited one-by-one in §4.

---

## 1. Design decisions

**D1 (unchanged) — nodes/histories.** `XNode n` with letter fields + coherence
(`t2inc`/`t3inc`/`t4rec`); `HistWF` (termLast, degProd) = ACCEPTED-source facts, planned
MovesSp discharge. **D2 (unchanged)** doubled index `ind2`. **D3 (unchanged)** `p1Region`
Finset, (P1) pin, EQUALITY tie. **D4 (unchanged)** `AlignState`/`dCert`/`DescX`.

**D5 (upgraded — the carrier is now CONCRETE).** `MonicBox n p :=
{f : Polynomial ℤ_[p] // f.Monic ∧ f.natDegree = n}`; `discZero := {f | f.1.discr = 0}`;
`vdisc f := (f.1.discr).valuation` (pinned `PadicInt.valuation : ℤ_[p] → ℕ`, already
ℕ-valued — Fable finding 2; junk 0 on discZero via `valuation_zero`; every statement using it
carries `f ∉ discZero`). Tail (3b) at finite level over `ZMod (p^D)` via
`PadicInt.toZModPow`; INTEGER exponent `tailExp : ℤ` (spot checks re-confirmed by the
auditor: 4 and 1/4 at (2,2,0)/(2,2,4); 2/3, 2/9, 2/27 at (3,3,5/7/9)).

**D6 (retyped) — GMN interface over the concrete carrier.** `GMNIndex n p`: only `ind`
and `inStratum` remain fields; `vdisc`/`discZero` are DEFINED (D5), so (P2) is a field
about concrete valuations. Published (GMN); real instance owner MovesD/HC-2.

**D7 (rebuilt per Ruling 1 + findings 11/12) — ONE concrete context.** `XCtx n p` = the
per-f rooted-forest tree presentation (Branch f, hist, root/parent/children/reach), the
detection vocabulary (`DetectedAt`, `threshold`, `capDetectable`/`detCap`, `nsTrack`),
the (NS-c) fiber family, and the box content `frac` with `frac_univ = 1` (finding 5).
The rev-2 fields `detectInter`, `stratumLink`, `infBranch`, `tallFrac`, `link`, `hσ`,
`densityσ` are DELETED: `InfTree`, `TallEvent`, `DeepEvent`, `densityOf` are DEFINED sets/
quantities, and the X.3(b)/(d) content is DERIVED by units XG.2b–d (findings 4/11/12).
Remaining fields are each ONE note-cited input, listed and quoted in §4.

**D8 (unchanged route, Ruling-2 placement) — ValExt.** Constructed by XF.3
(`SplittingField` + `spectralNorm`); consumed EXPLICITLY only by the internals XF.4/XF.6;
discharged inside XF.7's proof. No public statement mentions it.

**D9 (NEW — p-freeness by parameter order, finding 3).** All kernel constants live in
`XConsts n` — a structure indexed by n ALONE, defined before any p enters scope. Kernel
Props take `(X : XFamily n) (K : XConsts n)` and quantify `∀ p [Fact p.Prime]` INSIDE.
A constant cannot depend on p because p is not in scope where the constant is bound.

---

## 2. Proposed Defs skeleton (`lean/LeanUrat/MovesX/Defs.lean`) — REV 3

```lean
import LeanUrat.Moves.Defs
-- import LeanUrat.MovesSp.Defs   -- Defs-sync round
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace LeanUrat.MovesX

/-! §A Nodes, rows, region, doubled index (UNCHANGED from rev 2; arithmetic confirmed) -/

structure XNode (n : ℕ) where
  e ell h s0 u0 : ℕ
  sel : Option (ℕ × ℕ)
  isIncrement : Bool
  epos : 1 ≤ e ; hpos : 1 ≤ h ; ellpos : 1 ≤ ell
  hcop : Nat.Coprime e h
  selBound : ∀ g μ, sel = some (g, μ) → 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ ell
  t2inc : ell = 1 → 2 ≤ e → 2 ≤ h → sel.isSome → isIncrement = true
  t3inc : ell = 1 → 2 ≤ e → h = 1 → sel.isSome → isIncrement = true
  t4rec : ell = 1 → e = 1 → sel.isSome → isIncrement = false

abbrev XHistory (n : ℕ) := List (XNode n)
def XNode.continuing (ν : XNode n) : Bool := ν.sel.isSome

inductive Row | T1 | T2 | T3 | T4 | T5 deriving DecidableEq, Repr
def rowOf (ν : XNode n) : Row :=
  if ν.sel = none then .T5
  else if 2 ≤ ν.ell then .T1
  else if 2 ≤ ν.e then (if 2 ≤ ν.h then .T2 else .T3) else .T4

def p1Region (s0 u0 e h ell : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc s0 (s0 + e * ell) ×ˢ Finset.Ioc u0 (u0 + h * ell)).filter
    (fun q => h * (q.1 - s0) + e * (q.2 - u0) ≤ e * h * ell)
def XNode.region (ν : XNode n) : Finset (ℕ × ℕ) := p1Region ν.s0 ν.u0 ν.e ν.h ν.ell

def ind2 (ν : XNode n) : ℕ :=
  match rowOf ν with
  | .T1 => ν.ell * (ν.e * ν.h * ν.ell + 1 - ν.e - ν.h)
  | .T2 => (ν.e - 1) * (ν.h - 1)
  | _   => 0

structure AlignState where (inc rec : Bool)
def certified (st : AlignState) (ν : XNode n) : Bool :=
  ν.continuing && match rowOf ν with
    | .T1 => (ν.isIncrement && st.inc) || (!ν.isIncrement && st.rec)
    | .T2 => st.inc
    | _   => false
def dTotal (H : XHistory n) : ℕ := (H.filter (·.continuing)).length
def dCert (st : AlignState) (H : XHistory n) : ℕ := (H.filter (certified st)).length
def dUnc (st : AlignState) (H : XHistory n) : ℕ := dTotal H - dCert st H

inductive Pop | incT12 | recT1 | t3 | t4 deriving DecidableEq
def popOf? (ν : XNode n) : Option Pop :=
  if ¬ ν.continuing then none else some (match rowOf ν, ν.isIncrement with
    | .T1, true => .incT12 | .T2, _ => .incT12 | .T1, false => .recT1
    | .T3, _ => .t3 | .T4, _ => .t4 | .T5, _ => .t4)
def countPop (H : XHistory n) (c : Pop) : ℕ := (H.filter (popOf? · = some c)).length
def maxH (H : XHistory n) : ℕ := (H.map (·.h)).foldr max 0
def sumH (H : XHistory n) : ℕ := (H.map (·.h)).sum

structure HistWF (n : ℕ) (H : XHistory n) : Prop where
  termLast : ∀ i : Fin H.length, (i : ℕ) + 1 < H.length → (H.get i).continuing = true
  degProd  : ((H.filter (fun ν => ν.continuing && ν.isIncrement)).map (·.e)).prod ≤ n

/-! §B The CONCRETE carrier (D5; Ruling 1) -/

def MonicBox (n p : ℕ) [Fact p.Prime] : Type :=
  { f : Polynomial ℤ_[p] // f.Monic ∧ f.natDegree = n }
def discZero (n p : ℕ) [Fact p.Prime] : Set (MonicBox n p) := { f | f.1.discr = 0 }
noncomputable def vdisc {n p : ℕ} [Fact p.Prime] (f : MonicBox n p) : ℕ :=
  (f.1.discr).valuation      -- ℕ-valued in pinned mathlib (PadicIntegers.lean:321);
                             -- junk value 0 on discZero (valuation_zero); guarded at every use

def polyOfCoeffs (R : Type) [CommRing R] (n : ℕ) (a : Fin n → R) : Polynomial R :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)
def tailCount (p n D : ℕ) : ℕ :=
  Nat.card { a : Fin n → ZMod (p ^ D) // (polyOfCoeffs _ n a).discr = 0 }
def tailExp (p n D : ℕ) : ℤ := ⌈((D : ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ)⌉

/-- The a₀-free monic family tail and the level-D disc event (rev 4, Fable findings 3/4:
    hom name = pinned `PadicInt.Coe.ringHom` (PadicIntegers.lean:130); the Fin (n−1+1)/Fin n
    unification via an explicit OUTER `Fin.cast` on the index, legal from `hn : 1 ≤ n` —
    threaded from every consumer's `h2 : 2 ≤ n`. Derivative kills a₀: any slot-0 value
    gives the same fTail. -/
def fTail (n p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (aTail : Fin (n - 1) → ℤ_[p]) :
    Polynomial ℚ_[p] :=
  ((polyOfCoeffs ℤ_[p] n
      ((Fin.cons 0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map
    PadicInt.Coe.ringHom).derivative
def Event (p n D : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (aTail : Fin (n - 1) → ℤ_[p])
    (a0 : ℤ_[p]) : Prop :=
  (p : ℤ_[p]) ^ D ∣ (polyOfCoeffs ℤ_[p] n
      ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).discr

structure ValExt (p : ℕ) [Fact p.Prime] (g : Polynomial ℚ_[p]) where
  L : Type ; [field : Field L] ; [alg : Algebra ℚ_[p] L]
  w : AbsoluteValue L ℝ
  ext : ∀ x : ℚ_[p], w (algebraMap ℚ_[p] L x) = ‖x‖
  splits : (g.map (algebraMap ℚ_[p] L)).Splits (RingHom.id L)
```

```lean
/-! §C The GMN interface (D6) and the ONE concrete context (D7; Ruling 1) -/

/-- Published GMN consumption surface over the CONCRETE carrier: (P2) + Thm 4.18(1).
    Real instance: OM engine; owner MovesD/HC-2 (wave 4/phase 3). -/
structure GMNIndex (n p : ℕ) [Fact p.Prime] where
  ind : MonicBox n p → ℕ
  inStratum : MonicBox n p → XHistory n → Prop
  p2 : ∀ f, f ∉ discZero n p → 2 * ind f ≤ vdisc f

/-- THE context: per-f canonical tree presentation + detection vocabulary + ns fibers +
    box content. Each field = ONE note-cited accepted/owed LOCAL input (§4 quotes each);
    the X.3(a)/(b)/(d) CONCLUSIONS are units XG.2b–d, never fields (findings 11/12). -/
structure XCtx (n p : ℕ) [Fact p.Prime] where
  Branch : MonicBox n p → Type
  hist : ∀ {f}, Branch f → XHistory n
  wf : ∀ {f} (b : Branch f), HistWF n (hist b)
  root : ∀ f, Branch f
  hist_root : ∀ f, hist (root f) = ([] : XHistory n)
  parent : ∀ {f}, Branch f → Option (Branch f)
  parent_hist : ∀ {f} (b b' : Branch f), parent b = some b' → ∃ ν, hist b = hist b' ++ [ν]
  parent_root : ∀ f, parent (root f) = none
  reach : ∀ {f} (b : Branch f), Relation.ReflTransGen (fun c d => parent c = some d) b (root f)
  children : ∀ {f}, Branch f → Finset (Branch f)          -- FINITE menus (§M-SPECIES)
  children_iff : ∀ {f} (b c : Branch f), c ∈ children b ↔ parent c = some b
  complete : ∀ {f}, Branch f → Prop        -- full branch of a complete τ-halted tree
  nsTrack : XNode n → Prop ; nsDec : DecidablePred nsTrack
  capDetectable : ∀ {f}, Branch f → Prop ; capDec : ∀ f, DecidablePred (@capDetectable f)
  detCap : ∀ {f}, Branch f → ℕ             -- TB-CAP cap of the branch's OWN cells
  threshold : ∀ {f}, Branch f → ℕ          -- Thm 2.1's per-stratum N₀
  DetectedAt : ∀ {f}, Branch f → ℕ → Prop  -- "this leaf branch is cap-detected at level N"
  detectBranch :                            -- Thm 2.1 + TB-CAP per-clause caps (X.3(b) INPUT)
    ∀ {f} (b : Branch f), IsLeafB b → (∀ ν ∈ hist b, ¬ nsTrack ν) →
      ∀ N, threshold b + capHB b ≤ N → DetectedAt b N
  Undec : ℕ → Set (MonicBox n p)
  undec_spec :                              -- X.0's DEFINITION of Undec, pinned
    ∀ f N, f ∉ Undec N ↔ (Finite (Branch f) ∧ ∀ b : Branch f, IsLeafB b → DetectedAt b N)
  undec_antitone : Antitone Undec           -- Thm 2.1 N-stability
  nsIdx : Type ; nsCountable : Countable nsIdx            -- (NS-c) symbolic indexing
  nsFiber : nsIdx → Set (MonicBox n p)
  nsCover :                                 -- ns-leaf f's covered by the fiber family
    ∀ f, (∃ b : Branch f, IsLeafB b ∧ ∃ ν ∈ hist b, nsTrack ν) → ∃ i, f ∈ nsFiber i
  frac : Set (MonicBox n p) → ℚ
  frac_univ : frac Set.univ = 1             -- NORMALIZED (finding 5)
  frac_nonneg : ∀ s, 0 ≤ frac s
  frac_mono : ∀ s t, s ⊆ t → frac s ≤ frac t
  frac_union_le : ∀ s t, frac (s ∪ t) ≤ frac s + frac t
  frac_iUnion_null : ∀ (s : ℕ → Set (MonicBox n p)), (∀ i, frac (s i) = 0) → frac (⋃ i, s i) = 0
  frac_inter_tendsto :                      -- monotone convergence for the box content
    Filter.Tendsto (fun N => frac (Undec N)) Filter.atTop (nhds (frac (⋂ N, Undec N)))
  vdisc_le_tail :                           -- the level-D cylinder fact (definitional at sync)
    ∀ D, frac { f | D ≤ vdisc f ∨ f ∈ discZero n p } ≤ (tailCount p n D : ℚ) / p ^ (n * D)

-- Defs-level abbreviations on XCtx (C : XCtx n p), {f} implicit:
--   IsLeafB b := C.children b = ∅                          -- "finite branch" = leaf-terminated
--   capHB b := if C.capDetectable b then C.detCap b else 0 -- cap conventions (TOTAL)
--   NsFreeB b := ∀ ν ∈ C.hist b, ¬ C.nsTrack ν             -- (τ-ns)-FREE, decidable
--   FourthPieceB b := (IsLeafB b ∨ ∃ b', C.complete b' ∧ isPrefixB b b') ∧ NsFreeB b
--       -- finding 1 REPAIRED: the 'finite branch' disjunct restored verbatim
--   isPrefixB b b' := Relation.ReflTransGen (fun c d => C.parent c = some d) b' b
--   InfTree : Set (MonicBox n p) := { f | ¬ Finite (C.Branch f) }        -- DEFINED (not a field)
--   TallEvent (hstar : ℕ) : Set (MonicBox n p) :=                        -- DEFINED (finding 4)
--       { f | ∃ b : C.Branch f, ∃ ν ∈ C.hist b, hstar ≤ ν.h }
--   DeepEvent (d : ℕ) : Set (MonicBox n p) := { f | ∃ b : C.Branch f, d ≤ dTotal (C.hist b) }

/-- The corpus's ONE shared parameter (Ruling 1): the concrete objects for every prime,
    with the tree-to-stratum tie. Real instance owner: MovesD/MovesT (wave-4 sync);
    ONE inhabitation obligation for the whole corpus, tracked in the campaign ledger. -/
structure XFamily (n : ℕ) where
  ctx : ∀ (p : ℕ) [Fact p.Prime], XCtx n p
  gmn : ∀ (p : ℕ) [Fact p.Prime], GMNIndex n p
  gmnLink :                                  -- §D4-R: f lies in the stratum of each of
    ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (ctx p).Branch f),  -- its own histories
      (gmn p).inStratum f ((ctx p).hist b)

/-- n-ONLY constants (D9, finding 3): defined BEFORE any p is in scope, so p-freeness
    is enforced by binder order, not convention. -/
structure XConsts (n : ℕ) where
  s : ℕ                                      -- WEIGHT-CHARGE's s(n)
  c0 ccap : ℚ ; c0nonneg : 0 ≤ c0 ; ccapnonneg : 0 ≤ ccap    -- (X2-AFF)/(X2-CAP)
  cd cd' ch ch' : ℚ ; cdpos : 0 < cd ; chpos : 0 < ch        -- (X.2) target slopes
  CT cT : ℝ ; CTpos : 0 < CT ; cTpos : 0 < cT                -- (X2-TAILS)
```

```lean
/-! §D The kernels as Props over the shared context (Ruling 1; findings 2/3/4/6).
    Each `def …P : Prop` quotes its display in its docstring; asserting it = asserting
    the note's condition about THE objects. Variables: (X : XFamily n) (K : XConsts n);
    ∀ p INSIDE each Prop (D9). Abbreviations from the XCtx comment block in scope. -/

def X1aAlignP (n : ℕ) (X : XFamily n) (st : AlignState) : Prop :=      -- (X1a-ALIGN)
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H → dCert st H ≤ (X.gmn p).ind f

def WeightChargeT4P (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=  -- X.1b, T4 burden
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H → countPop H .t4 ≤ K.s * vdisc f

def WeightChargeFullP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop := -- X.1b, FULL burden
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H →
      countPop H .recT1 + countPop H .t4 ≤ K.s * vdisc f

def X2AffP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=            -- (X2-AFF)
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f),
    FourthPieceB b → ((X.ctx p).threshold b : ℚ) ≤ 1 + K.c0 * sumH ((X.ctx p).hist b)

def X2CapP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=            -- (X2-CAP)
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f),
    FourthPieceB b → (X.ctx p).capDetectable b →                        -- finding 2: inside
      ((X.ctx p).detCap b : ℚ) ≤ K.ccap * (1 + sumH ((X.ctx p).hist b)) --   the ns-free family

def X2ProgressP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=       -- (X.2) target
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f) (N : ℕ),
    FourthPieceB b → N < (X.ctx p).threshold b + capHB b →
      K.cd * N - K.cd' ≤ dTotal ((X.ctx p).hist b) ∨
      K.ch * N - K.ch' ≤ maxH ((X.ctx p).hist b)

def X2TailsP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=          -- (X2-TAILS)
  ∀ (p : ℕ) [Fact p.Prime] (hstar : ℕ),                                  -- finding 4: THE event
    ((X.ctx p).frac (TallEvent (X.ctx p) hstar) : ℝ) ≤ K.CT * (p : ℝ) ^ (-(K.cT * hstar))

def X2BridgeP (n : ℕ) (X : XFamily n) : Prop :=                          -- (X2-BRIDGE), both clauses
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
    ((X.ctx p).Undec N ⊆ discZero n p ∪ (⋃ i, (X.ctx p).nsFiber i) ∪ InfTree (X.ctx p) ∪
      { f | ∃ b : (X.ctx p).Branch f,
          IsLeafB b ∧ NsFreeB b ∧ N < (X.ctx p).threshold b + capHB b }) ∧
    (X.ctx p).frac { f | f ∈ (X.ctx p).Undec N ∧
      ¬ ∃ b : (X.ctx p).Branch f,
          IsLeafB b ∧ NsFreeB b ∧ N < (X.ctx p).threshold b + capHB b } = 0
  -- rev 4 (Fable finding 1): the note's "(τ-ns)-FREE FINITE BRANCH" witness — leaf-
  -- terminated (IsLeafB) in BOTH clauses. The witness then satisfies FourthPieceB via
  -- its FIRST disjunct (IsLeafB b) ∧ NsFreeB b, which is what X2ProgressP/XD.4 consume.

def NsNullP (n : ℕ) (X : XFamily n) : Prop :=                            -- (ns-null) TAG
  ∀ (p : ℕ) [Fact p.Prime] (i : (X.ctx p).nsIdx), (X.ctx p).frac ((X.ctx p).nsFiber i) = 0

/-- X.3(a)'s route disjunction, verbatim tags. -/
def X3aRouteP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  (X1aAlignP n X ⟨true, true⟩  ∧ WeightChargeT4P n X K) ∨
  (X1aAlignP n X ⟨true, false⟩ ∧ WeightChargeFullP n X K)

/-! §E Series objects (finding 12: densityOf DEFINED; finding 13: additivity defined) -/

/-- Per-(p) series presentation: the countable family of complete realizable finite
    trees with their fibers and letter-computed types. Fields = (NS-a)/§D4-R inputs;
    the density IDENTITY is the unit XG.4, never a field. Owner MovesD/MovesT. -/
structure SeriesData (n p : ℕ) [Fact p.Prime] (C : XCtx n p) where
  FinTree : Type ; treeCountable : Countable FinTree
  fiber : FinTree → Set (MonicBox n p)
  typemult : FinTree → SplitType n              -- the letter-computed type
  splitType : MonicBox n p → SplitType n        -- the TRUE splitting type of f
  fiber_disjoint : ∀ T T', T ≠ T' → Disjoint (fiber T) (fiber T')
  fiber_decided : ∀ T, Disjoint (fiber T) (⋂ N, C.Undec N)   -- fibers are decided sets
  decided_covered : ∀ f, f ∉ (⋂ N, C.Undec N) → f ∉ discZero n p → ∃ T, f ∈ fiber T

def densityOf (S : SeriesData n p C) (σ : SplitType n) : ℚ :=   -- DEFINED (finding 12)
  C.frac { f | S.splitType f = σ }

/-- VP-SOUND — (HEN-LIFT)/(OM-SAT): the typemult-to-true-type identification (note
    finding 13), the ONE place it is consumed. -/
def VPSoundP (S : SeriesData n p C) : Prop :=
  ∀ T (f : MonicBox n p), f ∈ S.fiber T → S.splitType f = S.typemult T

/-- The (3e)/Tonelli positive-term regrouping (finding 13 — now fully specified):
    countable additivity of the content on the disjoint fiber family. Owed (MovesD/T). -/
def CountableFiberAdditive (S : SeriesData n p C) : Prop :=
  ∀ (I : Set S.FinTree) (E : Set (MonicBox n p)),
    (∀ f ∈ E, ∃ T ∈ I, f ∈ S.fiber T) → (∀ T ∈ I, S.fiber T ⊆ E) →
    HasSum (fun T : I => C.frac (S.fiber T)) (C.frac E)

end LeanUrat.MovesX
```

(E-gate entry: this skeleton compiling, with the comment-block abbreviations
(`IsLeafB`, `capHB`, `NsFreeB`, `FourthPieceB`, `isPrefixB`, `InfTree`, `TallEvent`,
`DeepEvent`) made literal `def`s over `(C : XCtx n p)`, and `SplitType n` bound to the
campaign's target type at the Defs sync.)

---

## 3. The units (id · statement · moves_ref · deps · sketch · difficulty · hypothesis_fields)

Files `lean/LeanUrat/MovesX/<id>.lean`. Layers A/B are UNCHANGED from rev 2 (no rev-2
finding touched them; the two audited inequalities were independently confirmed) — full
statements restated for self-containedness, sketches abbreviated.

### Layer A — the index table (10 units, all statements frozen at rev 2)

**XA.1 rowTotal** — `theorem rowTotal (ν : XNode n) : (rowOf ν = .T5 ↔ ν.sel = none) ∧ (rowOf ν = .T1 ↔ ν.sel ≠ none ∧ 2 ≤ ν.ell) ∧ (rowOf ν = .T2 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ 2 ≤ ν.e ∧ 2 ≤ ν.h) ∧ (rowOf ν = .T3 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ 2 ≤ ν.e ∧ ν.h = 1) ∧ (rowOf ν = .T4 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ ν.e = 1)`. moves_ref: "Every continuing node … exactly one row (ℓ ≥ 2 vs ℓ = 1; then e, h…)". deps: Defs. EASY.
**XA.2 selForce** — `theorem selForce (ν) (g μ) (hs : ν.sel = some (g, μ)) (h2 : 2 ≤ μ ∨ 2 ≤ g) : 2 ≤ ν.ell ∧ rowOf ν = .T1`. moves_ref: "μ·g ≤ d(S) = ℓ forces every μ ≥ 2 or g ≥ 2 selection onto an ℓ ≥ 2 side". deps: XA.1. EASY.
**XA.3 t1Witness** — `theorem t1Witness (ν) (h1 : rowOf ν = .T1) : (ν.s0 + ν.e, ν.u0 + (ν.ell - 1) * ν.h) ∈ ν.region ∧ 1 ≤ ν.region.card`. moves_ref: T1 witness "(s+e, u+(ℓ−1)h): ON S …" — the (P1) ON-OR-BELOW pin (§4 trap). deps: XA.1. EASY.
**XA.4 t1Arith** — `theorem t1Arith (e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 2 ≤ ell) : e + h ≤ e * h * ell + 1 ∧ h * (ell - 1) ≤ e * h * ell + 1 - e - h ∧ 1 ≤ ell * (e * h * ell + 1 - e - h)`. moves_ref: T1 column bracket "[e ≥ 1: ehℓ−e−h+1 = e(hℓ−1)−(h−1) ≥ h(ℓ−1)]". deps: none. EASY.
**XA.5 t2Witness** — `theorem t2Witness (ν) (h2 : rowOf ν = .T2) : (ν.s0 + 1, ν.u0 + 1) ∈ ν.region ∧ 2 ≤ (ν.e - 1) * (ν.h - 1) ∧ 2 ∣ (ν.e - 1) * (ν.h - 1)`. moves_ref: T2 witness "(s+1, u+1) … gcd(e,h) = 1 excludes (2,2)". deps: XA.1. EASY-MEDIUM→MEDIUM band.
**XA.6 lat1** — `theorem lat1 (s0 u0 e h : ℕ) (he) (hh) (hcop : Nat.Coprime e h) : 2 * (p1Region s0 u0 e h 1).card = (e - 1) * (h - 1)`. moves_ref: "strict-interior count (EH−E−H−d)/2 + 1, on-side non-vertex count d − 1" at ℓ = 1. sketch: center-reflection involution + no on-segment points (coprime). HARD.
**XA.7a latSlice** — `theorem latSlice (s0 u0 e h ell) (he) (hh) (hl : 1 ≤ ell) : (p1Region s0 u0 e h ell).card = ∑ k ∈ Finset.range ell, ((p1Region (s0 + k * e) (u0 + (ell - 1 - k) * h) e h 1).card + e * ((ell - 1 - k) * h))`. moves_ref: (IND)'s region as column blocks (slice above rectangle; stride vertices absorbed). HARD.
**XA.7b latGen** — `theorem latGen (s0 u0 e h ell) (he) (hh) (hl) (hcop) : 2 * (p1Region s0 u0 e h ell).card = ell * (e * h * ell + 1 - e - h)` + `example` anchors (ℓ = 1 ↦ XA.6; e = h = ℓ = 1 ↦ 0). moves_ref: "(IND) ind(S) = ½·ℓ·(ehℓ − e − h + 1)". deps: XA.6, XA.7a. MEDIUM.
**XA.8 t34Zero** — `theorem t34Zero (ν) (h34 : rowOf ν = .T3 ∨ rowOf ν = .T4) : ν.region.card = 0 ∧ ind2 ν = 0`. moves_ref: T3/T4 zero rulings; docstring carries finding-1 semantics ("0" = no positive per-side bound — NEVER "actual ind_r = 0"). deps: XA.1, XA.6. EASY.
**XA.9 ind2Region** — `theorem ind2Region (ν) (hc : ν.continuing) : ind2 ν = 2 * ν.region.card ∧ ((rowOf ν = .T1 ∨ rowOf ν = .T2) → 1 ≤ ind2 ν)`. moves_ref: the table's ind(S) column, EQUALITY (doubled per D2). deps: XA.3–XA.8. MEDIUM.

### Layer B — (CD), populations, degree charge (4 units, frozen at rev 2)

**XB.1 dCertZero** — `theorem dCertZero (H : XHistory n) : dCert ⟨false, false⟩ H = 0 ∧ ∀ st, dCert st H ≤ dTotal H`. moves_ref: "At today's discharge state … d_cert ≡ 0". deps: Defs. EASY.
**XB.2 dCertMono** — `theorem dCertMono (H) : dCert ⟨true, false⟩ H = countPop H .incT12 ∧ dCert ⟨true, true⟩ H = countPop H .incT12 + countPop H .recT1`. moves_ref: "given (ALIGN-inc): d_cert = #T1-increments + #T2; given both: also the T1 recenterings". deps: Defs. MEDIUM.
**XB.3 fourPop** — `theorem fourPop (H) : dTotal H = countPop H .incT12 + countPop H .recT1 + countPop H .t3 + countPop H .t4`. moves_ref: "{T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}" (coherence fields make it typecheck). deps: XA.1. MEDIUM.
**XB.4 t3Charge** — `theorem t3Charge (H) (W : HistWF n H) (hn : 1 ≤ n) : countPop H .t3 ≤ Nat.log 2 n`. moves_ref: "each T3 node multiplies the key degree by e ≥ 2, so #T3 per branch ≤ ⌊log₂ n⌋ (derived…)"; exponential step proved in-unit, only Πe ≤ n rides (`HistWF.degProd`, MovesSp-discharged). deps: XA.1. MEDIUM.

### Layer C — the X.1a chain and reduction (retyped over `XFamily`; displays unchanged)

**XC.1 x1aChain** — with `DescX (X : XFamily n) (p) (st) (d) : Set (MonicBox n p) := {f | ∃ H, (X.gmn p).inStratum f H ∧ d ≤ dCert st H}` (Defs):
```lean
theorem x1aChain (X : XFamily n) (st : AlignState) (AL : X1aAlignP n X st)
    (p : ℕ) [Fact p.Prime] :
    (∀ (f : MonicBox n p) H, (X.gmn p).inStratum f H → f ∈ DescX X p st (dCert st H)) ∧
    (∀ (f : MonicBox n p) d, f ∈ DescX X p st d → f ∉ discZero n p → 2 * d ≤ vdisc f)
```
moves_ref: "(X.1a) stratum(H) ⊆ Desc_{d_cert(H)} ⊆ { v_p(disc f) ≥ 2·d_cert(H) }"; first inclusion definitional, second via transport + (P2). deps: Defs. EASY-MEDIUM→MEDIUM band. hyp_fields: X1aAlignP (kernel), GMNIndex.p2 (published).
**XC.2 x1aTrivial** — the same two-inclusion statement at st = ⟨false, false⟩ WITHOUT the `AL` hypothesis. moves_ref: "at zero discharge d_cert ≡ 0 and (X.1a) is trivially true". deps: XB.1. EASY. hyp: none (the honest unconditional instance).
**XC.3 x1bReduction** —
```lean
theorem x1bReduction (X : XFamily n) (K : XConsts n)
    (AL : X1aAlignP n X ⟨true, false⟩) (WC : WeightChargeFullP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n)
    (hf : (X.gmn p).inStratum f H) (hd : f ∉ discZero n p) (W : HistWF n H) (hn : 1 ≤ n) :
    2 * dTotal H ≤ (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n
```
moves_ref: the two-step reduction display, cleared form (auditor-confirmed: "2I ≤ v, R ≤ sv, T3 ≤ ⌊log₂n⌋ give 2d_total ≤ (2s+1)v + 2⌊log₂n⌋"). deps: XB.2–4, XC.1. MEDIUM. hyp_fields: X1aAlignP(inc) ∧ WeightChargeFullP + HistWF.
**XC.4 x1bReductionT4** — same signature at st = ⟨true, true⟩ with `WeightChargeT4P`, conclusion `countPop H .t4 ≤ K.s * vdisc f ∧ 2 * dTotal H ≤ (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n`. moves_ref: X.3(a1)'s three bounds. deps: XB.2–4, XC.1. MEDIUM. hyp_fields: X1aAlignP(both) ∧ WeightChargeT4P + HistWF.

### Layer D — (τ-ns)-FREE, caps, (X2-HYP) (retyped over `XCtx`; displays unchanged)

**XD.1 nsFreeDec** — `instance (C : XCtx n p) (f) : DecidablePred (NsFreeB C (f := f))` + `theorem capTotal (C) (f) (b : C.Branch f) : (¬ C.capDetectable b → capHB C b = 0) ∧ (C.capDetectable b → capHB C b = C.detCap b)` + `theorem maxHNil : maxH ([] : XHistory n) = 0 ∧ sumH ([] : XHistory n) = 0`. moves_ref: DOMAIN CONVENTIONS (predicate exclusion; cap 0-convention; max h(∅) = 0). deps: Defs. EASY.
**XD.2 x2hypCount** — `theorem x2hypCount (H : XHistory n) (W : HistWF n H) : sumH H ≤ (dTotal H + 1) * maxH H` (unconditional; empty case both sides 0). moves_ref: "Σ_{r∈H} h_r ≤ (d_total(H) + 1)·max h(H); the d_total = 0 lone-terminal-read history is carried by the +1". deps: Defs. MEDIUM. hyp: HistWF.
**XD.3 x2hypDichotomy** — `theorem x2hypDichotomy (M : ℚ) (d m : ℕ) (h : M < (d + 1) * m) : M < ((d : ℚ) + 1)^2 ∨ M < (m : ℚ)^2`. moves_ref: the √ dichotomy, squared form. deps: none. EASY.
**XD.4 x2hypAssembled** — (X2-HYP), over the context:
```lean
theorem x2hypAssembled (X : XFamily n) (K : XConsts n)
    (AF : X2AffP n X K) (CP : X2CapP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f)
    (hb : FourthPieceB b) (N : ℕ) (hN : N < (X.ctx p).threshold b + capHB b) :
    (N : ℚ) - 1 - K.ccap < (K.c0 + K.ccap) * ((dTotal ((X.ctx p).hist b) : ℚ) + 1)^2 ∨
    (N : ℚ) - 1 - K.ccap < (K.c0 + K.ccap) * (maxH ((X.ctx p).hist b) : ℚ)^2
```
moves_ref: "(X2-HYP) … DERIVED given (X2-AFF) ∧ (X2-CAP) … both prices in the ONE currency Σ h_r, combined constant c₀⁺ := c₀ + c_cap". deps: XD.1–XD.3. MEDIUM. hyp_fields: X2AffP, X2CapP by name.

### Layer E — kernel-Prop units + the DERIVED envelopes (findings 6/7 repaired)

**XE.1a–h** — one unit per kernel Prop: **XE.1a** `X1aAlignP` · **XE.1b** `WeightChargeT4P` · **XE.1c** `WeightChargeFullP` · **XE.1d** `X2AffP` · **XE.1e** `X2CapP` · **XE.1f** `X2BridgeP` · **XE.1g** `X2TailsP` · **XE.1h** `X2ProgressP`. Each unit: the `def` elaborates against Defs; docstring = its display verbatim + owner/status line (a/b/c math-side OPEN; d/e/h owned by PROGRESS; f owned by PROGRESS; g [2b]-owed, discharged at [2b]'s acceptance). NON-VACUITY BY CONSTRUCTION (Ruling 1): each is a Prop about the shared `X : XFamily n` — it carries no data of its own to degenerate; the ONE inhabitation obligation (the real `XFamily` instance, owner MovesD/MovesT) is ledger-tracked. deps: Defs. EASY ×8. hyp: they ARE the hypotheses.

**XE.2 envelopeExp** — the note's exponential envelope [RESTATED POST-REFUTATION, §7 — the
rev-4 ∀N form was KERNEL-CERTIFIED FALSE; the adjudication: the NOTE's envelope is vacuous
at small N by design (the (N−1−c_cap) numerator; X.5(iii)'s "no teeth at census range"),
so the conclusion now binds ONLY where the note's arithmetic has content — ∃ N₀ before ∀ N,
with N₀, c3, c4 functions of (n, K) alone (bound BEFORE p, the D9 discipline)]:
```lean
theorem envelopeExp (n : ℕ) (hn : 2 ≤ n) (K : XConsts n) :
    ∃ N₀ : ℕ, ∃ c3 c4 : ℝ, 0 < c3 ∧ 0 < c4 ∧
      ∀ (X : XFamily n), X2ProgressP n X K → X2BridgeP n X → X2AffP n X K → X2CapP n X K →
        X1aAlignP n X ⟨true, false⟩ → WeightChargeFullP n X K →
        X2TailsP n X K → NsNullP n X → X3aRouteP n X K →
        ∀ (p : ℕ) [Fact p.Prime], ∀ N, N₀ ≤ N →
          ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3 * (p : ℝ) ^ (-(c4 * N))
```
TAG CHECK against the CONDITIONALITY SUMMARY (MOVES ~11449, "exponential GIVEN
(X.2)+X.1b+(ALIGN-inc)+(X2-TAILS)+(X2-BRIDGE)+(X2-CAP)"): PR=(X.2), WC=X.1b,
AL=(ALIGN-inc), TL, BR, CP — ALL present; the retained extras are themselves displayed
(AF from the envelope block's opening "Given (X2-BRIDGE) + (X2-CAP) + (X2-AFF)"; NS per
the (NS-c) display rule; R = X.3(a)'s tags for the bridge's first-three-pieces mass).
D9 REBIND (XE-audit adjudication: Codex findings 2/4 ACCEPTED — the constants were
bound after X, so nothing forced them (n,K)-only): N₀, c3, c4 now bind BEFORE ∀ X with
the tags as implications — quantified over exactly (n, K), no Defs change (XConsts was
already a separate structure; additive-only rule respected trivially). Findings 1/3/5
OVERRULED (ledger): the units encode the tags→envelope DERIVATION, and the kernel proved
the tags cannot yield the ∀N form — ∃N₀ is the derivation's only faithful rendering.
DISCLOSED: R is redundant given AL ∧ WC (route a2) — kept, matching the tag list; the
note's summary line under-lists the envelope-block tags (AF/NS) — a NOTE-SIDE
observation, recorded here only, no statement change.
INTENDED N₀ (sketch-level): the least N at which BOTH displayed exponents are positive —
N > 1 + c_cap (the (N−1−c_cap) numerator) AND d*(N) = cd·N − cd′ exceeds the ⌊log₂ n⌋
offset AND h*(N) ≥ 1 — an (n, K)-formula, p-free.
REFUTATION-ESCAPE WALK (the certified countermodel now SATISFIES the statement): the
countermodel (point mass at X² + X — unit discriminant at every p — with the root-only
tree, threshold 1, detCap 1) has Undec N = univ for N < 2 and ∅ for N ≥ 2; the refutation
lived at the FIXED N = 1, where frac = 1 for every p while all nine tags hold. Restated:
the prover picks N₀ ≥ 2 (this K has c_cap = 1, so the intended formula gives N₀ ≥ 3);
for every claimed N ≥ N₀, Undec N = ∅ and frac = 0 ≤ RHS; N ∈ {0, 1} are OUTSIDE the
claim — exactly the note's no-teeth regime. No p-uniform decay at fixed small N is
asserted anywhere anymore.
moves_ref: "Given (X2-BRIDGE) + (X2-CAP) + (X2-AFF) … Given (X.2) with linear d*, h* AND both legs …: env(N) ≤ c₃(n)·p^{−c₄(n)·N}, with c₃, c₄ traced to s(n), c₀, C_T, c_T, c_cap". deps: XC.3, XE.1*, XF.7, XG.2b–d (for the bridge's first-three-pieces mass, via X.3's tags). sketch: BR splits Undec(N) into the three null-tagged pieces (discZero via XF.7/vdisc_le_tail; ns via NS; InfTree via XG.2d ⊆ discZero) + the witness-branch piece. WITNESS FEED (rev 4, traced): BR's witness b carries `IsLeafB b ∧ NsFreeB b`, hence `FourthPieceB b` by the FIRST disjunct of FourthPieceB — exactly PR's (and XD.4's, in XE.3) hypothesis; PR on b gives deep-or-tall at d* = cd·N − cd', h* = ch·N − ch'; DEEP LEG: DeepEvent d* ⊆ {vdisc ≥ (2(d*−log)/(2s+1))} pointwise (XC.3 + gmnLink) → vdisc_le_tail + XF.7 give the (3b) bound with the note's displayed exponent; TALL LEG: TL. Constants assembled n-only (c₄ from cd, s, n − 1; the p^{n·v_p(n)/(n−1)} ≤ n^{n/(n−1)} absorption into c₃ — p-free). HARD. hyp_fields: the FULL tag set, verbatim the note's "CONSUMERS … inherit ALL tags above" line.
**XE.3 envelopeSqrt** — the √N fallback [RESTATED POST-REFUTATION, §7 — same adjudication;
the same countermodel refuted the ∀N form and escapes identically via N₀]: same signature
MINUS `PR` (X2ProgressP), conclusion `∃ N₀ : ℕ, ∃ c3' c4' : ℝ, 0 < c3' ∧ 0 < c4' ∧ ∀ (X : XFamily n), [the eight tags as implications] → ∀ (p : ℕ) [Fact p.Prime], ∀ N, N₀ ≤ N → ((X.ctx p).frac ((X.ctx p).Undec N) : ℝ) ≤ c3' * (p : ℝ) ^ (-(c4' * Real.sqrt N))` (D9 REBIND as in XE.2). TAG CHECK (summary's √N line "(X2-HYP)+(X2-AFF)+(X2-CAP)+X.1b+(ALIGN-inc)+(X2-TAILS)+(X2-BRIDGE)"): (X2-HYP) is XD.4's derived shape from AF ∧ CP; WC=X.1b, AL, TL, BR all present; NS/R as in XE.2.
moves_ref: "Given (X2-HYP) + (X2-AFF) + (X2-CAP) + (X2-BRIDGE) PLUS the same two leg tags …: env(N) ≤ c₃′(n)·p^{−c₄′(n)·√N} — subexponential, enough for X.3's qualitative form, NOT for SQUEEZE's constants". deps: XD.4 in place of PR; otherwise as XE.2. HARD. hyp_fields: (X2-HYP)'s inputs + both leg tags — the rev-4 leg-tag line reproduced.

### Layer F — the ELEMENTARY DISCRIMINANT TAIL, UNCONDITIONAL (Ruling 2; findings 8/9/13)

Display: `(3b) μ{v_p(disc f) ≥ D} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉} → 0; corollary
μ{disc f = 0} = 0`. `fTail`/`Event` now Defs (finding 13). XF.9 DELETED (Ruling 2).

**XF.1 discCylinder** — `theorem discCylinder (p n D : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (f : Polynomial ℤ_[p]) (hm : f.Monic) (hd : f.natDegree = n) : ((p : ℤ_[p]) ^ D ∣ f.discr ↔ (polyOfCoeffs (ZMod (p ^ D)) n (fun i => PadicInt.toZModPow D (f.coeff i))).discr = 0)`.
moves_ref: the (3b) event is level-D cylinder data. deps: Defs. sketch: `polyOfCoeffs … = f.map (toZModPow D)` for monic deg-n; monic-case `discr_map` helper (Mathlib gap flagged); `PadicInt.ker_toZModPow`. MEDIUM.
**XF.2 discResBridge** — `theorem discResBridge (p) [Fact p.Prime] (f : Polynomial ℤ_[p]) (hm : f.Monic) (h1 : 0 < f.natDegree) : ‖f.discr‖ = ‖f.resultant f.derivative‖`.
moves_ref: "Res(f, f′)" ↔ disc for monic f. deps: Defs. sketch: Mathlib `resultant_deriv`, lc = 1, ‖±x‖. MEDIUM band.
**XF.3 valExtOf** — `noncomputable def valExtOf (p : ℕ) [Fact p.Prime] (g : Polynomial ℚ_[p]) (hg : g ≠ 0) : ValExt p g`.
moves_ref: none (proof apparatus; §4 flag: never strengthens (3b) — and per Ruling 2 it appears in NO public statement). deps: Defs. sketch: `g.SplittingField` finite over complete ℚ_[p]; `spectralNorm` multiplicative there (Mathlib `SpectralNorm.lean` + Krasner layer); package as `AbsoluteValue`. HARD; STUCK ⟹ report (Ruling 2), no rider.
**XF.4 resRootSum** — `theorem resRootSum (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (f : Polynomial ℤ_[p]) (hm : f.Monic) (hd : f.natDegree = n) (V : ValExt p ((f.map PadicInt.Coe.ringHom).derivative)) : ‖f.resultant f.derivative‖ = ‖(n : ℚ_[p])‖ ^ n * ((((f.map PadicInt.Coe.ringHom).derivative.map (algebraMap ℚ_[p] V.L)).roots).map (fun θ => V.w (Polynomial.aeval θ (f.map PadicInt.Coe.ringHom)))).prod`.
moves_ref: "Res(f, f′) over the n−1 roots of f′" + the n·v_p(n) offset. deps: XF.3-independent (V explicit — INTERNAL unit). sketch: resultant map-commutation helper; root-product over V.L (`resultant_eq_prod_roots_sub` + eval-product lemmas); lc(f′) = n. HARD.
**XF.5 pigeonMax** — `theorem pigeonMax (m : Multiset ℚ) (hm : m ≠ 0) (K : ℚ) (h : K ≤ m.sum) : ∃ v ∈ m, K ≤ (m.card : ℚ) * v`.
moves_ref: "some θᵢ has v_p(f(θᵢ)) ≥ (D − n·v_p(n))/(n−1)". deps: none. EASY. FLAG: no sign hypothesis (terms may be negative).
**XF.6 ballCover** — `theorem ballCover (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (aTail : Fin (n - 1) → ℤ_[p]) (V : ValExt p (fTail n p (by omega) aTail)) : ∃ idx : ℤ_[p] → Fin (n - 1), ∀ a0 b0, Event p n D (by omega) aTail a0 → Event p n D (by omega) aTail b0 → idx a0 = idx b0 → (p : ℤ_[p]) ^ (tailExp p n D).toNat ∣ (a0 - b0)` (pairwise-congruence form; `Event`/`fTail` = Defs).
moves_ref: "the a₀-translation, union bound + Fubini". deps: XF.2, XF.4, XF.5 (INTERNAL unit, V explicit). sketch: f′ a₀-free; event point → root θᵢ with V.w(a₀ + c(θᵢ)) ≤ p^{−tailExp}; same-index points ultrametrically congruent; `.toNat` trivializes tailExp ≤ 0. MEDIUM-HARD.
**XF.7 tailCountBound** — (3b-LEAN), UNCONDITIONAL (Ruling 2 — no V argument):
```lean
theorem tailCountBound (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) :
    (tailCount p n D : ℚ) * (p : ℚ) ^ (tailExp p n D) ≤ (n - 1 : ℚ) * (p : ℚ) ^ ((n * D : ℕ) : ℤ)
```
moves_ref: "(3b) μ{f monic deg n : v_p(disc f) ≥ D} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉}" (auditor-confirmed arithmetic: 4 and 1/4 at (2,2,0)/(2,2,4); 2/3, 2/9, 2/27 at (3,3,5/7/9)). deps: XF.1, XF.6, XF.3. sketch: fiber over aTail ∈ (ZMod p^D)^{n−1} (XF.1); INSIDE the proof, `valExtOf (fTail n p (by omega) aTail) (fTail ≠ 0: lead coeff n ≠ 0 in char 0)` discharges XF.6's V; ≤ (n−1)·p^{D−tailExp.toNat} residues per fiber; trivial-face check at tailExp ≤ 0. MEDIUM-HARD (carries XF.3's stuck-risk — by ruling, a STUCK report, not a rider).
**XF.8 tailZero** — UNCONDITIONAL: `theorem tailZero (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) : Filter.Tendsto (fun D => (tailCount p n D : ℚ) / (p : ℚ) ^ (n * D)) Filter.atTop (nhds 0)`.
moves_ref: "→ 0 as D → ∞". deps: XF.7. sketch: tailExp → ∞ linearly; geometric squeeze. MEDIUM.
**XF.10 discZeroNull** — UNCONDITIONAL over the context (Ruling 2):
```lean
theorem discZeroNull (n p : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (C : XCtx n p) :
    C.frac (discZero n p) = 0
```
moves_ref: "corollary μ{disc f = 0} = 0". deps: XF.8. sketch: discZero ⊆ {D ≤ vdisc ∨ discZero} for every D, so `C.vdisc_le_tail` + XF.8 + `frac_nonneg` squeeze. EASY-MEDIUM→MEDIUM band. hyp_fields: XCtx's `vdisc_le_tail` (definitional cylinder fact, §4).

### Layer G — X.3 DERIVED end-to-end (findings 10/11/12 repaired; 7 units)

**XG.1 branchLenBound** — cleared display over the family:
```lean
theorem branchLenBound (X : XFamily n) (K : XConsts n) (R : X3aRouteP n X K)
    (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n)
    (hf : (X.gmn p).inStratum f H) (hd : f ∉ discZero n p) (W : HistWF n H) (hn : 1 ≤ n) :
    2 * dTotal H ≤ (2 * K.s + 1) * vdisc f + 2 * Nat.log 2 n
```
moves_ref: X.3(a)'s four-population bound, both routes (auditor-confirmed arithmetic). deps: XC.3, XC.4. EASY (glue). hyp_fields: X3aRouteP + HistWF.

**XG.2 koenigFinite** — the note's König, VERBATIM premise (finding 10 — no uniform depth bound):
```lean
theorem koenigFinite (C : XCtx n p) (f : MonicBox n p)
    (hbranch : ¬ ∃ g : ℕ → C.Branch f, g 0 = C.root f ∧ ∀ k, C.parent (g (k + 1)) = some (g k)) :
    Finite (C.Branch f)
```
moves_ref: "T_can(f) is FINITELY BRANCHING — each node's child menu is finite … — so König's lemma upgrades 'every branch finite' to 'T_can(f) finite'" (finite branching is `children : Finset` in the interface; "every branch finite" = no infinite root-descending path). deps: Defs. sketch: contrapositive is König: if Branch f infinite, the finitely-branching rooted forest (children_iff, reach) has a node at every level with infinitely many descendants; choose successively (Mathlib route: `nonempty_sections_of_finite_inverse_system` on the level-k sets of infinite-descendant nodes, or a direct classical induction). HARD. hyp: none beyond the context.

**XG.2b detectJoin** — X.3(b), the finite-level detection, DERIVED (finding 11):
```lean
theorem detectJoin (C : XCtx n p) (f : MonicBox n p) (hfin : Finite (C.Branch f))
    (hleaves : ∀ b : C.Branch f, IsLeafB b → ∀ ν ∈ C.hist b, ¬ C.nsTrack ν) :
    ∃ N, f ∉ C.Undec N
```
moves_ref: "(b) DETECTION AT A FINITE LEVEL [derived from accepted sources]. Every f whose tree is complete with all leaves (τ-irr)/(τ-hen) … exits Undec(N) at its finite threshold thr(T): Thm 2.1 … joined over the tree's finitely many branches with TB-CAP's per-clause caps". deps: Defs. sketch: N := max over the finitely many leaf branches of (threshold b + capHB b) (Finite ⟹ the max exists); `C.detectBranch` detects each ns-free leaf at N; `C.undec_spec` (the Undec DEFINITION) closes. MEDIUM. hyp_fields: XCtx's detectBranch + undec_spec (accepted LOCAL inputs, §4).

**XG.2c interTrichotomy** — X.3(d)'s first half, DERIVED (finding 11):
```lean
theorem interTrichotomy (C : XCtx n p) :
    (⋂ N, C.Undec N) ⊆ InfTree C ∪ (⋃ i, C.nsFiber i)
```
moves_ref: "(d) … an f whose complete tree is undetected at EVERY level has an ns leaf (TB-CAP's clause trichotomy — detection fails at all N only on the (τ-ns) class)". deps: XG.2b. sketch: f ∉ InfTree ⟹ Finite (Branch f); if every leaf ns-free, XG.2b exits f from some Undec N — contradiction; so some leaf carries an ns node; `C.nsCover` places f in a fiber. MEDIUM. hyp_fields: nsCover ((NS-c) input).

**XG.2d treeFinite** — X.3(a) pointwise, DERIVED (replaces the deleted `stratumLink`/`infBranch` fields):
```lean
theorem treeFinite (X : XFamily n) (K : XConsts n) (R : X3aRouteP n X K)
    (p : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (f : MonicBox n p) (hd : f ∉ discZero n p) :
    Finite ((X.ctx p).Branch f)
```
moves_ref: "Off {disc f = 0} …, EITHER route gives every branch finite pointwise, by the four-population decomposition … Hence a.e. f has a FINITE tree". deps: XG.1, XG.2. sketch: an infinite path g (¬Finite via XG.2's contrapositive) gives hist (g k) of length k (parent_hist induction), each a stratum of f (`X.gmnLink`) with HistWF (`wf`); dTotal ≥ k − 1 (termLast) contradicts XG.1's bound at large k. MEDIUM-HARD→HARD band. hyp_fields: X3aRouteP; gmnLink/wf (context inputs).

**XG.3 x3Density** — the density limit, DERIVED (finding 11: no detectInter, no MassLink):
```lean
theorem x3Density (X : XFamily n) (K : XConsts n) (hn : 2 ≤ n)
    (R : X3aRouteP n X K) (NS : NsNullP n X) (p : ℕ) [Fact p.Prime] :
    Filter.Tendsto (fun N => (X.ctx p).frac ((X.ctx p).Undec N)) Filter.atTop (nhds 0)
```
moves_ref: "(X.3) … μ(Undec(N)) → 0 (N → ∞)" + CONDITIONALITY SUMMARY "X.3 = [routes] + (ns-null, closed, tag displayed) + accepted perimeter". deps: XG.2c, XG.2d, XF.10, XD.1. sketch: ⋂Undec ⊆ InfTree ∪ ⋃ns (XG.2c); InfTree ⊆ discZero (XG.2d contrapositive); frac(discZero) = 0 (XF.10); frac(⋃ns) = 0 (NS + nsCountable + frac_iUnion_null); frac_mono/union_le ⟹ frac(⋂) = 0; frac_inter_tendsto + undec_antitone close the limit. MEDIUM-HARD→HARD band. hyp_fields: X3aRouteP, NsNullP (tag) — NOTHING else beyond XCtx's audited inputs.

**XG.4 x3Series** — the per-σ series identity, DERIVED (finding 12: `hσ` deleted; `densityOf` DEFINED):
```lean
theorem x3Series (X : XFamily n) (K : XConsts n) (hn : 2 ≤ n)
    (R : X3aRouteP n X K) (NS : NsNullP n X)
    (p : ℕ) [Fact p.Prime] (S : SeriesData n p (X.ctx p))
    (VP : VPSoundP S) (ADD : CountableFiberAdditive S) (σ : SplitType n) :
    HasSum (fun T : { T // S.typemult T = σ } => (X.ctx p).frac (S.fiber T)) (densityOf S σ)
```
moves_ref: "for each type σ the tree-fiber series sums the full density … [(ns-null) tag displayed]" + "(3e)-style regrouping (Tonelli, positive terms) yields the per-σ series identity"; VP-SOUND consumed exactly at the typemult identification (note finding 13). deps: XG.3, XF.10. sketch: E_σ := {f | S.splitType f = σ} ∖ (⋂Undec ∪ discZero); `decided_covered` + `fiber_disjoint` + VP.typeFaithful show E_σ is exactly the union of the σ-typemult fibers minus null sets; ADD gives HasSum to frac E_σ; frac(⋂Undec) = 0 (XG.3's chain) and frac(discZero) = 0 (XF.10) + union_le/mono give frac E_σ = densityOf S σ. HARD. hyp_fields: VPSoundP, CountableFiberAdditive (Tonelli, owed), SeriesData's three coverage fields (§4) + the XG.3 riders.

---

## 4. Audit table (trust surface; each interface field = ONE note-cited LOCAL input)

| object | note display it must match | class |
|---|---|---|
| `p1Region`'s `≤` | (P1)/Remark 4.14 on-or-below pin | DEF — sharpest trap |
| `rowOf` + `XNode` coherence | table rows; T2/T3 increments, T4 recenterings | DEF (MovesSp-discharged) |
| `ind2` + XA.9 equality | (IND) doubled; finding-1 semantics in docstrings | DEF+THM |
| `certified`/`dCert`/`DescX` | (CD); Desc_d keyed by d_cert | DEF |
| `HistWF` | §D4-R terminal-last; §B2-DEF "Π e_i ≤ n along a branch" | IF accepted (MovesSp sync) |
| `MonicBox`/`discZero`/`vdisc` | the monic box; v_p(disc f) — now CONCRETE (D5) | DEF (Mathlib) |
| `GMNIndex` (ind, inStratum, p2) | (P2) + Thm 4.18(1), D.12 dictionary | IF published (MovesD/HC-2) |
| `XFamily.gmnLink` | §D4-R: f lies in the stratum of each of its own histories | IF definitional (sync) |
| `XCtx` tree fields (root/parent/children/reach) | §D4-R T_can rooted presentation; §M-SPECIES finite menus | IF (MovesD; PrefFamily precedent) |
| `XCtx.detectBranch` | X.3(b)'s INPUTS: "Thm 2.1 (each stratum a finite union of level-N₀ cylinders)" + "TB-CAP's per-clause caps ((τ-hen) N_V = 1 PROVED; (τ-irr) per-realized-cell cap PROVED)" — per ONE leaf branch | IF accepted (MovesT sync) |
| `XCtx.undec_spec` | X.0's DEFINITION of Undec(N) verbatim ("does not certify a complete τ-halted tree with every leaf cap-detected") | IF definitional (sync) |
| `XCtx.undec_antitone`, `frac_inter_tendsto` | Thm 2.1 N-stability; monotone convergence of the box content | IF accepted/owed |
| `XCtx.nsIdx/nsCountable/nsFiber/nsCover` | "(NS-c)'s symbolic indexing"; ns-leaf f's covered | IF (owed, [3t]) |
| `XCtx.frac_*` laws + `frac_univ = 1` | the box probability content (finding 5 repaired) | IF (MovesD/T) |
| `XCtx.vdisc_le_tail` | the level-D cylinder fact ({v_p ≥ D} is level-D data) — definitional | IF definitional (sync) |
| kernel Props `*P` over `XFamily` | their displays verbatim; Ruling-1 non-vacuity; D9 p-freeness by binder order; NONNEG normalizations on c0/ccap WLOG-safe (flagged); rev 4: X2BridgeP's witness leaf-qualified (IsLeafB) in both clauses | HYP (open kernels) |
| `TallEvent`/`DeepEvent`/`InfTree`/`FourthPieceB` | the displayed events/sets (finding 4/1 repaired: defined, 'finite branch' disjunct restored) | DEF |
| `tailCount`/`tailExp`/`fTail`/`Event` | (3b) finite-level, INTEGER exponent (auditor-confirmed); rev 4: `Coe.ringHom` + outer `Fin.cast` from `hn : 1 ≤ n` | DEF |
| `ValExt`/`valExtOf` | proof apparatus only — appears in NO public statement (Ruling 2) | DEF+construction |
| `SeriesData` fields | (NS-a) 𝒯^fin quantification; canonical-tree fiber partition; decided coverage | IF (MovesD/T sync) |
| `VPSoundP` | VP-SOUND = (HEN-LIFT)/(OM-SAT) at the typemult identification (note finding 13) | HYP tag |
| `CountableFiberAdditive` | "(3e)-style regrouping (Tonelli, positive terms)" | IF owed (MovesD/T) |

INHABITATION: ONE obligation — the real `XFamily n` instance (+ per-p `SeriesData`),
owner MovesD/MovesT at wave-4 sync (HC-2 for `GMNIndex`); ledger-tracked. Kernels are
Props about it (Ruling 1), so no kernel has independent degenerate models.

## 5. Census and counts

**48 units.** EASY 19 (XA.1–4, XA.8; XB.1; XC.2; XD.1, XD.3; XE.1a–h; XF.5; XG.1) ·
MEDIUM 17 (XA.5, XA.7b, XA.9; XB.2–4; XC.1, XC.3, XC.4; XD.2, XD.4; XF.1, XF.2, XF.8,
XF.10; XG.2b, XG.2c) · HARD 12 (XA.6, XA.7a — lattice; XE.2, XE.3 — envelope assembly;
XF.3, XF.4, XF.6, XF.7 — tail analytics; XG.2, XG.2d, XG.3, XG.4 — X.3 chain).
Escalation-risk set = the 12 HARD ids; XF.3-class failures are STUCK reports (Ruling 2),
never hypothesis riders. X.5 gate layers = runtime, out of corpus. NOT formalized (OPEN
upstream): the X.1b/X.2 kernel derivations, STALL-probe, (X2-TAILS)'s derivation —
matching X.4's perimeter; the envelopes (exponential + √N) are now IN-corpus theorems
XE.2/XE.3 given the tag set (finding 7).

## 6. Findings→repairs (cumulative)

REV-2 round (25 findings of MOVESX_AUDIT_CODEX_2026-07-28.md): all repaired at rev 2 —
1 iffs · 2 split XA.7a/b · 3 equality · 4 coherence fields · 5 degree charge derived ·
6/7 two-inclusion chain · 8 unconditional count · 9 termLast · 10 prefix clause ·
11 FourthPiece domain · 12 ℝ constants · 13 ℚ slopes · 14 bridge fields · 15/16 kernel
units split · 17 c4pos · 18 toZModPow · 19 D8 route · 20 integer exponent · 21 split
XF.8/XF.10 · 22 cleared display · 23 rooted forest · 24 MassLink deleted · 25 series
theorem. (Rev-3 findings below supersede where they touch the same objects.)

REV-3 round (13 findings of MOVESX_AUDIT_CODEX_REV2_2026-07-28.md):

| # | class | object | repair (rev 3) |
|---|---|---|---|
| 1 | CRIT | FourthPiece | FIXED: `IsLeafB b ∨ ∃ b', complete b' ∧ isPrefixB b b'` — the 'finite branch' disjunct restored verbatim |
| 2 | CRIT | X2Cap | FIXED: `X2CapP` quantifies `FourthPieceB b → capDetectable b → …` — inside the ns-free family |
| 3 | CRIT | p-free constants | REDESIGNED (D9): all constants in `XConsts n`, bound before p; kernels `∀ p` INSIDE — p-freeness by binder order |
| 4 | CRIT | X2Tails event | REDESIGNED (Ruling 1): `TallEvent` a DEFINED set over the concrete tree context; `tallFrac` field deleted |
| 5 | CRIT | zero content | FIXED: `frac_univ : frac Set.univ = 1` field added |
| 6 | CRIT | kernel vacuity | REDESIGNED (Ruling 1): kernels are Props over the ONE shared `XFamily n`; no kernel carries its own data; single ledger-tracked inhabitation obligation |
| 7 | CRIT | XE.2 | FIXED: `envelopeExp` = ∃-theorem deriving the exponential envelope from the full tag set; NEW `XE.3 envelopeSqrt` = the p^{−c√N} fallback display |
| 8 | GAP | XF.9 | CLOSED BY DELETION (Ruling 2): XF.7/XF.8 are unconditional; no 'same as' statement remains |
| 9 | CRIT | ValExt riders | FIXED (Ruling 2): XF.7, XF.8, XF.10, XG.3 carry NO ValExt; discharge inside XF.7's proof via valExtOf; stuck ⟹ report |
| 10 | CRIT | König | FIXED: `koenigFinite` premise = no infinite root-descending path (+ finite menus in the interface) — the note's form, no uniform depth bound |
| 11 | CRIT | detectInter | REDESIGNED: field deleted; X.3(b)/(d) DERIVED by units XG.2b (detection join), XG.2c (trichotomy), XG.2d (pointwise tree-finiteness) from the LOCAL inputs detectBranch/undec_spec/nsCover |
| 12 | CRIT | hσ | REDESIGNED: deleted; `densityOf` DEFINED as frac of the true-type event; XG.4 derives the identity from decided coverage + fiber partition + VPSoundP + Tonelli |
| 13 | GAP | Defs deps | FIXED: `fTail`, `Event`, `CountableFiberAdditive` fully specified in the Defs skeleton |

REV-4 round (4 findings of MOVESX_AUDIT_FABLE_2026-07-28.md; all 13 rev-3 repairs
verified genuine there):

| # | class | object | repair (rev 4) |
|---|---|---|---|
| F1 | CRIT | X2BridgeP | FIXED: `IsLeafB b ∧ NsFreeB b` witness in BOTH clauses (the note's "(τ-ns)-FREE finite branch"); witness feed traced in XE.2's sketch — IsLeafB ∧ NsFreeB ⟹ FourthPieceB (first disjunct) ⟹ X2ProgressP/XD.4 apply |
| F2 | CRIT | vdisc | FIXED: `.toNat` dropped — pinned `PadicInt.valuation : ℤ_[p] → ℕ` (PadicIntegers.lean:321); junk-0 convention preserved via `valuation_zero` |
| F3 | GAP | PadicInt.coe | FIXED: renamed to pinned `PadicInt.Coe.ringHom` (PadicIntegers.lean:130) at fTail + XF.4 (grep-verified) |
| F4 | GAP | fTail/Event arity | FIXED: explicit OUTER `Fin.cast (by omega : n = n − 1 + 1)` on the index, from a new `hn : 1 ≤ n` argument threaded from every consumer's `h2 : 2 ≤ n` (option chosen and noted; no Fin (n−1+1) restatement ripple) |

---

## 7. DEVIATIONS (E-phase elaboration record, 2026-07-27)

E-phase built `lean/LeanUrat/MovesX/` (Defs + 48 unit files + MANIFEST.json); every
proof body `sorry`. All deviations below are ELABORATION-LEVEL (identifier/spelling/
marker changes forced by Lean 4 / pinned mathlib v4.31.0); none changes what any
statement says. Anything semantic the blueprint left open is resolved by the most
conservative reading, flagged here for the Defs-sync round.

- **D-1 (identifier).** `AlignState`'s second field `rec` is a reserved name in Lean 4
  (clashes with the auto-generated recursor `AlignState.rec`); renamed to `recn`. No
  unit statement mentions the field name (all uses are anonymous constructors
  `⟨true, true⟩` etc. and `st.inc`/`st.recn` inside Defs' `certified` only).
- **D-2 (spelling).** Inside `structure XCtx`, the fields `detectBranch`, `undec_spec`,
  `nsCover` spell the comment-block abbreviations inline — `IsLeafB b` as
  `children b = ∅`, `capHB b` as `@ite ℕ (capDetectable b) (capDec f b) (detCap b) 0` —
  because the literal `def`s take `(C : XCtx n p)` and can only be declared AFTER the
  structure. The E-gate `def`s `IsLeafB`/`capHB`/`NsFreeB`/`isPrefixB`/`FourthPieceB`/
  `InfTree`/`TallEvent`/`DeepEvent` are declared immediately below `XCtx` and unfold
  DEFINITIONALLY to exactly these inline spellings.
- **D-3 (left-open semantic choice, conservative).** `SplitType n` exists nowhere in
  the codebase yet ("bound to the campaign's target type at the Defs sync" — E-gate
  note). Declared `opaque SplitType : ℕ → Type`: commits to NO structure, admits no
  degenerate models, nothing about it is provable until the sync round replaces the
  `opaque` with the campaign binding (candidate: `LeanUrat.FactorizationType` filtered
  by degree n, `LeanUrat/Interface.lean:152`). Statement forms are byte-stable under
  that replacement (they consume `SplitType n` by name).
- **D-4 (pinned-mathlib API).** `ValExt.splits`: mathlib v4.31.0 carries the REFACTORED
  absolute `Polynomial.Splits (f : R[X]) : Prop` (Algebra/Polynomial/Splits.lean:36),
  not the old relative `Splits (i : K →+* L) f`. The blueprint's
  `(g.map (algebraMap ℚ_[p] L)).Splits (RingHom.id L)` is the pre-refactor spelling;
  the field is `(g.map (algebraMap ℚ_[p] L)).Splits` — the identical condition
  (old `Splits (RingHom.id L) q ↔ new q.Splits`).
- **D-5 (elliptical binders).** XA.6/XA.7a/XA.7b's unannotated `(he) (hh) (hl)` are
  resolved to `1 ≤ e`, `1 ≤ h`, `1 ≤ ell`, matching XA.4's explicit spelling (the only
  annotated occurrence) and the ℓ ≥ 1 anchor set.
- **D-6 (markers only).** `noncomputable` added where mathlib forces it
  (`polyOfCoeffs`, `tailCount`, `fTail` — Polynomial arithmetic and `Nat.card` are
  noncomputable; `vdisc` was already marked in the skeleton). Two external instance
  accessors `Field V.L`/`Algebra ℚ_[p] V.L` for `ValExt` (structure instance-fields are
  not auto-instances outside the structure; needed to ELABORATE XF.4/XF.6's statements,
  zero content).
- **Census note (blueprint-specified multi-decl units).** 44 `sorry` declarations for
  48 stated units: XE.1a–h are def-witness units (their kernels are Defs §D `def`s per
  the skeleton; each file = display docstring + an `example` forcing elaboration — no
  proof obligation, 0 sorries); XA.7b carries its 2 specified example anchors (3
  sorries); XD.1 is the specified 3-declaration unit (3 sorries). `Defs.lean` has 0.
  No `native_decide`/`decide` anywhere; the only in-statement tactics are the
  blueprint's own `(by omega)` coherence casts (fTail/Event/XF.6).

---

## 7. REFUTATION RECORD (stuck-rule outcome, 2026-07-27 — XE.2/XE.3 as E-phase-stated)

**Event.** The prover fleet KERNEL-CERTIFIED the E-phase statements of XE.2
(`envelopeExp`) and XE.3 (`envelopeSqrt`) FALSE — sorry-free refutations with
statement-match certificates:
- `lean/notes/XE2_refutation_witness.lean` — the countermodel + `envelopeExp_statement_false`
  (axiom-clean; `#print axioms` in-file);
- `lean/notes/XE2_refutation_transcription_check.lean` — the type-agreement certificate
  (the refuted ∀-closure accepts `envelopeExp` itself as an inhabitant);
- `lean/notes/XE3_REFUTATION_2026-07-27.lean` — the XE.3 certificate (verbatim Pi-type
  `abbrev` + `example : XE3Statement := envelopeSqrt` match) whose one countermodel also
  satisfies `X2ProgressP`, re-refuting XE.2.

**The countermodel.** n = 2; every f gets the root-only tree (Branch = Unit, hist = [],
children = ∅); threshold = 1, capDetectable with detCap = 1, DetectedAt _ N := 2 ≤ N, so
Undec N = univ for N < 2 and ∅ for N ≥ 2; content = the point mass at f₀ = X² + X, whose
discriminant is 1 — a UNIT at every prime (vdisc f₀ = 0, f₀ ∉ discZero, `vdisc_le_tail`
slack). All nine/eight tags hold verbatim, yet frac (Undec 1) = 1 for EVERY p, killing
`∃ c3 c4, … ∀ p N` at N = 1 as p → ∞.

**Adjudication (orchestrator, against the note's own display).** The NOTE is intact: its
(N−1−c_cap) numerator makes the envelope vacuous at small N by design (X.5(iii) records
env*(N) > 1 at every N ≤ 8 — "no teeth at census range, displayed for shape only"). The
blueprint's `∃ c ∀ p N` rendering was unfaithfully STRONG — a transcription defect of
rev 3/4, not a math error. Repair: the §3 XE.2/XE.3 statements now bind `∃ N₀` (an
(n, K)-function, bound before p per D9) with the claim quantified over N ≥ N₀ only; the
countermodel's escape is walked in the XE.2 spec (N₀ ≥ 2 empties every claimed Undec N).

**Process notes.** E-phase files `XE2.lean`/`XE3.lean` restated to the §3 forms (bodies
`sorry` again; fleet re-proves); MANIFEST entries re-hashed with status
`restated-post-refutation`; both compile green (lake build, 2026-07-27, sorry warnings
only). SIDE EVENT during the recompile: XF.6's fleet proof ("proved pending
re-verification") FAILED independent re-verification — (kernel) deterministic timeout at
`ballCover`, reproduced in two clean builds and solo (>590s wall); XF6.lean restored to
its E-phase sorry with the statement verbatim, the proof text preserved at
`lean/notes/XF6_pending_reverify_2026-07-27.lean.txt`, MANIFEST noted — an
escalation-prover item, exactly what the V-gate exists to catch. The restated units get a mini dual audit (Codex + fresh
Fable) before re-proving. The three refutation artifacts are NOTES-side (outside the
lake build graph) and are retained as permanent negative controls: any future draft of
XE.2/XE.3 whose statement the transcription-check `example` still accepts is refuted
before proving starts.
