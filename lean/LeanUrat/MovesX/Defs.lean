/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Moves.Defs

/-!
# MovesX/Defs — shared vocabulary for §X-EXHAUST (MovesX corpus)  [E-PHASE]

E-phase skeleton per `lean/notes/MOVESX_LEAN_BLUEPRINT_2026-07-28.md` (rev 4,
dual-accepted at 0/0). Ground truth: MOVES §X-EXHAUST rev 8 (`MOVES_2026-07-24.md`).

Layers:
* §A nodes, rows, region, doubled index (D1–D4);
* §B the CONCRETE monic carrier over `ℤ_[p]` with `vdisc` via `Polynomial.discr` (D5),
  the (3b) tail objects `tailCount`/`tailExp`/`fTail`/`Event`, and `ValExt` (D8);
* §C the GMN interface (D6), THE concrete per-prime context `XCtx` (D7, Ruling 1),
  its literal abbreviation `def`s (`IsLeafB` … `DeepEvent`), `XFamily`, `XConsts` (D9),
  and `DescX`;
* §D the kernel Props over the shared context (Ruling 1; `∀ p` INSIDE, D9);
* §E series objects (`SplitType`, `SeriesData`, `densityOf`, `VPSoundP`,
  `CountableFiberAdditive`).

Statement-fence: every definition is the blueprint §2 skeleton verbatim; only
elaboration-level adjustments were made, each recorded in the blueprint's DEVIATIONS
section. NO axioms, NO `sorry` in this file.
-/

namespace LeanUrat.MovesX

set_option linter.style.longLine false

/-! ## §A Nodes, rows, region, doubled index (UNCHANGED from rev 2) -/

/-- A node of the §X-EXHAUST tower: letter fields `(e, ℓ, h, s₀, u₀)`, the selection
`sel = some (g, μ)` for continuing nodes, and the increment/recentering flag, with the
positivity/coprimality/selection-bound and T2/T3/T4 coherence laws. -/
structure XNode (n : ℕ) where
  e : ℕ
  ell : ℕ
  h : ℕ
  s0 : ℕ
  u0 : ℕ
  sel : Option (ℕ × ℕ)
  isIncrement : Bool
  epos : 1 ≤ e
  hpos : 1 ≤ h
  ellpos : 1 ≤ ell
  hcop : Nat.Coprime e h
  selBound : ∀ g μ, sel = some (g, μ) → 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ ell
  t2inc : ell = 1 → 2 ≤ e → 2 ≤ h → sel.isSome → isIncrement = true
  t3inc : ell = 1 → 2 ≤ e → h = 1 → sel.isSome → isIncrement = true
  t4rec : ell = 1 → e = 1 → sel.isSome → isIncrement = false

abbrev XHistory (n : ℕ) := List (XNode n)

variable {n : ℕ}

def XNode.continuing (ν : XNode n) : Bool := ν.sel.isSome

/-- The index-table rows T0–T5 (T0 folded into T5: terminal read). -/
inductive Row
  | T1 | T2 | T3 | T4 | T5
  deriving DecidableEq, Repr

/-- Row classification: terminal (T5) vs `ℓ ≥ 2` (T1) vs `ℓ = 1` split by `(e, h)`. -/
def rowOf (ν : XNode n) : Row :=
  if ν.sel = none then .T5
  else if 2 ≤ ν.ell then .T1
  else if 2 ≤ ν.e then (if 2 ≤ ν.h then .T2 else .T3) else .T4

/-- The (P1) region: lattice points strictly right/above `(s₀, u₀)`, ON OR BELOW the
segment — the `≤` is the Remark 4.14 on-or-below pin (§4 audit trap). -/
def p1Region (s0 u0 e h ell : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc s0 (s0 + e * ell) ×ˢ Finset.Ioc u0 (u0 + h * ell)).filter
    (fun q => h * (q.1 - s0) + e * (q.2 - u0) ≤ e * h * ell)

def XNode.region (ν : XNode n) : Finset (ℕ × ℕ) := p1Region ν.s0 ν.u0 ν.e ν.h ν.ell

/-- The DOUBLED index (D2): `2·ind(S)` per row of the table. "0" at T3/T4 records
NO POSITIVE PER-SIDE BOUND from the table — never "actual ind_r = 0" (finding-1
semantics; see XA.8's docstring). -/
def ind2 (ν : XNode n) : ℕ :=
  match rowOf ν with
  | .T1 => ν.ell * (ν.e * ν.h * ν.ell + 1 - ν.e - ν.h)
  | .T2 => (ν.e - 1) * (ν.h - 1)
  | _   => 0

/-- Discharge state for (X1a-ALIGN): are T1/T2-increments (`inc`) resp. T1-recenterings
(`recn`) certified? (Blueprint field name `rec`; renamed — `rec` is reserved in Lean 4.
DEVIATION D-1; no unit statement mentions the field name.) -/
structure AlignState where
  inc : Bool
  recn : Bool

def certified (st : AlignState) (ν : XNode n) : Bool :=
  ν.continuing && match rowOf ν with
    | .T1 => (ν.isIncrement && st.inc) || (!ν.isIncrement && st.recn)
    | .T2 => st.inc
    | _   => false

def dTotal (H : XHistory n) : ℕ := (H.filter (·.continuing)).length
def dCert (st : AlignState) (H : XHistory n) : ℕ := (H.filter (certified st)).length
def dUnc (st : AlignState) (H : XHistory n) : ℕ := dTotal H - dCert st H

/-- The four populations of continuing nodes: T1/T2 increments, T1 recenterings, T3, T4. -/
inductive Pop
  | incT12 | recT1 | t3 | t4
  deriving DecidableEq

def popOf? (ν : XNode n) : Option Pop :=
  if ¬ ν.continuing then none else some (match rowOf ν, ν.isIncrement with
    | .T1, true => .incT12 | .T2, _ => .incT12 | .T1, false => .recT1
    | .T3, _ => .t3 | .T4, _ => .t4 | .T5, _ => .t4)

def countPop (H : XHistory n) (c : Pop) : ℕ :=
  (H.filter (fun ν => popOf? ν = some c)).length

def maxH (H : XHistory n) : ℕ := (H.map (·.h)).foldr max 0
def sumH (H : XHistory n) : ℕ := (H.map (·.h)).sum

/-- History well-formedness: only the last node may be terminal (`termLast`), and the
product of increment degrees is bounded by the ambient degree budget (`degProd` — §B2-DEF
"Π e_i ≤ n along a branch"; ACCEPTED source, planned MovesSp discharge; the field is the
inequality Π e_i ≤ n, NOT a divisibility — prose corrected 2026-07-30 verify-2, so any
future discharge targets ≤). -/
structure HistWF (n : ℕ) (H : XHistory n) : Prop where
  termLast : ∀ i : Fin H.length, (i : ℕ) + 1 < H.length → (H.get i).continuing = true
  degProd  : ((H.filter (fun ν => ν.continuing && ν.isIncrement)).map (·.e)).prod ≤ n

/-! ## §B The CONCRETE carrier (D5; Ruling 1) -/

/-- The monic box: monic degree-`n` polynomials over `ℤ_[p]`. -/
def MonicBox (n p : ℕ) [Fact p.Prime] : Type :=
  { f : Polynomial ℤ_[p] // f.Monic ∧ f.natDegree = n }

/-- The zero-discriminant locus of the box. -/
def discZero (n p : ℕ) [Fact p.Prime] : Set (MonicBox n p) := { f | f.1.discr = 0 }

/-- `v_p(disc f)` — ℕ-valued via the pinned `PadicInt.valuation : ℤ_[p] → ℕ`
(PadicIntegers.lean:321); junk value 0 on `discZero` (`PadicInt.valuation_zero`);
every statement using it carries `f ∉ discZero`. -/
noncomputable def vdisc {n p : ℕ} [Fact p.Prime] (f : MonicBox n p) : ℕ :=
  (f.1.discr).valuation

/-- The monic polynomial `X^n + Σ aᵢ Xⁱ` with prescribed lower coefficients. -/
noncomputable def polyOfCoeffs (R : Type) [CommRing R] (n : ℕ) (a : Fin n → R) :
    Polynomial R :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

/-- The (3b) finite-level count: coefficient tuples over `ZMod (p^D)` whose monic
polynomial has vanishing discriminant. -/
noncomputable def tailCount (p n D : ℕ) : ℕ :=
  Nat.card { a : Fin n → ZMod (p ^ D) // (polyOfCoeffs _ n a).discr = 0 }

/-- The (3b) INTEGER exponent `⌈(D − n·v_p(n))/(n − 1)⌉` (auditor-confirmed spot values:
4 and 1/4 at (2,2,0)/(2,2,4); 2/3, 2/9, 2/27 at (3,3,5/7/9)). -/
def tailExp (p n D : ℕ) : ℤ :=
  ⌈((D : ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ)⌉

/-- The a₀-free monic family tail: the derivative of the family member, mapped to
`ℚ_[p]` (rev 4, Fable findings 3/4: hom name = pinned `PadicInt.Coe.ringHom`
(PadicIntegers.lean:130); the `Fin (n−1+1)`/`Fin n` unification via an explicit OUTER
`Fin.cast` on the index, legal from `hn : 1 ≤ n` — threaded from every consumer's
`h2 : 2 ≤ n`). Derivative kills a₀: any slot-0 value gives the same `fTail`. -/
noncomputable def fTail (n p : ℕ) [Fact p.Prime] (hn : 1 ≤ n)
    (aTail : Fin (n - 1) → ℤ_[p]) : Polynomial ℚ_[p] :=
  ((polyOfCoeffs ℤ_[p] n
      ((Fin.cons 0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).map
    PadicInt.Coe.ringHom).derivative

/-- The level-`D` disc event of the a₀-fiber: `p^D ∣ disc (X^n + a₀ + Σ aᵢXⁱ)`. -/
def Event (p n D : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (aTail : Fin (n - 1) → ℤ_[p])
    (a0 : ℤ_[p]) : Prop :=
  (p : ℤ_[p]) ^ D ∣ (polyOfCoeffs ℤ_[p] n
      ((Fin.cons a0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))).discr

/-- A multiplicative-norm extension of `‖·‖_p` splitting `g` (D8 proof apparatus:
constructed by XF.3 via `SplittingField` + `spectralNorm`, consumed EXPLICITLY only by
the internals XF.4/XF.6, discharged inside XF.7's proof — appears in NO public
statement, Ruling 2). -/
structure ValExt (p : ℕ) [Fact p.Prime] (g : Polynomial ℚ_[p]) where
  L : Type
  [field : Field L]
  [alg : Algebra ℚ_[p] L]
  w : AbsoluteValue L ℝ
  ext : ∀ x : ℚ_[p], w (algebraMap ℚ_[p] L x) = ‖x‖
  splits : (g.map (algebraMap ℚ_[p] L)).Splits
  -- pinned mathlib's `Polynomial.Splits` is the refactored ABSOLUTE form (`f : R[X] → Prop`,
  -- "splits over its own ring"); the blueprint's `.Splits (RingHom.id L)` is its pre-refactor
  -- spelling of the SAME condition (old `Splits (RingHom.id L) q ↔ new q.Splits`). DEVIATION D-4.

instance {p : ℕ} [Fact p.Prime] {g : Polynomial ℚ_[p]} (V : ValExt p g) :
    Field V.L := V.field

instance {p : ℕ} [Fact p.Prime] {g : Polynomial ℚ_[p]} (V : ValExt p g) :
    Algebra ℚ_[p] V.L := V.alg

/-! ## §C The GMN interface (D6) and the ONE concrete context (D7; Ruling 1) -/

/-- Published GMN consumption surface over the CONCRETE carrier: (P2) + Thm 4.18(1).
Real instance: OM engine; owner MovesD/HC-2 (wave 4/phase 3). -/
structure GMNIndex (n p : ℕ) [Fact p.Prime] where
  ind : MonicBox n p → ℕ
  inStratum : MonicBox n p → XHistory n → Prop
  p2 : ∀ f, f ∉ discZero n p → 2 * ind f ≤ vdisc f

/-- THE context: per-f canonical tree presentation + detection vocabulary + ns fibers +
box content. Each field = ONE note-cited accepted/owed LOCAL input (blueprint §4 quotes
each); the X.3(a)/(b)/(d) CONCLUSIONS are units XG.2b–d, never fields (findings 11/12).
Inside the structure the Defs-level abbreviations `IsLeafB`/`capHB` are necessarily
spelled inline (`children b = ∅`; the `@ite … capDec` cap) — they are `def`ed literally
right below and unfold to these spellings (DEVIATION D-2). -/
structure XCtx (n p : ℕ) [Fact p.Prime] where
  Branch : MonicBox n p → Type
  hist : ∀ {f}, Branch f → XHistory n
  wf : ∀ {f} (b : Branch f), HistWF n (hist b)
  root : ∀ f, Branch f
  hist_root : ∀ f, hist (root f) = ([] : XHistory n)
  parent : ∀ {f}, Branch f → Option (Branch f)
  parent_hist : ∀ {f} (b b' : Branch f), parent b = some b' → ∃ ν, hist b = hist b' ++ [ν]
  parent_root : ∀ f, parent (root f) = none
  reach : ∀ {f} (b : Branch f),
    Relation.ReflTransGen (fun c d => parent c = some d) b (root f)
  /-- FINITE menus (§M-SPECIES). -/
  children : ∀ {f}, Branch f → Finset (Branch f)
  children_iff : ∀ {f} (b c : Branch f), c ∈ children b ↔ parent c = some b
  /-- full branch of a complete τ-halted tree -/
  complete : ∀ {f}, Branch f → Prop
  nsTrack : XNode n → Prop
  nsDec : DecidablePred nsTrack
  capDetectable : ∀ {f}, Branch f → Prop
  capDec : ∀ f, DecidablePred (@capDetectable f)
  /-- TB-CAP cap of the branch's OWN cells -/
  detCap : ∀ {f}, Branch f → ℕ
  /-- Thm 2.1's per-stratum N₀ -/
  threshold : ∀ {f}, Branch f → ℕ
  /-- "this leaf branch is cap-detected at level N" -/
  DetectedAt : ∀ {f}, Branch f → ℕ → Prop
  /-- Thm 2.1 + TB-CAP per-clause caps (X.3(b) INPUT). -/
  detectBranch :
    ∀ {f} (b : Branch f), children b = ∅ → (∀ ν ∈ hist b, ¬ nsTrack ν) →
      ∀ N, threshold b + @ite ℕ (capDetectable b) (capDec f b) (detCap b) 0 ≤ N →
        DetectedAt b N
  Undec : ℕ → Set (MonicBox n p)
  /-- X.0's DEFINITION of Undec, pinned. -/
  undec_spec :
    ∀ f N, f ∉ Undec N ↔
      (Finite (Branch f) ∧ ∀ b : Branch f, children b = ∅ → DetectedAt b N)
  /-- Thm 2.1 N-stability. -/
  undec_antitone : Antitone Undec
  /-- (NS-c) symbolic indexing. -/
  nsIdx : Type
  nsCountable : Countable nsIdx
  nsFiber : nsIdx → Set (MonicBox n p)
  /-- ns-leaf f's covered by the fiber family. -/
  nsCover :
    ∀ f, (∃ b : Branch f, children b = ∅ ∧ ∃ ν ∈ hist b, nsTrack ν) → ∃ i, f ∈ nsFiber i
  frac : Set (MonicBox n p) → ℚ
  /-- NORMALIZED (finding 5). -/
  frac_univ : frac Set.univ = 1
  frac_nonneg : ∀ s, 0 ≤ frac s
  frac_mono : ∀ s t, s ⊆ t → frac s ≤ frac t
  frac_union_le : ∀ s t, frac (s ∪ t) ≤ frac s + frac t
  frac_iUnion_null :
    ∀ (s : ℕ → Set (MonicBox n p)), (∀ i, frac (s i) = 0) → frac (⋃ i, s i) = 0
  /-- monotone convergence for the box content. -/
  frac_inter_tendsto :
    Filter.Tendsto (fun N => frac (Undec N)) Filter.atTop (nhds (frac (⋂ N, Undec N)))
  /-- the level-D cylinder fact (definitional at sync). -/
  vdisc_le_tail :
    ∀ D, frac { f | D ≤ vdisc f ∨ f ∈ discZero n p } ≤ (tailCount p n D : ℚ) / p ^ (n * D)

section CtxAbbrev

variable {p : ℕ} [Fact p.Prime]

/-- "finite branch" = leaf-terminated. -/
def IsLeafB (C : XCtx n p) {f : MonicBox n p} (b : C.Branch f) : Prop :=
  C.children b = ∅

/-- cap conventions (TOTAL): the cap if detectable, else 0. -/
def capHB (C : XCtx n p) {f : MonicBox n p} (b : C.Branch f) : ℕ :=
  @ite ℕ (C.capDetectable b) (C.capDec f b) (C.detCap b) 0

/-- (τ-ns)-FREE (decidable — XD.1). -/
def NsFreeB (C : XCtx n p) {f : MonicBox n p} (b : C.Branch f) : Prop :=
  ∀ ν ∈ C.hist b, ¬ C.nsTrack ν

/-- `b` is a prefix of `b'` (parent-path reachability). -/
def isPrefixB (C : XCtx n p) {f : MonicBox n p} (b b' : C.Branch f) : Prop :=
  Relation.ReflTransGen (fun c d => C.parent c = some d) b' b

/-- The fourth-piece family: (τ-ns)-FREE finite branches — leaf-terminated OR a prefix
of a complete branch (finding 1 REPAIRED: the 'finite branch' disjunct restored
verbatim). -/
def FourthPieceB (C : XCtx n p) {f : MonicBox n p} (b : C.Branch f) : Prop :=
  (IsLeafB C b ∨ ∃ b', C.complete b' ∧ isPrefixB C b b') ∧ NsFreeB C b

/-- DEFINED (not a field): the infinite-tree locus. -/
def InfTree (C : XCtx n p) : Set (MonicBox n p) :=
  { f | ¬ Finite (C.Branch f) }

/-- DEFINED (finding 4): THE tall event — some history node with `h ≥ h*`. -/
def TallEvent (C : XCtx n p) (hstar : ℕ) : Set (MonicBox n p) :=
  { f | ∃ b : C.Branch f, ∃ ν ∈ C.hist b, hstar ≤ ν.h }

/-- DEFINED: the deep event — some branch with `d_total ≥ d`. -/
def DeepEvent (C : XCtx n p) (d : ℕ) : Set (MonicBox n p) :=
  { f | ∃ b : C.Branch f, d ≤ dTotal (C.hist b) }

end CtxAbbrev

/-- The corpus's ONE shared parameter (Ruling 1): the concrete objects for every prime,
with the tree-to-stratum tie. Real instance owner: MovesD/MovesT (wave-4 sync); ONE
inhabitation obligation for the whole corpus, tracked in the campaign ledger. -/
structure XFamily (n : ℕ) where
  ctx : ∀ (p : ℕ) [Fact p.Prime], XCtx n p
  gmn : ∀ (p : ℕ) [Fact p.Prime], GMNIndex n p
  /-- §D4-R: f lies in the stratum of each of its own histories. -/
  gmnLink :
    ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (ctx p).Branch f),
      (gmn p).inStratum f ((ctx p).hist b)

/-- n-ONLY constants (D9, finding 3): defined BEFORE any p is in scope, so p-freeness
is enforced by binder order, not convention. -/
structure XConsts (n : ℕ) where
  /-- WEIGHT-CHARGE's s(n). -/
  s : ℕ
  /-- (X2-AFF)/(X2-CAP) constants. -/
  c0 : ℚ
  ccap : ℚ
  c0nonneg : 0 ≤ c0
  ccapnonneg : 0 ≤ ccap
  /-- (X.2) target slopes. -/
  cd : ℚ
  cd' : ℚ
  ch : ℚ
  ch' : ℚ
  cdpos : 0 < cd
  chpos : 0 < ch
  /-- (X2-TAILS) constants. -/
  CT : ℝ
  cT : ℝ
  CTpos : 0 < CT
  cTpos : 0 < cT

/-- `Desc_d` keyed by `d_cert` (D4/(CD)): the f's lying in SOME stratum with certified
depth ≥ d. -/
def DescX (X : XFamily n) (p : ℕ) [Fact p.Prime] (st : AlignState) (d : ℕ) :
    Set (MonicBox n p) :=
  { f | ∃ H, (X.gmn p).inStratum f H ∧ d ≤ dCert st H }

/-! ## §D The kernels as Props over the shared context (Ruling 1; findings 2/3/4/6).
Each `def …P : Prop` quotes its display in its docstring; asserting it = asserting the
note's condition about THE objects. Variables: `(X : XFamily n) (K : XConsts n)`;
`∀ p` INSIDE each Prop (D9). -/

/-- (X1a-ALIGN): "d_cert(H) ≤ ind(f) on every stratum, off disc = 0". -/
def X1aAlignP (n : ℕ) (X : XFamily n) (st : AlignState) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H → dCert st H ≤ (X.gmn p).ind f

/-- X.1b, T4 burden: "#T4(H) ≤ s(n)·v_p(disc f)". -/
def WeightChargeT4P (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H → countPop H .t4 ≤ K.s * vdisc f

/-- X.1b, FULL burden: "#T1-recenterings + #T4 ≤ s(n)·v_p(disc f)". -/
def WeightChargeFullP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H →
      countPop H .recT1 + countPop H .t4 ≤ K.s * vdisc f

/-- (X2-AFF): "thr(b) ≤ 1 + c₀·Σ h_r on the fourth-piece family". -/
def X2AffP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f),
    FourthPieceB (X.ctx p) b →
      ((X.ctx p).threshold b : ℚ) ≤ 1 + K.c0 * sumH ((X.ctx p).hist b)

/-- (X2-CAP): "cap(b) ≤ c_cap·(1 + Σ h_r)", quantified INSIDE the ns-free fourth-piece
family (finding 2). -/
def X2CapP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f),
    FourthPieceB (X.ctx p) b → (X.ctx p).capDetectable b →
      ((X.ctx p).detCap b : ℚ) ≤ K.ccap * (1 + sumH ((X.ctx p).hist b))

/-- (X.2) target: undetected-at-N fourth-piece branches are deep or tall at linear
rates. -/
def X2ProgressP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f) (N : ℕ),
    FourthPieceB (X.ctx p) b → N < (X.ctx p).threshold b + capHB (X.ctx p) b →
      K.cd * N - K.cd' ≤ (dTotal ((X.ctx p).hist b) : ℚ) ∨
      K.ch * N - K.ch' ≤ (maxH ((X.ctx p).hist b) : ℚ)

/-- (X2-TAILS): "frac(TallEvent h*) ≤ C_T·p^{−c_T·h*}" — THE defined event
(finding 4). -/
def X2TailsP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (hstar : ℕ),
    ((X.ctx p).frac (TallEvent (X.ctx p) hstar) : ℝ) ≤ K.CT * (p : ℝ) ^ (-(K.cT * hstar))

/-- (X2-BRIDGE), both clauses. rev 4 (Fable finding 1): the note's "(τ-ns)-FREE FINITE
BRANCH" witness — leaf-terminated (`IsLeafB`) in BOTH clauses. The witness then
satisfies `FourthPieceB` via its FIRST disjunct (`IsLeafB b`) ∧ `NsFreeB b`, which is
what `X2ProgressP`/XD.4 consume. -/
def X2BridgeP (n : ℕ) (X : XFamily n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
    ((X.ctx p).Undec N ⊆ discZero n p ∪ (⋃ i, (X.ctx p).nsFiber i) ∪ InfTree (X.ctx p) ∪
      { f | ∃ b : (X.ctx p).Branch f,
          IsLeafB (X.ctx p) b ∧ NsFreeB (X.ctx p) b ∧
            N < (X.ctx p).threshold b + capHB (X.ctx p) b }) ∧
    (X.ctx p).frac { f | f ∈ (X.ctx p).Undec N ∧
      ¬ ∃ b : (X.ctx p).Branch f,
          IsLeafB (X.ctx p) b ∧ NsFreeB (X.ctx p) b ∧
            N < (X.ctx p).threshold b + capHB (X.ctx p) b } = 0

/-- (ns-null) TAG: every (NS-c) fiber is null. -/
def NsNullP (n : ℕ) (X : XFamily n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (i : (X.ctx p).nsIdx), (X.ctx p).frac ((X.ctx p).nsFiber i) = 0

/-- X.3(a)'s route disjunction, verbatim tags. -/
def X3aRouteP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  (X1aAlignP n X ⟨true, true⟩  ∧ WeightChargeT4P n X K) ∨
  (X1aAlignP n X ⟨true, false⟩ ∧ WeightChargeFullP n X K)

/-! ## §E Series objects (finding 12: `densityOf` DEFINED; finding 13: additivity
defined) -/

/-- The campaign's splitting-type target for degree `n`. OPAQUE until the Defs-sync
round binds it to the campaign's concrete target type (blueprint E-gate note); opacity
commits to NO structure, so no statement over it can degenerate (DEVIATION D-3). -/
opaque SplitType : ℕ → Type

/-- Per-(p) series presentation: the countable family of complete realizable finite
trees with their fibers and letter-computed types. Fields = (NS-a)/§D4-R inputs; the
density IDENTITY is the unit XG.4, never a field. Owner MovesD/MovesT. -/
structure SeriesData (n p : ℕ) [Fact p.Prime] (C : XCtx n p) where
  FinTree : Type
  treeCountable : Countable FinTree
  fiber : FinTree → Set (MonicBox n p)
  /-- the letter-computed type -/
  typemult : FinTree → SplitType n
  /-- the TRUE splitting type of f -/
  splitType : MonicBox n p → SplitType n
  fiber_disjoint : ∀ T T', T ≠ T' → Disjoint (fiber T) (fiber T')
  /-- fibers are decided sets -/
  fiber_decided : ∀ T, Disjoint (fiber T) (⋂ N, C.Undec N)
  decided_covered : ∀ f, f ∉ (⋂ N, C.Undec N) → f ∉ discZero n p → ∃ T, f ∈ fiber T

variable {p : ℕ} [Fact p.Prime] {C : XCtx n p}

/-- DEFINED (finding 12): the density of a splitting type = the content of its
true-type event. -/
def densityOf (S : SeriesData n p C) (σ : SplitType n) : ℚ :=
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


/-- From the termLast discipline (only the last node may be non-continuing) the length
exceeds the continuing-count by at most one.
[SYN2-S1 SWEEP-6, 2026-07-31: hoisted SURVIVOR — XD2's raw-hypothesis form (the more
general of the two wave-minted copies; XG2d's HistWF-keyed twin and its private
`len_le_filter_succ` engine are deleted, uses re-pointed through `.termLast`).] -/
theorem length_le_dTotal_succ {n : ℕ} (H : XHistory n)
    (hterm : ∀ i : Fin H.length, (i : ℕ) + 1 < H.length → (H.get i).continuing = true) :
    H.length ≤ dTotal H + 1 := by
  induction H with
  | nil => simp [dTotal]
  | cons a t ih =>
    -- termLast restricts to the tail
    have htTerm : ∀ j : Fin t.length, (j : ℕ) + 1 < t.length →
        (t.get j).continuing = true := by
      intro j hj
      have h := hterm j.succ (by simpa using hj)
      simpa [List.get_cons_succ] using h
    -- if the tail is nonempty, the head is continuing
    have haCont : t.length ≠ 0 → a.continuing = true := by
      intro hne
      have h := hterm ⟨0, Nat.succ_pos _⟩ (by simp; omega)
      simpa [List.get_cons_zero] using h
    have IH := ih htTerm
    by_cases hc : a.continuing = true
    · have hd : dTotal (a :: t) = dTotal t + 1 := by
        simp [dTotal, hc]
      simp only [List.length_cons]
      omega
    · have ht0 : t.length = 0 := by
        by_contra h0
        exact hc (haCont h0)
      simp only [List.length_cons, ht0]
      omega

end LeanUrat.MovesX
