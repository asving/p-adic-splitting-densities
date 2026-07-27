# MOVES §X-EXHAUST — Lean formalization blueprint (MovesX corpus)
# REV 2 (post-Codex-audit, 25 findings repaired)

*Rev 2, 2026-07-28. Repairs ALL 25 findings of `lean/notes/MOVESX_AUDIT_CODEX_2026-07-28.md`
(REJECT 14 crit / 11 gap); findings→repairs table in §6. Source of truth unchanged: the
DUAL-ACCEPTED §X-EXHAUST rev 8 (`lean/notes/MOVES_2026-07-24.md` ~10947–11555). Consumes
MovesSp (parallel blueprint; planned names cited generically, sync at Defs round).
Protocol-L. Discipline: NO new axioms; every open kernel a HYPOTHESIS STRUCTURE with its
note display quoted in its docstring — never weakened, merged, or silently strengthened;
`sorry`-free ≠ non-vacuous; statement-fence applies.*

---

## 0. What §X-EXHAUST is, and what is formalizable NOW

Four layers: **X.1a** the per-species INDEX TABLE (rows T0–T5 keyed by letter fields
e, h, ℓ, selection) turning certified depth into GMN index into v_p(disc f) — pointwise,
measure-free, conditional exactly on (X1a-ALIGN); **X.1b** WEIGHT-CHARGE (OPEN; only the
two-step reduction DISPLAY is derived); **X.2** the dichotomy (kernel OPEN; only
(X2-HYP)'s √N shape is derived given (X2-AFF)∧(X2-CAP)); **X.3** the density form,
assembled from X.1a + the ELEMENTARY DISCRIMINANT TAIL (3b), every conditionality tagged.

DERIVED layer (provable outright): row classification + selection constraint; the
(P1)-pin lattice counts as EQUALITIES (rev 2 — finding 3); the T3 degree charge FROM the
accepted Πe ≤ n branch fact (rev 2 — finding 5); (CD) + d_cert ≡ 0; the four-population
partition; the X.1b reduction arithmetic in CLEARED form (rev 2 — finding 22); (X2-HYP);
the (τ-ns)-FREE predicate + cap totality; the tail (3b) with the note's INTEGER exponent
(rev 2 — finding 20); X.3's assembly DERIVED from contentful interface fields — the
rev-1 `MassLink` shortcut is DELETED (rev 2 — finding 24).
HYPOTHESIS layer (one named structure per kernel, one unit each — rev 2, findings 15/16):
(ALIGN-inc)/(ALIGN-rec) via `X1aAlign`, WEIGHT-CHARGE (T4 + full), (X2-AFF), (X2-CAP),
(X2-BRIDGE), (X2-TAILS), (X2-PROGRESS), VP-SOUND, the (ns-null) tag; plus the
accepted-perimeter interfaces (GMN, measure content, tree structure) — each field quoted
in §4, each with an INHABITATION note naming the intended real instance + owner.

---

## 1. Design decisions

**D1 — Nodes = planned MovesSp letters + retained height pair + COHERENCE fields.**
`XNode n` carries (e, h, ℓ, selection, isIncrement, s₀, u₀) with well-formedness
(1 ≤ e, h, ℓ; coprime e h; μ·g ≤ ℓ) AND the table's increment/recentering coherence
(rev 2, finding 4): T2/T3 shapes are increment-only, T4 recentering-only — species facts
(D.8 key ×e; D.10 only at e_read = 1, the Species lemma), carried as XNode fields with
planned MovesSp discharge at sync. Histories are `List (XNode n)` PLUS the `HistWF`
well-formedness structure (rev 2, findings 5/9): terminal-read-last/at-most-one (§D4-R
branch shape) and the accepted §B2-DEF branch fact Π e_i ≤ n — ACCEPTED-source fields
(planned `MovesSp.degProd_le`, `MovesSp.termLast`), discharged at sync, NOT open kernels.

**D2 — DOUBLED index, division-free (unchanged).** `ind2 : ℕ` = twice (IND):
T1 ↦ ℓ(ehℓ−e−h+1), T2 ↦ (e−1)(h−1), T3/T4 ↦ 0; (X.1a) reads v_p(disc f) ≥ Σ ind2 =
2·CUM. All table-layer statements in ℕ.

**D3 — The (P1) region as a Finset (unchanged), now tied by EQUALITY.** `p1Region` :=
on-or-below S, strictly above L, strictly beyond L′ (Remark 4.14 PINNED). Rev 2
(finding 3): the table identity is `ind2 ν = 2 · ν.region.card` — equality, per row.

**D4 — (CD) as a discharge-state-indexed count (unchanged).** `AlignState` = the two
sub-clause Booleans; `dCert ⟨false,false⟩ = 0` a THEOREM; no `d_gen^sem` anywhere.
NEW rev 2 (findings 6/7): the Desc object is formalized — `DescX A st d` := the union of
strata still descending at certified depth ≥ d — so (X.1a) is stated as the note's
TWO-inclusion chain, not its numeric corollary.

**D5 — Mathlib discriminant decision (confirmed).** Corpus discriminant =
`Polynomial.discr` over `ℤ_[p]`, tied to `resultant f f.derivative` via Mathlib's
`resultant_deriv` (monic ⟹ lc = 1). Tail (3b) at FINITE LEVEL over `ZMod (p^D)` boxes
(`Nat.card`), reduction map = Mathlib's `PadicInt.toZModPow` (rev 2, finding 18 — typed).
EXPONENT ARITHMETIC IN ℤ (rev 2, finding 20): D′ := ⌈(D − n·v_p(n) : ℤ)/(n−1)⌉ ∈ ℤ, zpow
in ℚ — the note's integer subtraction, verified at n=2, p=2, D=0 (note bound 4) and D=4
(note bound 1/4) in unit XF.7. No p-adic Haar measure anywhere.

**D6 — GMN apparatus as an interface (unchanged), over an explicit carrier.**
`IndexApparatus n p F`: carrier `F` (the monic box), `vdisc : F → ℕ` meaningful off the
`discZero : Set F` locus (the note works "off {disc f = 0}"), `ind`, (P2), `inStratum`.
INHABITATION (rev 2, finding 15): intended real instance = the OM-engine/MovesD monic-box
carrier with `vdisc := p-multiplicity of Polynomial.discr`; owner: MovesD + HC-2 (the
JetSetup-existence bridge), wave-4/phase-3 sync — recorded per structure in §4.

**D7 — Owed-elsewhere objects as CONTENTFUL interface structures (rebuilt, rev 2,
findings 10/14/15/23/24).** `XTreeInterface` is now a rooted forest presentation: root,
parent/children (`Finset` children = finite menus), reachability, per-branch histories,
`isPrefix`, `complete`, nsTrack/capDetectable/detCap — everything König and FourthPiece
need. `XMassInterface n p F A` replaces bare-Prop fields with contentful ones over an
abstract point space `F`: `Undec : ℕ → Set F`, a finitely-subadditive normalized content
`frac : Set F → ℚ` with its content laws as fields, `discZero`, the countable ns-fiber
family, `infBranch`, and the four LINK fields (stratumLink, detectInter, nsInUndec,
discZero_le_tail) — each a note-cited accepted/owed fact, quoted in §4. X.3's conclusion
is then DERIVED (rev 2: `MassLink` deleted; nothing smuggles X.3(d)).

**D8 — ValExt: CONSTRUCTION route chosen (rev 2, finding 19).** The interface `ValExt`
lives in Defs; unit XF.3 is the CONSTRUCTION `valExtOf g : ValExt p g` over
`g.SplittingField` via Mathlib `spectralNorm` (+ `Krasner.lean` machinery). All root-side
units (XF.4/6/7/8) take an explicit `(V : ValExt …)` argument, so they compile and prove
independently of XF.3's fate; the single wrapper unit XF.9 plugs `valExtOf` in to give
the UNCONDITIONAL (3b). If XF.3 sticks (twice, per the stuck rule), XF.9 alone is stuck,
(3b) stays conditional-on-ValExt, and the adjudication is a Defs-defect round — the
resolution is recorded HERE, not left open.

---

## 2. Proposed Defs skeleton (`lean/LeanUrat/MovesX/Defs.lean`) — REV 2

```lean
import LeanUrat.Moves.Defs
-- import LeanUrat.MovesSp.Defs   -- Defs-sync round
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace LeanUrat.MovesX

/-! §A Nodes, rows, region, doubled index -/

structure XNode (n : ℕ) where
  e ell h s0 u0 : ℕ
  sel : Option (ℕ × ℕ)              -- selection (g, μ) or ⊥
  isIncrement : Bool                 -- D.8 increment vs D.10 recentering
  epos : 1 ≤ e
  hpos : 1 ≤ h
  ellpos : 1 ≤ ell
  hcop : Nat.Coprime e h
  selBound : ∀ g μ, sel = some (g, μ) → 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ ell
  -- COHERENCE (rev 2, finding 4; table rows T2/T3 "(increment…)", T4 "recenterings";
  -- species facts, planned MovesSp discharge at sync):
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

/-- Remark 4.14's counted set: on-or-below S, strictly above L, strictly beyond L′. -/
def p1Region (s0 u0 e h ell : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc s0 (s0 + e * ell) ×ˢ Finset.Ioc u0 (u0 + h * ell)).filter
    (fun q => h * (q.1 - s0) + e * (q.2 - u0) ≤ e * h * ell)
def XNode.region (ν : XNode n) : Finset (ℕ × ℕ) := p1Region ν.s0 ν.u0 ν.e ν.h ν.ell

def ind2 (ν : XNode n) : ℕ :=
  match rowOf ν with
  | .T1 => ν.ell * (ν.e * ν.h * ν.ell + 1 - ν.e - ν.h)   -- ℕ-safe: XA.4's guard
  | .T2 => (ν.e - 1) * (ν.h - 1)
  | _   => 0

/-! §B (CD), populations, history well-formedness -/

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
    | .T3, _ => .t3 | .T4, _ => .t4 | .T5, _ => .t4)   -- T5 branch unreachable (continuing)
def countPop (H : XHistory n) (c : Pop) : ℕ := (H.filter (popOf? · = some c)).length

def maxH (H : XHistory n) : ℕ := (H.map (·.h)).foldr max 0     -- max h(∅) = 0
def sumH (H : XHistory n) : ℕ := (H.map (·.h)).sum             -- Σ over ALL reads

/-- ACCEPTED-source history well-formedness (rev 2, findings 5/9): NOT open kernels;
    planned discharge `MovesSp.termLast` / `MovesSp.degProd_le` at Defs sync. -/
structure HistWF (n : ℕ) (H : XHistory n) : Prop where
  termLast : ∀ i : Fin H.length, (i : ℕ) + 1 < H.length → (H.get i).continuing = true
  degProd  : ((H.filter (fun ν => ν.continuing && ν.isIncrement)).map (·.e)).prod ≤ n
```

```lean
/-! §C The GMN carrier interface and the Desc object (D6; findings 6/7/15) -/

/-- (P2) + Thm 4.18(1) consumption surface, over an explicit monic-box carrier F.
    INHABITATION: real instance = MovesD monic box + `Polynomial.discr` p-multiplicity;
    owner MovesD/HC-2, wave-4 sync. -/
structure IndexApparatus (n p : ℕ) (F : Type) where
  discZero  : Set F                    -- {disc f = 0}
  vdisc     : F → ℕ                    -- v_p(disc f), meaningful off discZero
  ind       : F → ℕ
  p2        : ∀ f, f ∉ discZero → 2 * ind f ≤ vdisc f
  inStratum : F → XHistory n → Prop    -- f ∈ stratum(H)

/-- Desc_d keyed by d_cert per (CD): the union of strata still descending at
    certified depth ≥ d (X.0). -/
def DescX (A : IndexApparatus n p F) (st : AlignState) (d : ℕ) : Set F :=
  { f | ∃ H, A.inStratum f H ∧ d ≤ dCert st H }

/-- (X1a-ALIGN) — OPEN KERNEL, sub-clauses (ALIGN-inc)/(ALIGN-rec) indexed by st.
    Field = the assembly paragraph's conclusion: "Thm 4.18(1) sums over ALL orders…,
    so ind(f) ≥ d_cert(H) for EACH branch H". INHABITATION: discharge = the D.12
    dictionary transport; owner: the math side (kernel OPEN); no Lean instance owed. -/
structure X1aAlign (n p : ℕ) (F : Type) (A : IndexApparatus n p F) (st : AlignState) : Prop where
  transport : ∀ f H, f ∉ A.discZero → A.inStratum f H → dCert st H ≤ A.ind f

/-! §D The rooted-forest tree interface (D7; findings 10/23) -/

/-- §D4-R/§T-ASSEMBLY objects X.2/X.3 type against. Rooted forest with FINITE menus
    (§M-SPECIES; planned `MovesSp.menuFinite`). INHABITATION: real instance = MovesD's
    T_can presentation (PrefFamily precedent); owner MovesD, wave-4 sync. -/
structure XTreeInterface (n : ℕ) where
  Branch : Type
  hist : Branch → XHistory n
  wf : ∀ b, HistWF n (hist b)
  root : Branch
  hist_root : hist root = []
  parent : Branch → Option Branch
  parent_hist : ∀ b b', parent b = some b' → ∃ ν, hist b = hist b' ++ [ν]
  parent_root : parent root = none
  reach : ∀ b, Relation.ReflTransGen (fun c d => parent c = some d) b root
  children : Branch → Finset Branch                 -- FINITE child menus
  children_iff : ∀ b c, c ∈ children b ↔ parent c = some b
  complete : Branch → Prop        -- full branch of a complete τ-halted tree ([3t] τ)
  nsTrack : XNode n → Prop        -- per-node (τ-ns) cell-data predicate (VP clauses)
  nsDec : DecidablePred nsTrack
  capDetectable : Branch → Prop   -- ≥ 1 window read reaching a (τ-irr) detection cell
  capDec : DecidablePred capDetectable
  detCap : Branch → ℕ             -- TB-CAP cap of H's OWN leaf-detection cells
  threshold : Branch → ℕ          -- Thm 2.1's N₀ per stratum (§C's N(H,Z), trivial Z)

def isPrefix (I : XTreeInterface n) (a b : I.Branch) : Prop :=
  Relation.ReflTransGen (fun c d => I.parent c = some d) b a   -- a below-or-equal b

/-- (τ-ns)-FREE: the membership predicate ITSELF excludes ns tracks (rev 5). -/
def NsFree (I : XTreeInterface n) (b : I.Branch) : Prop :=
  ∀ ν ∈ I.hist b, ¬ I.nsTrack ν    -- Decidable via nsDec (List.decidableBAll)

/-- The FOURTH-PIECE FAMILY (X.2 rev 5, finding 10): "H is a finite branch or prefix
    of a complete τ-halted tree AND H is (τ-ns)-FREE". -/
def FourthPiece (I : XTreeInterface n) (b : I.Branch) : Prop :=
  (∃ b', I.complete b' ∧ isPrefix I b b') ∧ NsFree I b

/-- cap(H), TOTAL by the DOMAIN CONVENTIONS (genuine cap iff cap-detectable, else 0). -/
def capH (I : XTreeInterface n) (b : I.Branch) : ℕ :=
  if I.capDetectable b then I.detCap b else 0
```

```lean
/-! §E The named kernels (one structure per display; findings 11–14, 16, 17).
    Constants are ℚ (the note's candidates include 1/2 — finding 13); NONNEG
    normalizations are recorded WLOG-safe (Σh, cap ≥ 0: enlarging a coefficient
    preserves each bound, so no note instance is excluded) — §4 flags them. -/

/-- WEIGHT-CHARGE, T4-restricted burden (X.3(a1)'s consumption). OPEN. -/
structure WeightChargeT4 (n p : ℕ) (F : Type) (A : IndexApparatus n p F) where
  s : ℕ
  bound : ∀ f H, f ∉ A.discZero → A.inStratum f H → countPop H .t4 ≤ s * A.vdisc f

/-- WEIGHT-CHARGE, FULL recentering burden: "#{recentering nodes of H} ≤ s(n)·v_p(disc f)".
    OPEN. -/
structure WeightChargeFull (n p : ℕ) (F : Type) (A : IndexApparatus n p F) where
  s : ℕ
  bound : ∀ f H, f ∉ A.discZero → A.inStratum f H →
    countPop H .recT1 + countPop H .t4 ≤ s * A.vdisc f

/-- (X2-AFF): "threshold(H) ≤ 1 + c₀(n)·Σ_{r∈H} h_r", quantified over the
    fourth-piece family ONLY (finding 11). OPEN, owned by PROGRESS. -/
structure X2Aff (n : ℕ) (I : XTreeInterface n) where
  c0 : ℚ
  c0nonneg : 0 ≤ c0                    -- WLOG-safe normalization (§4)
  bound : ∀ b, FourthPiece I b → (I.threshold b : ℚ) ≤ 1 + c0 * sumH (I.hist b)

/-- (X2-CAP): "cap(H) ≤ c_cap(n)·(1 + Σ h_r)" on cap-detectable branches; extends by
    the 0-convention to the fourth-piece family. OPEN, owned by PROGRESS. -/
structure X2Cap (n : ℕ) (I : XTreeInterface n) where
  ccap : ℚ
  ccapnonneg : 0 ≤ ccap
  bound : ∀ b, I.capDetectable b → (I.detCap b : ℚ) ≤ ccap * (1 + sumH (I.hist b))

/-- (X2-PROGRESS), the X.2 linear target: threshold(H)+cap(H) > N ⟹ d_total ≥ c_d·N−c_d′
    OR max h ≥ c_h·N−c_h′, positive slopes, n-only/p-free (p-freeness recorded §4;
    enforced at instance time). OPEN — THE kernel. -/
structure X2Progress (n : ℕ) (I : XTreeInterface n) where
  cd ch : ℚ ; cd' ch' : ℚ
  cdpos : 0 < cd ; chpos : 0 < ch
  dichotomy : ∀ b N, FourthPiece I b → (N : ℚ) < I.threshold b + capH I b →
    cd * N - cd' ≤ dTotal (I.hist b) ∨ ch * N - ch' ≤ maxH (I.hist b)

/-! §F The mass interface + (X2-BRIDGE)/(X2-TAILS) (findings 12, 14, 15, 24) -/

/-- The measure-side objects X.3 types against: an abstract monic-box point space F
    with a normalized monotone finitely-subadditive content and the note-cited link
    fields. Every field is an accepted/owed fact quoted in §4. INHABITATION: real
    instance = MovesD/MovesT box-fraction content; owner wave-4 sync. -/
structure XMassInterface (n p : ℕ) (F : Type) (A : IndexApparatus n p F) where
  Undec : ℕ → Set F
  frac : Set F → ℚ
  frac_nonneg : ∀ s, 0 ≤ frac s
  frac_mono : ∀ s t, s ⊆ t → frac s ≤ frac t
  frac_union_le : ∀ s t, frac (s ∪ t) ≤ frac s + frac t
  frac_iUnion_null : ∀ (s : ℕ → Set F), (∀ i, frac (s i) = 0) → frac (⋃ i, s i) = 0
  undec_antitone : Antitone Undec                          -- Thm 2.1 N-stability
  frac_inter_tendsto :                                     -- monotone convergence (owed)
    Filter.Tendsto (fun N => frac (Undec N)) Filter.atTop (nhds (frac (⋂ N, Undec N)))
  nsIdx : Type ; nsCountable : Countable nsIdx             -- 𝒯^ns countable ((NS-c))
  nsFiber : nsIdx → Set F
  infBranch : Set F                                        -- {T_can^τ(f) has an ∞ branch}
  stratumLink :                                            -- ∞ branch ⟹ long prefixes (§D4-R)
    ∀ f ∈ infBranch, ∀ B, ∃ H, A.inStratum f H ∧ HistWF n H ∧ B ≤ dTotal H
  detectInter :                                            -- X.3(b)+(d): TB-CAP trichotomy
    (⋂ N, Undec N) ⊆ infBranch ∪ (⋃ i, nsFiber i) ∪ A.discZero
  nsInUndec : ∀ i, nsFiber i ⊆ ⋂ N, Undec N               -- (NS-d) typing
  discZero_le_tail : ∀ D, frac A.discZero ≤ (tailCount p n D : ℚ) / p ^ (n * D)
  tallFrac : ℕ → ℚ                                         -- μ{some read has h_r ≥ h*}
  deepFrac : ℕ → ℚ                                         -- μ{some branch has d_total ≥ d}

/-- (ns-null) TAG (closed at [3t]; displayed per (NS-c)): each ns fiber has mass 0. -/
def NsNull (M : XMassInterface n p F A) : Prop := ∀ i, M.frac (M.nsFiber i) = 0

/-- (X2-TAILS) [2b]-owed: μ{some read has h_r ≥ h*} ≤ C_T·p^{−c_T·h*}, C_T, c_T > 0
    REAL constants (finding 12); stated in ℝ via rpow. -/
structure X2Tails (n p : ℕ) (F : Type) (A : IndexApparatus n p F)
    (M : XMassInterface n p F A) where
  CT cT : ℝ
  CTpos : 0 < CT ; cTpos : 0 < cT
  bound : ∀ hstar : ℕ, (M.tallFrac hstar : ℝ) ≤ CT * (p : ℝ) ^ (-(cT * hstar))

/-- (X2-BRIDGE), OPEN, owned by PROGRESS — both displayed clauses as fields (finding 14). -/
structure X2Bridge (n p : ℕ) (F : Type) (A : IndexApparatus n p F)
    (I : XTreeInterface n) (M : XMassInterface n p F A) (link : F → I.Branch → Prop) : Prop where
  decomposition : ∀ N, M.Undec N ⊆ A.discZero ∪ (⋃ i, M.nsFiber i) ∪ M.infBranch ∪
    { f | ∃ b, link f b ∧ NsFree I b ∧ (N : ℚ) < I.threshold b + capH I b }
  existential : ∀ N, M.frac { f | f ∈ M.Undec N ∧
    ¬ ∃ b, link f b ∧ NsFree I b ∧ (N : ℚ) < I.threshold b + capH I b } = 0
    -- "for a.e. f ∈ Undec(N), SOME (τ-ns)-FREE branch has threshold + cap > N"
```

```lean
/-! §G The discriminant model (D5/D8) -/

def polyOfCoeffs (R : Type) [CommRing R] (n : ℕ) (a : Fin n → R) : Polynomial R :=
  Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

/-- Level-D tail event count, division-free (D5). -/
def tailCount (p n D : ℕ) : ℕ :=
  Nat.card { a : Fin n → ZMod (p ^ D) // (polyOfCoeffs _ n a).discr = 0 }

/-- The note's integer-ceiling exponent (finding 20): D′ = ⌈(D − n·v_p(n))/(n−1)⌉ ∈ ℤ. -/
def tailExp (p n D : ℕ) : ℤ := ⌈((D : ℤ) - n * padicValNat p n : ℚ) / (n - 1 : ℚ)⌉

/-- Valued home for the roots of g (D8). Constructed by XF.3 (`valExtOf`); consumed
    as an explicit argument everywhere else. NOT a note object — must never
    strengthen (3b)'s statement (§4 flag). -/
structure ValExt (p : ℕ) [Fact p.Prime] (g : Polynomial ℚ_[p]) where
  L : Type
  [field : Field L]
  [alg : Algebra ℚ_[p] L]
  w : AbsoluteValue L ℝ
  ext : ∀ x : ℚ_[p], w (algebraMap ℚ_[p] L x) = ‖x‖
  splits : (g.map (algebraMap ℚ_[p] L)).Splits (RingHom.id L)

/-! §H X.3's route tag and VP-SOUND -/

/-- X.3(a)'s hypothesis alternatives, verbatim:
    [(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)]. -/
inductive X3aRoute (n p : ℕ) (F : Type) (A : IndexApparatus n p F)
  | a1 (al : X1aAlign n p F A ⟨true, true⟩)  (wc : WeightChargeT4 n p F A)
  | a2 (al : X1aAlign n p F A ⟨true, false⟩) (wc : WeightChargeFull n p F A)
def X3aRoute.s : X3aRoute n p F A → ℕ | .a1 _ wc => wc.s | .a2 _ wc => wc.s

/-- VP-SOUND — (HEN-LIFT)/(OM-SAT), §T-ASSEMBLY's retained citation obligations,
    inherited by X.3's per-σ series (note finding 13): the typemult-to-true-type
    identification, over the series interface data (XG.4). -/
structure VPSound (n p : ℕ) (F : Type) (S : SeriesData n p F) : Prop where
  typeFaithful : ∀ T, S.typemult T = S.trueTypeOf T

/-- Series-side interface for XG.4 (MovesD/MovesT-owed; §4). `FinTree` = the complete
    realizable finite trees; `fiber T` = {f : T_can^τ(f) = T}; `densityσ` = the decided
    per-σ mass. -/
structure SeriesData (n p : ℕ) (F : Type) where
  FinTree : Type ; treeCountable : Countable FinTree
  fiber : FinTree → Set F
  typemult trueTypeOf : FinTree → SplitType n     -- SplitType per the campaign target
  densityσ : SplitType n → ℚ

end LeanUrat.MovesX
```

(Defs-level abbreviations `DescX`, `NsFree`-decidability instance, `X3aRoute.s` shown;
the E-gate entry criterion is this skeleton compiling with the two forward references
(`tailCount` before `XMassInterface`, `SeriesData` before `VPSound`) reordered.)

---

## 3. The units (id · statement · moves_ref · deps · sketch · difficulty · hypothesis_fields)

Files `lean/LeanUrat/MovesX/<id>.lean`, each importing `MovesX.Defs` + deps.

### Layer A — the index table

**XA.1 rowTotal** — full statement (finding 1 — no ellipsis; the ℓ = 1 edge cases explicit; `rowOf` total by construction, so these five iffs ARE exhaustiveness + exclusivity):
```lean
theorem rowTotal (ν : XNode n) :
    (rowOf ν = .T5 ↔ ν.sel = none) ∧
    (rowOf ν = .T1 ↔ ν.sel ≠ none ∧ 2 ≤ ν.ell) ∧
    (rowOf ν = .T2 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ 2 ≤ ν.e ∧ 2 ≤ ν.h) ∧
    (rowOf ν = .T3 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ 2 ≤ ν.e ∧ ν.h = 1) ∧
    (rowOf ν = .T4 ↔ ν.sel ≠ none ∧ ν.ell = 1 ∧ ν.e = 1)
```
moves_ref: "Every continuing node of every history falls in exactly one row (ℓ ≥ 2 vs ℓ = 1; then e, h…)". deps: Defs. sketch: unfold `rowOf`; `ellpos`/`hpos` turn ¬(2 ≤ ·) into = 1; `omega` per conjunct. EASY. hyp: none.

**XA.2 selForce** — `theorem selForce (ν : XNode n) (g μ) (hs : ν.sel = some (g, μ)) (h2 : 2 ≤ μ ∨ 2 ≤ g) : 2 ≤ ν.ell ∧ rowOf ν = .T1`.
moves_ref: "the selection constraint μ·g ≤ d(S) = ℓ forces every μ ≥ 2 or g ≥ 2 selection onto an ℓ ≥ 2 side". deps: XA.1. sketch: `selBound` gives 1 ≤ g, 1 ≤ μ, μ·g ≤ ℓ; either case gives ℓ ≥ 2 by `nlinarith`; row via XA.1. EASY. hyp: none.

**XA.3 t1Witness** — `theorem t1Witness (ν : XNode n) (h1 : rowOf ν = .T1) : (ν.s0 + ν.e, ν.u0 + (ν.ell - 1) * ν.h) ∈ ν.region ∧ 1 ≤ ν.region.card`.
moves_ref: T1 witness "(s+e, u+(ℓ−1)h): ON S one e-step from its initial point; strictly above L …; strictly beyond L′". deps: XA.1. sketch: three membership inequalities; the on-S equality case is INCLUDED by `p1Region`'s `≤` — the (P1) ON-OR-BELOW pin (§4 trap). `Finset.card_pos`. EASY. hyp: none.

**XA.4 t1Arith** — `theorem t1Arith (e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 2 ≤ ell) : e + h ≤ e * h * ell + 1 ∧ h * (ell - 1) ≤ e * h * ell + 1 - e - h ∧ 1 ≤ ell * (e * h * ell + 1 - e - h)`.
moves_ref: T1 column "½ℓ(ehℓ−e−h+1) ≥ ½ℓ·h(ℓ−1) ≥ 1 [e ≥ 1: ehℓ−e−h+1 = e(hℓ−1)−(h−1) ≥ h(ℓ−1)]". deps: none. sketch: first conjunct = the ℕ-truncation guard for `ind2`'s T1 arm; then `nlinarith` on the bracket identity. EASY. hyp: none.

**XA.5 t2Witness** — `theorem t2Witness (ν : XNode n) (h2 : rowOf ν = .T2) : (ν.s0 + 1, ν.u0 + 1) ∈ ν.region ∧ 2 ≤ (ν.e - 1) * (ν.h - 1) ∧ 2 ∣ (ν.e - 1) * (ν.h - 1)`.
moves_ref: T2 "explicit witness (s+1, u+1) … strictly below S ⟺ (e−1)(h−1) > 1 — true since e, h ≥ 2 and gcd(e,h) = 1 excludes (2,2)"; "(e−1)(h−1)/2 ≥ 1". deps: XA.1. sketch: membership ⟺ h + e ≤ eh ⟺ (e−1)(h−1) ≥ 1; coprimality kills (2,2) and both-even, giving ≥ 2 and parity. EASY-MEDIUM. hyp: none.

**XA.6 lat1** — `theorem lat1 (s0 u0 e h : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hcop : Nat.Coprime e h) : 2 * (p1Region s0 u0 e h 1).card = (e - 1) * (h - 1)`.
moves_ref: "Pick-style split: strict-interior count (EH−E−H−d)/2 + 1, on-side non-vertex count d − 1" at ℓ = 1 (both endpoints excluded; gcd ⟹ no on-segment point). deps: Defs. sketch: the involution (x, y) ↦ (s0+e+s0+1−x… i.e. reflection through the open rectangle's center) swaps strictly-below-S and strictly-above-S; coprimality ⟹ no lattice point ON the open segment; `Finset.card_nbij` + rectangle card. HARD (no Pick in Mathlib). hyp: none.

**XA.7a latSlice** — the column-block partition (finding 2 — the former XA.7 split into two one-lemma units):
```lean
theorem latSlice (s0 u0 e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 1 ≤ ell) :
    (p1Region s0 u0 e h ell).card
      = ∑ k ∈ Finset.range ell,
          ((p1Region (s0 + k * e) (u0 + (ell - 1 - k) * h) e h 1).card
            + e * ((ell - 1 - k) * h))
```
moves_ref: (IND)'s region decomposed: each e-wide column block k = a translated ℓ = 1 slice above a full e × (ℓ−1−k)h rectangle (the stride vertices ON S absorbed by the rectangles' top rows). deps: Defs. sketch: partition `p1Region` by x-block via `Finset.card_biUnion` (disjoint by x-range); within block k, the on-or-below condition splits at y = u0 + (ℓ−1−k)h into rectangle + translated slice (`Finset.card_image_of_injective` for the translation). HARD. hyp: none.

**XA.7b latGen** — `theorem latGen (s0 u0 e h ell : ℕ) (he : 1 ≤ e) (hh : 1 ≤ h) (hl : 1 ≤ ell) (hcop : Nat.Coprime e h) : 2 * (p1Region s0 u0 e h ell).card = ell * (e * h * ell + 1 - e - h)` — with `example` sanity anchors: ℓ = 1 reduces to XA.6; e = h = ℓ = 1 gives 0.
moves_ref: "(IND) ind(S) = ½(EH − E − H + d) = ½·ℓ·(ehℓ − e − h + 1)". deps: XA.6, XA.7a. sketch: substitute XA.6 into XA.7a; 2·Σ_k [eh(ℓ−1−k)] + ℓ(e−1)(h−1) = ehℓ(ℓ−1) + ℓ(eh−e−h+1) = ℓ(ehℓ+1−e−h) (`Finset.sum_range` + `ring_nf`-with-guards; ℕ-subtraction cleared via XA.4's guard). MEDIUM. hyp: none.

**XA.8 t34Zero** — `theorem t34Zero (ν : XNode n) (h34 : rowOf ν = .T3 ∨ rowOf ν = .T4) : ν.region.card = 0 ∧ ind2 ν = 0`.
moves_ref: T3 "interior count (e−1)·0/2 = 0; endpoints excluded"; T4 "only the two endpoints are lattice points on S (gcd(e,h) = 1); both excluded". deps: XA.1, XA.6. sketch: ℓ = 1 and (h = 1 ∨ e = 1) ⟹ (e−1)(h−1) = 0 ⟹ card = 0 by XA.6; `ind2` arm is 0 by cases. EASY. hyp: none. Docstring carries finding-1 semantics verbatim: "0" = NO positive per-side bound — NEVER "actual ind_r = 0".

**XA.9 ind2Region** — EQUALITY per row (audit finding 3):
```lean
theorem ind2Region (ν : XNode n) (hc : ν.continuing) :
    ind2 ν = 2 * ν.region.card ∧ ((rowOf ν = .T1 ∨ rowOf ν = .T2) → 1 ≤ ind2 ν)
```
moves_ref: the table's ind(S) column from (IND) — "pure arithmetic, DERIVED"; doubled per D2 (`ind2 = 2·ind(S) = 2·card`). deps: XA.3–XA.8. sketch: T1: XA.7b (+ XA.4 positivity); T2: XA.6 (ℓ = 1) + XA.5; T3/T4: XA.8; T5 excluded by `hc`. MEDIUM. hyp: none.

### Layer B — (CD), populations, degree charge

**XB.1 dCertZero** — `theorem dCertZero (H : XHistory n) : dCert ⟨false, false⟩ H = 0 ∧ ∀ st, dCert st H ≤ dTotal H`.
moves_ref: "At today's discharge state (neither sub-clause displayed) d_cert ≡ 0"; d_unc = d_total − d_cert. deps: Defs. sketch: `certified ⟨false,false⟩ ν = false` by row cases; filter monotone. EASY. hyp: none.

**XB.2 dCertMono** — `theorem dCertMono (H : XHistory n) : dCert ⟨true, false⟩ H = countPop H .incT12 ∧ dCert ⟨true, true⟩ H = countPop H .incT12 + countPop H .recT1`.
moves_ref: "given (ALIGN-inc): d_cert = #T1-increments + #T2; given both: also the T1 recenterings". deps: Defs. sketch: pointwise `certified st ν` ↔ `popOf? ν` case match (T2 → incT12 uses `t2inc`); List count algebra. EASY-MEDIUM. hyp: none.

**XB.3 fourPop** — `theorem fourPop (H : XHistory n) : dTotal H = countPop H .incT12 + countPop H .recT1 + countPop H .t3 + countPop H .t4`.
moves_ref: "the four-population decomposition {T1/T2 increments} ⊔ {T1 recenterings} ⊔ {T3} ⊔ {T4}". deps: XA.1. sketch: `popOf?` is total on continuing nodes and the four values are exclusive (finding 4 repaired: `t2inc`/`t3inc`/`t4rec` XNode coherence fields make T2/T3 increments and T4 recenterings BY TYPE); `List.length_filter` partition. MEDIUM. hyp: none (coherence is Defs-level, MovesSp-discharged at sync).

**XB.4 t3Charge** — `theorem t3Charge (H : XHistory n) (W : HistWF n H) (hn : 1 ≤ n) : countPop H .t3 ≤ Nat.log 2 n` — DERIVED (finding 5 repaired: the species/degree argument is proved HERE; only the accepted §B2-DEF branch fact Π e_i ≤ n rides, as the `HistWF.degProd` field with planned discharge `MovesSp.degProd_le`).
moves_ref: "each T3 node multiplies the key degree by e ≥ 2, so #T3 per branch ≤ ⌊log₂ n⌋ (derived…)". deps: XA.1, Defs. sketch: T3 nodes are continuing increments with e ≥ 2 (XA.1 + `t3inc`), so 2^(#T3) ≤ Π_{T3} e ≤ Π_{continuing increments} e ≤ n (`W.degProd`, `Finset.prod_le_prod_of_subset`-style on lists); then `Nat.pow_le_iff_le_log`. EASY-MEDIUM. hyp: `HistWF` (ACCEPTED-source, not a kernel).

### Layer C — the X.1a chain and the X.1b reduction

**XC.1 x1aChain** — the note's TWO-inclusion chain (findings 6/7 repaired):
```lean
theorem x1aChain (A : IndexApparatus n p F) (st : AlignState) (AL : X1aAlign n p F A st) :
    (∀ f H, A.inStratum f H → f ∈ DescX A st (dCert st H)) ∧
    (∀ f d, f ∈ DescX A st d → f ∉ A.discZero → 2 * d ≤ A.vdisc f)
```
moves_ref: "(X.1a) stratum(H) ⊆ Desc_{d_cert(H)} ⊆ { v_p(disc f) ≥ 2·d_cert(H) }" + "The first inclusion is the definition of Desc; the second is the displayed chain". deps: Defs. sketch: first inclusion: `⟨H, hf, le_rfl⟩` (definitional); second: `AL.transport` (dCert ≤ ind on the witness history) + `A.p2` chain. The off-discZero side condition is the (P2) reducible-case domain (v_p(disc) finite). EASY-MEDIUM. hyp_fields: `X1aAlign` (kernel), `IndexApparatus` (published (P2)/4.18(1)).

**XC.2 x1aTrivial** — the SAME two-inclusion chain at zero discharge, unconditional (finding 7):
```lean
theorem x1aTrivial (A : IndexApparatus n p F) :
    (∀ f H, A.inStratum f H → f ∈ DescX A ⟨false, false⟩ (dCert ⟨false, false⟩ H)) ∧
    (∀ f d, f ∈ DescX A ⟨false, false⟩ d → f ∉ A.discZero → 2 * d ≤ A.vdisc f)
```
moves_ref: "at zero discharge d_cert ≡ 0 and (X.1a) is trivially true". deps: XB.1. sketch: first inclusion definitional as in XC.1; second: any witness H has dCert = 0 (XB.1), so d = 0 and 2·0 ≤ vdisc — the numeric leg trivializes, the CHAIN is intact. EASY. hyp: none (the corpus's honest unconditional (X.1a) instance).

**XC.3 x1bReduction** — cleared display (matches XG.1's form):
```lean
theorem x1bReduction (A) (AL : X1aAlign n p F A ⟨true, false⟩) (WC : WeightChargeFull n p F A)
    (f H) (hf : A.inStratum f H) (hd : f ∉ A.discZero) (W : HistWF n H) (hn : 1 ≤ n) :
    2 * dTotal H ≤ (2 * WC.s + 1) * A.vdisc f + 2 * Nat.log 2 n
```
moves_ref: "d_total ≤ [v_p(disc f)/2 + ⌊log₂ n⌋] + s(n)·v_p(disc f) ⟹ v_p(disc f) ≥ (d_total − ⌊log₂ n⌋)/(s(n) + 1/2)" — cleared: ×2 gives 2·d_total ≤ (2s+1)·v + 2·⌊log₂ n⌋, the same inequality. deps: XB.2, XB.3, XB.4, XC.1. sketch: fourPop; 2·incT12 ≤ vdisc (XC.1 at ⟨true,false⟩ + XB.2); 2·(recT1 + t4) ≤ 2s·vdisc (WC); 2·t3 ≤ 2·log (XB.4); `omega`. MEDIUM. hyp_fields: X1aAlign(inc) ∧ WeightChargeFull ("X.1b ALONE discharges nothing" — finding 11 of the note) + HistWF.

**XC.4 x1bReductionT4** — route (a1)'s population bounds:
```lean
theorem x1bReductionT4 (A) (AL : X1aAlign n p F A ⟨true, true⟩) (WC : WeightChargeT4 n p F A)
    (f H) (hf : A.inStratum f H) (hd : f ∉ A.discZero) (W : HistWF n H) (hn : 1 ≤ n) :
    countPop H .t4 ≤ WC.s * A.vdisc f ∧
    2 * dTotal H ≤ (2 * WC.s + 1) * A.vdisc f + 2 * Nat.log 2 n
```
moves_ref: X.3(a1) "#T1/T2 = d_cert ≤ v_p(disc f)/2 by (X.1a) …; #T3 ≤ ⌊log₂ n⌋; #T4 ≤ s(n)·v_p(disc f) by WEIGHT-CHARGE RESTRICTED to the T4 population". deps: XB.2–4, XC.1. sketch: as XC.3 with st = ⟨true,true⟩ covering incT12 + recT1 inside 2·dCert ≤ vdisc. MEDIUM. hyp_fields: X1aAlign(both) ∧ WeightChargeT4 + HistWF.

### Layer D — (τ-ns)-FREE, caps, (X2-HYP)

**XD.1 nsFreeDec** — `instance (I : XTreeInterface n) : DecidablePred (NsFree I)` + `theorem capTotal (I) (b) : (¬ I.capDetectable b → capH I b = 0) ∧ (I.capDetectable b → capH I b = I.detCap b)` + `theorem maxHNil : maxH ([] : XHistory n) = 0 ∧ sumH ([] : XHistory n) = 0`.
moves_ref: "the membership predicate itself excludes them"; "cap(H) := 0 for every hen/no-window branch"; "max h(∅) := 0". deps: Defs. sketch: `List.decidableBAll` via `nsDec`; `if` splits; `rfl`. EASY. hyp: interface only.

**XD.2 x2hypCount** — UNCONDITIONAL (finding 8; the empty history carried by maxH ∅ = 0, both sides 0):
```lean
theorem x2hypCount (H : XHistory n) (W : HistWF n H) :
    sumH H ≤ (dTotal H + 1) * maxH H
```
moves_ref: "H's reads are its d_total continuing nodes PLUS at most one terminal read … Σ_{r∈H} h_r ≤ (d_total(H) + 1)·max h(H); the d_total = 0 lone-terminal-read history is carried by the +1". deps: Defs. sketch: `W.termLast` (finding 9 repaired: the field exists) gives H.length ≤ dTotal H + 1; each h_r ≤ maxH; sum ≤ length·max. MEDIUM. hyp: `HistWF` (ACCEPTED-source).

**XD.3 x2hypDichotomy** — `theorem x2hypDichotomy (M : ℚ) (d m : ℕ) (h : M < (d + 1) * m) : M < ((d : ℚ) + 1)^2 ∨ M < (m : ℚ)^2`.
moves_ref: "(d_total+1)·max h > (…) ⟹ d_total + 1 ≥ √(…) OR max h ≥ √(…)" — the √-free squared form. deps: none. sketch: contrapositive; (d+1)², m² ≤ M ⟹ ((d+1)m)² ≤ M² ⟹ (d+1)m ≤ M (nonneg); `nlinarith`. EASY. hyp: none.

**XD.4 x2hypAssembled** — (X2-HYP), multiplied through (division-free; c₀⁺ := c0 + ccap):
```lean
theorem x2hypAssembled (I) (AF : X2Aff n I) (CP : X2Cap n I) (b) (hb : FourthPiece I b)
    (N : ℕ) (hN : N < I.threshold b + capH I b) :
    (N : ℚ) - 1 - CP.ccap < (AF.c0 + CP.ccap) * ((dTotal (I.hist b) : ℚ) + 1)^2 ∨
    (N : ℚ) - 1 - CP.ccap < (AF.c0 + CP.ccap) * (maxH (I.hist b) : ℚ)^2
```
moves_ref: "(X2-HYP) … DERIVED given (X2-AFF) ∧ (X2-CAP) … threshold(H) + cap(H) > N ⟹ Σ h_r > (N−1−c_cap)/c₀⁺ ⟹ (d_total+1)·max h > (N−1−c_cap)/c₀⁺ ⟹ [√ dichotomy]". deps: XD.1–XD.3, I.wf. sketch: N < threshold + cap ≤ 1 + ccap + (c0+ccap)·Σh (AF.bound on FourthPiece — finding 11's domain — + CP.bound via capTotal); Σh ≤ (d+1)·maxh (XD.2); XD.3-style split with c₀⁺ ≥ 0 (the nonneg fields). MEDIUM. hyp_fields: X2Aff, X2Cap (OPEN kernels, by name).

### Layer E — kernel-statement units, ONE PER KERNEL (findings 15/16 repaired)

Each unit: the Defs structure's docstring quotes its display verbatim; the unit file
re-states the structure's field as a `#check`-level elaboration test PLUS the
INHABITATION note (intended real instance + owner + wave). NO toy instances are offered
as vacuity guards (finding 15): the guard is (i) contentful fields over data — no bare
`Prop` fields remain anywhere in Defs — and (ii) the recorded inhabitation obligations,
tracked in the campaign ledger at each sync.

**XE.1a alignKernel** — `X1aAlign` elaborates; docstring = the (X1a-ALIGN) block + both sub-clauses. INHABITATION: discharge route = the D.12 dictionary (math-side, OPEN); Lean-side instance owed by nobody until the kernel closes. EASY. hyp: is the hypothesis.
**XE.1b wcT4Kernel** — `WeightChargeT4`; docstring = the boxed WEIGHT-CHARGE display restricted "to the T4 population — the one piece no ALIGN discharge ever covers". INHABITATION: math-side OPEN kernel; STALL-probe tests candidates s(3) = 2 only. EASY.
**XE.1c wcFullKernel** — `WeightChargeFull`; docstring = the boxed display, FULL burden ("T4 AND the uncertified T1 recenterings"). INHABITATION: as XE.1b. EASY.
**XE.1d x2affKernel** — `X2Aff`; docstring = the (X2-AFF) display + "Neither c₀(n)'s value NOR its existence is derived here". Domain = FourthPiece (finding 11). INHABITATION: owned by PROGRESS (OPEN); candidate c₀(3) = 4. EASY.
**XE.1e x2capKernel** — `X2Cap`; docstring = the (X2-CAP) display + level-relativity note. INHABITATION: owned by PROGRESS (OPEN); c_cap(3) UNSEALED. EASY.
**XE.1f x2bridgeKernel** — `X2Bridge` (both fields: the four-piece `decomposition` inclusion AND the a.e. `existential` conversion — finding 14). INHABITATION: owned by PROGRESS (OPEN); the `link` relation's real instance = MovesD's f-to-branch fibering, wave-4 sync. EASY.
**XE.1g x2tailsKernel** — `X2Tails` (ℝ constants, both positive — finding 12; global event, hstar-only). INHABITATION: [2b]/§H-DOMAINS-owed, discharged at [2b]'s acceptance; candidates C_T(3) = 53, c_T(3) = 1. EASY.
**XE.1h x2progressKernel** — `X2Progress` (ℚ slopes, 0 < cd/ch — finding 13: the sealed candidate c_d(3) = c_h(3) = 1/2 is now expressible). INHABITATION: THE PROGRESS kernel, math-side OPEN. EASY.

**XE.2 envelopeStatement** — statement-only def with POSITIVE decay (finding 17):
```lean
structure EnvKernels where (c3 c4 : ℝ) (c3pos : 0 < c3) (c4pos : 0 < c4)
def EnvBound (M : XMassInterface n p F A) (K : EnvKernels) : Prop :=
  ∀ N : ℕ, (M.frac (M.Undec N) : ℝ) ≤ K.c3 * (p : ℝ) ^ (-(K.c4 * N))
```
moves_ref: "env(N) ≤ c₃(n)·p^{−c₄(n)·N}, with c₃, c₄ traced to s(n) (X.1b), c₀ ((X2-AFF)), C_T, c_T ((X2-TAILS)), c_cap ((X2-CAP))" — the trace is the docstring; SQ-side consumption is MovesU's. deps: Defs. EASY (statement). hyp: EnvKernels + the full X.2 tag set at any future proof site.

### Layer F — the ELEMENTARY DISCRIMINANT TAIL (3b)

Target display: `(3b) μ{v_p(disc f) ≥ D} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉} → 0`;
corollary `μ{disc f = 0} = 0`. Lean form (finite level, INTEGER exponent — finding 20):
> `(3b-LEAN)  (tailCount p n D : ℚ) * (p : ℚ) ^ (tailExp p n D) ≤ (n − 1) * (p : ℚ) ^ (n * D : ℤ)`
with `tailExp p n D = ⌈((D : ℤ) − n·v_p(n))/(n−1)⌉ : ℤ` (zpow; negative exponents legal).
Spot checks (finding 20's counterexample class, verified): n=2, p=2, D=0: tailExp = ⌈−2/1⌉ = −2,
fraction bound (n−1)·p^{−tailExp} = 1·2² = 4 — the note's value (trivially true, NOT truncated
to 1); D=4: tailExp = 2, bound 1/4 — matches (3b); n=3, p=2: tailExp = ⌈D/2⌉ reproduces X.5(ii)'s
sealed legs 2·2^{−⌈D/2⌉}.

**XF.1 discCylinder** — typed reduction (finding 18):
```lean
theorem discCylinder (p n D : ℕ) [Fact p.Prime] (hn : 1 ≤ n) (f : Polynomial ℤ_[p])
    (hm : f.Monic) (hd : f.natDegree = n) :
    ((p : ℤ_[p]) ^ D ∣ f.discr ↔
      (polyOfCoeffs (ZMod (p ^ D)) n (fun i => PadicInt.toZModPow D (f.coeff i))).discr = 0)
```
moves_ref: (3b)'s event is coefficient-cylinder data (implicit in "union bound + Fubini" over the box). deps: Defs. sketch: `polyOfCoeffs _ n (toZModPow D ∘ f.coeff)` = `f.map (toZModPow D)` for monic deg-n f (coeff n = 1, higher coeffs 0); a `discr_map` helper for natDegree-preserving maps (dets of `sylvesterDeriv` entries commute with ring homs — Mathlib GAP flagged: no `Polynomial.discr_map` exists; proved here for the monic case); divisibility ↔ zero via `PadicInt.ker_toZModPow`. MEDIUM. hyp: none.

**XF.2 discResBridge** — `theorem discResBridge [Fact p.Prime] (f : Polynomial ℤ_[p]) (hm : f.Monic) (h1 : 0 < f.natDegree) : ‖f.discr‖ = ‖f.resultant f.derivative‖`.
moves_ref: the (3b) proof-on-record's object "Res(f, f′)" identified with disc for monic f. deps: Defs. sketch: Mathlib `Polynomial.resultant_deriv` (Res(f,f′) = (−1)^{n(n−1)/2}·lc·discr), lc = 1, ‖±x‖ = ‖x‖; degree-argument defaults handled by `hm.natDegree`-rewrites. EASY-MEDIUM. hyp: none.

**XF.3 valExtOf** — the D8 CONSTRUCTION (finding 19 resolved to this route):
```lean
noncomputable def valExtOf (p : ℕ) [Fact p.Prime] (g : Polynomial ℚ_[p]) (hg : g ≠ 0) :
    ValExt p g
```
moves_ref: none (Lemma 3.3's proof apparatus; §4 flag — must never strengthen (3b)). deps: Defs. sketch: L := g.SplittingField (finite over the complete ℚ_[p]); `spectralNorm ℚ_[p] L` is power-multiplicative, extends ‖·‖, and is MULTIPLICATIVE on a finite extension of a complete nonarchimedean field (Mathlib `SpectralNorm.lean` + the `spectralMulAlgNorm` layer); package as `AbsoluteValue`; splits by construction. HARD (Mathlib-archaeology; stuck ⟹ XF.9 alone stalls, D8's recorded fallback). hyp: none.

**XF.4 resRootSum** — the root-product valuation identity, over an explicit ValExt:
```lean
theorem resRootSum (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (f : Polynomial ℤ_[p])
    (hm : f.Monic) (hd : f.natDegree = n)
    (V : ValExt p ((f.map PadicInt.coe).derivative)) :
    ‖f.resultant f.derivative‖ =
      ‖(n : ℚ_[p])‖ ^ n *
      ((((f.map PadicInt.coe).derivative.map (algebraMap ℚ_[p] V.L)).roots).map
        (fun θ => V.w (Polynomial.aeval θ (f.map PadicInt.coe)))).prod
```
moves_ref: "Res(f, f′) over the n−1 roots of f′" with the offset n·v_p(n) ((3b)'s exponent "(D − n·v_p(n))"). deps: XF.3-independent (V explicit). sketch: push Res to ℚ_[p] then L (resultant commutes with injective natDegree-preserving maps — helper, cf. XF.1's `discr_map` gap); over L, f′ splits: Res(f, f′) = (−1)^{n(n−1)}·lc(f′)^{deg f}·Π_{f′(θ)=0} f(θ) via Mathlib's root-product lemmas (`resultant_eq_prod_roots_sub` + eval-product helpers); lc(f′) = n·1 gives ‖n‖^n; V.ext transports norms. HARD. hyp: ValExt (explicit).

**XF.5 pigeonMax** — `theorem pigeonMax (m : Multiset ℚ) (hm : m ≠ 0) (K : ℚ) (h : K ≤ m.sum) : ∃ v ∈ m, K ≤ (m.card : ℚ) * v` — max ≥ average, division-free, for the valuations vᵢ := −log_p V.w(f(θᵢ)) of the n−1 root terms.
moves_ref: "some θᵢ has v_p(f(θᵢ)) ≥ (D − n·v_p(n))/(n−1)". deps: none. sketch: if every card·v < K then sum < K; `Multiset.sum_lt_sum` style. EASY. hyp: none. AUDIT FLAG: terms may be NEGATIVE (non-integral roots); no sign hypothesis allowed.

**XF.6 ballCover** — pairwise-congruence form (centers stay in L; no ℚ_[p]-center claimed):
```lean
theorem ballCover (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n) (aTail : Fin (n - 1) → ℤ_[p])
    (V : ValExt p (fTail n aTail))   -- fTail := (the monic family's a₀-free derivative)
    : ∃ idx : ℤ_[p] → Fin (n - 1),
      ∀ a0 b0 : ℤ_[p], Event p n D aTail a0 → Event p n D aTail b0 → idx a0 = idx b0 →
        (p : ℤ_[p]) ^ (tailExp p n D).toNat ∣ (a0 - b0)
```
where `Event p n D aTail a0 := (p : ℤ_[p])^D ∣ (polyOfCoeffs ℤ_[p] n (Fin.cons a0 aTail)).discr` (Defs abbreviation; `Fin.cons` puts a₀ in slot 0).
moves_ref: "the a₀-translation, union bound + Fubini" — f(θ) = a₀ + c(θ), c a₀-independent. deps: XF.2, XF.4, XF.5. sketch: f′ is a₀-free (derivative kills the constant term); its root multiset in V.L is fixed; an event point gets, by XF.2 + XF.4 + XF.5, a root θᵢ with V.w(a₀ + c(θᵢ)) ≤ p^{−tailExp} — set idx a₀ := i; two event points at one i are both p^{−tailExp}-close to −c(θᵢ), hence to each other (ultrametric), and V.ext turns that into ℤ_[p]-divisibility (`.toNat` legal: for tailExp ≤ 0 the divisibility is trivial, p⁰ = 1). MEDIUM-HARD. hyp: ValExt (explicit).

**XF.7 tailCountBound** — (3b-LEAN), the note's INTEGER exponent (finding 20 repaired):
```lean
theorem tailCountBound (p n D : ℕ) [Fact p.Prime] (h2 : 2 ≤ n)
    (V : ∀ aTail : Fin (n - 1) → ℤ_[p], ValExt p (fTail n aTail)) :
    (tailCount p n D : ℚ) * (p : ℚ) ^ (tailExp p n D) ≤ (n - 1 : ℚ) * (p : ℚ) ^ ((n * D : ℕ) : ℤ)
```
moves_ref: "(3b) μ{f monic deg n : v_p(disc f) ≥ D} ≤ (n−1)·p^{−⌈(D − n·v_p(n))/(n−1)⌉}". deps: XF.1, XF.6. sketch: fiber tailCount over aTail ∈ (ZMod p^D)^{n−1}, lifting fibers via XF.1; XF.6's congruence caps each fiber at (n−1)·p^{D−tailExp.toNat} residues; when tailExp ≤ 0 the claim is the trivial box bound (spot check n=2, p=2, D=0: LHS = 1·2^{−2} = 1/4 ≤ 1·2⁰ = 1; the fraction reading gives the note's 4). Sum over p^{(n−1)D} tails; `Nat.card` fiber arithmetic (MovesC M4 pattern). MEDIUM-HARD. hyp: ValExt family (explicit; discharged by XF.9).

**XF.8 tailZero** — the formal limit (finding 21: limit and null-locus now SEPARATE units):
```lean
theorem tailZero (p n : ℕ) [Fact p.Prime] (h2 : 2 ≤ n)
    (V : ∀ aTail : Fin (n - 1) → ℤ_[p], ValExt p (fTail n aTail)) :
    Filter.Tendsto (fun D => (tailCount p n D : ℚ) / (p : ℚ) ^ (n * D)) Filter.atTop (nhds 0)
```
moves_ref: "→ 0 as D → ∞". deps: XF.7. sketch: fraction ≤ (n−1)·p^{−tailExp p n D}; tailExp → ∞ linearly in D; geometric squeeze. MEDIUM. hyp: ValExt family.

**XF.9 tailUnconditional** — the D8 wrapper (finding 19's resolution): `theorem tailUnconditional … : same statements as XF.7 + XF.8 with the V argument DISCHARGED by valExtOf` (the derivative is nonzero: monic deg n ≥ 2, char 0).
moves_ref: (3b) verbatim, now unconditional. deps: XF.3, XF.7, XF.8. sketch: apply. EASY (given deps; carries XF.3's stuck-risk). hyp: none.

**XF.10 discZeroNull** — the corollary, formal (finding 21):
```lean
theorem discZeroNull (M : XMassInterface n p F A) [Fact p.Prime] (h2 : 2 ≤ n)
    (V : ∀ aTail : Fin (n - 1) → ℤ_[p], ValExt p (fTail n aTail)) :
    M.frac A.discZero = 0
```
moves_ref: "corollary μ{disc f = 0} = 0". deps: XF.8. sketch: `M.discZero_le_tail` (the interface's cylinder-inclusion field, §4) bounds frac discZero by every tail fraction; XF.8 + `M.frac_nonneg` squeeze to 0 (`le_of_tendsto` + antisymm). EASY-MEDIUM. hyp: XMassInterface (accepted/owed link field), ValExt family.

### Layer G — X.3's qualitative assembly (DERIVED; findings 22/23/24/25 repaired)

**XG.1 branchLenBound** — the CLEARED display, identical on both routes (finding 22):
```lean
theorem branchLenBound (A : IndexApparatus n p F) (R : X3aRoute n p F A)
    (f H) (hf : A.inStratum f H) (hd : f ∉ A.discZero) (W : HistWF n H) (hn : 1 ≤ n) :
    2 * dTotal H ≤ (2 * R.s + 1) * A.vdisc f + 2 * Nat.log 2 n
```
moves_ref: X.3(a) "EITHER route gives every branch finite pointwise, by the four-population decomposition …: (a1) … OR (a2) …" — the bound is XC.3/XC.4's cleared form `2·d_total ≤ (2s+1)·v_p(disc f) + 2·⌊log₂ n⌋`. deps: XC.3, XC.4. sketch: case on R: a1 ↦ XC.4's second conjunct; a2 ↦ XC.3. EASY (glue). hyp_fields: X3aRoute (both disjuncts carry X.1b's T4 leg — "NO route avoids X.1b") + HistWF.

**XG.2 koenigFinite** — the tree-finite bridge, over the rooted forest (finding 23):
```lean
theorem koenigFinite (I : XTreeInterface n) (B : ℕ)
    (hlen : ∀ b : I.Branch, (I.hist b).length ≤ B) : Finite I.Branch
```
moves_ref: "TREE-FINITE BRIDGE [rev 2, finding 12]: T_can(f) is FINITELY BRANCHING — … §M-SPECIES' finite letter menus — so König's lemma upgrades 'every branch finite' to 'T_can(f) finite'". deps: Defs. sketch: `parent_hist` makes hist-length strictly decrease along `parent`; `reach` puts every b on a parent-chain to root; induction on B over the level sets Lev k := {b | (I.hist b).length = k}: Lev 0 ⊆ {root} (length-0 ⟹ parent none via parent_hist ⟹ reach forces b = root), Lev (k+1) ⊆ ⋃_{b ∈ Lev k} children b (`children_iff`), each a `Finset` — finite union of finites. NOTE (audit-visible): this is the BOUNDED-DEPTH form — XG.1 supplies a uniform per-f bound, so no infinite-path compactness is invoked; a premise-weaker USE of the note's König citation, not a statement change. MEDIUM-HARD. hyp: XTreeInterface (finite menus = MovesSp-owed field). CONSUMER: the wave-4 discharge of `detectInter` (MovesD/MovesT), where branch-finiteness feeds detection — recorded so the unit is not an orphan.

**XG.3 x3Density** — the conditional theorem, conclusion DERIVED (finding 24: `MassLink` deleted; every input is a note-listed tag or an accepted/owed interface field):
```lean
theorem x3Density (A : IndexApparatus n p F) (M : XMassInterface n p F A)
    [Fact p.Prime] (h2 : 2 ≤ n)
    (R : X3aRoute n p F A)                     -- [(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)]
    (hns : NsNull M)                            -- (ns-null) tag, displayed (closed at [3t])
    (V : ∀ aTail : Fin (n - 1) → ℤ_[p], ValExt p (fTail n aTail)) :
    Filter.Tendsto (fun N => M.frac (M.Undec N)) Filter.atTop (nhds 0)
```
moves_ref: "(X.3) … the undecided complement has mass 0; equivalently μ(Undec(N)) → 0" + CONDITIONALITY SUMMARY "X.3 = [routes] + (ns-null, closed, tag displayed) + accepted perimeter (3.2/3.3/Thm 2.1, TB-CAP, König, VP-SOUND …)". deps: XG.1, XF.10, XD.1. sketch (each note step to its input): (a) infBranch ⊆ A.discZero — pointwise: f ∈ infBranch gives arbitrarily long stratified WF histories (`M.stratumLink`, §D4-R prefix fact), contradicting XG.1's bound off discZero; (c) frac (⋃ nsFiber) = 0 — `nsCountable` + `hns` + `frac_iUnion_null`; (b)+(d): `M.detectInter` (TB-CAP trichotomy + Thm 2.1 detection, MovesD/T-owed field) gives ⋂ Undec ⊆ infBranch ∪ ⋃ns ∪ discZero, so frac (⋂ Undec) = 0 by `frac_mono`/`frac_union_le` + XF.10; `undec_antitone` + `frac_inter_tendsto` (monotone convergence, owed field) close the limit. MEDIUM-HARD. hyp_fields: X3aRoute, NsNull (tag), ValExt family, XMassInterface's accepted/owed fields (detectInter, stratumLink, frac laws, frac_inter_tendsto, discZero_le_tail) — one-to-one against the note's tag list in §4; VP-SOUND is NOT consumed here (it belongs to the series clause — note finding 13).

**XG.4 x3Series** — the per-σ series identity as a THEOREM (finding 25), with the note's proof sketch and an explicit deferral clause:
```lean
theorem x3Series (A : IndexApparatus n p F) (M : XMassInterface n p F A)
    (S : SeriesData n p F) (VP : VPSound n p F S)
    (hpart : ∀ T T', T ≠ T' → Disjoint (S.fiber T) (S.fiber T'))
    (hσ : ∀ σ, M.frac {f | f ∈ ⋃ T ∈ {T | S.trueTypeOf T = σ}, S.fiber T} = S.densityσ σ)
    (hadd : CountableFiberAdditive M S)        -- (3e)-regrouping/Tonelli field, MovesD/T-owed
    (hx3 : Filter.Tendsto (fun N => M.frac (M.Undec N)) Filter.atTop (nhds 0)) (σ) :
    HasSum (fun T : {T // S.typemult T = σ} => M.frac (S.fiber T)) (S.densityσ σ)
```
moves_ref: "for each type σ the tree-fiber series sums the full density: Σ_{T ∈ 𝒯^fin …, typemult(T) = σ} μ{f : T_can^τ(f) = T} = density_σ(p), with the 𝒯^ns fibers' total contribution dropped as 0 [(ns-null) tag]" + "(3e)-style regrouping (Tonelli, positive terms) yields the per-σ series identity". deps: XG.3 (supplies hx3). sketch (the note's): decided mass fills to densityσ as N → ∞ (hx3 + hσ); the decided set partitions into countably many tree fibers (hpart, treeCountable); positive-term regrouping (`hadd`, the Tonelli field) turns the monotone fill into `HasSum`; `VP.typeFaithful` converts the typemult-indexed family to the trueType-indexed one — exactly where VP-SOUND is inherited (note finding 13). DEFERRAL CLAUSE: if `CountableFiberAdditive`'s typing is contested at the MovesD/MovesT sync, this unit DEFERS to wave 4 with the statement frozen — the deferral is the recorded alternative, not silence. MEDIUM-HARD. hyp_fields: VPSound (restored tag), NsNull via hx3's provenance, the two owed measure fields (hσ definitional at sync; hadd Tonelli).

(Defs postscript: `CountableFiberAdditive M S` — the (3e)/Tonelli positive-term
regrouping field consumed only by XG.4 — is a Defs §H structure: countable additivity of
`M.frac` on disjoint families of tree fibers. MovesD/MovesT-owed; §4.)

---

## 4. Audit table (trust surface for the Codex semantic gate)

| object | note display it must match | class |
|---|---|---|
| `p1Region`'s `≤` (on-or-below) | (P1)/Remark 4.14 pin; strictly-below would zero every e = 1 event | DEF — sharpest trap |
| `rowOf`, `XNode` coherence (`t2inc`/`t3inc`/`t4rec`) | table rows T1–T5; T2/T3 "(increment…)", T4 "recenterings" | DEF (coherence MovesSp-discharged at sync) |
| `ind2` + XA.9 EQUALITY | (IND) doubled; finding-1 semantics in T3/T4 docstrings | DEF+THM |
| `certified`/`dCert`/`DescX` | (CD) verbatim; Desc_d "keyed here by d_cert per (CD)" | DEF |
| `HistWF` (termLast, degProd) | §D4-R branch shape; §B2-DEF "Π e_i ≤ n along a branch" | IF (ACCEPTED-source; discharge `MovesSp.termLast`/`degProd_le`) |
| `X1aAlign.transport` | X.1a assembly conclusion "ind(f) ≥ d_cert(H) for EACH branch" | HYP (kernel) |
| `WeightChargeT4/Full` | the boxed WEIGHT-CHARGE display; T4 vs FULL burden (rev 3) | HYP (kernels) |
| `X2Aff` (FourthPiece domain), `X2Cap`, `X2Progress` (ℚ, 0 < slopes), `X2Tails` (ℝ, > 0), `X2Bridge` (both clauses) | their displays verbatim; NONNEG normalizations on c0/ccap are WLOG-safe (Σh, cap ≥ 0) — flagged for the auditor's sign-off | HYP (kernels) |
| `X2Progress` p-freeness | "n-only, p-free" — recorded; enforced at instance time (per-(n,p) structure) | HYP + design note |
| `NsFree`/`FourthPiece` (prefix clause)/`capH`/`maxH ∅ = 0` | X.2 DOMAIN CONVENTIONS rev 4/5; "finite branch or prefix of a complete τ-halted tree" | DEF |
| `XTreeInterface` (rooted forest, Finset children, reach) | §D4-R T_can + §M-SPECIES finite menus | IF (owner MovesD, wave-4 sync; PrefFamily precedent) |
| `XMassInterface` content laws + `frac_inter_tendsto` | box mass; Thm 2.1 N-stability; monotone convergence | IF (owner MovesD/MovesT, wave-4 sync) |
| `stratumLink` | §D4-R: an infinite branch has arbitrarily long finite prefixes, each a stratified history | IF (owed; wave-4) |
| `detectInter` | X.3(b) + (d): "detection fails at all N only on the (τ-ns) class" + TB-CAP trichotomy | IF (owed; wave-4 — the ONE field carrying X.3(b)) |
| `nsInUndec`, `nsIdx` countable | (NS-d); "𝒯^ns is COUNTABLE ((NS-c))" | IF (owed) |
| `discZero_le_tail` | discZero lies in every level-D disc-vanishing cylinder (definitional at sync) | IF (owed) |
| `tailCount`/`tailExp` + (3b-LEAN) | Lemma 3.3's (3b); INTEGER exponent, spot-checked n=2,p=2,D=0→4 and D=4→1/4 | DEF+THM |
| `ValExt`/`valExtOf` | not a note object (proof apparatus); must never strengthen (3b) | IF→CONSTRUCTED (D8) |
| `IndexApparatus` | (P2) + Thm 4.18(1) via D.12 (GMN pins); real instance MovesD/HC-2 | IF (published) |
| `X3aRoute` | "[(X1a-ALIGN) ∧ X.1b(T4)] ∨ [(ALIGN-inc) ∧ X.1b(full)]" | DEF (tag) |
| `NsNull`, `VPSound`, `SeriesData`, `CountableFiberAdditive` | (ns-null) tag; VP-SOUND = (HEN-LIFT)/(OM-SAT) at the typemult identification; (3e)/Tonelli | HYP tags + IF (owed) |

INHABITATION LEDGER (finding 15): every structure above carries its intended real
instance + owner in its unit's INHABITATION note; obligations tracked at each sync
round in the campaign ledger. No bare `Prop` field remains in Defs.

## 5. Census and counts

**45 units.** EASY 21 (XA.1–4, XA.8; XB.1; XC.2; XD.1, XD.3; XE.1a–h, XE.2; XF.5, XF.9;
XG.1) · MEDIUM 15 (XA.5, XA.7b, XA.9; XB.2–4; XC.1, XC.3, XC.4; XD.2, XD.4; XF.1, XF.2,
XF.8, XF.10) · HARD 9 (XA.6, XA.7a — lattice counts; XF.3, XF.4 — ValExt/Mathlib
archaeology; XF.6, XF.7 — covering/Fubini; XG.2, XG.3, XG.4 — assembly, scored
medium-hard). Escalation-risk set = the 9 HARD ids; XG.4 carries an explicit wave-4
deferral clause. Sealed-gate X.5 layers = runtime artifacts, out of corpus. NOT
formalized (OPEN upstream): the X.1b/X.2 kernel derivations, the STALL-probe,
(X2-TAILS)'s derivation, the envelope's SQ-side consumption — matching X.4's perimeter.

## 6. Findings→repairs table (audit `MOVESX_AUDIT_CODEX_2026-07-28.md`, all 25)

| # | class | unit | repair |
|---|---|---|---|
| 1 | GAP | XA.1 | FIXED: five explicit iffs, no ellipsis, ℓ = 1 edge cases stated |
| 2 | GAP | XA.7 | SPLIT: XA.7a (column-block partition) + XA.7b (arithmetic assembly) |
| 3 | CRIT | XA.9 | FIXED: `ind2 ν = 2·card` EQUALITY per row (was ≤) |
| 4 | GAP | XB.3 | FIXED: `t2inc`/`t3inc`/`t4rec` coherence fields added to `XNode` |
| 5 | CRIT | XB.4 | REDESIGNED: exponential step proved in-unit; only accepted Πe ≤ n rides (`HistWF.degProd`, MovesSp-discharged) |
| 6 | CRIT | XC.1 | FIXED: full two-inclusion chain with formalized `DescX` |
| 7 | CRIT | XC.2 | FIXED: same chain at ⟨false,false⟩ — nothing deleted |
| 8 | CRIT | XD.2 | FIXED: unconditional (empty case via maxH ∅ = 0, both sides 0) |
| 9 | GAP | XD.2 | FIXED: `HistWF.termLast` field added to Defs |
| 10 | GAP | FourthPiece | FIXED: explicit `isPrefix` + `complete`; "branch or prefix" verbatim |
| 11 | CRIT | X2Aff | FIXED: quantifier restricted to FourthPiece |
| 12 | CRIT | X2Tails | FIXED: ℝ constants, both > 0; global hstar-only event |
| 13 | CRIT | X2Progress | FIXED: ℚ slopes, 0 < cd/ch — candidate 1/2 expressible; ℚ-form inequality |
| 14 | GAP | X2Bridge | FIXED: both clauses (`decomposition`, `existential`) as fields |
| 15 | CRIT | XE.1 | REDESIGNED: contentful fields everywhere (no bare Props); per-structure INHABITATION notes (owner + instance); toy instances dropped |
| 16 | GAP | XE.1 | SPLIT: XE.1a–XE.1h, one kernel per unit |
| 17 | CRIT | XE.2 | FIXED: `c4pos : 0 < c4` (and c3pos) explicit |
| 18 | GAP | XF.1 | FIXED: typed via `PadicInt.toZModPow`; `discr_map` gap flagged |
| 19 | GAP | XF.3 | REDESIGNED: D8 records the CONSTRUCTION route; explicit-V arguments downstream; XF.9 wrapper isolates the risk |
| 20 | CRIT | XF.7 | FIXED: `tailExp : ℤ` (integer subtraction, zpow); spot-checked n=2,p=2,D=0 → note bound 4, D=4 → 1/4; all inequality units re-checked digit-by-digit |
| 21 | GAP | XF.8 | SPLIT+FIXED: XF.8 formal limit; XF.10 formal `discZeroNull` over the interface |
| 22 | CRIT | XG.1 | FIXED: cleared display `2·dTotal ≤ (2s+1)·vdisc + 2·log₂ n` (matches XC.3/XC.4) |
| 23 | GAP | XG.2 | REDESIGNED: rooted-forest `XTreeInterface` (root/parent/children/reach); bounded-depth proof; premise-weaker König use flagged in-unit |
| 24 | CRIT | XG.3 | REDESIGNED: `MassLink` DELETED; conclusion derived from note-cited fields (stratumLink, detectInter, content laws, monotone convergence, XF.10); tags restored |
| 25 | CRIT | XG.4 | FIXED: theorem with the note's Tonelli sketch; VPSound + (ns-null) provenance restored as hypotheses; explicit wave-4 deferral clause |
