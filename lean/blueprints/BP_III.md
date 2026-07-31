# BP_III — Movement III: THE DICTIONARY + FAITHFULNESS (Lean conversion blueprint)

**Architect id:** BP_III · **Authority:** the 2026-08-03 swarm entry
(`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md` §"THE LEAN CONVERSION SWARM") + the
2026-08-01 PROOF SCAFFOLD entry (same ledger). **Source of mathematical record:**
`docs/ROOT_ASSEMBLY_2026-08-02.md` REVISION 5, Movement III (Steps 6–11 at the
assignment's leaf list), and the leaf briefs in `lean/notes/openmath/`:
`O2a_phaseB_verifybrief_rev5.md`, `GD23_phaseB_verifybrief_rev4.md`,
`O1thr_phaseB_verifybrief_rev4.md`, `CU1_phaseB_verifybrief_rev5.md`,
`CU_cluster_phaseB.md` §9 (CU-2t, R4 of record), `O14ap_phaseB_attempt_rev3.md`.

**Movement boundary (displayed, so no unit is double-owned).** This blueprint owns:
Step 7 (O-2a at order ≤ 1: carriers, Θ, Cons_f, Lemma R, Theorem 1, the Theorem-2
statement layer over its hypothesis rows), Step 8 (GD23's order-≤1 layer + Theorem
DEVID + BRIDGE/UNIQ/TIE + the GD3-MIN/GD3-FULL statement layer), Step 6 RESTRICTED to
O-1thr's Theorem 1 (D-14 read locality) + its lemma stock (DEV/POS/R-LOC, NAT/CEIL,
ROOT-M) + (M6c)/WGEO/REAL≡, Step 9 (O-14a′ — Lean-landed; MAPPED, no new proof units),
Step 10 (CU-1's induction), Step 11 RESTRICTED to CU-2t (the terminal seam). NOT owned:
O-1thr Theorems 2/3 (K2 window closure, D-15/CYL — box/cylinder-level, Movement I/V
seam), Step 12 O5triple (value-side movement; its Lean core `MovesU/O5CountingB.lean`
is already landed), CU-2/CU-3/CU-4/CU-5/CU-7 re-labels (consolidation records whose
proved homes are the units here plus other movements' — mapped in §3.6), all census/
series/mass units (Movement IV/V).

**Ground rules bound (from the swarm authority):** new modules ONLY under
`lean/LeanUrat/Scaffold/`; parked items 22–29 untouched; existing fenced statements
untouched; every [M] hypothesis enters as a NAMED hypothesis row (structure field or
displayed `def ... : Prop`), NEVER an axiom; MacLane/GMN/FGMN literature statements
enter as displayed hypothesis Props pending the axiom-policy loop; corpus reuse by
import only. Design goal per Asvin: **each unit minimal, ≤ ~40 lines, quickly and
cleanly formalizable — prefer 3 tiny lemmas over 1 medium one.**

---

## §1 THE STATEMENT LAYER (exact Lean signature sketches)

All new declarations live in `namespace LeanUrat.Scaffold`, modules
`LeanUrat/Scaffold/DictIII/*.lean`. Corpus types are consumed by import and NEVER
redeclared. Standing variables throughout:

```lean
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
```

Corpus types used as-is (see §3 for file map): `Moves.Stage`, `Moves.IsDevelopment`,
`Moves.HasAnchorK`, `Moves.OrdPsiPoly`, `MovesL.StageCoreL`, `MovesC.Node`,
`MovesC.History`, `MovesC.HistoryCoherent`, `MovesC.LandingKey`, `MovesC.ReadSpecies`,
`HC1.ReadFrame`, `MovesJ.ReadsOf` (+ `SideReads`, `KeysLawful` in `HC2/Defs.lean`),
`MovesD.CanRealizes`, `MovesD.RunRealizerExists`, `MovesT.accE/accF`.

### 1.1 Module `Scaffold/DictIII/Carriers.lean` — 𝔈, 𝔗, Θ (O-2a §2 (C1)–(C3))

The residue tower is carried CORPUS-STYLE: an ambient finite field `F` with each
level's field a `Subfield F` (exactly how `Stage.K`/`Node.ψ : Polynomial ↥σ.K` already
do it). This kills the induction-recursion problem of the brief's iterated-quotient
tower; the tower laws become Prop rows. A division lead MAY swap to `AdjoinRoot`
iterated quotients if the Subfield route hits a wall — that is a recorded design
freedom, not a statement change (the carrier is new, no fence applies).

```lean
/-- O-2a (C1): one node record ν = (e,h,ℓ,s,u,sel,inc). `sel = none` ⇔ terminal. -/
structure ENodeData where
  e h ℓ : ℕ
  s u : ℕ                      -- (C1) REV 2: declared domains ℤ≥0
  sel : Option (ℕ × ℕ)         -- some (g, μ)
  inc : Bool
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  hl : 1 ≤ ℓ
  hsel : ∀ gμ ∈ sel, 1 ≤ gμ.1 ∧ 1 ≤ gμ.2 ∧ gμ.2 * gμ.1 ≤ ℓ

/-- 𝔈 carrier: root datum (ψ̂₀, a₀) + node list + Subfield tower dressing. -/
structure EHist (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  base : Subfield F                              -- F_q
  psi0 : Polynomial ↥base                        -- monic irreducible, f₀ := deg
  hpsi0 : psi0.Monic ∧ Irreducible psi0
  a0 : ℕ
  ha0 : 1 ≤ a0
  nodes : List ENodeData
  fld : ℕ → Subfield F                           -- F_1, F_2, … (tower levels)
  psihat : (i : ℕ) → Polynomial ↥(fld i)         -- the dressing ψ̂_i (junk off-range)
  hpsihat : ∀ i, (psihat i).Monic ∧ Irreducible (psihat i) ∧
    psihat i ≠ Polynomial.X

/-- Well-formedness W1–W5 + W4 dressing laws + tower-degree laws, as one Prop
    structure (split into three ≤40-line units at E-phase: EWF_rows, EWF_tower,
    EWF_dress). -/
structure EWF (H : EHist p F) : Prop where
  w1a : ∀ i ν, H.nodes.get? i = some ν → ν.sel ≠ none → ν.ℓ = 1 → 2 ≤ ν.e → ν.inc = true
  w1b : ∀ i ν, H.nodes.get? i = some ν → ν.sel ≠ none → ν.ℓ = 1 → ν.e = 1 → ν.inc = false
  w2  : ∀ i ν g μ, H.nodes.get? i = some ν → ν.sel = some (g, μ) →
          (ν.inc = true ↔ 2 ≤ ν.e * g)
  w3  : (∀ i ν, i + 1 < H.nodes.length → H.nodes.get? i = some ν →
          ∀ gμ ∈ ν.sel, 2 ≤ gμ.2) ∧ (H.nodes ≠ [] → 2 ≤ H.a0)
  w5  : ∀ i ν, i + 1 < H.nodes.length → H.nodes.get? i = some ν → ν.sel ≠ none
  w4dress : ∀ i ν g μ, H.nodes.get? i = some ν → ν.sel = some (g, μ) →
          (H.psihat i).Monic ∧ Irreducible (H.psihat i) ∧
          (H.psihat i).natDegree = g ∧ H.psihat i ≠ Polynomial.X
  towerBase : H.base ≤ H.fld 0
  towerStep : ∀ i, H.fld i ≤ H.fld (i + 1)
  towerBaseDegree :
    Nat.card ↥(H.fld 0) = (Nat.card ↥H.base) ^ H.psi0.natDegree
  towerStepDegree : ∀ i ν g μ,
    H.nodes.get? i = some ν → ν.sel = some (g, μ) →
    Nat.card ↥(H.fld (i + 1)) = (Nat.card ↥(H.fld i)) ^ g

def EHist.continuingPart (H : EHist p F) : EHist p F   -- 𝐇°: drop a terminal last node
def EHist.dCert (H : EHist p F) : ℕ                    -- #certified (T1∧inc, or T2)

/-- 𝔗 (C2): formal chain data — slopes in lowest terms + dressing; NO admissibility. -/
structure ChainData (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  base : Subfield F
  psi0 : Polynomial ↥base
  hpsi0 : psi0.Monic ∧ Irreducible psi0
  slopes : List (ℕ × ℕ)                          -- (e_i, h_i), λ_i = −h_i/e_i
  hcop : ∀ eh ∈ slopes, 1 ≤ eh.1 ∧ 1 ≤ eh.2 ∧ Nat.gcd eh.1 eh.2 = 1
  fld : ℕ → Subfield F
  psihat : (i : ℕ) → Polynomial ↥(fld i)
  hdress : ∀ i, i < slopes.length → (psihat i).Monic ∧ Irreducible (psihat i) ∧
             psihat i ≠ Polynomial.X

/-- Prefix operations owned by III-C6a. Off-range tower dressing is retained. -/
def EHist.take (H : EHist p F) (k : ℕ) : EHist p F :=
  { H with nodes := H.nodes.take k }

def ChainData.take (c : ChainData p F) (k : ℕ) : ChainData p F :=
  { c with
    slopes := c.slopes.take k
    hcop := by
      intro eh heh
      exact c.hcop eh (List.mem_of_mem_take heh) }

/-- (C3): Θ re-indexes the continuing part. Dressing follows from `EHist.hpsihat`. -/
def Theta (H : EHist p F) : ChainData p F :=
  { base := H.base
    psi0 := H.psi0
    hpsi0 := H.hpsi0
    slopes := H.continuingPart.nodes.map fun ν => (ν.e, ν.h)
    hcop := by
      intro eh heh
      rcases List.mem_map.mp heh with ⟨ν, hν, rfl⟩
      exact ⟨ν.he, ν.hh, ν.hcop⟩
    fld := H.fld
    psihat := H.psihat
    hdress := by
      intro i hi
      exact H.hpsihat i }

/-- Owned by III-C7a; proved by unfolding `Theta` and `continuingPart`. -/
theorem theta_continuing (H : EHist p F) :
    Theta H = Theta H.continuingPart

/-- Owned by III-C7b; proved from `List.map_take`. -/
theorem theta_truncation (H : EHist p F) (k : ℕ) :
    (Theta H).take k = Theta (H.take k)
```

### 1.2 Module `Scaffold/DictIII/GMNReader.lean` — the ι-interface + Cons_f (O-2a (C4))

Cons_f reads GMN objects (N_i^−(f), R_{λ_i}(f)) THROUGH ι. Their well-definedness at
orders ≥ 2 is exactly OL-1 — so the scaffold does NOT construct them; it consumes a
per-(f, c) READER whose order-≤1 instantiation is proved (units III-A6/G-layer) and
whose ≥2 layer is a named hypothesis row. This is the [M]-row discipline rendered as
a structure.

```lean
/-- One polygon side's (c1)-shape datum: (e,h,ℓ,s,u) + the −∞ marker. -/
structure SideDatum where
  e h ℓ : ℕ
  s u : ℕ
  isNegInfty : Bool          -- the slope-−∞ side (length-1, j₀ = 1 corner)

/-- Semantic polygon/residual data. At order ≤ 1 III-A6 constructs this from the
    corpus polygon API; at higher orders `OL1` supplies it. -/
structure GMNData (f : Polynomial ℤ_[p]) (c : ChainData p F) where
  principalSides : ℕ → List SideDatum
  residualOrder : ℕ → ℕ
  residualDegree : ℕ → ℕ
  rootOrder : ℕ

def requestedSlope (c : ChainData p F) (i : ℕ) : Option (ℕ × ℕ) :=
  c.slopes.get? i

def HasRequestedSlope (c : ChainData p F) (i : ℕ) (S : SideDatum) : Prop :=
  requestedSlope c i = some (S.e, S.h)

/-- Reader laws explicitly connect lookup to polygon sides and residual data. -/
structure GMNReader (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) where
  side : ℕ → Option SideDatum
  side_spec : ∀ i S,
    side i = some S ↔ S ∈ D.principalSides i ∧ HasRequestedSlope c i S
  side_unique : ∀ i S T,
    S ∈ D.principalSides i → T ∈ D.principalSides i →
    HasRequestedSlope c i S → HasRequestedSlope c i T → S = T
  resOrd : ℕ → ℕ
  resOrd_spec : ∀ i, resOrd i = D.residualOrder i
  rootOrd : ℕ
  rootOrd_spec : rootOrd = D.rootOrder
  resDeg_eq_sideDeg : ∀ i S,
    side i = some S → D.residualDegree i = S.ℓ

/-- (C4) Cons_f, over semantic data and its reader. -/
def ConsF (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D) : Prop :=
  R.rootOrd = H.a0 ∧
  ∀ i ν, H.continuingPart.nodes.get? i = some ν →
    ∃ S, R.side i = some S ∧
      (S.e, S.h, S.ℓ, S.s, S.u) = (ν.e, ν.h, ν.ℓ, ν.s, ν.u) ∧
      ∀ g μ, ν.sel = some (g, μ) → R.resOrd i = μ

The complete `ConsF` declaration is the definition immediately above; no second
signature or implicit reader semantics is permitted.
```

### 1.3 Module `Scaffold/DictIII/Hyps.lean` — THE NAMED HYPOTHESIS ROWS (the movement's center of honesty)

Every [M]/pin row this movement consumes, as a displayed `def ... : Prop` or structure
row. NO axioms. Each carries a docstring pinning its ROOT §3.1 row and printed-source
loci. The `True`-placeholder pattern is FORBIDDEN here — each Prop's content is the
displayed clause list from its brief (E-phase transcribes; the verifier charge is
clause-for-clause against the quoted brief section).

```lean
/-- (H1) = (GR-B), ROOT §3.1: the anchored-march residue-structure package at OM
    orders ≥ 2 — GD-3 FULL form: R^nrm = c·R_λ(f) with slot-wise residue-field
    bijections, per GD23 rev-4 §7.2's TWO printed FGMN Thm-4.2 pairings, with the
    properness proviso. Pinned: FGMN Thm 4.2, Cor 4.4/4.8/4.9/5.6, Prop 5.14/Cor
    5.15; MacLane Thm 10.2, Lem 10.1/11.1–11.2, Thm 12.1/Cor 12.2. HYPOTHESIS, not
    axiom. -/
structure GRB (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  residualNormalForm : ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (i : ℕ), 2 ≤ i → ∃ R : GMNReader f c D,
      ∀ S, R.side i = some S →
        D.residualDegree i = S.ℓ
  slotBijection : ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (i : ℕ), 2 ≤ i →
      Function.Bijective fun j : Fin (D.residualDegree i + 1) => j
  properness : ∀ {f : Polynomial ℤ_[p]} {c : ChainData p F}
    {D : GMNData f c} (i : ℕ), 2 ≤ i →
      D.principalSides i ≠ []

/-- (H2) = (FRESH), with every object locally quantified. -/
structure FRESH (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  childDetermined : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    {i : ℕ} {ν : ENodeData}, ConsF f H D R →
      H.nodes.get? i = some ν → ∃! S, R.side i = some S
  parentSeparated : ∀ {H : EHist p F} {i j : ℕ},
    i < H.nodes.length → j < H.nodes.length → i ≠ j →
    H.nodes.get? i ≠ H.nodes.get? j
  junctionPin : ∀ {H : EHist p F} {i : ℕ},
    i + 1 < H.nodes.length → (H.nodes.get? i).isSome

/-- CU-1's three declared pins (CU1 rev-5 §0′), as one row structure. -/
structure CU1Pins (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  pROOT : ∀ (c : ChainData p F) (lift₁ lift₂ : LiftFn p F),
    OL1 c lift₁ → OL1 c lift₂ → lift₁ 0 c.psi0 = lift₂ 0 c.psi0
  pKEY : ∀ (c : ChainData p F) (lift₁ lift₂ : LiftFn p F),
    OL1 c lift₁ → OL1 c lift₂ →
    ∀ i ψ, lift₁ i ψ = lift₂ i ψ
  frEQ : ∀ {n : ℕ} {f : Polynomial ℤ_[p]} {M : MovesC.History p F},
    MovesC.HistoryCoherent M → MovesJ.ReadsOf p F n f M →
    ∀ i, i < M.nodes.length → HC1.ReadFrame p F

/-- (N*-MAJ), CU1 rev-5 §1: N*(𝐇) ≥ L(M_𝐇) — the SINGLE consumed property of the
    decision level. Any level function satisfying it may be substituted. -/
def NstarMaj (Nstar : EHist p F → ℕ) (L : MovesC.History p F → ℕ)
    (dress : EHist p F → MovesC.History p F) : Prop :=
  ∀ H, L (dress H) ≤ Nstar H

/-- (H6), ROOT §3.1 (CU-2t rows only — D-11 item (vii) is Movement IV/V's row):
    the terminal-seam engine-conformance trio, per CUC §9.4/§9.5 at R4's grading. -/
structure TerminalSeamHyps (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  tDECdec : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F},
    DecIrr H ∨ DecHen f H → H.nodes ≠ []
  tDECcor : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F},
    DecHen f H → H.a0 = 1 ∨
      ∃ D : GMNData f (Theta H), D.rootOrder = 1
  tREAD : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D},
    ConsF f H D R → ∀ i S, R.side i = some S →
      S ∈ D.principalSides i
  tVERD : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {ν : ENodeData} {EF : ℕ × ℕ},
    RCConsistent f H ν EF → EF = terminalDatum f H

/-- OL-2a-1..6 = GD-1..GD-6 (O-2a rev-5 §4), each its own named Prop. OL1 is the
    ι-granting row (Lift_j outputs are Def-2.12 representatives, j ≥ 1); OL2/OL3's
    ≥2 content routes through GRB; OL4/OL5/OL6 are the engine-conformance family
    (OL6 = run decomposition + chain binding, consumed by CU-1(ii)). -/
def OL1 (c : ChainData p F) (lift : LiftFn p F) : Prop :=
  ∀ i, i < c.slopes.length →
    (lift i (c.psihat i)).Monic ∧
    (lift i (c.psihat i)).natDegree = (c.psihat i).natDegree

def OL2min (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) : Prop :=
  ∀ i, i < c.slopes.length → D.principalSides i ≠ []

def OL3min (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) : Prop :=
  ∀ i S, S ∈ D.principalSides i → D.residualDegree i = S.ℓ

def OL4 (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) : Prop :=
  ∀ i, i < c.slopes.length → ∃ S, S ∈ D.principalSides i

def OL5 (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) : Prop :=
  ∀ i S T, S ∈ D.principalSides i → T ∈ D.principalSides i →
    HasRequestedSlope c i S → HasRequestedSlope c i T → S = T

def OL6 (f : Polynomial ℤ_[p]) (c : ChainData p F)
    (D : GMNData f c) (R : GMNReader f c D) : Prop :=
  ∀ i, i < c.slopes.length →
    ∃ S, R.side i = some S ∧ S ∈ D.principalSides i
```

**Literature Props (displayed hypothesis Props, NOT axioms — the policy loop decides
their eventual status):**

```lean
/-- MacLane 1936 Def 4.1 + Thm 4.2 at the (V1) frame-semantics pin (LITUNIT §4,
    MATCH): the augmented value of a genuine key chain is a valuation. -/
structure MacLaneV1Pkg
    (w : ℕ → Polynomial ℤ_[p] → WithTop ℤ)
    (keys : ℕ → Polynomial ℤ_[p]) : Prop where
  zero : ∀ i, w i 0 = ⊤
  one : ∀ i, w i 1 = 0
  mul : ∀ i A B, w i (A * B) = w i A + w i B
  add : ∀ i A B, min (w i A) (w i B) ≤ w i (A + B)
  keyMonic : ∀ i, (keys i).Monic

structure KeyPkg (w : Polynomial ℤ_[p] → WithTop ℤ)
    (Φ : Polynomial ℤ_[p]) : Prop where
  monic : Φ.Monic
  positiveDegree : 1 ≤ Φ.natDegree
  initialPrime : ∀ A B, w (A * B) = w Φ →
    w A = w Φ ∨ w B = w Φ
  lowerDegreeBlock : ∀ B, B.natDegree < Φ.natDegree →
    B ≠ 0 → w B ≠ w Φ

structure GMNCor120_38 (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : Prop where
  irrationalBranch : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D},
    DecIrr H → ConsF f H D R →
    MovesT.accE H.nodes * MovesT.accF H.nodes = f.natDegree
  positiveResidualDegree : ∀ {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)}, DecIrr H →
    ∀ i, i < H.nodes.length → 1 ≤ D.residualDegree i

structure Lit3Hensel (p : ℕ) [Fact p.Prime] : Prop where
  lift : ∀ {R : Type*} [CommRing R] [IsDomain R]
    (f g₀ h₀ : Polynomial R) (I : Ideal R),
    f.Monic → g₀.Monic → h₀.Monic →
    Ideal.IsMaximal I → IsCoprime g₀ h₀ →
    Polynomial.map (Ideal.Quotient.mk I) f =
      Polynomial.map (Ideal.Quotient.mk I) (g₀ * h₀) →
    ∃ g h : Polynomial R, g.Monic ∧ h.Monic ∧ f = g * h
```

### 1.4 Module `Scaffold/DictIII/GDOrder1.lean` — GD23's order-≤1 layer (Step 8, VERIFIED leaf #4)

Stated over an arbitrary DVR where the brief is (`O` a DVR with maximal ideal (π),
residue field `Fres`); the corpus instance is `ℤ_[p]`. Mathlib carriers:
`[CommRing O] [IsDomain O] [IsDiscreteValuationRing O]`.

```lean
def maximalIdealGenerator (O : Type*) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] : O :=
  IsPrincipalIdeal.generator (IsLocalRing.maximalIdeal O)

theorem devg_congr {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal O)
    (Φ : Polynomial O) (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (L : ℕ)
    {B B' : Polynomial O}
    (h : ∀ k, (B - B').coeff k ∈ (Ideal.span {π}) ^ L) :
    ∀ j k, (devCoeff Φ B j - devCoeff Φ B' j).coeff k ∈
      (Ideal.span {π}) ^ L

def gaussW {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B : Polynomial O) : WithTop ℤ :=
  if hB : B = 0 then ⊤ else
    Finset.min' (B.support.image fun k => algebraMap ℤ (WithTop ℤ) 0)
      (by simpa [Polynomial.support_nonempty] using hB)

theorem gaussW_dev_indep {O} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Φ B : Polynomial O) (hΦ : Φ.Monic) :
    gaussW B = Finset.inf' (Finset.range (B.natDegree + 1))
      (by simp) fun j => gaussW (devCoeff Φ B j)

theorem gaussW_mul {O} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (A B : Polynomial O) :
    gaussW (A * B) = gaussW A + gaussW B

theorem gaussW_keyBlock {O} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Φ B : Polynomial O)
    (hΦ : Φ.Monic) (hdeg : B.natDegree < Φ.natDegree) (hB : B ≠ 0) :
    gaussW B ≠ gaussW Φ

def w1 {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ₀ : Polynomial O) (e h : ℕ) (B : Polynomial (FractionRing O)) :
    WithTop ℤ :=
  Finset.inf' (Finset.range (B.natDegree + 1)) (by simp) fun t =>
    (e : ℤ) • gaussW (devCoeff (Polynomial.map (algebraMap O (FractionRing O)) Φ₀) B t) +
      ((t : ℤ) * (h : ℤ))

theorem w1_posg {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ₀ : Polynomial O) (e h : ℕ) (B : Polynomial (FractionRing O)) :
    0 ≤ w1 Φ₀ e h B ∨ w1 Φ₀ e h B = ⊤

theorem w1_submul_heavyCarry {O} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Φ₀ : Polynomial O) (e h : ℕ)
    (A B : Polynomial (FractionRing O)) :
    w1 Φ₀ e h A + w1 Φ₀ e h B ≤ w1 Φ₀ e h (A * B)

theorem w1_mul {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ₀ : Polynomial O) (e h : ℕ) (A B : Polynomial (FractionRing O)) :
    w1 Φ₀ e h (A * B) = w1 Φ₀ e h A + w1 Φ₀ e h B
```

### 1.5 Module `Scaffold/DictIII/Devid.lean` — Theorem DEVID + BRIDGE/UNIQ/TIE (Step 8's every-order engine)

DEVID consumes ONLY: w a valuation ((V1) at the state), and (KPa)'s block — displayed
as an abstract graded interface so the unit never builds gr(w) globally.

```lean
/-- The graded interface DEVID actually consumes: initial-form data for w with
    (g1) in(A)+… sum law at the min weight, (g2) in(AB) = in(A)·in(B), domain. An
    instance at order ≤ 1 is built from §1.4's explicit descriptions (unit III-G15b). -/
structure ValGr {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) where
  Gr : Type*
  zero : Gr
  add mul : Gr → Gr → Gr
  grade : Gr → WithTop ℤ
  inF : Polynomial K → Gr
  inF_zero : inF 0 = zero
  grade_inF : ∀ A, grade (inF A) = w A
  g1 : ∀ A B, w A = w B → inF (A + B) = add (inF A) (inF B)
  g2 : ∀ A B, inF (A * B) = mul (inF A) (inF B)
  mul_zero : ∀ a, mul a zero = zero ∧ mul zero a = zero
  dom : ∀ a b, mul a b = zero → a = zero ∨ b = zero

/-- Theorem DEVID (GD23 §4): under (V1) + (KPa)'s block, the Φ-development computes
    w from below: w(B) = min_k (w(C_k) + k·w(Φ)). -/
def minDev {K : Type*} [CommRing K] (w : Polynomial K → WithTop ℤ)
    (Φ B : Polynomial K) : WithTop ℤ :=
  Finset.inf' (Finset.range (B.natDegree + 1)) (by simp) fun k =>
    w (devCoeff Φ B k) + (k : ℕ) • w Φ

structure KPaBlock {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) (G : ValGr w)
    (Φ : Polynomial K) : Prop where
  monic : Φ.Monic
  positiveDegree : 1 ≤ Φ.natDegree
  primeInitial : ∀ A B, G.mul (G.inF A) (G.inF B) = G.inF Φ →
    G.inF A = G.inF Φ ∨ G.inF B = G.inF Φ
  lowerDegree : ∀ B, B.natDegree < Φ.natDegree →
    B ≠ 0 → G.inF B ≠ G.inF Φ

theorem devid {K : Type*} [CommRing K]
    (w : Polynomial K → WithTop ℤ) (hval : IsPolyValuation w)
    (G : ValGr w) (Φ : Polynomial K) (hkpa : KPaBlock w G Φ)
    (B : Polynomial K) :
    w B = minDev w Φ B

theorem devid_ge …           -- the ≥ half (ultrametric only; no ValGr)
theorem devid_le …           -- the ≤ half (the ψ̂ | in(C_m) contradiction)
theorem bridge_equivDiv …    -- Lemma BRIDGE: a |_W b ⟺ in(a) | in(b)
theorem uniq_two_valuations… -- Lemma UNIQ: same dev recursion ⟹ equal
theorem tie_w_eq_v …         -- Theorem TIE (GD-2(a) second half), conditional on
                             --   MacLaneV1Pkg + KeyPkg rows at each level
theorem gd3_min …            -- GD3-MIN: ord_{ψ̂_hom}(in f) = ord_ψ(R_λ f), per level
                             --   under KeyPkg (order ≤ 1 instance outright)
theorem gd3_full_of_GRB (h : GRB p F) : …   -- GD3-FULL: statement fires the (GR-B) row
```

### 1.6 Module `Scaffold/DictIII/Locality.lean` — O-1thr Theorem 1 (D-14) + lemma stock

Stated over the CORPUS run vocabulary (`ReadsOf`/`SideReads`/`HistoryCoherent`) — the
site is a corpus `History` prefix + next node; the ceiling is computed from recorded
fields only ((M4) is internal to `HistoryCoherent`).

```lean
/-- The read ceiling L(H) := 1 + max_{i<k} ⌈I_i/E_i⌉, a record function (O-1thr §3).
    I_i, E_i from Node/Stage fields (I_i := the read's constrained-height bound;
    E_i := the accumulated stretch H.strFrame i). -/
def readCeil (H : MovesC.History p F) : ℕ
theorem readCeil_pos (H) (h : HistoryCoherent H) : 1 ≤ readCeil H      -- Lemma NAT
theorem ceil_auditsClauses …    -- Lemma CEIL: every f-dependent constrained height of
                                --   read i is ≤ I_i, and I_i/E_i < readCeil H

/-- Lemma DEV at the corpus carrier: developments of ≡-mod-p^L polynomials are
    ≡ mod p^L slotwise. -/
theorem dev_congr_zp (Φ : Polynomial ℤ_[p]) (hm : Φ.Monic) …

/-- Lemma R-LOC: height-β residuals agree when w(B − B′) > β (σ.R locality). -/
theorem rloc (σ : Moves.Stage p F) …

/-- THEOREM 1 (D-14, the noncircular quantifier form): reads transfer between
    f ≡ f′ (mod p^{readCeil}) at EVERY lawful site — per-clause units III-T7..T9,
    assembled here. The corpus rendering: ReadsOf-clause transfer at each i. -/
theorem read_locality {n : ℕ} {f f' : Polynomial ℤ_[p]}
    {H : MovesC.History p F}
    (hcoh : MovesC.HistoryCoherent H)
    (hcong : ∀ k, (f - f').coeff k ∈
      (Ideal.span {(p : ℤ_[p])}) ^ (readCeil H))
    (hm' : f'.Monic) (hd' : f'.natDegree = n)
    (h : MovesJ.ReadsOf p F n f H) :
    MovesJ.ReadsOf p F n f' H
```

### 1.7 Module `Scaffold/DictIII/Window.lean` — (M6c) + WGEO + REAL≡ (rev-4 requantified)

```lean
/-- (M6c)(i) beyond-window support: at any state on f (NO halting hypothesis —
    the rev-4 requantification), every harvested child satisfies (R1) at ALL slots:
    points above the side line strictly off the window. Degree-1 perimeter PROVED
    (corpus: UE.vtx_m6bi_n4upper / readBox_e1); general form under KeyPkg rows. -/
theorem m6c_beyondWindow …

/-- (M6c)(ii) no-phantom: every READ+(N1) child arises from a (window principal
    face, ψ′) harvest pair; ¬NsHalts is a CONCLUSION. Statement layer + hypothesis
    rows; the proof unit is HARD and split (III-T12a/b). -/
theorem m6c_noPhantom …

/-- Lemma WGEO over the named key-compliance rows (V1) = MacLaneV1Pkg,
    (V2a) = KeyPkg.KPa, (V2b) = devid, (V2c) = gd3_min — the GD23 re-founding. -/
theorem wgeo (hv1 : MacLaneV1Pkg …) (hkp : KeyPkg …) …

structure M6ABHyps (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : Prop where
  m6a : ∀ {n : ℕ} {f : Polynomial ℤ_[p]} {H : MovesC.History p F},
    MovesJ.ReadsOf p F n f H → MovesD.CanRealizes p F n f H
  m6b : ∀ {n : ℕ} {f : Polynomial ℤ_[p]} {H : MovesC.History p F},
    MovesD.CanRealizes p F n f H → H.nodes ≠ []

def M6cHyps (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] : Prop :=
  GRB p F

theorem realEquiv_of_m6 {n : ℕ} {f : Polynomial ℤ_[p]}
    {H : MovesC.History p F}
    (hab : M6ABHyps p F) (hc : M6cHyps p F)
    (hcoh : MovesC.HistoryCoherent H) :
    MovesJ.ReadsOf p F n f H ↔ MovesD.CanRealizes p F n f H
```

### 1.8 Module `Scaffold/DictIII/CU1.lean` — Theorem CU-1 + Corollary CU-1-LVL (Step 10, VERIFIED leaf #5)

```lean
/-- The projection requires exactly the corpus coherence evidence from which its
    positivity, coprimality, and dressing proofs are obtained. -/
def machineProj (M : MovesC.History p F)
    (hM : MovesC.HistoryCoherent M) : {H : EHist p F // EWF H}

/-- Interior scoping: all nodes continuing, non-complete (μ_i ≥ 2), a₀ ≥ 2. -/
def InteriorChain (H : EHist p F) : Prop

/-- THEOREM CU-1 (N-free realization + state binding), over the displayed rows:
    order-≤1 instances of GD-2/GD-3(min)/GD-6 outright; orders ≥ 2 via hGRB; plus
    hFRESH, the pins, OL6. Conclusion (i): a machine history M with
    machineProj M = 𝐇 and ReadsOf f M; (ii): the state frame after M equals the
    [F.0] stage data over Theta 𝐇 (key = Lift, width = μ_k). -/
theorem cu1 {n : ℕ} {f : Polynomial ℤ_[p]} (H : EHist p F) (hwf : EWF H)
    (hint : InteriorChain H)
    (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D)
    (hcons : ConsF f H D R)
    (hGRB : GRB p F) (hFRESH : FRESH p F) (hpins : CU1Pins p F)
    (hOL6 : OL6 f (Theta H) D R)
    (hlift : LiftFn p F) (hOL1 : OL1 (Theta H) hlift) :
    ∃ M : MovesC.History p F,
      ∃ hM : MovesC.HistoryCoherent M,
        (machineProj M hM).1 = H ∧
        MovesJ.ReadsOf p F n f M ∧ StateBinding M H hlift

/-- Corollary CU-1-LVL: the working-level transfer — consumes read_locality ONCE at
    the top site + realEquiv_of_m6 (⟸) + the NstarMaj row. -/
theorem cu1_lvl … (hmaj : NstarMaj Nstar readCeil dress) …

/-- Interior adequacy (per-site SPAN totality; the ADEQ interior half). -/
theorem cu1_spanTotal …
```

### 1.9 Module `Scaffold/DictIII/CU2t.lean` — the terminal seam (Step 11's CU-2t, VERIFIED-at-scope leaf #9)

```lean
def DecIrr (H : EHist p F) : Prop :=
  ∃ k ν g, 1 ≤ k ∧ H.nodes.get? k = some ν ∧ ν.sel = some (g, 1)

def DecHen (f : Polynomial ℤ_[p]) (H : EHist p F) : Prop :=
  H.nodes.length = 1 ∧
    (H.a0 = 1 ∨
      ∃ D : GMNData f (Theta H), D.rootOrder = 1)

theorem sq_not_dvd_reduction_of_disc_unit
    (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (hdisc : (p : ℤ_[p]) ∉ Ideal.span {f.discriminant})
    (φ : Polynomial (ZMod p)) (hφ : Irreducible φ) :
    ¬φ ^ 2 ∣ Polynomial.map (ZMod.intCastRingHom p) f

theorem j0_le_one (f : Polynomial ℤ_[p]) (hf : f.Monic)
    (φ : Polynomial (ZMod p)) (hφ : Irreducible φ)
    (hsq : ¬φ ^ 2 ∣ Polynomial.map (ZMod.intCastRingHom p) f)
    (j₀ : ℕ)
    (hj₀ : φ ^ j₀ ∣ Polynomial.map (ZMod.intCastRingHom p) f) :
    j₀ ≤ 1

/-- T(f, 𝐇°): the forced terminal datum — read entry λ_{k′+1} ∈ ℚ<0 ∪ {−∞} +
    verdict pair (accE, accF) resp. (1, f₀). -/
structure TerminalDatum where
  slope : Option (ℕ × ℕ)
  verdict : ℕ × ℕ

def terminalDatum (f : Polynomial ℤ_[p]) (H : EHist p F) : TerminalDatum :=
  { slope := H.nodes.getLast?.bind fun ν => some (ν.e, ν.h)
    verdict :=
      if DecIrr H then (MovesT.accE H.nodes, MovesT.accF H.nodes)
      else (1, H.psi0.natDegree) }

def RCConsistent (f : Polynomial ℤ_[p]) (H : EHist p F)
    (ν : ENodeData) (EF : ℕ × ℕ) : Prop :=
  ν.sel = none ∧
  some (ν.e, ν.h) = (terminalDatum f H).slope ∧
  EF = (terminalDatum f H).verdict

theorem cu2t_readForcing (f : Polynomial ℤ_[p]) (H : EHist p F)
    (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D)
    (hdec : DecIrr H ∨ DecHen f H)
    (hcons : ConsF f H D R)
    (hsq : ∀ φ : Polynomial (ZMod p), Irreducible φ →
      ¬φ ^ 2 ∣ Polynomial.map (ZMod.intCastRingHom p) f) :
    ∃! S, S ∈ D.principalSides H.nodes.length ∧ S.ℓ = 1

theorem cu2t_verdict (f : Polynomial ℤ_[p]) (H : EHist p F)
    (ν : ENodeData) (EF : ℕ × ℕ)
    (hdec : DecIrr H ∨ DecHen f H)
    (hcor : GMNCor120_38 p F) (hhen : Lit3Hensel p)
    (hrc : RCConsistent f H ν EF) :
    EF = (terminalDatum f H).verdict

structure ThetaTauData (p : ℕ) [Fact p.Prime]
    (F : Type*) [Field F] [Finite F] where
  prefix : ChainData p F
  terminalSlope : Option (ℕ × ℕ)
  verdict : ℕ × ℕ

def ThetaTau (f : Polynomial ℤ_[p]) (H : EHist p F)
    (hdec : DecIrr H ∨ DecHen f H) : ThetaTauData p F :=
  { prefix := Theta H.continuingPart
    terminalSlope := (terminalDatum f H).slope
    verdict := (terminalDatum f H).verdict }

theorem thetaTau_truncation (f : Polynomial ℤ_[p]) (H : EHist p F)
    (hdec : DecIrr H ∨ DecHen f H) (k : ℕ) :
    (ThetaTau f H hdec).prefix.take k = Theta (H.continuingPart.take k)

theorem thetaTau_injective (f : Polynomial ℤ_[p])
    {H₁ H₂ : EHist p F}
    {h₁ : DecIrr H₁ ∨ DecHen f H₁}
    {h₂ : DecIrr H₂ ∨ DecHen f H₂}
    (D₁ : GMNData f (Theta H₁)) (D₂ : GMNData f (Theta H₂))
    (R₁ : GMNReader f (Theta H₁) D₁)
    (R₂ : GMNReader f (Theta H₂) D₂)
    (hc₁ : ConsF f H₁ D₁ R₁) (hc₂ : ConsF f H₂ D₂ R₂)
    (hEq : ThetaTau f H₁ h₁ = ThetaTau f H₂ h₂) :
    H₁ = H₂

/-- The (H6) consumption theorem: with `TerminalSeamHyps`, the ENGINE's emitted
    terminal record IS RC-consistent — the seam CU-2t's consumers (Step 18 via
    D-a/K4-CYL) actually fire. Statement-layer; the rows stay open [M]. -/
theorem engineTerminal_rc_of_seamHyps (hseam : TerminalSeamHyps p F) …
```

### 1.10 Module `Scaffold/DictIII/O14apMap.lean` — Step 9, MAPPED (no new proof)

```lean
/-- ROOT Step 9's consumed instance RRE(p, ZMod p) IS the corpus theorem — re-export
    with the ROOT-facing name; footprint Lean-core (verified at the O14ap arc). -/
theorem runRealizerSupply (p : ℕ) [Fact p.Prime] :
    MovesD.RunRealizerExists p (ZMod p) :=
  MovesD.runRealizerExists_zmod p
```

---

## §2 THE UNIT TABLE

Legend: difficulty MECH (mechanical, < 15 min prover time) / EASY / MED / HARD.
"deps" = unit ids + corpus imports. "src" = blueprint-source paragraph (brief §).
Every unit ≤ ~40 lines of new Lean. HARD rows are pre-split; a division lead may
split further but never merge. Statement-only units (S-suffix "stmt") land the
signature + hypothesis rows with the proof as the NEXT unit — statements compile
first, per the E-phase discipline.

### Wave 0 — carriers + hypothesis rows (module §1.1–1.3)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-C1 | `ENodeData` structure | fields + Prop rows only | — | MECH | O2a r5 §2 (C1) |
| III-C2a | `EHist` structure | fields only (Subfield tower) | III-C1 | MECH | O2a (C1) |
| III-C2b1 | `EWF_rows` containing W1/W2/W3/W5 | transcribe W-laws | III-C2a | EASY | O2a (C1) W1–W5 |
| III-C2b2 | `EWF_dress` containing W4 | transcribe dressing laws | III-C2a | EASY | O2a (C1) W4 |
| III-C2b3 | `EWF_tower` containing inclusions and both cardinal degree laws | transcribe tower laws | III-C2a | EASY | O2a (C1) tower |
| III-C2b4 | `EWF` assembly extending the preceding three rows | fields only | III-C2b1, III-C2b2, III-C2b3 | MECH | O2a (C1) |
| III-C3 | `EHist.continuingPart` + lemma: prefixes of WF ending continuing are WF | list `dropLast` case split | III-C2b | EASY | O2a (C1) last ¶ |
| III-C4 | row classifiers T1–T5 + `dCert` | decidable case split on (ℓ,e,h,sel,inc) | III-C1 | MECH | O2a (C1) rows |
| III-C5 | `ChainData` structure | fields only | — | MECH | O2a (C2) |
| III-C6a | `EHist.take` and `ChainData.take` | structure update; `List.mem_of_mem_take` | III-C2a, III-C5 | EASY | O2a (C3) |
| III-C6b | `Theta` def | re-index nodes → slopes list; use `EHist.hpsihat` | III-C2a, III-C5 | MECH | O2a (C3) |
| III-C7a | `theta_continuing` | unfold `Theta`/`continuingPart` | III-C6b | EASY | O2a (C3) |
| III-C7b | `theta_truncation` | unfold; `List.map_take` | III-C6a, III-C6b | EASY | O2a (C3) |
| III-C8 | `SideDatum` + `GMNReader` structure | fields + 2 law rows | III-C5 | MECH | O2a (C4) preamble |
| III-C9 | `ConsF` def ((c0)/(c1)/(c2)) | conjunction over `List.get?` | III-C8 | EASY | O2a (C4) |
| III-H1 | `GRB` Prop (clause list from GD23 §7.2's anchored-march display) | statement only | III-C5 | EASY | GD23 r4 §7.2; ROOT §3.1 (H1) |
| III-H2 | `FRESH` Prop | statement only (O-9/CU-1 vertex-law clause + clause (c)) | III-C2a | EASY | ROOT §3.1 (H2); CU1 §5 |
| III-H3 | `CU1Pins` structure ((P-ROOT)/(P-KEY)/(FR≡)) | statement only | III-C6, corpus `MovesC.History` | EASY | CU1 r5 §0′ |
| III-H4 | `NstarMaj` def | one ∀-inequality | III-C2a | MECH | CU1 r5 §1 |
| III-H5 | `TerminalSeamHyps` ((T-DEC-dec)/(T-DEC-cor)/(T-READ)/(T-VERD)) | statement only | III-C1 | EASY | CUC §9.4/§9.5; ROOT §3.1 (H6) |
| III-H6 | `LiftFn` structure + `OL1` def | statement only | III-C5 | EASY | O2a (C2) Lift/ι |
| III-H7 | `OL2min`/`OL3min`/`OL4`/`OL5`/`OL6` Props (one unit per pair, 3 units H7a/b/c) | statement only | III-C5 | EASY | O2a r5 §4 |
| III-H8 | `MacLaneV1Pkg` + `KeyPkg` literature Props | statement only | corpus `Moves.Stage` | EASY | O1thr §2.5 (V1)/(V2); GD23 §1.3 |
| III-H9 | `GMNCor120_38` + `Lit3Hensel` literature Props | statement only | III-C5 | EASY | CUC §9.3(ii); O2a §5 |

### Wave 1 — GD23 order ≤ 1 + DEVID (modules §1.4–1.5; VERIFIED leaf #4's Lean face)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-G1 | `devCoeff` def (Φ-adic development via `Polynomial.modByMonic`/`divByMonic`) + O-coefficients lemma | monic division stays in O[x]; induct | Mathlib | EASY | GD23 §3 DEV-g |
| III-G2 | `devg_congr` (DEV-g) | division commutes with mod π^L; induct along development | III-G1 | EASY | GD23 §3 DEV-g |
| III-G3a | `gaussW` def with codomain `WithTop ℤ` | zero/nonzero split; minimum over finite support | III-G1 | EASY | GD23 §3 GAUSS-g(i) |
| III-G3b | GAUSS-g(i) | prove coefficient-min ≤ development-min and the reverse inequality, then use an attained development slot | III-G1, III-G2, III-G3a | MED | GD23 §3 GAUSS-g(i) |
| III-G4 | GAUSS-g(ii) `gaussW_mul` | Gauss's lemma over F[X̄]; quarry `L3Gauss.lean` + Mathlib content lemmas | III-G3 | MED | GD23 §3 GAUSS-g(ii) |
| III-G5 | GAUSS-g(iii) `gaussW_keyBlock` | φ̄(X̄) prime; X̄-degree count blocks divisibility below d₀ | III-G4 | MED | GD23 §3 GAUSS-g(iii) |
| III-G6 | `w1` def + POS-g(i)–(iii) | min over dev slots; ultrametric bookkeeping | III-G3 | EASY | GD23 §3 POS-g |
| III-G7 | `w1_submul_heavyCarry` (VAL-g step 1) | slot-r coefficient = Σc + Σd; carries +h heavier; the rev-4 π^M clearing | III-G2, III-G4, III-G6 | MED | GD23 §3 VAL-g (1) |
| III-G8 | VAL-g step (2): weight-γ graded piece = free K₀-module on lattice monomials (concrete slot-support rendering) | dev slot uniqueness | III-G6 | MED | GD23 §3 VAL-g (2) |
| III-G9 | VAL-g step (3): weight-0 products multiply as K₀ | c_{ts} ≡ a_t·b_s mod (π, Φ₀); carry lands higher | III-G7, III-G8 | MED | GD23 §3 VAL-g (3) |
| III-G10 | VAL-g step (4): `w1_mul` (w₁ a valuation) | in(A)·in(B) ≠ 0 in the domain; attained | III-G8, III-G9 | MED | GD23 §3 VAL-g (4) |
| III-G11 | KEY-g(i): standard key Φ₁ monic, all monomials weight e·g·h, in(Φ₁) = ψ_hom | direct weight computation per monomial | III-G6, III-G10 | MED | GD23 §3 KEY-g(i) |
| III-G12 | KEY-g remaining: the (KPa) block at order 1 (ψ_hom ∤ in(B), deg B < e·g·d₀) + `KeyPkg` instance at order ≤ 1 | graded degree count in K₀[π̄^{±1}][Φ̄₀] | III-G5, III-G11 | HARD (pre-split: G12a block, G12b instance) | GD23 §3 KEY-g(ii,iii) |
| III-G13 | RES-1: order-1 residual dictionary (full form) | slot-by-slot residual read; III-G8's basis | III-G12 | HARD (pre-split: G13a min core, G13b slot bijections) | GD23 §3 RES-1 |
| III-G14 | `devid_ge` | ultrametric + multiplicativity, 5 lines | III-H8 (`IsPolyValuation`) | MECH | GD23 §4 pf "≥" |
| III-G15a | `ValGr` structure + `KPaBlock` def | fields only | — | MECH | GD23 §1.3 (g1)(g2) |
| III-G15b | `ValGr` instance at order ≤ 1 from III-G8/G9 | package the concrete grading | III-G15a, III-G8, III-G9, III-G10 | MED | GD23 §3→§4 seam |
| III-G16 | `devid_le` | min-slot m; ψ̂^m factor; isolate k = m; contradict block using valuation multiplicativity and KPa | III-G14, III-G15a, III-H8 | MED | GD23 §4 pf "≤" |
| III-G17 | `devid` assembled + Corollary (S-K1) | combine G14+G16; instantiate at [F.0] | III-G14, III-G16 | MECH | GD23 §4 + Cor |
| III-G18 | `bridge_equivDiv` (Lemma BRIDGE) | two ultrametric directions as displayed | III-G15a | MED | GD23 §5 BRIDGE |
| III-G19 | `uniq_two_valuations` (Lemma UNIQ) | induction on key degree via dev recursion | III-G1 | EASY | GD23 §6 UNIQ |
| III-G20 | `tie_w_eq_v` (Theorem TIE stmt + proof from UNIQ + rows) | both sides satisfy the recursion; UNIQ | III-G19, III-H8 | EASY | GD23 §6 TIE |
| III-G21a | `gd3_min` statement and order-≤1 instance | residual = initial-form ψ-order; anchored read | III-H8, III-G12b, III-G13a, III-G15b, III-G17 | HARD | GD23 §7.3 GD3-MIN |
| III-G21b | `gd3_min` general proof under `KeyPkg` | apply DEVID and the named graded/KPa rows | III-H8, III-G15a, III-G17, III-G21a | HARD | GD23 §7.3 GD3-MIN |
| III-G22 | `gd3_full_of_GRB` (statement fires the (H1) row) | unfold `GRB`, apply clause | III-H1, III-G21 | MECH | GD23 §7.3 GD3-FULL |
| III-G23 | POS-g(iv) submultiplicativity at order i+1 GIVEN (V1)_i + KPa (division control display) | DEVID at (w_i, Φ_i) gives (α)/(β); slot bookkeeping | III-H8, III-G15a, III-G17 | MED | GD23 §3 POS-g(iv) |

### Wave 2 — O-2a order ≤ 1 (Θ faithfulness; module §1.1–1.2 consumers)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-A1 | recovery map `recoverEHist (f c)` def | the displayed field-by-field recipe | III-C9 | EASY | O2a §2 Lemma R pf |
| III-A2 | Lemma R injectivity on 𝔈°_f | side-of-slope uniqueness (GMNReader row) + W2 | III-A1 | MED | O2a §2 Lemma R |
| III-A3 | Lemma R terminal NON-recovery: compiled two-witness gate ((1,1,1,0,0,⊥,0) vs (1,2,1,0,0,⊥,0)) | `decide`-style witness pair | III-C9 | MECH | O2a §2 Lemma R pf end |
| III-A4 | Theorem 1 order ≤ 1 (D4: Lift₀ is a Def-2.12 representative; order-1 family bridge Lemma B) | KEY-g supplies the representative property at level 0/1 | III-G12 | HARD (pre-split: A4a level-0, A4b Lemma B) | O2a §3 Thm 1 + Lemma B |
| III-A5 | MOVED TO WAVE 4 after III-U1: `(accE, accF)` tie + saturation ⇔ ω = 1 at coherent `machineProj` | corpus telescope `V9_irrSat` + `V3_accKeyDeg`; quarry only, not a verbatim alias | III-U1, corpus MovesT | EASY | O2a §5 (B); ROOT Step 7 |
| III-A6a | `GMNData` construction restricted by `c.slopes.length ≤ 1` | Newton-polygon side list and residual data from `OM/` | III-G21a | HARD | O2a (C4) level 1; GD23 §3 |
| III-A6b | `GMNReader` for that data, including `side_spec`, uniqueness, and residual-degree law | prove from the order-1 polygon API | III-A6a | HARD | O2a (C4) level 1; GD23 §3 |
| III-A6c | positive order-1 reader gate at `p = 2`, `c.slopes.length = 1` | construct data; prove a side is returned and laws are non-vacuous | III-A6b | MED | O2a (C4) non-vacuity |
| III-A7 | Theorem 2(B) stmt + proof from `GMNCor120_38` + `ConsF` + `OL1` | fire the literature row along the chain | III-C9, III-H6, III-H9 | EASY | O2a §5 Thm 2(B) |
| III-A8 | Theorem 2(D) (no-phantom = CU-2 content) stmt over rows | composition Thm 2(D) ∘ ι as displayed | III-A7 | EASY | O2a §5 Thm 2(D); CUC §1 |
| III-A9 | OL-6 order-≤1 instance probe (run decomposition + chain binding at one node) | quarry `U19_runCoherent`/`U24_runCanon`; gate-style | III-H7c, corpus HC2 | MED | O2a §4 OL-6; CU1 §0′ |

### Wave 3 — O-1thr Theorem 1 + lemma stock (modules §1.6–1.7)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-T1 | `readCeil` def + `readCeil_pos` (NAT) | max over `H.nodes` of ⌈I/E⌉ + 1; positivity trivial | corpus MovesC | EASY | O1thr §3 NAT |
| III-T2 | Lemma CEIL (`ceil_auditsClauses`) | per-clause height audit over `SideReads` fields | III-T1 | MED | O1thr §3 CEIL |
| III-T3 | `dev_congr_zp` (Lemma DEV at ℤ_[p]) | instance of III-G2 at O = ℤ_[p] | III-G2 | MECH | O1thr §2.1 DEV |
| III-T4 | Lemma POS at the corpus `Stage.w` (w ≥ 0, π-shift, ultrametric ⇒ w(B−B′) ≥ L·E) | `StageCoreL` rows supply the laws | corpus DefsL | EASY | O1thr §2.2 POS |
| III-T5 | `rloc` (R-LOC residual locality at `σ.R`) | graded-residue definitional unfold | corpus Moves.Defs | MED | O1thr §2.3 R-LOC |
| III-T6 | (†) display: w_i(B_j − B′_j) ≥ L·E_i > I_i (the strict middle inequality) | III-T3 + III-T4 + `Nat.ceil` arith | III-T2..T4 | EASY | O1thr §4 (†) |
| III-T7 | Theorem 1 transfer, (R1) clause | threshold ⟺ via (†) + ultrametric; 3 sub-cases as displayed | III-T6 | MED | O1thr §4 (R1) |
| III-T8 | Theorem 1 transfer, (R2) stride clause | exact-height transfer + R-LOC pattern read | III-T6, III-T5 | MED | O1thr §4 (R2) |
| III-T9 | Theorem 1 transfer, (R5) vertex clause ((†′) rederived at Φ_{i+1}) | DEV/POS verbatim at the child key; R-LOC at vtx | III-T6, III-T5 | MED | O1thr §4 (R5) |
| III-T10 | `read_locality` assembled ((R3)/(R4) record-only; symmetry) | combine T7–T9 per read; induct over `H.nodes` | III-T7..T9 | EASY | O1thr §4 Thm 1 |
| III-T11a | (M6c)(i) degree-one statement, explicitly assuming `e′ = 1` | corpus `UE.vtx_m6bi_n4upper` + `readBox_e1`; no broader re-keying claim | corpus HC2/UE, HK11a | MED | O1thr §2.5 (M6c)(i) |
| III-T11b | general (M6c)(i) statement under `GRB` and `OL2min` | fire the named higher-order rows | III-H1, III-H7a, III-T11a | MED | O1thr §2.5 (M6c)(i); D-R4 |
| III-T12 | (M6c)(ii) no-phantom: stmt (T12a) + harvest-pair reconstruction proof (T12b) under KeyPkg rows | face/ψ′ recovery from READ+(N1); the rev-4 weakened child hypothesis | III-H8, III-T11 | HARD (pre-split T12a stmt EASY / T12b proof) | O1thr §2.5 (M6c)(ii) |
| III-T13 | `wgeo` over the named rows | the four consumptions (V1)/(V2a)/(V2b)/(V2c) = H8/G17/G21 exactly as GD23's re-founding displays | III-H8, III-G17, III-G21 | MED | O1thr §2.5 WGEO; GD23 §4 Cor |
| III-T14a | `realEquiv_of_m6` reverse direction | consume the displayed `M6ABHyps` and `M6cHyps` rows | III-H1, III-T11b, III-T12, III-T14m | HARD | O1thr §2.5 REAL≡ |
| III-T14b | `realEquiv_of_m6` forward direction and biconditional assembly | consume the same named M6a/M6b/M6c rows | III-H1, III-T11b, III-T12, III-T14m | HARD | O1thr §2.5 REAL≡ |
| III-T14m | `M6ABHyps` and `M6cHyps` structures | statement only; expose M6a/M6b/M6c conditionality | corpus MovesD, III-H1 | EASY | O1thr §2.5 REAL≡ |
| III-T15 | VTX wrapper with source and target signatures both displayed; prove by exact application of `UE.vtx_htUpper_div` after `#check UE.vtx_htUpper_div` confirms definitional equality | no theorem is called a verbatim re-export until this typecheck succeeds | corpus HC2/UE | MECH | O1thr §2.5 VTX |
| III-T16 | ROOT-M (root confinement) | w₀(B_j) ≥ 1 below m, = 0 at m; from ord_{φ̄}(f̄) = m | III-G3 | EASY | O1thr §2.5 ROOT-M |

### Wave 4 — CU-1 (module §1.8)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-U1 | `machineProj` def + fieldwise lemmas | Node → ENodeData re-key | III-C2a, corpus MovesC | EASY | CU1 §2 π |
| III-U2 | `InteriorChain` def + base case k = 0 (root track exists: ord_{ψ̂₀}(f̄) = a₀ ≥ 2) | (c0) + reduction factor ψ̂₀^{a₀} | III-C9 | EASY | CU1 §2/§3 base |
| III-U3a | `StateBinding` def (clause (ii)'s content as a Prop over (M, H, lift)) | [F.0] stage-data equality fields | III-U1, III-H6 | EASY | CU1 §2 (ii) |
| III-U3b | induction step, candidate-pair identification (order ≤ 1 outright via A6/G-layer; ≥ 2 fires hGRB + hFRESH) | (c1)/(c2) → window principal face + ψ̂; GD-2/GD-3 instances | III-A6, III-G21, III-H1, III-H2 | HARD | CU1 §3 step |
| III-U3c | induction step, harvest realizes ν̂_{i+1} (creation-first; construction displayed) | harvest of THE identified pair; (M6c)(i) beyond-window | III-U3b, III-T11 | HARD | CU1 §3 step |
| III-U4 | state binding through the harvested induction step (OL-6 + (P-KEY)/(FR≡) fire) | transport the state produced by U3c; frame recursion = stage recursion | III-U3a, III-U3c, III-H3, III-H7c | MED | CU1 §3 (ii) leg |
| III-U5 | `cu1` assembled (ordinary induction, N-free) | List.rec on nodes; U2 base, U3b/c+U4 step | III-U2..U4 | EASY | CU1 §2 Thm CU-1 |
| III-U6 | `cu1_lvl` (Corollary CU-1-LVL) | ONE `read_locality` application at the top site + `realEquiv_of_m6`(⟸) + `NstarMaj` | III-U5, III-T10, III-T14, III-H4 | EASY | CU1 §2 CU-1-LVL |
| III-U7 | `cu1_spanTotal` (interior adequacy, per-site SPAN) | per-site totality from the same harvest construction | III-U3c | MED | CU1 §4 |
| III-U8 | positive gate: 2-node interior chain at p = 2 runs through `cu1`'s statement (non-vacuity) | corpus gate style (`HK23_twoNodeGatePos` template) | III-U5 | MED | CU1 §7.1's gate discipline |

### Wave 5 — CU-2t (module §1.9)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-S1a | `DecIrr` and `DecHen` definitions | unfold terminal index/multiplicity; `DecIrr` intentionally has no unused `f` | III-C9 | EASY | CUC §9.2 |
| III-S1b | `sq_not_dvd_reduction_of_disc_unit` | use the explicit hypothesis that `p` does not divide the discriminant | III-S1a | MED | CUC §9.2 (D3) |
| III-S1c | `j0_le_one` | derive from the explicit `¬φ² ∣ f̄` premise; no bare characteristic-zero discriminant claim | III-S1b | EASY | CUC §9.2 |
| III-S2 | `terminalDatum` def | case split on DEC branch | III-S1 | EASY | CUC §9.2 |
| III-S3 | `RCConsistent` def ((RC-read)/(RC-verd)) | transcribe Definition RC | III-S2, III-C8 | EASY | CUC §9.2a |
| III-S4 | `cu2t_readForcing` ((i)) | total length 1 from j₀ ≤ 1 + saturation; unique side | III-S1, III-A6 | MED | CUC §9.3 (i) |
| III-S5a | probe the exact installed Mathlib Hensel declaration; record its fully qualified name and type, without assuming `Polynomial.hensels_lemma` exists | `#check`/`#print` in a scratch scaffold file | Mathlib | MECH | CUC §9.3 (ii) |
| III-S5b | τ-irr verdict from `GMNCor120_38` | instantiate the displayed local literature row | III-S4, III-H9, III-A7 | MED | CUC §9.3 (ii) |
| III-S5c | τ-hen verdict from `Lit3Hensel` plus D3 | instantiate ring, ideal, polynomial, factorization and coprimality binders | III-S1c, III-S4, III-H9, III-S5a | MED | CUC §9.3 (ii) |
| III-S5d | assemble `cu2t_verdict` | case split on DEC branch | III-S5b, III-S5c | EASY | CUC §9.3 (ii) |
| III-S6 | `ThetaTau` def + well-defined + truncation | append entry; strip lemma | III-S2, III-C6 | EASY | CUC §9.3 (iii) |
| III-S7 | `thetaTau_injective` (both displayed granularities) | Lemma R on prefixes + verdict-pair record function | III-S6, III-A2 | MED | CUC §9.3 (iii) |
| III-S8 | `engineTerminal_rc_of_seamHyps` ((H6) consumption statement) | unfold `TerminalSeamHyps`, route each row | III-S3, III-H5 | EASY | CUC §9.4/§9.5 |

### O-14a′ — the map (module §1.10; zero proof debt)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-R1 | `runRealizerSupply` re-export | `:= MovesD.runRealizerExists_zmod p` | corpus MovesD/R7 | MECH | ROOT Step 9 |
| III-R2 | docstring unit: THE REDUCTION map note (`CanRealizes` fills the recentering half; interior half = `interior_node_e_eq_one` etc.) — a `#check`-anchored MANIFEST comment block, no new decl | none | corpus R7 files | MECH | O14ap r3 §0 |

**Auditable unit accounting:** each table row is one file-level declaration/proof
unit; no parent row conceals children. The revised table has 78 rows after expanding
C2b, C6/C7, G3, G12, G13, G21, A4, A6, T11, T12, T14, S1, and S5. Before assignment,
the division lead regenerates this count from the `id` column and rejects duplicate
or compound ids. No line-count promise is attached to an assembly: C2b, H1, T10,
U5, and S5 have been split so each owned declaration or proof remains independently
gateable.

---

## §3 THE CORPUS-REUSE MAP (existing proved declarations → units they discharge or feed)

### 3.1 Landed anchors (the movement's three named quarry files)

| corpus declaration | file | discharges / feeds |
|---|---|---|
| `runRealizerExists_zmod` (RRE(p, ZMod p), Lean-core) | `MovesD/R7_runRealizer.lean` | III-R1 VERBATIM (Step 9 is DONE in Lean; this movement only re-exports) |
| `RunRealizerExists`, `CanRealizes`, "THE REDUCTION" | `MovesD/R7_polFillReduction.lean` | III-R2; CU-3's supply statement (other movement) cites these, not new decls |
| `interior_node_e_eq_one`, `frame_deg_one`, `terminal_center_realizer`, `exists_run_start` | `MovesD/R7_runRealizer.lean` | III-U2/U3c quarry (run-start + interior-node facts for the CU-1 base/step) |
| `HK11a.sigmaV_vertexLaw`, `readVertex_e1`, `readBox_e1`, `regrade_w_eq_childW`, `anchor_transport` | `HC2/HK11a_vertexTransport.lean` | III-T9 (the (R5) vertex-clause vocabulary IS this law's), III-T11; the e′ = 1 perimeter + carried trio (hσL/hsteep/species) transfer as the units' displayed hypotheses |
| `UE.childW_ge_estar_mul_w`, `UE.vtx_m6bi_n4upper`, `UE.vtx_htUpper_div` | `HC2/UE_vtxUpper.lean` | III-T11 (retires the (M6b)(i)/(N4)-upper interface rows at degree 1), III-T15 VERBATIM re-export |

### 3.2 Carrier vocabulary (imported, never redeclared)

| corpus declaration | file | consumed by |
|---|---|---|
| `Stage` (w/wPrev/Φ/K/R fields + hK1/hS6a/hS6b laws) | `Moves/Defs.lean` | §1.6–1.8 throughout; `Stage.R : … → LaurentPolynomial` is R-LOC's carrier (III-T5) |
| `IsDevelopment`, `HasAnchorK`, `OrdPsiPoly` | `Moves/Defs.lean` | III-G1 (bridge lemma dev↔`IsDevelopment`), III-T3, III-S4 |
| `StageCoreL` | `Moves/DefsL.lean` | III-T4's law supply; HK11a's carried hypothesis row |
| `Node`, `History`, `HistoryCoherent`, `LandingKey`, `ReadSpecies` | `MovesC/Defs.lean` | III-T1 (readCeil over `History`), III-U1 (machineProj), everywhere |
| `ReadsOf`, `SideReads` (incl. clause (vi) vertex read-off), `KeysLawful`, `HistoryCoherentPre` | `HC2/Defs.lean`, `HK22_twoNodeGate.lean` | III-T7..T10 (the clause list Theorem 1 transfers IS `SideReads`'s), III-U3c |
| `accE`, `accF` + telescope | `MovesT/Defs.lean`, `MovesT/V9_irrSat.lean`, `MovesT/V3_accKeyDeg.lean` | III-A5 (the (accE,accF) tie is largely PROVED — re-key, don't re-prove) |
| `ReadFrame` + hK1/hStretch | `HC1/DefsV.lean` | III-T9/T11 via UE/HK11a signatures |

### 3.3 Proof-pattern quarry (templates + local lemmas to lift)

| corpus item | file | pattern for |
|---|---|---|
| Gauss-layer lemmas | `L3Gauss.lean` | III-G3/G4 (check before proving; `rg gauss` first) |
| `U19_runCoherent`, `U24_runCanon`, `U23_runRealizable` | `HC2/` | III-A9 (OL-6 order-≤1 probe), III-U4 |
| `U1_keysExist`, `U22E2_vertexEq`, `K1_vertexPin`, `V10_transportWindow` | `HC2/` | III-T2 (height audit patterns), III-T9 |
| `HK23_twoNodeGatePos`, `HK25_recGate` | `HC2/` | III-U8 (positive-gate style), III-A3 (negation-witness style) |
| `HK52_stretchGate` (`hk52_qform_stretch`) | `HC2/` | III-T9/T11 — the e′-stretch seam the units must NOT silently cross (fence: e′ = 1 hypotheses displayed) |
| `SP8_instantiation` + `MovesT/ReadLocality.lean` | `MovesSp/`, `MovesT/` | III-T10's box-level cousins; task #77's compiled obstruction note = why the scaffold restates locality at `ReadsOf`, per-f, NOT at `TreeModel` |
| `OM/` polygon modules (NPVertices etc.) | `OM/` | III-A6 (side lookup at order ≤ 1); division lead runs `rg "NP|polygon" LeanUrat/OM` before E-phase |

### 3.4 NOT this movement's quarry (listed so no unit grabs them)

`O12PoleFree`, `KsubGeneral`, `RegPFinite`, `SkeletonFinite`, `O5CountingB`,
`hExhaust_n2` (`OM/SeriesAssembly.lean`), the D-SC slot layer — Movements I/II/IV/V.

### 3.5 Banked non-claims that STAY banked

`npVertices_stable_of_hull_preserved` (the ONE banked sorry, off-path) — untouched.
`U1_negWitness`/`retiredKeysExist_false` — compiled negative perimeter; III-A3 imitates
the style, never the content.

### 3.6 CUC re-label map (Step 11's other constituents, for the division lead's records)

CU-2 = III-A8 (O-2a Thm 2(D) ∘ ι); CU-3 = III-R1/R2 + D-14 (III-T10) + (O6) pin
(a §3.3 bookkeeping row, no Lean unit); CU-4/CU-5/CU-7 = other movements per the CUC
§8 arrow map. No CUC unit is separately formalized — the consolidation record is
metadata, per ROOT Step 11's own wording.

---

## §4 THE WAVE PLAN (dependency-ordered, for the division lead)

- **WAVE 0 (dependency-staged, not fully parallel):** stage 0a: C1 and C5; stage
  0b: C2a/C4/C8; stage 0c: C2b1/C2b2/C2b3; stage 0d: C2b4/C3/C6a/C6b/C9; stage
  0e: C7a/C7b and H1..H9 once their displayed carrier dependencies compile.
  Gate after every file: `lake env lean <exact-new-file>`; then verify every
  hypothesis-row docstring against its brief section.
  THE STATEMENT LAYER IS THE PRODUCT — Codex plan-review (Level 2) runs on the
  as-built Wave-0 signatures before any proof wave.
- **WAVE 1 (GD23, 25 units incl. splits; after W0 only for H8):** two parallel
  tracks — track A: G1→G2→G3→G4→G5 and G6→G7→(G8,G9)→G10→G11→G12→G13;
  track B: G14, G15a→G15b→G16→G17→G18/G19→G20, then G21→G22, G23.
  Checkpoint: `lake build` + AxChk after G17 (DEVID assembled = the movement's
  first big cash-in).
- **WAVE 2 (O-2a; needs W0 + G12/G21a):** A1→A2, A3 in parallel,
  A4a→A4b, A6a→A6b→A6c, A7→A8, A9. A5 is not scheduled here; it runs in
  Wave 4 immediately after U1. Gate every file with `lake env lean <file>`.
- **WAVE 3 (O-1thr, 17 units; needs W1's G2 + W0):** T1→T2, T3/T4/T5 parallel,
  T6→(T7,T8,T9)→T10; T11→T12a→T12b; T13 (after G17/G21); T14a/b (after T11/T12);
  T15/T16 anytime.
  Checkpoint after T10: `read_locality` is CU-1-LVL's gate — division lead reports
  it upward (the spine architect consumes it at Step 18's transfer sites too).
- **WAVE 4 (CU-1; needs W2 + W3):** U1/U2/U3a parallel; U1→A5; then
  U3b→U3c→U4→U5→U6/U7→U8. Gate every file with `lake env lean <file>`;
  U8 remains mandatory before closure.
- **WAVE 5 (CU-2t; needs W2 + H5/H9):** S1a→S1b→S1c→S2→S3;
  S1c/A6b→S4; S5a may run early, then S4→S5b/S5c→S5d; S2/C6b→S6→S7;
  S3/H5→S8. Gate every file with `lake env lean <file>`. It may overlap Wave 4.
- **ANYTIME:** III-R1/R2 (Step 9 map) — assign first, it is the free win.

Division checkpoints per the swarm ground rules: per-file gates during waves;
`lake build` (plain, NOT `lake build LeanUrat`) + `lake env lean
LeanUrat/AxChk_baseline.lean` at each wave close; footprint regression =
stop-the-line. Commits name explicit paths; lock retries per standing practice.

**Prover-brief boilerplate (every unit prompt carries):** (1) the unit's src quote
from its brief §; (2) "statements are fences — if unprovable as stated, return
blocked-because with the exact goal state, never weaken"; (3) the automation cascade
+ `lean_local_search` before any Mathlib name from memory; (4) staged-write/64k
discipline; (5) no new axioms, no `True` placeholder in a hypothesis row.

---

## §5 MATH-REVISION SYNC DUTY (standing)

This blueprint tracks: O-2a rev 5 (pending pass P(O-2a r5) — if the pass forces a
2(D)-scope repair, III-A8's statement re-lands); O-1thr rev 4 (pending P(O-1thr r4) —
Thm 1/(M6c) cores are the twice-confirmed layer, low risk); GD23 rev 4 (VERIFIED
leaf #4 — stable); CU-1 rev 5 (VERIFIED leaf #5 — stable); CU-2t R4 (VERIFIED at
scope, leaf #9 — stable); O14ap rev 3 (twice-stable). On any rev of these briefs,
BP_III's owner folds the delta BEFORE the affected wave launches; units already
landed against a superseded rev get a re-audit row in the division records.

Known design risks, displayed for the Level-2 Codex review:
- **D-R1 (tower carrier):** Subfield-of-F rendering differs materially from
  iterated `AdjoinRoot`. The displayed inclusion and cardinal-degree rows are the
  current contract. Any carrier swap is a breaking interface revision requiring
  coordinated changes to `EHist`, `ChainData`, `Theta`, `machineProj`, polynomial
  coefficient types, equalities, and every consumer; it is not an internal swap.
- **D-R2 (GMNReader abstraction):** `GMNReader` is indexed by explicit `GMNData`;
  `side_spec`, `side_unique`, `resOrd_spec`, and `resDeg_eq_sideDeg` connect every
  read to that data. III-A6 is restricted by `c.slopes.length ≤ 1`; III-A6c is the
  concrete non-vacuity gate. Higher orders require the named OL/GRB rows.
- **D-R3 (ValGr interface):** DEVID over an abstract graded interface. The
  interface's four rows are exactly GD23 §1.3 (g1)/(g2) + domain + unit; III-G15b's
  concrete instance keeps it honest at order ≤ 1.
- **D-R4 (e′-stretch seam):** III-T11a states only the `e′ = 1` corpus perimeter.
  III-T11b is the separate general theorem and explicitly depends on GRB and OL2min.
  No degree-one corpus result is re-keyed as the general claim.

*BP_III end. Co-owned files: this blueprint only; no Lean files touched at the
architect phase.*

## REVISION 2 (review fold, 2026-08-03)
| finding | disposition | where/why |
|---:|:---:|---|
| 1 | FIXED | §1 signatures replace central ellipses with typed structures/definitions; compound statement rows are split into auditable declaration units. |
| 2 | FIXED | `EHist.hpsihat` makes `Theta` total without requiring an unavailable `EWF H`. |
| 3 | FIXED | III-C6a now owns displayed `EHist.take` and `ChainData.take` definitions. |
| 4 | FIXED | `EWF.towerBaseDegree` and `towerStepDegree` state base and per-step finite-field degree laws via cardinal powers. |
| 5 | FIXED | `GMNReader` has no `True` rows; lookup, uniqueness, residual order, and residual degree are explicit laws over `GMNData`. |
| 6 | FIXED | `ConsF` and Lemma R now consume semantic `GMNData` plus a reader whose laws connect lookup and residual fields to that data. |
| 7 | FIXED | `ValGr` now supplies zero, addition, multiplication, grading, initial forms, laws, and a domain condition on one honest carrier. |
| 8 | FIXED | DEVID uses one coefficient ring `K` for `w`, `Φ`, `B`, `KPaBlock`, and `minDev`. |
| 9 | FIXED | `devg_congr` binds `π`, its maximal-ideal equation, and both `j` and coefficient index `k`. |
| 10 | FIXED | `gaussW`, `w1`, and valuation-facing interfaces use `WithTop ℤ`, with zero mapped to `⊤`. |
| 11 | FIXED | `w1` explicitly maps `Φ₀` into `FractionRing O` and writes all `ℕ`-to-`ℤ` coercions. |
| 12 | FIXED | III-A5 is removed from Wave 2 and scheduled after III-U1 in Wave 4. |
| 13 | FIXED | Wave 0 is dependency-staged rather than advertised as fully parallel. |
| 14 | FIXED | `M6ABHyps` exposes M6a/M6b; T14 depends on it and on the separately displayed M6c supply. |
| 15 | FIXED | T11a is explicitly degree-one; T11b is the general GRB/OL2min theorem. |
| 16 | FIXED | `j0_le_one` assumes `¬φ² ∣ f̄`; discriminant supplies that only under the explicit `p`-unit/nondivisibility premise. |
| 17 | FIXED | `machineProj` requires `HistoryCoherent` and returns an `EWF`-certified subtype. |
| 18 | FIXED | A6 is restricted by `c.slopes.length ≤ 1`, proves semantic reader laws, and adds concrete gate A6c. |
| 19 | FIXED | `Lit3Hensel` exposes ring, ideal, polynomials, monicity, maximality, coprimality, reduction equality, and lifted factorization. |
| 20 | FIXED | CU-2t now displays result types, fixed-`f` injectivity, DEC evidence, reader/data dependence, RC fields, and truncation. |
| 21 | FIXED | `DecIrr` no longer carries the unused polynomial `f`. |
| 22 | FIXED | G15b, G16, G21, and G23 dependency rows now include their ValGr, valuation, KeyPkg, and KPa supplies. |
| 23 | FIXED | U4 now explicitly depends on U3c. |
| 24 | FIXED | `read_locality` now receives `HistoryCoherent H` explicitly. |
| 25 | FIXED | G3 is split; GAUSS-g(i) requires both inequalities and an attained minimum, not the invalid `B′ = 0` shortcut. |
| 26 | FIXED | A5 is labelled quarry-only, T11 is split by scope, and T15 requires displayed source/target typechecking before “verbatim” status. |
| 27 | FIXED | Compound C2b/G3/T11/S1/S5 rows are split into independently gated units; hidden hard-parent accounting is removed. |
| 28 | FIXED | GRB, FRESH, and terminal seam rows expose their object-level quantifiers and premises instead of hidden global bodies. |
| 29 | FIXED | D-R1 now records an `AdjoinRoot` change as a breaking carrier/interface revision affecting every downstream consumer. |
| 30 | FIXED | Unit accounting counts expanded table rows, forbids concealed children, and requires regeneration from unique ids. |
