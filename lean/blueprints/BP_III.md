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
  tower : (∀ x : ↥H.base, ↑x ∈ H.fld 0) ∧      -- F₁ ⊇ F_q with [F₁:F_q] = deg ψ̂₀ …
          ∀ i, ∀ x : ↥(H.fld i), ↑x ∈ H.fld (i+1)   -- degree laws per w4dress (unit III-C2b)

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

/-- (C3): Θ — the pure re-indexing of the continuing part. Total, unconditional. -/
def Theta (H : EHist p F) : ChainData p F
theorem theta_continuing (H : EHist p F) : Theta H = Theta H.continuingPart
theorem theta_truncation (H : EHist p F) (k : ℕ) : (Theta H).take k = Theta (H.take k)
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

/-- The GMN reader over (f, c): level-i principal-polygon side lookup by slope +
    residual ψ-order. Laws (uniqueness of a side of given slope; residual degree =
    side degree) are rows. Instances: order ≤ 1 PROVED (unit III-A6 + G-layer);
    orders ≥ 2 supplied only under `OL1 c` (§1.3). -/
structure GMNReader (f : Polynomial ℤ_[p]) (c : ChainData p F) where
  side   : ℕ → Option SideDatum        -- the side of N_i^−(f) of slope −h_i/e_i
  resOrd : ℕ → ℕ                       -- ord_{ψ̂_i}(R_{λ_i}(f))
  rootOrd : ℕ                          -- ord_{ψ̂₀}(f̄)
  side_unique : True                    -- rendered: at most one side per slope (row)
  resDeg_eq_sideDeg : True              -- residual degree = d(S_i) (row)

/-- (C4) Cons_f, over a reader: (c0) root order = a₀; (c1) side exists with the
    recorded shape at every continuing level; (c2) residual order = μ_i. -/
def ConsF (f : Polynomial ℤ_[p]) (H : EHist p F) (R : GMNReader f (Theta H)) : Prop
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
def GRB (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop := …

/-- (H2) = (FRESH), ROOT §3.1: joint-with-parent level-determinacy separation
    (O-9's named open, priced at the GD-2/CL-13 vertex-law layer = CU-1's step),
    incl. clause (c) (the former JUNCTION-PIN). -/
def FRESH (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop := …

/-- CU-1's three declared pins (CU1 rev-5 §0′), as one row structure. -/
structure CU1Pins (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  pROOT : …   -- (P-ROOT): the policy's root lift IS O-2a's Lift₀
  pKEY  : …   -- (P-KEY): produced key a function of the FORMAL chain datum only
  frEQ  : …   -- (FR≡): frame/read identification (order-2 content refutable — gate on record)

/-- (N*-MAJ), CU1 rev-5 §1: N*(𝐇) ≥ L(M_𝐇) — the SINGLE consumed property of the
    decision level. Any level function satisfying it may be substituted. -/
def NstarMaj (Nstar : EHist p F → ℕ) (L : MovesC.History p F → ℕ)
    (dress : EHist p F → MovesC.History p F) : Prop :=
  ∀ H, L (dress H) ≤ Nstar H

/-- (H6), ROOT §3.1 (CU-2t rows only — D-11 item (vii) is Movement IV/V's row):
    the terminal-seam engine-conformance trio, per CUC §9.4/§9.5 at R4's grading. -/
structure TerminalSeamHyps (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] : Prop where
  tDECdec : …   -- (T-DEC-dec): emission discipline at decided sites
  tDECcor : …   -- (T-DEC-cor): the corner fence, at the Corollary's own conditionality
  tREAD   : …   -- (T-READ): emitted shape/position fields = the (c1)-shape polygon datum
  tVERD   : …   -- (T-VERD): terminal verdict-field conformance

/-- OL-2a-1..6 = GD-1..GD-6 (O-2a rev-5 §4), each its own named Prop. OL1 is the
    ι-granting row (Lift_j outputs are Def-2.12 representatives, j ≥ 1); OL2/OL3's
    ≥2 content routes through GRB; OL4/OL5/OL6 are the engine-conformance family
    (OL6 = run decomposition + chain binding, consumed by CU-1(ii)). -/
def OL1 (c : ChainData p F) (lift : LiftFn p F) : Prop := …
def OL2min …  def OL3min …  def OL4 …  def OL5 …  def OL6 … : Prop := …
```

**Literature Props (displayed hypothesis Props, NOT axioms — the policy loop decides
their eventual status):**

```lean
/-- MacLane 1936 Def 4.1 + Thm 4.2 at the (V1) frame-semantics pin (LITUNIT §4,
    MATCH): the augmented value of a genuine key chain is a valuation. -/
def MacLaneV1Pkg (w : ℕ → Polynomial ℤ_[p] → ℤ) (keys : ℕ → Polynomial ℤ_[p]) : Prop := …

/-- The (KP) key package at one level: (KPa) in(Φ) = u·ψ̂ with the divisibility
    block ψ̂ ∤ in(B) for deg B < deg Φ; (KPirr) primeness; monicity. GD23 §1.3/§4. -/
structure KeyPkg (w : Polynomial ℤ_[p] → ℤ) (Φ : Polynomial ℤ_[p]) : Prop where …

/-- GMN Cor 1.20 (k′ = 1) / Cor 3.8 (k′ ≥ 2): the saturated-leaf invariant pair —
    consumed by O-2a Thm 2(B), hence CU-2t(ii). -/
def GMNCor120_38 (p : ℕ) … : Prop := …

/-- LIT-3 coprime Hensel (the (τ-hen) leg of CU-2t(ii)). Candidate corpus discharge:
    Mathlib `Polynomial.hensels_lemma` variants — probe unit III-S5a. -/
def Lit3Hensel (p : ℕ) : Prop := …
```

### 1.4 Module `Scaffold/DictIII/GDOrder1.lean` — GD23's order-≤1 layer (Step 8, VERIFIED leaf #4)

Stated over an arbitrary DVR where the brief is (`O` a DVR with maximal ideal (π),
residue field `Fres`); the corpus instance is `ℤ_[p]`. Mathlib carriers:
`[CommRing O] [IsDomain O] [IsDiscreteValuationRing O]`.

```lean
/-- Lemma DEV-g: monic-division development congruence mod π^L, coefficients in O[x]. -/
theorem devg_congr {O} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Φ : Polynomial O) (hΦ : Φ.Monic) (hd : 1 ≤ Φ.natDegree) (L : ℕ)
    {B B' : Polynomial O} (h : ∀ k, (B - B').coeff k ∈ (Ideal.span {π})^L) :
    ∀ j, (devCoeff Φ B j - devCoeff Φ B' j).coeff k ∈ (Ideal.span {π})^L

/-- w₀ := the Gauss valuation (min coefficient valuation); GAUSS-g (i)–(iii). -/
def gaussW {O} … (B : Polynomial O) : ℤ
theorem gaussW_dev_indep …               -- (i): dev-min = coeff-min
theorem gaussW_mul …                     -- (ii): w₀(AB) = w₀(A) + w₀(B) (Gauss)
theorem gaussW_keyBlock …                -- (iii): φ̄(X̄) prime; φ̄ ∤ in(B) for deg B < d₀

/-- w₁(B) := min_t (e·w₀(b_t) + t·h) over the Φ₀-development (root read (e,h)). -/
def w1 {O} … (Φ₀ : Polynomial O) (e h : ℕ) (B : Polynomial (FractionRing O)) : ℤ
theorem w1_posg …                        -- POS-g (i)–(iii) at w₁
theorem w1_submul_heavyCarry …           -- VAL-g step (1): ≥ with carries +h heavier
theorem w1_mul …                         -- VAL-g: w₁ is a valuation (steps (2)–(4))
theorem keyg_standardKey …               -- KEY-g: standard first key Φ₁; in(Φ₁) = ψ_hom;
                                         --   w₁(Φ₁) = e·g·h; the (KPa) block at order 1
theorem res1_dictionary …                -- RES-1: order-1 residual dictionary, full form
```

### 1.5 Module `Scaffold/DictIII/Devid.lean` — Theorem DEVID + BRIDGE/UNIQ/TIE (Step 8's every-order engine)

DEVID consumes ONLY: w a valuation ((V1) at the state), and (KPa)'s block — displayed
as an abstract graded interface so the unit never builds gr(w) globally.

```lean
/-- The graded interface DEVID actually consumes: initial-form data for w with
    (g1) in(A)+… sum law at the min weight, (g2) in(AB) = in(A)·in(B), domain. An
    instance at order ≤ 1 is built from §1.4's explicit descriptions (unit III-G15b). -/
structure ValGr (w : Polynomial K → ℤ) where
  Gr : ℤ → Type*            -- weight-γ pieces (concrete: slot-support functions)
  inF : (A : Polynomial K) → A ≠ 0 → Gr (w A)
  g1 : …                    -- sum-at-min-weight law
  g2 : …                    -- multiplicativity of initial forms
  dom : …                   -- no zero divisors among homogeneous elements

/-- Theorem DEVID (GD23 §4): under (V1) + (KPa)'s block, the Φ-development computes
    w from below: w(B) = min_k (w(C_k) + k·w(Φ)). -/
theorem devid (w : Polynomial K → ℤ) (hval : IsPolyValuation w) (G : ValGr w)
    (Φ : Polynomial ℤ_[p]) (hkpa : KPaBlock G Φ) (B : Polynomial K) (hB : B ≠ 0) :
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
theorem read_locality {n : ℕ} {f f' : Polynomial ℤ_[p]} {H : MovesC.History p F}
    (hcong : ∀ k, (f - f').coeff k ∈ (Ideal.span {(p : ℤ_[p])})^(readCeil H))
    (hm' : f'.Monic) (hd' : f'.natDegree = n)
    (h : MovesJ.ReadsOf p F n f H) : MovesJ.ReadsOf p F n f' H
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

/-- Lemma REAL≡: (M6a)+(M6b)+(M6c) ⟹ (walk visits o ⟺ REALIZED(f, o)). Split:
    ⟸ (used by CU-1-LVL) and ⟹ as separate units. -/
theorem realEquiv_of_m6 …
```

### 1.8 Module `Scaffold/DictIII/CU1.lean` — Theorem CU-1 + Corollary CU-1-LVL (Step 10, VERIFIED leaf #5)

```lean
/-- The projection π: corpus machine history → 𝔈 (field-by-field re-key). -/
def machineProj (M : MovesC.History p F) : EHist p F

/-- Interior scoping: all nodes continuing, non-complete (μ_i ≥ 2), a₀ ≥ 2. -/
def InteriorChain (H : EHist p F) : Prop

/-- THEOREM CU-1 (N-free realization + state binding), over the displayed rows:
    order-≤1 instances of GD-2/GD-3(min)/GD-6 outright; orders ≥ 2 via hGRB; plus
    hFRESH, the pins, OL6. Conclusion (i): a machine history M with
    machineProj M = 𝐇 and ReadsOf f M; (ii): the state frame after M equals the
    [F.0] stage data over Theta 𝐇 (key = Lift, width = μ_k). -/
theorem cu1 {n : ℕ} {f : Polynomial ℤ_[p]} (H : EHist p F) (hwf : EWF H)
    (hint : InteriorChain H) (R : GMNReader f (Theta H)) (hcons : ConsF f H R)
    (hGRB : GRB p F) (hFRESH : FRESH p F) (hpins : CU1Pins p F)
    (hOL6 : OL6 …) (hlift : LiftFn p F) (hOL1 : OL1 (Theta H) hlift) :
    ∃ M : MovesC.History p F, machineProj M = H ∧ MovesJ.ReadsOf p F n f M ∧
      StateBinding M H hlift        -- clause (ii), its own def (unit III-U4a)

/-- Corollary CU-1-LVL: the working-level transfer — consumes read_locality ONCE at
    the top site + realEquiv_of_m6 (⟸) + the NstarMaj row. -/
theorem cu1_lvl … (hmaj : NstarMaj Nstar readCeil dress) …

/-- Interior adequacy (per-site SPAN totality; the ADEQ interior half). -/
theorem cu1_spanTotal …
```

### 1.9 Module `Scaffold/DictIII/CU2t.lean` — the terminal seam (Step 11's CU-2t, VERIFIED-at-scope leaf #9)

```lean
def DecIrr (f : Polynomial ℤ_[p]) (H : EHist p F) : Prop   -- k′ ≥ 1 ∧ μ_{k′} = 1
def DecHen (f : Polynomial ℤ_[p]) (H : EHist p F) (R : GMNReader f (Theta H)) : Prop
   -- k′ = 0 ∧ (a₀ = 1 ∨ j₀ = 1)

theorem j0_le_one …            -- φ² ∤ f from disc f ≠ 0 (the (D3) argument)

/-- T(f, 𝐇°): the forced terminal datum — read entry λ_{k′+1} ∈ ℚ<0 ∪ {−∞} +
    verdict pair (accE, accF) resp. (1, f₀). -/
def terminalDatum …

/-- Definition RC (CUC §9.2a): (RC-read) the (c1)-shape clause at level k′+1 with
    sel = ⊥; (RC-verd) announced pair = the prefix accumulator pair. -/
def RCConsistent (f) (H : EHist p F) (ν : ENodeData) (EF : ℕ × ℕ) … : Prop

/-- Lemma CU-2t(i): read forcing — N_{k′+1}^−(f) has total length 1, exactly one
    side; every read-entry coordinate a function of (f, c). -/
theorem cu2t_readForcing …

/-- Lemma CU-2t(ii): verdict forcing + correctness — fires GMNCor120_38 (τ-irr) /
    Lit3Hensel + the (D3)/(L3+) layer (τ-hen); RC-consistent records agree at datum
    granularity. -/
theorem cu2t_verdict (hcor : GMNCor120_38 …) (hhen : Lit3Hensel p) … 

/-- Lemma CU-2t(iii): Θ^τ := Θ(𝐇°) ⌢ (λ_{k′+1}, ⊥, (E_ν, F_ν)) — well-defined on
    DEC seam objects, truncation-compatible, injective over fixed f at both
    displayed granularities. -/
def ThetaTau …
theorem thetaTau_injective …

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
| III-C2b | `EWF` rows W1/W2/W5 + `EWF_tower` + `EWF_dress` (3 sub-structures, one `structure … extends` assembly) | transcribe W-laws | III-C2a | EASY | O2a (C1) W1–W5 |
| III-C3 | `EHist.continuingPart` + lemma: prefixes of WF ending continuing are WF | list `dropLast` case split | III-C2b | EASY | O2a (C1) last ¶ |
| III-C4 | row classifiers T1–T5 + `dCert` | decidable case split on (ℓ,e,h,sel,inc) | III-C1 | MECH | O2a (C1) rows |
| III-C5 | `ChainData` structure | fields only | — | MECH | O2a (C2) |
| III-C6 | `Theta` def | re-index nodes → slopes list | III-C2a, III-C5 | MECH | O2a (C3) |
| III-C7 | `theta_continuing` + `theta_truncation` | unfold; `List.map_take` | III-C6 | EASY | O2a (C3) |
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
| III-G3 | `gaussW` def + GAUSS-g(i) | dev-min = coeff-min via III-G2 with B′=0 | III-G1 | EASY | GD23 §3 GAUSS-g(i) |
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
| III-G15b | `ValGr` instance at order ≤ 1 from III-G8/G9 | package the concrete grading | III-G8..G10 | MED | GD23 §3→§4 seam |
| III-G16 | `devid_le` | min-slot m; ψ̂^m factor; isolate k = m; contradict block | III-G15a | MED | GD23 §4 pf "≤" |
| III-G17 | `devid` assembled + Corollary (S-K1) | combine G14+G16; instantiate at [F.0] | III-G14, III-G16 | MECH | GD23 §4 + Cor |
| III-G18 | `bridge_equivDiv` (Lemma BRIDGE) | two ultrametric directions as displayed | III-G15a | MED | GD23 §5 BRIDGE |
| III-G19 | `uniq_two_valuations` (Lemma UNIQ) | induction on key degree via dev recursion | III-G1 | EASY | GD23 §6 UNIQ |
| III-G20 | `tie_w_eq_v` (Theorem TIE stmt + proof from UNIQ + rows) | both sides satisfy the recursion; UNIQ | III-G19, III-H8 | EASY | GD23 §6 TIE |
| III-G21 | `gd3_min` under `KeyPkg` (+ outright at order ≤ 1 via G12/G13a) | residual = initial-form ψ-order; the anchored read | III-G13a, III-G17 | HARD (pre-split: G21a stmt+order≤1, G21b general under KeyPkg) | GD23 §7.3 GD3-MIN |
| III-G22 | `gd3_full_of_GRB` (statement fires the (H1) row) | unfold `GRB`, apply clause | III-H1, III-G21 | MECH | GD23 §7.3 GD3-FULL |
| III-G23 | POS-g(iv) submultiplicativity at order i+1 GIVEN (V1)_i + KPa (division control display) | DEVID at (w_i, Φ_i) gives (α)/(β); slot bookkeeping | III-G17 | MED | GD23 §3 POS-g(iv) |

### Wave 2 — O-2a order ≤ 1 (Θ faithfulness; module §1.1–1.2 consumers)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-A1 | recovery map `recoverEHist (f c)` def | the displayed field-by-field recipe | III-C9 | EASY | O2a §2 Lemma R pf |
| III-A2 | Lemma R injectivity on 𝔈°_f | side-of-slope uniqueness (GMNReader row) + W2 | III-A1 | MED | O2a §2 Lemma R |
| III-A3 | Lemma R terminal NON-recovery: compiled two-witness gate ((1,1,1,0,0,⊥,0) vs (1,2,1,0,0,⊥,0)) | `decide`-style witness pair | III-C9 | MECH | O2a §2 Lemma R pf end |
| III-A4 | Theorem 1 order ≤ 1 (D4: Lift₀ is a Def-2.12 representative; order-1 family bridge Lemma B) | KEY-g supplies the representative property at level 0/1 | III-G12 | HARD (pre-split: A4a level-0, A4b Lemma B) | O2a §3 Thm 1 + Lemma B |
| III-A5 | (accE, accF) tie + saturation ⇔ ω = 1 (statement over corpus `MovesT.accE/accF` at `machineProj`) | corpus telescope `V9_irrSat` + `V3_accKeyDeg` | III-U1, corpus MovesT | EASY | O2a §5 (B); ROOT Step 7 |
| III-A6 | `GMNReader` instance at order ≤ 1 (side lookup from N₁^−(f); resOrd from R_λ) | Newton-polygon side data at level ≤ 1; quarry `OM/` polygon modules | III-G21a | HARD (pre-split: A6a side, A6b resOrd) | O2a (C4) level 1; GD23 §3 |
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
| III-T11 | (M6c)(i) statement + degree-1-perimeter proof | corpus `UE.vtx_m6bi_n4upper` + `readBox_e1` re-keyed to the harvested-child quantifier | corpus HC2/UE, HK11a | MED | O1thr §2.5 (M6c)(i) |
| III-T12 | (M6c)(ii) no-phantom: stmt (T12a) + harvest-pair reconstruction proof (T12b) under KeyPkg rows | face/ψ′ recovery from READ+(N1); the rev-4 weakened child hypothesis | III-H8, III-T11 | HARD (pre-split T12a stmt EASY / T12b proof) | O1thr §2.5 (M6c)(ii) |
| III-T13 | `wgeo` over the named rows | the four consumptions (V1)/(V2a)/(V2b)/(V2c) = H8/G17/G21 exactly as GD23's re-founding displays | III-H8, III-G17, III-G21 | MED | O1thr §2.5 WGEO; GD23 §4 Cor |
| III-T14 | `realEquiv_of_m6` (⟸ direction — the CU-1-LVL consumer) | walk reconstruction along records; (M6a/b/c) fire per step | III-T11, III-T12 | HARD (pre-split: T14a ⟸, T14b ⟹) | O1thr §2.5 REAL≡ |
| III-T15 | VTX corollary re-export (corpus map, no new proof) | alias `UE.vtx_htUpper_div` with ROOT-facing docstring | corpus HC2/UE | MECH | O1thr §2.5 VTX |
| III-T16 | ROOT-M (root confinement) | w₀(B_j) ≥ 1 below m, = 0 at m; from ord_{φ̄}(f̄) = m | III-G3 | EASY | O1thr §2.5 ROOT-M |

### Wave 4 — CU-1 (module §1.8)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-U1 | `machineProj` def + fieldwise lemmas | Node → ENodeData re-key | III-C2a, corpus MovesC | EASY | CU1 §2 π |
| III-U2 | `InteriorChain` def + base case k = 0 (root track exists: ord_{ψ̂₀}(f̄) = a₀ ≥ 2) | (c0) + reduction factor ψ̂₀^{a₀} | III-C9 | EASY | CU1 §2/§3 base |
| III-U3a | `StateBinding` def (clause (ii)'s content as a Prop over (M, H, lift)) | [F.0] stage-data equality fields | III-U1, III-H6 | EASY | CU1 §2 (ii) |
| III-U3b | induction step, candidate-pair identification (order ≤ 1 outright via A6/G-layer; ≥ 2 fires hGRB + hFRESH) | (c1)/(c2) → window principal face + ψ̂; GD-2/GD-3 instances | III-A6, III-G21, III-H1, III-H2 | HARD | CU1 §3 step |
| III-U3c | induction step, harvest realizes ν̂_{i+1} (creation-first; construction displayed) | harvest of THE identified pair; (M6c)(i) beyond-window | III-U3b, III-T11 | HARD | CU1 §3 step |
| III-U4 | state binding through the step (OL-6 + (P-KEY)/(FR≡) fire) | frame recursion = stage recursion at matched records | III-U3a, III-H3, III-H7c | MED | CU1 §3 (ii) leg |
| III-U5 | `cu1` assembled (ordinary induction, N-free) | List.rec on nodes; U2 base, U3b/c+U4 step | III-U2..U4 | EASY | CU1 §2 Thm CU-1 |
| III-U6 | `cu1_lvl` (Corollary CU-1-LVL) | ONE `read_locality` application at the top site + `realEquiv_of_m6`(⟸) + `NstarMaj` | III-U5, III-T10, III-T14, III-H4 | EASY | CU1 §2 CU-1-LVL |
| III-U7 | `cu1_spanTotal` (interior adequacy, per-site SPAN) | per-site totality from the same harvest construction | III-U3c | MED | CU1 §4 |
| III-U8 | positive gate: 2-node interior chain at p = 2 runs through `cu1`'s statement (non-vacuity) | corpus gate style (`HK23_twoNodeGatePos` template) | III-U5 | MED | CU1 §7.1's gate discipline |

### Wave 5 — CU-2t (module §1.9)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-S1 | `DecIrr`/`DecHen` defs + `j0_le_one` | φ² \| f ⇒ repeated root ⇒ disc = 0 | III-C9 | EASY | CUC §9.2 |
| III-S2 | `terminalDatum` def | case split on DEC branch | III-S1 | EASY | CUC §9.2 |
| III-S3 | `RCConsistent` def ((RC-read)/(RC-verd)) | transcribe Definition RC | III-S2, III-C8 | EASY | CUC §9.2a |
| III-S4 | `cu2t_readForcing` ((i)) | total length 1 from j₀ ≤ 1 + saturation; unique side | III-S1, III-A6 | MED | CUC §9.3 (i) |
| III-S5 | `cu2t_verdict` ((ii)) from the literature rows | τ-irr: fire `GMNCor120_38`; τ-hen: fire `Lit3Hensel` + (D3) layer | III-S4, III-H9, III-A7 | MED | CUC §9.3 (ii) |
| III-S6 | `ThetaTau` def + well-defined + truncation | append entry; strip lemma | III-S2, III-C6 | EASY | CUC §9.3 (iii) |
| III-S7 | `thetaTau_injective` (both displayed granularities) | Lemma R on prefixes + verdict-pair record function | III-S6, III-A2 | MED | CUC §9.3 (iii) |
| III-S8 | `engineTerminal_rc_of_seamHyps` ((H6) consumption statement) | unfold `TerminalSeamHyps`, route each row | III-S3, III-H5 | EASY | CUC §9.4/§9.5 |

### O-14a′ — the map (module §1.10; zero proof debt)

| id | statement | proof sketch | deps | diff | src |
|---|---|---|---|---|---|
| III-R1 | `runRealizerSupply` re-export | `:= MovesD.runRealizerExists_zmod p` | corpus MovesD/R7 | MECH | ROOT Step 9 |
| III-R2 | docstring unit: THE REDUCTION map note (`CanRealizes` fills the recentering half; interior half = `interior_node_e_eq_one` etc.) — a `#check`-anchored MANIFEST comment block, no new decl | none | corpus R7 files | MECH | O14ap r3 §0 |

**Unit count: 62 (+ pre-split children counted at their parents).** HARD rows: G12,
G13, G21, A4, A6, T12, T14, U3b, U3c — nine, each pre-split; everything else lands in
one prover pass by design.

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

- **WAVE 0 (18 units, all MECH/EASY; fully parallel):** III-C1..C9, III-H1..H9.
  Gate: module compiles + every hypothesis-row docstring quotes its brief §.
  THE STATEMENT LAYER IS THE PRODUCT — Codex plan-review (Level 2) runs on the
  as-built Wave-0 signatures before any proof wave.
- **WAVE 1 (GD23, 25 units incl. splits; after W0 only for H8):** two parallel
  tracks — track A: G1→G2→G3→G4→G5 and G6→G7→(G8,G9)→G10→G11→G12→G13;
  track B: G14, G15a→G15b→G16→G17→G18/G19→G20, then G21→G22, G23.
  Checkpoint: `lake build` + AxChk after G17 (DEVID assembled = the movement's
  first big cash-in).
- **WAVE 2 (O-2a, 10 units; needs W0 + G12/G21a):** A1→A2, A3 (parallel),
  A4a→A4b, A5, A6a/A6b, A7→A8, A9.
- **WAVE 3 (O-1thr, 17 units; needs W1's G2 + W0):** T1→T2, T3/T4/T5 parallel,
  T6→(T7,T8,T9)→T10; T11→T12a→T12b; T13 (after G17/G21); T14a/b (after T11/T12);
  T15/T16 anytime.
  Checkpoint after T10: `read_locality` is CU-1-LVL's gate — division lead reports
  it upward (the spine architect consumes it at Step 18's transfer sites too).
- **WAVE 4 (CU-1, 9 units; needs W2 + W3):** U1/U2/U3a parallel → U3b → U3c → U4 →
  U5 → U6/U7 → U8 (gate MANDATORY before the wave closes — CU-1 non-vacuity).
- **WAVE 5 (CU-2t, 8 units; needs W2 + S-layer of W0):** S1→S2→S3, S4→S5,
  S6→S7, S8. Independent of W3/W4 except S4's III-A6 dep — may run parallel to W4.
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
- **D-R1 (tower carrier):** Subfield-of-F rendering of the 𝔈/𝔗 towers (vs the
  brief's literal iterated quotients). Mitigation: the tower laws are Prop rows, so
  a later `AdjoinRoot` swap changes carriers, not downstream statements; the
  faithfulness question (literal-quotient ↔ Subfield) is a §3.3-style transcription
  row for the eventual semantic audit.
- **D-R2 (GMNReader abstraction):** Cons_f over a reader structure instead of
  constructed GMN objects. This is deliberate ([M]-row discipline: OL-1/(GR-B) own
  the ≥2 construction), but the order-≤1 instance (III-A6) must be REAL — the unit
  is HARD and gate-checked, else ConsF is vacuously satisfiable. Non-vacuity gate:
  a p = 2, n = 2 concrete reader instance with `decide`-checked side data.
- **D-R3 (ValGr interface):** DEVID over an abstract graded interface. The
  interface's four rows are exactly GD23 §1.3 (g1)/(g2) + domain + unit; III-G15b's
  concrete instance keeps it honest at order ≤ 1.
- **D-R4 (e′-stretch seam):** every T-layer unit consuming HK11a/UE inherits the
  e′ = 1 sub-perimeter (HK52's compiled obstruction). Units display it; the general
  e′ case rides the (GR-B)/OL-2 rows — NOT silently claimed.

*BP_III end. Co-owned files: this blueprint only; no Lean files touched at the
architect phase.*
