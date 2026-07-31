# BP_II — Movement II blueprint: SOLVE REGULARITY (ROOT Steps 4–5)

Blueprint architect deliverable for the LEAN CONVERSION SWARM (authority: ledger
`lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`, 2026-08-03 entry; scaffold shape per the
2026-08-01 PROOF SCAFFOLD entry). Movement II = the solve's regularity: pole-freeness at
every prime power — ROOT (`docs/ROOT_ASSEMBLY_2026-08-02.md` REV 5) **Step 4** (K-13
(REG-p) finiteness, Lean-LANDED) and **Step 5** (O-12 + D-6: 𝔅_n, the master denominator
theorem, (SL≥2), (REG-p) emptiness). Source of mathematical truth: the VERIFIED leaf
`lean/notes/openmath/O12_phaseB_verifybrief_rev4.md` (V19 + Fable pass 2, zero criticals
at the honest scope) + its attempt record `O12_phaseB_attempt_rev4.md`.

## 0. Charter, landed perimeter, and what this blueprint adds

**Already landed (do NOT re-blueprint; reuse by import):**

* `LeanUrat/MovesU/O12PoleFree.lean` — the ABSTRACT pole-free layer: 𝒮 (`cycS`), Lemma
  L5 (`cycS_eval_pos`; = ROOT's "Lemma RR", the rev-1 name), ℛ-membership (`MemRcyc` +
  ring closure + `powSubst` closure = L7(i)(ii)), the grammar `Gram` + `Gram.memRcyc`
  (Theorem 2's absorption step), Corollary D margins (`marginO1/O2/O3`,
  `detO1/detO2/detO3` + `_unit` + `_margin`), `AbsSolveTable` / `RegAt` /
  `RcycDiscipline` / `regAt_of_discipline` / `regAt_primePow` (Theorem 3's mechanism).
* `LeanUrat/MovesU/RegPFinite.lean` — Step 4 in full (M17 A/B/C + Corollary U):
  `RegP`, `RegData`, `regP_iff_pool_avoids`, `regP_failing_eq/_finite`, `regP_cofinite`.

**This blueprint adds the REMAINING Movement II layers** (per the swarm dispatch): the
block stratification lemmas L1–L6e, Fact F, the three/four kernel organizations
(bookings O1/O2/O2′/O3) with Theorem 1 and the (SL≥2) display, and Theorem 2's
ℛ-induction over the 𝔅_n row families — plus the Step-4⊕Step-5 seam ((REG-p) EMPTINESS
in the `RegP` vocabulary) behind the named instance-pin hypothesis row.

**Honest scope (binding, from the leaf's §1 scope declaration):** the claim is about
zeros/poles of the §2-defined family 𝔅_n; VALUE correctness is OUTSIDE (V7-F1 on
record — that is D-11/O-11, Movements IV–V). The identification of the project's
realized tables with 𝔅_n is the interface seam (B-INST)/OL-O12-1/OL-O12-2 — here a
NAMED HYPOTHESIS ROW (`InstancePin`, §1.10), never an axiom. T-8's block structure and
T-3/T-6's event structure enter "as structure only": they are the `BnMember` DATA, not
hypotheses. The e = 1 corner is vacuous by construction (`K_1 = 0` definitional +
hand-off descent) — the (SL≥2) display, units II-B11/B12.

**Ground rules honored:** new modules only under `LeanUrat/Scaffold/`; namespace
`LeanUrat.Scaffold`; no new axioms (the two audited axioms are not needed by this
movement); the semantic-measure inputs use the corpus's established
recorded-via-hypothesis convention (`L4.cellVolume_eq`'s `hfactor`, `R1.stratum_volume`,
`L2core.perShapeVolume_baseChange`) — displayed structure fields, flagged for the
semantic-guardian audit; parked items 22–29 untouched; no fenced statement touched.

**Module map (all new, all `LeanUrat/Scaffold/O12/`):**

| module | content | units |
|---|---|---|
| `Core.lean` | q, E_e, κ₀/κ₁, shared arithmetic | II-C1..C4 |
| `Bookings.lean` | the four bookings, Theorem 1, (SL≥2) | II-B1..B12 |
| `Family.lean` | GramOver, 𝔅_n row families, Theorem 2 R-induction | II-R1..R14 |
| `RegEmpty.lean` | Theorem 3, Corollary D at 𝔅_n, InstancePin seam | II-G1..G7 |
| `Substochastic.lean` | Theorem 4 backup | II-S1..S3 |
| `PolygonData.lean` | face-kinds, heights, L6b, L4(ii) bounds | II-P1..P8 |
| `FactF.lean` | N_ρ/P_ρ polynomials + the finite-field counts | II-F1..F9 |
| `Torus.lean` | (T1) + the L6d telescope + (JC) | II-T1..T5 |
| `Semantic.lean` | L1–L3, L6a, L6c, L6e over the displayed rows | II-M0..M11 |

## 1. STATEMENT LAYER

Everything below is `namespace LeanUrat.Scaffold`, with
`open LeanUrat.MovesU (MemRcyc Gram cycS DefinedAt AbsSolveTable detO1 detO2 detO3)`
and `abbrev Qq := RatFunc ℚ`. Signatures are sketches: provers may adjust implicit
binders/instance arguments, never the mathematical content (statement-fence applies
after E-phase sign-off).

### 1.1 Core (`Scaffold/O12/Core.lean`)

```lean
noncomputable def qX : Qq := algebraMap (Polynomial ℚ) Qq Polynomial.X

/-- `E_e = e(e+1)/2 = 1 + 2 + ⋯ + e` (brief §2.2). -/
def blockE (e : ℕ) : ℕ := e * (e + 1) / 2

theorem blockE_ge_three {e : ℕ} (he : 2 ≤ e) : 3 ≤ blockE e
theorem two_le_blockE_sub_one {e : ℕ} (he : 2 ≤ e) : 2 ≤ blockE e - 1

/-- κ₀ = q^{−E} (the in-place loop mass, symbolic; brief §2.4). -/
noncomputable def kappa0 (e : ℕ) : Qq := (qX ^ blockE e)⁻¹
/-- κ₁ = (q−1)·q^{−E} (the recentering mass, symbolic). -/
noncomputable def kappa1 (e : ℕ) : Qq := (qX - 1) * (qX ^ blockE e)⁻¹

/-- κ₀ + κ₁ = q^{1−E} (Theorem 1(1)'s scalar). -/
theorem kappa_add (e : ℕ) : kappa0 e + kappa1 e = qX * (qX ^ blockE e)⁻¹
theorem gram_kappa0 (e : ℕ) : Gram (kappa0 e)
theorem gram_kappa1 (e : ℕ) : Gram (kappa1 e)
```

### 1.2 Bookings + Theorem 1 + (SL≥2) (`Scaffold/O12/Bookings.lean`)

```lean
/-- The four kernel organizations (brief §2.4). `O2r` = (O2′). -/
inductive Booking | O1 | O2 | O2r | O3
  deriving DecidableEq, Fintype

/-- The 1×1 kernel scalar `K_e` per booking; block 1 (and the degenerate e = 0)
carries `K = 0` (brief §2.2: block 1 terminates immediately). -/
noncomputable def Booking.kernel (b : Booking) (e : ℕ) : Qq :=
  if e ≤ 1 then 0 else
  match b with
  | .O1  => qX * (qX ^ blockE e)⁻¹              -- κ₀ + κ₁ = q^{1−E}
  | .O2  => (qX ^ blockE e)⁻¹                   -- κ₀
  | .O2r => (qX ^ blockE e)⁻¹                   -- κ₀ (κ₁ re-fed as exit legs)
  | .O3  => (qX - 1) * (qX ^ blockE e - 1)⁻¹    -- κ₁/(1−κ₀)

noncomputable def Booking.Phi (b : Booking) (e : ℕ) : Qq := 1 - b.kernel e

/-- The booking's solve denominator `u` (Theorem 1(3)): `1 − q^{1−E}` for the three
re-entrant bookings, `1 − q^{−E}` for (O2). -/
noncomputable def Booking.solveU (b : Booking) (e : ℕ) : Qq :=
  match b with
  | .O2 => 1 - (qX ^ blockE e)⁻¹
  | _   => 1 - qX * (qX ^ blockE e)⁻¹

theorem Booking.kernel_one (b : Booking) : b.kernel 1 = 0        -- K₁ = 0
theorem Booking.Phi_one (b : Booking) : b.Phi 1 = 1              -- Φ₁ = 1

/-- Theorem 1(2), displayed forms: the Φ's are the landed dets. -/
theorem Phi_O1_eq {e : ℕ} (he : 2 ≤ e) : Booking.O1.Phi e = detO1 (blockE e - 1)
theorem Phi_O2_eq {e : ℕ} (he : 2 ≤ e) : Booking.O2.Phi e = detO2 (blockE e)
theorem Phi_O2r_eq {e : ℕ} (he : 2 ≤ e) : Booking.O2r.Phi e = detO2 (blockE e)
theorem Phi_O3_eq {e : ℕ} (he : 2 ≤ e) : Booking.O3.Phi e = detO3 (blockE e)

/-- gcd(X^a − 1, X^b − 1) = X^gcd(a,b) − 1 in ℚ[X] (Theorem 1(2)'s gcd input). -/
theorem gcd_X_pow_sub_one (a b : ℕ) :
    EuclideanDomain.gcd (Polynomial.X ^ a - 1) (Polynomial.X ^ b - 1)
      = (Polynomial.X ^ Nat.gcd a b - 1 : Polynomial ℚ)  -- up to unit normalization

/-- Theorem 1(2), (O3) reduced numerator: q^E − q = q(q^{E−1}−1), and after the
gcd = q−1 division the numerator is q·(1 + q + ⋯ + q^{E−2}). -/
theorem detO3_reduced {E : ℕ} (hE : 2 ≤ E) :
    (Polynomial.X ^ E - Polynomial.X : Polynomial ℚ)
      = (Polynomial.X - 1) * (Polynomial.X * ∑ i ∈ Finset.range (E - 1), Polynomial.X ^ i)

/-- Theorem 1(3), O1/O2′ solve: the balance equation has the displayed unique solution. -/
theorem solve_O1_O2r {e : ℕ} (he : 2 ≤ e) (s x : Qq)
    (hbal : x = (kappa0 e + kappa1 e) * x + s) :
    x = s * (1 - qX * (qX ^ blockE e)⁻¹)⁻¹
/-- Theorem 1(3), O3 solve: multiplying through by 1 − κ₀ ≠ 0 gives the SAME equation. -/
theorem solve_O3 {e : ℕ} (he : 2 ≤ e) (s x : Qq)
    (hbal : (1 - kappa1 e * (1 - kappa0 e)⁻¹) * x = s * (1 - kappa0 e)⁻¹) :
    x = s * (1 - qX * (qX ^ blockE e)⁻¹)⁻¹
/-- Theorem 1(3), O2 solve: no feedback, genuine division by 1 − κ₀. -/
theorem solve_O2 {e : ℕ} (he : 2 ≤ e) (t x : Qq) (hbal : x = kappa0 e * x + t) :
    x = t * (1 - (qX ^ blockE e)⁻¹)⁻¹

/-- Theorem 1(1)'s presentation-independence parenthetical: a scalar loop graded by a
finite type set has kernel κ·Id, whose det (1−κ)^k has the same zero set as 1−κ. -/
theorem det_one_sub_scalar_id {k : ℕ} (κ : Qq) :
    ((1 : Matrix (Fin k) (Fin k) Qq) - κ • 1).det = (1 - κ) ^ k

/-- (SL≥2), unit half: for 2 ≤ e the solve denominator is a nonzero ℛ-unit (L7(iii)). -/
theorem solveU_unit (b : Booking) {e : ℕ} (he : 2 ≤ e) :
    b.solveU e ≠ 0 ∧ MemRcyc (b.solveU e) ∧ MemRcyc (b.solveU e)⁻¹

/-- (SL≥2), display (ROOT Movement II, REV-2 finding V2-6): every self-loop of the
system has e ≥ 2 — the kernel scalar VANISHES at e ≤ 1 and is nonzero at e ≥ 2, so
the degenerate denominator 1/(1 − q^{−(E−1)}) at E = 1 never fires. -/
theorem selfloop_ge_two (b : Booking) {e : ℕ} (h : b.kernel e ≠ 0) : 2 ≤ e
theorem kernel_ne_zero (b : Booking) {e : ℕ} (he : 2 ≤ e) : b.kernel e ≠ 0

/-- (SL≥2)(a): inter-block descent — a hand-off relation contained in < admits no
cycle through distinct blocks (self-loops are within-block). -/
theorem no_interblock_cycle {H : ℕ → ℕ → Prop} (hlt : ∀ a b, H a b → b < a) :
    ∀ e, ¬ Relation.TransGen H e e
```

### 1.3 GramOver + the 𝔅_n row families + Theorem 2 (`Scaffold/O12/Family.lean`)

Verdicts reuse the corpus `LeanUrat.MovesU.SplittingType n` (Fintype instance landed,
`U0b_splitTypeFintype.lean`).

```lean
/-- The grammar 𝒢 with LEAVES: generated from a set S by (g1)–(g6) (brief §2.3).
Mirrors the landed `Gram` (O12PoleFree.lean) plus a leaf constructor — the leaves are
the lower blocks' solved entries in Theorem 2's induction. -/
inductive GramOver (S : Set Qq) : Qq → Prop
  | leaf {f : Qq} (h : f ∈ S) : GramOver S f
  | poly (P : Polynomial ℚ) : GramOver S (algebraMap (Polynomial ℚ) Qq P)
  | invS {s : Polynomial ℚ} (hs : s ∈ cycS) : GramOver S (algebraMap (Polynomial ℚ) Qq s)⁻¹
  | add {f g} : GramOver S f → GramOver S g → GramOver S (f + g)
  | mul {f g} : GramOver S f → GramOver S g → GramOver S (f * g)
  | neg {f} : GramOver S f → GramOver S (-f)
  | subst {f} (δ : ℕ+) : GramOver S f → GramOver S (MovesS.powSubst δ f)

theorem GramOver.memRcyc {S : Set Qq} (hS : ∀ g ∈ S, MemRcyc g) {f : Qq}
    (h : GramOver S f) : MemRcyc f
theorem Gram.gramOver {S : Set Qq} {f : Qq} (h : Gram f) : GramOver S f
theorem GramOver.mono {S T : Set Qq} (hST : S ⊆ T) {f} : GramOver S f → GramOver T f
theorem GramOver.finsetSum {S} {ι : Type*} (t : Finset ι) (F : ι → Qq)
    (h : ∀ i ∈ t, GramOver S (F i)) : GramOver S (∑ i ∈ t, F i)
theorem GramOver.listProd {S} (l : List Qq) (h : ∀ f ∈ l, GramOver S f) :
    GramOver S l.prod

/-- The β-legs available to block e: β_{e′}(σ′) for e′ < e (base changes are `subst`,
so δ needs no indexing here — brief §2.3(vi)). -/
def lowerLegs {n : ℕ} (β : ℕ → MovesU.SplittingType n → Qq) (e : ℕ) : Set Qq :=
  {g | ∃ e' < e, ∃ σ, g = β e' σ}

/-- One block of a 𝔅_n member, presented for the R-induction (brief §2.3(iv)+(vii)):
the aggregated verdict rows t_σ are 𝒢-generated over the lower solved entries, and the
block solves by division by the booking's ℛ-unit denominator. This structure IS the
T-8 block structure consumed "as structure only" (ROOT Step 5 consumes-list). -/
structure BlockPresentation (n : ℕ) (β : ℕ → MovesU.SplittingType n → Qq) (e : ℕ) where
  trow    : MovesU.SplittingType n → Qq
  htrow   : ∀ σ, GramOver (lowerLegs β e) (trow σ)
  u       : Qq
  hu      : u ≠ 0 ∧ MemRcyc u ∧ MemRcyc u⁻¹
  hsolve  : ∀ σ, β e σ = u⁻¹ * trow σ

/-- **Theorem 2's R-induction engine**: base blocks in ℛ + every block presented over
its lower legs ⟹ every solved entry lies in ℛ. Strong induction on e. -/
theorem beta_memRcyc {n : ℕ} {β : ℕ → MovesU.SplittingType n → Qq}
    (hbase : ∀ e ≤ 1, ∀ σ, MemRcyc (β e σ))
    (hstep : ∀ e, 2 ≤ e → BlockPresentation n β e) :
    ∀ e σ, MemRcyc (β e σ)
```

The concrete row families (brief §2.3 (i)–(vii)), each with its 𝒢 witness:

```lean
/-- Family (ii): divisor-pattern mass m(π) = q^{−(E−e)}·N_π(q)·q^{−e}. -/
noncomputable def massPatt (e : ℕ) (Nπ : Polynomial ℚ) : Qq :=
  (qX ^ (blockE e - e))⁻¹ * algebraMap (Polynomial ℚ) Qq Nπ * (qX ^ e)⁻¹
theorem gram_massPatt (e : ℕ) (Nπ : Polynomial ℚ) : Gram (massPatt e Nπ)

/-- Family (iii): polygon-family mass m(κ, ρ⃗) — a finite sum over L6b(ii)'s
enumeration of (g3)-volumes times (g4)-closures (exponents c_j ≥ 1, from
`PolygonData`), times the (JC) shape factor ∏ P_{ρ_j}(q)·(q^{d_j}−q^{d_j−1})⁻¹. The
DEFINITION takes the enumeration data as finite lists; L6′ (unit II-M11) ties it to
the polygon cells. -/
noncomputable def massPoly (e : ℕ) (enum : Finset (ℕ × ℕ))   -- (V, N_min(ε)) pairs
    (cs : List ℕ+) (shape : List (Polynomial ℚ × ℕ+)) : Qq   -- (P_ρ_j, d_j) pairs
theorem gram_massPoly (e : ℕ) (enum) (cs) (shape) : Gram (massPoly e enum cs shape)

/-- Family (iv): the verdict row of a family F with hand-off list H(F) and composition
datum comp — a 0/1-coefficient finite sum of products of m(F) with base-changed lower
β-legs (brief §2.3(iv) display). μ < e per L4 (units II-B12/II-P8 supply the bound). -/
noncomputable def rowOf {n : ℕ} (β : ℕ → MovesU.SplittingType n → Qq)
    (m : Qq) (H : List (ℕ × ℕ+))                              -- (μ_i, D_i)
    (comp : (∀ i : Fin H.length, MovesU.SplittingType n) → MovesU.SplittingType n)
    (σ : MovesU.SplittingType n) : Qq
theorem gramOver_rowOf {n β e} (hm : Gram m) (H) (hH : ∀ x ∈ H, x.1 < e) (comp σ) :
    GramOver (lowerLegs β e) (rowOf β m H comp σ)

/-- Family (iv), (O2) allocation adjustment: for EVERY α : verdicts → ℚ[q] the adjusted
row t_σ + α(σ)·q^{−E} stays generated (Theorem 2 needs only α(σ) ∈ ℚ[q]; the mass
identity Σ_σ α(σ) = q−1 is the value-side datum, displayed as `AllocDatum`). -/
def AllocDatum (n : ℕ) : Type :=
  {α : MovesU.SplittingType n → Polynomial ℚ //
    ∑ σ, α σ = Polynomial.X - 1}   -- Σ_σ α_e(σ) = q − 1 (brief §2.3(iv))
theorem gramOver_allocAdjust {n β e S} (h : GramOver S t) (α : Polynomial ℚ) :
    GramOver S (t + algebraMap (Polynomial ℚ) Qq α * (qX ^ blockE e)⁻¹)

/-- Family (iv)/(v), (O3) exit scaling q^E/(q^E − 1) = Σ_{L≥0} κ₀^L (closed form). -/
theorem gramOver_o3scale {e S t} (h : GramOver S t) :
    GramOver S ((qX ^ blockE e) * ((qX ^ blockE e - 1 : Polynomial ℚ) ... )⁻¹ * t)

/-- Family (v): the entrance/shape weight list (brief §2.3(v)), all Gram. -/
noncomputable def weightSet (n : ℕ) : Finset Qq
theorem gram_weightSet {n g} (hg : g ∈ weightSet n) : Gram g

/-- A 𝔅_n member: booking × per-block presentation × entry lists E(e) with their
generation witnesses over the solved entries (families (i)–(vii) union). -/
structure BnMember (n : ℕ) where
  booking  : Booking
  β        : ℕ → MovesU.SplittingType n → Qq
  hbase    : ∀ e ≤ 1, ∀ σ, MemRcyc (β e σ)                 -- E(1) = {1}
  blocks   : ∀ e, 2 ≤ e → BlockPresentation n β e
  hblockU  : ∀ e (he : 2 ≤ e), (blocks e he).u = booking.solveU e
  entries  : ℕ → Finset Qq                                  -- E(e)
  hentries : ∀ e, ∀ g ∈ entries e, GramOver {f | ∃ e' ≤ e, ∃ σ, f = β e' σ} g

/-- **THEOREM 2 (master denominator theorem)**: every member of every E(e), every
booking, every composition datum, every allocation datum, every solved β at every
depth, lies in ℛ — hence (landed L7(i)) is defined at every prime power q₀ ≥ 2. -/
theorem BnMember.entries_memRcyc {n : ℕ} (T : BnMember n) :
    ∀ e, ∀ g ∈ T.entries e, MemRcyc g
theorem BnMember.beta_leg_memRcyc {n : ℕ} (T : BnMember n) (e : ℕ)
    (σ : MovesU.SplittingType n) (δ : ℕ+) : MemRcyc (MovesS.powSubst δ (T.β e σ))
```

### 1.4 Theorem 3 + the Step-4⊕Step-5 seam (`Scaffold/O12/RegEmpty.lean`)

```lean
/-- Package a 𝔅_n member as the landed abstract solve table (O12PoleFree.lean §1). -/
noncomputable def BnMember.toAbs {n : ℕ} (T : BnMember n) : AbsSolveTable where
  nBlocks := n + 1
  Phi     := fun e => T.booking.Phi e
  entries := fun e => T.entries e

/-- The ℛ-discipline holds at every member: dets are ℛ-units (II-B10 + landed
`detO1_unit`/`detO3_unit` + `Phi_one`), entries in ℛ (Theorem 2). -/
theorem BnMember.discipline {n : ℕ} (T : BnMember n) : T.toAbs.RcycDiscipline

/-- **THEOREM 3 ((REG-p) EMPTINESS at 𝔅_n)**: every member, every prime p, every
depth δ ≥ 1 — fires the landed `AbsSolveTable.regAt_primePow`. The failing set is
EMPTY; composite depths p^{δm} are again prime powers ≥ 2, so no descent-depth
evaluation fails either. -/
theorem BnMember.regEmpty {n : ℕ} (T : BnMember n) {p δ : ℕ}
    (hp : 2 ≤ p) (hδ : 1 ≤ δ) : T.toAbs.RegAt ((p ^ δ : ℕ) : ℚ)

/-- **Corollary D at 𝔅_n** (the Step-17 (r1) margin numbers): per booking the det
values at every prime power obey the displayed lower bounds Φ ≥ 3/4 [O1],
7/8 [O2/O2′], 6/7 [O3] (and Φ₁ = 1). Reuses the landed `detO*_margin`. -/
theorem BnMember.detMargin {n : ℕ} (T : BnMember n) {e : ℕ} (he : 2 ≤ e)
    {x : ℚ} (hx : 2 ≤ x) :
    (match T.booking with
     | .O1 => (3:ℚ)/4 | .O2 => 7/8 | .O2r => 7/8 | .O3 => 6/7)
      ≤ (T.booking.Phi e).eval (RingHom.id ℚ) x

/-- **(B-INST) — the instance-pin hypothesis row** (ROOT Step 5, REVISION 1 finding 9;
OL-O12-1/OL-O12-2/D-11 seam). NOT proved here and NOT an axiom: the identification of
a realized `RegData` table (RegPFinite vocabulary, Step 4) with a 𝔅_n member. The
degree-2 pin is dischargeable from the machine-checked table (α₂ = (0, q−1), brief §7);
the complete degree-3 pin is OL-O12-2 (finite transcription pass, zero mathematics);
general n is D-11's pin (ROOT Step 17). -/
structure InstancePin (p n : ℕ) (D : MovesU.RegData p) (T : BnMember n) : Prop where
  det_eq      : ∀ e : D.Block, ∃ e' : ℕ, D.det e = T.booking.Phi e' ∧ 2 ≤ e' ∨ D.det e = 1
  entries_sub : ∀ e : D.Block, ∀ g ∈ D.entryList e, ∃ e', g ∈ T.entries e'
  -- field names/shapes to be finalized against RegData at E-phase; the CONTENT is
  -- fixed: dets are the member's Φ's, entry lists land inside the member's E(e')'s.

/-- The seam theorem: pinned tables satisfy `RegP` at EVERY prime — Step 4's finiteness
upgraded to Step 5's emptiness. (`RegP`'s (r2) act-agreement conjunct is free given
definedness — RegPFinite.lean `RegPin.act_agree`.) -/
theorem regP_of_pin {p n : ℕ} {D : MovesU.RegData p} {T : BnMember n}
    (hpin : InstancePin p n D T) (hp : 2 ≤ p) : MovesU.RegP D

/-- Display form: the landed failing-set Finset (`regP_failing_eq`) is EMPTY under
the pin — "every prime" in the root. -/
theorem regP_failing_empty_of_pin ...
```

### 1.5 Theorem 4, the substochastic backup (`Scaffold/O12/Substochastic.lean`)

```lean
/-- Theorem 4, nonvanishing: nonnegative M with row sums ≤ 1 − ε has det(1 − M) ≠ 0
(strict diagonal dominance; Mathlib `Matrix.det_ne_zero_of_sum_row_lt_diag`). -/
theorem det_one_sub_ne_zero {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {ε : ℝ}
    (hε : 0 < ε) (h0 : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j ≤ 1 - ε) :
    ((1 : Matrix (Fin k) (Fin k) ℝ) - M).det ≠ 0

/-- Theorem 4, positivity: t ↦ det(1 − tM) is continuous, nonzero on [0,1], = 1 at
t = 0 ⟹ positive at t = 1. -/
theorem det_one_sub_pos {k M ε} (hε) (h0) (hrow) :
    0 < ((1 : Matrix (Fin k) (Fin k) ℝ) - M).det

/-- Instantiation at 𝔅_n: the scalar kernel value at any prime power is ≤ 1 − ε with
ε = 3/4, 7/8, 6/7 per booking (Corollary D margins) — the hypothesis holds if a finer
state set ever replaces the scalar kernel. -/
theorem bn_substochastic_margin (b : Booking) {e : ℕ} (he : 2 ≤ e) {x : ℚ} (hx : 2 ≤ x) :
    (b.kernel e).eval (RingHom.id ℚ) x
      ≤ 1 - (match b with | .O1 => (3:ℚ)/4 | .O2 => 7/8 | .O2r => 7/8 | .O3 => 6/7)
```

### 1.6 Polygon combinatorics, L6b + L4(ii) (`Scaffold/O12/PolygonData.lean`)

Pure integer/rational arithmetic — no valuations, no measure. Vocabulary chosen to
bridge to the LANDED `LeanUrat.L4.LatticePolygon` (BB1) at unit II-M7.

```lean
/-- A face-kind sequence κ = (L_j, b_j)_{j=1..k} on width e (brief §3, L6): L_j ≥ 1,
Σ L_j = e, b_j ∣ L_j, b_k ≥ 2. d_j := L_j/b_j; x_1 = 0, x_{j+1} = x_j + L_j. -/
structure FaceKind (e : ℕ) where
  faces    : List (ℕ+ × ℕ+)                    -- (L_j, b_j), left to right
  hsum     : (faces.map (·.1.val)).sum = e
  hdvd     : ∀ f ∈ faces, (f.2 : ℕ) ∣ (f.1 : ℕ)
  hlast    : ∀ h : faces ≠ [], 2 ≤ ((faces.getLast h).2 : ℕ)
def FaceKind.x (κ : FaceKind e) (j : ℕ) : ℕ        -- vertex abscissas
def FaceKind.d (κ : FaceKind e) (j : ℕ) : ℕ        -- residual degrees L_j/b_j

/-- An admissible slope tuple: numerators a_j ≥ 1, gcd(a_j, b_j) = 1, s_1 > ⋯ > s_k,
s_k ∈ (0,1) (i.e. a_k < b_k). -/
structure SlopeTuple (κ : FaceKind e) where
  a       : Fin κ.faces.length → ℕ+
  hcop    : ∀ j, Nat.Coprime (a j) (κ.faces.get j).2
  hdesc   : ∀ j j', j < j' → slope j' < slope j     -- slope j := a j / b j : ℚ
  hlt1    : ∀ h : κ.faces ≠ [], slope (last) < 1

/-- Heights h_i := P(i) ∈ ℚ (right-anchored: h_e = 0); vertex heights are integers
h_{x_j} = Σ_{j′≥j} a_{j′}·d_{j′} (each face drops a_j·d_j ∈ ℤ). -/
noncomputable def heights (κ : FaceKind e) (s : SlopeTuple κ) (i : ℕ) : ℚ
theorem vertexHeight_int (κ s j) : heights κ s (κ.x j) = ((Σ_{j′ ≥ j} a·d : ℕ) : ℚ)

/-- N(P) = Σ_{i<e} ⌈h_i⌉, with every ⌈h_i⌉ ≥ 1 (slopes > 0, h_e = 0). -/
noncomputable def Npg (κ : FaceKind e) (s : SlopeTuple κ) : ℤ :=
  ∑ i ∈ Finset.range e, ⌈heights κ s i⌉
theorem one_le_ceil_height {i : ℕ} (hi : i < e) (hpos : ...) : 1 ≤ ⌈heights κ s i⌉

/-- L6b(i), the elementary move: a_j ↦ a_j + b_j changes N by exactly
c′_j = x_j·L_j + L_j(L_j+1)/2 ≥ 1 (integer gains; ⌈h + z⌉ = ⌈h⌉ + z for z ∈ ℤ). -/
def cPrime (κ : FaceKind e) (j : Fin κ.faces.length) : ℕ :=
  κ.x j * (κ.faces.get j).1 + (κ.faces.get j).1 * ((κ.faces.get j).1 + 1) / 2
theorem elemMove_Npg (κ s j) :
    Npg κ (s.bump j) = Npg κ s + cPrime κ j       -- s.bump j := a_j += b_j
theorem one_le_cPrime (κ j) : 1 ≤ cPrime κ j

/-- L6b(ii), the nested-minimum period shift: a_j^min(s+1) = a_j^min(s) + b_j. -/
theorem aMin_shift ...
/-- L6b(ii), enumeration affinity: a unit step of the gap variable w_j performs the
elementary move on face j AND (through shifted minima) on every j′ < j:
ΔN = c_j := Σ_{j′≤j} c′_{j′} ≥ 1; the vertex count k is w-independent. -/
theorem gapStep_Npg ...
/-- L6b(ii), k = 1: a single-face kind has NO unbounded parameter (finitely many
admissible tuples: a_k ∈ {1,…,b_k−1}). -/
theorem singleFace_finite (κ : FaceKind e) (h : κ.faces.length = 1) :
    Finite (SlopeTuple κ)

/-- L4(ii) arithmetic (the (SL≥2)(a) hand-off bound): rightmost face has
d_k ≤ e/2 (b_k ≥ 2); every other face d_j ≤ e − 2; hence any residual factor of
multiplicity μ ≥ 2 and degree D with μ·D ≤ d_j has μ < e. -/
theorem faceDeg_bound (κ : FaceKind e) (he : 2 ≤ e) :
    ∀ j, κ.d j < e
theorem handoff_mu_lt (κ : FaceKind e) (he : 2 ≤ e) {μ D j : ℕ}
    (hμ : 2 ≤ μ) (hle : μ * D ≤ κ.d j) (hD : 1 ≤ D) : μ < e

/-- L4(i) arithmetic (the divisor-pattern half): a multiset of atoms (D, m) with
Σ D·m = e, not equal to {(1,e)}, has every atom's m < e. -/
theorem patt_mult_lt {e : ℕ} (π : Multiset (ℕ+ × ℕ+))
    (hdeg : (π.map fun x => (x.1 : ℕ) * x.2).sum = e)
    (hne : π ≠ {(1, ⟨e, _⟩)}) : ∀ x ∈ π, (x.2 : ℕ) < e
```

### 1.7 Fact F (`Scaffold/O12/FactF.lean`)

Two halves: the ℚ[q]-POLYNOMIALS (all that Theorem 2 consumes — MECH) and the
finite-field COUNTS (the Step-17/value-side handoff — the hard cluster).

```lean
/-- M_D(q) = D⁻¹ Σ_{δ|D} μ(δ) q^{D/δ} ∈ ℚ[q] (Fact F, brief §2.3). -/
noncomputable def Mpoly (D : ℕ+) : Polynomial ℚ :=
  Polynomial.C (1 / (D : ℚ)) * ∑ δ ∈ (D : ℕ).divisors,
    Polynomial.C (Nat.ArithmeticFunction.moebius δ : ℚ) * Polynomial.X ^ ((D : ℕ) / δ)

noncomputable def fallingFac (P : Polynomial ℚ) (r : ℕ) : Polynomial ℚ :=
  ∏ i ∈ Finset.range r, (P - Polynomial.C (i : ℚ))

/-- N_ρ(q), P_ρ(q) for a pattern ρ : Multiset (ℕ+ × ℕ+) of atoms (D, m):
N_ρ = ∏_D (M_D)_{r_D} / ∏_m c_{D,m}!, and P_ρ = the same with the D = 1 supply
M_1 = q replaced by q − 1 (z-free). -/
noncomputable def Npoly (ρ : Multiset (ℕ+ × ℕ+)) : Polynomial ℚ
noncomputable def Ppoly (ρ : Multiset (ℕ+ × ℕ+)) : Polynomial ℚ
theorem gram_Npoly (ρ) : Gram (algebraMap (Polynomial ℚ) Qq (Npoly ρ))   -- (g1)

/-- The factorization pattern of h ∈ F[z]: each distinct monic irreducible factor
contributes the atom (its degree, its multiplicity). Unit-scalar invariant. -/
noncomputable def patternOf {F : Type*} [Field F] (h : Polynomial F) :
    Multiset (ℕ × ℕ)
theorem patternOf_smul_unit {F} [Field F] (u : Fˣ) (h : Polynomial F) :
    patternOf ((u : F) • h) = patternOf h

-- The count layer, F a finite field, q := Fintype.card F:
/-- F(i) step: X^{q^D} − X = ∏ (monic irreducibles of degree ∣ D), squarefree.
(Mathlib supplies one divisibility direction:
`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`.) -/
theorem X_pow_card_prod_irreducibles ...
/-- F(i) degree count: q^D = Σ_{δ|D} δ·I_δ. -/
theorem card_irred_degree_sum ...
/-- **Fact F(i)**: D·I_D = Σ_{δ|D} μ(δ)·q^{D/δ}, i.e. (Mpoly D).eval q = I_D
(Möbius inversion: `Nat.ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`). -/
theorem card_monicIrreducible_eq (D : ℕ+) :
    ((Mpoly D).eval (Fintype.card F : ℚ)) = #{f : Polynomial F | f.Monic ∧
      Irreducible f ∧ f.natDegree = D}
/-- F(ii) abstract count: choices of r DISTINCT items from an M-element supply
carrying a multiplicity multiset {m : c_m} number (M)_r / ∏ c_m!. -/
theorem distinct_choice_count ...
/-- **Fact F(ii)**: (Npoly ρ).eval q = #{monic h : patternOf h = ρ, deg = total}. -/
theorem card_pattern_eq ...
/-- **Fact F(iii)**: (Ppoly ρ).eval q = the z-free count (h(0) ≠ 0); the only monic
irreducible with zero constant term is z. -/
theorem card_pattern_zfree_eq ...
```

### 1.8 The torus telescope, L6d (`Scaffold/O12/Torus.lean`)

```lean
/-- **(T1), the torus identity** (L6d Step 1): for every c ∈ Fˣ and z-free ρ,
#{R : deg R = d, R(0) = c, patternOf R = ρ} = (Ppoly ρ).eval q — independent of c
(the two-sided unit-rescaling bijection). -/
theorem torus_count (F) [Field F] [Fintype F] (d : ℕ) (ρ) (c : Fˣ) :
    #{R : Polynomial F | R.natDegree = d ∧ R.coeff 0 = c ∧ patternOf R = ρ}
      = #{S : Polynomial F | S.Monic ∧ S.natDegree = d ∧ S.coeff 0 ≠ 0 ∧ patternOf S = ρ}

/-- **The fibered telescope** (L6d Step 2), abstract form: counting functions
n_j : Fˣ × Fˣ → ℕ whose torus row-sums Σ_λ n_j(λ, c) = P_j are c-independent
telescope over shared-vertex chains: Σ_{V ∈ (Fˣ)^k} ∏_j n_j(V_j, V_{j+1}) = ∏_j P_j
(V_{k+1} := 1, the anchor). Induction on k, left to right. -/
theorem chain_telescope {k : ℕ} (n : Fin k → Fˣ → Fˣ → ℕ) (P : Fin k → ℕ)
    (hrow : ∀ j c, ∑ λ : Fˣ, n j λ c = P j) :
    (∑ V : Fin k → Fˣ, ∏ j, n j (V j) (V.next j 1)) = ∏ j, P j

/-- **(JC) count form** (L6d): the joint residue-configuration count over a face-kind
κ with shape vector ρ⃗ equals ∏_j (Ppoly ρ_j).eval q — instantiating the telescope
with the interior-coefficient counts, row sums supplied by (T1). -/
theorem jc_count ...
/-- **(JC) probability** + product-of-marginals: divide by (q−1)^k·q^{Σ(d_j−1)};
each factor is P_{ρ_j}(q)·(q^{d_j} − q^{d_j−1})⁻¹ — ONE element of ℚ(q), uniform in
the characteristic (Fact F), face events independent. -/
theorem jc_prob ...
/-- Consistency: Σ_{ρ z-free of degree d} (Ppoly ρ).eval q = q^d − q^{d−1}. -/
theorem zfree_total ...
```

### 1.9 The semantic layer, L1–L3 / L6a / L6c / L6e (`Scaffold/O12/Semantic.lean`)

The analytic inputs enter by the corpus's recorded-via-hypothesis convention
(cf. `L4.cellVolume_eq`'s `hfactor`, `R1.stratum_volume`): ONE displayed structure of
rows, everything downstream derived sorry-free. The VOLUME half of L6a is already
LANDED as `LeanUrat.L4.cellVolume_eq` (BB1) — unit II-M7 is a wrapper.

```lean
/-- **The semantic rows** (the [M]-style hypothesis structure of this movement;
each field is a standard cited fact, flagged for the semantic-guardian audit):
(HAAR-COORD) the per-coordinate valuation law μ{v ≥ t} = q₀^{−t}, μ{v = t} =
(1−q₀^{−1})q₀^{−t}, coordinates independent (brief §2.1; = L4.lean's `hfactor`
convention); (NP-SLOPES) the multiset of root valuations equals the multiset of
Newton-polygon slopes (brief L1 last sentence; standard, cite Neukirch II.6);
(TYPE-INV) splitting types invariant under x ↦ πx rescale and x ↦ x + c recenter
(brief L2/L3 — VALUE-side, consumed only by Movements IV–V). -/
structure SemanticRows (params...) where
  haarBall   : ...   -- μ{v(a_i) ≥ t} = q₀^{−t}
  haarShell  : ...   -- μ{v(a_i) = t} = (1 − q₀^{−1})·q₀^{−t}
  haarIndep  : ...   -- product over coordinates
  npSlopes   : ...   -- root valuations = polygon slopes (multiset equality)
  typeRescale  : ... -- L2's splitting-type preservation (value-side)
  typeRecenter : ... -- L3's splitting-type preservation (value-side)

/-- L1 upper bound: v(a_i) = v(±e_i(r)) ≥ i·μ, μ := min_j v(r_j) (ultrametric sum
bound over the i-subsets). Over an abstract `Valuation K Γ₀`. -/
theorem val_esymm_ge ...
/-- L1 equality case: with k := #{j : v(r_j) = μ}, v(a_k) = k·μ (unique
strict-minimum term in e_k). -/
theorem val_esymm_min_eq ...
/-- **L1(i)/(ii)** both directions + the ℤ-snap (v(a) > 0 ⟹ v(a) ≥ 1 for integral
coefficients): all roots v > 0 ⟺ ∀i v(a_i) ≥ 1; all roots v ≥ 1 ⟺ ∀i v(a_i) ≥ i. -/
theorem L1_root_coeff ...

/-- L2 algebraic half: the coefficients of h(y) = g(πy)/π^e are b_i = a_i/π^i
(`Polynomial.scaleRoots` vocabulary). -/
theorem rescale_coeff ...
/-- L3 algebraic half: recentering is coefficient-triangular with unit diagonal:
coeff i of h(c + y) = a_i + (polynomial in a_{<i}, c) (`Polynomial.taylor`). -/
theorem recenter_triangular ...

/-- **L6a, cell identification**: hull = P ⟺ (α) every diagram point on/above P and
(β) equality at the k vertex columns — both directions (brief L6a proof). Stated over
the `FaceKind`/`heights` data of §1.6, bridged to `L4.LatticePolygon`. -/
theorem hull_eq_iff_cell ...
/-- **L6a, volume** — REUSE: `LeanUrat.L4.cellVolume_eq` gives
(1 − q₀⁻¹)^k · q₀^{−N(P)} from (HAAR-COORD); this unit is the FaceKind → LatticePolygon
transport (N(P) = `newtonExponent`, k = `newtonVertexCount`). -/
theorem cell_volume ...
/-- L6c column classification: integer-height columns of face j are those at distance
t ≡ 0 mod b_j from its right endpoint; consecutive faces share EXACTLY the vertex
column x_{j+1}. -/
theorem intHeight_cols ...

/-- **L6e**: Z_e := (C_e\R_e) ∩ {a_e = 0}. (i) off Z_e the cells partition C_e\R_e
(every a_e ≠ 0 point in exactly ONE cell, no a_e = 0 point in any — the finite-hull
argument + (NP-SLOPES)); (ii) Z_e has measure ≤ q₀^{−t} for every t (HAAR-COORD),
and Z_2 = ∅; (iii) is a scope clause — recorded as the module docstring, not a unit:
nothing downstream consumes set-theoretic completeness. -/
theorem L6e_partition ...
theorem L6e_null ...
theorem L6e_empty_two ...

/-- L6′ display: each polygon stratum family's closed mass (the `massPoly` of §1.3)
is the finite Enum sum of (g3)-volumes × (g4)-closures with the L6b exponents
c_j ≥ 1 — the definitional tie massPoly ↔ (heights/Npg/cPrime data). The ANALYTIC
depth-sum evaluation (Σ_w at a real q₀) is Movement V's side of the seam. -/
theorem massPoly_enum_display ...
```

### 1.10 The named hypothesis rows (consolidated; the movement's honest conditionality)

| row | where | content | discharge path |
|---|---|---|---|
| **(B-INST)** `InstancePin` | §1.4 | realized `RegData` tables = a `BnMember` (dets + entry lists) | n=2: transcription from the machine-checked table (α₂ = (0,q−1)); n=3: OL-O12-2 (finite data pass); general n: D-11 (ROOT Step 17, Movement V's blueprint) |
| **(HAAR-COORD)** `SemanticRows.haar*` | §1.9 | per-coordinate valuation measure law + independence | the corpus convention (L4 `hfactor`); a future `PadicMeasure` bridge could discharge it — out of Movement II scope |
| **(NP-SLOPES)** `SemanticRows.npSlopes` | §1.9 | root valuations = polygon slopes | standard (Neukirch II.6); consumed only by L6e(i)/L1-last-sentence — off the pole-free path |
| **(TYPE-INV)** `SemanticRows.type*` | §1.9 | L2/L3 splitting-type preservation | VALUE-side, expressly outside the O-12 claim; consumed by Movements IV–V only |

Everything in §§1.1–1.8 is UNCONDITIONAL (Lean-core target). §1.9's theorems are
conditional exactly on the displayed rows above, matching the leaf's honest scope.

## 2. UNIT TABLE

Every unit ≤ ~40 lines of Lean. Difficulty: MECH (definition/transcription) < EASY
(one-idea proof) < MED (a real but bounded proof) < HARD (needs care; pre-decomposed).
"Source" = the paragraph of `O12_phaseB_verifybrief_rev4.md` (default) or ROOT.
Dependencies list unit ids + corpus imports (§3 keys in brackets).

### Core + Bookings

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| II-C1 | `qX`, `blockE`, `kappa0/1` defs | transcription | [U-B] | MECH | §2.2, §2.4 |
| II-C2 | `blockE_ge_three`, `two_le_blockE_sub_one` | unfold `e*(e+1)/2`; `Nat.le_div_iff_mul_le` + omega | II-C1 | EASY | §4 Thm1(3), Cor D |
| II-C3 | `kappa_add`: κ₀+κ₁ = q·q^{−E} | `field_simp` in `RatFunc ℚ` (qX ≠ 0 helper) | II-C1 | EASY | §2.4 display |
| II-C4 | `gram_kappa0/1` + `qX_pow_ne_zero` helpers | `Gram.poly`/`Gram.invS` composites via `Xpow_mem_cycS` | II-C1, [U-B] | MECH | §2.3 (g2) |
| II-B1 | `Booking` + `kernel` + `solveU` defs | transcription (e ≤ 1 guard = 0) | II-C1 | MECH | §2.4 |
| II-B2 | `kernel_one`, `Phi_one` | `simp [Booking.kernel]` | II-B1 | MECH | §2.2 block 1 |
| II-B3 | `Phi_*_eq`: the four Φ's are the landed dets | `field_simp`; `1 − q^{1−E} = (q^{E−1}−1)/q^{E−1}` etc. | II-B1, II-C2, [U-B detO*] | MED | §2.4, L7(iii) |
| II-B4 | `gcd_X_pow_sub_one` in ℚ[X] | Euclidean induction on (a,b): X^a−1 = X^{a−b}(X^b−1)+(X^{a−b}−1); search Mathlib first | — | MED | §4 Thm1(2) |
| II-B5 | `detO3_reduced`: q^E−q = (q−1)·q·Σ_{i<E−1}q^i | `geom_sum_mul` + ring | — | EASY | §4 Thm1(2) |
| II-B6 | `solve_O1_O2r` | rearrange to (1−κ₀−κ₁)x = s; divide by the unit (nonzero via II-C3 + evaluation or degree argument) | II-C3 | EASY | §4 Thm1(3) |
| II-B7 | `solve_O3` | multiply hbal by (1−κ₀) ≠ 0; reduces to II-B6's equation | II-B6 | EASY | §4 Thm1(3) |
| II-B8 | `solve_O2` | x(1−κ₀) = t; divide | II-C1 | EASY | §4 Thm1(3) |
| II-B9 | `det_one_sub_scalar_id`: det(1−κ·Id) = (1−κ)^k | `Matrix.det_diagonal`-shape (1−κ)•1 | — | EASY | §4 Thm1(1) parenthetical |
| II-B10 | `solveU_unit`: u is a nonzero ℛ-unit for e ≥ 2 | rewrite via II-B3 forms; `unit_of_cycS_ratio` | II-B3, [U-B] | EASY | §4 Thm1(3), L7(iii) |
| II-B11 | `selfloop_ge_two` + `kernel_ne_zero` | e ≤ 1 gives kernel = 0 (defn); e ≥ 2: q-power/quotient ≠ 0 | II-B1 | EASY | ROOT (SL≥2)(b)(c) |
| II-B12 | `no_interblock_cycle` | `Relation.TransGen` into < is irreflexive (wf descent) | — | EASY | ROOT (SL≥2)(a); L4 bounds via II-P8/R8 |

### Family / Theorem 2

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| II-R1 | `GramOver` inductive + `mono` + `Gram.gramOver` | mirror landed `Gram`; two induction walks | [U-B Gram] | MECH | §2.3 grammar |
| II-R2 | `GramOver.memRcyc` | induction; leaf case from hS; rest verbatim `Gram.memRcyc` | II-R1, [U-B] | EASY | §5 Thm2 absorption |
| II-R3 | `GramOver.finsetSum` / `.listProd` | `Finset.sum_induction` / list induction | II-R1 | EASY | §2.3(iv) 0/1 sums |
| II-R4 | `lowerLegs` + `BlockPresentation` structure | transcription | II-R1, [U0b] | MECH | §2.3(iv)(vii) |
| II-R5 | `beta_memRcyc` (the R-INDUCTION ENGINE) | `Nat.strong_induction_on e`; e ≤ 1 = hbase; step: `GramOver.memRcyc` with hS := IH on lowerLegs, then β = u⁻¹·t ∈ ℛ via hu | II-R2, II-R4 | MED | §5 Thm2 proof, (vii) |
| II-R6 | `massPatt` + `gram_massPatt` | (g1)·(g2)·(g2) product | II-C4 | MECH | §2.3(ii) |
| II-R7 | `massPoly` def + `gram_massPoly` | finite sum of (g3)·(g4) terms × (JC) factor; each a Gram composite | II-C4, II-F1 | MED | §2.3(iii), L6′ |
| II-R8 | `rowOf` + `gramOver_rowOf` | Finset sum over verdict tuples (Fintype [U0b]); products via `.listProd`; legs = `leaf` + `subst` | II-R3, II-R4, [U0b], [PowSubst] | MED | §2.3(iv) display |
| II-R9 | `AllocDatum` + `gramOver_allocAdjust` (∀ α ∈ ℚ[q]) | `.add` of `.mul (poly α) (invS q^E)` | II-R1 | EASY | §2.3(iv) O2 row; rev-4 repair V13-1 |
| II-R10 | `gramOver_o3scale` | `.mul` with the (g4)-shaped q^E/(q^E−1) | II-R1 | MECH | §2.3(iv)(v) O3 scaling |
| II-R11 | `weightSet` + `gram_weightSet` | finite list of (g2)/(g4) atoms | II-C4 | MECH | §2.3(v) |
| II-R12 | `BnMember` structure | transcription; docstring records the §1 scope + that composition/allocation data are member coordinates | II-R4, II-B1 | MECH | §2.3 closing, §1 |
| II-R13 | **THEOREM 2** `BnMember.entries_memRcyc` | II-R5 gives all β ∈ ℛ; `hentries` + II-R2 | II-R5, II-R12 | EASY | §5 Thm2 |
| II-R14 | `beta_leg_memRcyc` (every depth δ ≥ 1) | `MemRcyc.powSubst` on II-R13's β's | II-R13, [U-B] | MECH | §2.3(vi) |

### RegEmpty + Substochastic

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| II-G1 | `BnMember.toAbs` | transcription | II-R12, [U-B AbsSolveTable] | MECH | §1 frame |
| II-G2 | `BnMember.discipline` | dets: II-B2/B3/B10 + landed `detO*_unit` (e=0,1: Φ=1 unit); entries: II-R13 | II-G1, II-R13, II-B10 | EASY | §5+§4 |
| II-G3 | **THEOREM 3** `BnMember.regEmpty` | fire landed `regAt_primePow` | II-G2, [U-B] | MECH | §6 Thm3 |
| II-G4 | Corollary D `BnMember.detMargin` | II-B3 rewrite + landed `detO*_margin` + II-C2 | II-B3, [U-B margins] | EASY | §4 Cor D |
| II-G5 | `InstancePin` structure ((B-INST) row) | statement layer; fields finalized against `RegData` at E-phase; Codex plan-review REQUIRED (new trust surface) | II-R12, [RegPFinite] | MECH | ROOT Step 5 (B-INST) |
| II-G6 | `regP_of_pin`: pinned ⟹ `RegP D` at every prime | translate `RegAt` through the pin; (r2) agreement free via `RegPin.act_agree` pattern | II-G3, II-G5, [RegPFinite] | MED | §6 Thm3 + ROOT Step 4⊕5 |
| II-G7 | `regP_failing_empty_of_pin` | II-G6 + landed `regP_failing_eq` | II-G6, [RegPFinite] | EASY | ROOT Step 5 delivers-line |
| II-S1 | `det_one_sub_ne_zero` (Thm 4 nonvanishing) | Gershgorin `Matrix.det_ne_zero_of_sum_row_lt_diag`; nonneg ⟹ ‖M i j‖ = M i j | Mathlib | EASY | §6 Thm4 |
| II-S2 | `det_one_sub_pos` (Thm 4 positivity) | t ↦ det(1−tM) continuous (det = polynomial in entries), never 0 on [0,1] by II-S1 at scaled ε, = 1 at 0; IVT/connectedness | II-S1 | MED | §6 Thm4 |
| II-S3 | `bn_substochastic_margin` | kernel value = 1 − Φ value; II-G4 | II-G4 | MECH | §6 Thm4 closing |

### Polygon combinatorics (L6b + L4)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| II-P1 | `FaceKind` + `x`/`d` defs | transcription | — | MECH | §3 L6 setting |
| II-P2 | `SlopeTuple` + `heights` + `vertexHeight_int` | right-anchored partial sums; each face drops a_j·d_j ∈ ℤ | II-P1 | EASY | §3 L6 setting |
| II-P3 | `Npg` + `one_le_ceil_height` | slopes > 0, h_e = 0 ⟹ h_i > 0 for i < e; `Int.one_le_ceil_iff` | II-P2 | EASY | L6a closing |
| II-P4 | `elemMove_Npg` (L6b(i)): ΔN = c′_j = x_j·L_j + L_j(L_j+1)/2 | column gains: 0 right of face j, t at distance t, L_j left; `Int.ceil_add_intCast`; `Finset.sum` split by region + Gauss sum | II-P3 | HARD | L6b(i) proof |
| II-P5 | `aMin_shift`: a^min(s+1) = a^min(s) + b | bijection a ↦ a − b of the residue class; minimality both ways | II-P2 | EASY | L6b(ii) proof |
| II-P6 | `gapStep_Npg` (L6b(ii)): unit w_j step ⟹ ΔN = c_j = Σ_{j′≤j} c′_{j′} ≥ 1; k w-independent | compose II-P4 across the shifted nested minima (II-P5), right-to-left induction on j | II-P4, II-P5 | HARD | L6b(ii) proof |
| II-P7 | `singleFace_finite` | a_k ranges in Finset.Ico 1 b_k | II-P2 | EASY | L6b(ii) k=1 |
| II-P8 | `faceDeg_bound` + `handoff_mu_lt` + `patt_mult_lt` (L4 arithmetic) | rightmost: d = L/b ≤ e/2 < e (b ≥ 2); others: L ≤ e − L_k ≤ e − 2; μ ≤ μD ≤ d; L4(i): atom (D,m) with m = e forces D = 1 = excluded | II-P1 | EASY | L4 proof |

### Fact F + Torus (the Step-17 count handoff)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| II-F1 | `Mpoly`/`fallingFac`/`Npoly`/`Ppoly` defs | transcription (Multiset.prod over atom groups) | — | MECH | §2.3 count polys |
| II-F2 | `gram_Npoly` (+Ppoly) — (g1) status | `Gram.poly` | II-F1, [U-B] | MECH | §2.3(ii) bracket |
| II-F3 | `patternOf` + `patternOf_smul_unit` | `UniqueFactorizationMonoid.normalizedFactors`; units don't change normalized factors | Mathlib | MED | L6d orientation ¶ |
| II-F4 | X^{q^D} − X = ∏ irred of deg ∣ D, squarefree | derivative = −1 ⟹ squarefree; dvd direction landed in Mathlib (`Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`); converse via `FieldTheory/Finite/Extension` roots; split into ≤3 sub-lemmas in-file if >40 lines | Mathlib | HARD | Fact F(i) proof |
| II-F5 | q^D = Σ_{δ∣D} δ·I_δ | degrees of II-F4's product; `Polynomial.natDegree_prod` | II-F4 | EASY | Fact F(i) proof |
| II-F6 | **Fact F(i)** `card_monicIrreducible_eq` | Möbius inversion `Nat.ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq` on II-F5; cast ℕ→ℚ; tie to `Mpoly.eval` | II-F5 | MED | Fact F(i) |
| II-F7 | `distinct_choice_count` ((M)_r/∏c!) | pure Fintype counting: ordered distinct choices (M)_r quotient by within-multiplicity permutations; CHECK `O5CountingB` for the abstract lemma first | Mathlib, [O5CountingB?] | HARD | Fact F(ii) proof |
| II-F8 | **Fact F(ii)** `card_pattern_eq` | factorization ↔ per-degree distinct choices + multiplicity assignment; product over D; II-F6 supplies M_D, II-F7 the per-degree count | II-F6, II-F7, II-F3 | HARD | Fact F(ii) |
| II-F9 | **Fact F(iii)** `card_pattern_zfree_eq` | remove z from the degree-1 supply (only monic irred with 0 constant term is z); rerun II-F8's count with q−1 | II-F8 | EASY | Fact F(iii) |
| II-T1 | **(T1)** `torus_count` | the displayed two-sided bijection R ↦ lead(R)⁻¹R, S ↦ (c/S(0))S; `Finset.card_bij`; pattern invariance II-F3 | II-F3, II-F9 | MED | L6d Step 1 |
| II-T2 | `chain_telescope` (abstract) | induction on k: sum V_1 first via hrow (c-independent), pull out P_1, recurse | — | MED | L6d Step 2 |
| II-T3 | `jc_count` = ∏ P_{ρ_j}(q) | instantiate II-T2 with interior-coefficient counts n_j; hrow from II-T1; anchor c = 1 | II-T1, II-T2 | MED | L6d Step 2 |
| II-T4 | `jc_prob` + independence | divide by (q−1)^k·q^{Σ(d_j−1)}; (q−1)q^{d−1} = q^d − q^{d−1}; marginals by re-running II-T2 with one face unsummed | II-T3 | EASY | L6d Step 3 + consistency ¶ |
| II-T5 | `zfree_total`: Σ_ρ P_ρ = q^d − q^{d−1} | partition all monics with nonzero constant term by pattern; II-F9 | II-F9 | EASY | L6d consistency ¶ |

### Semantic layer (rows-conditional; Step-17 handoff)

| id | statement | proof sketch | deps | diff | source |
|---|---|---|---|---|---|
| II-M0 | `SemanticRows` structure (the displayed rows table §1.10) | statement layer ONLY; semantic-guardian audit + Codex review REQUIRED before provers consume | — | MECH | §2.1, L1–L3 |
| II-M1 | `val_esymm_ge` | `Multiset.esymm` expansion; nonarch bound on sums/products of valuations | Mathlib Valuation | MED | L1 (⇒) |
| II-M2 | `val_esymm_min_eq` | unique strict-minimum term: v(sum) = min when one term strictly smallest (`Valuation.map_add_eq_of_lt` chain over the k-subsets) | II-M1 | HARD | L1 (⇐) |
| II-M3 | `L1_root_coeff` (i)+(ii) + ℤ-snap | assemble II-M1/M2; v(a) ∈ ℤ_{≥0} forces > 0 ⟹ ≥ 1 | II-M1, II-M2 | EASY | L1 |
| II-M4 | `rescale_coeff` (L2 algebraic half) | `Polynomial.scaleRoots`/direct coeff computation of g(πy)/π^e | Mathlib | EASY | L2 proof |
| II-M5 | `recenter_triangular` (L3 algebraic half) | `Polynomial.taylor` coefficients: a_i + poly(a_{<i}, c) | Mathlib | MED | L3 proof |
| II-M6 | `hull_eq_iff_cell` (L6a identification) | (α)+(β) ⟺ hull = P, both directions per the displayed convexity argument; split forward/converse in-file | II-P2, II-P3 | HARD | L6a proof |
| II-M7 | `cell_volume` (L6a volume) | WRAPPER on landed `L4.cellVolume_eq`: FaceKind→LatticePolygon transport, N(P) = `newtonExponent`, k = `newtonVertexCount` | II-M6, [L4/BB1] | EASY | L6a display |
| II-M8 | `intHeight_cols` (L6c classification) | t·a_j/b_j ∈ ℤ ⟺ b_j ∣ t (coprimality); ranges intersect in {x_{j+1}} | II-P2 | EASY | L6c proof |
| II-M9 | `L6e_partition` | a_e ≠ 0: finite-hull is the diagram hull; (NP-SLOPES) row + g ∈ C_e\R_e pin admissibility; uniqueness via II-M6; a_e = 0: column-0 equality impossible at v = ∞ | II-M6, II-M0 | HARD | L6e proof (i) |
| II-M10 | `L6e_null` + `L6e_empty_two` | measure ≤ q₀^{−t} ∀t from haarBall; e = 2: a_2 = 0 ∧ v(a_1) ≥ 1 ⟹ g ∈ R_2 | II-M0, II-M3 | EASY | L6e proof (ii) |
| II-M11 | `massPoly_enum_display` (L6′ tie) | definitional: massPoly's (cs, enum) instantiated from Npg/cPrime data; per-cell = II-M7 | II-R7, II-P6, II-M7 | MED | L6′ |

**Unit count: 63** (12 core/bookings, 14 family, 10 reg/substochastic, 8 polygon,
14 FactF/torus, 12 semantic — counting II-M0). Mandatory pole-free path (ROOT Step 5's
own delivery) = C+B+R+G+S+P8 ≈ 37 units, ALL unconditional; the rest is the
Step-17 mass-lemma handoff Step 5 carries ("Includes the semantic mass lemma base
L1–L6′/Fact F that Step 17 consumes").

## 3. CORPUS-REUSE MAP

| key | declaration(s) | discharges |
|---|---|---|
| [U-B] `MovesU/O12PoleFree.lean` | `cycS`, `X_mem_cycS`, `Xpow_sub_one_mem_cycS`, `Xpow_mem_cycS`, `cycS_eval_pos` (L5/"Lemma RR"), `MemRcyc` + `.add/.mul/.neg/.sub`, `memRcyc_algebraMap`, `memRcyc_inv_cycS`, `MemRcyc.definedAt` (L7(i)), `MemRcyc.eval_ne_zero_of_inv` (L7(iii)), `cycS_expand`+`MemRcyc.powSubst` (L7(ii)), `Gram`+`Gram.memRcyc`, `eval_ratio`, `marginO1/O2/O3`, `detO1/detO2/detO3`+`_unit`+`_margin`, `unit_of_cycS_ratio`, `AbsSolveTable`+`RegAt`+`RcycDiscipline`+`regAt_of_discipline`+`regAt_primePow` | the WHOLE abstract layer: II-C4, II-B3/B10, II-R2, II-G1–G4 lean on it; Theorem 3's mechanism is landed |
| [RegPFinite] `MovesU/RegPFinite.lean` | `RegP`, `RegData`, `RegData.detFull`, `regP_iff_pool_avoids`, `RegPin.act_agree`, `regP_failing_eq`, `regP_failing_finite`, `regP_cofinite` (Step 4 = M17 A/B/C/U) | II-G5–G7 (the seam); Step 4 needs NO new units |
| [Defs] `MovesU/Defs.lean` | `DefinedAt`, `SplittingType`, `RegData` | vocabulary everywhere |
| [U0b] `MovesU/U0b_splitTypeFintype.lean` | `instSplittingTypeFintype`, `instSplittingTypeDecEq` | II-R4/R8/R9 verdict Finset sums |
| [PowSubst] `MovesS/PowSubst.lean` | `powSubst`, `powSubst_X`, `powSubst_C` | (g5) legs: II-R1 subst, II-R14 |
| [L4/BB1] `LeanUrat/L4.lean` | `LatticePolygon`, `newtonExponent`, `newtonVertexCount`, `bb1Value`, `cellVolume_eq`, `cellVolume_pIndependent` | II-M7 (L6a volume) LANDED up to transport; also the `hfactor` recorded-via-hypothesis precedent for II-M0 |
| [conv] `R1.stratum_volume`, `L2core.perShapeVolume_baseChange` | the hypothesis-row convention precedent | II-M0 design authority |
| [O5CountingB?] `MovesU/O5CountingB.lean` | abstract counting lemma (O5triple Thm B) | CANDIDATE for II-F7 — division lead checks at E-phase before assigning a prover |
| Mathlib | `Matrix.det_ne_zero_of_sum_row_lt_diag` (Gershgorin); `Nat.ArithmeticFunction` Möbius inversion (`.../Moebius.lean`); `FiniteField.X_pow_card_pow_sub_X_natDegree_eq`, `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`, `FieldTheory/Finite/Extension`; `UniqueFactorizationMonoid.normalizedFactors`; `geom_sum_mul`; `Int.ceil_add_intCast`; `Polynomial.taylor`, `Polynomial.scaleRoots`; `Relation.TransGen` wf | II-S1, II-F4–F6, II-F3, II-B5, II-P4, II-M4/M5, II-B12 |

NOT reused (checked, different content): `KsubGeneral`, `SkeletonFinite` (O-13),
`R7_runRealizer`, `HK11a_vertexTransport`, `UE_vtxUpper`, D-SC slots, `hExhaust_n2` —
those are Movements I/III/IV quarry.

## 4. WAVE PLAN (for the division lead)

Per-file gates during waves; `lake build` + `lake env lean LeanUrat/AxChk_baseline.lean`
at each checkpoint (footprint regression = stop-the-line).

* **Wave 0 — defs + statement layer (all MECH, fully parallel, no deps):**
  II-C1, II-B1, II-R1(def only), II-R4, II-R12, II-P1, II-F1, II-M0(statement), II-G5(statement).
  GATE before Wave 1: Codex plan-review of the two trust surfaces (II-M0 rows,
  II-G5 pin fields) + orchestrator sign-off that `BnMember`/`BlockPresentation`
  faithfully transcribe brief §2.3 (the dedup-audit new-declaration check applies:
  every new decl here is a transcription of a displayed brief object).
* **Wave 1 — the easy algebra (parallel after Wave 0):**
  II-C2, II-C3, II-C4, II-B2, II-B5, II-B6, II-B7, II-B8, II-B9, II-B11, II-B12,
  II-R2, II-R3, II-R6, II-R9, II-R10, II-R11, II-P2, II-P3, II-P5, II-P7, II-P8,
  II-F2, II-S1.
* **Wave 2 — the spine (needs Wave 1):**
  II-B3, II-B4, II-B10, II-R5 (the engine — assign the strongest prover), II-R7,
  II-R8, II-R13, II-R14, II-G1, II-G2, II-G3, II-G4, II-S2, II-S3, II-T2, II-M4,
  II-M5, II-M8.
  **CHECKPOINT: Theorems 2 + 3 + 4 + Corollary D compiled = ROOT Step 5's pole-free
  clause formalized at 𝔅_n.** Commit + AxChk.
* **Wave 3 — the hard cluster (parallel tracks):**
  (a) counts: II-F3 → II-F4 → II-F5 → II-F6; II-F7 → II-F8 → II-F9 → II-T5;
  (b) torus: II-T1 → II-T3 → II-T4;
  (c) polygon: II-P4 → II-P6;
  (d) L1: II-M1 → II-M2 → II-M3.
  HARD units get the bounded-repair rule (3 attempts, then back to the division lead
  with the exact obstruction; splitting a HARD unit into sub-lemmas is allowed and
  expected, statements unchanged).
* **Wave 4 — semantic assembly + seam (needs Waves 2–3):**
  II-M6 → II-M7 → II-M9, II-M10, II-M11; II-G6 → II-G7.
  **CHECKPOINT: full Movement II. Commit + AxChk + update `docs/PROJECT_STATE.md`.**

Estimated prover-agent load: ~63 units ⇒ ~70–80 prover runs (HARD units may split).

## 5. Sync duty + honesty notes

* **Math-revision sync:** if O-12 revs past rev 4 (or ROOT past REV 5 touches Step 5's
  (SL≥2)/(B-INST) displays), the deltas land here first. Watch items: OL-O12-2's data
  pass (would let II-G5's n=3 pin be DISCHARGED rather than hypothesized), D-11's pin
  (Movement V's blueprint owns the general-n discharge), any change to the allocation
  datum display (II-R9 quantifies over ALL α ∈ ℚ[q] — robust to it).
* **Never claim past the leaf:** the compiled Theorem 3 is about `BnMember`s; any
  progress report must say "at the abstract solve family 𝔅_n, realized tables behind
  the `InstancePin` row". Value correctness is NOT touched by any unit here.
* **No statement weakening:** the (SL≥2) display units (II-B11/B12) exist to make the
  e = 1 vacuity a THEOREM, not a convention — do not fold them into definitions.
* Numeric falsifiers already on record (18,120 prime powers + 303 primes < 2000 via
  D-11's run; `verification/openmath/O12_rev4_checks.py` 12/12) — provers hitting a
  seemingly-false subgoal should suspect the TRANSCRIPTION, not the math, and escalate.

