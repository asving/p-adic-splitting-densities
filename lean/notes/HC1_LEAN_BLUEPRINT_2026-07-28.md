# HC1 LEAN BLUEPRINT — §B2-DEF's tower induction — REV 2 (2026-07-28)

AUDIT TRAIL: rev 1 → fresh-Fable REJECT 3 crit / 6 gap
(`HC1_AUDIT_FABLE_2026-07-28.md`; every critical machine-confirmed, computations
re-verified against the note and disk at this revision). REV 2 folds all nine findings:
C-1 (the κ double-count → the note's EXCLUSIVE-STR convention, §2.2 + `strTop`
re-thread through T3/T6/the C-layer), C-2 (S1's unsatisfiable increment gate → the
degree-1 base inside ambient F₄, satisfiability re-derived by explicit construction),
C-3 (G4's wrong both-rise algebra → `d₀ = d₁²`, decide gates CONTENT-pinned on element
lists per the campaign order-discipline precedent), G-1–G-6 (the §4 re-census against
disk — four rev-1 dep-sorries were already CLOSED at this blueprint's own commit —
plus the 4.5/4.6 repair-spec corrections, the §2.2 recorded-decisions paragraph, C6's
full dichotomy, T9's de-trivialization, S12's quantifier pin). Dispositions in §1.1.

*Hard-core #1 blueprint (Fable writer, wave 5 of the campaign master plan
`LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`). GROUND TRUTH: the dual-accepted §B2-DEF
text `MOVES_2026-07-24.md` 1849–2745 (D.0–D.12) + the §C displays 3644–3831 (Lemma DOM
3644, Lemma LST 3728, Lemma TYP 3783) + the pass-7 carry-algebra spec 1502–1530.
BUILDS OVER: `lean/LeanUrat/Moves/` (the census document
`MOVES_LEAN_FINAL_CENSUS_2026-07-26.md` predates the repair wave; DISK at REV 2:
the tail is down to `L6_measureExact_R4`'s two sorries + the not-consumed
superseded files — the §4 re-census is normative), `lean/LeanUrat/MovesGr/`
(19 proved + 2 sorried + 5 held, option-(a) `add_def` landed), `lean/LeanUrat/MovesC/`
(36/36, the Line/DomData/LevelClause layer), and the PARKED `MovesR` CInterface
(`MOVESR_LEAN_BLUEPRINT_2026-07-28.md` §1, `GradedCarrier`/`ReBased`) whose REAL
construction this corpus OWNS per the wave-5 resumption charge.*

DELIVERABLE: `lean/LeanUrat/HC1/` — the carry algebra 𝒟 as a concrete object; the
REAL graded carriers (chain weights, in_γ, the D.3(e) pieces, alphabets, floors);
LST/TYP/DOM as THEOREMS over them; the per-level transport bijections; the induction
spine constructing every tower level's stage package from the Moves move-ledger; the
e_birth/e_read threading; the sealed-gate decide/eval checks. 54 units.

## 0. Design decisions (stated once, each with its warrant)

**(D1) The graded ring is MovesGr's; the carry algebra is DERIVED, not primitive.**
§B2-DEF's structural decision (MOVES 1855–1861): work inside gr_w(A) and its monomial
localization; "the pass-7 carry algebra is CONSTRUCTED below (D.7(v)–(vi)), not
postulated". So HC1 keeps MovesGr's `SideVal`/`grPiece`/`pmul`/`initialForm` as the
engine and introduces 𝒟 = F[u]/(u^e − z̄) (pass-7 spec, MOVES 1508–1514) as the
PORTABLE digit-arithmetic object: the algebra where a coefficient class's (S5) digit
`c·z^k` lives as `u_{k mod e}`-homogeneous data, products carry via the cocycle, and
the e_birth threading is typed. Units prove 𝒟's algebra facts and the DIG
homomorphism from `Stage` digits; nothing downstream postulates them.

**(D2) Towers are EXPLICIT: a `Tower` is a base stage + a list of move witnesses.**
The induction "at every tower level" needs the object it inducts along. `Tower p F`
carries `stg : Fin (K+1) → Stage p F`, a faithful base pin (D5 below), and per-level
`MoveWitness` = increment (full D.3–D.7 hypothesis interface `TransHyp` +
`TransitionCoreL`) or recentering (`IsRecenteringCore` — the reps/Tvec-recording
form, per the MovesGr L5 fence). The spine theorem gives `StageCoreL (T.stg k)` for
every k. Consumers quantify over towers; no "abstract history" type rides.

**(D3) Heights and carriers live at the TOWER, in absolute v_p-scale, ℚ-valued.**
Chain weight `ht(c) = l + Σ_r innerslot_r(c)·κ_r`, κ_r = h_r/(e_r·STR_r) fixed at the
read that augmented level r (LST head, MOVES 3731–3735) — **with the note's EXCLUSIVE
STR convention** (audit C-1): STR_r := e₀·…·e_{r−1}, the stretch accumulated BEFORE
level r's read, STR₀ = 1 (LST base 3752: "w(x) = h₀/e₀ = κ₀ (STR₀ = 1)"); so
κ_r = h_r/(e₀·…·e_r) with each e counted ONCE. The frame conversion factor is a
SEPARATE object, `strTop := STR_K·e_K = e₀·…·e_K` (C.1.0(c)'s frame str: "the product
of the history's stretches down to that frame" — inclusive of the last read; the
exclusive/inclusive seam is exactly where rev 1 double-counted). The MovesR
`GradedCarrier` indexes `Gr : ℚ → Type`; the real instance sets
`Gr γ := S.grPiece ⌊strTop·γ⌋` (S = the top stage's SideVal): on-lattice γ hits the
genuine stage-scale piece; off-lattice γ has `inγ γ := 0` and no weight ever equals
it, so `inγ_kills`/`inγ_detects` hold with no junk (recorded, auditable convention).

**(D4) The MovesGr fences are LOAD-BEARING inputs, not obstacles.** The three
machine-checked certificates (`MOVESGR §8.2`) shape HC1's statements: (i)
`baseStage_exists` is VACUOUS with `wPrev = 0` ⟹ HC1's base pin is the faithful D.2
bundle (`IsBaseStage`: wPrev = the Gauss valuation, reps = [C p], K = FQ); (ii)
`TRANSstage` is FALSE at e′ = 0 ⟹ `TransHyp` carries 1 ≤ e′, 1 ≤ h′, gcd = 1,
`IsStandardLift`, ψ monic irreducible ≠ X, `IAug` — the D.3/D.7 interface IN the
hypothesis, so the ∃-statement quantifies only over legal reads; (iii) `recTRANSRS`
is only-vacuously-provable from bare `IsRecentering` ⟹ HC1 consumes
`IsRecenteringCore` (DefsCore §7: `reps_eq`/`Tvec_eq`) everywhere.

**(D5) The base stage is CONSTRUCTED at the Gauss valuation, then gated concretely.**
Unit T1 builds `Stage p F` for a base read (e, h) over `wPrev = gaussVal` (§A/§B1
re-expressed, MOVES 1992–2015), discharging its `Stage` fields from the Moves L1
layer (`L1_gaussVal`, `L1_baseResidual_R4`, `L1_baseWeight_R3` — ALL clean on disk;
rev 1's dep-sorry tag was stale, §4 re-census). Unit T2 inhabits it at p = 2,
F = GaloisField 2 2, φ = X² + X + 1 — the honest replacement for MovesGr's held
`L4_base_nonvacuity_gate`. A SECOND base instance — the degree-1 pin φ = X,
(e,h) = (1,1), K = the prime subfield F₂ inside the same ambient F₄ — is
constructed in S1 as the increment gate's base (audit C-2: over T2's own base
K = F₄ = F, NO degree-≥2 TransHyp is inhabitable at all — see §1.1).

**(D6) e_birth vs e_read is a TOWER function, threaded through 𝒟.** Per level k ≥ 1,
`eBirth T k` := the e′ of the increment that created level k's coefficient algebra;
recenterings PRESERVE it (they replace the current key, never the coefficient
algebra — D.10/TRANS-RS: "same C, same v, same T"). A key born at e_birth > 1 read
later at e_read = 1 keeps nontrivial ℤ/e_birth anchor cosets (the pass-7 critical 2,
MOVES 1478–1499); HC1 types this as: the DIG map lands in `CarryAlg F (eBirth T k)`,
and the substitution/landing units (S15/S16) run the D.10 substitution WITH the coset data
visible — the ledger reads e_read = 1 stages' digits at position 0 (P2), but the
𝒟-typing is what makes the rerun's carry bookkeeping well-formed at e_birth > 1.

**(D7) LST/TYP/DOM are theorems over the REAL carriers; the MovesR statement defs
get RE-KEYED to match, with the four audit repairs built in.** Per the wave-5
resumption charge (campaign ledger, MovesR PARKED entry) + `MOVESR_AUDIT_FABLE3`:
(i) TYP's additive object = the level-set-digits → graded-piece COMPOSITE
`(y_c)_c ↦ Σ_c y′_c·in(m_c)` (MOVES 3801–07, 9401–04), additive in the digit tuple —
NEVER the jet map on box points (F3-1: additivity on (O_δ, +) is p^N-torsion-impossible);
(ii) alphabets are priced on the slot-image SPAN in the graded piece, not the
digit-value set (F3-2; TYP(b) 3815–21; the F₉ a = 2 instance is gate G5);
(iii) `floorB` is DEFINED from the history's lines via a block-edge map + the
staircase equation (F3-3) — in HC1 it is a construction, so the free-field defect
cannot recur; (iv) the four gaps: slotCoeff additivity stated at the graded-piece
level (G3-1), a window predicate scoping (i-b)/(i-c) (G3-2), DOM stated as the
DISPLAYED conclusion line_i ≥ line_m on the per-i interior (G3-3), EQ-2's
conditionality on the ∀-instance pass (G3-4).

**(D8) One move is measure-exact; composition is §C — the scope fence stands.**
D.11's own scope clause (MOVES 2716–2718): "Statement scope: ONE move. The
composition of moves along a read history is §C — deliberately NOT claimed here."
HC1's spine delivers D.11 AT EVERY LEVEL of any tower (each level's move, stratum →
landing cylinder, measure-exact) with the stage hypotheses DISCHARGED by the
induction instead of assumed. The §C composition stays MovesC's (proved over
JetSetup); the JetSetup instantiation from these carriers is HC-2's seam (§5).

**(D9) NO new axioms — this is our own mathematics.** §B2-DEF's literature note
(MOVES 2738–2743): D.1–D.7 are the graded-algebra formulation of MacLane–Vaquié/GMN
but "proved self-contained here because the ledger content … has no published
digit-level counterpart". Accordingly HC1 declares ZERO published-axiom candidates
and must not import `MontesAxiom`'s GMN axiom or `PadicMeasure`'s cell axioms into
any unit's footprint (verify leg: Lean-core only, per unit). Open obligations ride
as hypothesis fields or named `sorry`-fenced deps (§4), never as axioms.

## 1. The fences and criticals this blueprint is REQUIRED to respect

| fence | source | HC1 consequence |
|---|---|---|
| `baseStage_hbase_empty` (wPrev = 0 base VACUOUS) | MovesGr §8.2 cert | `IsBaseStage` = Gauss-valuation bundle (T1) |
| `transitionCoreL_e0_false` (e′ = 0 kills TRANSstage) | MovesGr §8.2 cert | `TransHyp` carries 1 ≤ e′,1 ≤ h′,gcd,lift,ψ-irr,IAug (S1) |
| `recTRANSRS_only_vacuous` (bare IsRecentering strips reps) | MovesGr §8.2 cert | recentering units consume `IsRecenteringCore` (S17) |
| `L4_TRANSvi` held: child T-law not from (ht,M′) alone | MovesGr §8.2 | child TvecUnitLaw derived from parent `StageCoreL.tvec_unit` + `child_Tvec` (S8) |
| F3-1: jet additivity group-impossible | MOVESR_AUDIT_FABLE3 | TYP typed on the composite, digit-tuple-additive (C2, R2) |
| F3-2: value-set pricing contradicts a = 2 | MOVESR_AUDIT_FABLE3 | span pricing (T7/C3/C6, R2); gate G5 |
| F3-3: floorB free field | MOVESR_AUDIT_FABLE3 | `floorB` DEFINED via `blockEdge` + staircase eq (T10, R1) |
| G3-1..G3-4 | MOVESR_AUDIT_FABLE3 | built into R1–R5 as stated in D7 |
| D.11 one-move scope | MOVES 2716 | no composition claim anywhere in HC1 (D8) |
| statement fence | parent CLAUDE.md | Moves/MovesGr/MovesC statements untouched; MovesR re-key = the authorized wave-5 charge, re-audit required |

DOCTRINE (wave-3+ prompts carry it, campaign ledger): every interface below must be
FALSE for instances the note would reject; obligations may be open, but their TYPES
pin their content. Per-structure falsifiability notes are given inline (§2).

### 1.1 The rev-1 audit findings (`HC1_AUDIT_FABLE_2026-07-28.md`) — REV-2 dispositions

All nine findings folded; the three criticals were machine-confirmed by the auditor
and re-verified against the note/disk at this revision. These rows now BIND this
blueprint exactly like the §1 fences.

| finding | content (one line) | REV-2 disposition |
|---|---|---|
| C-1 | κ formula double-counted e_k (exclusive-STR formula pasted onto an inclusive STR; κ₀ = 1/4 instead of 1/2 at (e₀,h₀) = (2,1)) | §2.2: `Tower.str` = the note's EXCLUSIVE STR (STR₀ = 1); κ_k = h_k/(e_k·STR_k) verbatim; NEW `Tower.strTop` = STR_K·e_K carries the frame conversion; T3's factor, T6/carrier's reindexing, C2's δ' re-threaded to strTop |
| C-2 | S1's gate unsatisfiable: z²+z+1 is REDUCIBLE over F₄ (roots = the cube roots of unity), and over T2's base K = F₄ = F no g ≥ 2 TransHyp exists (hirr + hroot force [K(z̄):K] = g ≤ [F:K] = 1) | S1(a) re-based: degree-1 base (φ = X, K = F₂) inside ambient F₄; ψ = z²+z+1 now genuinely irreducible over K; z̄ = a primitive cube root in F₄ˣ; satisfiability re-derived clause by clause in-unit. RECORDED CONSTRAINT: any increment gate needs [F : K] ≥ g |
| C-3 | G4's both-rise predicate d₀ = d₁³ contradicts the seal's d₀ = d₁² (char-3 double root forces τ = d₁, d₀ = τ² = d₁²); both sets have card 8, so a count-only decide passes SILENTLY on the wrong algebra | G4 predicate fixed to d₀ = d₁²; ALL G4 decide legs CONTENT-pinned — finite-set EQUALITY against explicit element lists, cardinalities only as corollaries (the campaign order-discipline precedent; the v1-seal adjudication at MOVES 2934 is the warrant) |
| G-1 | §4 ledger stale at the blueprint's own commit: 4.1/4.2/4.4 were already proved (35bf18a, 4b29f6e); 4.3's cone repaired | §4 re-censused against disk: 4.1–4.4 CLOSED (entries retained with their landing commits); phantom `dep-sorry:` tags dropped from T1, S12, C4, S16; only 4.6's pair remains open |
| G-2 | 4.5's gloss ("ord_z of the vertex slot term = 0") is NOT the file's clause and is FALSE by rev-D¹¹ F4 (the anchor is the ord of the SUM); the repair already LANDED fence-safe (`L5_landTwoSided_repair.lean` :755, hexact hypothesis); 4.6's ":143 resolves with 4.5" wrong — the inlined lemma lacks the clause and needs it THREADED | §4.5 rewritten: RESOLVED-fence-safe, citing the landed repair theorem and the correct clause `¬ X ∣ Σ_j Cdig j·ψ^j` (the digit TOTAL); S16/S17 thread `hexact` as a stratum-side hypothesis; §4.6's :143 spec = restate the inlined lemma + L6_measureExact's hypotheses WITH the clause (sign-off), then import the repair |
| G-3 | `Coord`/`slotBound`/`kappa`/root-`eBirth` underspecified (top-level slot bound not tower data; recentered levels implicit; κ total; root convention unrecorded) | §2.2's RECORDED DECISIONS paragraph pins all four |
| G-4 | C6 stated only the sufficient direction, dropping the note's "exactly when" + "STRICTLY SMALLER at shallow heights" | C6 upgraded to the full dichotomy (iff + strict inequality on the unattainable side), per MOVES 2160–2165 |
| G-5 | T9 as re-typed was definitionally trivial; the note's leaf-partition content (disjoint leaf subtrees, "no two equations of one system pin the same digit coordinate") uncertified | T9 gains leg (b): the mixed-radix leaf-address injectivity — the content S17's ledger counting consumes |
| G-6 | S12's "(I-aug) holds at every read" ambiguous between the projection-trivial reading (TransHyp carries hiaug) and the substantive D.4 derivation | S12 pinned to the D.4 derivation form: every side of every landing's child polygon available to the next read, per D.4's three bullets |

## 2. Defs skeleton (normative for CONTENT; E-phase fixes syntax only; statement
fence applies from acceptance)

Namespace `LeanUrat.HC1`; `open LeanUrat.Moves LeanUrat.MovesGr` (and `MovesC` in
DefsCar). Ambient conventions as Moves: `p : ℕ` `[Fact p.Prime]`, `F : Type u`
`[Field F] [Finite F]`, coefficient ring `A := Polynomial ℤ_[p]`.

### 2.1 `HC1/DefsD.lean` — the carry algebra 𝒟

```lean
/-- **The carry algebra 𝒟 = F[u]/(u^e − z̄)** (pass-7 spec, MOVES 1508–1514), as the
concrete graded function object `ZMod e → F` with the cocycle product. `zbar` enters
through the multiplication only. Requires `NeZero e` (e ≥ 1; e = 0 is note-rejected —
no read has denominator 0). -/
def CarryAlg (F : Type u) (e : ℕ) : Type u := ZMod e → F

variable {F : Type u} [Field F] {e : ℕ} [NeZero e] (zbar : Fˣ)

/-- the 2-cocycle: 1 iff adding the canonical representatives overflows e. -/
def carryExp (ρ σ : ZMod e) : ℕ := if e ≤ ρ.val + σ.val then 1 else 0

/-- twisted convolution: `(x * y) τ = Σ_{ρ+σ=τ} x ρ · y σ · z̄^{carryExp ρ σ}`. -/
noncomputable def cmul (x y : CarryAlg F e) : CarryAlg F e :=
  fun τ => ∑ ρ : ZMod e, x ρ * y (τ - ρ) * (zbar : F) ^ carryExp ρ (τ - ρ)

/-- homogeneous generator `u_ρ` with scalar c: `Pi.single ρ c`. -/
def dOf (ρ : ZMod e) (c : F) : CarryAlg F e := Pi.single ρ c

/-- homogeneity: supported on one coset. -/
def IsHomog (x : CarryAlg F e) (ρ : ZMod e) : Prop := ∀ σ, σ ≠ ρ → x σ = 0
```

Falsifiability: `carryExp` is FORCED (⌊(ρ.val+σ.val)/e⌋ for representatives < e is
exactly this indicator); a wrong cocycle breaks unit D1's associativity — the
structure cannot silently degenerate. The `CommRing (CarryAlg F e)` instance is
unit D1's construction (addition pointwise, `1 = dOf 0 1`), NOT a Defs field.

```lean
/-- **The DIG map** of a stage's coefficient digit into 𝒟 at the BIRTH index
(D6 threading): `R B = c·z^k` (S5) ⟼ the `u_{k mod e_b}`-homogeneous element whose
scalar is the ALIGNED residual class `c·z̄^{(k − k mod e_b)/e_b}` evaluated at zbar.
Total on A: 0 off the (S5) shape. -/
noncomputable def Stage.digD (σ : Stage p F) (zbar : Fˣ) (e_b : ℕ) [NeZero e_b]
    (B : Polynomial ℤ_[p]) : CarryAlg F e_b := ...
  -- from σ.R B via LaurentPolynomial data: position k := −σ.t * σ.wPrev B,
  -- coset ρ := (k : ZMod e_b), scalar := σ.digPrime zbar B aligned by zbar^((k − ρ.val)/e_b)
```

### 2.2 `HC1/DefsTower.lean` — towers, moves, birth indices

```lean
/-- The FULL D.3–D.7 increment hypothesis interface (the TRANSstage fence, D4(ii)):
everything the note requires of a legal read, nothing more. FALSE at e′ = 0, at
ψ = X (the note's ψ ≠ z), at reducible ψ, at a non-(I-aug) side. -/
structure TransHyp (σ : Stage p F) (ψ : Polynomial ↥σ.K) (g : ℕ)
    (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) (zbar : Fˣ) : Prop where
  hmonic : ψ.Monic
  hirr : Irreducible ψ
  hne_z : ψ ≠ Polynomial.X          -- ψ ≠ z (D.3 head)
  hdeg : ψ.natDegree = g
  hg : 1 ≤ g
  hlift : IsStandardLift σ ψ g Φhat -- D.5's displayed formula (Moves Defs)
  he' : 1 ≤ e'
  hh' : 1 ≤ h'
  hcop : Nat.gcd e' h' = 1
  hiaug : IAug σ Φhat e' h'         -- h′ > e′·w(Φ̂) (D.4/D.7 head)
  hroot : Polynomial.aeval (zbar : F) (ψ.map σ.K.subtype) = 0  -- z̄ a root of ψ in F

/-- One tower move: an increment with its full interface + transition record, or a
recentering with the RECORDING form (the recTRANSRS fence, D4(iii)). -/
inductive MoveWitness (σ σ' : Stage p F) : Type u
  | inc (ψ g Φhat e' h' zbar) (hyp : TransHyp σ ψ g Φhat e' h' zbar)
      (core : TransitionCoreL σ σ' Φhat e' h' zbar) : MoveWitness σ σ'
  | rec (cc : ↥σ.K) (tt : Polynomial ℤ_[p])
      (core : IsRecenteringCore σ σ' cc tt) : MoveWitness σ σ'
```

```lean
/-- The faithful D.2 base pin (the baseStage fence, D4(i)/D5): parent valuation =
the Gauss valuation, reps = [C p] (U = {π}, representative p — MOVES 1999–2001),
current field = the base field. `gaussVal` binds to the `L1_gaussVal` layer's
definition (verify exact name at E-phase; content: min over coefficients of v_p).
FALSE for the wPrev = 0 clone MovesGr certified vacuous. -/
def IsBaseStage (σ : Stage p F) : Prop :=
  (∀ f, f ≠ 0 → σ.wPrev f = gaussVal f) ∧
  σ.reps = [Polynomial.C (p : ℤ_[p])] ∧ σ.K = σ.FQ

/-- **A tower**: base + K moves; `stg 0` faithfully based, every step witnessed.
Nonempty by gate T2 (depth 0) and S1's gate (depth 1). -/
structure Tower (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Finite F] where
  K : ℕ
  stg : Fin (K + 1) → Stage p F
  base : IsBaseStage (stg 0) ∧ StageCoreL (stg 0)
  move : ∀ k : Fin K, MoveWitness (stg k.castSucc) (stg k.succ)

/-- e_birth per level (D6): base e at 0; an increment sets e′; a recentering
KEEPS the previous value ("same C, same v, same T" — TRANS-RS). -/
def Tower.eBirth (T : Tower p F) : Fin (T.K + 1) → ℕ := ...   -- recursion on moves

/-- **EXCLUSIVE accumulated stretch** (the note's STR, audit C-1): the stretch
accumulated BEFORE level k's read — `STR₀ = 1`, `STR_{k+1} = STR_k · e_k`
(e_k := (T.stg k).e; recentered stages contribute e = 1 — D.10's e_read = 1
precondition, S10's `σ.e = 1` hypothesis). LST base 3752: κ₀ at STR₀ = 1. -/
def Tower.str (T : Tower p F) : Fin (T.K + 1) → ℕ := ...

/-- κ_k := h_k/(e_k·STR_k) — the note's formula VERBATIM on the exclusive STR
(LST head, MOVES 3731–3735); = h_k/(e₀·…·e_k), each e counted once. AUDIT
RECOMPUTE (C-1): at (e₀,h₀) = (2,1), κ₀ = 1/2 — rev 1's inclusive-STR paste gave
1/4, the stale-κ-class defect the note itself warns about (3640). -/
noncomputable def Tower.kappa (T : Tower p F) : Fin (T.K + 1) → ℚ := ...

/-- the frame-(K+1) accumulated stretch `strTop = STR_K·e_K = e₀·…·e_K`
(C.1.0(c)'s frame str, inclusive of the last read): THE stage-scale conversion
factor — stage-K weights = strTop × absolute heights (T3; the carrier's
reindexing, T6; TYP's δ' := strTop·γ', C2). -/
def Tower.strTop (T : Tower p F) : ℕ := T.str (Fin.last T.K) * (T.stg (Fin.last T.K)).e

/-- A tower coordinate: p-adic level l + inner slot vector (bounded per level by the
key-degree ratios — the iterated-development address (b, l) of D.3(e)); the TOP
slot is the current development-slot index (unbounded here — see the recorded
decisions below). -/
structure Tower.Coord (T : Tower p F) where
  l : ℕ
  slot : Fin (T.K + 1) → ℕ
  slot_lt : ∀ r : Fin T.K, slot r.castSucc < slotBound T r   -- ratios; def in-file

/-- the coordinate's basis monomial `m_c = p^l·∏_r Φ_r^{slot r}` (TYP(a) display). -/
noncomputable def Tower.mono (T : Tower p F) (c : T.Coord) : Polynomial ℤ_[p] :=
  Polynomial.C ((p : ℤ_[p]) ^ c.l) * ∏ r, (T.stg r).Φ ^ c.slot r

/-- the absolute height `ht(c) = l + Σ_r slot_r·κ_r` (LST head, MOVES 3734–3735). -/
noncomputable def Tower.ht (T : Tower p F) (c : T.Coord) : ℚ := ...
```

**RECORDED DECISIONS (audit G-3 — four conventions pinned, one paragraph).**
(1) `slotBound T r` for r < K := the key-degree ratio
`deg (T.stg r.succ).Φ / deg (T.stg r.castSucc).Φ` — an integer (= e_r·g_{r+1} at an
increment, by D.3; = 1 at a recentering, degree unchanged). (2) THE TOP LEVEL:
D.3(e)'s C_{K+1} coordinates would need the PENDING read's g, which a K-move Tower
does not carry — so `slot (Fin.last T.K)` (the current development-slot index, = the
block label: `blk c := c.slot (Fin.last T.K)`, DefsCar) is UNBOUNDED in `Coord`;
every consumer pins it per use (levelSet fixes it to b; T12's level-N boxes bound it
by the box's window length; LST/TYP are per-block statements, so no top bound is
ever consumed). (3) RECENTERED LEVELS: ratio 1 at (1) forces slot ≡ 0 there, so
`mono` auto-selects the CURRENT frame's key of each degree class (replaced keys
never appear — the note's "the replaced key is the CURRENT one, absent from off",
LST step); `kappa` is TOTAL on Fin (T.K + 1) and its value at a recentered level is
junk-but-harmless (it multiplies a forced-0 slot; the note assigns κ only to
augmented levels — recorded, no consumer reads the junk). (4) ROOT e_birth:
`eBirth T 0 := (T.stg 0).e` (the base e) — deliberately diverging from the pass-7
root phrasing ("e_birth = 1 at the root"): the root coefficient algebra is born at
the base read, whose (S5) digit positions −t·v carry ℤ/e₀ coset structure, and
D7/D8's DIG typing consumes exactly that; a convention decision, recorded here.

### 2.3 `HC1/DefsCar.lean` — the REAL graded carriers

```lean
/-- The top stage's side-valuation package: `σ.w` extended by `0 ↦ ⊤`, laws from
`StageCoreL` (this is MovesGr's SideVal built from a GENUINE stage — the L1-layer
construction, reused). -/
noncomputable def Tower.side (T : Tower p F) : SideVal p := ...

/-- **The real GradedCarrier** (instantiates MovesR D4(a) at δ = 1; D3 convention):
Coeff := the top coefficient space as a submodule-carrier (deg < deg Φ̂_top, an
AddCommGroup via Polynomial.degreeLT); Gr γ := (T.side).grPiece ⌊T.strTop·γ⌋
(strTop = §2.2's frame stretch STR_K·e_K — audit C-1's re-thread);
w := strTop⁻¹·(side weight) in WithTop ℚ; inγ := the class map into the piece
(0 off-lattice). The four laws are unit T6's theorems (from MovesGr L0/L1). -/
noncomputable def Tower.carrier (T : Tower p F) : GradedCarrierR p := ...
  -- GradedCarrierR := MovesR's GradedCarrier shape, re-declared in HC1 pending
  -- the MovesR re-key (R-layer); one structure, ten fields, same laws.

/-- level set `L_γ(b) = {c : blk c = b ∧ ht c = γ}` and block map (D.3(e)(ii)). -/
def Tower.levelSet (T : Tower p F) (b : ℕ) (γ : ℚ) : Set T.Coord := ...
def Tower.blk (T : Tower p F) : T.Coord → ℕ := ...   -- development-slot block label

/-- slot coefficient of a digit assignment on a block: `Σ_{c ∈ blk b} y′_c·m_c`
(TYP(a)'s display: B IS its tower expansion; y′ = Teichmüller-style unit lift of the
F_Q-digit, bound to the Moves base-residue apparatus). -/
noncomputable def Tower.slotCoeff (T : Tower p F) (b : ℕ)
    (y : T.Coord → ↥(T.stg 0).FQ) : Polynomial ℤ_[p] := ...

/-- **the TYP composite** (D7(i) — THE additive object): level-set digits →
graded piece, `(y_c)_c ↦ inγ γ (slotCoeff b y)` restricted to L_γ(b)-supported y. -/
noncomputable def Tower.typComposite (T : Tower p F) (b : ℕ) (γ : ℚ) :
    (T.levelSet b γ → ↥(T.stg 0).FQ) → (T.carrier).Gr γ := ...

/-- **the alphabet = the slot-image SPAN** (D7(ii), the F3-2 repair): the additive
closure of the single-coordinate images. `aDim` := its p-logarithm. -/
noncomputable def Tower.alphabet (T : Tower p F) (b : ℕ) (γ : ℚ) :
    AddSubgroup ((T.carrier).Gr γ) :=
  AddSubgroup.closure (⋃ c ∈ T.levelSet b γ,
    Set.range fun y => T.typComposite b γ (Pi.single c y))

/-- block edges and THE STAIRCASE FLOOR (the F3-3 repair, by construction):
`floorB b := (lines kIdx).at (blockEdge b)` — the current read line at the block's
left base edge; `lines` := the tower's read-side lines (MovesC `Line`, from each
move's (e_k, h_k) at its frame — C.1.0(a) blocks). -/
def Tower.blockEdge (T : Tower p F) : ℕ → ℕ := ...
noncomputable def Tower.lines (T : Tower p F) : ℕ → MovesC.Line := ...
noncomputable def Tower.floorB (T : Tower p F) (b : ℕ) : ℚ :=
  (T.lines T.K).at (T.blockEdge b)
```

Falsifiability of the carrier layer: `floorB` is a definition (no free field to set
to 42); `alphabet` is generated by the ACTUAL slot images (an instance cannot inflate
or deflate `aDim` — F3-2's junk instance `aDim ≡ δ` is unconstructible); `mono`/`ht`
are computed from the tower's own keys and read indices (a stale-κ instance is
unrepresentable: κ is a function of the move list, fixed at the augmenting read).

### 2.4 `HC1/DefsSpine.lean` — strata, transports, the per-level ledger objects

Reused UNCHANGED from Moves (statement fence): `StratumData`, `LandingCylinderL`,
`CarryTransportL`, `carryDigit`, `K1At`, `IsSlotMinWeight`, `HasAnchorK`,
`OrdPsiPoly`, `DigitSystem`. New:

```lean
/-- the child valuation as a FUNCTION (D.7 head): `w′(Σ B_j Φ̂^j) := min_j (e′·w(B_j)
+ j·h′)`, via the monic Φ̂-development (Fact A existence + Fact B uniqueness, Moves
L0). Total: junk value 0 at f = 0. -/
noncomputable def childW (σ : Stage p F) (Φhat : Polynomial ℤ_[p]) (e' h' : ℕ) :
    Polynomial ℤ_[p] → ℤ := ...

/-- level-k stratum/landing data bundle for the spine (the D.8/D.10 per-move pack,
at tower level k — all data in level-k's frame). -/
structure LevelMove (T : Tower p F) (k : Fin T.K) where ...
```

## 3. Unit specs

FORMAT (campaign §2): `id · file · statement · moves_ref · deps · sketch ·
difficulty · hypothesis_fields`. Statements are given in full where short; units
whose statement is a Defs display above cite it as `[§2.x]`. Every unit ≤ ~40
expected proof lines (splits pre-approved where flagged). `hyp:` lists open kernels
riding as hypotheses — never silently strengthened or dropped; `dep-sorry:` names a
consumed Moves unit that still carries a sorry (§4 ledger).

### Layer D — the carry algebra (8 units, file `HC1/D_*.lean`)

* **HC1.D1_carryRing** — `noncomputable instance : CommRing (CarryAlg F e)` (product
  `cmul zbar`; the instance is a def `carryRing zbar` — the ring depends on zbar).
  moves_ref: MOVES 1508–1511 "𝒟 ≅ F_{r+1}[u]/(u^e − z̄), a strongly graded twisted
  algebra". deps: DefsD. sketch: pointwise add; associativity of cmul reduces to the
  cocycle identity `carryExp ρ σ + carryExp (ρ+σ) τ = carryExp σ τ + carryExp ρ (σ+τ)`
  on ZMod-vals (case split + omega); distributivity from sum-linearity. difficulty:
  medium. hyp: none.
* **HC1.D2_carryGrading** — `dOf ρ c * dOf σ c' = dOf (ρ+σ) (c·c'·z̄^{carryExp ρ σ})`
  and `IsHomog x ρ → IsHomog y σ → IsHomog (x*y) (ρ+σ)`. moves_ref: MOVES 1508–1509
  (the u_ρ·u_σ law). deps: D1. sketch: unfold cmul; single surviving summand.
  difficulty: easy. hyp: none.
* **HC1.D3_carryDomain** — products of nonzero homogeneous elements are nonzero:
  `IsHomog x ρ → IsHomog y σ → x ≠ 0 → y ≠ 0 → x * y ≠ 0`. moves_ref: MOVES
  1510–1511 "products of nonzero homogeneous elements nonzero (c·c′·z̄^κ ≠ 0 in the
  field — the graded-domain property, irreducibility not needed)". deps: D2.
  sketch: the (ρ+σ)-component is c·c′·z̄^κ, a product of units and nonzeros in F.
  difficulty: easy. hyp: none.
* **HC1.D4_carryAdjoinRoot** — `CarryAlg F e ≃+* AdjoinRoot (X^e − C (zbar : F))`
  sending `dOf ρ c ↦ c·u^{ρ.val}` (ring iso; e ≥ 1). moves_ref: MOVES 1509
  "𝒟 ≅ F_{r+1}[u]/(u^e − z̄)". deps: D1, D2. sketch: the map on the F-basis
  {u^0,…,u^{e−1}} of both sides; multiplicativity = the division identity
  u^{a+b} = u^{(a+b) mod e}·(u^e)^{⌊(a+b)/e⌋} in the quotient; inverse by basis.
  difficulty: medium. hyp: none.
* **HC1.D5_carryE1** — at e = 1: `CarryAlg F 1 ≃+* F` (the trivial twist; every
  e_read = 1 read sees a plain field). moves_ref: MOVES 1483–1486 (e″ = 1 reads vs
  e_birth cosets — the distinction D6 threads). deps: D1. sketch: ZMod 1 a point;
  carryExp ≡ 1 but z̄^1 scales… compute: ρ = σ = 0, val 0+0 < 1, carryExp = 0; iso
  is evaluation at the point. difficulty: easy. hyp: none.
* **HC1.D6_carryHomogUnits** — nonzero homogeneous elements are UNITS of
  `CarryAlg F e`: inverse of `dOf ρ c` is `dOf (−ρ) (c⁻¹·z̄^{−carryExp ρ (−ρ)})`.
  moves_ref: MOVES 1513–1514 (digits live in homogeneous components; the R-calculus
  needs their invertibility). deps: D2. sketch: one product computation via D2.
  difficulty: easy. hyp: none.

* **HC1.D7_digD_mul** — the DIG homomorphism: for `B, B″ ∈ C_Φ̂∖0` with monic
  division `B·B″ = Q·Φ̂ + R_dev`, `σ.digD zbar e_b R_dev = σ.digD zbar e_b B *
  σ.digD zbar e_b B″` in `CarryAlg F e_b` (product = D1's cmul: positions add WITH
  the carry — the pass-7 twist made exact). moves_ref: MOVES 2305–2315 (Lemma
  DIV(iii): dig′(R_dev) = dig′(B)·dig′(B″)) + 1456–1459 (D(BB′ mod Φ) =
  z̄^κ·D(B)D(B′)). deps: D2, Moves `L3_DIV` (clean). sketch: DIV gives the F′-level
  identity; split the z-positions by e_b; the quotient/alignment exponent is exactly
  `carryExp`; assemble via D2. difficulty: medium. hyp: the (S5)-shape of the three
  digits (from `StageCoreL`, rides as hypothesis).
* **HC1.D8_digD_recenter** — a recentering PRESERVES the 𝒟-typing: if
  `IsRecenteringCore σ σ' cc tt` then for every coefficient B (`inC σ.Φ B`),
  `σ'.digD zbar e_b B = σ.digD zbar e_b B` — coefficients' birth cosets ride through
  e_read = 1 moves untouched. moves_ref: MOVES 2668 "S5: coefficient digits
  LITERALLY unchanged (same C, same v, same T; position 0)" + 1523–1526 (e_birth vs
  e_read). deps: DefsD, Moves DefsCore (`IsRecenteringCore`). sketch: the core's
  digit-equality field transports digPrime; positions from the shared wPrev.
  difficulty: easy. hyp: none.

### Layer T — tower, heights, real carriers (12 units, `HC1/T_*.lean`)

* **HC1.T1_baseStage** — `theorem baseStage_exists : ∀ (e h : ℕ) (bdata :
  BaseReadData p F e h), ∃ σ : Stage p F, IsBaseStage σ ∧ StageCoreL σ ∧ σ.e = e ∧
  σ.h = h` — the base package CONSTRUCTED at the Gauss valuation (`BaseReadData` :=
  the §A base pins: monic φ of degree d ≥ 1, φ̄ irreducible over F_p, F_Q := the
  splitting subfield, gcd(e,h) = 1, w := min_i(e·v(aᵢ) + i·h)). moves_ref: MOVES
  1992–2015 (the base stage, (S1)–(S6) item by item). deps: Moves `L1_gaussVal`,
  `L1_baseResidual_R4`, `L1_baseWeight_R3` (ALL clean — baseWeight proved on disk
  at 35bf18a via direct MacLane, §4.1 CLOSED). sketch: fields of `Stage` from the display: hS5 = D.2's
  dig(B) = ū·z^{−tv} computation; hS6a/hS6b coincide at the base (𝒜 = {(ev, −tv)},
  realizers p^v·û); value group from gcd(e,h) = 1. difficulty: HARD (pre-split:
  T1a fields through hS5; T1b the (S6) legs). hyp: none beyond bdata.
* **HC1.T2_baseGate** — concrete inhabitant: p = 2, F := GaloisField 2 2,
  φ := X² + X + 1, (e,h) = (1,1): `∃ σ, IsBaseStage σ ∧ StageCoreL σ` by
  CONSTRUCTION (discharges what MovesGr's held `L4_base_nonvacuity_gate` wanted,
  at the honest base pin). moves_ref: MOVES 1992–1994. deps: T1. sketch:
  instantiate T1's data; decidable side conditions by decide/norm_num. difficulty:
  HARD (the concrete Gauss-valuation fields are labor; escalation-risk). hyp: none.
* **HC1.T3_htChainWeight** — `theorem ht_chainWeight (T : Tower p F) (c : T.Coord)
  (hc : c.MonoNZ) : ((T.stg T.K).w (T.mono c) : ℚ) = (T.strTop : ℚ) * T.ht c` —
  LST(i-a): ht IS the K1-chain weight of the basis monomial, stage scale =
  strTop·abs (strTop = STR_K·e_K, §2.2 — audit C-1: rev 1's factor `T.str T.K`
  paired with the double-counted κ; SANITY at K = 0, (e₀,h₀): w(p^l·φ^b) =
  e₀·l + b·h₀ = e₀·(l + b·κ₀) = strTop·ht ✓). moves_ref: MOVES 3736–3738 "ht(b, l)
  is the K1-chain weight of the coordinate's basis monomial
  p^l·∏_r Φ̂_r^{innerslot_r(b)}". deps: DefsTower; Moves `L3_K1`,
  `L2_keyResidualPow` (clean); the per-move κ-update discipline (LST proof, MOVES
  3750–3777). sketch: induction on K; increment step adds one inner level at
  κ_{new} = h_{new}/(e_{new}·STR_{new}) — the EXCLUSIVE prefix STR, so the child
  frame's strTop = STR_{new}·e_{new} absorbs exactly the D.0 stretch (w′(Φ̂) = h′;
  multiplicativity hwmul on the monomial); recentering step: v = v′ at fixed
  labels, strTop unchanged (e = 1). difficulty: HARD. hyp: none.
* **HC1.T4_slotMinHt** — LST(i-b): for a block b and assignment y with
  `slotCoeff b y ≠ 0`, `(T.carrier).w (T.slotCoeff b y) = inf {T.ht c : c ∈ blk b,
  y c ≠ 0}` (WithTop ℚ inf over the nonzero digit coordinates). moves_ref: MOVES
  3738–3739 "w(B) = min{ht(b, l) : (b, l) ∈ blk(B), y_{(b,l)} ≠ 0} (the iterated
  slot-minimum)". deps: T3; Moves `hK1`/`L0_FactB_unique`. sketch: iterate K1 down
  the tower on the expansion Σ y′_c·m_c; ties handled by hRadd/hRlt (D.1(b)).
  difficulty: medium. hyp: none.
* **HC1.T5_levelSetInγ** — LST(i-c): if two assignments agree on `levelSet b γ` and
  both have all digits below γ zero on the block, then `inγ γ (slotCoeff b x) =
  inγ γ (slotCoeff b y)`. moves_ref: MOVES 3739–3742 "the weight-γ initial form
  in_γ(B) is a function of exactly the LEVEL SET L_γ(B)". deps: T4, T6. sketch:
  difference has weight > γ (T4 on x − y); inγ_kills. difficulty: medium. hyp: none.
* **HC1.T6_carrierLaws** — the real `Tower.carrier` satisfies the four GradedCarrier
  laws (`w_add`, `inγ_add`, `inγ_kills`, `inγ_detects`). moves_ref: MOVES 3799–3801
  ("the class map is additive and kills weight > δ′ — D.1") + D.1(b). deps:
  DefsCar; MovesGr `L0_pmul_mk`, `L0_initialForm_*`, `L0_deg_add` (proved). sketch:
  transport MovesGr's piece lemmas through the ⌊strTop·γ⌋ reindexing (§2.2's frame
  stretch — C-1 re-thread); off-lattice clauses vacuous by D3's convention.
  difficulty: medium. hyp: none.

* **HC1.T7_alphabetSpan** — `Tower.alphabet` is the additive span of the slot
  images, is finite, and `Nat.card = p ^ aDim` for `aDim := (Nat.card …).log p`
  with the exactness equation `p ^ aDim = Nat.card` as the theorem (F_p-subgroup of
  a p-group carrier). moves_ref: MOVES 3815–3821 "image = the additive span of the
  slot images … = the digit's ALPHABET". deps: DefsCar, T6. sketch: closure of
  finitely many F_p-lines in an elementary abelian p-group; card a p-power.
  difficulty: easy. hyp: none.
* **HC1.T8_alphabetStep** — the (ii.2) step bijection: the typComposite restricted
  to attainable tuples is an F_p-linear BIJECTION onto the alphabet, and
  `|β(B,γ)| = Σ_{i∈I(γ)} |β(B_i,γ_i)| = log_p |𝔸(γ)|` (per-height block size).
  moves_ref: MOVES 2139–2160 ((ii.2), 𝔸(γ) = u(γ)·{Σ c_i z̄^i}, "an F_p-SUBSPACE
  … of size Π |𝔸_k(γ_i)|; distinct attainable tuples give distinct values").
  deps: T4, T5, T7; Moves `L2_slotDecomp_R4`, `L2_strideRule` (clean). sketch:
  slots are independent coordinates (S3); (1, z̄, …, z̄^{g−1}) an F_k-basis; u(γ) a
  unit; injectivity = the basis independence, surjectivity = span; induction up the
  tower. difficulty: HARD (pre-split: T8a fixed-level bijection; T8b the tower
  induction on block size). hyp: none.
* **HC1.T9_blockDisjoint** — (ii.3), TWO legs (audit G-5: rev 1 stated only (a),
  which is definitionally trivial — ht is a function). (a) locus disjointness:
  `γ ≠ γ' → Disjoint (levelSet b γ) (levelSet b γ')` and distinct blocks partition
  coordinates (kept as the ledger-facing form). (b) **THE CONTENT — leaf-address
  injectivity**: the mixed-radix address map
  `c ↦ (Σ_r c.slot r · ((T.stg r).Φ.natDegree), c.l)` (the base index of `mono c`'s
  x-leading block + the p-level — C.1.0(a)/(c)'s affine correspondence) is
  INJECTIVE on Coord at each fixed window (top slot bounded per T12's box): the
  slot vector is the mixed-radix representation of the base index in the
  degree-ratio radices (slot_lt = exactly the digit bounds), so distinct
  coordinates address distinct base digit coordinates — hence distinct (b, γ)-pins
  constrain DISJOINT base coordinate sets: the note's "no two equations of one
  system pin the same digit coordinate", the injectivity S17's `L6_ledgerCount`
  consumption rests on. moves_ref: MOVES 2175–2188 ("distinct development slots
  have disjoint leaf subtrees (the development is a coordinate partition) … the two
  forced slot classes t_k·γ*, t_k·γ′* differ (t_k invertible mod e_k) … induction
  bottoms at distinct p-adic heights … disjoint addresses"). deps: DefsCar, T12;
  Moves `L0_FactB_unique` (clean — development uniqueness = the partition).
  sketch: (a) definitional; (b) mixed-radix uniqueness (Nat.div/mod induction down
  the radix list; the note's slot-class argument is the γ-indexed instance of it).
  difficulty: medium. hyp: none.
* **HC1.T10_floorStaircase** — `T.floorB b = (T.lines T.K).at (T.blockEdge b)` is
  DEFINITIONAL (rfl-level); the content unit: on factor-interior blocks the
  coordinate floor is the block staircase — `interiorB b → ∀ c, blk c = b →
  floorC c = floorB b` with `floorC` the pointwise history-floor max (MovesC
  `floorOf`). moves_ref: MOVES 3743–3745 (LST(ii)) + 3650–3651 (DOM: "the floor is
  the current staircase: F_i(b) = old_i(slot(b))"). deps: T3, C4 (DOM_real), MovesC
  `C2.DOM_floorForm` (proved). sketch: DOM gives line domination on the interior;
  staircase evaluation at the nested block edges (MOVES 3720–3726). difficulty:
  medium. hyp: realizability chain (SAE)/(NA)/(HV) of the tower's moves — rides as
  a `TowerRealizable` hypothesis field (open kernel, §5).
* **HC1.T11_attainDichotomy** — pinning `typComposite b γ y = X` is solvable iff
  `X ∈ T.alphabet b γ`; an off-alphabet pin has EMPTY solution set; a zero pin never
  does (0 ∈ 𝔸). moves_ref: MOVES 2165–2168 "Pinning d_γ(B) = X is solvable iff
  X ∈ 𝔸(γ) — an off-alphabet pin EMPTIES the locus". deps: T7, T8. sketch: image
  characterization from T8's bijection. difficulty: easy. hyp: none.
* **HC1.T12_coordFin** — bookkeeping: `T.Coord` restricted to any level-N box is
  finite; `blk`/`blockEdge` total; `ht` injective on no block (heights repeat) but
  `(blk, ht)`-fibers are the level sets — the finiteness/typing lemmas every counting
  unit cites. moves_ref: MOVES 2088–2094 (height scales declared once). deps:
  DefsTower. sketch: bounded slot vectors, product finiteness. difficulty: easy.
  hyp: none.

### Layer C — LST/TYP/DOM as theorems (6 units, `HC1/C_*.lean`)

* **HC1.C1_LST** — **Lemma LST over the real carriers**: the conjunction (i-a) T3,
  (i-b) T4, (i-c) T5, (ii) T10, (iii) `interiorB b → floorB b < γ' → levelSet b γ' ∩
  floorSet b = ∅` where `floorSet b := {c : blk c = b ∧ ht c ≤ floorB b}`.
  moves_ref: MOVES 3728–3777 (Lemma LST, all legs). deps: T3, T4, T5, T10.
  sketch: assembly; (iii) is arithmetic from (i)+(ii) (ht = γ' > floorB on the
  set). difficulty: medium (assembly + (iii)). hyp: `TowerRealizable` (via T10).
* **HC1.C2_TYPa** — **TYP(a)**: on any assignment with block-b digits of height
  < γ' all zero, `inγ γ' (slotCoeff b y) = T.typComposite b γ' (y ↾ levelSet b γ')`,
  and the composite is ADDITIVE in the digit tuple (the F3-1 repair: additivity in
  (y_c)_c, never in box points). moves_ref: MOVES 3795–3807 "in_{γ'}(B) =
  Σ_{c ∈ L_{γ'}(B)} y′_c·in(m_c) … an ADDITIVE function … of exactly the level-set
  digits". deps: T4, T5, T6. sketch: expand slotCoeff; summands below γ' absent by
  hypothesis, above γ' killed by inγ_kills; additivity: unit lifts of F_Q-digit
  SUMS differ from digit-wise lift sums by weight-> γ' terms (the base-residue
  carry — killed in the piece); this is the one genuinely delicate step.
  difficulty: HARD. hyp: none.

* **HC1.C3_TYPb** — **TYP(b)**: the composite's image = `T.alphabet b γ'` and the
  fibers over the image are equipotent (kernel cosets), so a fresh value clause at
  exact valuation γ' cuts exactly `|𝔸|⁻¹` among level-set assignments. moves_ref:
  MOVES 3813–3824 "additive with image = the additive span of the slot images …
  An additive surjection onto its image has equal-size fibers (kernel cosets), so
  the clause cuts exactly (alphabet)^{−1}". deps: C2, T7, T8. sketch: image = span
  by T8; fiber count = card kernel, additive group theory. difficulty: medium.
  hyp: none.
* **HC1.C4_DOM** — **Lemma DOM's DISPLAYED CONCLUSION** (the G3-3 repair): for a
  `TowerRealizable` tower, at every base index b of the PER-i factor interior
  `[0, interiorEnd i)` and every m < i ≤ K: `(T.lines i).at b ≥ (T.lines m).at b`,
  and the floor form `floorOf (T.lines) i b = (T.lines i).at b` there. moves_ref:
  MOVES 3647–3651 "line_i(b) ≥ line_m(b) for all m < i; consequently the floor is
  the current staircase". deps: DefsCar; MovesC `C2.DOM`, `C2.DOM_floorForm`,
  `DomData` (proved, base-free); Moves `L2_iaugRoot/-Step/-Recenter` for the
  steeper chain. sketch: instantiate MovesC's affine engine with `DomData` built
  from (I-aug) (steeper) + (SAE)'s vertex-entry (hypothesis); per-i interiors nest
  (MOVES 3683–3688), recorded. difficulty: medium. hyp: `TowerRealizable` —
  (SAE)+(NA)+(HV) per move. (`L2_iaugStep` is PROVED on disk with the +Irreducible
  hypothesis, §4.2 CLOSED — instantiated here at TransHyp's own `hirr`.)
* **HC1.C5_typToClause** — the bridge to MovesC's counting: a TYP(b) fresh value
  clause yields a `MovesC.LevelClause` with `support = levelSet b γ'` (as base
  coordinates), `codim = aDim b γ'`, and the `count` law from C3's equal-fiber
  theorem. moves_ref: MOVES 3813–3815 (USE 1: "C.1.5's counting consumes exactly
  this object"). deps: C3, T12; MovesC `LevelClause` (fence: consumed, not
  restated). sketch: package; count = card kernel-coset arithmetic, division-free.
  difficulty: medium. hyp: none.
* **HC1.C6_alphabetCard** — `Nat.card (T.alphabet b γ) = p ^ (T.aDim b γ)` and
  **the fullness DICHOTOMY, both directions** (audit G-4 — rev 1 stated only the
  sufficient leg): `𝔸(b,γ) = the full piece ⟺ every height in γ's slot tree is
  attainable`, and on the failing side STRICTLY SMALLER — `(∃ unattainable slot
  height in γ's tree) → aDim b γ < full piece dimension` (the shallow-heights
  clause); the D.9(b) clean-threshold regime is the displayed sufficient INSTANCE
  of the ⟸ leg (every stage bound cleared ⟹ attainable), not the statement. Still
  no unconditional fullness claim (the rev-D¹¹c fix stands). moves_ref: MOVES
  2160–2165 "= [F_{k+1} : F_p] … EXACTLY WHEN every height in γ's slot tree is
  attainable … and STRICTLY SMALLER at shallow heights". deps: T7, T8; Moves
  `L5_realCofin_R3`, `L5_realDomination_R3` (clean). sketch: T8's product formula
  per factor — full ⟺ each factor full ⟺ each height attainable; one unattained
  factor is a PROPER subgroup of its piece line, so the product card strictly
  drops. difficulty: medium. hyp: none.

### Layer S — the induction spine + per-level transports (17 units, `HC1/S_*.lean`)

* **HC1.S1_transHypGate** — `TransHyp` is non-vacuously inhabitable AND correctly
  exclusive. **RE-BASED (audit C-2): rev 1's data (T2's base, ψ = z² + z + 1) was
  UNSATISFIABLE** — z² + z + 1 is reducible over F₄ (its roots ARE F₄'s cube roots
  of unity), and structurally NO g ≥ 2 TransHyp exists over T2's base at all:
  hirr + hroot force [σ.K⟮z̄⟯ : σ.K] = g ≤ [F : σ.K], and T2 has K = F_Q = F₄ = F.
  RECORDED CONSTRAINT: any increment-gate instance needs [F : K] ≥ g. (a) the
  repaired concrete inhabitant at p = 2, ambient F := GaloisField 2 2 (= F₄, T2's
  ambient reused): base σ_lin := T1's package at the DEGREE-1 pin (φ = X, monic,
  φ̄ = X irreducible over F₂; (e,h) = (1,1); K = F_Q = the prime subfield F₂ — so
  [F : K] = 2 = g); ψ := z² + z + 1 ∈ K[z], now GENUINELY irreducible over K = F₂
  (root-free: ψ(0) = ψ(1) = 1; degree 2), monic, ≠ X, g = 2; z̄ := a primitive cube
  root of unity in F₄ˣ (exists since X² + X + 1 splits in F₄ — G1's own identity
  z̄² = z̄ + 1 is its root equation), giving hroot: aeval z̄ (ψ.map K.subtype) = 0;
  Φ̂ from `L3_liftExists` (clean; its threshold `wPrev(Φ) < h·(g−k)` reads
  gaussVal(X) = 0 < 1, 2 ✓); (e′,h′) := (1, w(Φ̂)+1) — hiaug: w(Φ̂)+1 > 1·w(Φ̂) ✓,
  hcop: gcd(1,·) = 1 ✓, hh′: w(Φ̂) = e·h·g = 2 ≥ 0 by the L3 lift-weight law ✓ —
  every TransHyp field discharged by the listed computation. (b) `¬∃` at e′ = 0
  (respects the MovesGr certificate — provable now as `TransHyp → 1 ≤ e'` is a
  field: state as the structure being False on the e′ = 0 instantiation by
  projection). moves_ref: MOVES 2325–2328 (D.7 head: the side satisfies (I-aug));
  MOVESGR §8.2 `transitionCoreL_e0_false`; HC1_AUDIT C-2. deps: DefsTower, T1 (the
  degree-1 base instance, constructed in-unit from T1's bdata); Moves
  `L3_liftExists`, `L3_liftWeight` (clean). sketch: (a) construct per the listed
  data (E-phase latitude: if GaloisField-root plumbing stalls, the recorded
  fallback ambient is `AdjoinRoot (X² + X + 1 : (ZMod 2)[X])` — G1's concrete F₄
  model, same content); (b) projection. difficulty: medium. hyp: none.
* **HC1.S2_childW** — `childW` well-defined: for f ≠ 0 the Φ̂-development exists and
  is unique (Moves L0 Fact A/B), the min is attained, and `IsSlotMinWeight
  (childW σ Φhat e' h') Φhat e' h' σ.w` holds. moves_ref: MOVES 2329
  "w′(Σ_j B_j Φ̂^j) := min_j (e′·w(B_j) + j·h′)". deps: DefsSpine; Moves
  `L0_FactA_exists`, `L0_FactB_unique` (clean). sketch: development as a function
  by monic division recursion; min over the finite nonzero slot set. difficulty:
  HARD (the function-level development + attained min is real plumbing; pre-split:
  S2a development function; S2b the IsSlotMinWeight law). hyp: none.
* **HC1.S3_childK1** — K1(Φ̂/w′) is definitional: `K1At (childW …) Φhat h'` (slot
  minimum at the child's own key; w′(Φ̂) = h′). moves_ref: MOVES 2338–2340 "(ii)
  K1(Φ̂/w′) is definitional (the accepted pass-4 observation)". deps: S2. sketch:
  unfold; the development of f at Φ̂ IS the defining data. difficulty: easy.
  hyp: none.
* **HC1.S4_childSubmult** — D.7(i): `childW (f·g) ≥ childW f + childW g` (via DIV(i)
  on coefficient products + the (I-aug) strict-depth of Q-terms). moves_ref: MOVES
  2331–2337 (D.7(i), the slot-(j+k+1) Q-part strictly deeper by (I-aug)). deps:
  S2; Moves `L3_DIV`, `L4_TRANSi_R3` (clean). sketch: re-develop products; the
  ultrametric assembly is L4_TRANSi's content instantiated at childW. difficulty:
  medium. hyp: none.

* **HC1.S5_childValuation** — D.7(iii): `childW` is multiplicative on nonzeros
  (leading slots multiply via DIV(iii)'s field product; Y′ transcendental via S3),
  and the child value group is ℤ (the un-rescaled form: coefficient weights e′·w(Ĉ)
  + h′ with gcd(e′,h′) = 1). moves_ref: MOVES 2343–2352 (D.7(iii), incl. the F5
  "nothing is renormalized" clause). deps: S3, S4; Moves `L4_TRANSiii_R3`,
  `L2_psiNotDvd_R3`, `L3_digPrime_nonzero` (clean). sketch: L4_TRANSiii is the
  proved engine; instantiate at childW; value group from L5_realCofin-style
  cofiniteness + Bézout. difficulty: medium. hyp: none.
* **HC1.S6_childS4field** — D.7(v): the child degree-0 coefficient field is F′ =
  K⟮z̄⟯: the D-map (dig′ per piece) is additive-injective per piece with image ALL
  of F′ by the LARGE-WEIGHT (S6b) argument (the three displayed ingredients).
  moves_ref: MOVES 2364–2391 (D.7(v), ingredients (1)–(3) displayed). deps: S5;
  Moves `L4_TRANSv_R3` (CLEAN — repaired at 4b29f6e: +StageCore fence-change
  APPROVED per its header, import re-pointed to `L4_TRANSviii_b_R4`,
  fresh-recompile axiom-clean; §4.3 CLOSED — S6 supplies `hcore` from the spine),
  `L4_TRANSviii_b_R4` (clean, the (S6b) recursion), `L2_widthBound` (clean).
  sketch: unit-monomial weights from powers of in(p); g consecutive stride
  positions; (S6b) scalars above the clean threshold; span = F′. difficulty: HARD.
  hyp: none.
* **HC1.S7_childPin** — D.7(vi)–(vii): the transported vector V′, u₀ := V′^{−h′},
  z′ := u₀·Y′^{e′}, T′ per the e′ = 1 / e′ ≥ 2 split, and S5′ (child digits are
  monomial units at forced positions −t′·w′). moves_ref: MOVES 2392–2418
  (D.7(vi)–(vii)). deps: S5, S6; Moves `L4_TRANSvii_R4`, `L5_recVV_R4`,
  `L2_keyResidualPow` (clean). sketch: the vector transport is `TransitionCoreL.
  child_Tvec`'s shape; D.3(b) re-runs verbatim (L2_keyResidualPow at the child).
  difficulty: medium. hyp: none.
* **HC1.S8_childS6** — D.7(viii): the split axiom transports — (S6a′) index set
  𝒜′ with instantiated positions + single-slot realizers over the CONSTANT orbit
  O = F_Qˣ; (S6b′) the offset P-lift with clean threshold via the two-line mutual
  recursion bottoming at the base. Child `TvecUnitLaw` DERIVED from parent
  `StageCoreL.tvec_unit` + `child_Tvec` (the L4_TRANSvi fence). moves_ref: MOVES
  2419–2463 (D.7(viii), both halves + consumers). deps: S7; Moves
  `L4_TRANSviii_a_R5_final`, `L4_TRANSviii_b_R4` (clean); MovesGr
  `tvec_units_fragment` (proved fragment). sketch: the two finals are the proved
  content; assembly threads the threshold arithmetic (I-aug at the PREVIOUS read).
  difficulty: medium. hyp: none.
* **HC1.S9_transStage** — **the D.7 capstone**: `theorem transStage_exists
  (σ : Stage p F) (hσ : StageCoreL σ) (th : TransHyp σ ψ g Φhat e' h' zbar) :
  ∃ σ' : Stage p F, TransitionCoreL σ σ' Φhat e' h' zbar ∧ StageCoreL σ' ∧
  σ'.K = σ.nextField zbar ∧ σ'.e = e' ∧ σ'.h = h'` — the child stage ASSEMBLED
  (the honest replacement for MovesGr's fenced `L4_TRANSstage`, now with the full
  hypothesis interface). moves_ref: MOVES 2464–2465 "The stage axioms (S1′)–(S5′),
  (S6a′), (S6b′) all hold: the induction closes with the split axiom." deps: S2–S8.
  sketch: `Stage` literal with w := childW, K := nextField, reps := σ.reps ++ [σ.Φ],
  Tvec := the transported vector; each field discharged by S3–S8. difficulty: HARD
  (assembly + the ↥K-vs-↥K′ subfield plumbing; pre-split: S9a the Stage literal +
  (S1′)–(S5′); S9b the (S6) legs + TransitionCoreL record). hyp: none.
* **HC1.S10_recStage** — **the D.10/TRANS-RS capstone**: at e_read = 1, given
  `StageCoreL σ`, `σ.e = 1`, a center `cc ≠ 0`, and the D.9-supplied lift
  (existence via S13), `∃ σ' tt, IsRecenteringCore σ σ' cc tt ∧ StageCoreL σ'` —
  the recentered package item by item (the honest replacement for MovesGr's
  `L5_recTRANSRS`, consuming the RECORDING relation per the fence). moves_ref:
  MOVES 2661–2670 (TRANS-RS, S1–S6 item by item). deps: S13; Moves `L5_recSpecies`,
  `L5_recSubst_R4`, `L5_recLiftIndep_R4`, `L5_recRSland_R4`, `L5_recVV_R4` (clean).
  sketch: Φ′ := Φ − tt; same w/wPrev/K/FQ/weightSet fields; K1(Φ′/v) = the g = 1
  instance of D.5 (L5_recSubst); digits unchanged. difficulty: HARD. hyp: none.
* **HC1.S11_towerSpine** — **the spine**: `theorem tower_stageCore (T : Tower p F) :
  ∀ k, StageCoreL (T.stg k)` + `tower_wf`: every increment's child data matches S9's
  output shape (K/e/h fields). moves_ref: MOVES 1862 ("Everything below is
  self-contained given the ACCEPTED §A and §B1") + D.7/D.10 closes. deps: T1
  (base), S9, S10; DefsTower. sketch: induction on k along `T.move`; the base field
  of `Tower` seeds it. NOTE: `Tower` CARRIES `TransitionCoreL`/`IsRecenteringCore`
  witnesses, so the spine is the PROPAGATION of StageCoreL, with S9/S10 showing
  such witnesses EXIST for legal reads — both directions recorded. difficulty:
  medium. hyp: none.
* **HC1.S12_iaugPersist** — (I-aug) in **the D.4 DERIVATION form** (audit G-6 —
  the quantifier pinned; rev 1's "(I-aug) holds at every read" admitted the
  projection-trivial reading via TransHyp's own hiaug field, which is the D4(ii)
  INTERFACE, not this unit's content): for every tower T, every level k, and every
  landing at k (root case k = 0, increment landings, recentering landings — D.4's
  three bullets), EVERY side of the child polygon available to the NEXT read is
  steeper than w(Φ̂) — displayed per-side as the chord inequality
  `e·h·g·(μ − j) < w(B_j) − w(B_μ)` for j < μ (the L2_iaug* statement shape), so
  that any (e′,h′) read off such a side satisfies `IAug`. This unit DERIVES that
  legal continuations exist at every level; TransHyp merely records the derived
  fact per read. moves_ref: MOVES 2217–2249 (D.4, all three bullets + "by
  induction along the history"). deps: DefsTower, S11; Moves `L2_iaugRoot`,
  `L2_iaugRecenter`, `L2_iaugStep` (ALL clean — iaugStep proved on disk at 4b29f6e
  with the +Irreducible hypothesis, discharged here by the move's `hirr`; §4.2
  CLOSED). sketch: induction on move index; each case is the proved Moves unit.
  difficulty: medium. hyp: none.

* **HC1.S13_realPersist** — Lemma REAL along the tower (D.9): the per-stage weight
  sets, cofiniteness bounds, and the domination h_r > e_r·f_r persist; at every
  e_read = 1 read the side value is realizable with any digit scalar. moves_ref:
  MOVES 2551–2581 (D.9(a)–(d), incl. the induction-order clause). deps: S11, S12;
  Moves `L5_realRecursion_R3`, `L5_realCofin_R3`, `L5_realDomination_R3`,
  `L5_realConclusion` (all clean). sketch: thread the four proved units along the
  tower index; the induction order (stage-r quantities before Φ_{r+1}) is the
  Tower's own structural order. difficulty: medium. hyp: none.
  **REV (2026-07-28, S13 ADJUDICATION — campaign ledger
  `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`, orchestrator direct read):**
  conjunct 3 RESTATED with D.9(d)'s own scope. The note (MOVES 2573–2581) scopes
  any-scalar realizability to e_read = 1 READS — "At any e_read = 1 read, the
  side value λ″ … any digit scalar c̃ ∈ F'ˣ is realizable ((S6b) … above the
  bound by (c))" — persisting along histories; in Lean: at `(T.stg k).e = 1`,
  for every ν with `wPrev Φ < ν` (the (S6b)/DEF-8 threshold = this statement's
  rendering of the display's λ″ > w(current key) ≥ bound), ν ∈ weightSet AND
  any digit scalar `c ∈ Kˣ` has a position-0 realizer. The E-phase conjunct
  quantified over ALL of `weightSet` (where the note supplies only the (S6a)
  base orbit) — BLUEPRINT OVER-STRENGTH (type i), the note intact; XE-precedent
  (statement repair post-refutation). S10's `hlift` consumer unaffected
  (ν = h is in scope by conjunct 2 at e = 1). MANIFEST statement re-synced.
* **HC1.S14_wellTypedAnchor** — the rev-D¹¹ F7 lemma: at an e_read = 1 stage,
  `R(f)` is a z-POLYNOMIAL and `a := ord_z R(f) ≥ 0` (T coefficient-pure ⟹ all
  digit positions 0 ⟹ stride positions j ≥ 0). moves_ref: MOVES 2636–2643
  (WELL-TYPEDNESS LEMMA (a ≥ 0 here)). deps: S11; Moves `L2_strideRule` (clean),
  Stage.he1t. sketch: he1t gives t = 0; hS5 positions 0; K1 slot positions = j.
  difficulty: medium. hyp: none.
* **HC1.S15_anchoredSubst** — the anchored substitution display (e_birth/e_read
  rerun, D6): on the stratum `R(f) = z^a·(z − c̃)^μ·h(z)` (ψ′-order μ, anchor a),
  the primed data are `a' = μ` and `R'_anch(z') = (z' + c̃)^a·h(z' + c̃)` — derived
  through `L5_recSubst`'s substitution identity with S14 typing it inside F[z′];
  stated ALSO in 𝒟-form: the digD data of f transform by the same display with the
  birth cosets spectator (D8). moves_ref: MOVES 2644–2653 (the anchored display
  + "Case J pinned a > 0 at level 1"); 1488–1497 (the pass-7 e_birth/e_read
  demand). deps: S10, S14, D8; Moves `L5_recSubst_R4` (clean). sketch: substitute
  z = z′ + c̃; ord_z′ of (z′+c̃)^a·h(z′+c̃) is 0 at z′ = 0 value c̃^a·h(c̃) ≠ 0…
  compute: h(c̃) ≠ 0 iff ψ′ ∤ h — the stratum's own clause; factor z′^μ explicit.
  difficulty: medium. hyp: none.
* **HC1.S16_levelLanding** — **the per-level transport bijection**: for a tower T,
  level k, and stratum data (ψ, μ, a, pattern Cdig), the move at level k restricts
  to a bijection stratum → landing cylinder: `StratumData … f ↔ LandingCylinderL …
  (development of f)`, both directions, at level k's stage (hypotheses DISCHARGED
  by S11). The statement THREADS the anchor-exactness clause (§4.5's landed
  repair): the increment leg carries the explicit hypothesis
  `hexact : ¬ X ∣ Σ_{j<N} Cdig j · ψ^j` — the stratum's own a = ord_z pin (part of
  the stratum's DATA per D.8; forward it is derivable from `HasAnchorK`'s
  exactness, backward it is genuinely additional — the shifted-anchor
  countermodel), matching `L5_landTwoSided_repair`'s theorem verbatim. moves_ref:
  MOVES 2484–2546 (D.8 proof: BOX/VERTEX both directions + TRANSPORT +
  two-sidedness); 2654–2659 (RS-landing, the g = 1 case). deps: S11, S15; Moves
  `L5_landBox`, `L5_landVertex`, `L5_landVertexDigit` (CLEAN — proved on disk,
  §4.4 CLOSED), `L5_landTransport_R4`, `L5_landTwoSided` from
  `L5_landTwoSided_repair.lean` (CLEAN, sorry-free, the hexact-hypothesized
  theorem at :755 — §4.5 RESOLVED; the superseded `_R5` file is NOT consumed),
  `L6_moveAffineBij` (clean). sketch: instantiate the five Moves landing units at
  `T.stg k` with StageCoreL from the spine; the recentering case via S10 +
  L5_recRSland. difficulty: medium-hard (assembly). hyp: `hexact` per stratum
  (threaded, never dropped); zero dep-sorries (rev 1's two tags were stale/
  resolved — §4 re-census).
* **HC1.S17_levelMeasureExact** — **D.11 at every level**: for every tower T, level
  k, admissible stratum, and every N above the largest constrained height + 1:
  `#{f mod p^N ∈ stratum} = #{development data mod p^N ∈ cylinder} = p^{nN} ·
  vol(cylinder)`, vol = the ATTAINABLE product over the cylinder's digit equations
  (each factor `|𝔸(γ)|⁻¹` = C6's cardinality; inadmissible pins ⟹ empty locus —
  the D¹¹d dichotomy). ONE move; no composition (D8 fence). "Admissible stratum"
  INCLUDES the anchor-exactness clause `hexact : ¬ X ∣ Σ_{j<N} Cdig j · ψ^j`
  (threaded from S16 — §4.5's landed repair; the G-2 threading). moves_ref: MOVES
  2672–2718 (D.11 in full, incl. the unit-system clause and the dichotomy). deps:
  S16, C3, C5, C6, T11; Moves `L6_ledgerCount`, `L6_moveReduceCommute_R4` (clean);
  dep-sorry: `L6_measureExact_R4` (§4.6 — two sorries, the SOLE surviving tail
  entry; its :143 inline lemma needs the same hexact clause threaded by
  restatement — §4.6's spec). sketch: first equality = S16's bijection +
  moveReduceCommute at level N; second = the unitriangular digit-count
  (ledgerCount) with per-pin attainable factors from C3/T11. difficulty: HARD.
  hyp: `hexact` per stratum; dep-sorry §4.6 only.

### Layer G — sealed-gate check units (5 units, `HC1/G_*.lean`; all decide/eval,
no sorry allowed, Lean-core footprints)

* **HC1.G1_divGate** — the pass-6/DIV arithmetic gate over F₄: with
  `F4 := AdjoinRoot (X² + X + 1 : (ZMod 2)[X])`, z̄ := root: `z̄² = z̄ + 1` and the
  DIV instance `dig′(Φ) = z̄ ⟹ dig′(Φ² mod Φ̂) = z̄² = z̄ + 1`, checked as the
  field computation (the verifier's value, MOVES 2318–2322). statement: the two
  F4-equalities by `decide` (AdjoinRoot over ZMod 2 with DecidableEq via quotient
  representatives — if decide stalls, restate over the 4-element enum field; E-phase
  latitude recorded). difficulty: easy. hyp: none.
* **HC1.G2_carryGate** — the carry-algebra table at e = 2 over F4 (z̄ := root ≠ 0,1):
  `dOf 1 1 * dOf 1 1 = dOf 0 z̄`, `dOf 1 c * dOf 0 c' = dOf 1 (c·c')`, and the
  cocycle identity for all ρ,σ,τ ∈ ZMod 2 — by `decide`/`Finset.forall`. moves_ref:
  MOVES 1508–1509. deps: D1, D2. difficulty: easy. hyp: none.
* **HC1.G3_caseJGate** — the Case-J anchor-monomial gate (a > 0), algebraic
  instance: over ZMod 2 (c̃ = 1), P := z·(z+1)²·(z²+z+1) (a = 1, μ = 2, ψ′ = z+1,
  h = z²+z+1 with ψ′ ∤ z^a·h): verify `P.comp (z + 1) = (z+1)·z²·(z²+z+1).comp (z+1)`
  and `a' = ord_z P(z+1) = μ = 2`, `R'_anch = (z'+1)·h(z'+1)` — by `decide` on
  coefficients (or `ring`+`norm_num`). moves_ref: MOVES 2644–2651 (the anchored
  display; "Case J pinned a > 0"); D.12 (Case J sealed, 12 strata). deps: none
  (pure Polynomial ZMod-2 arithmetic). difficulty: easy-medium. hyp: none.

* **HC1.G4_caseKGate** — the Case-K F₉ conditioned-digit gate: with
  `F9 := ZMod 3 × ZMod 3` (product carrying the X²+1 multiplication
  `(a,b)·(c,d) = (ac − bd, ad + bc)`; a hand-rolled CommRing instance — fully
  decidable), τ-variable over F9. **PREDICATE CORRECTED (audit C-3): the both-rise
  cell law is `d₀ = d₁²`** — the seal's own algebra: both-rise ⟺ R₂ = X² + d₁X + d₀
  has the double root τ ⟺ τ = −d₁/2 = d₁ (char 3) and d₀ = τ² = d₁² (rev 1's
  `d₀ = d₁³` was the wrong algebra; script ground truth
  `case_k_gate_v2_p3.py` :396 `d0 = f9mul(d1, d1)`). **ALL legs CONTENT-pinned:
  finite-set/list EQUALITY against explicit element lists, never bare
  cardinalities** — the audit's demonstration that {d₀ = d₁³} ALSO has card 8
  makes a count-only decide pass silently on the wrong set (the exact species of
  the adjudicated v1-seal failure, MOVES 2934; the campaign order-discipline
  precedent governs). Legs: (i) the Frobenius-matched both-rise set
  `{(d₀,d₁,τ) ∈ F9ˣ × F9ˣ × F9 : d₀ = d₁² ∧ τ = d₁}` = the EXPLICIT 8-triple list
  {(d₁², d₁, d₁) : d₁ ∈ F9ˣ} (elements enumerated literally in the unit;
  8-of-512 as a Nat.card COROLLARY of the list equality, matching Q4's "the unique
  both-rise is the Frobenius-matched τ = d₁ on each d₀ = d₁² cell — 8 both-rise
  combos of 512"); (ii) the char-3 edge clauses `2τ + d₁ = 0` / `R₂(τ) = 0`:
  solution SETS pinned as explicit element lists per cell, with Q2's sealed
  cardinalities (56 / 64 / 8 both) as corollaries. moves_ref: MOVES 3017–3045
  (CASE-K v2 SEALED GATE RECORD, Q1–Q6; Q4 at 3030–3032). deps: none
  (self-contained F9 arithmetic; the gate re-checks the ALGEBRAIC layer of the
  seal, not the p-adic census). difficulty: medium. hyp: none. NOTE: the literal
  element lists are transcribed from `verification/case_k_gate_v2_p3.py` at
  E-phase, but the NORMATIVE predicates are the ones displayed HERE (d₀ = d₁²,
  τ = d₁) — the sealed record's displayed law, not the script, is the fence; a
  transcription that disagrees with these predicates is a stop-the-line event.
* **HC1.G5_spanGate** — the F₉ a = 2 span-pricing gate (the F3-2 check): over F9,
  the ADDITIVE closure of the two slot-image lines `{c·1 : c ∈ ZMod 3} ∪
  {c·τ : c ∈ ZMod 3}` is all of F9 (card 9 = 3², aDim = 2), while any single line
  prices card 3 — `decide`. moves_ref: MOVES 9580–9582 ("the full position a = 2
  gives each re-based branch 𝔸_δ = F₉, i.e. a_δ = 2 ≠ δ·a = 4");
  MOVESR_AUDIT_FABLE3 F3-2. deps: G4's F9 object. difficulty: easy. hyp: none.

### Layer R — the MovesR re-key (6 units, `HC1/R_*.lean`; re-audit REQUIRED before
MovesR unparks — these are the statement defs MovesR's CInterface will import)

* **HC1.R1_LSTStmt** — `LSTStmt'` over `GradedCarrierR` + the ReBased carriers,
  with: the staircase equation INLINED into leg (ii) (`floorB H B = (K.lines H
  (K.C.kIdx H)).at (K.blockEdge H B)` via a new `blockEdge` carrier field — F3-3),
  and a `window : Hist → ℕ → Prop` predicate scoping legs (i-b)/(i-c) (G3-2).
  moves_ref: MOVES 3728–3749; MOVESR blueprint 602–615 (the rev-4 text being
  repaired). deps: DefsCar shapes. difficulty: easy (statement unit). hyp: the
  statement def itself is the open REL.1 clause — consumers hypothesize it.
* **HC1.R2_TYPStmt** — `TYPStmt'`: conjunct 1 = the COMPOSITE's additivity in the
  digit tuple (typed exactly as `Tower.typComposite`'s shape over the abstract
  carrier — F3-1); conjunct 2 = span pricing:
  `Nat.card ↥(AddSubgroup.closure (⋃ c ∈ lvl, Set.range fun y => K.G.inγ (K.ht H c)
  (K.slotCoeff H b (Pi.single c y)))) = p ^ K.aDim H i` (F3-2 — the Fable-3
  displayed form). moves_ref: MOVES 3801–3824; 9401–9406 (walk item (i): additive
  on digit blocks; F_δ-linearity stays walked, NOT asserted). deps: R1's carrier
  fields. difficulty: medium (statement unit; quantifier care). hyp: open REL.1
  clause.
* **HC1.R3_DOMStmt** — `DOMStmt'`: the displayed CONCLUSION (`∀ m < i, ∀ b <
  interiorEnd H i, (K.lines H i).at b ≥ (K.lines H m).at b` — per-i interiorEnd,
  G3-3), with `DomData` retained as the note's proof-input record but no longer the
  statement. moves_ref: MOVES 3647–3651; MOVESR_AUDIT_FABLE3 G3-3. deps: R1.
  difficulty: easy. hyp: open REL.1 clause.
* **HC1.R4_SecB1Stmt** — `SecB1Stmt'`: slot-coefficient additivity restated at the
  GRADED-PIECE level (`inγ γ (slotCoeff (x+y)) = inγ γ (slotCoeff x) + inγ γ
  (slotCoeff y)` at weight — G3-1's model-commitment removed), stage-carrier laws
  unchanged. moves_ref: MOVES 3799–3801; MOVESR_AUDIT_FABLE3 G3-1. deps: R1.
  difficulty: easy. hyp: open REL.1 clause.
* **HC1.R5_EQ2Pass** — `EQ2lawIfREL1'`: antecedent = the ∀-instances pass
  (`(∀ δ K, REL1 … δ … K) → EQ2law p AD` — G3-4's quantifier repair; the note's
  conditionality is on the FULL re-scoping pass). moves_ref: MOVES 9587–9588 +
  9379–9382; MOVESR_AUDIT_FABLE3 G3-4. deps: R1–R4. difficulty: easy. hyp: EQ-2
  stays OPEN, REL.1-conditional — typed, never asserted.
* **HC1.R6_carrierInstance** — the instantiation deliverable at δ = 1: `Tower.
  carrier` inhabits `GradedCarrierR p` (T6), and the LST/TYP/DOM LEGS of
  `CStatements` hold for it (C1, C2+C3, C4) — packaged as
  `theorem hc1_carrier_legs (T) (hreal : TowerRealizable T) : LSTStmt'-inst ∧
  TYPStmt'-inst ∧ DOMStmt'-inst`. The jets/counting legs (thmCa/thmCb/C05/C1/C15)
  are NOT claimed: they need the JetSetup bridge = **HC-2's seam**, recorded.
  moves_ref: MOVESR blueprint D4(a) "instantiation from the OM engine is HC-1's
  declared deliverable" + campaign §1 HC-2. deps: T6, C1–C4, R1–R4. difficulty:
  medium (assembly). hyp: `TowerRealizable` (§5).

## 4. The Moves tail dependencies (dep-sorry ledger + repair specs)

**RE-CENSUSED AGAINST DISK at REV 2 (audit G-1: rev 1's ledger was stale at this
blueprint's own commit — entries 4.1–4.4 were already closed by 35bf18a/4b29f6e;
re-verified by `grep sorry` + file headers + `git show` at this revision).** Each
entry names the consuming HC1 unit and its disposition. NO HC1 unit may close a
gap by weakening a Moves statement (fence). ONE entry remains open: 4.6.

* **4.1 `L1_baseWeight_R3` — CLOSED** (proved at 35bf18a, +823 lines, header dated
  2026-07-27: the direct-MacLane φ-adic development argument — `dev_slots` master
  lemma, Cauchy-product ≥, dominant-slot ≤). Consumer T1's dep is clean; no tag.
* **4.2 `L2_iaugStep` — CLOSED** (proved at 4b29f6e, the +`Irreducible ψ`
  hypothesis fence-change flagged at bfdfb5e and landed: the statement now covers
  the irreducible branch only). Consumers S12/C4 instantiate it at TransHyp's own
  `hirr`, so the strengthened hypothesis is discharged for free; no tag.
* **4.3 `L4_TRANSv_R3` — CLOSED** (repaired at 4b29f6e: +`StageCore` fence-change
  APPROVED per its own header, import re-pointed to the clean
  `L4_TRANSviii_b_R4`; commit message records fresh-recompile axiom-clean).
  Consumer S6 supplies `hcore` from the spine; no tag. E-phase verify leg
  re-checks the cone's footprint as usual.
* **4.4 `L5_landVertexDigit` — CLOSED** (the private core discharged on disk:
  +757 lines at 35bf18a, `vertexCongruence` closed from clean deps at 4b29f6e;
  header: "fully closed — no sorry"). Consumer S16's dep is clean; no tag.
* **4.5 `L5_landTwoSided` — RESOLVED FENCE-SAFE (audit G-2a/b; rev 1's spec was
  doubly wrong).** The repair ALREADY LANDED as `L5_landTwoSided_repair.lean`'s
  theorem (:755, commit 4b29f6e, file sorry-free): the anchor-exactness clause
  rides as the explicit hypothesis `hexact : ¬ X ∣ Σ_{j<N} Cdig j · ψ^j` — the
  file's own proposed clause, on the digit TOTAL. No `LandingCylinderL` field
  change and NO sign-off event occurred or is needed; rev 1's fence-gated
  field-addition plan is moot. Rev 1's gloss ("ord_z of the vertex slot term = 0
  after anchoring") is hereby STRUCK: it is not the file's clause and is FALSE on
  honest strata by rev-D¹¹ F4 (MOVES 2500–2505 — individual anchored slot terms
  need not have ord_z 0; the anchor is the ord of the SUM, bottom coefficients can
  cancel across slots); implemented literally it would empty legitimate strata.
  HC1 consumption: S16 imports the repair theorem and THREADS `hexact` (S16/S17
  hypothesis fields); the superseded `L5_landTwoSided_R5.lean` (:964 sorry) is NOT
  consumed.
* **4.6 `L6_measureExact_R4` — OPEN (2 sorries :143/:189; the sole surviving tail
  entry).** Consumer: S17. (a) :143 is the inlined private
  `L5_landTwoSided_missing` (:130–:143), stated on `LandingCylinder` WITHOUT the
  exactness clause — REFUTED-as-stated by the same shifted-anchor countermodel, so
  4.5's closure does NOT discharge it (audit G-2c; rev 1's ":143 resolves with
  4.5" struck). Repair spec: RESTATE the inline lemma and thread the `hexact`
  clause through `L6_measureExact`'s own hypotheses (a restatement on a fenced
  statement → sign-off required), after which :143 becomes an import of 4.5's
  repair theorem. (b) :189 is the `exfalso; sorry` zero-coordinate leg — a genuine
  faithfulness gap the fenced statement omits (the in-file FLAG): needs the
  E.IsSolution-at-Θ(code 0) hypothesis threaded (the "+hzsol" spec of bfdfb5e) — a
  restatement candidate for the tail fleet WITH sign-off, or a strengthened-
  hypothesis v5 unit (option (b) style), decided at adjudication. Until closed,
  S17 carries the dep-sorry honestly.

Superseded sorried files (`L2_P6i_R5`, `L4_TRANSviii_a_R5`, `L4_TRANSviii_b_R3`,
`L5_landTransport_R3`, `L5_landTwoSided_R5`, `L6_moveReduceCommute_R3`) are NOT
consumed — HC1 imports only the clean finals/R4s/the landed repair files.

## 5. Hypothesis-field ledger (open kernels; the axiom answer)

* **`TowerRealizable T`** — per-move (SAE) + (NA) + (HV) (C.0's realizability data
  conditions). Consumers: T10, C1, C4, R6. This is §C's own quantifier (MOVES
  3670–3677: on (SAE)-violating data DOM's statement is FALSE — so it MUST sit in
  the hypothesis). Typed as a structure over the tower's lines/windows; never
  discharged inside HC1 (its discharge per-instance is classifier work, HC-2-side).
* **REL.1 / the ∀δ re-scoping pass** — stays the OPEN KERNEL it is in the note
  (MOVES 9379–9418): HC1's R-layer TYPES it faithfully (with the seven repairs)
  and INSTANTIATES the carrier legs at δ = 1 (R6); the base-change instances
  δ > 1 and the jets/counting legs are not claimed.
* **`hexact` (anchor exactness, per stratum)** — `¬ X ∣ Σ_{j<N} Cdig j · ψ^j`, the
  a = ord_z pin that is part of the stratum's data per D.8; rides as an explicit
  hypothesis on S16/S17 exactly as on the landed `L5_landTwoSided_repair` theorem
  (§4.5). Never silently strengthened into the cylinder or dropped.
* **dep-sorries** — §4.6's pair only (the sole survivors of rev 1's six entries —
  §4 re-census, audit G-1), named at S17.
* **PUBLISHED-AXIOM CANDIDATES: NONE.** This is our own mathematics (D9). The
  verify leg must show Lean-core-only footprints on every proved unit; `sorryAx`
  appears exactly where §4 predicts, and any GMN/Denef import in an HC1 cone is a
  stop-the-line event.

## 6. File map, import order, build protocol

```
lean/LeanUrat/HC1/DefsD.lean      §2.1  (CarryAlg, carryExp, cmul, dOf, IsHomog, digD)
lean/LeanUrat/HC1/DefsTower.lean  §2.2  (TransHyp, MoveWitness, IsBaseStage, Tower,
                                         eBirth, str, kappa, strTop, Coord, mono, ht)
lean/LeanUrat/HC1/DefsCar.lean    §2.3  (side, carrier, levelSet, blk, slotCoeff,
                                         typComposite, alphabet, blockEdge, lines, floorB)
lean/LeanUrat/HC1/DefsSpine.lean  §2.4  (childW, LevelMove)
lean/LeanUrat/HC1/D_*.lean        D1–D8   ·  T_*.lean  T1–T12  ·  C_*.lean  C1–C6
lean/LeanUrat/HC1/S_*.lean        S1–S17  ·  G_*.lean  G1–G5   ·  R_*.lean  R1–R6
```

Import DAG: DefsD ← D-layer; DefsTower (imports Moves.Defs*, MovesGr.Defs) ←
DefsCar (adds MovesC.Defs) ← DefsSpine; layers as their deps state. Per-file
build: `lake env lean -o <olean> LeanUrat/HC1/<f>.lean` in topological order —
NEVER bare `lake build` (NFS hang; census protocol). Every unit file ends with
`#print axioms <thm>`. Options: `linter.style.longLine false`,
`maxHeartbeats 800000`. Provers follow the campaign preamble discipline
(MANIFEST `preamble` string to be emitted at E-phase, statements regenerated
verbatim — the MOVESGR §6 double-elaboration protocol).

## 7. Census, risks, process

**54 units**: D-layer 8 (5 easy / 3 medium) · T-layer 12 (3 easy / 5 medium /
4 hard: T1, T2, T3, T8 — T9 easy → medium at REV 2, the G-5 content leg) ·
C-layer 6 (5 medium / 1 hard: C2) · S-layer 17 (1 easy /
11 medium incl. the medium-hard S16 / 5 hard: S2, S6, S9, S10, S17) · G-layer 5
(4 easy / 1 medium) · R-layer 6 (4 easy / 2 medium). **HARD TOTAL: 10** (T1, T2,
T3, T8, C2, S2, S6, S9, S10, S17), each with a pre-approved split (T1a/b, T8a/b,
S2a/b, S9a/b) or a named escalation surface. Highest escalation risk: S9 (the
↥K/↥K′ subfield plumbing — the known type wall Moves' Defs were designed around),
C2 (the unit-lift additive carry — the one delicate new algebra step), T2
(concrete-instance labor).

Process per the campaign gates: this blueprint → Codex/Fable semantic audit
(REJECT loops; audit charge: faithfulness to the quoted displays, non-vacuity per
the doctrine, quantifier exactness, hypothesis-field fidelity, the §1 fence table
AND the §1.1 disposition table) → E-phase (Defs compile + statements elaborate
twice) → prover fleet (D/T-easy/G first; S9/S10/S17 last, after their deps) →
per-unit verify (Lean-core footprints) → the R-layer re-audit gates MovesR's
unparking. STUCK rule per campaign §3. REV-2 loop record: rev 1 REJECT 3c/6g
(`HC1_AUDIT_FABLE_2026-07-28.md`) → this revision (all nine folded, §1.1);
re-audit required before E-phase.

END OF BLUEPRINT — REV 2 (54 units; 10 hard; 0 published-axiom candidates;
rev-1 audit findings C-1..C-3, G-1..G-6 all folded, dispositions §1.1).

## 8. E-PHASE DEVIATIONS APPENDIX (2026-07-28, elaborator record — all elaboration-level;
no statement meaning changed; deliverable `lean/LeanUrat/HC1/` = 4 Defs files (sorry-free)
+ 54 units (51 sorry statements) + MANIFEST.json; every file `lake env lean`-green,
footprints Lean-core + sorryAx only; ZERO blocked units)

* **D-1 (rename).** `MoveWitness`'s blueprint constructor `rec` collides with the
  auto-generated recursor; renamed `recenter`. No content change.
* **D-2 (digD position).** `Stage.digD` guards on the (S5) MONOMIAL-UNIT shape of `σ.R B`
  and uses the monomial's OWN choice-extracted position, not the display-comment's
  `−t·wPrev B` (the S5 law identifies them on `C_Φ`; D7's `C_Φ̂` digits must carry their
  own positions or D7 is vacuous/false as typed). Scalar = the display's aligned class.
* **D-3 (lines/windows are not tower data).** `Tower.lines`/`floorB` as §2.3 displays them
  are UNDERDETERMINED by `Tower` (intercepts need each read's recorded vertex; windows are
  §C node data). They ride as fields of the Type-valued `TowerRealizable` (§5's own open
  kernel, which every line-consuming unit already hypothesizes: T10/C1/C4/R6), tied to
  tower data by the slope law `slope·frameWidth = κ` and the vertex/entry/window condition
  fields ((SAE)/(NA)/(HV) in the consumers' form). `floorB`/`floorC`/`interiorB` live on
  `TowerRealizable`; `blockEdge`/`baseIdx`/`frameWidth` stay pure tower defs.
* **D-4 (side by choice).** `Tower.side` is chosen against `HasSide` (∃ MovesGr `SideVal`
  agreeing with the top stage's `w` on nonzeros — the `GenuineStageModel.hSw` pattern) with
  a trivial fallback: `SideVal.w_smul` needs constant-weight nonnegativity, a spine-induction
  fact not definitionally dischargeable in a sorry-free Defs layer. `HasSide` is T6's first leg.
* **D-5 (carrier packaging).** `GradedCarrierR` keeps MovesR's ten-field law-carrying shape
  verbatim; since its four laws are unit T6's THEOREMS, `Tower.carrier` takes the
  `CarrierLaws` proof as an argument, and downstream units are stated on the concrete
  carrier data (`wQ`/`inGr`/`grQ`/`typComposite`) that `carrier` packages. T6 =
  `HasSide ∧ CarrierLaws`.
* **D-6 (attained-min form).** T4 / C1(i-b) / R1(i-b) state the slot minimum in the Moves
  `SlotMinAttained` attained form (corpus convention) instead of an `sInf` on `WithTop ℚ`.
* **D-7 (syntax fixes).** `aDim := Nat.log p (Nat.card …)` (the display's dot-notation
  reversed Nat.log's arguments); T3's stage weight read at `Fin.last T.K`; recursions
  (`eBirthAux`/`strAux`/`frameWidth`) clamp junk indices beyond K.
* **D-8 (S1 split + pins).** S1 = two theorems: (a) the concrete gate with the C-2 re-based
  data pinned in-statement (σ.Φ = X, σ.e = σ.h = 1, σ.K = ⊥ inside ambient `GaloisField 2 2`,
  ψ = X²+X+1 literal, e′ = 1); (b) the generic ¬TransHyp at e′ = 0.
* **D-9 (S17 conclusion form).** S17 concludes the division-free count law
  `#stratum · p^ktot = p^{D·N}` with the jet chart (code/Θ/E + unitriangularity) riding as
  hypotheses EXACTLY as the fenced `L6_measureExact` takes them; the inadmissible-pin
  empty-locus leg is T11's dichotomy (cited dep, not restated). Dep-sorry §4.6 recorded in
  the manifest.
* **D-10 (C6 typing).** "Every height in γ's slot tree is attainable" typed per-coordinate
  (each level-set coordinate's slot image nonzero); "the full piece" = cardinality agreement
  with the top residue field `[F_{K+1}]`; a `levelSet.Nonempty` guard added (the note's
  regime; an empty set would satisfy the ∀ vacuously and falsify the ⟸ leg).
* **D-11 (C5 chart).** The block-convention base-coordinate chart `enc` of the level set is
  §C-side data and rides as an additive-surjective-dep hypothesis; the LevelClause produced
  is pinned by support/codim/sat-iff exactly per `C1_TYP_toClause`'s shape.
* **D-12 (the two editorial folds, per the E-phase charge).** (a) G4(ii)'s clause order
  fixed to the seal tuple pairing — `R₂(τ) = 0` ↦ 56, `2τ + d₁ = 0` ↦ 64, both ↦ 8
  (machine-recomputed from `verification/case_k_gate_v2_p3.py`'s arithmetic at E-phase;
  the element lists are machine-transcribed, the normative predicates the §3 displays).
  (b) §4's closing paragraph adjective is STALE for `L2_P6i_R5.lean` and
  `L4_TRANSviii_a_R5.lean`: both are on disk SORRY-FREE (deprecated/superseded, not
  sorried); they remain NOT consumed. `L4_TRANSviii_b_R3`, `L5_landTransport_R3`,
  `L5_landTwoSided_R5`, `L6_moveReduceCommute_R3` remain superseded as listed.
* **D-13 (stale/missing oleans rebuilt).** `L4_TRANSv_R3.olean` was stale (predated the
  4b29f6e import re-point to `L4_TRANSviii_b_R4`; its stale import graph clashed with the
  clean R4 import) — recompiled green. Never-compiled oleans built for: MovesGr `L0_pmul_mk`,
  `L0_initialForm_zero/_ne_zero`, `L0_deg_add`, `L0_ge_antitone`, `L0_gt_le_ge`,
  `HeldUnits_certs`; MovesC `C2_DOM`, `C2_DOM_floorForm`; Moves `L5_landTwoSided_repair`.
  All Lean-core footprints (no sorryAx) — the §4 re-census confirmed on disk.
* **D-14 (small hypothesis notes).** S3 carries the derivable `hw1 : σ.w 1 = 0` explicitly
  (keeps the unit easy); S4–S9 bundle the read's legality as `TransHyp` (the D4(ii)
  interface) instead of re-listing its eleven fields; S8's (S6a′)/(S6b′) legs are Stage
  fields of the assembled child (projections), so S8 states the non-projection content
  (child `TvecUnitLaw` + child prevIaug — the `L4_TRANSvi` fence's derivation); S10's D.9
  lift existence rides as `hlift` (the blueprint's "existence via S13" cross-reference);
  S15 takes the stratum factorization `Ranch = (X − C cc)^μ · h` with `ψ′ ∤ h` and `a ≥ 0`
  (S14's clause) explicitly, conclusion in the `map`-to-F frame (the ↥K/↥K′ wall, the
  L5_recRSland precedent); T2/G2/S1 use `GaloisField 2 2` as the concrete ambient, G1 uses
  the recorded `AdjoinRoot` latitude model.
