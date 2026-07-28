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
  **REV (2026-07-28, D7 ADJUDICATION — orchestrator, from the note MOVES
  1385–1400):** the E-phase form carried the three (S5)-shapes as bare
  `IsMonomialUnit` hypotheses — DIG-multiplicativity stated against the WRONG
  target: the three anchors ride as free choice-data tied only through DIV's
  field-level identity dig′(R_dev) = dig′(B)·dig′(B″), against which the stated
  equation is UNDERDETERMINED — it holds iff `e_b ∣ d ∧ z̄^{d − d/e_b} = 1` for
  the free anchor discrepancy d := (kB + kB″) − kR (the prover's re-derived
  condition; the pass-6/7 counterexample that forced the twist, MOVES 1388; in
  particular this sketch's "split the z-positions" step and the Fable-audit gloss
  "position additivity from the exact remainder weight" are NOT available from
  bare shapes — nothing ties choice-extracted positions to weights on `C_Φ̂`).
  The note's law (1390–1396) is the homomorphism into the TWISTED group
  (ℤ/e) ⋉_{z̄} F_{r+1}ˣ, and its proof line (1400) inputs "the ψ_r-adic division
  identity … applied to the ALIGNED absolute residuals (the z-offsets now
  included on both sides …), plus the anchor addition". RESTATED accordingly:
  the monomial hypotheses carry explicit scalars/offsets `(cB, kB)`,
  `(cB″, kB″)`, `cR`, and h5R is pinned at the ADDED anchor `kB + kB″` (the
  anchor addition as hypothesis; in consumption = the (P6) absolute bookkeeping,
  position additivity from DIV's exact remainder weight at weight-pinned
  positions). Conclusion UNCHANGED: `digD R_dev = cmul zbar (digD B) (digD B″)`
  with `cmul` the DefsD cocycle product (checked: `(x⋆y) τ = Σ_ρ x ρ · y (τ−ρ) ·
  z̄^{carryExp ρ (τ−ρ)}`). PROVED same day: `L3_DIV` forces the scalar law
  `c_R = c·c″` at the added anchor; the alignment-quotient carry identity
  `⌊(k+k′)/e⌋ = ⌊k/e⌋ + ⌊k′/e⌋ + carryExp` supplies the twist exponent; D2's
  generator law inlined against `cmul` directly (dodging the `CarryRingPack`
  dependence, keeping the unit sorry-free). Axioms: Lean core only
  ([propext, Classical.choice, Quot.sound]). MANIFEST statement re-synced.
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

## 9. FRONTIER — the stuck-rule adjudication PREP (2026-07-28, HC-1 frontier
designer; round-2 fleet + next-wave state)

STATE AT THIS SECTION: ~44/54 units PROVED on disk (D-layer 8/8 with D7
restated-proved same day; T-layer 11/12; C-layer 5/6; S-layer incl. S10 PROVED
at escalation and S13 PROVED under its adjudicated e_read = 1 scope; all 5
gates). The seven mapped obstructions below are the ENTIRE remaining frontier
of the fenced statements (R6's independent R-layer kernel is recorded in
`R6_carrierInstance.lean` and queued with the MovesR re-audit, not here; S16's
single sorry is unobstructed fleet backlog). Each item: KERNEL (the
machine-checked artifact) → NOTE TRACE → DIAGNOSIS → REFINEMENT → DISPOSITION.

**Disposition summary: 6 repairable-now · 0 needs-note-round · 1 seam-homed.**
One coordinated SIGN-OFF EVENT covers all statement/Defs changes below (F-1..F-6
in the table at §9.8); every change is additive or a refutation-forced
restatement; the note is INTACT at every item — no note-round required
anywhere.

### 9.1 T10_floorStaircase — conjunct 2 machine-refuted → restate on the STEP floor

KERNEL: `ScratchT10.lean` `T10_conjunct2_refuted` (Lean-core footprint): on ANY
realizable tower, ANY factor-interior block b, ANY block coordinate c with a
nonzero sub-top slot, `rl.floorC c < rl.floorB b` STRICTLY — via
`baseIdx c = OFF + blockEdge b` (mixed-radix decomposition), `0 < OFF <
deg Φ_top`, `slopeK > 0` forced by `slope_law` + kappa positivity, and
`Line.at b = intercept − slope·b` strictly decreasing. Conjunct 1 is rfl
(recorded in the scratch).

NOTE TRACE: LST(ii), MOVES 3743–3745 — "F_i(b) = old_i(slot(b)): ht-constant on
each current block" — and DOM's close, MOVES 3648–3651 — "the floor is the
current staircase: F_i(b) = old_i(slot(b))". The note's floor is old_i evaluated
at the SLOT of b (the block edge), i.e. a STEP function constant on each current
block. MovesC's own Defs say this in code: `floorOf` is "§C DOM's floor of RAW
lines; the step-function floor of a history is `History.floorH`"
(`MovesC/Defs.lean:268–271`), with the per-node quantization `Node.lineStep ν b
= ν.line.at ((b/ν.childWidth)·ν.childWidth)` (:507).

DIAGNOSIS: transcription defect in HC1's `floorC` — it bound T10's coordinate
floor to the RAW-line max `MovesC.floorOf … (T.baseIdx c)` (DefsCar :273–274),
the object DOM uses for LINE comparisons, where LST(ii) displays the STEP floor.
On a slope-K > 0 line the raw value strictly descends across the block, so
"ht-constant on each current block" is provable only for towers with all
slotBounds = 1 — the scratch's schema. The statement, not the note, is wrong.

REFINEMENT (statement F-1, sign-off; new defs additive, no fence event):
```lean
/-- read m's staircase at a base index (MovesC `Node.lineStep` convention):
the line evaluated at the left edge of b's frame-m fine slot. -/
noncomputable def TowerRealizable.lineStep (m b : ℕ) : ℚ :=
  (rl.line m).at ((b / T.frameWidth (m + 1)) * T.frameWidth (m + 1))

/-- THE HISTORY STEP-FLOOR at a coordinate (the note's F_i; MovesC
`History.floorH`'s shape over the tower's reads). -/
noncomputable def TowerRealizable.floorS (c : T.Coord) : ℚ :=
  Finset.sup' (Finset.range (T.K + 1)) (by simp)
    (fun m => rl.lineStep m (T.baseIdx c))
```
T10 conjunct 2 RESTATED: `∀ c, T.blk c = b → rl.floorS c = rl.floorB b` (conjunct
1 and the hypotheses unchanged). C1_LST leg (ii) restates identically in the same
event (C1's proof cites T10 verbatim; its other four legs untouched). PROOF
ROUTE (checked on the kernel's own lemmas): the m = K summand is exactly
`floorB b` (frame-K quantization of `baseIdx c = OFF + blockEdge b` with
`OFF < deg Φ_top` returns `blockEdge b`, per `ScratchT10.offset_lt`); for m < K,
the frame-m edge is ≥ the frame-K edge (nested radices: `frameWidth (m+1) ∣
frameWidth (K+1)`, a new tower lemma from the move records — `IsStandardLift`
degree law at increments, degree-preservation at recenterings), `Line.at`
decreasing gives `lineStep m ≤ (rl.line m).at (blockEdge b)`, and DOM
(`C2_DOM_floorForm`'s `dom_le`, at `blockEdge b ≤ interiorEnd` from `hb`)
caps it by `floorB b`. `floorC` STAYS as-is for DOM-side consumers; the
refuted-statement certificate `ScratchT10` is retained.
CONSUMER CHECK: C1(iii) and the S17 chain consume only `floorB` — unaffected.

DISPOSITION: **repairable-now** (restate T10(2)+C1(ii) on `floorS`; sign-off
F-1; proof from existing DOM engine + one divisibility lemma).

### 9.2 C6_alphabetCard — no card-K bridge corpus-wide → the CharP tie (Defs addition)

KERNEL: fleet round-2 verdict (commit 2f388c8; PROJECT_STATE 2026-07-28d):
conjunct 1 is T7's theorem (`p ^ aDim = Nat.card 𝔸`, PROVED via `IsPGroup` —
the alphabet is p-torsion by `grQ_torsion`), but conjuncts 2–3 equate/compare
`Nat.card ↥(T.stg (Fin.last T.K)).K` with p-powers, and NOTHING corpus-wide
ties `Nat.card K` to p: `Stage p F` carries `[Field F] [Finite F]` with NO
characteristic pin (`Moves/Defs.lean:106`), so `Nat.card K` is a power of
char F, and `Nat.log p (Nat.card K)` is junk off char p. The iff/strict legs
are unprovable as typed — and false on char-≠-p instantiations of the
interface.

NOTE TRACE: MOVES 2148–2165 — "𝔸(γ) = u(γ)·{Σ c_i·z̄^i : c_i ∈ 𝔸_k(γ_i)}, an
F_p-SUBSPACE of F_{k+1} … = [F_{k+1} : F_p] with 𝔸(γ) = F_{k+1} exactly when
every height in γ's slot tree is attainable … and STRICTLY SMALLER at shallow
heights". The note's F_{k+1} is an F_p-extension BY SETTING (residue fields of
extensions of ℚ_p); char F = p is intrinsic to §B2-DEF's semantics, never a
side condition. The Lean interface simply under-records the setting.

REFINEMENT (Defs addition F-2, additive-only, sign-off note): add ONE field to
`Tower` (HC1's own Defs, `DefsTower.lean`):
```lean
  /-- CHAR PIN (frontier adjudication 2026-07-28): the ambient residue field
  has characteristic p — intrinsic to the note's setting (F_{k+1}/F_p
  extensions, MOVES 2148–2165); the card-K bridge `Nat.card ↥K = p^[K:F_p]`
  is underivable without it (round-2 fleet kernel). -/
  hcharF : CharP F p
```
SIGN-OFF NOTE (drafted): additive field on an HC1-owned structure; NO `Tower`
literal exists anywhere on disk (grep-verified: no `Tower.mk`/anonymous-
constructor inhabitant yet), so no existing proof re-opens; every planned gate
instance (T2/S1/G2 ambients: `GaloisField 2 2` at p = 2) satisfies it by
instance; faithfulness: records the note's own setting, excludes only
note-rejected instantiations (char ≠ p ambients) — the doctrine's
"FALSE for instances the note would reject" direction, strengthening
falsifiability, weakening nothing. Chosen over a `TowerRealizable` card law
because C6 (and its S17 consumers) are deliberately realizability-free
(hyp: none), and characteristic is tower-intrinsic, not per-move data.
BRIDGE LEMMA (new, easy — lands in C6's file): `∃ d, 1 ≤ d ∧
Nat.card ↥(T.stg k).K = p ^ d` (finite subfield of a char-p field; mathlib
`CharP.card_eq_prime_pow`-class route via the `Subfield` instance). C6's proof
then: conjunct 1 = T7; conjuncts 2–3 = T8's per-coordinate product formula +
the bridge (full ⟺ every factor full ⟺ every slot image nonzero; one dead
coordinate drops a factor strictly — exponent comparison now in ℕ via the
bridge). C6's STATEMENT is unchanged — only `Tower` grows the field.

DISPOSITION: **repairable-now** (additive Defs field + bridge lemma; sign-off
F-2; C6's statement text untouched).

### 9.3 S7_childPin — narrowed to CoeffLocLaw conjunct (c) → the D.7(vi) pin, homed to S9

KERNEL: `lean/scratch_S7_escalation.lean` (escalation pass): conjuncts 1–2
(child Bézout + P2), 3 (S5′ digit shape), and CoeffLocLaw legs (a) AND (b) are
PROVED sorry-free from the recorded data alone — (a) via the Ein/Eout
weight-detecting evaluation (`coeffLocLaw_sub`, machine-checked, printed
axioms Lean-core), (b) via the NEW route `coeffLocLaw_sup`: the outgoing key
σ.Φ is a child rep of parent-scale weight σ.h ≥ 1, so an (S6b′) realizer with
scalar d·c_Φ^k at weight k·σ.h times the k-th power of the σ.Φ rep-unit
INVERSE is exactly `C (C d)` (the `CT_cancel` identity). THE WALL IS EXACTLY
leg (c), the z′-pin: decoding `IsLVecVal`/`lvecWeight zv = 0` against
`hbez`-determinacy leaves (⋆) `∃ v : Σᵢ vᵢ·wPrev(repᵢ) = −h′ ∧ Πᵢ cᵢ^{vᵢ} = 1`;
the weight leg is always solvable (v₀ := −h′·(transported parent vector)), but
its scalar is z̄^{h′·E} with E built from `child_dig_frame`'s EXISTENTIALLY
supplied `mfun` — the SAME uncontrolled frame twist as S8's kernel (the scratch
says so verbatim). {(a),(b) proved} + {(c) ⟺ the twist} is the exact
obstruction partition.

NOTE TRACE: the same displays as 9.4 below (MOVES 2395–2402: z = V^{−h}·Y^e BY
PINNING, z′ := V′^{−h′}·Y′^{e′} "explicit, no choice") — even `CoeffLocLaw`'s
own docstring cites it: "(P1) the z-pinning — the genuine z = V^{−h}·Y^{e} of
D.2/D.7(vi)" (`Moves/DefsL.lean:165–166`). The note pins (c)'s witness
LITERALLY; the recorded interface (bare `Stage` + `TransitionCoreL`) does not
carry the pin.

REFINEMENT (statement F-3, sign-off): S7 RESTATED to conclude conjuncts 1–3 +
CoeffLocLaw legs (a) and (b) — the scratch's proved shape, transplanted
verbatim (`S7_scratch` minus its (c) leg; footprints already Lean-core). Leg
(c) MOVES to S9d (§9.5), where the child is CONSTRUCTED with
z′ := V′^{−h′}·Y′^{e′} as the literal witness vector (weight leg: the
transported vector's Σ b·ν = 1 identity, already derived in the scratch
comment; scalar leg: 1 by construction — no twist exists on the constructed
child). No pin hypothesis is added to S7 itself: the corpus consumer of (c) is
S9's assembly alone (the scratch's own CONSUMER NOTE), so hypothesizing the pin
here would be dead weight.

DISPOSITION: **seam-homed** — (a)/(b)/1–3 transplant now; the (c) residual is
the D.7(vi)-pin seam, discharged inside S9d by construction (one seam with 9.4).

### 9.4 S8_childS6 — the twist symmetry vs TvecUnitLaw → the note PINS the twist; statement gains it

KERNEL: `S8_childS6.lean` in-file certificate (dual-audited Fable + Codex,
findings 1–11, 13 CONFIRMED): with ẑ := z̄, r := ord z̄, λ : ℤ, the twist
σ̃′ := σ′ with `R̃ f := C (ẑ^{λ·σ'.w f}) · σ'.R f` preserves EVERY Stage law of
σ′, `child_dig_frame` (via mfun + λe′·id), and every other hypothesis in scope
(none mention σ′.R), yet multiplies the pinned TvecUnitLaw product by
C (C (ẑ^λ)); at admitting numerics (𝔽₃ ≤ F ⊇ 𝔽₉, z̄ a generator, (e′,h′) =
(1,8), λ = 4) the shift is C (C (−1)) ≠ 1 — so NO proof of the conjunct exists
over the recorded hypothesis class. A twist SYMMETRY of the entire class, not a
missing lemma.

NOTE TRACE (the adjudication question: does the note pin the twist?) — YES.
MOVES 2395–2402 (D.7(vi)): "the stage carries the exponent VECTOR of its pinned
coefficient unit V over the representative list (P2); T = V^s·Y^t and
z = V^{−h}·Y^e BY PINNING (literal identities) … Transport:
V′ := Π_i in_{w′}(ũ_i)^{s·b_i} · in_{w′}(Φ)^{t} … Then u₀ := V′^{−h′}
(explicit, no choice); z′ := u₀·Y′^{e′}". MOVES 2410–2414 (D.7(vii)): "the
next stage's pinned unit is V′, its vector is the transported one, and the
D.3(b) literal identity re-runs verbatim". The child residual normalization is
an EXPLICIT CHOICE-FREE function of the parent data; the z̄-twist freedom
exists only in the Lean record (`child_dig_frame`'s `∃ mfun`), which
under-records the display. NOT a note gap — an interface under-recording.

REFINEMENT (statement F-4, sign-off): per the stuck rule, the statement gains
the pin — and the honest carrier of the pin is the CONSTRUCTION: S8's
TvecUnitLaw conjunct MOVES to S9d, stated of S9's constructed child (where V′
is the literal factorwise product and the product law is rfl-adjacent; the
scratch/kernel reduction shows outer-T/inner-z exponents already collapse from
parent laws — only the residue leg needed the pin). S8 RESTATED to its proved
leg: the child previous-read (I-aug) law `(σ'.e : ℤ) * σ'.wPrev σ'.Φ <
(σ'.h : ℤ)` (already closed in-file from `th.hiaug` + the records; keeps S8 a
theorem, no sorry). The kernel comment is retained in-file as the certificate
that no recorded-σ′ form is provable. EXPLICITLY NOT a note-round item: the
note's pin display is quoted above; nothing to send back.

DISPOSITION: **repairable-now** (S8 restated to the proved leg; TvecUnitLaw
homed to S9d where the note's pin is realized by construction; sign-off F-4).

### 9.5 S9_transStage — the assembly core: re-census + decomposition

KERNEL/STATE: S9 is the ONE remaining hard construction. Since the round-2
census: S10 (the recentering twin) is PROVED at escalation (37KB: Stage-literal
+ `shiftL` construction + res lemma — the assembly TEMPLATE now exists on
disk); S13 PROVED under the adjudicated D.9(d) scope; D7 RESTATED-PROVED (the
twisted DIG homomorphism with the anchor addition pinned — the carry-exact
scalar law hRmul needs). RE-CENSUS of S9's ~44 obligations (Stage: 12 data
choices + 25 law fields; StageCore: 11; StageCoreL extras: 2; TransitionCoreL:
12; pins: 3):

SUPPLIED (by proved units / rfl-by-construction):
* w-laws: hwmul + hvalgrp (S5 PROVED), submult (S4 PROVED), slot-min + hwult
  route (S2 PROVED), hK1 + hwΦ (S3 PROVED), hStretch (childW at j = 0 slots,
  definitional).
* (S6′): hS6a/hS6b via `L4_TRANSviii_a_R5_final`/`_b_R4` (clean Moves finals).
* child field + D-map surjectivity: S6 PROVED; CoeffLocLaw (a)/(b) + Bézout/P2
  + S5′ shape: the S7 scratch (§9.3, machine-checked).
* prevIaug: S8's proved leg (§9.4).
* TransitionData (10 fields), child_Tvec, the 3 conclusion pins: rfl-level
  from the construction data.
* arithmetic: he/hh/hcop/hbez/he1t from th + the (vii) Bézout split; hmonic/
  hdeg from `L3_liftMonic`; hreps by degree arithmetic; hTvec rfl.

REMAINING (the honest core — 1 definition + ~9 laws + assembly):
* `childR` — the D.7(vi)-NORMALIZED child residual on all of A (the new
  object; MOVES 2395–2418: normalize the minimal-slot development data by the
  transported unit T′^{−w′(f)}).
* its residual apparatus: hR0/hRne/hRadd/hRlt (additive laws via the slot-min
  ties), hRmul (via D7's cmul law + `L3_DIV` — the carry-exact product), hRΦ +
  hS5′ (by the normalization), `child_dig_frame` with mfun := THE alignment
  function (pinned, no ∃-slack — dissolving §9.3/§9.4's twist at the root).
* StageCore tie laws for the constructed pair: w_strict/w_jump/R_neg (childW/
  childR ties; S10's res-lemma pattern), SlotDecomp + CoeffFieldLawCore
  (transports via `L4_TRANSvii_R4` + S6).
* TvecLaw/TvecUnitLaw + CoeffLocLaw(c) — BY CONSTRUCTION (V′/z′ literal; §9.3/
  §9.4 land here).

DECOMPOSITION (six sub-units, pre-approved split; statement of S9 UNCHANGED):
* **S9r** (`DefsChild.lean`, additive + unit): `childR` definition + the S5′
  shape lemma (positions −t′·σ.w B; scalars = digPrime·(the pinned
  alignment)). Consumes D7, S2.
* **S9w**: hR0/hRne/hRadd/hRlt/hRmul + w_strict/w_jump/R_neg for
  (childW, childR). Consumes D7, `L3_DIV`, S2/S4/S5. HARD (the one genuinely
  new algebra block).
* **S9a**: the Stage literal + arithmetic/valuation legs (data + he..he1t,
  hmonic/hdeg, hwΦ, hStretch, hK1, hreps, hTvec, hWS).
* **S9b**: weightSet := 𝒜′ + hS6a/hS6b via the TRANSviii finals.
* **S9c**: StageCore assembly + TransitionCoreL records (TransitionData rfl
  fields, child_Tvec, pinned child_dig_frame) + SlotDecomp/CoeffFieldLawCore.
* **S9d**: TvecUnitLaw σ′ + CoeffLocLaw σ′ (transplant scratch (a)/(b);
  (c) + the product law by construction) → closes StageCoreL σ′ and DISCHARGES
  the §9.3/§9.4 seam. Then S9 = ⟨literal, S9c, S9a–S9d⟩.

DISPOSITION: **repairable-now** (hard; no note contact — D.7(vi)–(vii) supply
every construction; the S10 template de-risks the literal+res-lemma pattern).

### 9.6 S11_towerSpine Part 1 — partial transport succeeded → carry the core, name the residual

KERNEL: `S11_towerSpine.lean` in-file, TWO verdicts. (I) route failure: S9/S10
are ∃-shaped (existential child), type-mismatched against `StageCoreL
(T.stg i.succ)` for the RECORDED child. (II) semantic countermodel (the
sign-twist σ″.R f := σ′.R f·C(ξ^{σ′.w f}), ξ ∈ FQˣ, ξ^{h′} = 1, ξ ≠ 1):
preserves every round-2 Stage field and every carried record, breaks
TvecLaw/TvecUnitLaw — so Part 1 is UNPROVABLE from the carried witnesses. THE
PARTIAL TRANSPORT SUCCEEDED (verdict II's positive half, machine-verified at
escalation): wPrev_mul/wPrev_ult (child_wPrev + parent laws), both reps legs,
w_strict (the w(−1) = 0 valuation trick), R_neg (child_dig_frame at B = 1 pins
z̄^{mfun 0} = 1), prevIaug (the move's hiaug + threshold, S8-leg-2's pattern).
The RESIDUAL CORE — exactly the legs the records cannot pin — is the
twist-class set: {w_jump, TvecLaw, tvec_unit (TvecUnitLaw), coeff_loc,
SlotDecomp, CoeffFieldLawCore}.

NOTE TRACE: the note's tower induction CONSTRUCTS each child ("The stage
axioms (S1′)–(S5′), (S6a′), (S6b′) all hold: the induction closes with the
split axiom", MOVES 2464–2465) — in the note, a tower level IS the constructed
package; a `Tower` whose moves record less than stage-hood is a Lean
under-recording, same species as §9.4.

REFINEMENT (Defs F-5, sign-off + one new certificate unit):
(a) `MoveWitness` gains the child core (additive field on each constructor):
```lean
  | inc (…) (core : TransitionCoreL σ σ' Φhat e' h' zbar)
        (core' : StageCoreL σ')  : MoveWitness σ σ'
  | recenter (…) (core : IsRecenteringCore σ σ' cc tt)
        (core' : StageCoreL σ')  : MoveWitness σ σ'
```
Faithfulness: the note's move IS a stage-producing construction (trace above);
S9/S10 (the ∃-existence theorems, statements unchanged) prove enriched
witnesses EXIST for every legal read, so `Tower` inhabitation is unweakened —
both directions stay recorded, exactly as S11's docstring anticipated. No
MoveWitness LITERAL exists on disk (grep-verified: no constructor application
anywhere), so no inhabitant re-opens; HOWEVER the constructor-arity change
ripples through ~10 PATTERN-MATCH sites in Defs recursions (`eBirthAux`/
`strAux`) and the proved units T3/T4/T6/T7/C2/S13/S11-Part-2 — each needs one
extra `_` binder, a mechanical edit with NO content change, followed by the
standard footprint re-verify of the touched cones (stop-the-line on any
regression). Part 1's proof becomes Fin.induction + projection (~10 lines);
Part 2 is ALREADY PROVED in-file (both match arms) and only re-binds.
(b) THE RESIDUAL AS ITS OWN UNIT — **S11a_coreTransport** (NEW, certificate):
from `StageCoreL σ` + `TransitionCoreL σ σ'` + σ′'s bare Stage laws, derive
StageCore σ′ MINUS the residual set — i.e. wPrev_mul, wPrev_ult,
reps_nonempty, p_is_rep, w_strict, R_neg, prevIaug (the escalation's verified
transport, transplanted). Value: it certifies the F-5 enrichment is MINIMAL
(everything else was already derivable — the field adds exactly the
twist-class legs the kernel proved independent), and it shrinks S9c's
per-field work. The in-file countermodel comment is retained as the
independence certificate.

DISPOSITION: **repairable-now** (F-5 Defs addition + projection proof + the
S11a certificate unit; residual core named and homed to S9d's construction).

### 9.7 S17_levelMeasureExact — the L6 mirror → fold §4.6's spec into the restatement

KERNEL: `ScratchS17.lean` `S17_scratch_with_hcore_hzsol` — a SUFFICIENCY
CERTIFICATE, proved with ZERO sorry, Lean-core footprint: S17's fenced
statement PLUS exactly two hypotheses closes completely:
`hcore : StageCore (T.stg k.castSucc)` and
`hzsol : ¬ E.IsSolution (Θ (code 0))`. Necessity: (A) nothing pins
`E.IsSolution (Θ (code 0))` when 0 is the only deg-<D preimage — the
`L6_measureExact_R4`:189 gap = §4.6(b)'s "+hzsol" spec (bfdfb5e); (B) the only
StratumData ↔ LandingCylinderL bridge (`L5_landTwoSided`, the §4.5 repair
theorem) needs StageCore at the level stage, which S17 does not carry and the
tower did not propagate (§9.6's kernel). {A, B} is the EXACT obstruction set —
countermodels up, this proof down. CRUCIALLY the scratch proof consumes
`L5_landTwoSided` (repair file) + `L0_FactA_exists` + `L2_P6ii` directly and
inlines `development_truncate` — it NEVER consumes `L6_measureExact_R4`, so
the §4.6 dep-sorry pair drops out of HC1's cone entirely.

NOTE TRACE: D.11, MOVES 2672–2718 — statement scope ONE move, count law +
dichotomy; the note's stratum is a NONZERO-f object read against a genuine
stage of the tower ("at every tower level … with the stage hypotheses
DISCHARGED by the induction", blueprint D8) — hcore is the note's own standing
hypothesis, and the zero-code clause is jet-chart data the fenced Moves
statement omitted (the in-file FLAG at :189, §4.6(b)). The note is intact.

REFINEMENT (statement F-6, sign-off — the concrete restatement, folding
§4.6's spec): S17 RESTATED as the scratch theorem VERBATIM — + `hzsol` as an
explicit hypothesis (part of the jet chart's data, exactly as code/Θ/E
already ride per deviation D-9), + `hcore` — carried EXPLICITLY until F-5
lands, then discharged from the tower (`(S11 Part 1 k.castSucc).core`) and
dropped from the signature in the same sign-off event if F-5 is ratified
first (adjudicator's ordering choice; the scratch form is the safe landing
either way). Proof: transplant `ScratchS17` (zero new work). LEDGER EFFECTS:
§4.6's dep-sorry entry moves from "consumed by S17" to "Moves-tail-only" —
HC1's hypothesis-field ledger (§5) empties its dep-sorry row; `sorryAx`
leaves every HC1 cone. `L6_measureExact_R4`'s own repair (§4.6 (a)/(b))
remains queued for the Moves tail fleet on its own schedule, no longer
blocking HC1.

DISPOSITION: **repairable-now** (restate + transplant; sign-off F-6; kills
HC1's last dep-sorry).

### 9.8 The coordinated sign-off queue (one event, six entries)

| id | change | kind | units touched |
|---|---|---|---|
| F-1 | T10 conjunct 2 (+C1 leg (ii)) → `floorS` step floor; `lineStep`/`floorS` defs added | refutation-forced restatement + additive defs | T10, C1 |
| F-2 | `Tower` + `hcharF : CharP F p`; card-K bridge lemma | additive Defs field | DefsTower, C6 |
| F-3 | S7 → scratch's proved shape (legs (a)/(b) + 1–3); leg (c) to S9d | refutation-narrowed restatement | S7 |
| F-4 | S8 → its proved (I-aug) leg; TvecUnitLaw to S9d | refutation-forced restatement (note pins the twist — quoted) | S8 |
| F-5 | `MoveWitness` + `core' : StageCoreL σ'` (both constructors); S11a certificate unit | additive Defs field + new unit | DefsTower, S11, (+S17 via hcore) |
| F-6 | S17 → the ScratchS17 form (+hzsol, +hcore-until-F-5) | restatement per §4.6 spec | S17 |

S9's decomposition (S9r/S9w/S9a–S9d, §9.5) adds units without touching any
accepted statement — no sign-off entry needed; `DefsChild.lean` is additive.
POST-EVENT STATE if all six ratify: the frontier reduces to ONE hard
construction block (S9r + S9w) + five assembly/projection proofs, zero
dep-sorries, zero note-round items, the note intact at every point.

END OF FRONTIER SECTION (7 obstructions: 6 repairable-now, 0 needs-note-round,
1 seam-homed (S7 → the S9d construction seam); sign-off queue F-1..F-6).

## 9.9 EXECUTION RECORD (2026-07-28, queue applier — Asvin's definition-change
authority db323cc; Codex confirm-after per that marker; acceptance = proofs run
through)

All six sign-off entries + the S9 decomposition LANDED; every touched file
`lake env lean` green with `-o` olean refresh in topological order; footprints
as listed (Lean-core = [propext, Classical.choice, Quot.sound]).

* **F-1 EXECUTED as drafted.** `TowerRealizable.lineStep`/`floorS` added to
  DefsCar (additive, §9.1's displays verbatim modulo the `rl.` receiver); T10
  conjunct 2 + C1 leg (ii) restated on `floorS`; conjunct 1/hypotheses/other C1
  legs untouched; `floorC` stays for DOM-side consumers; `ScratchT10` retained
  and green. T10's sorry remains open per the §9.1 proof route (fleet work);
  C1 compiles delegating to T10 verbatim (sorryAx via T10 only).
* **F-2 EXECUTED; bridge PROVED.** `Tower.hcharF : CharP F p` added (additive
  field; no Tower literal existed on disk — re-verified by grep at execution).
  `C6_cardK_bridge` landed in C6's file and is PROVED (Lean-core:
  `RingHom.charP` at `K.subtype` + `FiniteField.card`), exceeding the "statement"
  minimum. C6's own statement UNCHANGED per §9.2 (the queue-table gloss "C6
  restated to consume it" resolved in favor of §9.2's explicit "statement
  unchanged" clause); C6's open proof consumes the bridge for conjuncts 2–3.
* **F-3 EXECUTED; S7 PROVED.** Restated to the scratch's proved shape
  (conjuncts 1–3 + CoeffLocLaw legs (a)/(b)); `scratch_S7_escalation.lean`'s
  machinery transplanted verbatim into the unit; footprint Lean-core. Leg (c)
  homed to S9d. The scratch file remains on disk (not part of the build).
* **F-4 EXECUTED; S8 PROVED.** Restated to the (I-aug) leg (the in-file proof);
  footprint Lean-core; the dual-audited twist-symmetry certificate retained in
  the file header verbatim (the independence certificate F-5/S9d rest on).
* **F-5 EXECUTED; S11 + S11a PROVED.** `MoveWitness` gains
  `core' : StageCoreL σ'` on BOTH constructors (docstring records the warrant +
  the minimality certificate); arity ripple fixed at all match sites —
  DefsTower `eBirthAux`, T3 (×2), T4 (×2), T6 (rcases), T7 (×2), C2 (×2), S13,
  S11 (statement + both parts) — every touched proved unit re-verified
  Lean-core (no footprint regression). S11 Part 1 = Fin.induction + `core'`
  projection, Part 2 re-bound: S11_towerSpine now PROVED, Lean-core.
  `S11a_coreTransport` CREATED **and PROVED** (Lean-core): the seven non-twist
  legs from `StageCoreL σ` + `TransitionCoreL` + `TransHyp` alone (the §9.6
  sketches re-derived in-file: child_wPrev transport, reps append legs,
  bare-Stage w_strict via the w(−1) = 0 trick, R_neg via `child_dig_frame` at
  B = ±1 pinning z̄^{mfun 0} = 1, prevIaug via hiaug + threshold).
* **F-6 EXECUTED; S17 PROVED.** Restated to the `ScratchS17` form (+`hzsol`,
  +`hcore` — the adjudication's safe landing; the post-F-5 discharge of `hcore`
  via `(S11_towerSpine T).1 k.castSucc |>.core` is RECORDED as available but
  NOT taken in this event); proof transplanted; footprint Lean-core. Import
  hygiene deviation: the unused `L6_measureExact_R4` import dropped,
  `L2_P6ii_R3` imported directly — the §4.6 dep-sorry pair leaves HC1's cone
  entirely (MANIFEST dep_sorries row emptied). `ScratchS17` retained.
* **S9 DECOMPOSITION CREATED (typing rendering recorded).** §9.5 displays no
  Lean statements, so the units were typed per the corpus's E-phase precedents,
  every content pin from §9.5 preserved:
  - `DefsChild.lean` (additive): `ChildResData` = the choice SPEC of childR
    (fields = §9.5's own law lists verbatim: hR0/hRne/hRadd/hRlt/hRmul at
    (childW, ·), the S5′ PINNED shape (= the K1 VertexPin clause), hRΦ = z^{s′},
    + the two Rc-involving tie laws w_jump/R_neg); `childR` by choice against it
    (the childW/`Tower.side` precedent, junk fallback); `childWeightSet` = 𝒜′.
    The S9r/S9w seam = the structure boundary (recorded in the header).
  - `S9r_childR` = `Nonempty ChildResData` (sorry — the hard construction
    block); `S9w_residualLaws` = the law pack of the DEFINED childR: nine
    projections PROVED through the choice + the childW-only w_strict as the one
    genuine open leg (sorry).
  - `S9a`/`S9b`/`S9c` = cumulative-∃ statements over the constructed child with
    the construction RECORDED F-frame-wise (TransitionData / TransitionCoreL +
    `VertexPin` + the childW tie [+ weightSet = 𝒜′ at S9b; + StageCore at
    S9c]) — the ↥K/↥K′ cast wall stays inside S9a's proof, where §9.5 put it
    (all three sorry).
  - `S9d_pinVerify` **PROVED** (Lean-core): TvecUnitLaw σ′ ∧ CoeffLocLaw σ′
    from the pin — `K1_tvecUnitLaw_of_pin` + S7's transplanted legs (a)/(b) +
    `K1_coeffLocC_of_pin`; plus `S9d_stageCoreL` closing `StageCoreL σ′` given
    S9c's StageCore. The §9.3/§9.4 seam is DISCHARGED at the statement level;
    its non-vacuity obligation rides S9c's construction (K1 faithfulness flag).
  - S9's own statement UNCHANGED (per §9.8: no sign-off entry needed).
* **POST-EVENT STATE (as §9.8 predicted):** the frontier = the construction
  block S9r + S9w(w_strict) + S9a/S9b/S9c assemblies + T10's floorS proof +
  S16's fleet backlog + the open E-phase sorries unaffected by this event;
  ZERO dep-sorries in any HC1 cone; the note intact at every point. MANIFEST
  re-synced (61 units; sign-off record key `signoff_2026-07-28`).

* **S9 DECOMPOSITION UNBUNDLED (2026-07-28 remediation round — the Codex
  batch-confirmation S9 rejection repair; grounded finding: the E-phase typing
  above bundled §9.5's S9w law list as `ChildResData` FIELDS, relocating S9w's
  billed hardness into S9r's inhabitation sorry and reducing S9w to cosmetic
  projections).** Restored shape, all files `lake build` green:
  - `ChildResData` (DefsChild) = the CHOICE-SPEC CARRIER ONLY: `Rc` + the two
    D.7(vi) normalization pins (`hRPhi = z^{s′}`, the S5′ pinned shape) —
    exactly §9.5's S9r billing ("`childR` definition + the S5′ shape lemma").
  - `ChildResLaws` (DefsChild, NEW): the §9.5 S9w law list as a `Prop` ON a
    carrier (hR0/hRne/hRmul/hRadd/hRlt + w_jump/R_neg) — no longer fields.
  - `S9w_residualLaws` RESTATED as the HARD unit's OWN theorem: (i) a carrier
    satisfying the FULL `ChildResLaws` pack EXISTS (takes th + (s′,t′) + hbez′ +
    ht′0, like S9r), ∧ (ii) the childW-only w_strict tie (one sorry — the §9.5
    "one genuinely new algebra block", now honestly homed). Its former
    proved content survives as the clearly-labeled PROJECTION corollary
    `childR_laws` (PROVED, Lean-core): given S9w's ∃, the defined `childR`
    carries pins + laws through the choice.
  - `childR` re-keyed to choose against carrier + `ChildResLaws` — the SAME
    witness class as the pre-unbundle bundled structure (zero denotation
    drift).
  - `S9r_childR` statement text unchanged (`Nonempty ChildResData`), semantics
    now the carrier SEED (weaker); once S9w lands it follows from S9w's first
    conjunct — kept as the named §9.5 seed unit.
  - Consumers re-threaded (docstrings): S9a (childR laws via S9w/childR_laws),
    S9c (w_jump via the `ChildResLaws` conjunct, formerly `ChildResData.hWjump`);
    no S9a–S9d STATEMENT touches ChildResData/childR, so all statements are
    byte-unchanged. Footprints: childR_laws Lean-core; S9r/S9w/S9a/S9b/S9c/S9
    sorryAx as expected (banked sorries unchanged in count: S9w still exactly
    one).

* **S9a RESTATED WITH THE NOTE'S INCREMENT GUARD + CENSUS RE-RUN (2026-07-28,
  adjudicated restate-after-refutation; the bc86e1b acceptance-fleet refutation
  closed out).** The unguarded S9a was REFUTED at the `σ.e * g = 1` corner:
  `TransitionData.child_reps` puts the outgoing key `σ.Φ` on the child list,
  `Stage.hreps` forces it into `C_Φ̂` (`deg σ.Φ < deg Φ̂`), and at the corner
  `deg Φ̂ = σ.e·g·deg σ.Φ = deg σ.Φ` (L3_liftMonic) — contradiction.
  ADJUDICATION (note-read): the note's LST tower-induction step carries the
  guard EXPLICITLY — MOVES 3755–3757: "STEP at an INCREMENT ν_{i+1} (stage data
  (e_{i+1}, h_{i+1}), e·g > 1): the frame-(i+2) tower adds exactly ONE inner
  level — the just-read key Φ̂_{i+1}"; the corner is the note's RECENTERING
  species (MOVES 3766–3767: "e_read = 1, degree unchanged … the key is
  REPLACED"), handled by the PROVED S10_recStage. §9.5's S9a spec had dropped
  the guard in transcription. Executed:
  - STATEMENT: `S9a_stageLiteral` gains `hEG : 1 < σ.e * g` (D.3's degree
    ratio; `Tower.slotBound`'s increment value). No other change; no consumers
    import S9a yet (ripple-free).
  - KERNELS (in-file, PROVED Lean-core): `S9a_ungated_corner_refuted` — the
    refutation, machine-checked at the corner from `th` + `TransitionData`
    alone; `S9a_corner_fails_guard` — the corner instance fails the restated
    hypothesis (the corner-exclusion verification).
  - CENSUS RE-RUN under the guard: the FULL Stage literal now ASSEMBLED in
    S9a's proof — data legs (the (vii) Bézout split, P2-pinned at e′ = 1),
    hmonic/hdeg (L3_liftMonic), w := childW with hwmul/hvalgrp (S5), hwΦ/hK1
    (S3), hStretch (L4_TRANSii), hwult (NEW in-file: slotwise development
    addition + the parent ultrametric per slot), reps/hreps + Tvec/hTvec (the
    guard's degree gap `deg σ.Φ < deg Φ̂`), weightSet := 𝒜′ with hWS
    definitional, hS6b AND the above-threshold half of hS6a (L4_TRANSviii_b +
    the carrier's S5′ pin, exact scalars), R/hR0/hRne/hRmul/hRadd/hRlt/hRΦ/hS5
    (S9w's lawful carrier), `TransitionData` all-definitional on the literal,
    `VertexPin` = the carrier's `hS5'` verbatim, childW tie `rfl`.
  - SINGLE RESIDUAL (the file's one sorry, exactly placed): **the (S6a′)
    BELOW-THRESHOLD STRIP** — `hS6a` at `ν ≤ σ.w Φ̂`. Under the raw D.7(vi)
    pin (`mfun ≡ 0`), the realizable digit set at `ν = e·w̃ + j·h` is the
    TWISTED orbit `⋃_slots D(w̃)·z̄^{j·s − t·w̃}` (twist `= (s·ν − w̃)/h`; the
    twist-0 slot `(t·ν, s·ν)` leaves the window on most of the strip), while
    `Stage.hS6a` demands the untwisted `F_Qˣ` — the exact `∃ m` that
    `L4_TRANSviii_a` records. Robust counterexample numerics (semantic;
    instance not yet built): depth-2 parent `K = 𝔽₉/F_Q = 𝔽₃` (unramified
    g = 2 root: weight-0 digits exactly `𝔽₃ˣ`), parent side `(e,h) = (3,2)`,
    Bézout `(1,−1)`, any read on top (guard passes): at `ν = 2` the window is
    the single slot `(1,0)`, digit set `𝔽₃ˣ·z̄` ∌ `F_Qˣ`. So the strip leg is
    NOT a proof gap but a NORMALIZATION MISMATCH: the note's (S6a′) lives in
    the V′-normalized child coordinate (MOVES 2395–2418), where the
    transported orbit lands untwisted; `VertexPin`/`hS5'` pin the RAW
    z̄-evaluation coordinate. ADJUDICATION QUEUED: either re-pin
    `VertexPin`/`ChildResData.hS5'` to the alignment function (§9.5's own
    "mfun := THE alignment function (pinned, no ∃-slack)"; the K1 faithfulness
    flag pre-authorized the bridge re-instantiation), or scope the child hS6a
    obligation to the above-threshold range at increment children. S9b's
    "(S6a′) via the TRANSviii finals" billing inherits the same seam
    (viii_a's conclusion carries `∃ m`, not `m = 0`).
  - Footprints: `S9a_ungated_corner_refuted`/`S9a_corner_fails_guard`
    Lean-core; `S9a_stageLiteral` sorryAx (its own strip sorry + the S9w
    cone), as the unbundle event predicted. In-file sorry count unchanged (1).

## 10. THE V′ KERNEL — the read-functional carry algebra in the aligned frame
## (designed 2026-07-28, V′-kernel pass; the ONE design behind every remaining
## hard-core sorry: S9w-(i), S9a's hS6a strip, HC2's K1_readVertexPin_nonrec)

VERDICT FIRST. The three hard residuals are three instances of ONE object —
the D.1(e) residual pack rebuilt at a NEW (e★, h★, s★, t★)-position law over
an existing stage's data, with a scalar transform:

  (†)  wV(f) := min_{j} ( e★·σ.w(B_j) + j·h★ )        (the read functional)
       RV(f) := Σ_{j minimizing} C( φ(slot-j digit) ) · T( j·s★ − t★·σ.w(B_j) )

over the P-development f = Σ B_j·P^j, where the instance is fixed by
(P, (e★,h★,s★,t★), φ):

* DESCENT instance (S9w): P = Φ̂ (the TransHyp lift), (e★,h★) = th's (e′,h′),
  φ = evaluation z ↦ z̄ (= `σ.digPrime zbar`) into K′ = σ.nextField z̄.
  wV = the EXISTING `childW σ Φ̂ e′ h′`; RV = the explicit `childR` carrier.
* REGRADE instance (K1-nonrec): P = σ.Φ (the SAME key), (e★,h★) = the
  RECORDED READ pair (ν.e, ν.h), φ = identity on ↥σ.K.
  wV = `childW σ σ.Φ ν.e ν.h`; RV = the read-graded residual — THE V′ FRAME.

KEY FINDING 1 (the campaign finding the charge asked for — stated LOUDLY,
but it is GOOD news): **the feared B2-DEF gap does not exist.** The
obstruction record at `HC2/K1_vertexPin.lean` item 4 derives the read-pair
vertex law by hand because no note display seems to cover it — but §B2-DEF's
D.3–D.8 are LEVEL-FREE, STAGE-INDEXED displays ("Fix a stage with read index
(e, h)…", MOVES 2017–2019), and the note's stages ALWAYS carry the index of
the side being read. HC2's recorded stages carry their BIRTH pair instead
(HistoryCoherent ties `TransitionCoreL … ν_i.e ν_i.h`; the next node reads a
NEW pair). The read-pair landing is therefore §B2-DEF's OWN D.5 + D.8 run at
the REGRADED frame (†) — an *interface* object HC1 never constructed, not
missing note mathematics. Two verbatim checks:
* The recorded lift is (†)-equal-weight: `IsReadLift` weights
  σ.w(t_k) = h★·(g−k) give e★·σ.w(t_k) + (e★k)·h★ = e★·h★·g for every
  present slot and for the leading slot — EXACTLY D.5's "EQUAL WEIGHTS"
  display (MOVES 2268–2269) transposed to wV; hence
  `IsReadLift σ ψ g e★ h★ Φ̂` IS the standard-lift shape OF THE REGRADED
  FRAME (wVPrev := σ.w, index (e★,h★)) — the D.5 residual computation
  re-runs verbatim to RV(Φ̂) = z^{m̂★}·ψ(z), m̂★ := −t★·h★·g (MOVES 2270–2276).
* The obstruction record's displayed vertex value is D.8-(VERTEX) at (†):
  F(μ) = wV(f) − μ·wV(Φ̂) + μ·h★ = gam − μ·(e★·g − 1)·h★ — the record's
  formula, exactly (Case J sealed this empirically at 12 strata).

KEY FINDING 2 (FORCED Defs adjudication — the strip's real content; SIGN-OFF
REQUIRED, queued as V5 below). `Stage.hS6a`'s untwisted form is an
OVER-TRANSCRIPTION of the note's (S6a). The note's axiom is "every index is
realized … whose digit is c·(THE INDEX'S FORCED MONOMIAL CLASS) with c
ranging over the CONSTANT orbit group O := F_Qˣ" — the orbit group AT ITS
FIXED POINT (D.2, MOVES 1964–1971, rev D⁶/pass-14 finding 1), and D.7(viii)'s
child realizers have dig′ = "c·(a fixed z̄-monomial class)" (MOVES 2431–2435).
The Lean field hard-codes the fixed class to the trivial one. That form is
machine-refuted on the strip (§9.9's S9a record; F₉/F₃ numerics) — and NO
re-pin of `hS5'`/`VertexPin` can rescue it:
* mfun ≡ 0 (the raw z̄-evaluation pin) IS the note's V′ normalization — the
  parent z-class evaluates to the SCALAR z̄ under the frame change
  (D-injectivity on degree-0, D.7(v); the parent pinning identity
  z = V^{−h}Y^{e} pushes to Π dig′(ũ)^{−h·b_i}·dig′(Φ)^{e} = z̄ in F′), so
  the "alignment function" of §9.5 is the ZERO function. THE WARRANT DISPLAY
  (recorded 2026-07-28 mechanical-closer round, closing VPRIME_CONFIRM gap 2 —
  the D.7(vi)–(vii) excerpt 2392–2418 alone does NOT state this; the pin
  lives one clause EARLIER): **D.7(v)'s own D-map definition, MOVES
  2364–2367** — "Define D on each coefficient piece gr^Ĉ_δ by D(x) := R(x)
  mod ψ ∈ F′ — ADDITIVE per piece, multiplicative across pieces (Lemma
  DIV(iii)), injective on each piece (width < g)". Reduction mod ψ IS
  evaluation at the root z̄ under F′ = F[z]/(ψ) ≅ F(z̄) — i.e. the Lean
  `digPrime` (`Moves/Defs.lean`: `eval₂ σ.K.subtype z̄ (σ.R B)`). The child
  digit map is DEFINED as the raw evaluation of the parent residual, so
  there is no alignment twist to normalize away; degree-0 injectivity
  (MOVES 2388–2390) + the pinning identity (D.7(vi) PINNING, MOVES
  2395–2399) then push the parent z-class to the scalar z̄ as displayed
  above. NOT the polOM normalization (that is HC2's D.10 lift apparatus);
  the warrant is the D.7(v) definition itself; and
* any OTHER multiplicative renormalization is a linear twist mfun = m₁·id
  (additivity mod ord(z̄) forces linearity), and the strip windows contain
  only g consecutive twist values λ (slots at weight ν are
  (γ, j) = (s·ν − λ·h, t·ν + λ·e), twist = λ): whenever e.g. σ.e | ord(z̄),
  e·m₁ ≡ −t (mod ord z̄) has no solution (gcd(e, ord z̄) = e ∤ t since
  th ≡ 1 mod e) — the untwisted demand is unsatisfiable at depth ≥ 2, PERIOD.
So the §9.9 queued adjudication resolves: NOT a re-pin (option 1 is vacuous),
NOT a scope-down (option 2 breaks D.7(viii)'s own consumer recursion — the
next TRANS consumes (S6a) realizers at ALL indices, strip included). The
faithful field is the FIXED-POINT COSET form (V5).

KEY FINDING 3 (a second forced interface fact, sized small). The regraded
frame CANNOT be a full `Stage`: its coefficient weights under wVPrev = σ.w
lie in σ.e·ℤ (hStretch), so `Stage.hS6b`'s quantifier "∀ ν > wPrev Φ" (the
D.9(b) cofinite range, true at genuine stages) is UNSATISFIABLE at a regrade
for σ.e > 1. Hence the proved Stage-typed D.8 assets (`L5_landVertex*`)
cannot be cited verbatim at the regrade; the landing re-runs at a PARTIAL
pack (V0's `ReadFrame`), with the L5 files as the worked Lean pattern. All
other fields (hS6a included — regrade scalars are PRESERVED, no z̄ enters at
the same level) do transport; hS6b alone is the blocker.

DEMOTION NOTE (so nobody hunts for a missing lemma): in the TOTAL (evaluated)
V′ coordinate the carry cocycle is INVISIBLE — z̄^{e·⌊k/e⌋ + ρ} recombines,
positions add exactly, and hRmul needs only `L3_DIV`'s evaluated identity.
The proved D-layer (D1–D8, `cmul`, `digD`) is the GRADED certificate of the
alignment's well-definedness (and stays cited by any consumer that needs
positions split mod e_birth); it is NOT load-bearing for V8's product law.
§9.5's "hRmul via D7's cmul law + L3_DIV" reads, post-design: via L3_DIV;
D7 certifies.

### 10.1 The unit DAG (files `HC1/V*_*.lean`, all ADDITIVE; zero axioms;
### `sorry` only as E-phase placeholders inside the new units)

Dependency shape:
  V0 → V1 → V2 → V3 → V4 → V9   (the regrade/K1 chain)
  V0 → V6 → (V5 sign-off) → V7  (the aligned-orbit/strip chain)
  V0 → V8                       (the descent/S9w chain; V8 ⊥ V1–V4)
V5 is a SIGN-OFF EVENT (Defs restatement), not a proof unit; V7 and the
TRANSviii_a repair are gated on it.

* **V0 `DefsV.lean`** (definitions only, no theorems, no sorry).
  - `ReadPair σ e★ h★ s★ t★ : Prop` := 1 ≤ e★ ∧ 1 ≤ h★ ∧ gcd = 1 ∧ Bézout ∧
    (e★ = 1 → t★ = 0) ∧ **(e★:ℤ)·σ.h < h★** — the read-form (I-aug)
    steepness (D.4, MOVES 2219–2220 "λ > w(Φ)" at the stage scale; on the
    HC2 side extracted from HistoryCoherent's slope law + strict steepening:
    h_{i+1} > h_i·e_{i+1}·e_i·g_i ≥ e_{i+1}·h_i — a short lemma in V9).
  - `ReadResData σ e★ h★ s★ t★ : Type` — the regrade carrier, mirroring
    `ChildResData`: `Rv : Polynomial ℤ_[p] → LaurentPolynomial ↥σ.K` + the
    two pins `Rv σ.Φ = T s★` (key pin; slot-1 arithmetic 1·s★ − t★·σ.w 1 = s★)
    and the S5-shape pin `∀ B ≠ 0, inC σ.Φ B → Rv B = C(digit scalar of
    σ.R B)·T(−t★·σ.w B)` — scalars PRESERVED, positions re-forced (the (S5)
    position law at the new pair, MOVES 1960–1963).
  - `ReadResLaws` — the D.1(e) law-pack Prop on a carrier w.r.t.
    `childW σ σ.Φ e★ h★` (NOTE THE REUSE: wV at the same key IS `childW`
    with Φhat := σ.Φ — no new functional is defined), same seven conjuncts
    as `ChildResLaws`.
  - `ReadFrame σ e★ h★ s★ t★ : Type` — the PARTIAL stage pack (Finding 3):
    a lawful carrier + the wV laws (hwmul/hwult/hwΦ/hK1-at-Φ/hStretch
    wV = e★·σ.w on C_Φ) + hS6a in the CURRENT form (untwisted — it HOLDS at
    regrades, V6a) — everything the D.5/D.8 reruns consume; NO hS6b, NO
    hvalgrp, NO reps/Tvec.
  Falsifiability: every pin is an equation against existing objects; wrong
  positions break V2's hRmul at the first product.

* **V1 `V1_readWPack`** — the read functional's laws at the same key.
  STATEMENT: for σ cored, `ReadPair` hypotheses: `childW σ σ.Φ e★ h★` has
  the slot-min/attained-min pack (S2 instance at Φhat := σ.Φ — signature
  admits it verbatim), hwmul, hwult, and the Q-ASCENT lemma: for parent
  coefficients B·B″ = Q·σ.Φ + R_dev (monic division), the Q-slot's
  (†)-value exceeds the R_dev-slot's by h★ − e★·σ.h > 0 (steepness).
  moves_ref: D.7(i) (MOVES 2331–2337) at the same-key instance; D.4.
  deps: S2_childW, σ's hRmul/hwmul/hwult/hK1. difficulty: medium.

* **V2 `V2_readResidual`** — the lawful regrade carrier exists:
  `∃ D : ReadResData, ReadResLaws D` (+ w_strict, the S9w-(ii) mirror).
  Construction: RV per (†) — scalars from σ.hS5's monomial digits (parent
  coefficients only, so every slot digit IS a monomial), positions
  (j − t★·wV(f))/e★ = j·s★ − t★·σ.w(B_j), injective in j across minimizing
  slots (elementary: the map j ↦ (j − t★γ)/e★ on the tie set), so RV(f) ≠ 0.
  hRmul: V1's Q-ascent + σ.hRmul on slot products + the position additivity
  (exact, carry-free in the total coordinate — see the DEMOTION NOTE).
  moves_ref: D.6/D.7(i)–(iii) read at the level-free stage; D.5's "no
  coset-splitting" absence note (MOVES 2291–2292). deps: V0, V1, L3_K1
  pattern. difficulty: medium-hard (the S9w mirror, EASIER: no field
  extension). THIS IS THE V′ FRAME CHANGE UNIT.

* **V3 `V3_readLift`** — the recorded lift is the regrade's standard lift:
  `IsReadLift σ ψ g e★ h★ Φ̂` → (equal (†)-weights of all slots; the D.5
  residual display RV(Φ̂) = T(m̂★)·(ψ as Laurent), m̂★ = −t★·h★·g via the
  distinct-exponents sum k − t★h★g; K1(Φ̂/wV): wV(f) = min_m (wV(B_m) +
  m·e★h★g) with attainment). moves_ref: D.5 VERBATIM (MOVES 2253–2289 —
  the whole display re-runs at the ReadFrame; the Lean pattern is
  L3_liftResidual + L3_K1). deps: V2, L3_digPrime_nonzero-analog at the
  same key (width < g: D.3(d)). difficulty: medium.

* **V4 `V4_readLanding`** — (BOX)+(VERTEX) at the ReadFrame: for f ≠ 0 with
  ord_ψ(RV f) = μ and anchored RV-data, the Φ̂-development satisfies
  wV(B_m) + m·e★h★g > wV(f) for m < μ, = at m = μ with B_μ ≠ 0 (and the
  vertex digit with its explicit unit z̄^{−μm̂★}, for consumers that want it).
  moves_ref: D.8 (BOX)/(VERTEX) VERBATIM (MOVES 2469–2490: the displayed
  proof — K1 + D.1(e) + D.3(d) distinct ψ-orders — consumes NOTHING beyond
  the ReadFrame pack; S6/valgrp are untouched, which is what makes Finding 3
  harmless). The Lean pattern: L5_landVertex/L5_landVertexDigit transplanted
  to the pack. deps: V3. difficulty: HARD-ish but bounded (one L5-sized
  file). The (TRANSPORT) leg is NOT needed by any of the three discharges —
  fence it OUT of V4 (record it as available follow-on).

* **V5 SIGN-OFF EVENT (Defs restatement; Asvin's approval REQUIRED; the
  resolution of §9.9's queued strip adjudication).**
  - `Stage.hS6a` restates to the FIXED-POINT COSET form:
    `∀ ν ∈ weightSet, ∃ b : (↥K)ˣ, ∀ c : (↥K)ˣ, ((c:↥K):F) ∈ FQ →
     ∃ B, B ≠ 0 ∧ inC Φ B ∧ wPrev B = ν ∧
       R B = C((c*b : ↥K)) * T (−t·ν)`
    — the base point ∃-quantified BEFORE the orbit scalar, base FREE in Kˣ
    (weakest faithful form: the note's fixed classes are z̄-monomial at
    depth 2 but general unit products at depth ≥ 3; no consumer reads the
    base's shape — D.2's consumer audit "exactness consumes no scalar range",
    MOVES 1971–1981).
  - RIPPLE CENSUS (grep `hS6a` at execution; expected complete):
    constructors — T1/T2 base stage (b := 1: base digits are untwisted,
    MOVES 2012–2015), S10 recentering (transport with the SAME b: e = 1
    stages have position-0 constant residuals, the substitution fixes them),
    R6 carrier instance, S9a/S9b (become CONSUMERS of V7); consumers —
    `L4_TRANSviii_a_R5{,_final}` (statement restates: conclusion's
    `(d:F) = c·z̄^m` weakens to the coset form `∃ d₀ : (↥σ'.K)ˣ` base,
    ∃-before-∀c UNCHANGED; the proof repair is ~10 lines — fold the parent
    base through `L2_strideRule`; footprint re-verify MANDATORY).
  - FAITHFULNESS WARRANT: D.2 (S6a) rev D⁶ "orbit group at its FIXED POINT"
    (MOVES 1964–1971); D.7(viii) "c·(a fixed z̄-monomial class): the O-orbit
    with O = F_Qˣ CONSTANT" (MOVES 2431–2435); pass-14 finding 1 + pass-15
    "closure is therefore trivial" (MOVES 3091–3097, 3122–3124). The current
    Lean form is refuted by the S9a strip countermodel; per Finding 2 no
    conservative repair exists. This is the honest-restate discipline, same
    species as the S9a guard event (§9.9).

* **V6 `V6_alignedOrbits`** — the aligned digit orbits, both levels:
  (a) REGRADE orbits are UNTWISTED: σ★-realizers = parent hS6a realizers
  re-positioned, scalars preserved (fills ReadFrame.hS6a; also the b-transport
  helper V5's census cites). (b) DESCENT orbit base points: the strip window
  display — slots at child weight ν are (γ, j) = (s·ν − λ·h, t·ν + λ·e),
  λ ∈ (a g-window), twist = λ; the minimizing-slot choice (TRANSviii_a
  conjunct 1 forward + choice) fixes THE base b(ν) per weight. moves_ref:
  D.7(viii)'s 𝒜′ + realizer display (MOVES 2423–2435); the S9a header's
  twisted-orbit display (now a POSITIVE statement, not an obstruction).
  deps: V0; (b) consumes L4_TRANSviii_a_R5_final post-V5. difficulty: short.

* **V7 `V7_stripDischarge`** — S9a's single sorry closes: under V5's coset
  hS6a, the below-threshold leg of hS6a′ is V6(b)'s base + TRANSviii_a's
  conjunct 2 verbatim; the above-threshold leg stays L4_TRANSviii_b (exact
  scalars, unchanged). S9b's billing seam (§9.9 last bullet) closes with the
  same key. deps: V5, V6. difficulty: short. UNBLOCKS: S9a → S9b → S9c/S9d
  → S9 (the assembly chain's statements are already staged).

* **V8 `V8_childResidual`** — S9w-(i) PROVED: the explicit descent carrier
    `Rc f := Σ_{j minimizing childW} C(⟨digPrime z̄ (B_j), mem⟩)·
             T(j·s′ − t′·σ.w (B_j))`
  (choice-packaged against `ChildResData`'s pins — hS5′ is the single-slot
  case DEFINITIONALLY (mfun ≡ 0 is CORRECT, per Finding 2's first bullet;
  the strip mismatch was hS6a's transcription, never the pin), hRPhi the
  slot-1 case) + `ChildResLaws`:
  - (a) additive legs hR0/hRne/hRadd/hRlt/hRneg + w_jump: slot-min ties
    (S2's hSMW), position-injectivity across tied slots, parent hRadd/hRlt
    slotwise; hRne needs D.3(d) (ψ ∤ R(B), width < g — on disk as
    L3_digPrime_nonzero) for digit nonvanishing and F′[z^{±1}]-domain for
    sums. difficulty: medium.
  - (b) hRmul: the bilinear slot expansion; per-pair monic division
    B_j·B″_k = Q_{jk}·Φ̂ + R_{jk}; `L3_DIV` gives R_{jk} ≠ 0, exact weight,
    digit product; Q-terms strictly deeper by th's (I-aug) (D.7(i) verbatim);
    tied (j,k)-pairs land at ONE position (j+k)s′ − t′(σ.w B_j + σ.w B″_k)
    and SUM as the Laurent product's convolution coefficient; a vanishing
    convolution coefficient = a parent-residual cancellation = the SAME
    zero on both sides (no false nonvanishing claim — the D.1(b) δ-calculus,
    MOVES 2305–2313). difficulty: HARD (the honest §9.5 core), but every
    ingredient is displayed + on disk.
  - (c) w_strict (S9w conjunct (ii)): S9a's in-file hwult pattern + strict
    slot domination. difficulty: short.
  moves_ref: D.6 Lemma DIV (MOVES 2299–2322), D.7(i)–(iii) (2331–2352),
  D.7(vi)–(vii) normalization (2392–2418). deps: V0 (shape only), S2, S3,
  L3_DIV, L3_liftMonic, L3_digPrime_nonzero, th. NOT dependent on V5 (the
  carrier + laws never mention hS6a). UNBLOCKS: S9w → S9r (already reduced),
  the S9a census's carrier legs, and kills the S9w cone's sorryAx.

* **V9 `V9_K1nonrec`** — HC2's `K1_readVertexPin_nonrec` PROVED as a
  corollary: (i) extract the read steepness from HistoryCoherent (slope law
  + strict steepening → ν.h > ν.e·σ.h — the ReadPair hypothesis); (ii) build
  the ReadFrame at (ν.e, ν.h) on σ_i (V1/V2); (iii) the recorded
  `IsNodeLift = IsReadLift` is V3's standard-lift shape — K1(Φ̂/wV) + D.8 at
  the frame (V4); (iv) f's ReadFrame residual IS the recorded side pattern:
  RV(f) = Σ_k C(pat k)·T(…) from SideReads (i)+(ii) (the side line supports
  the development with equality exactly at the stride digits — so wV(f) =
  ν.gam, attained); its anchor/ord data: HasAnchorK(RV f, a★, pattern-Ranch)
  DERIVED from (i)+(ii); ord_ψ(pattern) = ν.μ read against SideReads (iii)
  — ADJUDICATION SURFACED (see below); (v) V4's (VERTEX) gives B_μ ≠ 0 and
  wV(B_μ) = gam − μ·ν.e·g·ν.h, then σ′.w(B_μ) = ν.e·σ.w(B_μ) = wV(B_μ) via
  the RECORDED child_wPrev/hStretch on the ONE coefficient (no tower
  reconciliation needed — the kernel's conclusion touches only a child
  COEFFICIENT's weight); (vi) the ℚ-conversion to
  `STR_{i+1}·line.at(μ·childWidth)` is the γ-tie + slope-law arithmetic
  already PROVED in-file (`K1_SAE_vertexEq_endpoint`'s pattern).
  deps: V1–V4 + the HC2 records. difficulty: medium (assembly).
  UNBLOCKS: `K1_readVertexPin` total → U20a/U20b/U22-E2 close by the staged
  one-line consumers.
  ⚠ SIDEREADS-(iii) ADJUDICATION (the standing E-PHASE FLAG, now with its
  resolution named): (iii) anchors `σ.R f` — the FRAME residual — while the
  landing needs the READ residual RV(f)'s ψ-order. At single-side reads they
  agree; at multi-side polygons the frame residual sees the WRONG slots.
  The faithful object is RV(f) (§C's side data are side-local); the DERIVED
  pattern-anchor route above consumes only (i)+(ii)+the recorded μ, so V9
  should key ord_ψ to the PATTERN and treat (iii)'s σ.R f rendering as
  the U31-gated seam it already is. If the gate shows the recorded μ
  mis-associates on some run shape, THAT restatement (SideReads (iii) →
  RV-vocabulary) is a NEW sign-off item — flagged now, not silently changed.

### 10.2 What this section does NOT change

No accepted statement moves except the TWO named sign-off items (V5's
Stage.hS6a + the TRANSviii_a conclusion pair), each with a machine-checked
refutation of the old form and a quoted note display for the new one — the
same restate-after-refutation discipline as the S9a guard event. VertexPin,
ChildResData.hS5′, childR's denotation, S9a–S9d/S9 statements, all L5
assets, U20c, D1–D8, S10: UNTOUCHED. Zero new axioms anywhere; every new
unit ends with `#print axioms` and the standard footprint protocol.

### 10.3 Census and estimate

9 proof units (V1,V2,V3,V4,V6,V7,V8a/b/c as one file with three theorems,
V9) + 1 Defs file (V0) + 1 sign-off event (V5). Confidence the design as
specified discharges its three targets: V7 ≈ 0.9 (post-V5, mechanical);
V8 ≈ 0.85 (all engines on disk; the risk is Lean-side Laurent/coercion
grind, not mathematics); V9 chain ≈ 0.75 (V4 is the big rerun; the
SideReads-(iii) seam is the one open adjudication and is fenced). Joint
estimate ≈ 0.8. The failure mode that would falsify the DESIGN (not just
stall a proof): a ReadFrame law that secretly needs hS6b — Finding 3's
audit says none does, and V4's fence (no TRANSPORT leg) is chosen to keep
it that way.

## 10.4 EXECUTION RECORD (2026-07-28, V′-kernel applier — Asvin's
definition-change authority per the task charge; acceptance = proofs run
through + full perimeter green)

**V5 EXECUTED FIRST (the sign-off event).** `Stage.hS6a` restated to the
fixed-point coset form in `Moves/Defs.lean` — `∃ b : (↥K)ˣ` BEFORE
`∀ c : (↥K)ˣ, (c:F) ∈ FQ`, conclusion scalar `C((c·b : ↥K))` — with the
field docstring quoting the two note displays verbatim (D.2 (S6a) rev
D⁶/pass-14, MOVES 1964–1971 "orbit group at its FIXED POINT … O := F_Qˣ
CONSTANT"; D.7(viii) MOVES 2431–2435 "c·(a fixed z̄-monomial class)") and
recording the machine-refutation of the old untwisted form (§9.9's S9a
strip record). RIPPLE CENSUS EXECUTED (grep `hS6a` corpus-wide at
execution; 15 files touched, every proof run through green):

* constructors — `T1_baseStage` (b := 1, `rw [mul_one]`); `S1_transHypGate`
  σpin (b := 1, `k0_unit_eq_one (c * 1)`); `S10_recStage` (transport with
  the SAME b, per the census prediction); `U17b_galois` `stageMap`
  (b ↦ its `resAut` image; `apply_symm_apply` on the c-factor only);
  `U28_gateSep`/`U30_gatePol`/`U31_gateReadsOf` gate stages (b := 1, the
  trivial-subfield unit lemmas at `c * 1`); `S9a_stageLiteral` — `hS6a'`
  restated to the coset form (above-threshold leg b := 1 through the
  UNCHANGED `L4_TRANSviii_b`; the strip `sorry` STAYS, now billed as V7's
  obligation — header adjudication paragraph updated: RESOLVED, neither
  §9.9 queued option; `mfun ≡ 0` is the note's V′ normalization, the
  mismatch was hS6a's own transcription).
* consumers — `L4_TRANSviii_a_R5{,_final}`: CONCLUSION RESTATED per the
  census spec — `∃ m : ℤ … (d:F) = c·z̄^m` weakens to
  `∃ d₀ : (↥σ'.K)ˣ … (d:F) = c·(d₀:F)`, ∃-before-∀c UNCHANGED; proof
  repaired as drafted (the parent coset base `b` folds through
  `L2_strideRule`; `d₀ :=` the `d` of the `c = 1` instance; both files
  PROVED, sorry-free). `L5_realRecursion_R3` (two-line: obtain base, apply
  at c = 1). `T4_slotMinHt`/`T7_alphabetSpan`/`C2_TYPa` (base-stage
  `digLift` realizers: `IsBaseStage`'s `K = FQ` absorbs the base —
  c := y·b⁻¹, `inv_mul_cancel_right`).
* NOT touched (census verified): R6 (no hS6a in code — the §10.1 census
  row was conservative), S9b/S8 (import TRANSviii_a but consume only its
  file, statements sorry/proved unchanged), every `{ σ with … }` clone
  (field rides through).

**PERIMETER: 532 modules GREEN** (all of Moves/MovesC/MovesD/MovesGr/
MovesRBase/MovesS/MovesSp/MovesU/MovesX/HC1/HC2). The ONLY two exclusions,
`MovesGr/L2_degZero_subring_v2` + `MovesGr/L4_genuine_imp_stageCoreL_v2`,
are PRE-EXISTING failures — machine-verified by rebuilding them against
HEAD's (pre-V5) `Defs.lean`: identical DirectSum-instance errors, no olean
in the build cache (never green in this workspace state), content
unrelated to `hS6a`. Recorded here so nobody bills them to V5.
`AxChk_baseline` does not cover the Moves/HC perimeter (OM-only); the
footprint protocol is the per-file `#print axioms` tails, all as expected
(repaired proved units Lean-core; sorried units sorryAx).

**V0–V9 ELABORATED** (`lean/LeanUrat/HC1/DefsV.lean` + `V*_*.lean`, all
ADDITIVE, zero axioms, 13 E-phase sorries):

* V0 `DefsV.lean` — `ReadPair`/`ReadResData`/`ReadResLaws`/`ReadFrame`,
  sorry-free. ONE recorded deviation from the §10.1 text: `ReadFrame.hS6a`
  is transcribed in the CURRENT (= post-V5 COSET) `Stage.hS6a` form, not
  the pre-V5 untwisted form the parenthetical named — the field mirrors
  the Stage field at the regraded frame (weights over
  `childWeightSet σ σ.Φ`, wVPrev = σ.w); V6(a) fills it by base transport
  (scalars preserved ⇒ the parent's coset bases ride).
* V1–V4, V6, V7, V9 — statements per §10.1 (V1 Q-ascent with the
  displayed gap `h★ − e★·σ.h`; V2 + the `V2_readFrame` packaging
  corollary; V3 with the D.5 EQUAL-WEIGHTS display as an explicit
  conjunct; V4 (BOX)+(VERTEX)+vertex-digit, TRANSPORT leg fenced OUT as
  specified; V6(a)/(b) with the descent base's z̄-monomial SHAPE
  displayed; V7 = EXACTLY S9a's hS6a′ obligation shape over any lawful
  carrier; V9 = `K1_readVertexPin_nonrec`'s statement VERBATIM + the
  steepness lemma at reads with a predecessor — the ROOT read's steepness
  is P-phase, from the recorded side data).
* V8 — `ExplicitDescentCarrier` (the (†) formula as a Prop on
  `ChildResData`, classical filter) + V8a/V8b/V8c sorried + the capstone
  `V8_childResidual` ASSEMBLED (proved from V8b+V8c; byte-shape = S9w's
  statement, so `S9w_residualLaws` closes by `exact` once V8b/V8c land).
* The SideReads-(iii) seam: FENCED as charged — V9's header carries the
  §10.1 ⚠ block; `SideReads` untouched; any RV-vocabulary restatement is
  a named FUTURE sign-off item.

POST-EVENT FRONTIER: the V-kernel P-phase (V1→V2→V3→V4→V9; V6→V7; V8),
then the staged one-line closures (S9w ← V8, S9a strip ← V7,
`K1_readVertexPin_nonrec` ← V9). MANIFEST re-synced (69 units; record key
`vkernel_2026-07-28`).

## 10.5 ESCALATION RECORD (2026-07-28, S9w_final — Fable escalation round)

First prover's verdict CONFIRMED: S9w is not wiring; the hardness is V8b.
Landed this round (all Lean-core, `#print axioms` in-file; V8 cone + S9r/S9a
consumers rebuilt green):

* **V8c_wStrict PROVED** — the childW strict law: S9a's in-file hwult pattern
  (slotwise development addition, parent ultrametric per slot) + childW
  NEGATION-INVARIANCE (slotwise, from `σ.w(−B) = σ.w B` for any multiplicative
  integer valuation) + the reverse inequality via `f = (f+g′) + (−g′)`.
  `f + g′ ≠ 0` is DERIVED (g′ = −f would tie the values against strict <).
* **S9w_residualLaws WIRED** — own sorry killed; closes by
  `exact V8_childResidual σ hσ th s' t' hbez' ht'0` (byte-identical statement,
  per the staged plan). Its sorryAx now flows through V8b ALONE (V8a is off
  the capstone path: the capstone assembles from V8b + V8c only).
* **Three V8b atoms PROVED** (in `V8_childResidual.lean`):
  - `V8_tiedPos_inj` — tied-slot position injectivity (the hRne crux):
    childW-tie + equal child positions ⟹ j₁ = j₂, by the Bézout collapse
    d = d·(e′s′ + h′t′) = 0 (a one-line `linear_combination` certificate:
    (j₂−j₁)·hbez′ + e′·hpos + t′·htie).
  - `V8_eval₂_mem_nextField` — z̄-evaluation of any ↥K-Laurent polynomial
    lands in K′ (`LaurentPolynomial.induction_on`; T ±1 steps via z̄, z̄⁻¹ ∈ K′).
  - `V8_digitUnit` — dig′(B) realized as a K′-UNIT for B ≠ 0 with
    natDegree < e·g·deg Φ (atom 2 + `L3_digPrime_nonzero`).

**EXACT REMAINING OBSTRUCTION (V8a + V8b, the honest §9.5 core).** All are
now carrier-construction work; no missing engine was found:
1. DEFINE the explicit carrier (classical choice on the Fact-A development;
   sum over the min-slot filter of `C(digitUnit)·T(j·s′ − t′·σ.w B_j)`), with
   the pins: hRPhi = the slot-1 development of Φ̂ itself (needs `σ.R 1 = 1`,
   the S10 `R_one` pattern, + childW Φ̂ = h′) and hS5′ = the single-slot
   development (atom 3 verbatim; degree bound from `inC Φ̂` + L3_liftMonic).
2. hRne: atoms 1+3 + the Finsupp fact that a sum of `C c·T n` over DISTINCT
   positions with c ≠ 0 is ≠ 0 (coefficient extraction at a witness position;
   `LaurentPolynomial.single_eq_C_mul_T` + `Finsupp.single_apply`).
3. hRadd/hRlt/hRneg/w_jump: slotwise transport through Fact B on the summed
   development (the S9a hwult skeleton, upgraded to carry residuals): per
   tied slot the 5-way split (f-only / g-only / tie-no-jump via σ.hRadd +
   `map_add` under eval₂ / tie-jump = digit cancellation / untied via σ.hRlt),
   then re-index the min-slot filters (they partition by atom 1).
4. hRmul (THE block): per-pair monic division `B_j·B″_k = Q_jk·Φ̂ + R_jk` —
   `L3_DIV` (ON DISK, proved) gives R_jk ≠ 0 + exact weight + digit product;
   Q-terms strictly deeper by th.hiaug (h′ > e′·w(Φ̂); the L3_DIV 2-slot K1
   pattern gives the D.7(i) weight bound); regroup the double sum into the
   product's development (Fact B pins it); tied (j,k) pairs land at ONE
   position (atom 1 applied to the pair sums) and sum as the Laurent
   convolution coefficient (`AddMonoidAlgebra.single_mul_single`); a vanishing
   convolution coefficient is the SAME zero on both sides (D.1(b) δ-calculus).
   childW multiplicativity is ON DISK (`S5_childValuation`, Lean-core).
Estimate unchanged from §10.3 (the risk is Laurent/Finsupp grind, not
mathematics); sized as its own dedicated unit, NOT a one-session close.

## 10.6 SECOND ESCALATION RECORD (2026-07-28, V8b hRmul core — Fable round 2):
## V8 PROVED IN FULL — S9w SORRY-FREE

The §10.1 V8 unit is CLOSED: **V8a, V8b, V8c all proved, zero sorry; every
theorem in `V8_childResidual.lean` (capstone included) has footprint
{propext, Classical.choice, Quot.sound}; `S9w_residualLaws` + `childR_laws`
now Lean-core; full cone rebuilt green.**

The one genuinely new device (everything else was assembly of on-disk engines):
the private **graded-residue calculus** `v8gr σ ω x := if x ≠ 0 ∧ σ.w x = ω
then σ.R x else 0` with domain `v8Deep σ ω x := x = 0 ∨ ω ≤ σ.w x`. The single
lemma `v8gr_add` packages ALL FIVE D.1(b) tie laws (parent hRadd/hRlt +
StageCore w_strict/w_jump/R_neg) as: `v8Deep` is closed under `+` and `v8gr ω`
is ADDITIVE on it. Every per-slot digit claim in every law leg then reduces to
"compute `v8gr` of the slot sum termwise, evaluate at z̄, cite D.3(d)".

* Carrier: `v8Rc` = the (†) tied-slot sum on THE development (Fact A choice,
  Fact B independence spec `v8Rc_eq`); hRne by position injectivity
  (`e′·pos(j) = j − t′·m`, the ATOM-1 Bézout collapse) + Finsupp coefficient
  extraction at one tied position; pins hRPhi/hS5′ by direct evaluation of the
  2-slot/1-slot developments (`dig′(1) = 1` from idempotence in F).
* hRadd/w_jump/hRlt: per-slot `v8gr` case trees at the tie level ω_j (the
  slot-value ↔ parent-weight converters cancel e′ > 0); cancelling digit pairs
  are exactly the non-tied sum slots (D.3(d) forbids a tied slot with zero
  digit); hRlt consumes V8c's strict law (V8c MOVED above V8a/V8b in-file).
* hRmul (the §9.5 core): `L4_TRANSiii`'s convolution development
  `Cdev m = H.coeff m %ₘ Φ̂ + Q_{m−1}` re-derived IN-FILE at digit level (those
  helpers are private); `childW`-multiplicativity CITED from `L4_TRANSiii`;
  per-diagonal, `hgrC : v8gr ω (Cdev m) = Σ_{tied pairs (j,k), j+k=m}
  R((B_j·B″_k) %ₘ Φ̂)` — remainder weights exact by `L3_DIV`, carried quotients
  strictly deep by (I-aug) (the generalized hdeepQ at arbitrary ω with
  e′ω + m·h′ = M); evaluation at z̄ + `L3_DIV`'s digit product turns `hgrC`
  into "digit of `Cdev m` = the convolution coefficient Σ dig′(B_j)·dig′(B″_k)";
  the Laurent product regroups by `Finset.sum_mul_sum → sum_product' →
  sum_fiberwise_of_maps_to`, fiberwise-constant positions/weight-sums by the
  tie arithmetic. A VANISHING convolution coefficient is the SAME zero on both
  sides: the sum slot cannot be tied (its digit would be 0, against D.3(d)) —
  the D.1(b) δ-calculus exactly as §10 displayed it.
* Statement fence: V8a/V8b/V8c/V8_childResidual/`ExplicitDescentCarrier`
  signatures byte-identical; V8c's proof untouched (block moved verbatim).

UNBLOCKED: S9w → S9r (rides conjunct (i)); the S9a census's carrier legs.
The S9w cone's sorryAx is DEAD.

## 10.7 CONFIRMATION + CLOSER RECORD (2026-07-28, mechanical-closer round):
## the Codex VPRIME gaps closed; S9b restated with the guard and PROVED

### (A) Codex adversarial confirmation (`lean/notes/VPRIME_CONFIRM_CODEX_2026-07-28.md`)

Codex verified the applied V′ kernel (the V5 `Stage.hS6a` coset restate +
ripple, and the V0–V9 statements) against the note displays and this section's
text. Verdict: **ACCEPT — no critical findings** (coset quantifier order
∃ b before ∀ c confirmed; V0–V2/V4/V6(a)/V7/V8/V9 statement fidelity
confirmed; ripple confirmed). Three recorded gaps, ALL CLOSED same day:

* **Gap 2 (the `mfun ≡ 0` warrant).** The D.7(vi)–(vii) excerpt (MOVES
  2392–2418) cited at the normalization does not itself state the
  frame-change identity behind `mfun ≡ 0`. CLOSED: the REAL WARRANT is
  D.7(v)'s D-map DEFINITION display, **MOVES 2364–2367** — "Define D on each
  coefficient piece gr^Ĉ_δ by D(x) := R(x) mod ψ ∈ F′" — reduction mod ψ IS
  evaluation at the root z̄ under F′ = F[z]/(ψ) ≅ F(z̄), i.e. Lean's
  `digPrime`; the child digit map is DEFINED as the raw parent-residual
  evaluation, so no alignment twist exists to normalize away (injectivity on
  degree-0 MOVES 2388–2390; the pinning identity z = V^{−h}Y^{e} MOVES
  2395–2399 pushes the parent z-class to the scalar z̄). NOT the polOM
  normalization (that is HC2's D.10 lift apparatus). Recorded at: Key
  Finding 2's first bullet (§10 above), `V8_childResidual.lean` (header +
  moves_ref + `v8Rc_S5'`), `DefsChild.lean` (`ChildResData.hS5'`).
* **Gap 7 (V3's EQUAL-WEIGHTS conjunct not tied to the lift witness; leading
  slot absent).** CLOSED ADDITIVELY (statement fence intact — `V3_readLift`
  byte-unchanged): NEW `V3_equalWeights_lift` (PROVED, Lean-core)
  destructures `hlift` and states the D.5 display AT ITS WITNESS FAMILY —
  every present slot `e★·σ.w(tt k) + (e★k)·h★ = e★h★g` — PLUS the D.5
  leading-slot equation `e★·σ.w(1) + (e★g)·h★ = e★h★g` (the leading slot is
  `σ.Φ^{e★g}`, coefficient literally 1, `σ.w 1 = 0`; MOVES 2268–2269:
  "EQUAL WEIGHTS: each present slot has w(t_k) + ek·h = eh(g−k) + ekh = ehg,
  and the leading slot 0 + eg·h = ehg").
* **Gap 9 (V6(b) omits the λ-window/twist display).** CLOSED AT
  DOCUMENTATION LEVEL (fence-checked NOT a genuine weakening: V7's strip
  discharge was reproved σ′-free WITHOUT consuming V6(b), and S9a/S9b ride
  V7 — no consumer needs the λ-form): `V6_descentOrbits`' docstring now
  carries the full display — parent-scale slots at child weight ν are
  `(w̃, j) = (s·ν − λ·h, t·ν + λ·e)`, twist = λ, λ over the g consecutive
  values forced by `0 ≤ j < e·g`; the proof's base exponent `m := s·j − t·w̃`
  equals λ on the line (Bézout `e·s + h·t = 1`). The public-statement
  reduction (only `(γ, j, m)` exposed) is recorded as deliberate; any future
  exposure of λ is fenced to an ADDITIVE corollary.

### (B) S9b restated with the increment guard + PROVED (the S9a precedent verbatim)

`S9b_childWeightSet` = S9a's ∃ strengthened by the conjunct
`σ'.weightSet = childWeightSet σ Φ̂`; the unguarded form is refuted at the
`σ.e * g = 1` corner by exactly S9a's kernel argument (any S9b witness
witnesses the refuted S9a shape). Executed, mirroring the §9.5 S9a record:

* STATEMENT: gains `hEG : 1 < σ.e * g` (MOVES 3755–3757 increment guard;
  the corner is the RECENTERING species 3766–3767, S10's territory). No
  consumers import S9b yet (ripple-free).
* KERNEL (in-file, PROVED Lean-core): `S9b_ungated_corner_refuted` —
  delegates to `S9a_ungated_corner_refuted` by dropping the weightSet
  conjunct. Corner-exclusion arithmetic: `S9a_corner_fails_guard` cited
  as-is (statement-independent).
* PROOF (PROVED, footprint {propext, Classical.choice, Quot.sound}, zero
  sorry): the S9a_final construction re-run verbatim — Bézout split, S9w
  lawful carrier, S2/S3/S5 plumbing, in-file hwult, L4_TRANSviii_b +
  carrier pin above threshold, `V7_stripDischarge` below (σ′-free; the
  E-phase "via the TRANSviii finals" billing superseded exactly as at
  S9a_final — TRANSviii_a is circular here) — and the fourth conjunct
  closes by `rfl` (the literal already pins `weightSet := childWeightSet`,
  S9a's own `hWS` field). The §9.9/S9a-record seam "S9b's '(S6a′) via the
  TRANSviii finals' billing inherits the same seam" is thereby CLOSED.
* NEXT in the assembly chain: S9c/S9d → S9 (statements already staged).
