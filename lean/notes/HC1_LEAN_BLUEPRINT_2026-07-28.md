# HC1 LEAN BLUEPRINT — §B2-DEF's tower induction (2026-07-28)

*Hard-core #1 blueprint (Fable writer, wave 5 of the campaign master plan
`LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`). GROUND TRUTH: the dual-accepted §B2-DEF
text `MOVES_2026-07-24.md` 1849–2745 (D.0–D.12) + the §C displays 3644–3831 (Lemma DOM
3644, Lemma LST 3728, Lemma TYP 3783) + the pass-7 carry-algebra spec 1502–1530.
BUILDS OVER: `lean/LeanUrat/Moves/` (61 units, 50 clean + 2 conditional + 9 tail
sorries per `MOVES_LEAN_FINAL_CENSUS_2026-07-26.md`), `lean/LeanUrat/MovesGr/`
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
read that augmented level r (LST head, MOVES 3731–3735). The MovesR `GradedCarrier`
indexes `Gr : ℚ → Type`; the real instance sets `Gr γ := S.grPiece ⌊str·γ⌋` (S = the
top stage's SideVal, str = the accumulated stretch): on-lattice γ hits the genuine
stage-scale piece; off-lattice γ has `inγ γ := 0` and no weight ever equals it, so
`inγ_kills`/`inγ_detects` hold with no junk (recorded, auditable convention).

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
layer (`L1_gaussVal`, `L1_baseResidual_R4`; the sorried `L1_baseWeight_R3` is a
NAMED dep — §4). Unit T2 inhabits it at p = 2, F = GaloisField 2 2, φ = X² + X + 1 —
the honest replacement for MovesGr's held `L4_base_nonvacuity_gate`.

**(D6) e_birth vs e_read is a TOWER function, threaded through 𝒟.** Per level k ≥ 1,
`eBirth T k` := the e′ of the increment that created level k's coefficient algebra;
recenterings PRESERVE it (they replace the current key, never the coefficient
algebra — D.10/TRANS-RS: "same C, same v, same T"). A key born at e_birth > 1 read
later at e_read = 1 keeps nontrivial ℤ/e_birth anchor cosets (the pass-7 critical 2,
MOVES 1478–1499); HC1 types this as: the DIG map lands in `CarryAlg F (eBirth T k)`,
and the recentering units (S16/S17) run the D.10 substitution WITH the coset data
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

/-- accumulated stretch `STR_k = e₀·e₁·…·e_k` (C.1.0(c)); κ_k := h_k/(e_k·STR_k). -/
def Tower.str (T : Tower p F) : Fin (T.K + 1) → ℕ := ...
noncomputable def Tower.kappa (T : Tower p F) : Fin (T.K + 1) → ℚ := ...

/-- A tower coordinate: p-adic level l + inner slot vector (bounded per level by the
key-degree ratios — the iterated-development address (b, l) of D.3(e)). -/
structure Tower.Coord (T : Tower p F) where
  l : ℕ
  slot : Fin (T.K + 1) → ℕ
  slot_lt : ∀ r, slot r < slotBound T r   -- e_r·g_r ratios; def in-file

/-- the coordinate's basis monomial `m_c = p^l·∏_r Φ_r^{slot r}` (TYP(a) display). -/
noncomputable def Tower.mono (T : Tower p F) (c : T.Coord) : Polynomial ℤ_[p] :=
  Polynomial.C ((p : ℤ_[p]) ^ c.l) * ∏ r, (T.stg r).Φ ^ c.slot r

/-- the absolute height `ht(c) = l + Σ_r slot_r·κ_r` (LST head, MOVES 3734–3735). -/
noncomputable def Tower.ht (T : Tower p F) (c : T.Coord) : ℚ := ...
```

### 2.3 `HC1/DefsCar.lean` — the REAL graded carriers

```lean
/-- The top stage's side-valuation package: `σ.w` extended by `0 ↦ ⊤`, laws from
`StageCoreL` (this is MovesGr's SideVal built from a GENUINE stage — the L1-layer
construction, reused). -/
noncomputable def Tower.side (T : Tower p F) : SideVal p := ...

/-- **The real GradedCarrier** (instantiates MovesR D4(a) at δ = 1; D3 convention):
Coeff := the top coefficient space as a submodule-carrier (deg < deg Φ̂_top, an
AddCommGroup via Polynomial.degreeLT); Gr γ := (T.side).grPiece ⌊strTop·γ⌋;
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
  `L1_baseResidual_R4` (clean); dep-sorry: `L1_baseWeight_R3` (the min-formula
  valuation law — §4.1). sketch: fields of `Stage` from the display: hS5 = D.2's
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
  (hc : c.MonoNZ) : ((T.stg T.K).w (T.mono c) : ℚ) = (T.str T.K : ℚ) * T.ht c` —
  LST(i-a): ht IS the K1-chain weight of the basis monomial, stage scale = str·abs.
  moves_ref: MOVES 3736–3738 "ht(b, l) is the K1-chain weight of the coordinate's
  basis monomial p^l·∏_r Φ̂_r^{innerslot_r(b)}". deps: DefsTower; Moves `L3_K1`,
  `L2_keyResidualPow` (clean); the per-move κ-update discipline (LST proof, MOVES
  3750–3777). sketch: induction on K; increment step adds one inner level at
  κ_{new} = h/(e·STR) (w′(Φ̂) = h′; multiplicativity hwmul on the monomial);
  recentering step: v = v′ at fixed labels. difficulty: HARD. hyp: none.
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
  transport MovesGr's piece lemmas through the ⌊str·γ⌋ reindexing; off-lattice
  clauses vacuous by D3's convention. difficulty: medium. hyp: none.

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
* **HC1.T9_blockDisjoint** — (ii.3): distinct (b, γ) ≠ (b, γ′) pins have disjoint
  coordinate sets: `γ ≠ γ' → Disjoint (levelSet b γ) (levelSet b γ')` and distinct
  blocks partition coordinates. moves_ref: MOVES 2175–2188 ("distinct development
  slots have disjoint leaf subtrees … induction bottoms at distinct p-adic
  heights"). deps: DefsCar. sketch: level sets at distinct heights are disjoint by
  definition of ht (a function); block partition from the development coordinate
  partition. difficulty: easy (the note's hard content — distinct slot CLASSES mod
  e via t invertible — is absorbed into ht being single-valued on coordinates; the
  unit states the locus-level disjointness the ledger consumes). hyp: none.
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
  (SAE)+(NA)+(HV) per move; dep-sorry: `L2_iaugStep` (§4.2).
* **HC1.C5_typToClause** — the bridge to MovesC's counting: a TYP(b) fresh value
  clause yields a `MovesC.LevelClause` with `support = levelSet b γ'` (as base
  coordinates), `codim = aDim b γ'`, and the `count` law from C3's equal-fiber
  theorem. moves_ref: MOVES 3813–3815 (USE 1: "C.1.5's counting consumes exactly
  this object"). deps: C3, T12; MovesC `LevelClause` (fence: consumed, not
  restated). sketch: package; count = card kernel-coset arithmetic, division-free.
  difficulty: medium. hyp: none.
* **HC1.C6_alphabetCard** — `Nat.card (T.alphabet b γ) = p ^ (T.aDim b γ)` and
  monotone assembly: at clean-threshold heights `𝔸 = the full piece` (the
  D.9(b)-cleared regime), strictly smaller at shallow heights — stated as: IF every
  slot height in γ's tree clears its stage bound THEN aDim = the full piece
  dimension (no unconditional fullness claim — the rev-D¹¹c fix). moves_ref: MOVES
  2160–2165 "= [F_{k+1} : F_p] … exactly when every height in γ's slot tree is
  attainable … STRICTLY SMALLER at shallow heights". deps: T7, T8; Moves
  `L5_realCofin_R3`, `L5_realDomination_R3` (clean). sketch: T8's product formula;
  fullness under the cofiniteness bound. difficulty: medium. hyp: none.

### Layer S — the induction spine + per-level transports (17 units, `HC1/S_*.lean`)

* **HC1.S1_transHypGate** — `TransHyp` is non-vacuously inhabitable AND correctly
  exclusive: (a) a concrete inhabitant at p = 2 (base stage of T2, ψ = z² + z + 1,
  g = 2, the D.5 lift, (e′,h′) = (1, w(Φ̂)+1)); (b) `¬∃` at e′ = 0 (respects the
  MovesGr certificate — provable now as `TransHyp → 1 ≤ e'` is a field: state as
  the structure being False on the e′ = 0 instantiation by projection). moves_ref:
  MOVES 2325–2328 (D.7 head: the side satisfies (I-aug)); MOVESGR §8.2
  `transitionCoreL_e0_false`. deps: DefsTower, T2. sketch: (a) construct; (b)
  projection. difficulty: medium. hyp: none.
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
  Moves `L4_TRANSv_R3` (CONDITIONAL — inherits sorryAx via an import, §4.3),
  `L4_TRANSviii_b_R4` (clean, the (S6b) recursion), `L2_widthBound` (clean).
  sketch: unit-monomial weights from powers of in(p); g consecutive stride
  positions; (S6b) scalars above the clean threshold; span = F′. difficulty: HARD.
  hyp: none new; dep-sorry: the `L4_TRANSv` cone (§4.3).
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
* **HC1.S12_iaugPersist** — (I-aug) holds at every read of a tower (root case,
  increment landings, recentering landings — D.4's induction along the history).
  moves_ref: MOVES 2217–2249 (D.4, all three bullets + "by induction along the
  history"). deps: DefsTower; Moves `L2_iaugRoot`, `L2_iaugRecenter` (clean);
  dep-sorry: `L2_iaugStep` (reducible case — §4.2). sketch: induction on move
  index; each case is the proved Moves unit. difficulty: medium. hyp: none.

* **HC1.S13_realPersist** — Lemma REAL along the tower (D.9): the per-stage weight
  sets, cofiniteness bounds, and the domination h_r > e_r·f_r persist; at every
  e_read = 1 read the side value is realizable with any digit scalar. moves_ref:
  MOVES 2551–2581 (D.9(a)–(d), incl. the induction-order clause). deps: S11, S12;
  Moves `L5_realRecursion_R3`, `L5_realCofin_R3`, `L5_realDomination_R3`,
  `L5_realConclusion` (all clean). sketch: thread the four proved units along the
  tower index; the induction order (stage-r quantities before Φ_{r+1}) is the
  Tower's own structural order. difficulty: medium. hyp: none.
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
  by S11). moves_ref: MOVES 2484–2546 (D.8 proof: BOX/VERTEX both directions +
  TRANSPORT + two-sidedness); 2654–2659 (RS-landing, the g = 1 case). deps: S11,
  S15; Moves `L5_landBox`, `L5_landVertex`, `L5_landTransport_R4`,
  `L6_moveAffineBij` (clean); dep-sorry: `L5_landVertexDigit` (§4.4),
  `L5_landTwoSided_R5` (§4.5 — the anchor-exactness clause). sketch: instantiate
  the five Moves landing units at `T.stg k` with StageCoreL from the spine; the
  recentering case via S10 + L5_recRSland. difficulty: medium-hard (assembly).
  hyp: none new; two dep-sorries (BLOCKING for full closure — §4).
* **HC1.S17_levelMeasureExact** — **D.11 at every level**: for every tower T, level
  k, admissible stratum, and every N above the largest constrained height + 1:
  `#{f mod p^N ∈ stratum} = #{development data mod p^N ∈ cylinder} = p^{nN} ·
  vol(cylinder)`, vol = the ATTAINABLE product over the cylinder's digit equations
  (each factor `|𝔸(γ)|⁻¹` = C6's cardinality; inadmissible pins ⟹ empty locus —
  the D¹¹d dichotomy). ONE move; no composition (D8 fence). moves_ref: MOVES
  2672–2718 (D.11 in full, incl. the unit-system clause and the dichotomy). deps:
  S16, C3, C5, C6, T11; Moves `L6_ledgerCount`, `L6_moveReduceCommute_R4` (clean);
  dep-sorry: `L6_measureExact_R4` (§4.6 — two sorries). sketch: first equality =
  S16's bijection + moveReduceCommute at level N; second = the unitriangular
  digit-count (ledgerCount) with per-pin attainable factors from C3/T11.
  difficulty: HARD. hyp: none new; dep-sorries §4.4–4.6.

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
  decidable), τ := (0,1): verify by `decide` over all (d₀, d₁, τ-cell) triples the
  v2 seal's algebra: (i) the Frobenius-matched both-rise set
  `{(d₀,d₁) ∈ (F9ˣ)² : d₀ = d₁³}` meets the census's 8-of-512 count pattern at the
  gate's cell granularity, and (ii) the char-3 edge clauses `2τ + d₁ = 0` /
  `R₂(τ) = 0` have the sealed cardinalities on their cells (the counts of MOVES
  3025–3032, re-derived as finite-set cards). moves_ref: MOVES 3017–3045 (CASE-K v2
  SEALED GATE RECORD, Q1–Q6). deps: none (self-contained F9 arithmetic; the gate
  re-checks the ALGEBRAIC layer of the seal, not the p-adic census). difficulty:
  medium. hyp: none. NOTE: exact cell predicates transcribed from
  `verification/case_k_gate_v2_p3.py` at E-phase; the unit's fence is the SEALED
  RECORD's displayed counts.
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

HC1 consumes these sorried/conditional Moves units. Their closure is the wave-5
"Moves tail backlog fleet" (campaign §5); each entry names the consuming HC1 unit,
the gap, and the census-recorded repair direction. NO HC1 unit may close a gap by
weakening a Moves statement (fence).

* **4.1 `L1_baseWeight_R3`** (1 sorry :62 — the base min-formula valuation law).
  Consumer: T1. In-file verdict: statement TRUE under its hypotheses, proof
  outstanding. Repair: honest Gauss-valuation × Newton-slope argument (accepted
  B1.1); no restatement needed.
* **4.2 `L2_iaugStep`** (1 sorry :72 — the reducible case of the increment
  (I-aug) step). Consumers: S12, C4. Repair: D.4's chord-convexity display (MOVES
  2229–2237) — the landing-box chord inequality + hull monotonicity; flagged
  in-file as manifest-level gap, statement stands.
* **4.3 `L4_TRANSv_R3`** (CONDITIONAL — own file sorry-free, main theorem inherits
  `sorryAx` via an import; census `cond` row). Consumer: S6. Repair: rebuild its
  import cone on the closed 4.1/4.2 (the census identifies the cone; no
  mathematical gap of its own).
* **4.4 `L5_landVertexDigit`** (1 sorry :70 — private core; in-file comment STALE:
  deps `L3_K1`/`L5_landVertex` are CLEAN on disk). Consumer: S16. Repair: discharge
  the private core against the now-clean deps (the census's own note); expected
  medium.
* **4.5 `L5_landTwoSided_R5`** (1 sorry :964 — anchor exactness NOT encoded in the
  cylinder). Consumer: S16. Repair (the file's proposed round-6, adopted here as
  the spec): add the anchor-exactness clause to `LandingCylinderL` as an ADDITIVE
  field (`ord_z` of the vertex slot term = 0 after anchoring — the a-datum made
  cylinder-side), then close the sorry; this is a statement CHANGE on a Moves def
  → requires sign-off per the fence; flagged as the single fence-gated repair of
  the tail. Until closed, S16/S17 carry the dep-sorry honestly.
* **4.6 `L6_measureExact_R4`** (2 sorries :143/:189 — the landTwoSided placeholder
  + the zero-coordinate leg). Consumer: S17. Repair: :143 resolves with 4.5;
  :189 (the `exfalso; sorry` zero-coordinate leg — a genuine faithfulness gap the
  fenced statement omits) needs the E.IsSolution-at-Θ(0) hypothesis threaded — a
  restatement candidate for the tail fleet WITH sign-off, or a strengthened-
  hypothesis v5 unit (option (b) style), decided at adjudication.

Superseded sorried files (`L2_P6i_R5`, `L4_TRANSviii_a_R5`, `L4_TRANSviii_b_R3`,
`L5_landTransport_R3`, `L6_moveReduceCommute_R3`) are NOT consumed — HC1 imports
only the clean finals/R4s.

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
* **dep-sorries** — §4's six entries, each named at its consumer.
* **PUBLISHED-AXIOM CANDIDATES: NONE.** This is our own mathematics (D9). The
  verify leg must show Lean-core-only footprints on every proved unit; `sorryAx`
  appears exactly where §4 predicts, and any GMN/Denef import in an HC1 cone is a
  stop-the-line event.

## 6. File map, import order, build protocol

```
lean/LeanUrat/HC1/DefsD.lean      §2.1  (CarryAlg, carryExp, cmul, dOf, IsHomog, digD)
lean/LeanUrat/HC1/DefsTower.lean  §2.2  (TransHyp, MoveWitness, IsBaseStage, Tower,
                                         eBirth, str, kappa, Coord, mono, ht)
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

**54 units**: D-layer 8 (5 easy / 3 medium) · T-layer 12 (4 easy / 4 medium /
4 hard: T1, T2, T3, T8) · C-layer 6 (5 medium / 1 hard: C2) · S-layer 17 (1 easy /
11 medium incl. the medium-hard S16 / 5 hard: S2, S6, S9, S10, S17) · G-layer 5
(4 easy / 1 medium) · R-layer 6 (4 easy / 2 medium). **HARD TOTAL: 10** (T1, T2,
T3, T8, C2, S2, S6, S9, S10, S17), each with a pre-approved split (T1a/b, T8a/b,
S2a/b, S9a/b) or a named escalation surface. Highest escalation risk: S9 (the
↥K/↥K′ subfield plumbing — the known type wall Moves' Defs were designed around),
C2 (the unit-lift additive carry — the one delicate new algebra step), T2
(concrete-instance labor).

Process per the campaign gates: this blueprint → Codex/Fable semantic audit
(REJECT loops; audit charge: faithfulness to the quoted displays, non-vacuity per
the doctrine, quantifier exactness, hypothesis-field fidelity, the §1 fence table)
→ E-phase (Defs compile + statements elaborate twice) → prover fleet (D/T-easy/G
first; S9/S10/S17 last, after their deps) → per-unit verify (Lean-core footprints)
→ the R-layer re-audit gates MovesR's unparking. STUCK rule per campaign §3.

END OF BLUEPRINT (54 units; 10 hard; 0 published-axiom candidates).
