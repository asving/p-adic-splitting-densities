# MOVES §S-RESUM — Lean formalization blueprint (corpus MovesS) — REV 2 (post-Codex-audit, 22 findings repaired)

*REV 2, 2026-07-27. Round-1 text RETIRED (do not fan out from it). The Codex audit
`lean/notes/MOVESS_AUDIT_CODEX_2026-07-28.md` returned REJECT (19 crit / 3 gap); every
finding is repaired here in one batch; the findings→repairs table is §6. Source of truth
unchanged: the DUAL-ACCEPTED **§S-RESUM rev 6** of `lean/notes/MOVES_2026-07-24.md`
(lines ~11557–12430). Protocol-L; parent-CLAUDE.md discipline: NO new axioms,
statement-fence, every structure a flagged trust boundary (§4).*

## H. HEADER — the REV-2 design rulings

**R1 — NO `True`-typed hypothesis fields, anywhere** (findings 1, 3, 19). Every hypothesis
field states the note's actual condition as a contentful Prop over the structure's OWN
data. Where the condition's native vocabulary lives upstream (MovesV tables, MovesT trees,
[2b] height domains), the structure gains the **minimal abstract carriers needed to STATE
it** — the MovesD `PrefFamily` precedent (jet/enc/hist_inj as real fields with declared
owners). Concretely: a `MeasuredSide` interface (pool-indexed cell masses, height domains,
representatives, entrance shapes, k-step masses) over which all NINE CL-5 ledger items are
real Props (§2.B), and a `RatBurdens` structure in which every ℚ(q) table entry is DATA
**plus an interpolation law tying it to the measured per-pool values** — rationality is a
hypothesis package, never a bare field type (finding 3).

**R2 — NO assumed conclusions** (findings 4, 5, 8, 15, 16, 17, 18). A unit advertised as
deriving X takes the note's actual INPUTS. Where the derivation genuinely needs wave-4
vocabulary (TREE-EXP, CUT-WD, COMP-*), the unit moves to the explicit **WAVE-4 SYNC LIST**
(§3w) with its statement PINNED as a named Prop definition — a declared deferral, not a
fake derivation. Wave-2 keeps only what §S-RESUM itself marks DERIVED: the dispatch,
(K-TRI), the (SCS) chain from SP.1/stage-law carriers, (K-SUB) from PART-1's cell
partition, the solve, the E0 consequences, the evaluation/infinitude machinery, RS.1-DEEP
from the measured fixpoint, RS.4's rational-identity step.

**R3 — XRB reverts to an open hypothesis exactly as the note has it** (finding 2). The
measured subtree values `βmeas` carry an entrance-height index; `(XRB)` is the named field
`xrb : ∀ h h', βmeas … h … = βmeas … h' …` (CL-9; the note proves it at S.1 under its
displayed set — that proof is measure-side, wave-4/sync). The height-free symbolic family
`βfam` is only usable GIVEN `xrb`. Nothing in MovesS admits height-free β when XRB fails.

**R4 — inhabitation stories** (finding 19). Every structure carries a design note naming
its intended real instance + owner (§2, per structure), `RegP` quantifies over the
DEFINED pool set `consumedPools` (never a free Δ), pool/prime sets carry infinitude
fields where the note's arguments need them, and the corpus ships a **non-vacuity gate
unit** `instance_n2` building the note's own displayed 1×1 n = 2 instance (W6 geometric
series, denominator q² + q + 1) through the full structure stack.

**R5 — edge fidelity** (findings 6, 9, 10, 11, 12): both halves of (BDY) (edge rule AND
node shadow + the mass-split lemma; the consumption duties named on the sync list);
base-change indices are `ℕ+` (δ = 0 excluded); every block quantifier is `e ∈ Icc 1 n`
(no invented e = 0); `bSplit` takes the `DegCons` proof that licenses its smaller-block
applications; (R_e-exact) is a Lean statement (U-17b), not a docstring.

**R6 — splits** (finding 22): the three round-1 hards each split into one-display units:
`blockSolve` → {bSplit_def, blockSolve, blockSolve_spec}; `e0_det_ne_zero` →
{pow_fixed_vector, mulVec_abs_bound, e0_det_ne_zero}; `e0_inv_nonneg` →
{neumann_partial, pow_entry_nonneg, pow_entry_tendsto, e0_inv_nonneg}.

Downstream-corpus statement (per the campaign charge): MovesV/MovesT objects enter ONLY
through the §2 hypothesis structures (`TableShape`, `MeasuredSide`, `LedgerIV`,
`RatBurdens`, `RS1Bundle`, `RS4Chain`) — self-contained now, instantiable at wave 4 by
substituting the real objects; each field's owner is declared at the field.

---

## 0. What §S-RESUM is (one paragraph)

The depth direction of the classifier tree, resummed: per block size 1 ≤ e ≤ n, the
linear system
> (R_e-lump)  β_e = K_e β_e + b_e^{term,fin} + b_e^split
over ℚ(q); the (m, c) CLASSIFICATION routes every roster outcome to exactly one of
{K_e column, terminal exit, split exit}; (K-TRI) makes the block family triangular in e;
(K-SUB) makes K_e's rows sub-stochastic given the (iv) ledger; the solve is
β_e = adj(I−K_e)b_e/det(I−K_e) (RS.2, fixed coefficients); solvability rides the open
kernel ESCAPE(E0) per pool q₀ = p^δ (RS.3); RS.1 ties the solve to the density
components R_σ (DEEP/SH/MARKED); RS.4 is the checksum Σ_σ R_σ = 1 via "a rational
function equal to 1 at infinitely many prime evaluations is identically 1".

---

## 1. Mathlib design (verified names; unchanged from round 1 except D6/D9)

**D1** ℚ(q) := `abbrev Qq := RatFunc ℚ`; field structure `RatFunc.instField`
(pinned mathlib, FieldTheory/RatFunc/Basic.lean:480).
**D2** One matrix per block e, one vector per (e, σ′): K_e is σ′-independent (S.0), so
the system per σ′ is `β = K.mulVec β + b` over `Matrix (State e) (State e) Qq`.
**D3** Solve API: `Matrix.isUnit_iff_isUnit_det` (NonsingularInverse.lean:127),
`Matrix.mul_nonsing_inv`/`nonsing_inv_mul` (:211/:217), `Matrix.inv_def` (:172),
`Matrix.cramer_eq_adjugate_mulVec` (Adjugate.lean:245), `Matrix.mul_adjugate`/
`adjugate_mul` (:264/:269), `Matrix.det_smul_inv_mulVec_eq_cramer` (:656).
**D4** Per-pool evaluation is PARTIAL: subring `OKat q₀` (denominator nonvanishing at
q₀) with `evalAt q₀ : OKat q₀ →+* ℚ`, hom laws from the hypothesis-carrying
`RatFunc.eval_add`/`eval_mul` (AsPolynomial.lean:184/:203) — exactly S.4's per-pool
discipline. Determinants commute with evaluation via `RingHom.map_det`.
**D5** Infinitude arguments through `Polynomial.eq_zero_of_infinite_isRoot`
(Roots.lean:145), packaged once as `ratfunc_eval_infinite`; serves the measured→symbolic
lifts (K-SUB, RS.1-DEEP), interpolant uniqueness, RS.3(ii), and RS.4.
**D6** Base change `powSubst (δ : ℕ+) : Qq →+* Qq` via `IsFractionRing.lift` over
`Polynomial.aeval (X^(δ:ℕ))` — **δ = 0 excluded by type** (finding 9); [2r] (e2)'s
δ-ABSOLUTE convention is the `Member.δ : ℕ+` field's docstring duty.
**D7** σ′ = literal `Multiset VType`; finiteness via the Finset field `SigSet` + the
covering field `sig_covers` (finding 7); convolution index
`{g : Fin m → Multiset V // ∑ j, g j = σ'}` gets a constructed `Fintype`.
**D8** μ̂-type fence: `MuHat` (one field, no `Add`, no coercion) — RS.1-MARKED's
"NEVER summed into R_σ" enforced by the elaborator.
**D9 (NEW)** Measured values live in `ℝ` (per-pool masses/densities), symbolic tables in
`Qq`; the two meet ONLY through interpolation fields `(↑(evalAt q₀ f) : ℝ) = val q₀`
quantified over the infinite pool set — the note's "one polynomial …, valued correctly
at every prime power" (S.3), stated as data + law, never as bare typing.

---

## 2. Defs skeleton — `lean/LeanUrat/MovesS/Defs.lean`

### 2.A Combinatorial layer (owner MovesV/MovesSp rosters; instance story: V.6's n = 3
rosters — 677 shapes / 9,494 outcomes per the dual-acceptance census — and U-29's n = 2 gate)

```lean
import Mathlib
namespace LeanUrat.MovesS
open Matrix Polynomial

abbrev Qq := RatFunc ℚ

/-- An INDIVIDUATED outcome member ([3t] SIBLING INDEXING). `δ : ℕ+` — base-change
    index, ABSOLUTE per [2r] (e2); δ = 0 unrepresentable (audit finding 9). -/
structure Member (V : Type*) (State : ℕ → Type*) where
  size   : ℕ
  δ      : ℕ+
  status : V ⊕ State size          -- halted-with-verdict | continuing into a block state

def Member.continuing (μ : Member V State) : Prop := μ.status.isRight = true

structure Outcome (V : Type*) (State : ℕ → Type*) where
  mem : List (Member V State)
  hm  : mem ≠ []

def Outcome.m (o : Outcome V State) : ℕ := o.mem.length
def Outcome.c (o : Outcome V State) : ℕ := (o.mem.filter (·.status.isRight)).length
def Outcome.verdicts (o : Outcome V State) : Multiset V :=
  (o.mem.filterMap (fun μ => μ.status.getLeft?) : List V)

inductive Route | kcol | termFin | split deriving DecidableEq
/-- The (m, c) CLASSIFICATION (S.0 rev 6, a DISPLAYED DEFINITION the note adopts). -/
def routeOf (o : Outcome V State) : Route :=
  if o.c = 0 then .termFin else if o.m = 1 then .kcol else .split

/-- HYPOTHESIS STRUCTURE (owner §V-TABLES/[2a]): block states + outcome rosters.
    COMBINATORIAL ONLY — no masses here (they live in MeasuredSide/RatBurdens). -/
structure TableShape (n : ℕ) where
  State  : ℕ → Type
  fin    : ∀ e, Fintype (State e)
  deq    : ∀ e, DecidableEq (State e)
  VType  : Type
  deqV   : DecidableEq VType
  Out    : ∀ e, State e → Type
  finO   : ∀ e τ, Fintype (Out e τ)
  odata  : ∀ e τ, Out e τ → Outcome VType State
  SigSet : Finset (Multiset VType)      -- the occurring σ′ ([2a] M1/M5 finiteness)
  sig_covers : ∀ e ∈ Finset.Icc 1 n, ∀ τ (o : Out e τ),          -- audit finding 7
    routeOf (odata e τ o) = .termFin → (odata e τ o).verdicts ∈ SigSet
attribute [instance] TableShape.fin TableShape.deq TableShape.deqV TableShape.finO
```

**(SCS) supply — REDESIGNED (findings 4, 5): the SP.1 member-typing carriers, so U-4
DERIVES flank-emptiness instead of assuming it.** Owner [2a] SP.1 + §B2-DEF D.5/D.8/D.10
via SP.2 (B1)/(B3). Intended instance: the letter fields of the MovesSp catalogue.

```lean
/-- Per-outcome window/letter data for the (SCS) derivation. All fields are the note's
    cited displays, one each; NONE states (SCS) or flank-emptiness itself. -/
structure SCSData (T : TableShape n) where
  W D ℓ g μsel : ∀ e τ (o : T.Out e τ), ℕ          -- window, degree, read-side width,
                                                    -- selected residual factor (g, μ)
  ℓpos : ∀ e τ o, 1 ≤ ℓ e τ o
  flankCount : ∀ e τ (o : T.Out e τ), ℕ            -- # flank sides of the window
  flankWidth : ∀ e τ (o : T.Out e τ), ℕ            -- their total raw width
  window_comp : ∀ e τ o, W e τ o = e * ℓ e τ o + flankWidth e τ o
    -- SP.1: "the horizontal compositions of the window span outside the read side"
  flankWidth_pos : ∀ e τ o, 0 < flankCount e τ o → 0 < flankWidth e τ o
  resFactors : ∀ e τ (o : T.Out e τ), Finset (ℕ × ℕ)     -- the residual shape λ
  sel_mem : ∀ e τ o, (g e τ o, μsel e τ o) ∈ resFactors e τ o
  res_sum : ∀ e τ o, ∑ x ∈ resFactors e τ o, x.1 * x.2 = ℓ e τ o   -- "Σᵢ g⁽ⁱ⁾·μ⁽ⁱ⁾ = ℓ"
  -- EACH flank side and EACH non-selected residual factor IS a member, distinct from
  -- the designated continuing member ("each side carrying ≥ 1 residual factor … = ≥ 1
  -- member"; "the non-selected part of λ is the residual co-factor"):
  memberOf : ∀ e τ o, Fin (flankCount e τ o) ⊕
    {x // x ∈ resFactors e τ o ∧ x ≠ (g e τ o, μsel e τ o)} →
    Fin (T.odata e τ o).mem.length
  memberOf_inj : ∀ e τ o, Function.Injective (memberOf e τ o)
  memberOf_ne_sel : ∀ e τ o (hc : routeOf (T.odata e τ o) = .kcol ∨ True) i,
    (T.odata e τ o).mem.get (memberOf e τ o i) |>.continuing = False ∨
    memberOf e τ o i ≠ selIdx e τ o          -- distinct from the designated member
  selIdx : ∀ e τ o, Fin (T.odata e τ o).mem.length   -- the designated/walked member
  stage_D : ∀ e τ o, D' e τ o = e * g e τ o * D e τ o        -- (B1): D′ = e·g·D
  stage_W : ∀ e τ o, W' e τ o = μsel e τ o                    -- (B3): W′ = μ
  W' D' : ∀ e τ (o : T.Out e τ), ℕ
  cluster_parent : ∀ e τ o, W e τ o * D e τ o = e             -- cluster size IS W·D
  cluster_child : ∀ e τ o (i : Fin (T.odata e τ o).mem.length),
    ((T.odata e τ o).mem.get i).continuing → i = selIdx e τ o →
    ((T.odata e τ o).mem.get i).size = W' e τ o * D' e τ o
```

*(E-phase note: field order/grouping to be normalized so `W'`/`D'` precede their laws;
`memberOf_ne_sel` simplifies to `memberOf e τ o i ≠ selIdx e τ o` — the disjunct above
is a drafting artifact to strike at elaboration. The LOAD-BEARING content: injections
from flanks + non-selected factors into member positions AVOIDING the designated one,
so m = 1 pigeonholes both sources empty — the note's step (1) verbatim.)*

### 2.B The measured side + the NINE-input ledger (findings 1, 8, 19 repaired)

Owner: [1v] CTS-M / [2b] XHD / [5]. Intended instance: the CTS cell space with its
digit-cell partition and XHD height classes (MovesV wave 4); the per-pool masses are the
O_δ conditional masses. Every CL-5 item is now a REAL Prop over these carriers.

```lean
/-- The measured (per-pool) side of the tables. Values in ℝ; pools are the prime powers
    q₀ = p^δ the note evaluates at. -/
structure MeasuredSide (T : TableShape n) where
  Pools : Set ℚ
  pools_infinite : Pools.Infinite         -- S.3/S.4: "at every prime power"/"cofinitely
                                          -- many all-active primes" need infinitude
  Cell : ∀ e, T.State e → Type            -- the one-step digit CELLS at (e, τ) —
  finC : ∀ e τ, Fintype (Cell e τ)        --   PART-1's partition objects ([1v] V.3(iv))
  cellOut : ∀ e τ, Cell e τ → T.Out e τ   -- each cell belongs to ONE outcome class
  Rep : ∀ e, T.State e → Type             -- concrete states of the cell-class τ
  rep_ne : ∀ e ∈ Finset.Icc 1 n, ∀ τ, Nonempty (Rep e τ)   -- non-vacuity (finding 19)
  μcell : ∀ e τ, Rep e τ → Cell e τ → ℚ → ℝ  -- XHD-resummed conditional cell mass,
                                              --   per representative, per pool
  Hgt : Type                               -- height points ([2b] M4a-X)
  HDom : ∀ e τ, Cell e τ → Set Hgt         -- the EXACT per-cell height domain (XHD-d)
  gwt : ∀ e τ (c : Cell e τ), Hgt → ℚ → ℝ  -- XHD-w fixed-height weight g(h) at pool
  kstep : ℕ → ∀ e, T.State e → T.State e → ℚ → ℝ  -- measured k-step in-block mass
  EntShape : ∀ e, T.State e → Type         -- entrance shapes ε into (e, β₀) (CTS-M(iii))
  finE : ∀ e τ, Fintype (EntShape e τ)     -- finite family (ENT-COUNT's roster)
  hent : ∀ e τ, EntShape e τ → ℕ           -- the retained h_ent(ε)
  ιshH : ∀ e τ, EntShape e τ → Hgt → ℚ → ℝ -- FIXED-HEIGHT per-shape marked mass
                                            --   ((COMP-h)'s object: the monomial-g
                                            --   level, initial factor included)
  ιDom : ∀ e τ, EntShape e τ → Set Hgt     -- the shape's exact entrance-height classes
  ιsh : ∀ e τ, EntShape e τ → ℚ → ℝ        -- per-shape POST-SPLIT marked mass ι_{e,ε,β₀}
  ιval : ∀ e, T.State e → ℚ → ℝ            -- the ENT-AGG aggregate ι_e, per pool

/-- CL-5, the NINE-input conditionality ledger — every item a contentful Prop over
    MeasuredSide's carriers (audit finding 1). Owners as displayed at S.0. -/
structure LedgerIV (T : TableShape n) (M : MeasuredSide T) : Prop where
  xhd_sum : ∀ e τ x c q₀, q₀ ∈ M.Pools →                        -- (1) XHD [2b]
    HasSum (fun h : M.HDom e τ c => M.gwt e τ c h q₀) (M.μcell e τ x c q₀)
    -- resummed cell mass = the sum of XHD-w weights over the EXACT domain
    -- ("else resummed rows sum masses of non-events")
  d4r0 : ∀ e τ c c', c ≠ c' → Disjoint (M.HDom e τ c) (M.HDom e τ c')   -- (2) D4R.0:
    -- disjointness after height grouping, per listed pairwise-disjoint component
  part1 : ∀ e ∈ Finset.Icc 1 n, ∀ τ x q₀, q₀ ∈ M.Pools →        -- (3) (iv)-PART-1 [1v]
    ∑ c : M.Cell e τ, M.μcell e τ x c q₀ = 1
    -- the digit-cell partition identity, per representative, countable across heights
  rep_indep : ∀ e τ (x y : M.Rep e τ), M.μcell e τ x = M.μcell e τ y   -- (4) (iv)-REP =
    -- M2(ii), weighted representative independence (probe: STATE-probe-2, BLOCKING)
  meas_nonneg : ∀ e τ x c q₀, 0 ≤ M.μcell e τ x c q₀              -- (5) (iv)-MEAS shadow:
    -- masses of events are nonnegative (the disjoint-measurability face rides (2)+(3))
  hmc : ∀ k e τ β q₀, q₀ ∈ M.Pools →                              -- (6) CTS-M(v) HMC
    M.kstep (k+1) e τ β q₀ = ∑ γ, M.kstep k e τ γ q₀ * M.kstep 1 e γ β q₀
    -- the k-step masses FACTOR through one-step (the whole-template height domains
    -- factor) — OPEN kernel; consumed by every K_e-power claim
  act : ∀ e τ x c q₀, q₀ ∈ M.Pools →                              -- (7) CTS-M(ii) ACT
    (∀ h ∈ M.HDom e τ c, M.gwt e τ c h q₀ = 0) → M.μcell e τ x c q₀ = 0
    -- empty-at-q₀ cells carry no mass (wild-p emptiness = weight vanishing)
  init_agg : ∀ e τ q₀, q₀ ∈ M.Pools →                             -- (8) CTS-M(iii)
    M.ιval e τ q₀ = ∑ ε : M.EntShape e τ, M.ιsh e τ ε q₀          --   INIT/ENT-AGG
    -- entrance heights are summed HERE and nowhere else (h_ent rides in ε alone)
  comp_once : ∀ e τ ε q₀, q₀ ∈ M.Pools →                          -- (9) COMP-TYPING:
    HasSum (fun h : M.ιDom e τ ε => M.ιshH e τ ε h q₀) (M.ιsh e τ ε q₀)
    -- heights summed EXACTLY ONCE: the resummed per-shape mass ιsh is THE height sum
    -- of the fixed-height (COMP-h) family over the shape's exact classes ((COMP-hΣ));
    -- the aggregate ιval (item 8) sums SHAPES, never heights again ((COMP-Σ)'s
    -- once-only discipline is structural: no other field of MeasuredSide takes a
    -- height sum — the only Hgt-summations in this corpus are xhd_sum and comp_once)
```

*(Design note for the re-audit: items (1)–(9) map 1:1 onto S.0's displayed ledger; each
is a Prop over MeasuredSide's own carriers with the owner at the field. Items (2)/(5):
D4R.0's disjointness is stated on the per-cell height domains (the note's "after height
grouping" per listed component) and MEAS's face here is nonnegativity + the partition
identity — the full measurable-disjointness statement needs [1v]'s event space and is a
recorded sync-list deliverable (§3w item W-9), not a silent drop.)*

### 2.C Rationality burdens, the kernel/exit objects, pools/E0/(REG-p)

```lean
/-- The evaluation locus and partial evaluation (D4). -/
def OKat (q₀ : ℚ) : Subring Qq := sorry            -- {f // f.denom.eval q₀ ≠ 0}; U-19
noncomputable def evalAt (q₀ : ℚ) : OKat q₀ →+* ℚ := sorry                       -- U-19

/-- THE RATIONALITY BURDENS (finding 3 repaired): the ℚ(q) tables are DATA + the
    interpolation LAW tying them to the measured per-pool values. Owners: CTS-M
    (iv)-POLY = CL-6 [1v]; XHD-s [2b]; INIT-RAT [1v]; (J-RAT) [1v]/[2b]. Intended
    instance: the computed [1v] blocks (V.6 rosters). A `RatBurdens` cannot exist
    unless the note's rationality claims actually hold of the measured side. -/
structure RatBurdens (T : TableShape n) (M : MeasuredSide T) where
  TG : ∀ e τ, T.Out e τ → Qq          -- the resummed one-step T·G per NON-split outcome
  J  : ∀ e τ, T.Out e τ → Qq          -- the CELL-LEVEL branching mass per split outcome
  ι  : ∀ e, T.State e → Qq            -- the ENT-AGG entrance vector
  tg_ok : ∀ e τ o q₀, q₀ ∈ M.Pools → TG e τ o ∈ OKat q₀            -- (iv)-POLY/XHD-s:
  tg_interp : ∀ e τ (x : M.Rep e τ) o q₀ (h : q₀ ∈ M.Pools),       -- valued correctly
    routeOf (T.odata e τ o) ≠ .split →                             -- at every pool
    (evalAt q₀ ⟨TG e τ o, tg_ok e τ o q₀ h⟩ : ℝ) =
      ∑ c ∈ {c : M.Cell e τ | M.cellOut e τ c = o}.toFinset, M.μcell e τ x c q₀
    -- kcol/term outcomes: T·G is the outcome's cell mass (each cell once — the
    -- (c=1,m=1)/(c=0) rows; NO source-mass division anywhere)
  j_ok : ∀ e τ o q₀, q₀ ∈ M.Pools → J e τ o ∈ OKat q₀              -- (J-RAT), OPEN:
  j_interp : ∀ e τ (x : M.Rep e τ) o q₀ (h : q₀ ∈ M.Pools),        -- per-cell rational
    routeOf (T.odata e τ o) = .split →                             -- tables
    (evalAt q₀ ⟨J e τ o, j_ok e τ o q₀ h⟩ : ℝ) =
      ∑ c ∈ {c : M.Cell e τ | M.cellOut e τ c = o}.toFinset, M.μcell e τ x c q₀
    -- J = the branching-cell mass, EACH CELL ONCE — NEVER the marked per-branch T·G
  ι_ok : ∀ e τ q₀, q₀ ∈ M.Pools → ι e τ ∈ OKat q₀                  -- INIT-RAT (cited
  ι_interp : ∀ e τ q₀ (h : q₀ ∈ M.Pools),                          -- burden, [1v])
    (evalAt q₀ ⟨ι e τ, ι_ok e τ q₀ h⟩ : ℝ) = M.ιval e τ q₀
  allActive : Set ℚ                    -- S.4(ii)'s all-active pools: "cofinitely many —
  allActive_sub : allActive ⊆ M.Pools  -- only finitely many primes are roots of some
  allActive_infinite : allActive.Infinite   -- not-identically-zero cell-size polynomial"

/-- K_e (S.0 display): entries sum T·G over (c = 1, m = 1)-routed outcomes landing in β.
    `hK` is the (SCS) conclusion AS AN ARGUMENT (finding 4: no structure field; U-6
    derives it from SCSData + DegCons, and every consumer instantiates it that way). -/
def kTarget (T : TableShape n) (e : ℕ) (τ : T.State e) (o : T.Out e τ)
    (hk : routeOf (T.odata e τ o) = .kcol)
    (hK : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) : T.State e := sorry  -- U-16a region:
    -- the unique continuing member's state, cast along hK (m = 1 from hk)
def Kmat (T) (RB : RatBurdens T M) (e : ℕ)
    (hK : ∀ τ o hk, ∀ μ ∈ (T.odata e τ o).mem, μ.size = e) :
    Matrix (T.State e) (T.State e) Qq := sorry     -- Σ over kcol outcomes with target β
def bTerm (T) (RB : RatBurdens T M) (e : ℕ) (σ' : Multiset T.VType) :
    T.State e → Qq := sorry                        -- Σ over termFin outcomes, v(o) = σ'
-- bSplit is a UNIT-level definition (U-16a): it needs (K-TRI) to license its
-- smaller-block applications (finding 10) and so takes `hdc : DegCons T`.

/-- DEG-CONS (CL-11, [1v]): per member over the FULL roster, halted members included. -/
structure DegCons (T : TableShape n) : Prop where
  size_pos : ∀ e τ (o : T.Out e τ), ∀ μ ∈ (T.odata e τ o).mem, 1 ≤ μ.size
  size_sum : ∀ e ∈ Finset.Icc 1 n, ∀ τ (o : T.Out e τ),
    ((T.odata e τ o).mem.map Member.size).sum ≤ e

/-- ESCAPE(E0) (OPEN KERNEL, CL-1, owner THIS note; per-pool, rev-3 widened form).
    NEVER proved in MovesS; U-21*/U-23* are its displayed "hence" consequences. -/
structure EscapeE0 {ι : Type*} [Fintype ι] (A : Matrix ι ι ℚ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  escape : Filter.Tendsto (fun k => (A ^ k) *ᵥ (fun _ => (1 : ℚ))) Filter.atTop (nhds 0)

/-- Per-pool package (S.4). Intended instance: the CTS-M(ii) active submatrix at q₀. -/
structure PoolHyp (T) (RB : RatBurdens T M) (e : ℕ) (hK) (q₀ : ℚ) where
  pool_mem : q₀ ∈ M.Pools
  Act : Finset (T.State e)
  entry_ok : ∀ τ β, τ ∈ Act → β ∈ Act → Kmat T RB e hK τ β ∈ OKat q₀
  A : Matrix Act Act ℚ
  A_eval : ∀ τ β, A τ β = evalAt q₀ ⟨Kmat T RB e hK τ.1 β.1, entry_ok _ _ τ.2 β.2⟩
  inactive_vanish : ∀ τ β (h : τ ∈ Act) (hβ : β ∉ Act)
    (hok : Kmat T RB e hK τ β ∈ OKat q₀), evalAt q₀ ⟨_, hok⟩ = 0
  e0 : EscapeE0 A

/-- CTS-M(ii-c)'s ACTIVE-VALUE AGREEMENT (weakened REV-7 form), PER POOL — a NAMED Prop
    consumers must cite before reading a value off at q₀ (the note: "must pass BEFORE it
    may be read off; a pole SURVIVING cancellation at a wild pool is (ii-c)'s FAIL").
    NOT a PoolHyp field: it is a per-object read-off gate, quantified at each consumer. -/
def AVAgree (P : PoolHyp T RB e hK q₀) (v : Qq) (bA : P.Act → ℚ) (τ : P.Act) : Prop :=
  ∃ hok : v ∈ OKat q₀, evalAt q₀ ⟨v, hok⟩ = ((1 - P.A)⁻¹ *ᵥ bA) τ
  -- "the evaluated object's q₀-value (after cancellation where needed — membership in
  -- OKat is post-cancellation by RatFunc's reduced num/denom) equals the
  -- active-subsystem solve there"; junk-block determinants are census-side (S.7),
  -- recorded not required nonzero — no det(1 − D_{q₀}) ≠ 0 Prop exists here.

/-- The RELEVANT POOLS are COMPUTED from the roster, never a free parameter
    (finding 19): δ = 1 AND every base-change index a split leg or shallow leg consumes. -/
def consumedDeltas (T : TableShape n) (Sh : ShapeFam T) : Finset ℕ+ := sorry
  -- {1} ∪ split-leg δ's (U-16a) ∪ shape-leg δ's (U-18); ShapeFam is §2.D (forward ref,
  -- E-phase ordering)
def RegP (T) (RB) (p : ℕ) (hK) : Prop :=
  ∀ e ∈ Finset.Icc 1 n, ∀ δ ∈ consumedDeltas T _, Nonempty (PoolHyp T RB e hK ((p:ℚ)^(δ:ℕ)))
```

### 2.D (BDY), shapes, the RS.1/RS.4 interfaces (findings 2, 6, 13, 15–18 repaired)

```lean
structure MuHat where val : Qq              -- μ̂-type fence (D8): no Add, no coercion

/-- (BDY), BOTH halves (finding 6): edge rule AND node shadow, on the abstract path
    model (reads/edges indexed 0..L, `fe` = the first-entrance edge index). -/
inductive ReadOwner | entrance | block deriving DecidableEq
def bdyEdgeOwner (fe r : ℕ) : ReadOwner := if r ≤ fe then .entrance else .block
def bdyNodeOwner (fe r : ℕ) : ReadOwner := if fe ≤ r then .block else .entrance
-- node ν_fe is BLOCK-side (a STATE INDEX) while the edge INTO it is entrance-side MASS.

/-- Shallow tree shapes Ŝ — length-matched RECORD (finding 13: no independent lists). -/
structure Shape (T : TableShape n) where
  k    : ℕ                                   -- # block entrances
  eOf  : Fin k → ℕ
  eIcc : ∀ i, eOf i ∈ Finset.Icc 1 n
  τOf  : ∀ i : Fin k, T.State (eOf i)        -- the landed states (BDY: the entrance
  δOf  : Fin k → ℕ+                          --   node's index); the δ-legs, ABSOLUTE
  σ0   : Multiset T.VType                    -- verdicts of the shallow τ-halted leaves
structure ShapeFam (T : TableShape n) where  -- owner [2a] (finiteness) + [3t] (CUT-3)
  Sh : Finset (Shape T)                      -- the finite-up-to-heights family
  -- intended instance: CUT-3's choice-free image {Ŝ(T)}; the (BDY)-inclusive reads
  -- and every shallow τ-halt are part of Shape's intended semantics (§3w W-7/W-8)

/-- RS.1's interface (findings 2, 15, 16, 17): the MEASURED objects with height index,
    XRB as the OPEN field, the measured fixpoint as the wave-4-dischargeable input —
    the symbolic identities are DERIVED (U-24a/b), never fields. -/
structure RS1Bundle (T : TableShape n) (M : MeasuredSide T) (RB : RatBurdens T M)
    (hdc : DegCons T) (hK) where
  βmeas : ∀ e ∈ Finset.Icc 1 n, ∀ (h_ent : ℕ) (τ : T.State e),
    Multiset T.VType → ℚ → ℝ               -- the measured conditional subtree value,
                                            -- ENTRANCE-HEIGHT-INDEXED (owner [3t])
  xrb : ∀ e he h h' τ σ', βmeas e he h τ σ' = βmeas e he h' τ σ'   -- (XRB), CL-9 —
    -- OPEN HERE (finding 2): the note proves it at S.1 GIVEN XHD+(JC-INV)+(SIB)/
    -- (JC-multi)+TB-CAP/VP+REL.2(a)(b)(d)+(ns-null); that derivation is measure-side
    -- (§3w W-2). MovesS consumes it only through this displayed field.
  βfam : ∀ e ∈ Finset.Icc 1 n, T.State e → Multiset T.VType → Qq   -- the symbolic family
  β_ok : ∀ e he τ σ' q₀, q₀ ∈ M.Pools → βfam e he τ σ' ∈ OKat q₀
  β_interp : ∀ e he τ σ' q₀ (h : q₀ ∈ M.Pools) (h_ent : ℕ),        -- interpolation: the
    (evalAt q₀ ⟨βfam e he τ σ', β_ok e he τ σ' q₀ h⟩ : ℝ)          -- symbolic β values
      = βmeas e he h_ent τ σ' q₀                                   -- the measured ones
  recursion_meas : ∀ e he τ σ' (hσ : σ' ∈ T.SigSet) q₀ (h : q₀ ∈ M.Pools) h_ent,
    βmeas e he h_ent τ σ' q₀ = evalRe T RB e hK τ σ' q₀ (fun e' he' => βmeas e' he' h_ent)
    -- the MEASURED (R_e-lump) fixpoint at every pool: `evalRe` (U-16a region) is the
    -- evaluated right side K·β + bTerm + bSplit with the split legs read from the SAME
    -- family at δ-shifted pools ([2r] (e2)) — smaller blocks only, licensed by (K-TRI).
    -- WAVE-4 DISCHARGE: TREE-EXP + TREE-N + ONE-F + (SIB)/CL-10 + PCI = REL.2(a)(b)(d)
    -- + CTS-M(iv)-REP + XRB (§3w W-3). This is the note's input, NOT its conclusion:
    -- RS.1-DEEP's identity β = (I−K)⁻¹b is DERIVED from it at U-24a/b.
  βfull : ∀ e ∈ Finset.Icc 1 n, ∀ h_ent (τ : T.State e), Multiset T.VType → ℚ → ℝ
  nsNull : Prop                              -- the (ns-null) tag ([3t] §T.2, CLOSED there;
  rexact : nsNull → ∀ e he h_ent τ σ' q₀,    --   discharged at wave 4 by [3t]'s closure)
    βfull e he h_ent τ σ' q₀ = βmeas e he h_ent τ σ' q₀     -- (R_e-exact), GIVEN (ns-null)

/-- RS.4's inherited chain (finding 18): the note's TWO named primewise inputs, each
    with its owner — never a fused "eval = 1" oracle. -/
structure RS4Chain (T M RB hdc hK) (B : RS1Bundle T M RB hdc hK) (F : ShapeFam T) where
  Wsh : Shape T → Qq                          -- W_Ŝ; production = CL-17(ii), OPEN —
  wsh_ok : ∀ Ŝ ∈ F.Sh, ∀ q₀ ∈ M.Pools, Wsh Ŝ ∈ OKat q₀          -- its ℚ(q) membership
  R : SplitTy → Qq                            -- the density components (RS.1-SH's target)
  SplitTy : Type ; finS : Fintype SplitTy
  Rval : SplitTy → ℚ → ℝ                      -- measured densities at pools (owner [3t])
  r_ok : ∀ σ q₀, q₀ ∈ M.Pools → R σ ∈ OKat q₀
  r_interp : ∀ σ q₀ (h : q₀ ∈ M.Pools), (evalAt q₀ ⟨R σ, r_ok σ q₀ h⟩ : ℝ) = Rval σ q₀
  PrimePools : Set ℚ                          -- the evaluation primes (δ = 1 pools)
  prime_sub : PrimePools ⊆ M.Pools ; prime_infinite : PrimePools.Infinite
  decidedTotal : ℚ → ℝ                        -- the primewise decided-mass series total
  x3_total : ∀ p ∈ PrimePools, decidedTotal p = 1     -- X.3's density form — CL-4, OPEN,
    -- owner [5] §X-EXHAUST (conditional there per its record line); (ns) residual 0
    -- GIVEN (ns-null); wave-4 discharge W-4
  rs1_total : ∀ p ∈ PrimePools, (∑ σ, Rval σ p) = decidedTotal p  -- "RS.1 equates that
    -- series with Σ_σ R_σ(p)" — provenance: RS.1-SH + ONE-F (its own derivation is the
    -- deferred W-1); stated on the MEASURED side, owner [3t]/THIS note's S.2
```

*(Field-order/universe plumbing (`SplitTy` before its uses, `M` binders) is E-phase
normalization; the trust surface is the field LIST above.)*

---

## 3. The unit DAG — REV 2: 38 units (12 easy / 25 medium / 1 hard)

Format per campaign §2; one file `MovesS/<Id>.lean` per unit. All block quantifiers
`e ∈ Finset.Icc 1 n` (finding 11).

### Layer S0 — dispatch, arithmetic, (SCS), (BDY) [7]

**U-1 `MovesS.dispatch_spec` · Dispatch.lean · easy** — as round 1 (audit-clean):
`(routeOf o = .termFin ↔ o.c = 0) ∧ (routeOf o = .kcol ↔ o.c = 1 ∧ o.m = 1) ∧
(routeOf o = .split ↔ 1 ≤ o.c ∧ 2 ≤ o.m)` given `1 ≤ o.m`, `o.c ≤ o.m`.
moves_ref: "EXHAUSTIVE AND EXCLUSIVE BY CONSTRUCTION: the three predicates partition
{(m, c) : m ≥ 1, 0 ≤ c ≤ m}". deps: Defs · hyp: none · sketch: unfold + omega.

**U-2 `MovesS.ktri` · KTri.lean · easy** — as round 1: DegCons + `2 ≤ m` ⟹
`∀ μ ∈ mem, μ.size < e` (for `e ∈ Icc 1 n`). moves_ref: "at m ≥ 2 EVERY e_j < e".
deps: Defs · hyp: DegCons (CL-11) · sketch: sum bound + omega.

**U-3 `MovesS.kcol_agree` · KColAgree.lean · easy** — as round 1: a continuing block-e
member forces m = 1 (agreement check (ii)). deps: U-2 · hyp: DegCons.

**U-4 `MovesS.scs_flank` · ScsFlank.lean · medium — REDESIGNED (findings 4, 5).**
`statement`: `theorem scs_flank (T) (S : SCSData T) {e τ o} (hm : (T.odata e τ o).m = 1) :`
`S.flankCount e τ o = 0 ∧ S.resFactors e τ o = {(S.g e τ o, S.μsel e τ o)} ∧`
`S.W e τ o = e * S.ℓ e τ o ∧ S.g e τ o * S.μsel e τ o = S.ℓ e τ o`
moves_ref: "m = 1 forces NO flank side (the read side spans the window: e·ℓ = W) and a
SINGLETON residual shape λ = {(g, μ)}, i.e. g·μ = ℓ."
deps: Defs · hyp: SCSData's SP.1 carriers (memberOf/memberOf_inj/≠ selIdx, window_comp,
res_sum — owner [2a] SP.1) · sketch: m = 1 ⟹ Fin 1 member positions; `memberOf` avoids
`selIdx` injectively, so its domain is empty: flankCount = 0 and non-selected residual
factors = ∅, i.e. λ = {(g, μsel)}; `window_comp` + `flankWidth_pos` give W = e·ℓ;
`res_sum` on the singleton gives g·μ = ℓ. GENUINE pigeonhole derivation, no assumed
conclusion.

**U-5 `MovesS.scs_stage` · ScsStage.lean · easy** — `W' * D' = W * D` at m = 1 from
stage_D/stage_W + U-4. moves_ref: "W′·D′ = μ·e·g·D = (g·μ)·e·D = ℓ·e·D = W·D".
deps: U-4 · hyp: SCSData stage laws (§B2-DEF D.5/D.8/D.10 via [2a] SP.2 (B1)/(B3)).

**U-6 `MovesS.scs` · Scs.lean · medium** — `statement`:
`theorem scs (T) (S : SCSData T) (hdc : DegCons T) (e) (he : e ∈ Finset.Icc 1 n) τ o`
`(hk : routeOf (T.odata e τ o) = .kcol) : ∀ μ ∈ (T.odata e τ o).mem, μ.size = e`
moves_ref: "(SCS) a (c = 1, m = 1) outcome's single child inherits the block size:
e₁ = e". deps: U-1, U-4, U-5 · hyp: SCSData.cluster_parent/cluster_child · sketch:
hk ⟹ m = 1 (U-1); the single member is selIdx and continuing; cluster_child +
U-5 + cluster_parent: size = W′D′ = WD = e. **PRODUCES the `hK` argument every
`Kmat`/`PoolHyp`/solve consumer takes — no structure field assumes it (finding 4).**

**U-7 `MovesS.bdy` · Bdy.lean · medium — EXPANDED (finding 6).** Three statements:
`bdy_edge_partition : ∀ fe r, (bdyEdgeOwner fe r = .entrance ↔ r ≤ fe) ∧
(bdyEdgeOwner fe r = .block ↔ fe < r)`; `bdy_node_shadow : ∀ fe,
bdyNodeOwner fe fe = .block ∧ bdyEdgeOwner fe fe = .entrance ∧
∀ r ≠ fe, bdyNodeOwner fe r = bdyEdgeOwner fe r`; `bdy_mass_split : ∀ (μm : ℕ → ℝ) L fe,
fe ≤ L → ∑ r ∈ Finset.range (L+1), μm r = (∑ r ∈ Finset.Icc 0 fe, μm r) +
(∑ r ∈ Finset.Icc (fe+1) L, μm r)` — no read omitted, none double-charged.
moves_ref: "the first entrance node ν is BLOCK-side as a STATE INDEX …, while the edge
INTO ν is entrance-side MASS — no read omitted, none double-charged."
deps: Defs · hyp: none · sketch: split_ifs/omega; Finset.sum split. The CONSUMPTION
duties (ι owns the ε-prefix with retained h_ent; W_Ŝ inclusive; β charges nothing for
the entering read) are §3w W-8 — named, owned, not silently dropped.

### Layer S1 — (K-SUB) [4]

**U-8 `MovesS.ksub_regroup` · KSubRegroup.lean · medium** — `statement` (per e ∈ Icc 1 n,
τ, with hK from U-6): `(∑ β, Kmat T RB e hK τ β) + (∑ σ' ∈ T.SigSet, bTerm T RB e σ' τ) +`
`(∑ o ∈ splitOuts T e τ, RB.J e τ o) = ∑ o : T.Out e τ, routedMass RB e τ o` where
`routedMass := if routeOf = .split then J else TG`.
moves_ref: "(K-SUB) Σ_β K_e(τ,β) + Σ_{σ′} b_e^{term,fin}(τ)(σ′) + (branching-cell
one-step mass, per cell once) = 1, the third summand being exactly Σ_o J_{τ,o}".
deps: U-1, U-6 · hyp: `T.sig_covers` (now a REAL field — finding 7) · sketch: partition
the roster by routeOf (U-1); regroup kcol terms by kTarget and termFin terms by
verdicts (`Finset.sum_fiberwise_of_maps_to`; sig_covers makes the σ'-sum exhaustive).

**U-9a `MovesS.ksub_eval` · KSubEval.lean · medium** — per pool: `∀ q₀ ∈ M.Pools, ∀ x,`
`(evaluated LHS of U-8's right side) = 1`. moves_ref: "PART-1 (the digit-cell partition
identity, per representative, countable across heights) gives (K-SUB)".
deps: U-8, U-19 · hyp: LedgerIV.part1 + RB.tg_interp/j_interp (the TG-vs-J cell
identifications — the routing derivation the audit demanded, finding 8) · sketch:
evaluate routedMass o via interp = Σ of o's cell masses; `Finset.sum_fiberwise` over
cellOut collapses Σ_o Σ_{cells of o} to Σ_cells; part1 closes at 1.

**U-9b `MovesS.ksub` · KSub.lean · medium** — the SYMBOLIC identity: U-8's left side
`= 1` in Qq. deps: U-8, U-9a, U-27 · hyp: as U-9a + M.pools_infinite · sketch: the
difference vanishes at every pool (U-9a); infinitude (U-27) kills it. (K-SUB)'s
conditionality bracket (iv)-ledger + DEG-CONS + (m,c) + (SCS) is now the LITERAL
hypothesis trace: LedgerIV + DegCons + routeOf + U-6.

**U-10 `MovesS.ksub_pool` · KSubPool.lean · medium — RESTATED (finding 20).**
`statement`: `theorem ksub_pool (P : PoolHyp T RB e hK q₀) (L : LedgerIV T M)`
`(hTG : ∀ o, ∃ h : RB.TG e τ o ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨_, h⟩)`
`(hJ : ∀ o, ∃ h : RB.J e τ o ∈ OKat q₀, 0 ≤ evalAt q₀ ⟨_, h⟩)`
`(τA : P.Act) : (∀ βA : P.Act, 0 ≤ P.A τA βA) ∧ (∑ βA : P.Act, P.A τA βA) ≤ 1`
moves_ref: "K_e's rows are genuine sub-distributions … every summand ≥ 0".
deps: U-9a, U-19 · hyp: PoolHyp memberships explicit; nonneg evaluations supplied by
meas_nonneg + interp (a derivable lemma, folded here) · sketch: evaluate U-9a at q₀,
drop the two nonneg exit sums, restrict to Act via inactive_vanish.

### Layer S2 — the ℚ(q) system and its solve [11]

**U-11 `MovesS.decompFintype` · Decomp.lean · medium** — as round 1:
`instance : Fintype {g : Fin m → Multiset V // ∑ j, g j = σ'}` (DecidableEq V).
moves_ref: "the MULTISET CONVOLUTION over children's types". sketch: induct on m via
sub-multiset finiteness.

**U-12 `MovesS.powSubst` · PowSubst.lean · medium — δ = 0 EXCLUDED (finding 9).**
`noncomputable def powSubst (δ : ℕ+) : Qq →+* Qq` + `powSubst_X : powSubst δ X = X^(δ:ℕ)`
+ `powSubst_C`. moves_ref: "composed with q ↦ q^{δ_j} (which maps ℚ(q) → ℚ(q)); the
ARGUMENT convention is [2r] (e2) (δ absolute)". sketch: `IsFractionRing.lift` over
`aeval (X^(δ:ℕ))`; nonzero polys map to nonzero since δ ≥ 1 (degree scales by δ).

**U-13 `MovesS.solve_iff` · SolveIff.lean · easy** — as round 1:
`β = K *ᵥ β + b ↔ (1 - K) *ᵥ β = b`. moves_ref: "(R_e-lump) β_e = K_e β_e + b_e^{…}".

**U-14 `MovesS.solve_exists_unique` · SolveEU.lean · medium** — as round 1: `hdet ⟹
∃! β, β = K *ᵥ β + b`, witness `(1-K)⁻¹ *ᵥ b`. deps: U-13 · Mathlib:
`isUnit_iff_ne_zero`, `Matrix.isUnit_iff_isUnit_det`, `mul_nonsing_inv`/`nonsing_inv_mul`.

**U-15 `MovesS.solve_cramer` · SolveCramer.lean · medium** — as round 1 (adjugate/Cramer
entrywise form). moves_ref: "β_e = adj(I − K_e) b_e / det(I − K_e) entrywise". RS.2's
conditionality is now REAL (finding 3): `Kmat`/`bTerm`/`bSplit` exist only over a
`RatBurdens`, so "fixed coefficients in ℚ(q)" is exactly "GIVEN the cited rationality
burdens (each named)" — the burdens carry (iv)-POLY/XHD-s/INIT-RAT/(J-RAT) as
interpolation laws, and p enters only at `evalAt` (p-INDEPENDENCE, docstring duty).

**U-16a `MovesS.bSplit_def` · BSplitDef.lean · medium — NEW (findings 10, 22).**
`noncomputable def bSplit (T RB) (hdc : DegCons T) (e) (he : e ∈ Finset.Icc 1 n)`
`(βlt : ∀ e' ∈ Finset.Icc 1 (e-1), T.State e' → Multiset T.VType → Qq)`
`(σ' : Multiset T.VType) : T.State e → Qq` — per split outcome o:
`RB.J e τ o * ∑ g : decomps σ' o.m, ∏ j, legFactor j` where a halted member's factor is
`if σ_j = {verdict} then 1 else 0` (§T.4 leaf convention) and a continuing member μ's is
`powSubst μ.δ (βlt μ.size ⟨by exact ktri-bound⟩ (state of μ) σ_j)` — the βlt application
LICENSED INSIDE the definition by U-2's (K-TRI) bound (route = split ⟹ m ≥ 2 ⟹
μ.size < e, and μ.size ≥ 1 by DegCons). Also defines `evalRe` (the evaluated (R_e) right
side RS1Bundle.recursion_meas cites) and `consumedDeltas` (the δ's of all split legs ∪
shape legs ∪ {1}). moves_ref: "b_e^split(τ)(σ′) := Σ_{o branching} J_{τ,o}(q) ·
Σ_{σ′ = σ₁ ⊎ … ⊎ σ_m} ∏_{j=1}^m β_{e_j,τ_j(o)}(σ_j)(q^{δ_j})".
deps: U-1, U-2, U-11, U-12 · hyp: DegCons — now an ARGUMENT of the definition itself.

**U-16b `MovesS.blockSolve` · BlockSolve.lean · medium (was hard; split per finding 22).**
`noncomputable def blockSolve (T RB) (hdc) (hK) (hdet : ∀ e ∈ Finset.Icc 1 n,`
`(1 - Kmat T RB e (hK e)).det ≠ 0) : ∀ e ∈ Finset.Icc 1 n, T.State e → Multiset T.VType → Qq`
by strong recursion on e (`Nat.strong_induction_on`), body
`(1 - Kmat)⁻¹ *ᵥ (bTerm + bSplit … (previously solved family))`. moves_ref: "blocks
solve bottom-up, each b_e^split leg already solved". deps: U-14, U-16a. NO e = 0 case
(finding 11): the domain is `Icc 1 n` throughout.

**U-17a `MovesS.blockSolve_spec` · BlockSolveSpec.lean · medium** — the defining
(R_e-lump) equation per e ∈ Icc 1 n, σ' ∈ SigSet: `blockSolve … e he · σ' =`
`Kmat *ᵥ (blockSolve … e he · σ') + bTerm … + bSplit … (restriction of blockSolve) σ'`.
moves_ref: "(R_e-lump) β_e = K_e β_e + b_e^{term,fin} + b_e^split [UNCONDITIONAL]".
deps: U-16b, U-14 · sketch: unfold one recursion layer + U-14's witness equation.

**U-17b `MovesS.rexact_solve` · RexactSolve.lean · medium — NEW (finding 12).**
`statement`: `theorem rexact_solve (B : RS1Bundle …) (hns : B.nsNull) :`
`∀ e he h_ent τ σ' q₀, q₀ ∈ M.Pools → B.βfull e he h_ent τ σ' q₀ = B.βmeas e he h_ent τ σ' q₀`
— (R_e-exact) as a Lean statement: the FULL conditional subtree value equals the lump
value, GIVEN (ns-null). moves_ref: "(R_e-exact) β_e^full = β_e [GIVEN (ns-null) —
CLOSED at [3t] §T.2 …; the discharged tag stays displayed]". deps: Defs · hyp:
B.rexact + nsNull (the tag as a Prop field, discharged by [3t] at wave 4 — §3w W-5) ·
sketch: fire the field. The unit exists so the tag is a CITABLE Lean statement, per the
audit; combined with U-24b it yields βfull = the solve.

**U-18 `MovesS.rsh_def` · RshDef.lean · medium — REDESIGNED (finding 13).**
`noncomputable def shConv (T RB) (B) (Ŝ : Shape T) (σ : Multiset T.VType) : Qq :=`
`∑ g : {g : Fin Ŝ.k → Multiset T.VType // σ = Ŝ.σ0 + ∑ i, g i},`
`∏ i, powSubst (Ŝ.δOf i) (B.βfam (Ŝ.eOf i) (Ŝ.eIcc i) (Ŝ.τOf i) (g i))` and
`noncomputable def Rsh (F : ShapeFam T) … (σ) : Qq := ∑ Ŝ ∈ F.Sh, C.Wsh Ŝ * shConv … Ŝ σ`.
The Shape RECORD (§2.D) length-matches entrances/δ-legs BY CONSTRUCTION and supplies
σ₀; the β-family is B.βfam — every datum of the quoted display is now determined.
moves_ref: "R_σ = Σ_{Ŝ} W_Ŝ(q) · Σ_{σ = σ₀(Ŝ) ⊎ σ₁ ⊎ …} ∏_{i=1}^{k(Ŝ)}
β_{e_i(Ŝ),τ_i(Ŝ)}(σ_i)(q^{δ_i})". deps: U-11, U-12 · hyp: ShapeFam ([2a] finiteness;
CUT-3's choice-free image is the intended instance, §3w W-7).

**U-18b `MovesS.interp_unique` · InterpUnique.lean · easy — NEW.** If f, g ∈ Qq are
OK and agree at every pool of an infinite set, f = g. moves_ref: "every coefficient of
(R_e) is ONE FIXED element of ℚ(q), the same at every prime" (S.3 — fixedness IS
uniqueness of the interpolant). deps: U-27 · sketch: apply U-27 to f − g. Ties every
RatBurdens/RS-bundle Qq datum UNIQUELY to its measured values — the non-degeneracy
counterpart of the interp fields (finding 19's "satisfiable by a wrong instance" is
now excluded up to measured equality).

### Layer S3 — pools, evaluation, ESCAPE(E0) consequences [10]

**U-19 `MovesS.evalAt` · EvalAt.lean · medium** — `OKat q₀ : Subring Qq` +
`evalAt q₀ : OKat q₀ →+* ℚ` + `evalAt_coe`. moves_ref: "EVALUATION IS PER POOL (rev 3):
symbolic det ≠ 0 prevents no zero or uncancelled pole at an individual q₀ = p^δ."
sketch: denom-divisibility closure; hom laws from `RatFunc.eval_add`/`eval_mul`.

**U-20 `MovesS.eval_det` · EvalDet.lean · easy — moves_ref CORRECTED (finding 21).**
`evalAt q₀ M.det = (M.map (evalAt q₀)).det` via `RingHom.map_det`. This unit is
INFRASTRUCTURE for S.4(ii)'s evaluation step, whose display it now quotes:
moves_ref: "at all-active primes … K_e(p) = A and ρ(A) < 1 gives det(I − A) ≠ 0" —
the implicit "det evaluated = det of evaluated matrix" reading of `K_e(p) = A`.
deps: U-19. (The active-value-agreement display now lives at `AVAgree` (§2.C), not here.)

**U-21a `MovesS.pow_fixed_vector` · PowFixed.lean · easy (split of round-1 U21).**
`A *ᵥ v = v → ∀ k, (A ^ k) *ᵥ v = v`. sketch: induction; `Matrix.mulVec_mulVec`.

**U-21b `MovesS.mulVec_abs_bound` · MulVecBound.lean · medium (split).**
For `0 ≤ A i j` entrywise: `|((A ^ k) *ᵥ v) i| ≤ (Finset.univ.sup' _ fun j => |v j|) *`
`((A ^ k) *ᵥ 1) i`. sketch: triangle inequality along the matrix–vector sum; powers of
nonneg matrices are nonneg (uses U-23b).

**U-21c `MovesS.e0_det_ne_zero` · E0Det.lean · medium (split).**
`EscapeE0 A → (1 - A).det ≠ 0`. moves_ref: "A(q₀) being a FINITE nonnegative matrix,
ρ(A(q₀)) < 1, the Neumann series converges" (the det ≠ 0 face). deps: U-21a, U-21b ·
hyp: EscapeE0 (CL-1 — the OPEN kernel; this is its displayed "hence") · sketch:
contrapositive via `Matrix.exists_mulVec_eq_zero_iff`; kernel vector rides U-21a; U-21b
+ escape kills it.

**U-22 `MovesS.rs3_det_symbolic` · Rs3Det.lean · medium — RESTATED (finding 14).**
`statement`: `theorem rs3_det_symbolic (T RB hdc hK) (L : LedgerIV T M)`
`(hact : ∀ q₀ ∈ RB.allActive, ∃ P : PoolHyp T RB e hK q₀, P.Act = Finset.univ) :`
`∀ e ∈ Finset.Icc 1 n, (1 - Kmat T RB e (hK e)).det ≠ 0`
moves_ref: "at all-active primes (cofinitely many — only finitely many primes are roots
of some not-identically-zero cell-size polynomial) K_e(p) = A and ρ(A) < 1 gives
det(I − A) ≠ 0; a rational function vanishing at infinitely many prime evaluations is 0".
deps: U-19, U-20, U-21c, U-27 · hyp: **the note's package** — E0 (inside PoolHyp) +
(iv)-POLY, the latter entering as `RB.allActive_infinite` + `tg_ok` (the (iv)-POLY/XHD-s
burden's all-active infinitude and entry evaluability, §2.C) — no bespoke single-pool
package (the round-1 defect) · sketch: if det = 0 symbolically it evaluates to 0 at
every all-active pool (U-20 + entry_ok); at any one of the infinitely many, U-21c gives
det(1 − A) ≠ 0 — contradiction. Per-pool value read-off stays guarded by `AVAgree`
(never derived here); ESCAPE-UNIF is consumed by NOTHING.

**U-23a `MovesS.neumann_partial` · NeumannPartial.lean · easy (split of round-1 U23).**
`(1 - A) * (∑ m ∈ Finset.range k, A ^ m) = 1 - A ^ k`. sketch: telescope.

**U-23b `MovesS.pow_entry_nonneg` · PowNonneg.lean · easy (split).**
`(∀ i j, 0 ≤ A i j) → ∀ k i j, 0 ≤ (A ^ k) i j`. sketch: induction + sum of products.

**U-23c `MovesS.pow_entry_tendsto` · PowTendsto.lean · easy (split).**
`EscapeE0 A → ∀ i j, Tendsto (fun k => (A ^ k) i j) atTop (nhds 0)`. sketch:
`0 ≤ (A^k) i j ≤ ((A^k) *ᵥ 1) i` (U-23b) + squeeze.

**U-23d `MovesS.e0_inv_nonneg` · E0InvNonneg.lean · medium (split).**
`EscapeE0 A → ∀ i j, 0 ≤ (1 - A)⁻¹ i j`. moves_ref: "the Neumann series converges, and
(I − A(q₀))^{−1} ≥ 0." deps: U-21c, U-23a/b/c · sketch: `(1-A)⁻¹ = Σ_{m<k} A^m +`
`(1-A)⁻¹ * A^k` (U-23a + inverse); partial sums nonneg (U-23b); remainder → 0 (U-23c);
order-closed limit. Consumer: [4]/SQ.2 only — not on MovesS's downstream path.

### Layer S4 — RS.1-DEEP, the marked pairing, RS.4 [6]

**U-24a `MovesS.rs1_deep_eval` · Rs1DeepEval.lean · medium — NEW DECOMPOSITION
(finding 15).** `statement`: the SYMBOLIC fixpoint from the measured one: for
B : RS1Bundle, e ∈ Icc 1 n, σ' ∈ SigSet:
`B.βfam e he · σ' = Kmat T RB e (hK e) *ᵥ (B.βfam e he · σ') + bTerm … σ' +`
`bSplit T RB hdc e he (restriction of B.βfam) σ'`
deps: U-16a, U-19, U-27 · hyp: B.recursion_meas (the measured per-pool fixpoint —
wave-4 discharge W-3) + B.β_interp/β_ok + B.xrb + interp fields of RB + pools_infinite ·
sketch: at each pool the evaluated difference of the two sides vanishes
(recursion_meas + the interp laws + `powSubst`-evaluation compatibility at δ-shifted
pools — the [2r] (e2) convention); entrywise infinitude (U-27) lifts to Qq. **The
round-1 `∀ hβ` malformation is GONE: the recursion is stated of B's OWN family, smaller
blocks read from the same family.**

**U-24b `MovesS.rs1_deep` · Rs1Deep.lean · hard** — RS.1-DEEP:
`B.βfam e he · σ' = ((1 - Kmat T RB e (hK e))⁻¹ *ᵥ (bTerm + bSplit …(B.βfam))) ·` and
`B.βfam = blockSolve T RB hdc hK hdet` (strong induction on e).
moves_ref: "(RS.1-DEEP) per block (e, τ): β_{e,τ}(σ′) = ((I − K_e)^{−1} b_e)_τ(σ′)".
deps: U-14, U-16b, U-17a, U-24a · hyp: hdet (from U-22) + U-24a's set · sketch: per e,
U-24a + U-14 uniqueness identify βfam e with the inverse solve of ITS b; strong
induction on e (legs already identified) matches it with blockSolve. GENUINELY derived;
the only assumed input is the measured fixpoint, the note's actual GIVEN.

**U-25 `MovesS.marked_def` · MarkedDef.lean · easy — RESCOPED (finding 17).**
`noncomputable def markedPairing (T RB hK hdet) (e) (he) : MuHat :=`
`⟨RB.ι e ⬝ᵥ ((1 - Kmat T RB e (hK e))⁻¹ *ᵥ bAgg T RB hdc e he)⟩` — the ORIENTATION
display AS A DEFINITION (the scalar ι_e^T(I−K_e)^{−1}b_e), plus the fence lemma: no
`Add MuHat`/no coercion instance exists (a `#guard_msgs` elaboration check). The
IDENTIFICATION with the measured μ̂ marked total is NOT claimed here — it is sync entry
W-1m with its COMP-h/COMP-hΣ/HMC/ENT-AGG/(iv)-REP provenance. moves_ref: "(RS.1-MARKED)
the pairing ι_e^T(I − K_e)^{−1}b_e is the μ̂-typed MARKED-entrance total … NEVER summed
into R_σ." deps: U-16a/b.

**U-27 `MovesS.ratfunc_eval_infinite` · EvalInfinite.lean · medium** — as round 1:
infinite OK vanishing set ⟹ f = 0 (via `Polynomial.eq_zero_of_infinite_isRoot`).
moves_ref: "a rational function equal to 1 at infinitely many prime powers is
identically 1" (applied to f − 1 by consumers).

**U-28 `MovesS.rs4_rational_step` · Rs4.lean · medium — RESCOPED (finding 18).**
`statement`: `theorem rs4_rational_step (C : RS4Chain …) : (∑ σ, C.R σ) = 1`
moves_ref: "at each prime p the decided-mass series totals 1 — X.3's density form …;
RS.1 equates that series with Σ_σ R_σ(p); a rational function equal to 1 at infinitely
many prime powers is identically 1." deps: U-27 · hyp: the note's TWO named primewise
inputs, separately (finding 18): `C.x3_total` (X.3/CL-4, owner [5], OPEN) and
`C.rs1_total` (RS.1's equating — provenance W-1) + `C.r_interp`/`r_ok` (the RS.2
rationality chain: the burdens + CL-17(ii)'s wsh_ok ride the R-construction) +
prime_infinite · sketch: eval(Σ R − 1) = Σ Rval − decidedTotal = 0 at every prime pool;
U-27. This IS the note's "RS.4's rational-identity step [S.5 — GIVEN its inherited
set]" (S.6's own DERIVED bracket) — the inherited set is the explicit field trace.

**U-29 `MovesS.instance_n2` · InstanceN2.lean · medium — NEW (finding 19).**
The NON-VACUITY GATE: construct concrete `TableShape`/`MeasuredSide`/`RatBurdens`
(+ DegCons, SCSData, LedgerIV) for the note's displayed n = 2 instance — ONE block-2
state, the 1×1 kernel, W6's geometric series — and verify by `decide`/`norm_num`:
`(1 - Kmat …).det ≠ 0` and the solve's denominator is `q² + q + 1` (up to units).
moves_ref: "The n = 2 instance is the 1×1 case (W6's geometric series, denominator
q² + q + 1)". deps: U-16b · sketch: `Fin 1` states; kernel entry the displayed
monomial ratio; `RatFunc` arithmetic by `field_simp`. Inhabits EVERY structure of §2 —
the audit's degenerate-instance loophole is closed by exhibition.

---

## 3w. THE WAVE-4 SYNC LIST (declared deferrals — statements PINNED, derivations owed)

Each entry: the pinned Lean Prop (definition, in `MovesS/SyncDefs.lean`), its note
display, its provenance/owner. NO wave-2 unit proves these; NO structure field states
their conclusion beyond the measured inputs listed in §2.

- **W-1 `RS1SH_holds`** := `∀ σ, C.R σ = Rsh F … σ` — RS.1-SH verbatim (S.2). Owed by:
  MovesT (TREE-EXP, TREE-N, ONE-F, (SIB)/CL-10, PCI) + (CUT-WD) + XRB + [2r] legs +
  CL-17(ii)'s W_Ŝ machinery. `C.rs1_total` (§2.D) is its evaluated shadow.
- **W-1m `RS1Marked_holds`** := the measured μ̂ marked total equals
  `(markedPairing …).val` evaluated per pool — RS.1-MARKED's identification. Owed by:
  MovesV/MovesT ((COMP-h) → (COMP-hΣ) → HMC/(COMP-Σ) → ENT-AGG/(COMP-AGG), (iv)-REP).
- **W-2 XRB discharge** — S.1's proof of `RS1Bundle.xrb` under XHD(w/u/d/s) + (JC-INV)
  + (SIB)/(JC-multi) + TB-CAP/VP + REL.2(a)(b)(d) + (ns-null): measure-side; recorded
  at the acceptance-only edge [3] → [3t]-FULL. Until then `xrb` is an open field.
- **W-3 `recursion_meas` discharge** — the measured (R_e-lump) fixpoint from TREE-EXP's
  per-fiber expansion (deep splits at b^split ONCE, per the ROUTING law; J per cell).
- **W-4 `x3_total` discharge** — X.3's density form (CL-4, owner [5], conditional per
  §X-EXHAUST's record; (ns) residual 0 GIVEN (ns-null); countability via (NS-c)).
- **W-5 `nsNull` discharge** — [3t] §T.2's closure of (ns-null) instantiates the field.
- **W-6 per-pool read-off** — every numeric consumption of a β/R value at q₀ cites
  `AVAgree` (§2.C) + its `PoolHyp`; the RESUM-n3/census layers (S.7) live here, not in
  Lean units.
- **W-7 ShapeFam instantiation** — CUT-3's choice-free Ŝ(T) image as `Sh`, with
  (CUT-WD)'s trichotomy (derived in the note GIVEN the CL-13 entrance-predicate supply).
- **W-8 (BDY) consumption duties** — ι owns the ε-prefix with retained h_ent (MovesV
  (COMP-h)); W_Ŝ inclusive of entering reads (MovesT); βmeas charges no mass/height for
  the entering read (MovesT's conditioning). U-7 pins the convention they must satisfy.
- **W-9 (iv)-MEAS full form** — disjoint measurable events over [1v]'s event space
  (LedgerIV carries its nonneg/partition/disjoint-domain shadow, §2.B design note).

## 3b. Load-bearing DAG edges (acyclic)

U-1 → {U-3(via U-2), U-6, U-8, U-16a} · U-2 → {U-3, U-16a} · U-4 → U-5 → U-6 ·
U-6 ⟹ the `hK` argument of every Kmat consumer {U-8, U-16b, U-22, U-24a/b, U-25, U-29} ·
U-8 → U-9a → {U-9b, U-10} · U-11, U-12 → {U-16a, U-18} · U-13 → U-14 → {U-15, U-16b,
U-24b} · U-16a → {U-16b, U-24a} · U-16b → {U-17a, U-25, U-29} · U-19 → {U-9a, U-10,
U-20, U-22} · U-21a, U-21b(←U-23b) → U-21c → {U-22, U-23d} · U-23a/b/c → U-23d ·
U-27 → {U-9b, U-18b, U-22, U-24a, U-28} · U-24a → U-24b · U-22 → hdet of {U-16b, U-24b}.
The CONSUMPTION-DAG discipline (S.1 status line) holds: U-24a/b consume `xrb` and
`recursion_meas`, never a PCI site; nothing proves toward `xrb`.

---

## 4. Trust surface & audit flags (REV 2)

1. **No `True` fields exist.** Grep-check duty at phase E: `grep -n ': True' Defs.lean`
   must return empty. The two round-1 placeholder habits (LedgerIV tags, avAgree) are
   replaced by the §2.B carriers and the `AVAgree` Prop definition.
2. **`xrb` is the corpus's honest XRB interface** (open field; W-2). Flag any future
   claim that MovesS proves XRB.
3. **The interp fields are the rationality trust boundary**: (iv)-POLY/XHD-s (tg_ok/
   tg_interp), (J-RAT) (j_ok/j_interp), INIT-RAT (ι_ok/ι_interp), CL-17(ii) (wsh_ok),
   plus `allActive_infinite` (S.4(ii)'s cofinite-activity face). Auditor: check each
   maps to its S.3 inventory line and none is derivable from the others.
4. **`recursion_meas`/`x3_total`/`rs1_total` are the three measured inputs** the note
   marks GIVEN (S.2's statement line, S.5's route). They are per-pool ℝ-statements —
   NOT the symbolic conclusions (those are U-24a/b, U-28's outputs).
5. **PART-2's marked surplus row has no field** — unconsumable, as rev 6 demands.
6. **ESCAPE-UNIF does not exist in this corpus** (consumed by nothing).
7. **S.7 / probe roster / (CUT-WD)'s own proof / junk-determinant recording** are
   census-side or wave-4 (W-6, W-7); (BDY) is in scope as U-7 + W-8.
8. **`SCSData.memberOf_ne_sel`'s drafting artifact** (the vacuous left disjunct) is
   struck at phase E: the field is `memberOf e τ o i ≠ selIdx e τ o`. Recorded here so
   the elaborated Defs cannot silently weaken it.

## 5. Conventions (phase E / prover fleet) + census

Build per file `lake env lean LeanUrat/MovesS/<file>.lean`; `#print axioms` per unit
(Lean-core only; `sorryAx` flagged). Defs skeleton `sorry`s (`OKat`, `evalAt` bodies,
`kTarget`, `Kmat`, `bTerm`) are elaborated at phase E BEFORE fan-out; `consumedDeltas`/
`evalRe`/`bSplit` live in U-16a. Statement changes to any §2 field = statement-fence
event. Mathlib names as §1 (all verified in the pinned cache).

**Census: 38 units = 12 easy / 25 medium / 1 hard.** Easy {U-1, U-2, U-3, U-5, U-13,
U-18b, U-20, U-21a, U-23a, U-23b, U-23c, U-25}; hard {U-24b (the strong-induction
identification)}; medium the remaining 25. Round-1's three hards are split per R6
(finding 22): 3 → 10 one-display units.

---

## 6. Findings → repairs table (audit `MOVESS_AUDIT_CODEX_2026-07-28.md`, 22 findings)

| # | class | repair | where |
|---|---|---|---|
| 1 | crit | ALL `True` tags deleted; NINE CL-5 items now contentful Props over MeasuredSide carriers; [3t]/[2r]/X.3 tags → measured input fields (`recursion_meas`, `x3_total`, `rs1_total`, `xrb`) + sync entries W-1..W-5 | §2.B, §2.D, §3w |
| 2 | crit | XRB reverted to open hypothesis: `βmeas` height-indexed, `xrb` a displayed field, discharge = W-2 | §2.D, R3 |
| 3 | crit | rationality = `RatBurdens` (Qq data + per-pool interpolation laws, owners named); no bare-Qq table fields; U-15/RS.2 conditional on RB by construction | §2.C, U-15 |
| 4 | crit | `kcolSameSize` field DELETED; (SCS) is the `hK` ARGUMENT produced by U-6 from SCSData + DegCons | §2.C, U-6 |
| 5 | crit | SCSData carries SP.1's member-injection carriers; U-4 derives flank-empty + λ-singleton by pigeonhole | §2.A, U-4 |
| 6 | crit | (BDY) both halves: edge rule + node shadow + mass-split (U-7); consumption duties named at W-8 | U-7, W-8 |
| 7 | crit | `sig_covers` is a real TableShape field; U-8 cites it | §2.A, U-8 |
| 8 | crit | fused `part1` deleted; PART-1 = cell-partition identity over the Cell carrier; TG-vs-J identifications are RatBurdens interp laws; (K-SUB) derived in the chain U-8 → U-9a → U-9b with DegCons/(SCS)/dispatch in the trace | §2.B/C, U-9a/b |
| 9 | crit | `powSubst (δ : ℕ+)`; `Member.δ : ℕ+` | D6, §2.A, U-12 |
| 10 | crit | `bSplit` takes `hdc : DegCons`; βlt application licensed by U-2 inside the definition | U-16a |
| 11 | crit | every block quantifier `e ∈ Finset.Icc 1 n`; no e = 0 anywhere | R5, §3 |
| 12 | crit | (R_e-exact) is unit U-17b over `βfull`/`nsNull`/`rexact`; nsNull discharge = W-5 | §2.D, U-17b |
| 13 | crit | `Shape` is a length-matched record (k/eOf/τOf/δOf/σ0); `shConv` fully defined from B.βfam; Rsh determined | §2.D, U-18 |
| 14 | crit | U-22 restated with the note's package: E0 + (iv)-POLY via `allActive_infinite`/`tg_ok`; no single-pool bespoke input | U-22 |
| 15 | crit | `∀ hβ` malformation gone: `recursion_meas` is per-pool, of B's OWN family; symbolic fixpoint DERIVED (U-24a), identification with blockSolve DERIVED (U-24b) | §2.D, U-24a/b |
| 16 | crit | `shallow_expansion` field deleted; RS.1-SH = pinned sync statement W-1 (no fake wave-2 derivation); its evaluated shadow `rs1_total` feeds only RS.4 | §3w W-1 |
| 17 | crit | `marked_pairing` field deleted; U-25 is the DEFINITION + type fence; identification = W-1m | U-25, W-1m |
| 18 | crit | fused `primewise` deleted; RS.4 takes the note's two named inputs `x3_total` (CL-4/[5]) + `rs1_total` (RS.1's equating) separately + the rationality chain; U-28 = the note's own DERIVED rational-identity step | §2.D, U-28 |
| 19 | crit | inhabitation: per-structure intended-instance notes; `rep_ne`; pool/prime infinitude fields; `consumedDeltas` computed (RegP never vacuous by free Δ); `interp_unique` (U-18b); the `instance_n2` gate (U-29) | R4, §2, U-18b, U-29 |
| 20 | gap | U-10 restated: Act-subtype binders, explicit memberships, OKat witnesses for TG/J evaluations | U-10 |
| 21 | gap | U-20 re-referenced to the S.4(ii) display it serves (INFRA); active-value agreement lives at `AVAgree` | U-20, §2.C |
| 22 | gap | splits: U-16a/16b/17a; U-21a/b/c; U-23a/b/c/d — 10 one-display units replace 3 hidden multi-lemma units | R6, §3 |

STATUS: REV 2 complete, 2026-07-27. All 22 findings repaired (none pushed back; W-1,
W-1m, W-2, W-3, W-4, W-5 are the explicit deferred-to-wave-4 items the audit's R2
guidance licenses). Awaits the single budgeted re-audit.
