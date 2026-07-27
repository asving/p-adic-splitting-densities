# MovesU — Lean blueprint for §U-SQUEEZE (Theorem U, conditional form; 2026-07-28)

*Blueprint-writer deliverable (campaign wave 1, `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md`).
Source of truth: the DUAL-ACCEPTED §U-SQUEEZE rev 7 (`lean/notes/MOVES_2026-07-24.md`,
lines ~12879–13629; Codex passes 8+9 + Fable confirm CLEAN on identical text). TARGET
(master plan §0): Theorem U machine-checked in its CONDITIONAL form — the open kernels as
NAMED HYPOTHESES, never axioms. Upstream objects (MovesS's solve, MovesX's envelope,
MovesD's trees) enter as HYPOTHESIS STRUCTURES: self-contained now, instantiable later.
Protocol L: verbatim names, statements re-bound at use, explicit DAG.*

Discipline: NO new axioms; the statement-fence holds; every structure field is a trust
surface flagged for the Codex semantic audit (§4). `sorry`-free ≠ non-vacuous.

---

## 0. What §U-SQUEEZE is, in one paragraph

The level-N monic coefficient box (p^{nN} classes) is partitioned by the choice-free
canonical-tree verdict into decided-of-type-σ and undecided; (BOX-N) is the exact count
identity. The decided count is bracketed two-sidedly against §S-RESUM's fixed rational
R_σ ∈ ℚ(q): decided_σ(N) ≤ R_σ(p)·p^{nN} (SQ.2 — partial sum of a positive series
dominated by its fixpoint) and decided_σ(N) ≥ (R_σ(p) − env(N))·p^{nN} (SQ.3 — pure
arithmetic from (BOX-N) + SQ.2-at-every-other-τ + RS.4's checksum). env(N) → 0 then
forces ρ_σ(p) = lim decided_σ(N)/p^{nN} = R_σ(p) at every prime p satisfying the named
regularity schema (REG-p). Nothing substantive is unconditional: the note's exactly FOUR
tag-free steps are (BOX-N); SQ.3's bracket arithmetic AS arithmetic; Tonelli's
extended-value existence in [0, ∞]; and the env(N) → 0 ⟹ limit forcing. Everything
density-typed rides the capstone ledger CL-1…CL-19.

## 1. Design decisions (D1–D7)

**D1 — The box is concrete; the verdict is data.** `Box p n N := Fin n → ZMod (p ^ N)`
(the n free coefficients of a monic degree-n polynomial mod p^N; `Nat.card = p^(n*N)`).
A `Census` carries per level N a TOTAL FUNCTION `verdict N : Box p n N → Option σTy`
(`some σ` = decided of type σ, `none` = Undec(N)). This encodes the note's load-bearing
"PARTITION, not mere covering: T_can^τ is a CHOICE-FREE function of f" — totality and
choice-freeness are BUILT IN by the function type, which is exactly what [1] L2 + VP +
ONE-F license upstream. `decided`/`undec`/`env` are then DEFINED from `verdict`, so
(BOX-N) becomes a genuinely tag-free Fintype partition count — the note's tag-free step 1.

**D2 — Tonelli is typed in ℝ≥0∞.** The tree-fiber series (RS.1's positive series) lives
in `ℝ≥0∞`: `seriesSum σ := ∑' T, mass σ T` exists UNCONDITIONALLY (`ENNReal.summable` —
every ℝ≥0∞ family is summable), and every finite partial sum is dominated by the tsum
(`ENNReal.sum_le_tsum`, `ENNReal.tsum_eq_iSup_sum`). This is rev 2's retyped SQ.2 clause
verbatim: existence tag-free; FINITENESS (`seriesSum σ ≠ ⊤`) and IDENTIFICATION with
R_σ(p) are ledger fields (the tagged stack), never Tonelli's.

**D3 — Finiteness of the decided family is DATA-level.** `FiberSeries.thrSlice σ N :
Finset (Tree σ)` — the thr ≤ N slice is Finset-typed, so SQ.0/CL-7's finiteness
(TRACK-COUNT + D(n) + the genuine-increment sub-claim) rides the INSTANTIATION: whoever
builds a `FiberSeries` from MovesD trees must produce the Finset, which is exactly CL-7's
open duty. Flagged in the docstring; no silent strengthening — the abstract corpus never
proves finiteness, it consumes it.

**D4 — (REG-p) is a Prop schema over an entry-list bundle.** `RegData p` carries the pool
set Q(p) (Finset, each pool a power p^δ), the block index, the matrices K_e (so (r1) is a
literal determinant), the DISPLAYED ENTRY LIST E(e) as a `Finset (RatFunc ℚ)` with a
membership field putting every K-entry in it, and the ACT active-value semantics as an
abstract function `act` (upstream CTS-M(ii)). `RegP D : Prop` = (r1) det(I−K_e) defined
and ≠ 0 at every pool ∧ (r2) every entry of E(e) defined at q₀ (reduced denominator
nonvanishing, `RatFunc.denom` — "q₀ is not a pole") AND agreeing with `act`. Per rev 5
(the Fable D-G2 repair): (REG-p) is a SEPARATE named hypothesis — nothing in `RegData`
imports or implies E0/ACT's own statements; they live in ledger docstrings only.

**D5 — Literal evaluation.** `evalℝ S σ p := ((S.R σ).eval (RingHom.id ℚ) (p:ℚ) : ℝ)`
(Mathlib `RatFunc.eval`, junk-valued at poles). The theorem NEVER consumes `evalℝ` except
under `RegP D`, where the ledger's solve-stack field asserts the identification — so the
junk case is never load-bearing. The WILD-p/ACT reading is carried by (r2)'s agreement
clause inside `RegP`, exactly the note's "the two readings coincide, so ρ_σ(p) = R_σ(p)
is well-typed".

**D6 — The capstone ledger is ONE Prop structure; fields = the note's consumption
PACKAGES, docstrings = the CL entries verbatim.** At MovesU's boundary the 19 CL items
are consumed in exactly four operative packages, the note's own (U-n) grouping: the
FINITENESS STACK {CL-7, CL-10} → field `finiteness_stack` (TREE-N's exact fiber count:
decided_σ(N) as the thr ≤ N partial sum); the SOLVE STACK {CL-1, CL-5, CL-6, CL-8, CL-9,
CL-11, CL-13…CL-17, CL-18, CL-19} → field `solve_stack` (under RegP: seriesSum finite
and = R_σ(p)); RS.4's INHERITED SET → fields `rs4_checksum` (the ℚ(q) identity) and
`rs4_eval` (its evaluated form at p, what SQ.3 consumes); X.3/CL-4 QUALITATIVE → field
`cl4_env_tendsto` (env(N) → 0). Distributing one joint consequence over 19 fields would
FALSELY attribute per-item operative content; instead every CL-1…CL-19 number appears
VERBATIM in the docstring of the field that carries it (greppable audit: each of the 19
tags occurs — no tag dropped, per the theorem's own acceptance-record rule). (REG-p) is
NOT a ledger field: it is the ONE explicit hypothesis (rev 3, pass-2 critical 2), a
separate argument of every conditional unit.

**D7 — NO-CLAIM failure semantics = the restricted quantifier, no Lean artifact.** The
theorem's conclusion is `∀ p, p.Prime → ... → RegP D → (...)`. At a p failing (REG-p)
the implication is vacuously satisfied — Lean asserts NOTHING there: no equality, no
bound, no non-existence (the removable-auxiliary-zero case needs no encoding). This is
the note's failure semantics EXACTLY, for free. Design note only; no unit.

**The four TAG-FREE units** (= the note's re-audited unconditional perimeter, and the
only units proved without ledger fields): `U1_boxN`, `U2_tonelli`, `U5_sq3_arith`,
`U7_squeeze`. Everything else consumes hypothesis-structure fields and says so.

---

## 2. Defs skeleton — `lean/LeanUrat/MovesU/Defs.lean` (inline; elaboration-phase target)

```lean
import Mathlib
namespace LeanUrat.MovesU
open Filter Topology ENNReal

/-- The level-N monic coefficient box: n free coefficients mod p^N (p^{nN} classes). -/
abbrev Box (p n N : ℕ) := Fin n → ZMod (p ^ N)

/-- HYPOTHESIS STRUCTURE (instantiated later by MovesD's T_can^τ + MovesX's Undec).
    `verdict N f = some σ`: T_can^τ(f) complete finite realizable, all leaves
    (τ-irr)/(τ-hen), certified at level N, verdict-type multiset σ. `none`: Undec(N).
    TOTALITY + CHOICE-FREENESS are the function type ([1] L2 + VP + ONE-F, D1). -/
structure Census (n p : ℕ) (σTy : Type) [Fintype σTy] where
  verdict : ∀ N : ℕ, Box p n N → Option σTy

variable {n p : ℕ} {σTy : Type} [Fintype σTy]

/-- decided_σ(N), defined from the verdict function (never a field). -/
noncomputable def Census.decided (C : Census n p σTy) (σ : σTy) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // C.verdict N f = some σ}
/-- undec(N) := #Undec(N). -/
noncomputable def Census.undec (C : Census n p σTy) (N : ℕ) : ℕ :=
  Nat.card {f : Box p n N // C.verdict N f = none}
/-- env(N) := undec(N)/p^{nN}, real-valued (the measured envelope). -/
noncomputable def Census.env (C : Census n p σTy) (N : ℕ) : ℝ :=
  (C.undec N : ℝ) / (p : ℝ) ^ (n * N)
/-- The normalized decided mass d_σ(N) := decided_σ(N)/p^{nN}. -/
noncomputable def Census.dmass (C : Census n p σTy) (σ : σTy) (N : ℕ) : ℝ :=
  (C.decided σ N : ℝ) / (p : ℝ) ^ (n * N)

/-- HYPOTHESIS STRUCTURE (MovesS interface): the fixed p-independent rational output.
    R_σ := RS.1-SH's object — "the ONLY density-typed output of the solve" (§S type
    fence: no μ̂-typed marked total appears anywhere in MovesU). -/
structure SolveData (σTy : Type) where
  R : σTy → RatFunc ℚ

/-- Literal evaluation of R_σ at q = p (Mathlib `RatFunc.eval`; junk 0 at poles —
    consumed ONLY under RegP, D5). -/
noncomputable def evalℝ (S : SolveData σTy) (σ : σTy) (p : ℕ) : ℝ :=
  ((S.R σ).eval (RingHom.id ℚ) (p : ℚ) : ℚ)

/-- "The fixed ℚ(q)-element's literal evaluation at q₀ is DEFINED (q₀ not a pole)". -/
def DefinedAt (g : RatFunc ℚ) (q₀ : ℚ) : Prop := g.denom.eval q₀ ≠ 0

/-- HYPOTHESIS STRUCTURE (MovesS/§S S.4 interface): the (REG-p) bundle — the pool set
    Q(p), the blocks, K_e as literal matrices, the DISPLAYED ENTRY LIST E(e) (K, b both
    components incl. per-cell J (CL-18), ι_e, W_Ŝ, every β leg at every pool), and the
    ACT active-value semantics (CTS-M(ii), abstract here). -/
structure RegData (p : ℕ) where
  Pool : Finset ℕ                              -- Q(p), pools q₀ = p^δ
  pool_pow : ∀ q₀ ∈ Pool, ∃ δ ≥ 1, q₀ = p ^ δ
  Block : Type
  instB : Fintype Block
  bidx : Block → Type
  instBi : ∀ e, Fintype (bidx e)
  instBd : ∀ e, DecidableEq (bidx e)
  K : ∀ e : Block, Matrix (bidx e) (bidx e) (RatFunc ℚ)
  entryList : Block → Finset (RatFunc ℚ)       -- E(e), the rev-3 displayed list
  K_mem : ∀ e i j, K e i j ∈ entryList e       -- "{each entry of K_e} ⊆ E(e)"
  act : RatFunc ℚ → ℕ → ℚ                      -- ACT active value at a pool

/-- (REG-p), the rev-5 SEPARATE named hypothesis: (r1) full determinant (junk blocks
    included) defined and ≠ 0 at every pool; (r2) every E(e)-entry defined at q₀ AND
    literal = ACT active value ((ii-c) agreement). Neither implies nor is implied by
    E0/CL-1 or ACT/CL-5 — those never appear here (D4). -/
def RegP {p : ℕ} (D : RegData p) : Prop :=
  ∀ q₀ ∈ D.Pool, ∀ e : D.Block,
    (letI := D.instBi e; letI := D.instBd e;
     DefinedAt (Matrix.det (1 - D.K e)) (q₀ : ℚ) ∧
     (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0) ∧
    ∀ g ∈ D.entryList e,
      DefinedAt g (q₀ : ℚ) ∧ g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀

/-- HYPOTHESIS STRUCTURE (MovesD/[3t] interface): the tree-fiber series for type σ.
    `thrSlice σ N` = the thr(T) ≤ N slice; ITS FINSET TYPE IS CL-7's finiteness riding
    the instantiation (D3 — TRACK-COUNT + D(n) + genuine-increment, OPEN upstream). -/
structure FiberSeries (n p : ℕ) (σTy : Type) [Fintype σTy] (C : Census n p σTy) where
  Tree : σTy → Type
  mass : ∀ σ, Tree σ → ℝ≥0∞                     -- μ(fiber T): RS.1's positive series
  thrSlice : ∀ σ : σTy, ℕ → Finset (Tree σ)
  slice_mono : ∀ σ, Monotone (thrSlice σ)

/-- The extended-value sum of the σ tree-fiber series — EXISTS unconditionally in
    [0,∞] (Tonelli retype, rev 2): `ENNReal.summable`. -/
noncomputable def FiberSeries.seriesSum {C : Census n p σTy}
    (F : FiberSeries n p σTy C) (σ : σTy) : ℝ≥0∞ := ∑' T : F.Tree σ, F.mass σ T

end LeanUrat.MovesU
```

## 2b. The capstone ledger structure (Defs, continued) — THE trust surface

```lean
/-- THE CAPSTONE LEDGER as ONE hypothesis structure (SQ.4's CL-1…CL-19, REV 16 extent).
    Fields = the note's four consumption packages (D6); every CL tag appears verbatim
    below — "neither this display nor any acceptance record may drop a tag while any
    cited CL-item is open". (REG-p) is NOT a field: the ONE explicit hypothesis. -/
structure CapstoneLedger (n p : ℕ) (σTy : Type) [Fintype σTy]
    (C : Census n p σTy) (F : FiberSeries n p σTy C)
    (S : SolveData σTy) (D : RegData p) : Prop where
  /-- FINITENESS STACK — CL-7 (TRACK-COUNT + L(n), D(n), the positive
      genuine-increment sub-claim: "without them no finite decided family") and CL-10
      (the [3t] TREE-ASSEMBLY package: (SIB)/(SIB-STEP), TREE-EXP(-fin/-ns) + TREE-N
      (NS-ROUTE)-scoped, VP with TB-CAP per clause, (ns-null) closed, VP-SOUND:
      "without CL-10 the solve computes marked-branch totals, not densities").
      Operative form = TREE-N's exact count summed over the thr ≤ N slice:
      decided_σ(N) = p^{nN} · Σ_{thr(T)≤N} μ(fiber T). -/
  finiteness_stack : ∀ σ N,
    (C.decided σ N : ℝ≥0∞) =
      (p : ℝ≥0∞) ^ (n * N) * ∑ T ∈ F.thrSlice σ N, F.mass σ T
  /-- SOLVE STACK — CL-1 (ESCAPE(E0), per-pool active-block solvability), CL-5 (the
      NINE RS.PRE inputs: XHD; D4R.0; (iv)-PART/-REP/-MEAS; (v) HMC; (ii) ACT; (iii)
      INIT + ENT-COUNT; (vi) COMP-typing), CL-6 ((iv)-POLY — without it R_σ ∈ ℚ(q) is
      unfounded), CL-8 (REL.1 + REL.2(a)(b)(d)(e) + REL.3 — every β(q^δ) leg), CL-9
      (RS.0 lumpability + height-shift bisimulation = XRB's prover), CL-11
      (no-equal-e-feedback + DEG-CONS), CL-13 (CTS-M(i) SYNTAX), CL-14 ([2a] M1+M5),
      CL-15 (X.1a dictionary), CL-16 (M4b/M4b-T), CL-17 (RS.1-SH: routing + unique
      shallow-cut + W_Ŝ regrouping), CL-18 ((J-RAT) per-cell tables), CL-19 ((JC-INV)).
      Operative form: UNDER (REG-p), the extended-value sum is finite and IS the
      literal R_σ(p) — the identification/finiteness that Tonelli never gives. -/
  solve_stack : RegP D → ∀ σ,
    F.seriesSum σ ≠ ⊤ ∧ F.seriesSum σ = ENNReal.ofReal (evalℝ S σ p)
  /-- RS.4's checksum (§S S.5) WITH its full inherited set riding verbatim: "E0, the
      CL-5 nine, RS.1's set, X.3/CL-4, and the whole RS.2 rationality chain incl.
      (J-RAT)/CL-18". The ℚ(q) identity — Theorem U's second conjunct. -/
  rs4_checksum : ∑ σ, S.R σ = 1
  /-- RS.4 EVALUATED at p under (REG-p) — the form SQ.3's arithmetic consumes. Same
      inherited set. (E-phase note: derivable from `rs4_checksum` + (r2)-definedness
      via RatFunc eval-hom side conditions; carried as a field until that unit lands.) -/
  rs4_eval : RegP D → ∑ σ, evalℝ S σ p = 1
  /-- CL-4 = X.3 termination a.e. (QUALITATIVE form — "the limit consumes no envelope
      constant"; discharges only at [5]'s EVENT): env(N) → 0. The quantitative
      (X2-*) envelope family (CL-2, CL-3) is NOT consumed by the limit and has no
      field — the rate form is out of MovesU's scope (gate SQUEEZE-n3 is a census
      artifact, not a Lean unit). -/
  cl4_env_tendsto : Tendsto C.env atTop (𝓝 0)
```

Greppable audit: CL-1 … CL-19 all appear above (CL-2/CL-3 in the `cl4_env_tendsto`
docstring as explicitly NOT consumed by the qualitative limit — the note's own scoping;
CL-12, perimeter conditionality, is CLOSED per SQ.4's ledger — "NOTHING at CL-12 is
open" — so it is correctly ABSENT as a hypothesis; its O3 base-pin display duty is a
write-up sentence, out of Lean scope).

---

## 3. The unit DAG — 11 units, one file each: `lean/LeanUrat/MovesU/<id>.lean`

Layers: L0 Defs+counting (U0–U1) → L1 series (U2–U4) → L2 bracket (U5–U6) →
L3 limit (U7) → L4 schema/aux (U8–U9) → L5 capstone (U10). TAG-FREE = proved with no
ledger/structure hypothesis fields beyond definitions.

### U0 `MovesU.U0_boxCard` — the box cardinality  [support, tag-free]
- **file**: `MovesU/U0_boxCard.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement**: `theorem boxCard (p n N : ℕ) [NeZero p] : Nat.card (Box p n N) = p ^ (n * N)`
- **moves_ref**: "the monic degree-n coefficient box mod p^N (p^{nN} residue classes)"
- **sketch**: `Nat.card (Fin n → ZMod (p^N)) = (p^N)^n = p^(n*N)`; `Nat.card_fun`/
  `Nat.card_eq_fintype_card`, `ZMod.card` (needs `NeZero (p^N)` from `NeZero p`), `pow_mul` (commuted).
- **hypothesis_fields**: none.

### U1 `MovesU.U1_boxN` — (BOX-N), the count identity  [TAG-FREE step 1]
- **file**: `MovesU/U1_boxN.lean`  ·  **difficulty**: medium  ·  **deps**: U0
- **statement**: `theorem boxN (C : Census n p σTy) [NeZero p] (N : ℕ) :`
  `(∑ σ : σTy, C.decided σ N) + C.undec N = p ^ (n * N)`
- **moves_ref**: "(BOX-N) p^{nN} = Σ_τ decided_τ(N) + undec(N) — the box partition,
  EXACT and tag-free as an identity of counts"
- **sketch**: partition the Fintype `Box p n N` by the value of `verdict N` in
  `Option σTy`: `Finset.card_eq_sum_card_fiberwise` (Mathlib
  `Algebra/BigOperators/Group/Finset/Basic.lean`) over `t := Finset.univ : Finset (Option σTy)`;
  fibers of `some σ` are `decided`, fiber of `none` is `undec`
  (`Nat.card_eq_fintype_card` + subtype/filter card transfer); close with U0.
- **hypothesis_fields**: none — genuinely tag-free per the note; totality is D1's
  function type (the upstream ONE-F duty, flagged §4).

### U2 `MovesU.U2_tonelli` — extended-value existence + partial-sum domination  [TAG-FREE step 3]
- **file**: `MovesU/U2_tonelli.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement**: `theorem tonelli_partial_le {C : Census n p σTy}`
  `(F : FiberSeries n p σTy C) (σ : σTy) (N : ℕ) :`
  `∑ T ∈ F.thrSlice σ N, F.mass σ T ≤ F.seriesSum σ`
- **moves_ref**: "the positive series has a well-defined EXTENDED-VALUE sum in [0, ∞]
  unconditionally (nonnegative terms) … FINITENESS … and IDENTIFICATION … are NOT
  Tonelli's" (rev 2, pass-1 critical 7)
- **sketch**: `ENNReal.sum_le_tsum` (`Topology/Algebra/InfiniteSum/ENNReal.lean`);
  existence is the totality of `∑'` in ℝ≥0∞ (`ENNReal.summable`,
  `ENNReal.tsum_eq_iSup_sum` — cite in a doc comment; no separate lemma needed).
- **hypothesis_fields**: none (the FiberSeries DATA is used, no Prop field).

### U3 `MovesU.U3_sq2_partial` — decided mass is a dominated partial sum  [conditional]
- **file**: `MovesU/U3_sq2_partial.lean`  ·  **difficulty**: easy  ·  **deps**: U2
- **statement**: `theorem sq2_partial (L : CapstoneLedger n p σTy C F S D) (σ N) :`
  `(C.decided σ N : ℝ≥0∞) ≤ (p : ℝ≥0∞) ^ (n * N) * F.seriesSum σ`
- **moves_ref**: "decided_σ(N)/p^{nN} is a PARTIAL SUM (the thr ≤ N slice) of RS.1's
  positive tree-fiber series for type σ" (SQ.2 ROUTE)
- **sketch**: rewrite by `L.finiteness_stack`, apply U2 + `mul_le_mul_left'`.
- **hypothesis_fields**: `finiteness_stack` (CL-7 + CL-10).

### U4 `MovesU.U4_sq2_upper` — SQ.2, the fixpoint upper bound  [conditional]
- **file**: `MovesU/U4_sq2_upper.lean`  ·  **difficulty**: medium  ·  **deps**: U3
- **statement**: `theorem sq2_upper (L : CapstoneLedger n p σTy C F S D)`
  `(hreg : RegP D) (hp : 1 < p) (σ N) :`
  `(C.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)`
- **moves_ref**: "decided_σ(N) ≤ R_σ(p)·p^{nN} [hypothesis stack at (U-n) below]" (SQ.2);
  "with RS.3's positivity … R_σ(p) ≥ 0 stated EXPLICITLY — both GIVEN E0 + the CL-5 mass
  identification"
- **sketch**: from U3 and `L.solve_stack hreg σ` (finite, = `ofReal (evalℝ)`), transfer
  ℝ≥0∞ → ℝ: `ENNReal.toReal_le_toReal` (LHS ≠ ⊤ since RHS finite), `ENNReal.toReal_mul`,
  `ENNReal.toReal_ofReal` (needs `0 ≤ evalℝ` — extract from `ofReal`-form: if
  `evalℝ < 0` then `ofReal = 0`, forcing the sum = 0, bound trivial by case split;
  RS.3's positivity is thereby CONSUMED through the field, never re-derived).
- **hypothesis_fields**: `finiteness_stack`, `solve_stack` (the full solve stack:
  CL-1, CL-5, CL-6, CL-8, CL-9, CL-11, CL-13…CL-19); explicit `RegP D`.

### U5 `MovesU.U5_sq3_arith` — SQ.3's bracket arithmetic AS arithmetic  [TAG-FREE step 2]
- **file**: `MovesU/U5_sq3_arith.lean`  ·  **difficulty**: medium  ·  **deps**: U1
- **statement** (every tagged input an EXPLICIT argument — the tag-free content is the
  implication): `theorem sq3_arith (C : Census n p σTy) [NeZero p] (hp : 1 < p)`
  `(R : σTy → ℝ) (σ : σTy) (N : ℕ)`
  `(hupper : ∀ τ, τ ≠ σ → (C.decided τ N : ℝ) ≤ R τ * (p : ℝ) ^ (n * N))`
  `(hsum : ∑ τ, R τ = 1) :`
  `(R σ - C.env N) * (p : ℝ) ^ (n * N) ≤ (C.decided σ N : ℝ)`
- **moves_ref**: "decided_σ(N) = p^{nN} − Σ_{τ≠σ} decided_τ(N) − undec(N) ≥
  p^{nN}·(1 − Σ_{τ≠σ} R_τ(p) − env(N)) = (R_σ(p) − env(N))·p^{nN}" (SQ.3)
- **sketch**: cast U1's (BOX-N) to ℝ; `Finset.sum_erase_add`/`sub` bookkeeping;
  `env` unfolds to `undec/p^{nN}` with `div_mul_cancel₀` (`p^{nN} ≠ 0` from `hp`);
  finish by `linarith` over the τ ≠ σ sum of `hupper` + `hsum`. Pure ℝ arithmetic:
  no ledger, no RegP — the inputs carry the tags, as the note's re-audit says.
- **hypothesis_fields**: none (tag-free as an implication; instantiated at U6 with
  tagged inputs).

### U6 `MovesU.U6_un_bracket` — (U-n), the two-sided bracket  [conditional; the note's product]
- **file**: `MovesU/U6_un_bracket.lean`  ·  **difficulty**: easy  ·  **deps**: U4, U5
- **statement**: `theorem un_bracket (L : CapstoneLedger n p σTy C F S D)`
  `(hreg : RegP D) [NeZero p] (hp : 1 < p) (σ N) :`
  `(evalℝ S σ p - C.env N) * (p : ℝ) ^ (n * N) ≤ (C.decided σ N : ℝ) ∧`
  `(C.decided σ N : ℝ) ≤ evalℝ S σ p * (p : ℝ) ^ (n * N)`
- **moves_ref**: "(U-n) (R_σ(p) − env(N))·p^{nN} ≤ decided_σ(N) ≤ R_σ(p)·p^{nN}" — "for
  every n, σ, N, and EVERY prime p satisfying (REG-p) … at a p failing (REG-p) neither
  inequality is asserted" (the rev-3 qualifier = the `hreg` argument, D7)
- **sketch**: right leg = U4; left leg = U5 applied with `R := fun τ => evalℝ S τ p`,
  `hupper` from U4 at each τ ≠ σ, `hsum := L.rs4_eval hreg`.
- **hypothesis_fields**: `finiteness_stack`, `solve_stack`, `rs4_eval` (RS.4's full
  inherited set incl. X.3/CL-4); explicit `RegP D`.

### U7 `MovesU.U7_squeeze` — the limit forcing  [TAG-FREE step 4]
- **file**: `MovesU/U7_squeeze.lean`  ·  **difficulty**: medium  ·  **deps**: Defs
- **statement** (bracket + env-limit as EXPLICIT arguments): `theorem squeeze_limit`
  `(C : Census n p σTy) (hp : 1 < p) (r : ℝ) (σ : σTy)`
  `(hbr : ∀ N, (r - C.env N) * (p:ℝ)^(n*N) ≤ (C.decided σ N : ℝ) ∧`
  `           (C.decided σ N : ℝ) ≤ r * (p:ℝ)^(n*N))`
  `(henv : Tendsto C.env atTop (𝓝 0)) :`
  `Tendsto (C.dmass σ) atTop (𝓝 r)`
- **moves_ref**: "With env(N) → 0 (X.3/CL-4, the QUALITATIVE form …):
  ρ_σ(p) := lim_{N→∞} decided_σ(N)/p^{nN} EXISTS and = R_σ(p)"
- **sketch**: divide `hbr` by `p^{nN} > 0` (`div_le_div_of_nonneg_right` forms) to get
  `r − env N ≤ dmass σ N ≤ r`; squeeze with Mathlib's
  `tendsto_of_tendsto_of_tendsto_of_le_of_le` (`Topology/Order/Basic.lean`; the `'`
  eventually-variant if convenient); lower leg `r − env N → r − 0 = r` by
  `Filter.Tendsto.const_sub` (`Topology/Algebra/Group/Basic.lean`, the `to_additive`
  of `Tendsto.const_div'`) + `sub_zero`; upper leg `tendsto_const_nhds`.
- **hypothesis_fields**: none (tag-free forcing; the tagged bracket/limit enter as
  arguments, instantiated at U10 from U6 + `cl4_env_tendsto`).

### U8 `MovesU.U8_regP_access` — (REG-p) accessor lemmas  [definitional]
- **file**: `MovesU/U8_regP_access.lean`  ·  **difficulty**: easy  ·  **deps**: Defs
- **statement** (two lemmas): `theorem RegP.K_entry_agree {D : RegData p} (h : RegP D)`
  `(hq : q₀ ∈ D.Pool) (e i j) : DefinedAt (D.K e i j) q₀ ∧`
  `(D.K e i j).eval (RingHom.id ℚ) q₀ = D.act (D.K e i j) q₀` — via `D.K_mem`; and
  `theorem RegP.det_ne_zero {D : RegData p} (h : RegP D) (hq : q₀ ∈ D.Pool) (e) :`
  `(Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) q₀ ≠ 0`
- **moves_ref**: "(r1) det(I − K_e(q₀)) ≠ 0; and (r2) for EVERY member of the DISPLAYED
  ENTRY LIST E(e) … the literal evaluation at q₀ is DEFINED … AND AGREES with its ACT
  active value" (SQ.4's rev-3 schema)
- **sketch**: unfold `RegP`; direct projection. These are the API the MovesS
  instantiation will consume; no content beyond the schema.
- **hypothesis_fields**: explicit `RegP D` only.

### U9 `MovesU.U9_lmeas` — (L-meas)'s retype: equivalence + IMPLIED-BY  [conditional on `rs4_eval` only]
- **file**: `MovesU/U9_lmeas.lean`  ·  **difficulty**: medium  ·  **deps**: U1, U4
- **statement** (two lemmas, fixed σ, N; abbrev `d τ := C.dmass τ N`):
  `theorem lmeas_equiv [NeZero p] (hp : 1 < p) (hsum : ∑ τ, R τ = 1) :`
  `((R σ - C.env N) * (p:ℝ)^(n*N) ≤ (C.decided σ N : ℝ)) ↔`
  `(∑ τ ∈ Finset.univ.erase σ, C.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ)` — and
  `theorem lmeas_implied (hupper : ∀ τ, τ ≠ σ → C.dmass τ N ≤ R τ) :`
  `∑ τ ∈ Finset.univ.erase σ, C.dmass τ N ≤ ∑ τ ∈ Finset.univ.erase σ, R τ`
- **moves_ref**: "(L-meas) … by (BOX-N), for fixed σ this leg is EQUIVALENT to the
  AGGREGATE inequality Σ_{τ≠σ} d_τ ≤ Σ_{τ≠σ} R_τ(p) … It is IMPLIED BY — not
  equivalent to — the conjunction {SQ.2 at every τ ≠ σ} + RS.4's checksum" (rev 2,
  pass-1 critical 5)
- **sketch**: `lmeas_equiv`: divide U1 by `p^{nN}` and rearrange (`Finset.add_sum_erase`,
  `hsum`); `lmeas_implied`: `Finset.sum_le_sum` — ONE direction only, faithfully: no
  converse is stated anywhere (per-τ violations can cancel; the note's honesty).
- **hypothesis_fields**: none as stated (R : σTy → ℝ abstract with `hsum` explicit);
  at consumption `R := evalℝ`, `hsum := rs4_eval` — the gate-layer reading, recorded
  for SQUEEZE-n3's (L-meas) leg semantics only (the gate itself is NOT a Lean unit).

### U10 `MovesU.U10_theoremU` — THEOREM U, the ONE structure-carrying theorem  [capstone]
- **file**: `MovesU/U10_theoremU.lean`  ·  **difficulty**: medium  ·  **deps**: U6, U7
- **statement** (verbatim target; the campaign's statement-of-record):
```lean
/-- THEOREM U (CONDITIONAL — on the COMPLETE capstone ledger, a `CapstoneLedger`
    hypothesis; SQ.4). For each splitting type σ there is ONE fixed R_σ ∈ ℚ(q) (the
    `SolveData`, p-independent BY TYPE) with: at EVERY prime p satisfying (REG-p),
    ρ_σ(p) := lim_N decided_σ(N)/p^{nN} exists and equals the literal R_σ(p); and
    Σ_σ R_σ = 1 identically in ℚ(q). At a p failing (REG-p): NO CLAIM (D7 — the
    implication is simply not applicable; no equality, bound, or non-existence). -/
theorem theoremU (n : ℕ) (hn : 2 ≤ n) (σTy : Type) [Fintype σTy]
    (S : SolveData σTy) :
    ∀ (p : ℕ) (hp : p.Prime) (C : Census n p σTy) (F : FiberSeries n p σTy C)
      (D : RegData p) (L : CapstoneLedger n p σTy C F S D),
      RegP D →
        (∀ σ : σTy, Tendsto (C.dmass σ) atTop (𝓝 (evalℝ S σ p)))
        ∧ ∑ σ, S.R σ = 1
```
- **moves_ref**: "there is ONE fixed rational function R_σ ∈ ℚ(q) … such that for EVERY
  prime p, WILD primes included: ρ_σ(p) … exists and equals R_σ(p) … Σ_σ R_σ = 1
  identically in q (RS.4). … The quantifier 'for EVERY prime p' reads: every p
  satisfying (REG-p)." (SQ.4 = THEOREM U)
- **sketch**: first conjunct: U7 applied with `r := evalℝ S σ p`, bracket from U6
  (needs `1 < p` from `hp.one_lt`, `NeZero p` from `hp.pos`), env-limit from
  `L.cl4_env_tendsto`; second conjunct: `L.rs4_checksum`. ≤ 15 lines expected.
- **hypothesis_fields**: ALL FIVE ledger fields + explicit `RegP D` — the complete
  conditionality, nothing else. The "ρ_σ(p) IS the splitting density" clause and the
  wild-p ACT reading are instantiation semantics (§4 flags F2/F5), not extra fields.

---

## 4. Semantic-guardian flags (the trust surface, for the Codex audit)

- **F1 `Census.verdict`**: the abstract σTy/verdict makes "decided of type σ" a LABEL.
  The note's clause "the classifier verdicts are the true factorization types" is NOT
  stated here — it is the MovesD/OM instantiation's faithfulness duty (X.3/CL-4 +
  [3t] VP + VP-SOUND). Never describe U10 as certifying true splitting densities;
  it certifies the squeeze over the interface.
- **F2 `evalℝ` junk values**: Mathlib `RatFunc.eval` returns 0 at poles. Audit that no
  unit consumes `evalℝ` outside a `RegP`-guarded context except as the LIMIT TARGET in
  U10, where `solve_stack`/`rs4_eval` (both RegP-guarded) give it content.
- **F3 `FiberSeries.thrSlice : Finset`**: finiteness-as-data = CL-7 riding the
  instantiation (D3). Audit the docstring keeps TRACK-COUNT + D(n) + genuine-increment
  named OPEN.
- **F4 Ledger docstrings**: grep-check every one of CL-1 … CL-19 appears verbatim in
  `CapstoneLedger`'s docstrings (D6's no-tag-dropped rule); check no field silently
  strengthens (e.g. `solve_stack` must NOT assert `0 ≤ evalℝ` separately — positivity
  is consumed via the `ofReal` form only).
- **F5 `RegData.act` abstract**: (r2)'s ACT agreement is against an UNINTERPRETED
  `act`; the CTS-M(ii) semantics arrive at instantiation. (REG-p) stays the rev-5
  SEPARATE hypothesis — audit that no unit derives RegP from, or uses it to derive,
  any E0/ACT-shaped statement.
- **F6 statement-fence**: U5/U7 take their tagged inputs as EXPLICIT arguments; audit
  that this matches the note's "tag-free AS arithmetic / AS forcing" scoping and that
  U6/U10 re-supply those arguments ONLY from ledger fields + RegP.

## 5. Verified Mathlib inventory (names checked against the pinned mathlib, 2026-07-28)

- `tendsto_of_tendsto_of_tendsto_of_le_of_le`, `...'` — `Mathlib/Topology/Order/Basic.lean` (the squeeze, U7).
- `Filter.Tendsto.const_sub` — `to_additive` of `Filter.Tendsto.const_div'`,
  `Mathlib/Topology/Algebra/Group/Basic.lean` (U7's lower leg); `tendsto_const_nhds`, `sub_zero`.
- `ENNReal.summable` (every ℝ≥0∞ family), `ENNReal.tsum_eq_iSup_sum`,
  `ENNReal.sum_le_tsum` — `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` (U2).
- `ENNReal.toReal_le_toReal`, `ENNReal.toReal_mul`, `ENNReal.toReal_ofReal`,
  `ENNReal.summable_toReal` — same area (U4's transfer).
- `RatFunc.eval` — `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean`; `RatFunc.denom`,
  `RatFunc.denom_ne_zero` — `RatFunc/Basic.lean` (D5, `DefinedAt`).
- `Finset.card_eq_sum_card_fiberwise` — `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` (U1).
- `ZMod.card`, `Nat.card_eq_fintype_card`, `pow_mul` (U0); `Finset.add_sum_erase`/
  `Finset.sum_erase_add`, `Finset.sum_le_sum`, `div_mul_cancel₀` (U5/U9).
- E-phase check (flagged, not assumed): eval-additivity side-condition lemmas for
  deriving `rs4_eval` from `rs4_checksum` (`RatFunc.eval_add`'s hypotheses) — if absent
  or awkward, `rs4_eval` stays a field (already the blueprint default).

## 6. Status and counts

11 units (U0–U10): 4 TAG-FREE/unconditional (U1 (BOX-N), U2 Tonelli existence,
U5 SQ.3-as-arithmetic, U7 limit forcing — exactly the note's re-audited tag-free
perimeter) + U0 support + 6 conditional/definitional, every hypothesis a named
structure field or explicit `RegP`. Difficulty: 6 easy, 5 medium, 0 hard. No new
axiom anywhere; no `sorry` planned (conditional content = hypothesis structures).
Consumes NO existing Moves/MovesC module (self-contained per the master plan;
instantiation hooks: `Census` ← MovesD T_can + MovesX Undec, `SolveData`/`RegData`
← MovesS, `FiberSeries` ← MovesD/[3t]). Next gate: Codex semantic audit (§3 B→A),
charge = §4's flags + the master plan's faithfulness bar.

