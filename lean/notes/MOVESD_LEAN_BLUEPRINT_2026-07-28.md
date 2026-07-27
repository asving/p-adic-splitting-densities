# MOVESD LEAN BLUEPRINT (2026-07-28) — §D4-R, the per-shape-prefix mass law

Campaign unit-spec per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §2. Writer: Fable.

## 0. Source and ground truth

SOURCE: `lean/notes/MOVES_2026-07-24.md`, `## §D4-R — the per-shape-prefix mass law`
(lines ~4580–5432), **rev 9**, DUAL-ACCEPTED 2026-07-27 (Codex pass 11 + Fable confirm,
both CLEAN on identical rev-9 text — the acceptance record at the §D4-R DUAL-ACCEPTED
block). KERNEL STATUS (same record): D4R.0-K parts **(a)** L1 canonical-choice totality
and **(b)** L5 digit-cell structural exhaustiveness are **DISCHARGED** by the
dual-verified derivation `D4R0K_DERIVATION_2026-07-26.md` (rev 3; Codex pass 3 SOUND +
Fable CLEAN). The residual is **(c) — the verdict pin VP** (alphabet V + halting rule τ +
the uniform per-class detection cap), OPEN, owned by §T-ASSEMBLY ([3t]) → MovesT.
§D4-R's remaining conditionality: dual-accepted §C (rev 14) + dual-accepted §B2-DEF
(D¹¹d) + the (c)/VP residual.

TARGET DISPLAYS (the note's headline, encoded by this corpus):
  Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)}          (D4R.1-SUM)
  μ(P̂) := μ(⋃_η S(η,⊤)) ≤ C_P̂(p)·p^{−A(P̂)}, = iff mult ≡ 1  (D4R.1-EV)
  C_P̂(p) ≤ M(P̂)·p^{W(P̂)},  M(P̂) = ∏_r m̄_r p-free          (D4R.2′ / L11)
  Σ_η #{f mod p^N ∈ S(η,⊤)} = C_P̂(p)·p^{nN−A(P̂)}, N ≥ N(P̂) (D4R.4-SUM/EV)

## 1. The MovesC-consumption design (CONSUME, do not re-model)

MovesC (36/36 PROVED) supplies, and MovesD imports verbatim:
- `History p F` / `Node p F` — a realized lift-carrying prefix η IS a MovesC `History`
  (§D4-R L3: "A realized prefix IS a lift-carrying history in §C's sense"). No new
  history type. Node's rev-9 retained fields already exist: `ustar` (u*_r, ROUND 4
  finding 11), `gam` (γ_r), `s0/wSide/Dwidth/e/h/g/μ/a/species`.
- `JetSetup H n N m` — the presented history (the finite-level box, `hm : m = n*N`).
- `JetSetup.SHZ Z` — S(η, Z); at Z = ⊤ this is S(η,⊤), the D4R fiber.
- `C6_thmC_b : Nat.card (J.SHZ Z) * p ^ totalPins J Z = boxMass p m` — Theorem C(b),
  each D4R.1 summand. MovesD specializes it at the trivial locus `topLocus`
  (vol(⊤) = 1: `numPinned = 0`, `AdmissibleZ` vacuous) — unit D0b.
- `totalPins J ⊤ = Σ_{i<len} (J.fresh i).mstar` — the per-history ledger exponent;
  `J.mstar_eq` pins each summand to the fresh-band count from NODE data, which is what
  makes L9 (shape-constancy of A) PROVABLE here rather than hypothesized.
- `HistoryCoherent`, `Realizable` ((NA)+(HV)+(SAE)), `CoordPrec`, `Locus`, `DigitSystem`.

NEW OBJECTS (classifier content beyond MovesC's interface — modeled as structures with
the JetSetup-instance connection as HYPOTHESIS fields; the HC-2 bridge discharges them):
- `ShapePrefix` P̂ — the L3 dictionary as data (retained fields incl. (h_r, u*_r), the
  slot sets, the pool degree w_r), + shape functions W, M, m̄_r, ℓ_r.
- `PrefFamily` — the finite enumeration modeling Pref(P̂): index type, `hist`,
  per-member `jet : JetSetup (hist i) n N m` (HC-2 data), the L11 encoding `enc` with
  `henc : Injective enc` (hypothesis; the note's L11 proof is its math discharge).
- `TreeModel` — T_can(f) as a choice-free membership predicate with L2 prefix-closure
  and L6's (D4R-CYL) as fields; `VerdictModel` — the leaf layer, (c)/VP, statements only.

FINITE-LEVEL POLICY (house style): every statement is a `Nat.card` count over the
level-N box `Box p m := Fin m → ZMod p`, division-free (`count * p^A = C * p^(nN)`).
D4R.1 (the μ-form) and D4R.4 (the level-N form) COINCIDE in this model: μ is defined in
the note as the normalized level-N count at any N ≥ N(P̂) (§D4-R "Ledger data"), and the
family fixes ONE (n, N, m) — L12's max N(P̂) := max_η N(η,⊤) is absorbed into the
EXISTENCE of the jets at a common N (bridge-side; L8's finiteness makes the max exist).
The note's a.e.-vs-pointwise upgrade (positive-mass cylinder overlaps) COLLAPSES at
finite level: every nonempty set has positive card, so the mult ≡ 1 criterion is pure
counting — no measure theory anywhere.

## 2. Hypothesis-field ledger (never silently strengthened or dropped)

| field | encodes | status |
|---|---|---|
| `PrefFamily.jet` | η is §C-presented at level N (JetSetup existence, N ≥ N(η,⊤)) | HC-2 bridge (campaign phase 3) |
| `PrefFamily.henc` | L11 enc′ injectivity (digits + selection indices determine η) | note-DISCHARGED (L11 proof, rev 9, conditional on kernel (a) L1 — (a) dual-verified-discharged); Lean discharge = HC-2 |
| `PrefFamily.hist_inj` | Pref is a SET of distinct chains | bridge (enumeration duty) |
| `TreeModel.prefix_closed` | L2: T_can(f) is a tree | note-DISCHARGED (L2, choice-free by rev-6 architecture); Lean discharge = HC-2 |
| `TreeModel.cyl` | L6 (D4R-CYL): S(η,⊤) = {f : η ∈ T_can(f)} | note-DISCHARGED given kernel (a)+(b) — both DISCHARGED by `D4R0K_DERIVATION_2026-07-26.md` rev 3 (dual-verified) — + Thm C(a); Lean discharge = HC-2 |
| `VerdictModel` (whole) | leaf/verdict layer semantics | **OPEN** — D4R.0-K(c)/VP, owned by §T-ASSEMBLY → MovesT |
| `D10.hA` (theorem hyp) | A(P̂) = the common ledger exponent | DISCHARGED IN-CORPUS for nonempty idx by unit D9 (L9 chain) |

NOT modeled (recorded perimeter, §5): the canonical (S6b) offset-P lift policy (enters
only through L1/L6, already hypothesis-level); L7 complete-history identification
("bookkeeping for downstream notes; the mass law consumes L6 only" — the note);
completeness of the enumeration ("Pref(P̂) is ALL realizable canonical prefixes" —
bridge duty); everything on §D4-R.5's deferred list ([1v] polynomiality in p, [2a]/[2b]
catalogue, [3]/[5] resummation/exhaustion; the shape events are a multiplicity-weighted
COVER, never a partition — Σ_P̂ μ(P̂) may exceed 1).

## 3. Defs skeleton — `lean/LeanUrat/MovesD/Defs.lean` (definitions only, no theorems)

```lean
import Mathlib
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

/-- The level-N coefficient box in frame-0 digit coordinates (m = n·N base digits). -/
abbrev Box (p m : ℕ) : Type := Fin m → ZMod p

/-- **Z = ⊤** (§C plan §2 / §D4-R header: "the tautological terminal system (Z = ⊤: no
constraint, vol(⊤) = 1)"): the locus with NO pinned coordinate. `IsSolution` is vacuous. -/
def topLocus (p m : ℕ) : Locus p m := { pinned := fun _ => false, solve := fun _ _ => 0 }

/-- **One read of a shape-prefix** — §D4-R L3's retained fields, rev 9 EXACTLY: species,
(e,h,g,μ,a), side endpoints/raw width (s0, wSide), frame width, the stride-position/slot
set (hence d_r), anchor a, AND the height pair: h (slope numerator) and the SIDE HEIGHT
u*_r (rev 9, pass-10 F1 CRITICAL: u* is retained P̂ DATA, not recovered — at a
non-adjacent e=1 read the stride rule is γ-blind). `gam` = γ_r (§C's derived list); `w` =
the pool residue degree (pool size Q_r = p^w). Digit VALUES and lifts are forgotten. -/
structure ShapeRead where
  species : ReadSpecies
  e h g μ : ℕ
  a : ℤ
  s0 wSide Dwidth : ℕ
  ustar : ℚ
  gam : ℤ
  w : ℕ
  slots : Finset ℕ
  he : 1 ≤ e
  hg : 1 ≤ g
  hμ : 1 ≤ μ

/-- The digit count d_r := |slot set| (L3: "the stride-position/slot sets p_j (hence the
digit count d_r)"; W consumes d_r, NOT u* — rev 9). At the root the monic-lead slot is
excluded (the pinned instance: d₀ = 3 on span [0,3]). -/
def ShapeRead.d (R : ShapeRead) : ℕ := R.slots.card

/-- ℓ_r := w'_r/e_r, the NORMALIZED side length = deg R_anch,r (L11 rev 3: §C DOM
width-confinement "the residual factor, of degree w'/e"). Nat division: shape data has
`e ∣ wSide` in genuine instances; ⌊·⌋ only weakens m̄. -/
def ShapeRead.len (R : ShapeRead) : ℕ := R.wSide / R.e

/-- m̄_r := ⌊ℓ_r/(g_r·μ_r)⌋ — L11's SHARPER residual-degree selection bound (each
eligible factor contributes g·μ to deg R_anch). Nat division IS the floor. -/
def ShapeRead.mbar (R : ShapeRead) : ℕ := R.len / (R.g * R.μ)

/-- **A shape-prefix P̂** (§D4-R L3): the list of retained read data. |P̂| = reads.length. -/
structure ShapePrefix where
  reads : List ShapeRead

/-- W(P̂) := Σ_r w_r·d_r — the pool dimension (§D4-R Ledger data). -/
def ShapePrefix.W (P : ShapePrefix) : ℕ := (P.reads.map (fun R => R.w * R.d)).sum

/-- M(P̂) := ∏_r m̄_r — L11's p-FREE shape factor (M ≤ n^{|P̂|} is display-side). -/
def ShapePrefix.Mfac (P : ShapePrefix) : ℕ := (P.reads.map ShapeRead.mbar).prod

/-- `R.Matches ν`: node ν carries EXACTLY the retained shape data R — field-by-field
equalities, incl. the height pair (h, u*) and γ, plus the pool card p^w (the frame
field's size; §D4-R: "read r carries d_r side digits ranging in a pool of size
Q_r = p^{w_r}"). This is shape(η)'s per-node clause. -/
def ShapeRead.Matches {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (R : ShapeRead) (ν : Node p F) : Prop :=
  ν.species = R.species ∧ ν.e = R.e ∧ ν.h = R.h ∧ ν.g = R.g ∧ ν.μ = R.μ ∧
  ν.a = R.a ∧ ν.s0 = R.s0 ∧ ν.wSide = R.wSide ∧ ν.Dwidth = R.Dwidth ∧
  ν.ustar = R.ustar ∧ ν.gam = R.gam ∧ Nat.card ↥ν.σ.K = p ^ R.w

/-- shape(η) = P̂, as a match predicate (length + per-read `Matches`). -/
def ShapePrefix.MatchesHist {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (P : ShapePrefix) (H : History p F) : Prop :=
  ∃ hlen : H.nodes.length = P.reads.length,
    ∀ (r : ℕ) (hr : r < H.nodes.length),
      (P.reads[r]'(hlen ▸ hr)).Matches (H.nodes[r]'hr)

/-- **The L11 encoding target**: per read, (the side-digit tuple on the retained slot
set, valued in a size-p^{w_r} pool) × (the factor-selection index in {1,…,m̄_r}).
`Fin mbar` is EMPTY when m̄_r = 0 — consistent: realizability forces deg R_anch ≥ g·μ,
so a shape with m̄_r = 0 has empty Pref. -/
def EncTarget (p : ℕ) (P : ShapePrefix) : Type :=
  ∀ r : Fin P.reads.length,
    ((↥(P.reads.get r).slots → Fin (p ^ (P.reads.get r).w)) × Fin (P.reads.get r).mbar)
```

```lean
section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **The family modeling Pref(P̂)** (§D4-R L3: Pref(P̂) := {η : shape(η) = P̂, η
realizable, canonical lifts}; C_P̂(p) := #Pref(P̂)). `idx` enumerates the realized value
prefixes; each carries its MovesC presentation `jet` (realizability + coherence live
INSIDE `JetSetup` — fields `coherent`, `realizable`, so (NA)+(HV)+(SAE) is consumed, not
restated). BRIDGE FIELDS (HC-2): `jet` (existence of the presentation at the common
level N ≥ N(P̂)), `henc` (L11's enc′ injectivity: the side-digit tuples + the
factor-selection indices determine η — the note's proof is kernel-(a)-conditional, (a)
dual-verified-discharged), `hist_inj` (distinct chains). The CANONICAL-LIFT policy and
the enumeration's COMPLETENESS are docstring duties of the bridge, not fields — the
mass-law arithmetic never consumes them (they enter only via L1/L6, already
hypothesis-level in `TreeModel`). -/
structure PrefFamily (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (P : ShapePrefix) where
  idx : Type
  hist : idx → History p F
  hist_inj : Function.Injective hist
  hshape : ∀ i, P.MatchesHist (hist i)
  jet : (i : idx) → JetSetup (hist i) n N m
  enc : idx → EncTarget p P
  henc : Function.Injective enc

variable {n N m : ℕ} {P : ShapePrefix}

/-- The branch fiber S(η,⊤) of member i — Theorem C's locus at Z = ⊤ (L6's object). -/
def PrefFamily.fiber (S : PrefFamily p F n N m P) (i : S.idx) : Set (Box p m) :=
  (S.jet i).SHZ (topLocus p m)

/-- The prefix EVENT S(P̂,⊤) := ⋃_η S(η,⊤) (D4R.1 — the PLAIN union; NOT disjoint). -/
def PrefFamily.event (S : PrefFamily p F n N m P) : Set (Box p m) :=
  ⋃ i, S.fiber i

/-- **Branch multiplicity** mult_P̂(f) := #{η ∈ Pref(P̂) : f ∈ S(η,⊤)} (L6 corollary; by
(D4R-CYL) = #{η ∈ Pref(P̂) : η ∈ T_can(f)} — unit D15). Finite by L8 (unit D2). -/
noncomputable def PrefFamily.mult (S : PrefFamily p F n N m P) (x : Box p m) : ℕ :=
  Nat.card {i : S.idx // x ∈ S.fiber i}

/-- C_P̂(p) := #Pref(P̂) — a literal finite count of realized value prefixes. -/
noncomputable def PrefFamily.C (S : PrefFamily p F n N m P) : ℕ := Nat.card S.idx

/-- η ⪯ η′ — initial-segment order on chains (§D4-R L3's prefix order). -/
def _root_.LeanUrat.MovesC.History.IsPrefixOf (H H' : History p F) : Prop :=
  H.nodes <+: H'.nodes

/-- **T_can(f), the maximal canonical branch tree, as an interface** (§D4-R L2, rev 6:
BRANCH-INDEXED FIBERS — the tree is a genuine function of f; uniqueness lives at the
TREE level; branches may be finite or infinite; NO termination is consumed). `mem H x` =
"the chain H is a branch of T_can(x)". Fields are the two laws the mass law consumes:
L2's prefix-closure and L6's (D4R-CYL). Both are note-DISCHARGED (L2 by the rev-6
architecture; L6 given kernel (a)+(b), both dual-verified-discharged by
`D4R0K_DERIVATION_2026-07-26.md` rev 3, + Theorem C(a)); their LEAN discharge is the
HC-2 bridge — they ride as hypothesis fields here, per the campaign format. -/
structure TreeModel (S : PrefFamily p F n N m P) where
  mem : History p F → Box p m → Prop
  prefix_closed : ∀ (H H' : History p F) (x : Box p m),
    H.IsPrefixOf H' → mem H' x → mem H x
  cyl : ∀ (i : S.idx) (x : Box p m), x ∈ S.fiber i ↔ mem (S.hist i) x

/-- **The leaf/verdict layer — D4R.0-K(c)/VP, the OPEN residual** (statements only; NO
MovesD unit consumes it). `leaf H x` = "H, with its verdict, is a terminal maximal
branch of T_can(x)" (L7's object). The verdict alphabet V, the halting rule τ, and the
uniform per-class detection cap are §T-ASSEMBLY's VP-1/VP-2 — OWNED BY MovesT; this
structure exists so MovesT can consume MovesD's tree without re-modeling it. -/
structure VerdictModel {S : PrefFamily p F n N m P} (T : TreeModel S) where
  leaf : History p F → Box p m → Prop
  leaf_mem : ∀ (H : History p F) (x : Box p m), leaf H x → T.mem H x

end
end LeanUrat.MovesD
```

DESIGN NOTES (for the Codex audit).
(i) `Realizable`/`HistoryCoherent` are NOT `PrefFamily` fields: they are already fields
of each `jet` (MovesC round 4) — restating them would double the hypothesis boundary.
(ii) `ShapeRead.Matches` includes the pool card `Nat.card ↥ν.σ.K = p ^ w` — the ONLY
place the shape's `w` touches the tower; it is an equality on interface data, not a new
axiom. (iii) The empty prefix η = ∅ (P̂ = ∅) is NOT a `History` (MovesC histories are
nonempty); the note dispatches it by display, never by Theorem C(b) — unit D14 encodes
that display directly on the full box. (iv) `mult`/`C` use `Nat.card` (junk 0 on
infinite types) — L8 (unit D2) makes them genuine counts; mass-law units take
`[Fintype S.idx]` binders, consistent by subsingleton of `Fintype` cards.

## 4. Unit specs (16 units; format per campaign §2; all in `lean/LeanUrat/MovesD/`)

Common binders (elided below): `{p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
{n N m : ℕ} {P : ShapePrefix}`, and for mass-law units `(S : PrefFamily p F n N m P)
[Fintype S.idx]`. `top := topLocus p m`.

### D0a — MovesD.topLocus_laws · `D0a_topLocus.lean`
statement:
  `theorem topLocus_sol : ∀ x : Box p m, (topLocus p m).IsSolution x`
  `theorem topLocus_numPinned : (topLocus p m).numPinned = 0`
  `theorem topLocus_admissible (Σf : Locus p m) : AdmissibleZ Σf (topLocus p m)`
moves_ref: "S(η,⊤) is §C's joint stratum with the tautological terminal system (Z = ⊤:
  no constraint, vol(⊤) = 1)" (L6).
deps: MovesC.Defs. sketch: `pinned ≡ false`; all three unfold + simp (filter of false =
  ∅; implications vacuous). difficulty: easy. hypothesis_fields: none.

### D0b — MovesD.thmC_top · `D0b_thmCtop.lean`
statement:
  `theorem totalPins_top {H : History p F} (J : JetSetup H n N m) : totalPins J (topLocus p m) = (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar)`
  `theorem thmC_top {H : History p F} (J : JetSetup H n N m) : Nat.card (J.SHZ (topLocus p m)) * p ^ totalPins J (topLocus p m) = p ^ (n * N)`
moves_ref: "Each NONEMPTY summand is Theorem C(b) with Z = ⊤ on the lift-carrying
  history η: μ(S(η,⊤)) = ∏ᵢ vol(E_fresh(νᵢ))" (D4R.1 proof).
deps: MovesC.C6_thmC_b, D0a. sketch: `C6_thmC_b J top (topLocus_admissible _)`; rewrite
  `boxMass p m = p^m = p^(n*N)` by `J.hm`; `totalPins` unfolds with `numPinned = 0`.
difficulty: easy. hypothesis_fields: none (J is a binder; its existence per η is the
  family's `jet` field — HC-2).

### D1 — MovesD.encTarget_card · `D1_encCard.lean`
statement: `theorem encTarget_card (p : ℕ) (hp : 0 < p) (P : ShapePrefix) : Nat.card (EncTarget p P) = P.Mfac * p ^ P.W`
moves_ref: "an INJECTION Pref(P̂) ↪ (∏_r 𝔸_r^{d_r}) × (∏_r {1,…,m̄_r}) … C_P̂(p) ≤
  M(P̂)·p^{W(P̂)}, W(P̂) = Σ_r w_r·d_r" (L11).
deps: Defs. sketch: `Nat.card` of a `Fin`-indexed Pi of products:
  ∏_r ((p^{w_r})^{d_r} · m̄_r); regroup ∏ (p^{w·d}) = p^{Σ w·d} = p^W and ∏ m̄ = Mfac;
  List-to-Finset sum/prod bridging (`List.get` enumeration ↔ `map`.sum/prod).
difficulty: medium. hypothesis_fields: none.

### D2 — MovesD.L8_finite · `D2_finite.lean`
statement: `theorem L8_finite (S : PrefFamily p F n N m P) : Finite S.idx`
moves_ref: "L8 (finite value-prefix lemma): Pref(P̂) is FINITE … by L11's rev-2 ENLARGED
  encoding an η is determined by its side-digit tuples PLUS its factor-selection indices".
deps: Defs. sketch: `EncTarget p P` is a finite type (Pi over Fin of products of finite
  types); `Finite.of_injective S.enc S.henc`. difficulty: easy.
hypothesis_fields: `S.henc` (L11 injectivity — note-discharged, Lean = HC-2).

### D3 — MovesD.D4R2' · `D3_poolBound.lean`
statement: `theorem D4R2' (S : PrefFamily p F n N m P) (hp : 0 < p) : S.C ≤ P.Mfac * p ^ P.W`
moves_ref: "What this note ESTABLISHES is D4R.2′: C_P̂(p) ≤ M(P̂)·p^{W(P̂)}, M(P̂) ≤
  n^{|P̂|} p-FREE (L11)" (PLAN RECONCILIATION display).
deps: D1, D2. sketch: `Nat.card_le_card_of_injective S.enc S.henc` (card monotone under
  injection into the finite `EncTarget`), then rewrite by D1. The coarse chain
  M ≤ n^{|P̂|} is display-side (not a unit; m̄_r ≤ n needs ℓ_r ≤ n — a realizability
  fact outside the family's data). difficulty: easy.
hypothesis_fields: `S.henc`.

### D4 — MovesD.chart_unique · `D4_chartUnique.lean`
statement: `theorem chart_unique {m n N : ℕ} (hm : m = n * N) (c c' : Fin m → Coord) (hs : ∀ j j', j < j' ↔ CoordPrec (c j) (c j')) (hs' : ∀ j j', j < j' ↔ CoordPrec (c' j) (c' j')) (hlt : ∀ j, (c j).1 < N ∧ (c j).2 < n) (hlt' : ∀ j, (c' j).1 < N ∧ (c' j).2 < n) : c = c'`
moves_ref: (support for L9 — §C's fixed global order ≺; the chart is the unique ≺-sorted
  enumeration of the N×n box, so equal shapes read the SAME coordinates).
deps: MovesC.Defs. sketch: `CoordPrec` restricted to the box is a strict linear order on
  a set of size nN = m; a strictly-monotone map Fin m → box is injective, hence (cards
  equal) bijective; two strictly-monotone bijections from `Fin m` onto the same finite
  strict linear order agree (induction on rank / `Finset.orderIsoOfFin` uniqueness after
  transporting `CoordPrec` to a `LinearOrder` instance on a box subtype).
difficulty: hard (allowed split at elaboration: (a) box bijectivity, (b) sorted-enum
  uniqueness). hypothesis_fields: none.

### D5 — MovesD.line_shape · `D5_lineShape.lean`
statement:
  `theorem Dwidth_pos {H : History p F} (hcoh : HistoryCoherent H) (i : ℕ) (hi : i < H.nodes.length) : 0 < (H.nodes[i]'hi).Dwidth`
  `theorem line_shape {H H' : History p F} (hcoh : HistoryCoherent H) (hcoh' : HistoryCoherent H') (hP : P.MatchesHist H) (hP' : P.MatchesHist H') (i : ℕ) (hi : i < H.nodes.length) (hi' : i < H'.nodes.length) : (H.nodes[i]'hi).line = (H'.nodes[i]'hi').line`
moves_ref: "A CONSUMES u*_r — the fresh inventory's strip depths run between the
  recorded old/new lines, each pinned only WITH its height; A is a function of P̂ only
  because u*_r ∈ P̂" (Ledger data, rev 9; L9's rev-9 bracket).
deps: Defs. sketch: slope: coherence's slope law `slope·(e·STR·D) = h` with e,h,STR,D
  matched (STR = ∏ earlier e's, equal by induction over `Matches`) and `e·STR·D ≠ 0`
  (`Dwidth_pos`: root `deg Φ₀ = 1` + width chain `D_{i+1} = e·g·D_i`, e,g ≥ 1); intercept:
  `hLineU` pins `line.at((s0+wSide)·Dwidth) = ustar`, all matched — two affine maps with
  equal slope + one equal value are equal (`Line` ext). THIS is where u* enters: without
  `ustar ∈ ShapeRead` the intercept is free exactly at non-vertex-pinned e = 1 reads.
difficulty: medium. hypothesis_fields: none.

### D6 — MovesD.ht_shape · `D6_htShape.lean`
statement: `theorem ht_shape {H H' : History p F} (hP : P.MatchesHist H) (hP' : P.MatchesHist H') : (∀ i, H.strFrame i = H'.strFrame i) ∧ (∀ r, H.kappaH r = H'.kappaH r) ∧ (∀ r b, H.innerslotH r b = H'.innerslotH r b) ∧ (∀ i c, H.htH i c = H'.htH i c) ∧ (∀ i, H.prevRim n i = H'.prevRim n i)`
moves_ref: "Each vol(E_fresh(νᵢ)) is a product of per-digit factors … each alphabet
  cardinality a power of p determined by the history's SHAPE data (§C C.3, verbatim)" (L9).
deps: Defs. sketch: all five are formulas in `Node.(e,h,g,μ,Dwidth,childWidth)` only —
  matched field-by-field by `Matches`; lengths equal; `List.take/map` congruence, then
  `Finset.sum` congruence for `htH`. No coherence needed. difficulty: medium (list
  plumbing, zero mathematical content). hypothesis_fields: none.

### D7 — MovesD.floor_shape · `D7_floorShape.lean`
statement: `theorem floor_shape {H H' : History p F} (hcoh : HistoryCoherent H) (hcoh' : HistoryCoherent H') (hP : P.MatchesHist H) (hP' : P.MatchesHist H') : (∀ i (hi : i < H.nodes.length) (hi' : i < H'.nodes.length), (H.nodes[i]'hi).staircase = (H'.nodes[i]'hi').staircase ∧ (H.nodes[i]'hi).slotVal = (H'.nodes[i]'hi').slotVal ∧ (H.nodes[i]'hi).fineSlot = (H'.nodes[i]'hi').fineSlot) ∧ (∀ i b, H.floorH i b = H'.floorH i b)`
moves_ref: (L9 continued — the strip depths between the recorded old/new LINES are shape
  data once the lines are pinned; rev 9: "each line is the slope −h_r/e_r line through
  (j*_r, u*_r), pinned only with its height").
deps: D5, D6. sketch: `staircase`/`slotVal`/`fineSlot` are formulas in (line, μ,
  childWidth, Dwidth): line equal by D5, the rest by `Matches`; `floorH` is a fold of
  matched staircases. difficulty: medium. hypothesis_fields: none.

### D8 — MovesD.band_shape · `D8_bandShape.lean`
statement: `theorem band_shape {H H' : History p F} {J : JetSetup H n N m} {J' : JetSetup H' n N m} (hP : P.MatchesHist H) (hP' : P.MatchesHist H') (i : ℕ) (hi : i < H.nodes.length) (hi' : i < H'.nodes.length) (c : Fin m) : inFreshBand H n J.coordOf i (H.nodes[i]'hi) c ↔ inFreshBand H' n J'.coordOf i (H'.nodes[i]'hi') c`
moves_ref: (L9's per-read exponent: the fresh band is the shape-determined inventory —
  §C C.1(ii) via MovesC's `inFreshBand`).
deps: D4, D5, D6, D7. sketch: `J.coordOf = J'.coordOf` by D4 (both sorted charts on the
  same (n,N,m) box, `coordOf_sorted` + `coordOf_lt` + `hm`; coherence via `J.coherent`);
  then `inFreshBand`'s three conjuncts transfer: `prevRim` (D6), `floorH`/`htH` (D6/D7),
  `slotVal ∘ fineSlot` (D7). difficulty: medium. hypothesis_fields: none (jets are
  binders here).

### D9 — MovesD.L9_totalPins_const · `D9_L9.lean`
statement: `theorem L9_totalPins_const (S : PrefFamily p F n N m P) (i j : S.idx) : totalPins (S.jet i) (topLocus p m) = totalPins (S.jet j) (topLocus p m)`
moves_ref: "L9 (shape-constant fresh volume): for every η ∈ Pref(P̂),
  ∏ᵢ vol(E_fresh(νᵢ)) = p^{−A(P̂)} … So the product depends on P̂ alone; A(P̂) := the
  resulting shape exponent."
deps: D0b (totalPins_top), D8; MovesC `mstar_eq`. sketch: `totalPins_top` reduces both
  sides to Σ_{r<len} mstar; lengths equal (`hshape`); per read r, `mstar_eq` equates each
  mstar with its fresh-band `Nat.card`; D8's iff gives `Nat.card` equality
  (`Nat.card_congr` on subtypes of the same `Fin m`). This unit is the Lean form of L9 —
  a THEOREM, not a hypothesis: MovesC's `mstar_eq` is exactly the §C C.3 citation the
  note's L9 consumes. difficulty: medium.
hypothesis_fields: `S.jet` (per-member presentations at the common N).

### D10 — MovesD.D4R1_SUM · `D10_sumLaw.lean`
statement:
  `theorem D4R1_SUM (S : PrefFamily p F n N m P) [Fintype S.idx] (A : ℕ) (hA : ∀ i, totalPins (S.jet i) (topLocus p m) = A) : (∑ i : S.idx, Nat.card (S.fiber i)) * p ^ A = S.C * p ^ (n * N)`
  `theorem D4R1_SUM' (S : PrefFamily p F n N m P) [Fintype S.idx] (i₀ : S.idx) : (∑ i : S.idx, Nat.card (S.fiber i)) * p ^ (totalPins (S.jet i₀) (topLocus p m)) = S.C * p ^ (n * N)`
moves_ref: "Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)} (D4R.1-SUM) — EXACT, each
  summand Theorem C(b)" ≡ at level N: "Σ_{η ∈ Pref(P̂)} #{f mod p^N ∈ S(η,⊤)} =
  C_P̂(p)·p^{nN−A(P̂)} (D4R.4-SUM)" — division-free transposition (·p^A both sides).
deps: D0b, D9. sketch: distribute `* p^A` into the sum; per summand,
  `Nat.card (fiber i) * p^A = Nat.card (fiber i) * p^{totalPins (jet i) top}` (hA)
  `= p^{n·N}` (thmC_top); Σ constant = card·constant; `S.C = Fintype.card S.idx`
  (Nat.card_eq_fintype_card). D4R1_SUM' discharges hA via D9 with A := the i₀ value. NO
  disjointness consumed anywhere — the sum is over the INDEX type (the note's rev-6
  point, verbatim). difficulty: medium.
hypothesis_fields: `hA` (in-corpus discharged by D9/D4R1_SUM' when idx nonempty).

### D11 — MovesD.mult_count · `D11_mult.lean`
statement:
  `theorem mult_sum (S : PrefFamily p F n N m P) [Fintype S.idx] : ∑ x : Box p m, S.mult x = ∑ i : S.idx, Nat.card (S.fiber i)`
  `theorem event_iff_mult (S : PrefFamily p F n N m P) [Fintype S.idx] (x : Box p m) : x ∈ S.event ↔ 1 ≤ S.mult x`
moves_ref: "equivalently: at every level N ≥ N(P̂), the level-N average of mult_P̂ is
  C_P̂(p)·p^{−A(P̂)} — finitely many indicators, summed" (D4R.1-SUM parenthesis);
  "S(P̂,⊤) := ⋃_η S(η,⊤) = {f : mult_P̂(f) ≥ 1}".
deps: Defs, D2. sketch: double counting over the finite product {(i,x) : x ∈ fiber i} —
  `Finset.card` of the sigma set counted both ways (`Nat.card` of subtypes →
  `Finset.card` filters via Fintype); `event_iff`: `mem_iUnion` + `Nat.card_pos` for
  nonempty finite subtypes. This unit IS the finite-level measurability content: mult is
  a finite sum of indicators. difficulty: medium. hypothesis_fields: none.

### D12 — MovesD.D4R1_EV · `D12_evBound.lean`
statement: `theorem D4R1_EV (S : PrefFamily p F n N m P) [Fintype S.idx] (A : ℕ) (hA : ∀ i, totalPins (S.jet i) (topLocus p m) = A) : Nat.card S.event * p ^ A ≤ S.C * p ^ (n * N)`
moves_ref: "μ(P̂) := μ(S(P̂,⊤)) ≤ C_P̂(p)·p^{−A(P̂)} (D4R.1-EV) by subadditivity" ≡
  level-N: "#{f mod p^N ∈ S(P̂,⊤)} ≤ C_P̂(p)·p^{nN−A(P̂)} (D4R.4-EV), the union bound
  within the level-N box".
deps: D10, D11. sketch: `Nat.card S.event ≤ ∑ i, Nat.card (S.fiber i)` — the finite
  union bound (via D11: card event = #{x : mult ≥ 1} ≤ Σ_x mult = Σ_i card fiber);
  multiply by p^A, rewrite with D4R1_SUM. difficulty: medium. hypothesis_fields: `hA`.

### D13 — MovesD.D4R1_EV_iff · `D13_evIff.lean`
statement: `theorem D4R1_EV_iff (S : PrefFamily p F n N m P) [Fintype S.idx] (A : ℕ) (hA : ∀ i, totalPins (S.jet i) (topLocus p m) = A) : (Nat.card S.event * p ^ A = S.C * p ^ (n * N)) ↔ (∀ x ∈ S.event, S.mult x = 1)`
moves_ref: "with EQUALITY iff mult_P̂ ≡ 1 on the event … POINTWISE UPGRADE (displayed):
  … a μ-null overlap is EMPTY, so a.e.-equality forces mult_P̂ ≡ 1 POINTWISE on the
  event — the 'iff' holds at pointwise strength" (D4R.1 proof; D4R.4's finite-level
  form: "count-equality ⟺ the fibers are residue-disjoint ⟺ mult_P̂ ≡ 1 POINTWISE").
deps: D10, D11. sketch: cancel p^A (p ≥ 2 > 0) against D4R1_SUM: equality ⟺
  card event = Σ_i card fiber = Σ_x mult (D11). With card event = #{x : mult x ≥ 1}
  (D11) and mult = 0 off the event: Σ_x mult ≥ #{mult ≥ 1} with equality iff mult ≤ 1
  everywhere — pointwise, no a.e. slack AT FINITE LEVEL (the note's upgrade is automatic
  here: nonempty sets have positive card). difficulty: medium-hard (careful Finset
  double counting). hypothesis_fields: `hA`.

### D14 — MovesD.empty_dispatch · `D14_empty.lean`
statement:
  `theorem D4R4_empty (S : PrefFamily p F n N m P) [IsEmpty S.idx] : S.event = ∅ ∧ S.C = 0 ∧ ∀ A : ℕ, Nat.card S.event * p ^ A = S.C * p ^ (n * N)`
  `theorem emptyPrefix_display (p m : ℕ) [Fact p.Prime] : Nat.card (Set.univ : Set (Box p m)) * p ^ 0 = 1 * p ^ m`
moves_ref: L12: "If Pref(P̂) = ∅ then S(P̂,⊤) = ⋃_{η∈∅} S(η,⊤) = ∅ and C_P̂(p) = 0 …
  #{f mod p^N ∈ ∅} = 0 = C_P̂(p)·p^{nN−A(P̂)} — D4R.4 is trivially exact at every level;
  the max-over-∅ expression is never formed." And the η = ∅ dispatch: "its fiber S(∅,⊤)
  is the FULL BOX … mass μ = 1 = C_∅·p^{−A(∅)} … by L5's normalized full-box display —
  NOT by Theorem C(b), whose history quantifier begins at the root read."
deps: Defs. sketch: empty iUnion; `Nat.card` of ∅ and of the full box
  (`Fintype.card (Fin m → ZMod p) = p^m`, card ZMod p = p). Note (design note iii): η = ∅
  is not a `History`, so the display lives on the raw box, exactly as the note refuses
  Theorem C(b) there. difficulty: easy. hypothesis_fields: none.

### D15 — MovesD.tree_bridge · `D15_tree.lean`
statement:
  `theorem mult_eq_tree (S : PrefFamily p F n N m P) (T : TreeModel S) (x : Box p m) : S.mult x = Nat.card {i : S.idx // T.mem (S.hist i) x}`
  `theorem event_iff_tree (S : PrefFamily p F n N m P) [Fintype S.idx] (T : TreeModel S) (x : Box p m) : x ∈ S.event ↔ ∃ i : S.idx, T.mem (S.hist i) x`
moves_ref: "mult_P̂(f) := #{η ∈ Pref(P̂) : η ∈ T_can(f)} (finite, L8) — a genuine
  function of f (L2: the tree is), with S(P̂,⊤) := ⋃_η S(η,⊤) = {f : mult_P̂(f) ≥ 1}"
  (L6 corollary).
deps: Defs, D11. sketch: rewrite each `x ∈ S.fiber i` by `T.cyl i x`
  (`Nat.card_congr` via `Equiv.subtypeEquiv` on the iff); event via `mem_iUnion`.
difficulty: easy. hypothesis_fields: `T.cyl` (L6 D4R-CYL — kernel (a)/(b) discharged at
  the math level, Lean discharge HC-2), `T.prefix_closed` (carried, not consumed here).

## 5. Perimeter (what MovesD does NOT establish — mirror of §D4-R.5)

- NO claim that C_P̂(p) is polynomial/uniform in p ([1v]'s burden); C is `Nat.card idx`,
  a per-(p, family) count. D4R.3 (torus lemma) stays RETIRED — nothing here cites it.
- NO shape catalogue, state types, cones, or aggregation over P̂ ([2a]/[2b] → MovesSp/
  MovesV). CONSUMER DUTY carried in Defs docstrings: the events {S(P̂,⊤)} are a
  multiplicity-weighted COVER — downstream corpora must consume D4R1_SUM or the EV
  bounds, never a partition-of-the-box claim.
- NO resummation, drainage, or termination ([3]/[5] → MovesT/MovesX); the tree model is
  finite-or-infinite-agnostic (no termination field exists to consume).
- NO L7 complete-history unit (bookkeeping; `VerdictModel` carries the L7 OBJECT for
  MovesT, statements only). NO gate D4-n3 re-derivation (the sealed instance is census
  material; a future decidable-instance unit may pin P̂* as a `ShapePrefix` literal —
  NOT in this wave).
- The literal (3i) coefficient-one bound is NOT stated: D3 is the M-carrying D4R.2′
  (the note's PLAN RECONCILIATION, verbatim); M(P̂*) = 1 discharge is per-consumer.

## 6. Suggested build order and difficulty profile

  wave A (parallel, no interdeps): D0a, D1, D2, D14 → then D0b, D3.
  wave B (the L9 chain, sequential-ish): D5, D6 → D7 → D4 ∥ → D8 → D9.
  wave C (mass laws): D10 → D11 → D12 → D13; D15 anytime after D11.
  Hard units: D4 (chart uniqueness — split permission pre-granted), D13 (double
  counting). Everything else easy/medium, ≤ ~40 lines expected.

## 7. Codex-audit checklist (statement faithfulness, per campaign gate A)

1. `ShapeRead` retains EXACTLY rev-9 L3's list — in particular BOTH heights (h, u*) and
   the slot sets; nothing digit-valued. (u* omission = the pass-10 F1 CRITICAL.)
2. D10/D12/D13 are stated on the INDEX SUM / plain union — no disjointness field
   anywhere in `PrefFamily` (rev-6 F1: fiber disjointness is REFUTED; a `disj` field
   would encode the withdrawn rev-5 text).
3. `TreeModel.cyl` is an iff for EVERY x (D4R-CYL exact for every f, including inputs
   with infinite canonical runs) — no termination hypothesis may be added.
4. The EV equality criterion is pointwise-on-the-event (D13's RHS), never a.e.
5. Kernel conditionality: no unit may cite `D4R0K_DERIVATION` as a Lean discharge — (a)/
   (b) discharged at the MATH level only; the Lean fields stay hypotheses until HC-2.
   (c)/VP appears ONLY in `VerdictModel` (statements, no consumption).
6. `topLocus` must satisfy vol(⊤) = 1 literally (numPinned = 0), and D0b must consume
   `C6_thmC_b`'s statement verbatim (no re-proof of Theorem C content in MovesD).
7. Statement-fence: `hA` in D10/D12/D13 must never migrate into `PrefFamily` as a field
   (it is DERIVABLE via D9 for nonempty idx; a field would hide L9's theorem status).

## 8. MANIFEST stub

corpus: MovesD · source: §D4-R rev 9 (DUAL-ACCEPTED 2026-07-27) · consumes: MovesC
(C6_thmC_b, JetSetup/SHZ/totalPins/mstar_eq, History/Node) · units: 16 (D0a, D0b,
D1–D15) · defs: 1 file · open-hypothesis surface: PrefFamily.{jet, enc+henc, hist_inj},
TreeModel.{mem, prefix_closed, cyl}, VerdictModel (all HC-2/VP — see §2 ledger).
