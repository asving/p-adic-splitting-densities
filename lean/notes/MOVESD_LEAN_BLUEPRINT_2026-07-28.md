# MOVESD LEAN BLUEPRINT — REV 2 (post-Codex-audit, 10 findings repaired)

Campaign unit-spec per `LEAN_FORMALIZATION_CAMPAIGN_2026-07-28.md` §2. Writer: Fable.
REV 2 (2026-07-27): all 10 findings of `MOVESD_AUDIT_CODEX_2026-07-28.md` (REJECT,
8 crit / 2 gap) repaired in one batch; findings→repairs table at §9.

## 0. Source and ground truth

SOURCE: `lean/notes/MOVES_2026-07-24.md`, `## §D4-R — the per-shape-prefix mass law`
(lines ~4580–5432), **rev 9**, DUAL-ACCEPTED 2026-07-27 (Codex pass 11 + Fable confirm,
both CLEAN on identical rev-9 text). KERNEL STATUS (same record): D4R.0-K parts **(a)**
L1 canonical-choice totality and **(b)** L5 digit-cell structural exhaustiveness are
DISCHARGED by the dual-verified derivation `D4R0K_DERIVATION_2026-07-26.md` (rev 3;
Codex pass 3 SOUND + Fable CLEAN). The residual is **(c) — the verdict pin VP**
(alphabet V + halting rule τ + the uniform per-class detection cap), OPEN, owned by
§T-ASSEMBLY ([3t]) → MovesT. §D4-R's remaining conditionality: dual-accepted §C
(rev 14) + dual-accepted §B2-DEF (D¹¹d) + the (c)/VP residual.

TARGET DISPLAYS (the note's headline, encoded by this corpus):
  Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)}          (D4R.1-SUM)
  μ(P̂) := μ(⋃_η S(η,⊤)) ≤ C_P̂(p)·p^{−A(P̂)}, = iff mult ≡ 1  (D4R.1-EV)
  C_P̂(p) ≤ M(P̂)·p^{W(P̂)},  M(P̂) = ∏_r m̄_r ≤ n^{|P̂|} p-free (D4R.2′ / L11)
  μ(P̂) ≤ M(P̂)·p^{−A_net(P̂)}, A_net := A − W               (Corollary D4R.2)
  Σ_η #{f mod p^N ∈ S(η,⊤)} = C_P̂(p)·p^{nN−A(P̂)}, N ≥ N(P̂) (D4R.4-SUM/EV)
  Pref(∅) = {∅}, C_∅ = 1, A(∅) = 0, S(∅,⊤) = the full box   (the η = ∅ dispatch)

## 1. The MovesC-consumption design (CONSUME, do not re-model)

MovesC (36/36 PROVED) supplies, and MovesD imports verbatim:
- `History p F` / `Node p F` — a realized lift-carrying prefix η IS a MovesC `History`
  (§D4-R L3: "A realized prefix IS a lift-carrying history in §C's sense"). Node's
  rev-9 retained fields exist: `ustar` (u*_r), `gam` (γ_r), `pat` (the side digits),
  `s0/wSide/Dwidth/e/h/g/μ/a/species`.
- `Realizable` ((NA)+(HV)+(SAE) — §C C.0's live three-condition class, rev 14) and
  `HistoryCoherent` — used LITERALLY in `PrefSet` (the Lean Pref(P̂)); also carried by
  every `jet` (JetSetup fields `realizable`, `coherent`).
- `JetSetup H n N m` — the presented history; `JetSetup.SHZ Z` — S(η, Z); at the new
  `topLocus` (Z = ⊤: numPinned = 0, AdmissibleZ vacuous) this is the D4R fiber S(η,⊤).
- `C6_thmC_b : Nat.card (J.SHZ Z) * p ^ totalPins J Z = boxMass p m` — Theorem C(b),
  each D4R.1 summand (unit D0b specializes at ⊤; unit D0c extracts positive mass).
- `J.mstar_eq` — each read's fresh codimension = the fresh-band count from NODE data:
  this is the §C C.3 citation that makes L9 (A is a SHAPE function) PROVABLE here.

NEW OBJECTS (classifier content beyond MovesC's interface):
- `ShapePrefix` P̂ — the L3 dictionary as data (all rev-9 retained fields incl. the
  height pair (h_r, u*_r) and the slot sets), + the shape functions W, M(= Mfac),
  m̄_r, ℓ_r, AND [REV 2, finding 4] the DEFINED ledger exponent `ShapePrefix.A n N`
  (the shape-side fresh-band count — §3.3) with `Anet := A − W`.
- `PrefSet Canon P` — the LITERAL Lean Pref(P̂): {H | shape-match ∧ HistoryCoherent ∧
  Realizable ∧ Canon} [REV 2, finding 1]. `Canon` is the canonical-lift-policy
  predicate, an explicit OPEN PARAMETER (the §B2-DEF (S6b) offset-P policy; its Lean
  definition is §B2-DEF/HC-1 corpus content — every MovesD theorem is ∀-Canon).
- `PrefFamily` — an EXACT enumeration of `PrefSet Canon P`: injective `hist` +
  COMPLETENESS field (`complete`: every member of PrefSet is enumerated) [REV 2,
  finding 1 — an empty family is legal exactly when Pref(P̂) = ∅, the note's own
  allowance: L12 "no restriction to C_P̂(p) > 0 is imposed"]. Per-member `jet` (HC-2
  data) and the L11 encoding: `sel` (the factor-selection ranks, data) with the
  DEFINED `encOf` (actual side digits, ambient-field-valued, on the retained slots +
  the ranks) and `henc : Injective encOf` [REV 2, finding 2 — the injection is now ON
  THE ACTUAL DATA; the cardinal bound is DERIVED in units D1a/D1b/D3a].
- `TreeModel` — T_can(f) with L2's laws: prefix-closure, emits-only-realizable-
  canonical, and (D4R-CYL); `mem := False` is UNBUILDABLE for any nonempty family
  (unit D0c: fibers are nonempty) [REV 2, finding 7].
- `VerdictModel` — the (c)/VP surface with TYPED fields: verdict alphabet V (finite,
  nonempty), the emission map, leaf ⟺ verdict-emitted, leaf-maximality BOTH ways
  (L2: "a chain has NO children IFF its read returns a terminal verdict"), the
  detection cap — `leaf := False` no longer a free instance [REV 2, finding 8].

FINITE-LEVEL POLICY (house style): every statement is a `Nat.card` count over the
level-N box `Box p m := Fin m → ZMod p`, division-free (`count * p^A = C * p^(nN)`).
D4R.1 (the μ-form) and D4R.4 (the level-N form) COINCIDE in this model: μ is the
note's normalized level-N count at any N ≥ N(P̂) ("Ledger data"), and the family fixes
ONE (n, N, m) — L12's N(P̂) := max_η N(η,⊤) is absorbed into the EXISTENCE of the jets
at a common N (bridge-side; L8 makes the max exist; the empty-Pref clause N(P̂) := 1
is carried by explicit `hN : 1 ≤ N` hypotheses on the dispatch units [REV 2, finding
6]). The note's a.e.-to-pointwise upgrade collapses at finite level: nonempty sets
have positive card, so the mult ≡ 1 criterion is pure counting — no measure theory.

## 2. Hypothesis-field ledger (never silently strengthened or dropped)

| field | encodes | status |
|---|---|---|
| `Canon` (parameter) | the canonical (S6b) offset-P lift policy | OPEN parameter; pinned by §B2-DEF/HC-1; all theorems ∀-Canon |
| `PrefFamily.jet` | η presented at the common level N (N ≥ N(η,⊤), §C C.2) | HC-2 bridge |
| `PrefFamily.complete` | Pref(P̂) enumerated EXACTLY (with `hist_inj`, `hshape`, `hcanon`) | HC-2 bridge (enumeration duty) |
| `PrefFamily.henc` | L11 enc′ injectivity ON ACTUAL DATA (side digits on the retained slots + factor ranks determine η) | note-DISCHARGED (L11 proof, rev 9; kernel (a) dual-verified-discharged); Lean discharge = HC-2 |
| `PrefFamily.sel` semantics | s_r = rank of ψ_r in D.3(e)'s lex order | docstring duty, HC-2 (only injectivity is consumed) |
| `Matches.offSlots_forced` | off-slot side digits are the forced monic value | blueprint reading of L3's retained slot sets — AUDIT-FLAGGED at §3.2 |
| `TreeModel.{prefix_closed, mem_realizable}` | L2: tree structure; emits only realizable canonical patterns | note-DISCHARGED (L2, rev-6 architecture); Lean = HC-2 |
| `TreeModel.cyl` | L6 (D4R-CYL): S(η,⊤) = {f : η ∈ T_can(f)} | note-DISCHARGED given kernel (a)+(b) — both DISCHARGED by `D4R0K_DERIVATION` rev 3 (dual-verified) — + Thm C(a); Lean = HC-2 |
| `VerdictModel` (whole) | leaf/verdict layer: V, τ-emission, cap | **OPEN** — D4R.0-K(c)/VP, owned by §T-ASSEMBLY → MovesT |
| `hn : ∀ R ∈ P.reads, R.len ≤ n` (D3a/D3b hyp) | "deg R_anch,r ≤ n always" (L11's coarse chain) | classifier fact; HC-2-dischargeable; explicit theorem hypothesis |
| `hN : 1 ≤ N`, `hm : m = n*N` (D14a/D14b hyps) | L12's N(P̂) := 1 empty-case convention; the box shape | explicit (no jet available to supply them) |

## 3. Defs skeleton — `lean/LeanUrat/MovesD/Defs.lean` (definitions only, no theorems)

### 3.1 Box, top locus, shape reads

```lean
import Mathlib
import LeanUrat.MovesC.Defs

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

/-- The level-N coefficient box in frame-0 digit coordinates (m = n·N base digits). -/
abbrev Box (p m : ℕ) : Type := Fin m → ZMod p

/-- **Z = ⊤** (§D4-R L6: "the tautological terminal system (Z = ⊤: no constraint,
vol(⊤) = 1)"): no pinned coordinate; `IsSolution` is vacuous. -/
def topLocus (p m : ℕ) : Locus p m := { pinned := fun _ => false, solve := fun _ _ => 0 }

/-- **One read of a shape-prefix** — §D4-R L3's retained fields, rev 9 EXACTLY:
species, (e,h,g,μ,a), side endpoints/raw width (s0, wSide), frame width, the
stride-position/slot set (hence d_r), AND the height pair — h (slope numerator) and
the SIDE HEIGHT u*_r (rev 9, pass-10 F1 CRITICAL: retained DATA, not recovered: at a
non-adjacent e = 1 read the stride rule is γ-blind). `gam` = γ_r; `w` = the pool
residue degree (Q_r = p^w, w ≥ 1: pools are fields). Digit VALUES and lifts forgotten. -/
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
  hw : 1 ≤ w
  hDw : 1 ≤ Dwidth
  hslots : slots ⊆ Finset.range (wSide / e + 1)

def ShapeRead.d (R : ShapeRead) : ℕ := R.slots.card         -- d_r (W's count, rev 9)
def ShapeRead.len (R : ShapeRead) : ℕ := R.wSide / R.e      -- ℓ_r = w'_r/e_r = deg R_anch
def ShapeRead.mbar (R : ShapeRead) : ℕ := R.len / (R.g * R.μ) -- m̄_r (Nat ⌊·⌋)
def ShapeRead.childWidthS (R : ShapeRead) : ℕ := R.e * R.g * R.Dwidth

structure ShapePrefix where
  reads : List ShapeRead

def ShapePrefix.W (P : ShapePrefix) : ℕ := (P.reads.map (fun R => R.w * R.d)).sum
def ShapePrefix.Mfac (P : ShapePrefix) : ℕ := (P.reads.map ShapeRead.mbar).prod
```

### 3.2 The shape-match predicate and the L11 encoding (finding-2 repair)

```lean
section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- A node's side digit at pattern position k, valued in the AMBIENT field F (the
shared comparison field — subfield coercion; §C's D.3(e) fixed bases are the eventual
HC-2 refinement, but the F-coercion is already canonical). -/
def _root_.LeanUrat.MovesC.Node.sideDigit (ν : Node p F) (k : ℕ) : F :=
  ((ν.pat k : ↥ν.σ.K) : F)

/-- `R.Matches ν`: ν carries EXACTLY the retained shape data — field equalities incl.
the height pair (h, u*) and γ, the pool card p^w, AND [REV 2, finding 2 — the slot
tie] `offSlots_forced`: pattern positions OUTSIDE the retained slot set carry the
structurally forced monic digit 1 (the pinned instance's only exclusion: the root's
monic lead, digit 1 — §D4-R.6 "slot 3 = the monic lead, digit 1"). AUDIT FLAG: this
clause is the blueprint's reading of L3's "retained stride-position/slot sets (hence
the digit count d_r)" — off-slot digits carry no information, which is exactly what
makes the slots-restricted enc′ injective and W = Σ w·d the pool dimension. -/
def ShapeRead.Matches (R : ShapeRead) (ν : Node p F) : Prop :=
  ν.species = R.species ∧ ν.e = R.e ∧ ν.h = R.h ∧ ν.g = R.g ∧ ν.μ = R.μ ∧
  ν.a = R.a ∧ ν.s0 = R.s0 ∧ ν.wSide = R.wSide ∧ ν.Dwidth = R.Dwidth ∧
  ν.ustar = R.ustar ∧ ν.gam = R.gam ∧ Nat.card ↥ν.σ.K = p ^ R.w ∧
  (∀ k ≤ R.len, k ∉ R.slots → ν.sideDigit k = 1)

/-- shape(η) = P̂ (length + per-read `Matches`). -/
def ShapePrefix.MatchesHist (P : ShapePrefix) (H : History p F) : Prop :=
  ∃ hlen : H.nodes.length = P.reads.length,
    ∀ (r : ℕ) (hr : r < H.nodes.length),
      (P.reads[r]'(hlen ▸ hr)).Matches (H.nodes[r]'hr)

/-- **The L11 encoding target** (F-valued digit part; the pool restriction is applied
at the COUNTING units D1a/D1b/D3a, so this def needs no lemma): per read, (the
side-digit tuple on the retained slot set, in F) × (the selection index in Fin m̄_r).
`Fin mbar` is empty when m̄_r = 0 — consistent: such shapes have empty Pref. -/
def EncTarget (p : ℕ) (F : Type*) [Field F] (P : ShapePrefix) : Type :=
  ∀ r : Fin P.reads.length,
    ((↥(P.reads.get r).slots → F) × Fin (P.reads.get r).mbar)

/-- The unique candidate pool of residue degree w inside F: the root set of
X^{p^w} − X (a finite field has AT MOST ONE subfield per order, so every matched
frame field lands in THIS set — unit D1a; #pool ≤ p^w — unit D1b). -/
def pool (p w : ℕ) (F : Type*) [Field F] : Set F := {x : F | x ^ (p ^ w) = x}

end
```

### 3.3 The ledger exponent A(P̂), DEFINED (finding-4 repair)

The note: "A(P̂) := the ledger exponent — the sum over P̂'s nodes of the
shape-determined fresh-volume exponents (L9)… A CONSUMES u*_r". MovesC computes each
jet's exponent as a fresh-BAND count from node data (`mstar_eq`); the band predicate
is a formula in exactly the retained shape fields. So A is DEFINED by replicating
that formula on `ShapeRead` data over the (level, index) grid — u* enters through the
line intercept, precisely the rev-9 point.

```lean
def ShapePrefix.strS (P : ShapePrefix) (i : ℕ) : ℕ :=
  ((P.reads.take i).map ShapeRead.e).prod
/-- The read line of shape read r: slope h/(e·STR·D) (coherence's slope law),
intercept pinned by u* through the right endpoint (hLineU) — u*'s rev-9 role. -/
noncomputable def ShapePrefix.lineS (P : ShapePrefix) (r : ℕ) : Line :=
  (P.reads[r]?).elim ⟨0, 0⟩ (fun R =>
    let sl : ℚ := (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ) * (R.Dwidth : ℚ))
    ⟨R.ustar + sl * (((R.s0 + R.wSide) * R.Dwidth : ℕ) : ℚ), sl⟩)
noncomputable def ShapePrefix.kappaS (P : ShapePrefix) (r : ℕ) : ℚ :=
  (P.reads[r]?).elim 0 (fun R => (R.h : ℚ) / ((R.e : ℚ) * (P.strS r : ℚ)))
def ShapePrefix.innerslotS (P : ShapePrefix) (r b : ℕ) : ℕ :=
  (P.reads[r]?).elim 0 (fun R => (b % R.childWidthS) / R.Dwidth)
noncomputable def ShapePrefix.htS (P : ShapePrefix) (i : ℕ) (c : Coord) : ℚ :=
  (c.1 : ℚ) + (Finset.range i).sum (fun r => (P.innerslotS r c.2 : ℚ) * P.kappaS r)
noncomputable def ShapeRead.staircaseS (R : ShapeRead) (L : Line) (b : ℕ) : WithBot ℚ :=
  if b < R.μ * R.childWidthS
    then ((L.at ((b / R.childWidthS) * R.childWidthS) : ℚ) : WithBot ℚ) else ⊥
noncomputable def ShapePrefix.floorS (P : ShapePrefix) (i b : ℕ) : WithBot ℚ :=
  ((List.range i).map (fun r =>
    (P.reads[r]?).elim ⊥ (fun R => R.staircaseS (P.lineS r) b))).foldr max ⊥
def ShapePrefix.prevRimS (P : ShapePrefix) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => (P.reads[i]?).elim n (fun R => R.μ * R.childWidthS)
/-- The shape-side fresh-band predicate of read r at grid coordinate c = (ℓ, b) —
the `inFreshBand` formula on retained data. -/
noncomputable def ShapePrefix.bandS (P : ShapePrefix) (n : ℕ) (r : ℕ) (c : Coord) : Prop :=
  c.2 < P.prevRimS n r ∧
  P.floorS r c.2 < ((P.htS r c : ℚ) : WithBot ℚ) ∧
  (P.reads[r]?).elim False (fun R =>
    P.htS r c ≤ (P.lineS r).at ((c.2 / R.Dwidth) * R.Dwidth))
open Classical in
/-- **A(P̂)** at box parameters (n, N): Σ_r #(grid ∩ band_r). N-stable for N ≥ N(P̂)
(L12; not needed as a theorem — the family fixes one N). A(∅ shape) = 0 (empty sum). -/
noncomputable def ShapePrefix.A (P : ShapePrefix) (n N : ℕ) : ℕ :=
  (Finset.range P.reads.length).sum (fun r =>
    ((Finset.range N ×ˢ Finset.range n).filter (fun c => P.bandS n r c)).card)
/-- A_net(P̂) := A(P̂) − W(P̂) (Corollary D4R.2's exponent; ℤ-valued). -/
noncomputable def ShapePrefix.Anet (P : ShapePrefix) (n N : ℕ) : ℤ :=
  (P.A n N : ℤ) - (P.W : ℤ)
```

### 3.4 PrefSet and the family (finding-1/5 repair)

```lean
section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- **The LITERAL Lean Pref(P̂)** (§D4-R L3: "Pref(P̂) := {η : shape(η) = P̂, η
realizable, canonical lifts}"): realizability is MovesC's live (NA)+(HV)+(SAE) class,
coherence is §C history well-formedness, `Canon` the canonical-lift-policy parameter
(OPEN — the (S6b) offset-P rule; pinned by §B2-DEF/HC-1). -/
def PrefSet (Canon : History p F → Prop) (P : ShapePrefix) : Set (History p F) :=
  {H | P.MatchesHist H ∧ HistoryCoherent H ∧ Realizable H ∧ Canon H}

/-- **The family = an EXACT enumeration of Pref(P̂)** [REV 2, finding 1]. `complete` +
`hist_inj` + (`hshape`,`hcanon`, jet's `coherent`/`realizable`) make `hist` a
bijection onto `PrefSet Canon P` (unit D2b) — `idx := Empty` is buildable ONLY when
Pref(P̂) = ∅ (the note's honest allowance, L12). `hne`: the EMPTY shape P̂ = ∅ is NOT
family territory — the note dispatches η = ∅ "FIRST, separately from Theorem C(b)"
(unit D14a) [REV 2, finding 5]. `jet` = HC-2 presentation data at the COMMON level N.
`sel` = the L11 factor-selection ranks (data; rank semantics is a docstring/HC-2
duty). `henc` = L11's injectivity ON THE ACTUAL DATA (see `encOf`). -/
structure PrefFamily (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F]
    (n N m : ℕ) (Canon : History p F → Prop) (P : ShapePrefix) where
  idx : Type
  hist : idx → History p F
  hist_inj : Function.Injective hist
  hne : P.reads ≠ []
  hshape : ∀ i, P.MatchesHist (hist i)
  hcanon : ∀ i, Canon (hist i)
  complete : ∀ H ∈ PrefSet Canon P, ∃ i, hist i = H
  jet : (i : idx) → JetSetup (hist i) n N m
  sel : (i : idx) → (r : Fin P.reads.length) → Fin (P.reads.get r).mbar
  /-- **L11 enc′ injectivity, ON THE ACTUAL DATA** [REV 2, finding 2]: two members
  with the SAME side-digit values at every pattern position of every read (compared
  in the ambient field) and the SAME selection ranks are the same member. Quantifier
  bounded to pattern positions k ≤ ℓ_r (`hRanch`'s range — positions beyond it are
  Node junk, deliberately excluded). Note-discharged (L11's induction via L4/L1);
  Lean discharge = HC-2. -/
  henc : ∀ i j : idx,
    (∀ (r k : ℕ) (hr : r < P.reads.length), k ≤ (P.reads[r]'hr).len →
      ((hist i).nodes[r]?).elim (0 : F) (fun ν => ν.sideDigit k)
        = ((hist j).nodes[r]?).elim (0 : F) (fun ν => ν.sideDigit k)) →
    sel i = sel j → i = j

variable {n N m : ℕ} {Canon : History p F → Prop} {P : ShapePrefix}

/-- **The DEFINED L11 encoding** [REV 2, finding 2]: member i ↦ (its ACTUAL side
digits on the retained slots, read off `Node.pat` in the ambient field; its selection
ranks). Junk 0 beyond the history (never hit: lengths match by `hshape`). -/
noncomputable def PrefFamily.encOf (S : PrefFamily p F n N m Canon P) (i : S.idx) :
    EncTarget p F P :=
  fun r => (fun j => ((S.hist i).nodes[(r : ℕ)]?).elim 0 (fun ν => ν.sideDigit j),
            S.sel i r)
```

Note (the enc chain): `encOf` restricts to the RETAINED slots; `henc` quantifies over
ALL pattern positions k ≤ ℓ_r. The bridge is `Matches.offSlots_forced` (off-slot
digits = the forced monic 1 on BOTH sides), so `Injective S.encOf` is DERIVED (unit
D2a's first lemma), and the cardinal bound follows by counting `encOf`'s pool-valued
range (units D1a/D1b/D3a) — nothing about cardinalities is assumed in `henc`.

### 3.5 Fibers, event, multiplicity, tree, verdict layer (finding-7/8 repairs)

```lean
/-- The branch fiber S(η,⊤) of member i — Theorem C's locus at Z = ⊤ (L6's object). -/
def PrefFamily.fiber (S : PrefFamily p F n N m Canon P) (i : S.idx) : Set (Box p m) :=
  (S.jet i).SHZ (topLocus p m)

/-- The prefix EVENT S(P̂,⊤) := ⋃_η S(η,⊤) (D4R.1 — the PLAIN union; NOT disjoint). -/
def PrefFamily.event (S : PrefFamily p F n N m Canon P) : Set (Box p m) := ⋃ i, S.fiber i

/-- Branch multiplicity mult_P̂(f) := #{η ∈ Pref(P̂) : f ∈ S(η,⊤)}; by (D4R-CYL)
= #{η ∈ Pref(P̂) : η ∈ T_can(f)} (unit D15). Finite by L8 (unit D2a). -/
noncomputable def PrefFamily.mult (S : PrefFamily p F n N m Canon P) (x : Box p m) : ℕ :=
  Nat.card {i : S.idx // x ∈ S.fiber i}

/-- C_P̂(p) := #Pref(P̂) (= Nat.card (PrefSet Canon P), unit D2b). -/
noncomputable def PrefFamily.C (S : PrefFamily p F n N m Canon P) : ℕ := Nat.card S.idx

/-- η ⪯ η′ — initial-segment order on chains (§D4-R L3's prefix order: literal
node-data + lift equality — `Node` carries the lifts, so List prefix IS that). -/
def _root_.LeanUrat.MovesC.History.IsPrefixOf (H H' : History p F) : Prop :=
  H.nodes <+: H'.nodes

/-- **T_can(f) as an interface** (§D4-R L2, rev 6: branch-indexed fibers; the tree a
choice-free function of f; branches finite or infinite; NO termination consumed).
[REV 2, finding 7] Laws: (i) `prefix_closed` — L2 "T_can(f) is prefix-closed — a
tree" (the empty chain is not a `History`; its universal membership is the η = ∅
dispatch, unit D14a, never a tree field); (ii) `mem_realizable` — L2/D4R.1: "the tree
emits only realizable patterns … each single branch is a lift-carrying history in
§C's sense", with canonical lifts; (iii) `cyl` — L6 (D4R-CYL), for EVERY x including
inputs with infinite canonical runs. NON-VACUITY: `mem := fun _ _ => False` violates
`cyl` for ANY family with nonempty idx, since every fiber is NONEMPTY (unit D0c —
Theorem C(b)'s positive mass); with `complete` (finding 1) the family is empty ONLY
when Pref(P̂) = ∅. L2's maximality ("children = ALL eligible next-node data") is
delivered ON THE FAMILY by `cyl` + `complete`: the tree's shape-P̂ chains at x are
exactly the enumerated fibers containing x — beyond the interface, the cell-level
eligibility semantics is kernel-(b) content (dual-verified derivation; HC-2). -/
structure TreeModel (S : PrefFamily p F n N m Canon P) where
  mem : History p F → Box p m → Prop
  prefix_closed : ∀ (H H' : History p F) (x : Box p m),
    H.IsPrefixOf H' → mem H' x → mem H x
  mem_realizable : ∀ (H : History p F) (x : Box p m),
    mem H x → HistoryCoherent H ∧ Realizable H ∧ Canon H
  cyl : ∀ (i : S.idx) (x : Box p m), x ∈ S.fiber i ↔ mem (S.hist i) x

/-- **The leaf/verdict layer — D4R.0-K(c)/VP, the OPEN residual** [REV 2, finding 8:
typed fields; `leaf := False` is no longer a free instance]. `V` = the verdict
alphabet (VP-1: finite, nonempty); `vdict H x` = the verdict the read of chain H
emits on input x (`none` = the read continues); `leaf_iff` ties leaves to emission;
`leaf_maximal` + `leaf_of_maximal` are L2's clause IN BOTH DIRECTIONS: "a chain has
NO children IFF its read returns a terminal verdict" — so `leaf := False` forces
every mem-chain to extend properly, a substantive tree property, not a trivial
instance; `cap` = the uniform per-class detection cap (typed; its VP cap LAW, the
halting rule τ on cells, and (c2) exactly-one-verdict semantics are §T-ASSEMBLY's
VP-1/VP-2 — OWNED BY MovesT; nothing in MovesD consumes this structure). -/
structure VerdictModel {S : PrefFamily p F n N m Canon P} (T : TreeModel S) where
  V : Type
  hVfin : Finite V
  hVne : Nonempty V
  vdict : History p F → Box p m → Option V
  leaf : History p F → Box p m → Prop
  leaf_iff : ∀ H x, leaf H x ↔ (T.mem H x ∧ vdict H x ≠ none)
  leaf_maximal : ∀ H H' x, leaf H x → T.mem H' x → H.IsPrefixOf H' → H' = H
  leaf_of_maximal : ∀ H x, T.mem H x →
    (∀ H', T.mem H' x → H.IsPrefixOf H' → H' = H) → leaf H x
  cap : ℕ
  hcap : 1 ≤ cap

end
end LeanUrat.MovesD
```

DESIGN NOTES (for the re-audit).
(i) `Realizable`/`HistoryCoherent` appear in `PrefSet` LITERALLY and in each `jet`
(MovesC fields) — one hypothesis boundary, stated twice by construction, never
weakened. (ii) `ShapeRead.Matches` includes the pool card and the off-slot forcing —
the two ties findings 2 flagged; both are equalities on interface data. (iii) The
empty prefix η = ∅ is not a `History`; `hne` excludes P̂ = ∅ from families and unit
D14a carries the note's η = ∅ display (C_∅ = 1, A(∅) = 0, full box), connected
through `ShapePrefix.A` — never through Theorem C(b) [findings 5/6]. (iv) `mult`/`C`
use `Nat.card`; mass-law units take `[Fintype S.idx]`, consistent by `Subsingleton`
of Fintype cards; L8 (D2a) supplies the instance from `henc`.

## 4. Unit specs (32 units; format per campaign §2; all in `lean/LeanUrat/MovesD/`)

Common binders (elided): `{p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
{n N m : ℕ} {Canon : History p F → Prop} {P : ShapePrefix}`; `S : PrefFamily p F n N
m Canon P`; mass-law units add `[Fintype S.idx]` (supplied by D2a via
`Fintype.ofFinite`). `top := topLocus p m`. Units marked AUX have no note display —
their informal statement is given in the spec [REV 2, findings 9/10: every former
hidden sub-lemma is now its own auxiliary unit].

### D0a — MovesD.topLocus_laws · `D0a_topLocus.lean`
statement:
  `theorem topLocus_sol : ∀ x : Box p m, (topLocus p m).IsSolution x`
  `theorem topLocus_numPinned : (topLocus p m).numPinned = 0`
  `theorem topLocus_admissible (Σf : Locus p m) : AdmissibleZ Σf (topLocus p m)`
moves_ref: "the tautological terminal system (Z = ⊤: no constraint, vol(⊤) = 1)" (L6).
deps: MovesC.Defs. sketch: `pinned ≡ false`; unfold + simp. difficulty: easy.
hypothesis_fields: none.

### D0b — MovesD.thmC_top · `D0b_thmCtop.lean`
statement:
  `theorem totalPins_top {H : History p F} (J : JetSetup H n N m) : totalPins J (topLocus p m) = (Finset.range H.nodes.length).sum (fun i => (J.fresh i).mstar)`
  `theorem thmC_top {H : History p F} (J : JetSetup H n N m) : Nat.card (J.SHZ (topLocus p m)) * p ^ totalPins J (topLocus p m) = p ^ (n * N)`
moves_ref: "Each NONEMPTY summand is Theorem C(b) with Z = ⊤ on the lift-carrying
  history η: μ(S(η,⊤)) = ∏ᵢ vol(E_fresh(νᵢ))" (D4R.1 proof).
deps: MovesC.C6_thmC_b, D0a. sketch: `C6_thmC_b J top (topLocus_admissible _)`;
  `boxMass p m = p^(n*N)` by `J.hm`; `numPinned = 0`. difficulty: easy.
hypothesis_fields: none (J a binder; per-η existence = `S.jet`, HC-2).

### D0c — MovesD.fiber_pos · `D0c_fiberPos.lean`  [REV 2, finding 7 support]
statement: `theorem fiber_pos (S : PrefFamily p F n N m Canon P) (i : S.idx) : (S.fiber i).Nonempty`
moves_ref: "Positive mass survives: … for NONEMPTY η, Theorem C(b) gives mass
  p^{−A(P̂)} > 0" (L6 corollary).
deps: D0b. sketch: thmC_top gives `card · p^k = p^{nN} > 0` (p prime ⟹ p ≥ 2, and
  `hN : 1 ≤ N` inside the jet is not even needed: p^{nN} ≥ 1), so `Nat.card ≠ 0`;
  a set of nonzero card in a finite type is nonempty. Consequence recorded in the
  TreeModel docstring: `mem := False` violates `cyl` whenever idx is inhabited.
difficulty: easy. hypothesis_fields: none.

### D1a — MovesD.digit_in_pool · `D1a_digitPool.lean`  (AUX)
informal: a matched node's side digits lie in THE order-p^w root set of F — the
  note's "read r's digits range in a pool of size Q_r = p^{w_r}" made literal.
statement: `theorem digit_in_pool {R : ShapeRead} {ν : Node p F} (hM : R.Matches ν) (k : ℕ) : ν.sideDigit k ∈ pool p R.w F`
deps: Defs. sketch: `↥ν.σ.K` is a finite field of card `p^R.w` (hM's pool-card
  clause); `FiniteField.pow_card`: x^(p^w) = x in the subfield; push through the
  (injective ring hom) subfield coercion. difficulty: medium. hypothesis_fields: none.

### D1b — MovesD.pool_card_le · `D1b_poolCard.lean`  (AUX)
informal: the pool has at most p^w elements (roots of X^{p^w} − X).
statement: `theorem pool_card_le (p w : ℕ) (hp : 2 ≤ p) (hw : 1 ≤ w) (F : Type*) [Field F] [Finite F] : Nat.card ↥(pool p w F) ≤ p ^ w`
deps: Defs. sketch: pool = root set of the nonzero polynomial X^{p^w} − X (degree
  p^w ≥ 2 > 1, so it is not X − X); `Polynomial.card_roots_le_degree` /
  `Set.Finite.card` bridging. difficulty: medium. hypothesis_fields: none.

### D1c — MovesD.encTargetP_card · `D1c_encCard.lean`  (AUX)
Defs addendum (goes into `Defs.lean` §3.2 at elaboration):
  `def EncTargetP (p : ℕ) (F : Type*) [Field F] (P : ShapePrefix) : Type := ∀ r : Fin P.reads.length, ((↥(P.reads.get r).slots → ↥(pool p (P.reads.get r).w F)) × Fin (P.reads.get r).mbar)`
statement: `theorem encTargetP_card (hp : 2 ≤ p) : Nat.card (EncTargetP p F P) ≤ P.Mfac * p ^ P.W`
moves_ref: "an INJECTION Pref(P̂) ↪ (∏_r 𝔸_r^{d_r}) × (∏_r {1,…,m̄_r})" (L11 — this
  unit counts the CODOMAIN: ∏_r Q_r^{d_r}·m̄_r ≤ p^W·M).
deps: D1b. sketch: `Nat.card` of a Fin-indexed Pi of products: ∏_r
  (card pool)^{d_r}·m̄_r ≤ ∏_r (p^{w_r})^{d_r}·m̄_r; regroup = p^{Σ w·d}·∏ m̄ =
  p^W·Mfac (List↔Finset sum/prod bridging). difficulty: medium.
hypothesis_fields: none.

### D2a — MovesD.L8_finite · `D2a_finite.lean`
statement:
  `theorem encOf_inj (S : PrefFamily p F n N m Canon P) : Function.Injective S.encOf`
  `theorem L8_finite (S : PrefFamily p F n N m Canon P) : Finite S.idx`
moves_ref: "L8: Pref(P̂) is FINITE … by L11's rev-2 ENLARGED encoding an η is
  determined by its side-digit tuples PLUS its factor-selection indices".
deps: Defs. sketch: `encOf i = encOf j` gives slot-digit equality + `sel` equality;
  extend to ALL pattern positions k ≤ ℓ_r by `Matches.offSlots_forced` (both sides
  = 1 off the slot set); apply the field `S.henc`. `EncTarget p F P` is a finite
  type (F finite), so `Finite.of_injective S.encOf encOf_inj`. difficulty: medium.
hypothesis_fields: `S.henc` (L11 — note-discharged; Lean = HC-2),
  `Matches.offSlots_forced` (via `S.hshape`).

### D2b — MovesD.prefSet_eq · `D2b_prefSet.lean`  [REV 2, finding 1]
statement:
  `theorem range_hist (S : PrefFamily p F n N m Canon P) : Set.range S.hist = PrefSet Canon P`
  `theorem C_eq_card_prefSet (S : PrefFamily p F n N m Canon P) : S.C = Nat.card (PrefSet Canon P)`
moves_ref: "Pref(P̂) := { η : shape(η) = P̂, η realizable, canonical lifts },
  C_P̂(p) := #Pref(P̂)" (L3's definition display).
deps: Defs. sketch: ⊆ by `hshape`/`hcanon` + each jet's `coherent`/`realizable`;
  ⊇ by `complete`; the card identity by `hist_inj` (`Nat.card_range_of_injective`).
  THE de-vacuification display: every downstream `S.C` is literally #Pref(P̂).
difficulty: easy-medium. hypothesis_fields: `S.complete`, `S.jet` (HC-2).

### D3a — MovesD.D4R2' · `D3a_poolBound.lean`  [REV 2, findings 2/3]
statement:
  `theorem D4R2' (S : PrefFamily p F n N m Canon P) : S.C ≤ P.Mfac * p ^ P.W`
  `theorem Mfac_le (hn : ∀ R ∈ P.reads, R.len ≤ n) : P.Mfac ≤ n ^ P.reads.length`
moves_ref: "C_P̂(p) ≤ M(P̂)·p^{W(P̂)}, M(P̂) ≤ n^{|P̂|} p-FREE (L11)" (PLAN
  RECONCILIATION display — BOTH clauses now stated).
deps: D1a, D1c, D2a. sketch: restrict `S.encOf` to `EncTargetP` (digits land in the
  pool by D1a + `hshape`); injective by `encOf_inj`; `Nat.card_le_card_of_injective`
  + D1c. `Mfac_le`: m̄_r = ℓ_r/(g·μ) ≤ ℓ_r ≤ n (Nat.div_le_self, hn); List.prod ≤
  n^length. difficulty: medium. hypothesis_fields: `S.henc` (through D2a); `hn` (the
  note's "deg R_anch,r ≤ n always" — classifier fact, explicit hypothesis, ledger §2).

### D3b — MovesD.D4R2_cor · `D3b_corD4R2.lean`  [REV 2, finding 4 tail]
statement: `theorem D4R2_cor (S : PrefFamily p F n N m Canon P) [Fintype S.idx] : Nat.card S.event * p ^ (P.A n N) ≤ P.Mfac * p ^ (P.W + n * N)`
moves_ref: "μ(P̂) ≤ C_P̂(p)·p^{−A(P̂)} ≤ M(P̂)·p^{W(P̂)−A(P̂)} = M(P̂)·p^{−A_net(P̂)},
  A_net(P̂) := A(P̂) − W(P̂)" (Corollary D4R.2) — division-free transposition: both
  sides × p^{A}, RHS regrouped via `pow_add`; `ShapePrefix.Anet` records the named
  exponent for downstream (3i)-class consumers.
deps: D12, D3a. sketch: chain D4R1_EV (≤ S.C·p^{nN}) with D4R2' (S.C ≤ M·p^W);
  `pow_add`. difficulty: easy. hypothesis_fields: none beyond D12/D3a's.

### The L9 chain (D4a–D9): totalPins = A(P̂), one lemma per unit
[REV 2, findings 9/10: the former D4 chart-uniqueness theorem is GONE — the
shape-side band is defined on the raw (level, index) grid (§3.3), so only chart
BIJECTIVITY onto the grid is needed, split into two AUX units; the former D6/D7
bundles are unbundled one lemma per unit. Every unit below takes `hcoh :
HistoryCoherent H` and/or `hP : P.MatchesHist H` as marked.]

### D4a — MovesD.chart_bij · `D4a_chartBij.lean`  (AUX)
informal: a JetSetup's ≺-sorted chart is a bijection onto the N×n grid.
statement: `theorem chart_bij {H : History p F} (J : JetSetup H n N m) : Function.Injective J.coordOf ∧ ∀ c ∈ Finset.range N ×ˢ Finset.range n, ∃ j : Fin m, J.coordOf j = c`
deps: MovesC.Defs. sketch: injectivity: `coordOf_sorted` + irreflexivity of
  `CoordPrec` (j ≠ j' ⟹ one of j < j', j' < j ⟹ images CoordPrec-related ⟹
  distinct). Surjectivity: an injection `Fin m → grid` (by `coordOf_lt`) with
  `card grid = N·n = m` (`J.hm`) is surjective (`Finset.card` pigeonhole /
  `Fintype.bijective_iff_injective_and_card` on the grid subtype).
difficulty: medium. hypothesis_fields: none.

### D4b — MovesD.chart_count · `D4b_chartCount.lean`  (AUX)
informal: counting a coordOf-pulled-back predicate over `Fin m` = counting it over
  the grid (the pushforward of counts under D4a's bijection).
statement: `theorem chart_count {H : History p F} (J : JetSetup H n N m) (φ : Coord → Prop) [DecidablePred φ] : Nat.card {c : Fin m // φ (J.coordOf c)} = ((Finset.range N ×ˢ Finset.range n).filter (fun c => φ c)).card`
deps: D4a. sketch: `Nat.card_congr` along the D4a bijection restricted to the
  subtype; `Finset.card_filter` bridging. difficulty: medium.
hypothesis_fields: none.

### D5a — MovesD.Dwidth_pos · `D5a_dwidthPos.lean`  (AUX)
informal: every read of a coherent history has positive frame width (root
  `deg Φ₀ = 1`; width chain `D_{i+1} = e·g·D_i`, e, g ≥ 1).
statement: `theorem Dwidth_pos {H : History p F} (hcoh : HistoryCoherent H) (r : ℕ) (hr : r < H.nodes.length) : 0 < (H.nodes[r]'hr).Dwidth`
deps: MovesC.Defs. sketch: induction on r: base — coherence's root clause + the
  node's `hDwidth`; step — coherence's width chain `Dwidth_{r+1} = childWidth_r =
  e·g·Dwidth_r > 0`. difficulty: medium. hypothesis_fields: none.

### D6a — MovesD.strFrame_shape · `D6a_strShape.lean`
statement: `theorem strFrame_shape {H : History p F} (hP : P.MatchesHist H) : ∀ i, H.strFrame i = P.strS i`
moves_ref: (L9's shape data — the stretch STR_i = ∏_{m<i} e_m is a function of the
  retained e's).
deps: Defs. sketch: `List.take/map` congruence from the per-read `Matches` e-clause
  + length equality. difficulty: easy. hypothesis_fields: none.

### D5b — MovesD.line_shape · `D5b_lineShape.lean`
statement: `theorem line_shape {H : History p F} (hcoh : HistoryCoherent H) (hP : P.MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) : (H.nodes[r]'hr).line = P.lineS r`
moves_ref: "each line is the slope −h_r/e_r line through (j*_r, u*_r), pinned only
  WITH its height … A is a function of P̂ only because u*_r ∈ P̂" (L9's rev-9
  bracket — u* enters HERE, through the intercept).
deps: D5a, D6a. sketch: `Line` ext. Slope: coherence's slope law
  `slope·(e·STR·D) = h` with e·STR·D ≠ 0 (node `he`, D5a, STR ≥ 1 as a product of
  e's ≥ 1); shape side is the same quotient (D6a). Intercept: the node's `hLineU`
  pins `line.at((s0+wSide)·D) = ustar`; solve for the intercept — the shape
  formula. Without `ustar ∈ ShapeRead` the intercept is FREE exactly at
  non-vertex-pinned e = 1 reads (the pass-10 F1 witness pair). difficulty: medium.
hypothesis_fields: none.

### D6b — MovesD.kappaH_shape · `D6b_kappaShape.lean`
statement: `theorem kappaH_shape {H : History p F} (hP : P.MatchesHist H) : ∀ r, H.kappaH r = P.kappaS r`
moves_ref: (L9 — level weights κ_r = h_r/(e_r·STR_r) are shape data).
deps: D6a. sketch: getElem?-elim case split; Matches e/h clauses + D6a.
difficulty: easy. hypothesis_fields: none.

### D6c — MovesD.innerslot_shape · `D6c_innerslotShape.lean`
statement: `theorem innerslot_shape {H : History p F} (hP : P.MatchesHist H) : ∀ r b, H.innerslotH r b = P.innerslotS r b`
moves_ref: (L9 — inner slots are functions of the retained width chain).
deps: Defs. sketch: getElem?-elim; Matches e/g/Dwidth clauses (childWidth =
  e·g·Dwidth). difficulty: easy. hypothesis_fields: none.

### D6d — MovesD.htH_shape · `D6d_htShape.lean`
statement: `theorem htH_shape {H : History p F} (hP : P.MatchesHist H) : ∀ i c, H.htH i c = P.htS i c`
moves_ref: "each alphabet cardinality a power of p determined by the history's
  SHAPE data (§C C.3, verbatim)" (L9 — the height chart is shape data).
deps: D6b, D6c. sketch: `Finset.sum` congruence of the two K1-chain formulas.
difficulty: easy. hypothesis_fields: none.

### D6e — MovesD.prevRim_shape · `D6e_prevRimShape.lean`
statement: `theorem prevRim_shape {H : History p F} (hP : P.MatchesHist H) : ∀ i, H.prevRim n i = P.prevRimS n i`
moves_ref: (L9 — the rim thresholds μ_{i−1}·D_i are shape data).
deps: Defs. sketch: case split on i; getElem?-elim; Matches μ/e/g/Dwidth.
difficulty: easy. hypothesis_fields: none.

### D7a — MovesD.staircase_shape · `D7a_staircaseShape.lean`
statement: `theorem staircase_shape {H : History p F} (hcoh : HistoryCoherent H) (hP : P.MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) (hr' : r < P.reads.length) : ∀ b, (H.nodes[r]'hr).staircase b = (P.reads[r]'hr').staircaseS (P.lineS r) b`
moves_ref: (L9 — the (ZC-a) staircases: line + μ + widths, all retained).
deps: D5b. sketch: unfold both; rewrite line by D5b, μ/childWidth by Matches.
difficulty: easy. hypothesis_fields: none.

### D7b — MovesD.floorH_shape · `D7b_floorShape.lean`
statement: `theorem floorH_shape {H : History p F} (hcoh : HistoryCoherent H) (hP : P.MatchesHist H) : ∀ i b, H.floorH i b = P.floorS i b`
moves_ref: "the fresh inventory's strip depths run between the recorded old/new
  lines, each pinned only WITH its height" (L9 rev 9 — the floor is the old-lines
  max).
deps: D7a. sketch: both are folds of the first-i staircases; `List.take/map/range`
  congruence + D7a per entry. difficulty: medium (list plumbing only).
hypothesis_fields: none.

### D7c — MovesD.slotVal_shape · `D7c_slotValShape.lean`
statement: `theorem slotVal_shape {H : History p F} (hcoh : HistoryCoherent H) (hP : P.MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) (hr' : r < P.reads.length) : ∀ b, (H.nodes[r]'hr).slotVal ((H.nodes[r]'hr).fineSlot b) = (P.lineS r).at ((b / (P.reads[r]'hr').Dwidth) * (P.reads[r]'hr').Dwidth)`
moves_ref: (L9 — the band's fine-slot upper edge `new(j) = line.at(j·Dwidth)`,
  MovesC ROUND 6's exact boundary, is line + Dwidth: shape data).
deps: D5b. sketch: unfold `slotVal`/`fineSlot`; rewrite by D5b + Matches Dwidth.
difficulty: easy. hypothesis_fields: none.

### D8 — MovesD.band_shape · `D8_bandShape.lean`
statement: `theorem band_shape {H : History p F} {J : JetSetup H n N m} (hP : P.MatchesHist H) (r : ℕ) (hr : r < H.nodes.length) (c : Fin m) : (inFreshBand H n J.coordOf r (H.nodes[r]'hr) c ↔ P.bandS n r (J.coordOf c))`
moves_ref: (L9's per-read exponent — `inFreshBand` is the §C C.1(ii) inventory; all
  three conjuncts are shape formulas).
deps: D6d, D6e, D7b, D7c (coherence from `J.coherent`). sketch: conjunct-wise:
  prevRim (D6e), floor/height (D7b/D6d), fine-slot edge (D7c); the getElem?-elim on
  the shape side resolves by `hr' := hP.len ▸ hr`. difficulty: medium.
hypothesis_fields: none.

### D9 — MovesD.L9_A · `D9_L9.lean`
statement: `theorem L9_A (S : PrefFamily p F n N m Canon P) (i : S.idx) : totalPins (S.jet i) (topLocus p m) = P.A n N`
moves_ref: "∏_{i=0}^{k} vol(E_fresh(νᵢ)) = p^{−A(P̂)} … So the product depends on P̂
  alone; A(P̂) := the resulting shape exponent (the ledger exponent)" (L9). [REV 2,
  finding 4: A is now the DEFINED `ShapePrefix.A` — L9 is a THEOREM, exactly the §C
  C.3 citation via MovesC's `mstar_eq`.]
deps: D0b, D8, D4b; MovesC `mstar_eq`. sketch: `totalPins_top` → Σ_{r<len} mstar;
  len = |P̂| (hshape); per read, `mstar_eq` → the band `Nat.card`; D8 → the pulled-
  back `bandS` predicate; D4b → the grid filter card = A's r-th summand (classical
  decidability for the filter). difficulty: medium.
hypothesis_fields: `S.jet` (HC-2 presentations at the common N).

### D10 — MovesD.D4R1_SUM · `D10_sumLaw.lean`  [REV 2, finding 4: A defined, no hA]
statement: `theorem D4R1_SUM (S : PrefFamily p F n N m Canon P) [Fintype S.idx] : (∑ i : S.idx, Nat.card (S.fiber i)) * p ^ (P.A n N) = S.C * p ^ (n * N)`
moves_ref: "Σ_{η ∈ Pref(P̂)} μ(S(η,⊤)) = C_P̂(p)·p^{−A(P̂)} (D4R.1-SUM) — EXACT, each
  summand Theorem C(b)" ≡ at level N: "Σ_{η ∈ Pref(P̂)} #{f mod p^N ∈ S(η,⊤)} =
  C_P̂(p)·p^{nN−A(P̂)} (D4R.4-SUM)" — division-free transposition (·p^A both sides).
deps: D0b, D9. sketch: distribute `* p^A`; per summand rewrite the exponent by D9
  then close by `thmC_top`; Σ of the constant p^{nN} = card·p^{nN};
  `S.C = Fintype.card` (`Nat.card_eq_fintype_card`). NO disjointness consumed — the
  sum is over the INDEX type (the note's rev-6 point). Holds for empty idx (0 = 0):
  the L12 empty-Pref clause is INSIDE this statement; D14b displays it. difficulty:
  medium. hypothesis_fields: none new (jet via D9).

### D11a — MovesD.mult_sum · `D11a_multSum.lean`
statement: `theorem mult_sum (S : PrefFamily p F n N m Canon P) [Fintype S.idx] : ∑ x : Box p m, S.mult x = ∑ i : S.idx, Nat.card (S.fiber i)`
moves_ref: "equivalently: at every level N ≥ N(P̂), the level-N average of mult_P̂ is
  C_P̂(p)·p^{−A(P̂)} — finitely many indicators, summed" (D4R.1-SUM parenthesis).
deps: Defs, D2a. sketch: double counting of {(i,x) : x ∈ fiber i} (Finset.card of
  the sigma set both ways; `Nat.card` → `Finset.card` via Fintype). This IS the
  finite-level "mult is measurable": a finite sum of indicators. difficulty: medium.
hypothesis_fields: none.

### D11b — MovesD.event_iff_mult · `D11b_eventMult.lean`
statement: `theorem event_iff_mult (S : PrefFamily p F n N m Canon P) [Fintype S.idx] (x : Box p m) : x ∈ S.event ↔ 1 ≤ S.mult x`
moves_ref: "S(P̂,⊤) := ⋃_η S(η,⊤) = { f : mult_P̂(f) ≥ 1 }" (D4R.1's event display).
deps: Defs, D2a. sketch: `Set.mem_iUnion` + `Nat.card_pos` for nonempty finite
  subtypes (both directions). difficulty: easy. hypothesis_fields: none.

### D12 — MovesD.D4R1_EV · `D12_evBound.lean`
statement: `theorem D4R1_EV (S : PrefFamily p F n N m Canon P) [Fintype S.idx] : Nat.card S.event * p ^ (P.A n N) ≤ S.C * p ^ (n * N)`
moves_ref: "μ(P̂) := μ(S(P̂,⊤)) ≤ C_P̂(p)·p^{−A(P̂)} (D4R.1-EV) by subadditivity" ≡
  level-N: "#{f mod p^N ∈ S(P̂,⊤)} ≤ C_P̂(p)·p^{nN−A(P̂)} (D4R.4-EV), the union bound
  within the level-N box".
deps: D10, D11a, D11b. sketch: `Nat.card S.event = #{x : mult ≥ 1} ≤ Σ_x mult =
  Σ_i card(fiber i)` (D11a/b); multiply by p^A; rewrite by D4R1_SUM. difficulty:
  medium. hypothesis_fields: none.

### D13 — MovesD.D4R1_EV_iff · `D13_evIff.lean`
statement: `theorem D4R1_EV_iff (S : PrefFamily p F n N m Canon P) [Fintype S.idx] : (Nat.card S.event * p ^ (P.A n N) = S.C * p ^ (n * N)) ↔ (∀ x ∈ S.event, S.mult x = 1)`
moves_ref: "with EQUALITY iff mult_P̂ ≡ 1 on the event … count-equality ⟺ the
  fibers are residue-disjoint ⟺ mult_P̂ ≡ 1 POINTWISE on the event — the
  finite-level statement carries no measure-zero exception" (D4R.1 pointwise
  upgrade / L12's finite-level form).
deps: D10, D11a, D11b. sketch: cancel p^A (p ≥ 2) against D4R1_SUM: equality ⟺
  #{mult ≥ 1} = Σ_x mult; mult = 0 off the event, so the sum minorizes the count
  with equality iff mult ≤ 1 everywhere — pointwise, pure Finset counting (the
  note's a.e. subtlety collapses at finite level: nonempty ⟹ positive card).
difficulty: medium-hard. hypothesis_fields: none.

### D14a — MovesD.emptyShape_law · `D14a_emptyShape.lean`  [REV 2, findings 5/6]
statement:
  `theorem A_nil (P : ShapePrefix) (hP : P.reads = []) (n N : ℕ) : P.A n N = 0`
  `theorem emptyShape_law (p : ℕ) [Fact p.Prime] {n N m : ℕ} (hm : m = n * N) (hN : 1 ≤ N) (P : ShapePrefix) (hP : P.reads = []) : Nat.card (Set.univ : Set (Box p m)) * p ^ (P.A n N) = 1 * p ^ (n * N)`
moves_ref: "The EMPTY prefix η = ∅ (present iff P̂ = ∅, Pref(∅) = {∅}) is split off
  FIRST: its fiber is the FULL BOX, level-N count p^{nN} = C_∅·p^{nN − A(∅)}
  (C_∅ = 1, A(∅) = 0), by L5's normalized full-box display — NOT by Theorem C(b),
  whose quantifier begins at the root read" (L12 sketch; D4R.1 proof).
deps: Defs. sketch: A_nil: empty sum. Law: `Nat.card univ = p^m = p^{nN}` (hm;
  `Fintype.card_fun`, `ZMod.card`), A_nil kills the exponent; the literal 1 IS C_∅
  (Pref(∅) = {∅} — the η = ∅ chain is not a `History`, whence `hne` keeps P̂ = ∅ out
  of families and THIS display carries the case, connected through `ShapePrefix.A`
  [finding 5]; `hN : 1 ≤ N` = L12's N(∅-Pref) := 1 convention [finding 6]).
difficulty: easy. hypothesis_fields: `hm`, `hN` explicit (no jet exists to supply
  them).

### D14b — MovesD.D4R4_emptyPref · `D14b_emptyPref.lean`  [REV 2, finding 6]
statement: `theorem D4R4_emptyPref (S : PrefFamily p F n N m Canon P) [IsEmpty S.idx] (hN : 1 ≤ N) (hm : m = n * N) : S.event = ∅ ∧ S.C = 0 ∧ Nat.card S.event * p ^ (P.A n N) = S.C * p ^ (n * N)`
moves_ref: "If Pref(P̂) = ∅ then S(P̂,⊤) = ⋃_{η∈∅} S(η,⊤) = ∅ and C_P̂(p) = 0, so for
  EVERY N ≥ 1: #{f mod p^N ∈ ∅} = 0 = C_P̂(p)·p^{nN − A(P̂)} — D4R.4 is trivially
  exact at every level" (L12's empty case).
deps: Defs. sketch: empty iUnion; Nat.card of ∅ and of Empty; 0 = 0. `hN`/`hm`
  explicit per L12's convention [finding 6]. By D2b, `[IsEmpty S.idx]` occurs
  exactly when `PrefSet Canon P = ∅` — the note's honest allowance, no longer a
  vacuity leak [finding 1]. difficulty: easy. hypothesis_fields: `hN`, `hm`.

### D15 — MovesD.tree_bridge · `D15_tree.lean`
statement:
  `theorem mult_eq_tree (S : PrefFamily p F n N m Canon P) (T : TreeModel S) (x : Box p m) : S.mult x = Nat.card {i : S.idx // T.mem (S.hist i) x}`
  `theorem event_iff_tree (S : PrefFamily p F n N m Canon P) [Fintype S.idx] (T : TreeModel S) (x : Box p m) : x ∈ S.event ↔ ∃ i : S.idx, T.mem (S.hist i) x`
moves_ref: "mult_P̂(f) := #{ η ∈ Pref(P̂) : η ∈ T_can(f) } (finite, L8) — a genuine
  function of f (L2: the tree is), with S(P̂,⊤) := ⋃_η S(η,⊤) = {f : mult_P̂(f) ≥ 1}"
  (L6 corollary).
deps: Defs, D11b. sketch: rewrite each `x ∈ S.fiber i` by `T.cyl i x`
  (`Nat.card_congr`/`Equiv.subtypeEquiv`); event via `Set.mem_iUnion`. With D2b the
  index set is literally Pref(P̂), so the counted set is the note's display.
difficulty: easy. hypothesis_fields: `T.cyl` (L6 D4R-CYL — kernel (a)/(b)
  math-discharged, Lean = HC-2), `T.prefix_closed`/`T.mem_realizable` (carried).

## 5. Perimeter (what MovesD does NOT establish — mirror of §D4-R.5)

- NO claim that C_P̂(p) is polynomial/uniform in p ([1v]'s burden); `S.C` is a
  per-(p, Canon, P̂) count. D4R.3 (torus lemma) stays RETIRED — nothing cites it.
- NO shape catalogue, state types, cones, or aggregation over P̂ ([2a]/[2b] →
  MovesSp/MovesV). CONSUMER DUTY (Defs docstrings): the events {S(P̂,⊤)} are a
  multiplicity-weighted COVER — downstream must consume D4R1_SUM or the EV bounds,
  never a partition-of-the-box claim.
- NO resummation, drainage, or termination ([3]/[5]); the tree model is
  finite-or-infinite-agnostic (no termination field exists to consume).
- NO L7 unit (bookkeeping; `VerdictModel` carries L7's OBJECT — typed, statements
  only — for MovesT). NO gate D4-n3 re-derivation (census material; a decidable
  P̂*-literal unit is a possible later wave, not this one).
- The literal (3i) coefficient-one bound is NOT stated: D3a is the M-carrying
  D4R.2′ (PLAN RECONCILIATION, verbatim); M(P̂) = 1 discharge is per-consumer.
- `ShapePrefix.A n N`'s N-STABILITY (L12's N(P̂)) is not a unit: the family fixes
  one N and every law is stated there; the max-over-Pref existence is bridge-side.

## 6. Suggested build order and difficulty profile

  wave A (parallel): D0a, D1a, D1b, D5a, D6a, D6c, D6e, D14a → then D0b, D1c, D0c.
  wave B (encoding): D2a → D2b, D3a.
  wave C (L9 chain): D5b (needs D5a, D6a) → D6b, D6d, D7a, D7c → D7b → D4a → D4b →
    D8 → D9.
  wave D (mass laws): D10 → D11a, D11b → D12 → D13 → D3b; D14b, D15 anytime after
    their deps.
  Hardest: D13 (Finset double counting), D4a (grid pigeonhole), D9 (assembly).
  Everything else easy/medium, ≤ ~40 lines expected; every former hidden sub-lemma
  is now its own unit.

## 7. Codex-audit checklist (statement faithfulness, per campaign gate A)

1. `ShapeRead` retains EXACTLY rev-9 L3's list — BOTH heights (h, u*), the slot
   sets; nothing digit-valued. (u* omission = the pass-10 F1 CRITICAL.)
2. D10/D12/D13 are stated on the INDEX SUM / plain union — no disjointness field
   anywhere (rev-6 F1: fiber disjointness is REFUTED).
3. `TreeModel.cyl` is an iff for EVERY x (D4R-CYL exact, infinite runs included) —
   no termination hypothesis may be added; `mem_realizable` must not grow a
   termination or maximality clause beyond L2's text.
4. The EV equality criterion is pointwise-on-the-event (D13's RHS), never a.e.
5. Kernel conditionality: no unit cites `D4R0K_DERIVATION` as a LEAN discharge —
   (a)/(b) are math-discharged only; the fields stay hypotheses until HC-2. (c)/VP
   appears ONLY in `VerdictModel` (typed, statements only, consumed by nothing here).
6. `topLocus` satisfies vol(⊤) = 1 literally; D0b consumes `C6_thmC_b` verbatim (no
   re-proof of Theorem C content).
7. Statement-fence: `ShapePrefix.A` is a DEFINITION (finding 4) — no unit may
   replace it by a hypothesis; `complete`/`henc`/`hne` may not be weakened or moved
   into docstrings (findings 1/2/5); `Matches.offSlots_forced` is AUDIT-FLAGGED as
   the blueprint's reading of L3's slot retention — reject if it misreads the note.
8. The η = ∅ display (D14a) must stay clear of Theorem C(b) and carry `hN : 1 ≤ N`;
   the empty-Pref dispatch (D14b) likewise (findings 5/6).

## 8. MANIFEST stub

corpus: MovesD · source: §D4-R rev 9 (DUAL-ACCEPTED 2026-07-27) · consumes: MovesC
(C6_thmC_b, JetSetup/SHZ/totalPins/mstar_eq, History/Node, Realizable/
HistoryCoherent) · units: 32 (D0a–c, D1a–c, D2a–b, D3a–b, D4a–b, D5a–b, D6a–e,
D7a–c, D8, D9, D10, D11a–b, D12, D13, D14a–b, D15; 6 AUX) · defs: 1 file ·
open-hypothesis surface: the `Canon` parameter, `PrefFamily.{jet, complete, henc,
sel-semantics}`, `Matches.offSlots_forced` (flagged), `TreeModel.{mem,
prefix_closed, mem_realizable, cyl}`, `VerdictModel` (typed (c)/VP surface), and
the explicit theorem hypotheses `hn` (D3a/D3b), `hN`/`hm` (D14a/D14b) — see §2.

## 9. REV 2 findings→repairs table (audit `MOVESD_AUDIT_CODEX_2026-07-28.md`)

| # | finding (short) | repair |
|---|---|---|
| 1 | PrefFamily satisfiable by `idx := Empty` for any shape; completeness/canonicality "docstring duties" | `PrefSet Canon P` defined (the literal Pref(P̂), with MovesC's `Realizable`+`HistoryCoherent` and the `Canon` parameter); new fields `hcanon`, `complete`; unit D2b proves `range hist = PrefSet` and `C = #PrefSet`. Empty idx now legal EXACTLY when Pref(P̂) = ∅ (the note's L12 allowance) |
| 2 | `enc` an arbitrary injection; `slots` untied to node data — bound assumed, not derived | `encOf` DEFINED from actual `Node.pat` side digits (ambient-field-valued) + `sel` ranks; `henc` restated ON THE ACTUAL DATA (pattern positions k ≤ ℓ_r) inside the structure; `Matches` gains the pool-card and `offSlots_forced` ties; the cardinal bound DERIVED: D1a (digits ∈ pool) + D1b (#pool ≤ p^w) + D1c (#EncTargetP ≤ M·p^W) + D2a (encOf injective) + D3a |
| 3 | D3 dropped `M(P̂) ≤ n^{|P̂|}` | D3a states BOTH clauses: `D4R2'` and `Mfac_le` (hypothesis `hn : ∀ R ∈ P.reads, R.len ≤ n` = the note's "deg R_anch,r ≤ n always", ledgered §2) |
| 4 | A(P̂) undefined; D10/D12/D13 carried ad-hoc `hA`; Corollary D4R.2/A_net unstated | `ShapePrefix.A n N` DEFINED (§3.3, the shape-side fresh-band count — u* enters via the line intercept, the rev-9 point); `Anet` defined; D9 proves L9 as `totalPins = P.A n N`; D10/D12/D13 restated with `P.A n N`, no hA; new unit D3b = Corollary D4R.2 (division-free) |
| 5 | empty shape-prefix forced C = 0 while the note has Pref(∅) = {∅}, C_∅ = 1; display disconnected | `hne : P.reads ≠ []` keeps P̂ = ∅ out of families (the note dispatches η = ∅ FIRST, separately); D14a's `emptyShape_law` now CONNECTED: full box, literal C_∅ = 1, exponent through `ShapePrefix.A` with `A_nil` |
| 6 | empty-case units instantiable at N = 0 (m = 0) against L12's N := 1 | explicit `hN : 1 ≤ N` AND `hm : m = n·N` hypotheses on D14a and D14b (no jet available to supply them); ledgered §2 |
| 7 | TreeModel admits `mem := False` and lacks L2's laws | new field `mem_realizable` (L2: the tree emits only realizable canonical patterns); `mem := False` now UNBUILDABLE for inhabited idx (new unit D0c: every fiber is nonempty — Theorem C(b)'s positive mass — so `cyl` fails); maximality-on-the-family = `cyl` + `complete` (documented); the ∅-root is the D14a dispatch, not a tree field |
| 8 | VerdictModel satisfiable by `leaf := False`; no V/τ/cap | typed fields: `V` (finite, nonempty), `vdict : … → Option V`, `leaf_iff` (leaf ⟺ verdict emitted), `leaf_maximal` AND `leaf_of_maximal` (L2's "no children IFF terminal verdict", both directions — `leaf := False` forces every chain to extend, no longer free), `cap` with `hcap`; stays the OPEN (c)/VP surface, owned by MovesT |
| 9 | D4 chart-uniqueness: display-less hidden multi-lemma unit | chart UNIQUENESS deleted (not needed: `ShapePrefix.A` lives on the raw grid); split into two AUX units with informal statements: D4a (chart bijectivity onto the grid) + D4b (count pushforward) |
| 10 | D6/D7 bundled many plumbing lemmas | unbundled one lemma per unit: D6a (strFrame), D6b (kappaH), D6c (innerslot), D6d (htH), D6e (prevRim), D7a (staircase), D7b (floorH), D7c (slotVal∘fineSlot); D5a (Dwidth_pos) also extracted as AUX |
