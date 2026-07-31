# M12-cl2-route — Problem brief: the weight-charge route form (X.1b in X.3(a) route form)

**Target obligation:** the hypothesis row `cl2_route` of the typed capstone ledger
(`lean/LeanUrat/MovesU/DefsLedger.lean:167`):

```lean
structure UpstreamTyped (n : ℕ) {C : UCarriers n} (KC : KernelCarriers n C) : Prop where
  cl2_route : MovesX.X3aRouteP n KC.XF KC.XK
  ...
```

This is not a `sorry`: it is a named hypothesis of the assembled main theorem
(`theoremU`), to be **discharged at the intended instance** of the abstract data it
quantifies over (see §3 for what that instance is, and §5 for the precise sense in
which "prove the row" must be read — the bare universally-quantified form is known
to be refutable). Date: 2026-07-31.

This brief is self-contained. It re-expands every project-internal name; the reader
is assumed to know p-adic fields, Newton polygons, MacLane/Okutsu–Montes theory and
the index–discriminant formula, but nothing about this repository.

---

## 1. The Lean obligation (normative form)

All definitions from `lean/LeanUrat/MovesX/Defs.lean` (quoted verbatim; line numbers
as of 2026-07-31).

```lean
/-- X.3(a)'s route disjunction, verbatim tags. -/
def X3aRouteP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  (X1aAlignP n X ⟨true, true⟩  ∧ WeightChargeT4P n X K) ∨
  (X1aAlignP n X ⟨true, false⟩ ∧ WeightChargeFullP n X K)
```

with the three component propositions:

```lean
/-- (X1a-ALIGN): "d_cert(H) ≤ ind(f) on every stratum, off disc = 0". -/
def X1aAlignP (n : ℕ) (X : XFamily n) (st : AlignState) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H → dCert st H ≤ (X.gmn p).ind f

/-- X.1b, T4 burden: "#T4(H) ≤ s(n)·v_p(disc f)". -/
def WeightChargeT4P (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H → countPop H .t4 ≤ K.s * vdisc f

/-- X.1b, FULL burden: "#T1-recenterings + #T4 ≤ s(n)·v_p(disc f)". -/
def WeightChargeFullP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (H : XHistory n),
    f ∉ discZero n p → (X.gmn p).inStratum f H →
      countPop H .recT1 + countPop H .t4 ≤ K.s * vdisc f
```

`K.s : ℕ` is a free constant slot (a field of the constants pack `XConsts n`, bound
before any prime is in scope, so it is n-only/p-free by binder order). The
statement is existential in s: any instance whose `s` makes the inequalities true
discharges the row.

## 2. The definition stack, unfolded

### 2.1 The carrier

- `MonicBox n p` = monic degree-n polynomials f ∈ ℤ_p[x] (subtype of `Polynomial ℤ_[p]`).
- `discZero n p` = { f | disc f = 0 } (Mathlib `Polynomial.discr`).
- `vdisc f` = v_p(disc f) ∈ ℕ, via `PadicInt.valuation` (junk value 0 on `discZero`;
  every statement carries `f ∉ discZero`).

### 2.2 Abstract classifier histories

An `XNode n` is a record of "letter fields" (e, ℓ, h, s₀, u₀) ∈ ℕ⁵ with
1 ≤ e, h, ℓ and gcd(e, h) = 1, an optional selection `sel : Option (ℕ × ℕ)`
(`sel = some (g, μ)` with 1 ≤ g, μ and μ·g ≤ ℓ; `sel = none` = terminal), and a
Boolean `isIncrement`, subject to three coherence laws:
- `t2inc`: ℓ = 1 ∧ e ≥ 2 ∧ h ≥ 2 ∧ sel ≠ none → isIncrement = true;
- `t3inc`: ℓ = 1 ∧ e ≥ 2 ∧ h = 1 ∧ sel ≠ none → isIncrement = true;
- `t4rec`: ℓ = 1 ∧ e = 1 ∧ sel ≠ none → isIncrement = false.

`XHistory n := List (XNode n)`. A node is *continuing* iff `sel ≠ none`.

Row classification `rowOf`: terminal → T5; ℓ ≥ 2 → T1; ℓ = 1 with e ≥ 2 →
(h ≥ 2 → T2, h = 1 → T3); ℓ = 1, e = 1 → T4.

Populations (`popOf?`, on continuing nodes only): T1-increment and T2 → `incT12`;
T1-non-increment → `recT1`; T3 → `t3`; T4 → `t4`. `countPop H c` = number of nodes
of H in population c.

Certified depth: `AlignState` = a pair of Booleans ⟨inc, recn⟩. A continuing node
is `certified st` iff (row T1 ∧ ((isIncrement ∧ st.inc) ∨ (¬isIncrement ∧ st.recn)))
∨ (row T2 ∧ st.inc). `dCert st H` = number of certified nodes. Proved in-corpus
(`XB2.dCertMono`): dCert ⟨true,false⟩ H = #incT12(H), and dCert ⟨true,true⟩ H =
#incT12(H) + #recT1(H).

### 2.3 The classifier family and the index interface

```lean
structure GMNIndex (n p : ℕ) [Fact p.Prime] where
  ind : MonicBox n p → ℕ
  inStratum : MonicBox n p → XHistory n → Prop
  p2 : ∀ f, f ∉ discZero n p → 2 * ind f ≤ vdisc f

structure XFamily (n : ℕ) where
  ctx : ∀ (p : ℕ) [Fact p.Prime], XCtx n p       -- a canonical-tree presentation
  gmn : ∀ (p : ℕ) [Fact p.Prime], GMNIndex n p
  gmnLink : ∀ p [Fact p.Prime] (f) (b : (ctx p).Branch f),
      (gmn p).inStratum f ((ctx p).hist b)
```

`XCtx n p` presents, for each f, a rooted tree of "branches" with histories in
`XHistory n` (root history = [], child appends one node), plus
detection/threshold/measure structure not consumed by this obligation. The law
`gmnLink` says: every branch history of f's tree lies in f's stratum. So proving
`WeightCharge*P` requires the count bound **for every history in every stratum** of
the instantiated `inStratum` relation — in particular for every branch history of
the instantiated tree.

## 3. Standard-mathematics reading (the intended instance)

The intended instance (owner: the real-classifier instantiation wave; not yet
constructed in Lean) is the canonical Okutsu–Montes classification tree of f over
ℤ_p, presented as a digit-reading engine: each node is a Newton-polygon side read
in the current frame, with e/h the reduced slope (denominator/numerator), ℓ the
residual length (side degree = e·ℓ, height = h·ℓ), and the selection (g, μ) the
degree and multiplicity of the chosen irreducible factor of the residual
polynomial. `ind` is the Guàrdia–Montes–Nart index ind(f) = v_p([O : ℤ_p[x]/(f)])
(sum over irreducible factors plus pairwise resultant valuations); `p2` is the
classical inequality 2·ind(f) ≤ v_p(disc f) from
v_p(disc f) = 2·ind(f) + Σᵢ v_p(disc Lᵢ) ≥ 2·ind(f).

Row semantics at that instance:
- T1/T2 *increments*: reads that grow the key-polynomial degree (e·g ≥ 2) or sit on
  sides carrying positive certified per-side index (ℓ ≥ 2, or ℓ = 1 with
  e, h ≥ 2). These feed the *certified* depth once the corresponding alignment
  clause (§3.1) is discharged.
- `recT1` (T1-row recenterings) and `t4` (T4): *same-key-degree refinement steps*
  (MacLane refinements): the key polynomial is replaced by another of the same
  degree and its attained value strictly climbs; the read certifies no per-side
  index (their table value is 0 in the T4 case, and un-certified in the recT1
  case). These two populations are exactly what `WeightChargeFullP` charges.

In prose (the source note, MOVES_2026-07-24.md §X.1b, the open kernel named
WEIGHT-CHARGE): *"#{recentering nodes of H} ≤ s(n)·v_p(disc f), with explicit
s(n)"* — burden = the FULL recentering population (T4 and the uncertified
T1-recenterings); the T4-restricted sub-burden is what the left disjunct of the
route consumes.

### 3.1 The alignment legs

`X1aAlignP n X st` ("certified depth ≤ index") is the transport of the per-side
Newton-polygon index table into GMN's per-order index accounting — at state
⟨true,false⟩ it asserts #\{T1/T2-increment nodes of H\} ≤ ind(f) on every stratum;
at ⟨true,true⟩ additionally the T1-recenterings are counted. These are separate
open kernels: the ⟨true,false⟩ state is its own ledger row (`cl15_align`, the same
structure's last row, `DefsLedger.lean:175`) — so for the route's right disjunct
the alignment leg may be consumed as given, and the *new* content of `cl2_route`
is exactly `WeightChargeFullP`. The ⟨true,true⟩ state (needed by the left
disjunct) is NOT a ledger row anywhere; a proof choosing the left disjunct must
supply it too.

## 4. What is already proved in the corpus (verified 2026-07-31)

Consumption side:
- `XG4.x3Series` (PROVED): X3aRouteP + (ns-null) + soundness/additivity riders ⟹
  the per-splitting-type density series identity. This is what `cl2_route` feeds.
- `XC3.x1bReduction` / `XC4.x1bReductionT4` (PROVED): from either disjunct's
  components + history well-formedness, the two-step depth reduction
  2·d_total(H) ≤ (2s+1)·v_p(disc f) + 2·⌊log₂ n⌋.

Assembly/reduction side (all sorry-free, statement-checked):
- `Kernels/KD5.x3aRoute_of_weightCharge_align`: X1aAlignP ⟨true,false⟩ ∧
  WeightChargeFullP ⟹ X3aRouteP (right disjunct, pure pairing).
- `Kernels/KD6`: a carrier `KeyWeightData n` (a history functional
  w : XHistory n → ℚ with values in (1/D)·ℤ, D ≥ 1, monotone along appends,
  climbing ≥ 1/D at every `recT1`/`t4` node) and the PROVED ladder lemma
  #recT1(H) + #t4(H) ≤ D·(w(H) − w([])). The count functional itself (D = 1,
  w = the population count) is a compiled instance, so the carrier costs nothing.
- `Kernels/KD7`: the target Prop `WeightCapP n X KW c` :=
  (∀ p f H, off discZero, inStratum → KW.w H ≤ c·(1 + vdisc f)), and the PROVED
  transport: any budget of the form w ≤ c₁·(1 + ind f) gives WeightCapP c₁ via p2.
- `Kernels/KD10.weightChargeFull_of_ladderCap` (PROVED): KeyWeightData + WeightCapP
  c + REC-DISC + (2·D·c ≤ s) ⟹ WeightChargeFullP.
- `Kernels/WeightChargeRed`: KD2a (PROVED, unconditional): if f mod p is not
  squarefree and disc f ≠ 0 then 1 ≤ vdisc f. KD2 (`recentering_vdisc_pos`):
  REC-DISC — a stratum history with ≥ 1 recentering-population node forces
  1 ≤ vdisc f — proved MODULO the named hypothesis
  `RecImpliesWild n X` := (≥ 1 recentering node in a stratum of f, off discZero ⟹
  f mod p not squarefree). KD3/KD4 (PROVED): the same conclusions from a constant
  per-history recentering bound L (premise currently unsupported at general n; no
  route to it is scheduled).

Adjudication fence (binding on any new work): the X-n3 probe campaign
(verification/x_n3_probes.py, probe_results_2026-07-30.txt) tested the *prefix
cumulative per-node index transport* v_p(disc f) ≥ 2·CUM(j) on exhaustive cubic
boxes (2²⁴ at p = 2, 3¹⁵ at p = 3). Under the certified reading (only μ ≥ 2
engine-descending nodes counted): 0 violations. Under the over-broad reading
(T1-row μ·g = 1 selection nodes also carrying their side's table value): 155,648
violations at p = 2 (and 201,204 at p = 3) — REFUTED, adjudicated 2026-07-29
(tasks 57/58): the refutation confirms the source note's own caution (those nodes
are explicitly NOT certified); no note or Lean statement changed. Moreover the
probe's analytic remark exhibits an exact witness — f = (x−36)(x−117)(x−18),
p = 3: v₃(disc f) = 16 < 18 = 2·CUM — showing that even under the certified
reading the *cumulative table-value* form fails off-box (window reads of one
cluster re-count the same pair differences); only the *count* forms (the Props of
§1, which never sum table values) are the surviving targets.

Numerical evidence for the count form (same probe file): max over both exhaustive
cubic boxes of #recenterings/v_p(disc f) = 1/3 (sealed candidate s(3) = 2 passes
with room); on the quartic RS-conditioned cylinder 2²⁶ the max ratio is 1/10, max
recentering run length 2. KD9 (ladder/cap probe, 2026-07-30, exit 0): no
zero-gain recentering over ~3.9M recentering members; empirical minimal cap
constant c = 2/7 (cubic box) resp. 8/25 (quartic cylinder), declining in vdisc.
KD1 (REC-DISC probe): clean on both boxes.

## 5. What a proof must deliver

**The bare ∀-instance statement is FALSE** (recorded countermodel shape,
`Kernels/KD7.lean` header and `WeightChargeRed.lean` header): `inStratum := λ _ _,
True` with `ind := 0` satisfies every `GMNIndex`/`XFamily` law, and any f with
unit discriminant plus a history containing one recentering node violates
`WeightChargeFullP` for every s. So "prove `cl2_route`" means: prove `X3aRouteP`
**at the real classifier instance**, i.e. supply the mathematics that makes the
count bound true of the canonical Okutsu–Montes/digit-reading tree, in a form the
instantiation wave can transcribe. Acceptable shapes, in decreasing directness:

1. A proof, at the intended instance semantics, of
   **(WC-full)**: for every prime p, every monic f ∈ ℤ_p[x] of degree n with
   disc f ≠ 0, and every branch history H of the canonical classification tree of
   f: #\{same-degree refinement nodes of H\} ≤ s(n)·v_p(disc f), for some explicit
   n-only s(n) — together with X1aAlignP ⟨true,false⟩ taken as given (it is the
   separate row `cl15_align`). Via KD5 this closes the right disjunct.
2. Equivalently, through the built reduction (KD10 + KD6 + KD2): exhibit, at the
   intended semantics, (a) a key-weight functional satisfying the `KeyWeightData`
   laws whose cap w(H) ≤ c·(1 + v_p(disc f)) is provable (`WeightCapP`), and
   (b) the `RecImpliesWild` implication (a recentering forces a repeated factor of
   f mod p). Then s(n) = any integer ≥ 2·D·c.
3. The left disjunct instead: WeightChargeT4P (T4 population only) PLUS
   X1aAlignP ⟨true,true⟩ — note this route must additionally discharge the
   recentering alignment clause, which no other ledger row supplies.
4. A faithfulness-audited literature citation implying (WC-full) for the canonical
   tree (exact statement match required; note the tree here is the project's
   canonical digit-reading tree, not any particular published algorithm run).

Any proof must respect the adjudicated reading: no step may charge a per-node
table value cumulatively along a branch (the refuted mechanism); population
*counts* are the only licensed per-node quantities.

Constants discipline: s(n) must be independent of p, N, and the history — the
binder order of `XConsts` enforces this in Lean. Explicit growth in n is fine.
