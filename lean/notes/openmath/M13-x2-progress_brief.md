# M13-x2-progress — problem brief (neutral, self-contained)

**Obligation.** Five hypothesis rows of the project's capstone theorem (fields
`cl3_aff`, `cl3_cap`, `cl3_progress`, `cl3_tails`, `cl3_bridge` of the structure
`UpstreamTyped` in `lean/LeanUrat/MovesU/DefsLedger.lean:166`) assert five
properties — named (X2-AFF), (X2-CAP), (X.2)-linear, (X2-TAILS), (X2-BRIDGE) —
of the canonical p-adic polynomial-factorization classifier (an Okutsu–Montes /
MacLane key-polynomial engine). They are stated as `Prop`s over an abstract
interface; **proving a row** means proving the `Prop` for the intended concrete
instance of that interface (the real classifier), or deriving it from
precisely-stated, citable properties of Okutsu–Montes theory. All constants
must depend on the degree n only — they are quantified BEFORE any prime p.

This brief gives (1) the ambient definitions unfolded to standard mathematics,
(2) the five target statements (standard form + Lean verbatim), (3) what is
already proved around them, (4) what a proof must deliver.

---

## 1. Ambient objects

Fix n ≥ 2 and a prime p. The **monic box** is
`MonicBox n p := { f : Polynomial ℤ_[p] // f.Monic ∧ f.natDegree = n }`,
i.e. monic degree-n polynomials over ℤ_p, carrying the natural probability
content: identifying f with its n lower coefficients, the level-N box is
(ℤ/p^N)^n with normalized counting measure, and a set's content is its
Haar/cylinder measure. In the Lean interface the content appears as an abstract
finitely-subadditive normalized set function `frac` (see §1.3).

### 1.1 The classifier and its branch histories

The intended classifier is the canonical OM/MacLane factorization engine: for
each f it grows a rooted tree whose nodes are "reads" — each read inspects one
side of a Newton polygon of some order (the polygon of the φ-development of f
with respect to the current key polynomial φ and current inductive valuation),
selects an irreducible factor (with multiplicity) of the side's residual
polynomial, and either descends (refines the key: a same-degree recentering, or
a key-degree increment) or halts with a certificate (an irreducibility /
Hensel-type verdict for one factor of f).

A **node** ν records the read's letter data, in the read's own frame (its own
inductive-valuation normalization). Lean form (`MovesX/Defs.lean`):

```lean
structure XNode (n : ℕ) where
  e : ℕ; ell : ℕ; h : ℕ; s0 : ℕ; u0 : ℕ
  sel : Option (ℕ × ℕ)          -- selection (g, μ); none = terminal read
  isIncrement : Bool
  epos : 1 ≤ e; hpos : 1 ≤ h; ellpos : 1 ≤ ell
  hcop : Nat.Coprime e h
  selBound : ∀ g μ, sel = some (g, μ) → 1 ≤ g ∧ 1 ≤ μ ∧ μ * g ≤ ell
  t2inc : ell = 1 → 2 ≤ e → 2 ≤ h → sel.isSome → isIncrement = true
  t3inc : ell = 1 → 2 ≤ e → h = 1 → sel.isSome → isIncrement = true
  t4rec : ell = 1 → e = 1 → sel.isSome → isIncrement = false
```

Standard meaning: the read side has slope −h/e in lowest terms (h = height, e =
ramification index of the side, both in the node's own frame coordinates),
horizontal length e·ℓ (so ℓ = residual degree of the side); (s0, u0) locates
the side on the polygon (slot coordinates); the selection (g, μ) is the degree
and multiplicity of the chosen irreducible factor of the residual polynomial
(μ·g ≤ ℓ); terminal reads (certificates) carry `sel = none`. `isIncrement`
distinguishes key-degree increments from same-degree recenterings.

A **branch history** is a finite list `XHistory n := List (XNode n)`. Derived
quantities (Lean names, used verbatim in the targets):

- `dTotal H` = number of continuing nodes (sel ≠ none) — the **depth**;
- `sumH H` = Σ over ALL nodes of H (continuing and terminal) of h — the
  **height sum**;
- `maxH H` = max over all nodes of h (0 for the empty history);
- `HistWF n H`: only the last node may be terminal, and the product of e over
  continuing increment nodes is ≤ n (the degree budget Π eᵢ ≤ n along a
  branch: key degrees multiply by at least e at each increment and never
  exceed n).

### 1.2 The per-prime context (the abstract classifier interface)

`XCtx n p` packages, as free data constrained by named laws, everything the
targets mention. Relevant fields, with their standard meaning:

- `Branch f` — the type of branches of the canonical tree of f; `hist b` — the
  branch's history (a `XHistory n`, well-formed: `wf`); `root`, `parent`,
  `children` (finite menus), and `reach` (every branch reaches the root by
  parent steps); `complete b` — b is the full branch of a complete halted tree.
- `IsLeafB C b := C.children b = ∅` (leaf-terminated branch).
- `nsTrack : XNode n → Prop` — the node lies on a "non-standard" track (a
  measure-zero exceptional family, indexed countably by `nsIdx`/`nsFiber`,
  covering all trees with an ns-leaf: `nsCover`). `NsFreeB C b` — no node of
  `hist b` is on an ns track.
- **The fourth-piece family** (the guard of the targets):
  `FourthPieceB C b := (IsLeafB C b ∨ ∃ b', complete b' ∧ b prefix of b') ∧ NsFreeB C b`
  — (τ-ns)-free finite branches: leaf-terminated or a prefix of a complete
  branch.
- `threshold b : ℕ` — the least N such that the **stratum** of `hist b` (the
  set of f′ in the monic box whose canonical tree contains this branch history)
  is a finite union of level-N digit cylinders (i.e. membership is determined
  by f′ mod p^N). This is "Theorem 2.1's per-stratum N₀" in the project's
  decomposition note — the standard fact that an OM type/stratum is a
  finite-precision condition on the coefficients.
- `capDetectable b : Prop` (decidable), `detCap b : ℕ` — the branch's own
  leaf-detection **cap**: the extra levels needed, beyond the threshold, to
  certify the leaf's verdict cell. Standard content ("TB-CAP"): a Hensel-type
  (τ-hen) leaf is detected with cap 1; an irreducibility-type (τ-irr) leaf has
  a per-realized-cell cap indexed by the halting read's own levels. The total
  cap is `capHB C b := if capDetectable b then detCap b else 0`.
- `DetectedAt b N` and the law `detectBranch`: a leaf-terminated, ns-free
  branch is detected at every N ≥ threshold b + capHB b.
- `Undec N : Set (MonicBox n p)` — the level-N **undecided set**: f whose
  level-N digit data does not certify a complete halted tree with every leaf
  cap-detected. Pinned by `undec_spec`:
  f ∉ Undec N ↔ (Branch f finite ∧ every leaf branch DetectedAt N);
  `undec_antitone` (decided sets grow with N).
- `frac : Set (MonicBox n p) → ℚ` — the box content: normalized
  (`frac_univ = 1`), nonneg, monotone, finitely subadditive, with countable
  null-union (`frac_iUnion_null`) and monotone convergence along `Undec`
  (`frac_inter_tendsto`), plus the discriminant-tail comparison `vdisc_le_tail`.
- `TallEvent C h* := { f | ∃ b, ∃ ν ∈ hist b, h* ≤ ν.h }` — some read of some
  branch has height ≥ h*. `DeepEvent C d := { f | ∃ b, d ≤ dTotal (hist b) }`.
- `InfTree C := { f | ¬ Finite (Branch f) }`; `discZero n p` = zero
  discriminant locus.

`XFamily n` supplies one `XCtx n p` per prime (plus a per-prime index interface
`gmn` used by other rows, not by these five). `XConsts n` carries the n-only
constants: s, c₀ ≥ 0, c_cap ≥ 0, target slopes c_d > 0, c_d′, c_h > 0, c_h′,
and tail constants C_T > 0, c_T > 0 (reals). **Binder order enforces
p-uniformity: the constants exist before any p is mentioned.**

### 1.3 The five targets (Lean verbatim, `MovesX/Defs.lean`, then standard form)

```lean
def X2AffP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f),
    FourthPieceB (X.ctx p) b →
      ((X.ctx p).threshold b : ℚ) ≤ 1 + K.c0 * sumH ((X.ctx p).hist b)

def X2CapP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f),
    FourthPieceB (X.ctx p) b → (X.ctx p).capDetectable b →
      ((X.ctx p).detCap b : ℚ) ≤ K.ccap * (1 + sumH ((X.ctx p).hist b))

def X2ProgressP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : MonicBox n p) (b : (X.ctx p).Branch f) (N : ℕ),
    FourthPieceB (X.ctx p) b → N < (X.ctx p).threshold b + capHB (X.ctx p) b →
      K.cd * N - K.cd' ≤ (dTotal ((X.ctx p).hist b) : ℚ) ∨
      K.ch * N - K.ch' ≤ (maxH ((X.ctx p).hist b) : ℚ)

def X2TailsP (n : ℕ) (X : XFamily n) (K : XConsts n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (hstar : ℕ),
    ((X.ctx p).frac (TallEvent (X.ctx p) hstar) : ℝ) ≤ K.CT * (p : ℝ) ^ (-(K.cT * hstar))

def X2BridgeP (n : ℕ) (X : XFamily n) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ),
    ((X.ctx p).Undec N ⊆ discZero n p ∪ (⋃ i, (X.ctx p).nsFiber i) ∪ InfTree (X.ctx p) ∪
      { f | ∃ b, IsLeafB (X.ctx p) b ∧ NsFreeB (X.ctx p) b ∧
            N < (X.ctx p).threshold b + capHB (X.ctx p) b }) ∧
    (X.ctx p).frac { f | f ∈ (X.ctx p).Undec N ∧ ¬ ∃ b, IsLeafB (X.ctx p) b ∧
            NsFreeB (X.ctx p) b ∧ N < (X.ctx p).threshold b + capHB (X.ctx p) b } = 0
```

Standard form. There exist n-only constants such that for every prime p:

- **(X2-AFF)** threshold(H) ≤ 1 + c₀(n)·Σ_{r∈H} h_r on the fourth-piece family
  (the sum over ALL reads, continuing and terminal).
- **(X2-CAP)** cap(H) ≤ c_cap(n)·(1 + Σ_{r∈H} h_r) on cap-detectable
  fourth-piece branches.
- **(X.2)-linear ("progress")** if a fourth-piece branch is undetected at level
  N (i.e. N < threshold + cap), then depth(H) ≥ c_d·N − c_d′ or
  max-height(H) ≥ c_h·N − c_h′ — a **deep-or-tall dichotomy at rates linear
  in N**, with both slopes positive. (Intended reading: the classifier's
  potential drops linearly along non-terminating paths.)
- **(X2-TAILS)** the content of the tall event {some read has h ≥ h*} is
  ≤ C_T(n)·p^{−c_T(n)·h*}.
- **(X2-BRIDGE)** Undec(N) is covered by {disc = 0} ∪ (ns fibers) ∪ (infinite
  tree) ∪ {∃ leaf-terminated ns-free branch with threshold + cap > N}, and the
  part of Undec(N) with no such witnessing branch is null.

## 2. What is already proved in the corpus

All in `lean/LeanUrat/MovesX/`, sorry-free, Lean-core axioms unless noted.

- **XD.2 `x2hypCount`** (unconditional): for well-formed H,
  `sumH H ≤ (dTotal H + 1) * maxH H`.
- **XD.3 `x2hypDichotomy`** (pure arithmetic): M < (d+1)·m → M < (d+1)² ∨ M < m².
- **XD.4 `x2hypAssembled`** (the **√N form of progress**, PROVED): given
  `X2AffP` and `X2CapP`, an undetected-at-N fourth-piece branch has
  (N − 1 − c_cap) < (c₀+c_cap)·(dTotal+1)² or (N − 1 − c_cap) < (c₀+c_cap)·(maxH)².
  I.e. deep-or-tall at rate √N. **The open content of `cl3_progress` is
  exactly upgrading √N to linear.**
- **KE2 `x2Aff_of_thresholdStep`**: `X2AffP` follows from a named per-move law
  `ThresholdStep` (root threshold ≤ 1; each child read moves the threshold by
  ≤ scale·parent + C_move·h, scale = e at continuing increments else 1), with
  c₀ ≥ n·(C_move + 1). The law's instance at the real classifier is open.
- **KE3 `x2Cap_of_capStep`**: `X2CapP` follows from a named accumulation law
  `CapStep` (root cap ≤ C_root; each read adds ≤ C_cell·(1+h)), with
  c_cap ≥ C_root + 2·C_cell. Instance open.
- **KE5 `x2Tails_of_route`**: `X2TailsP` follows from a named carrier
  `TailsRoute` (a per-depth first-tall-read price from the pool/mass bound, a
  per-depth species-menu count ≤ menu^d, and a summability field dominating the
  windowed series by C_T·p^{−c_T·h*}). Instance open; this row's mathematics is
  a measure/tail estimate owned by a different note (§H-DOMAINS M4a cones).
- **KE6 `x2Bridge_cover`** (PROVED, unconditional over the interface): clause 1
  of `X2BridgeP` — the four-set cover — from `undec_spec` + `nsCover` +
  `detectBranch` alone. **KE7 `x2Bridge_assembled`** (PROVED): full `X2BridgeP`
  given 2 ≤ n, the route disjunction `X3aRouteP` (an X.1-side row, not in this
  family) and `NsNullP` (ns fibers null — ported paper proof, KE1).
- **KE9 `x2Progress_of_pricing`** (PROVED): `X2ProgressP` follows from a named
  law `ProgressPricing`: threshold + cap ≤ C_prog·(1 + dTotal + maxH) jointly,
  on the fourth-piece family, with slopes c_d = c_h = 1/(2C_prog) and
  intercepts 1/2. The instance of `ProgressPricing` is the open content.
- Census gates (n = 2 and n = 3 exhaustive boxes, p ∈ {2,3};
  `verification/results/ke11_affine_envelope.json`): the affine faces of
  AFF/CAP hold in-census with empirical minimal c₀ = n and per-move constant
  C_move = n; no super-affine growth family detected. These are candidate
  stress records, not proofs.

## 3. What a proof must deliver

1. For each row: either a rigorous derivation of the `Prop` from standard,
   precisely-cited Okutsu–Montes/MacLane theory (respecting the abstract
   interface's reading of threshold/cap/heights above), or a proof of the
   corresponding named instance law (`ThresholdStep`, `CapStep`, `TailsRoute`,
   `ProgressPricing`) for the real classifier — stated so the eventual concrete
   instance (`XCtx` builder) can discharge it. Constants n-only, before p.
2. For `cl3_progress` specifically: linear rates. The √N form is settled;
   a proof must either establish the linear dichotomy (equivalently, an affine
   bound of threshold + cap in (1 + dTotal + maxH)), or refute it (a family of
   branches, over any primes, with threshold + cap ⨸ O(1 + dTotal + maxH) —
   note the Prop is existential in the constants, so refutation must beat
   EVERY n-only constant).
3. Respect the guards: fourth-piece only (ns-free finite branches); the cap's
   0-convention off cap-detectable branches; empty-history conventions
   (maxH ∅ = 0). No claim is needed at non-fourth-piece branches.
4. Heights/frames: h is the side height in the node's OWN frame (the current
   inductive valuation's normalization, integer value group, gcd(e,h) = 1),
   NOT the p-adic absolute slope; any argument must track frame changes at
   increments (the degree budget Π e ≤ n is available via `HistWF`).
