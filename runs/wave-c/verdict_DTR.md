# UNIT DTR — VERDICT: THE DECISION TRANSPORT ACROSS THE RECENTRING LANDED (both directions, from ONE named pointwise law), THE OM TOWER STEP ISOLATED AS `CellTypeScalingAt D` WITH ITS `D = 1` INSTANCE MACHINE-CHECKED, AND THE PRIME-MASS `PowerFullSpanLaw` FIRED UNCONDITIONALLY — the whole file PURE LEAN CORE, cite-free (2026-08-30)

**Deliverable:** `leanfinal/Uniformity/ChapI/IFCG47.lean` (663 lines, ZERO sorries,
zero errors, zero warnings; 10 AxCheck footer lines).  **Axiom fence, better than
charged:** every declaration — the scaled-type calculus, the named Prop, BOTH transport
directions, the iff, the `D = 1` witness, the prime emptiness, and the prime-mass law
fire — is **pure Lean core `{propext, Classical.choice, Quot.sound}`.  Neither B.42 nor
C.33 occurs anywhere in the file's footprint.**  One-line aggregator import added to
`Uniformity/ChapI.lean` after IFCG45 (IFCG46's line is another unit's; that file
untouched).  No git ops.
Verification: per-increment `timeout 580 lake env lean Uniformity/ChapI/IFCG47.lean`
(6 increments, each GREEN before the next; final: zero diagnostics beyond the 10
expected axiom prints); targeted `lake build Uniformity.ChapI.IFCG47` GREEN (8958
jobs); aggregator `lake env lean Uniformity/ChapI.lean` GREEN with the line wired.

## ★★★ THE HEADLINE — the transport theorem, exactly as PSL4 supplied it

    theorem transport_decidedAt_iff (hCTS : CellTypeScalingAt D)   -- ★★★ THE IFF
        (hπ …) (hw : residue O w ≠ 0) (he' : 2 ≤ e') (hDN : D < N)
        (hF : MinFaceAt c 1 e')                                    -- the full-span frame
        (hbox : cellTransport hπ hw he' D N c ∈ alphaBox π w e' D (e' * N))
        (σ' : FactorizationType) :
        DecidedAt (AdjoinRoot (eisKey π w e')) D σ' (e' * N) (cellTransport … c)
          ↔ DecidedAt O (e' * D) (scaleType e' σ') N c

uniform in `q, e', D, σ', N`, every complete DVR — **level scales by exactly `e'`
(`N ↦ e'·N`), type by exactly `(e, f) ↦ (e'·e, f)`** (`scaleType`, §0): the two
bookkeepings of the classical tower step `e(L/K) = e(L/K')·e(K'/K)`, `f(L/K) = f(L/K')`
at the totally ramified Eisenstein stage (`q' = q` by `eis_residueCard`).  Both
directions are PROVED from the ONE pointwise law: inbound (`O'`-decided ⟹ `O`-decided)
because every `O`-lift's transform is an `O'`-lift of the transported class
(`cellTransport_apply` + level exactness); outbound because every `O'`-lift's
reassembly is an `O`-lift (`cellTransport_symm_apply`), the law reads
`devT (reassT G) = G`, and `scaleType`-INJECTIVITY (§0, `e' > 0`) converts back.

## ★★ THE NAMED REMAINDER — the OM tower step, isolated pointwise

    def CellTypeScalingAt (D : ℕ) : Prop :=      -- the exact surviving open math
      ∀ O (complete DVR) π w (hπ hw) e' ≥ 2, ∀ g monic of degree e'·D,
        (raw purity lattice: π^(⌈(e'D−j)/e'⌉) ∣ g.coeff j, j < e'D) →
        (deep box: α^(e'(D−t)+1) ∣ mk (dev (eisKey π w e') g t), t < D) →
        typeOf g = scaleType e' (typeOf (devT (eisKey π w e') D g))

* **The charge's literal mechanism is FALSE and was refuted before designing**: `devT`
  is NOT multiplicative — `devT(x)·devT(x) = α² = −wπ` while `devT(x²) = Y − wπ` at
  `eisKey = x² + wπ` (carry terms in the φ-adic development).  No unconditional
  "factorization pulls back through the bijection" exists; the correspondence is a
  CELL theorem (deep box = the carries are negligible), exactly as stated above.  The
  decided-class transport dodges multiplicativity entirely — that is why §2 lands NOW.
* ★ **`cellTypeScalingAt_one : CellTypeScalingAt 1` — PROVED** (the depth-1 witness,
  ~200 lines): at `D = 1` the lattice + box force `g` EISENSTEIN with `v(g₀) = 1`
  exact (`v(g₀ − wπ) ≥ 2`, `w` a unit), the x-frame polygon is the single
  slope-`1/e'` side `[0, e']` with linear residual (suppVal = e' computed from both
  ends), and IFCG35's UNCONDITIONAL `residualLeafLaw_one` fires:
  `typeOf g = ⟨{(e', 1)}⟩ = scaleType e' ⟨{(1, 1)}⟩` (transform monic linear).  This
  machine-checks the centre-sign, level-scale, and `(e,f)`-scale conventions.
* Truth support at `D ≥ 2`: hand-verified tame instance (e' = 2, D = 2, q odd:
  `g = (x² + w₁π)(x² + w₂π)`, `wᵢ ≡ w`, transform splits `(Y + w₁π)(Y + w₂π)` over
  `O'`, `{(1,1),(1,1)} ↦ {(2,1),(2,1)}` ✓); the general statement is the classical
  Montes/Okutsu induction step (FGMN — `docs/references/FGMN_residual_ideals_2015`).
  `powerSectorFull` produces ONLY `D = k·deg ψ ≥ 2`, so `D ≥ 2` is the census-relevant
  range and is genuinely the deep-wild tower (PROJECT_STATE standing obligation 2).

## ★★★ THE PRIME-MASS FIRE (unconditional, new census closure)

    theorem powerSectorFull_eq_empty_of_prime : m.Prime → powerSectorFull O π m σ M = ∅
    theorem powerFullSpanLaw_of_prime        : m.Prime → ∀ σ, PowerFullSpanLaw m σ  -- ★★★

Full span forces `m = e'·(k·deg ψ)` with `e' ≥ 2` (fractional face, `1 ≤ h < e'`) AND
`k ≥ 2` (proper power residual) — a factorization into two factors ≥ 2 — so at prime
mass the full-span sector is EMPTY and the law holds with rational pair `(0, 1)`.
PSL4's census row left `PowerFullSpanLaw` on the premise list at ALL masses; **at the
prime ramified-remainder masses `m = 5, 7, 11, 13, …` it is now CLOSED** (the first
mass where the full-span law has content is `m = 4 = 2·2`; at the front's `e ≥ 5`
range: `m = 6, 8, 9, 10, 12, …`).

## The three charge items, disposition

**(1) STATE — done, sharpened.**  `scaleType` (§0) pins the bookkeeping with degree
scaling (`scaleType_degree : degree = e'·degree`), identity (`scaleType_one`), tower
composition (`scaleType_scaleType : scaleType e₁ ∘ scaleType e₂ = scaleType (e₁e₂)` —
the associativity of `e`-multiplicativity), and injectivity at `e' > 0`.  The corpus's
`typeOf` supports the composition with NO new definitions.  Consistency check against
ER4's census: at `e' = 2` the three degree-2 types `{(1,1),(1,1)}, {(1,2)}, {(2,1)}`
scale to EXACTLY ER4's three dd-σ's `{ramPair, type22, type41}` — the dd rows exist at
precisely the `scaleType`-image types.

**(2) PROVE — done at the decision level; the pointwise heart isolated and witnessed.**
The transport needed splitting into (a) the decided-class equivalence — PROVED both
ways (`decidedAt_of_transport_decidedAt`, `transport_decidedAt_of_decidedAt`,
`transport_decidedAt_iff`) — and (b) the pointwise type-scaling on the cell — the
genuine OM tower step, named `CellTypeScalingAt D`, proved at `D = 1`, open at
`D ≥ 2`.  This split is FORCED by mathematics (devT non-multiplicativity), not a
convenience: any "uniqueness half transports through the bijection" argument still
needs (b) per lift.

**(3) FIRE — one unconditional fire; the two conditional reaches stated exactly.**
* `PowerFullSpanLaw m σ` at PRIME `m`: FIRED (Lean-core, no premises).
* `PowerFullSpanLaw m σ` at composite `m`: the discharge now rests on exactly
  {`CellTypeScalingAt D` for `D ∣ m, 2 ≤ D ≤ m/2`} + the face/centre partition
  assembly (partition `powerSectorFull` by `minFaceAt_unique` + centre, read cells by
  IFCG44 §4's `fullSpan_resPoly_iff_box → cellTransport_mem_alphaBox_iff`, transport
  the decided intersection by THIS unit's iff, count by `cellTransport_card_image` +
  `card_alphaBox`, sum by `recentred_decidedSeq_tendsto` at
  `φ = tendsto_transport_level` + `ZcURLim_sum`).  The assembly is a bookkeeping unit
  against landed API; the transport is no longer its missing leg.
* ER4's dd terms (`ZcURLim (e1DdDecFam σ)`, σ ∈ {ramPair, type22, type41}): the dd box
  IS the `m = 4, e' = 2, D = 2` full-span shape (`e1DdBox` = E1 classes with slope-1/2
  residual `L²`, `L` monic linear — the key `X² − bπ` = `eisKey π (−b) 2`), so the
  terms REDUCE through this unit's iff to `CellTypeScalingAt 2` + the E1-frame
  conversion (`e1Box → MinFaceAt c 1 2` + centre partition + `alphaBox` membership) +
  the mass-2 decided value laws at `O'` (closed) via `recentred_decidedSeq_tendsto`.
  NOT fired: `CellTypeScalingAt 2` is open (the first wild instance), and the frame
  conversion is ER4-successor bookkeeping.

## THE EXACT SURVIVING CENSUS SET after DTR

1. **`CellTypeScalingAt D`, `D ≥ 2`** (§1's named Prop) — THE OM tower step, the one
   open mathematics of the full-span/dd territory.  First consumers: `D = 2` for
   ER4's dd terms and `m = 4`; the divisor set `{D : D ∣ m, 2 ≤ D ≤ m/2}` for each
   composite mass.
2. **The full-span assembly unit** (composite `m`): face/centre partition + decided
   count summation, all instruments landed (IFCG44 §§3–6 + this unit's §2).
3. **The dd assembly unit** (`m = 4`): `e1DdBox → (MinFaceAt, alphaBox)` conversion +
   centre partition.
4. Unchanged: `PowerConvolutionDefectLaw` (IFCG38-genre converse),
   `SplitConvolutionDefectLaw`, `LeafSectorLaw` cell count, the five `e = 4` even-ram
   remainder laws' own opens (`E1IrrLeafDecision`, depth-0 box limits, E2 recursion),
   `e ≥ 5` σ-ramified laws, `UnramifiedBlockBridge`.

## File map (`leanfinal/Uniformity/ChapI/IFCG47.lean`, 663 lines)

§0 `scaleType`, `scaleType_data/degree/one/scaleType/injective` ·
§0b kit (private replicas: `isKey_X`, `monicPoly_coeff_self`, `mem_sideSet_iff'`,
`eisKey_degree'`) · §1 `CellTypeScalingAt` (THE named remainder), `CellTypeScaling`,
★ `cellTypeScalingAt_one` (the depth-1 witness) · §2 ★★ `decidedAt_of_transport_decidedAt`,
★★ `transport_decidedAt_of_decidedAt`, ★★★ `transport_decidedAt_iff` ·
§3 ★ `powerSectorFull_eq_empty_of_prime`, ★★★ `powerFullSpanLaw_of_prime` ·
AxCheck footer (10 lines, ALL pure Lean core).  Imports: `IFCG44` (transitively
IFCG35/37/39/43).  Aggregator: one import line in `Uniformity/ChapI.lean`.

## Repair log (4 error rounds over 6 increments; every statement landed as designed)

1. `ext` on `FactorizationType` recurses into `Multiset.count` — use
   `apply FactorizationType.ext`; `dev` lives in `Uniformity.Density.Leaf` (B02), not
   `.Induction`.
2. THE UNIVERSE FENCE (ER4's logged #5, second confirmed contact): `CellTypeScalingAt`
   quantifies `O : Type` (ZcURLim's convention) — §2's consumer section is
   `{O : Type}`, and the `Type*` attempt also produced a misleading whnf-timeout
   collateral error.  NOTE FOR SUCCESSORS: a heartbeat timeout co-reported with a
   universe mismatch is usually the mismatch's shadow.
3. `Nat.mul_eq_one` name drift → a `Nat.mul_le_mul_left` bound + omega;
   ZcURLim's body is not beta-reduced in `Tendsto.congr` goals — `show` the reduced
   form first.
4. `Polynomial.dvd_iff_modByMonic_eq_zero` doesn't exist → `Polynomial.modByMonic_self`
   (whose rw leaves a `Monic` side goal — discharge after the chain);
   `ENat.add_one_le_of_lt` doesn't exist → `(ENat.add_one_le_iff (ENat.coe_ne_top 1)).mpr`;
   `Finset.self_mem_range_succ` needs its explicit argument; `mul_le_mul_left'`
   deprecated → `mul_le_mul' le_rfl`.

Traps avoided by design (PSL3/PSL4/ER4/XHS logs consulted): all ℕ∞ smul bounds via the
`nsmul_eq_mul`/`mul_le_mul'` route (no primed-lemma dependence); `reassVec`'s
`0 < e'` proof spelled as `Nat.zero_lt_two.trans_le he'` everywhere
(`cellTransport_symm_apply`'s exact term — proof-irrelevant but rw-syntactic);
`e' * (…)` products kept out of omega via literal-form hypotheses; the `suppVal` inf
computed by two one-sided bounds with the `j = e'` case dispatched by `le_add_self`
(no valuation needed at the top corner).

## Consumption notes for the discharge units

* **The `CellTypeScalingAt D` discharge** (the OM step): the D=1 proof is the
  template's base — lattice+box ⟹ frame pins ⟹ leaf law.  At `D ≥ 2` the analogous
  route needs the depth-2 residual apparatus (the transform's own Newton polygon over
  `O'` refines the decision); C136's composedKey/refinement calculi and C133mh's
  graded frontier are the corpus's deepest instruments; FGMN's Theorem of the product
  is the literature form — a faithful `[cite:FGMN]` import at exactly this Prop is the
  honest alternative if the wild proof stalls (owner gate (b) applies).
* **The assembly units** consume `transport_decidedAt_iff` POINTED AT A CLASS: supply
  `MinFaceAt c 1 e'` from `powerSector_data` + `minFaceAt_unique`, `hbox` from
  IFCG44's `fullSpan_resPoly_iff_box → cellTransport_mem_alphaBox_iff` chain (mind
  PSL3's sign convention: centre `z`, key `eisKey π (−z) e'`), `hDN : D < N` from the
  level supply `N = M + m` with `M` large — the `M < D` head of the sequence is
  finite and drops out of every `Tendsto`.
* `scaleType_scaleType` is the DEPTH-≥2 tower's composition instrument (two-stage
  recentrings compose associatively) — landed now so the deep tower needs no new
  bookkeeping lemma.
