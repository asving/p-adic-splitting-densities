import Uniformity

/-!
# Chapter G — BASE CASES AND MENUS: the leanspec interface (design stage 0e)

Every SIGNATURE of `blueprint/CHAP-G_base_cases_menus.md` (78 nodes, 110 declarations), landed in
the isolated `leanspec` environment **before** the chapter-G fleet fires, in the blueprint's
topological order (node order `G.01 … G.77`; `G.78` is a `#print axioms` census block, not a
declaration).

**What is real and what is a stub.** Per stage-0e rule 1 (blueprint §12): the chapter's new
definitional layer lands as REAL BODIES — 26 `def`s, the `CertFamily` structure and the
`CubicFamilyIndex` inductive. The 81 theorem signatures land as `axiom` stubs. After a node lands
in `leanfinal` its normalised environment type is diffed against the stub here.

**Amended against blueprint AMENDMENT 2026-08-15** (the four §14 items adjudicated at this gate):
G.23a `card_resStratum` is **withdrawn — its statement is refuted** — and is commented out below
rather than signed; G.28 `decidedAt_split_of_sep` carries the amended window hypothesis
`2 * k + 1 ≤ N`. Signed contract count: **109** declarations (110 minus G.23a).

**Amended against blueprint AMENDMENT 2026-08-15, second append** (defects D2 and D3 cured):
G.62b `CubicFamilyIndex.schema` is re-signed as a **real `def`** carrying the derived 53 → 33
assignment (§A-5) — it is the 26th real body, and the `axiom` count drops 82 → 81 accordingly;
G.52g `c3_pairwise_ne` is re-signed with the **ten inequalities** in place of the placeholder
`True` (§A-6). Declaration count unchanged at **109**.

**This file is never imported by `leanfinal` or `leancheck`.** It carries `axiom`s by design; it
is an interface contract, not mathematics. Nothing here is proved.

**Environments.** The blueprint's ENV-A is the section `variable` block below; ENV-A' is ENV-A
with `(hπ : Irreducible π)`, which every node that names `π` takes explicitly; ENV-B adds
`[IsAdicComplete (maximalIdeal O) O]`, which every ENV-B signature carries inline; ENV-C binds its
own `(K : Type*) [Field K] [Finite K]` inline.

**Blueprint defects found at stub-landing** (stage-0e gate, 2026-08-14; recorded here and in the
0e report, NOT repaired in the blueprint — rule 3):

* **D1 — G.18 `tangCert`, ELABORATION FAILURE (verbatim form).** The two occurrences of
  `resFactor _ g` leave an unsynthesizable proof placeholder:
  `error: don't know how to synthesize placeholder for argument 'h'` with goal
  `(t + 1) / 2 ≤ t + r`. Landed below with the minimal repair — the same `(by omega : …)` proof
  the blueprint already writes on the left-hand side of each equation — which is type-identical by
  proof irrelevance. The blueprint entry needs the placeholder filled in.
* **D2 — G.62b `CubicFamilyIndex.schema`, DEF WITH NO BODY. ✅ CURED 2026-08-15 (blueprint
  AMENDMENT §A-5).** The SIGNATURE block declared a `def … : CubicFamilyIndex → Fin 33` and
  supplied no body, and the body was underdetermined by the prose (which of the 53 formal families
  collapse onto which of the 33 schemas was not stated). The 53 → 33 assignment is now **derived
  from `EFF-HMENU3`/ANNEX B** and tabulated in the blueprint amendment; the `axiom`-typed
  placeholder below is replaced by the real `def`, re-signed against the same signature.
* **D3 — G.52g `c3_pairwise_ne`, PLACEHOLDER STATEMENT. ✅ CURED 2026-08-15 (blueprint AMENDMENT
  §A-6).** The blueprint's SIGNATURE was literally `theorem c3_pairwise_ne : /- the ten
  inequalities -/ True`, landed verbatim, i.e. vacuous. The ten inequalities (the five cubic type
  constants pairwise distinct as `FactorizationType`s — what G.72's step 3 consumes) are now
  stated; the stub below carries the amended signature.
* **D4 — ENV-A under-binds `[Finite (ResidueField O)]` (systematic, 22 stubs).** Lean's
  variable-inclusion drops an instance-implicit section variable that the *statement* does not
  mention, but auto-includes it when the *proof* uses it (verified against the landed
  `Uniformity.Density.card_res`, whose statement has the same shape and which does carry the
  instance). Every count/density stub here therefore lacks a binder its `leanfinal` twin will
  have, and the 0e type diff will report a spurious extra instance argument on: `card_dvdSet`,
  `card_exactSet_add`, `card_tangAdm`, `card_tangSet`, `card_depthSet`, `card_resStratum`,
  `card_inertStratum`, `card_splitStratum`, `card_species3`, `tendsto_geom_partial`,
  `undecidedCount_two_eq`, `undecidedSeq_two_eq`, `gapSeq_two_le`, `decidedSeq_two_ram_eq`,
  `decidedSeq_two_inert_eq`, `decidedDensity_two_{ram,inert,split}_eq`,
  `genuineDensity_two_exact`, `lowers_three`, `drainage_three_of_hex3_bound`,
  `card_le_undecidedCount_three`. Fix belongs in the blueprint's ENV-A block (bind the instance in
  the SIGNATURE of every count node), not here.
* **D5 — G.03 `readEquiv`, cosmetic.** The declared `left_inv`/`right_inv` scripts need mathlib's
  `ring_nf` fallback rather than `ring1`; `ring` succeeds via its own fallback and emits a
  `Try this: ring_nf` suggestion. No failure.

G.21's signature defect was **pre-declared** by the blueprint and is handled per §12 rule 2 (the
two-hypothesis form is landed); it is not counted above.

**Name collisions: none.** All 110 names elaborate in an environment that already contains all of
`leanfinal`. The `leancheck`-shadowing direction was checked separately (`leancheck` imports
`leanfinal` and opens `Uniformity.Density` while re-declaring `c3split`, `readEquiv`, `dvdSet`, …
in `UniformityCheck`): current-namespace resolution wins, so no ambiguity is introduced there
either.
-/

namespace Uniformity.Density

open IsLocalRing Polynomial Filter Topology

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-! ## §3 — Chapter primitives and the certificate schema (G.01–G.08) -/

namespace Menu

/-- **G.01** `ExactVal π k x` : `x` has valuation exactly `k` with respect to the uniformizer
`π`. -/
def ExactVal (π : O) (k : ℕ) (x : O) : Prop := π ^ k ∣ x ∧ ¬ π ^ (k + 1) ∣ x

/-- **G.02a** -/
axiom exactVal_iff_addVal (hπ : Irreducible π) {k : ℕ} {x : O} :
    ExactVal π k x ↔ IsDiscreteValuationRing.addVal O x = (k : ℕ∞)

/-- **G.02b** -/
axiom exactVal_unique (hπ : Irreducible π) {k k' : ℕ} {x : O}
    (h : ExactVal π k x) (h' : ExactVal π k' x) : k = k'

/-- **G.03** The `(value, derivative)` re-coordinatisation of the level-`N` box at the centre
class `γ`. -/
def readEquiv {N : ℕ} (γ : Res O N) : Coeff O 2 N ≃ (Res O N × Res O N) where
  toFun c := (c 0 + c 1 * γ + γ ^ 2, 2 * γ + c 1)
  invFun p := ![p.1 - (p.2 - 2 * γ) * γ - γ ^ 2, p.2 - 2 * γ]
  left_inv := by intro c; funext i; fin_cases i <;> simp <;> ring
  right_inv := by intro p; simp <;> ring

/-- **G.04** -/
axiom readEquiv_proj {N : ℕ} (g : O) (a : Fin 2 → O) :
    readEquiv (Ideal.Quotient.mk _ g) (proj O 2 N a)
      = (Ideal.Quotient.mk _ (qval a g), Ideal.Quotient.mk _ (qder a g))

/-- **G.05a** A level-`N` certified family: a centre-indexed certificate that (i) reads through a
bijection, (ii) survives centre moves inside a fixed coset, (iii) pins the centre's coset, and
(iv) forces one splitting type on every lift. -/
structure CertFamily (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (n N : ℕ) where
  m : ℕ
  hm : m ≤ N
  D : Type
  cert : Res O N → Coeff O n N → Prop
  read : Res O N → (Coeff O n N ≃ D)
  S : Set D
  σ : FactorizationType
  hcert : ∀ γ c, cert γ c ↔ read γ c ∈ S
  hshift : ∀ γ γ' c, cert γ c → resFactor (O := O) hm γ' = resFactor hm γ → cert γ' c
  huniq : ∀ γ γ' c, cert γ c → cert γ' c → resFactor (O := O) hm γ' = resFactor hm γ
  hforce : ∀ γ (a : Fin n → O), cert γ (proj O n N a) → typeOf (monicPoly a) = σ

/-- **G.05b** The set of level-`N` classes certified by some centre. -/
def CertFamily.set {n N : ℕ} (F : CertFamily O n N) : Set (Coeff O n N) := {c | ∃ γ, F.cert γ c}

/-- **G.06** -/
axiom CertFamily.decidedAt {n N : ℕ} (F : CertFamily O n N) {c : Coeff O n N}
    (hc : c ∈ F.set) : DecidedAt O n F.σ N c

/-- **G.07** -/
axiom CertFamily.card {n N : ℕ} (F : CertFamily O n N) :
    Nat.card F.set = residueCard O ^ F.m * Nat.card F.S

/-- **G.08** -/
axiom CertFamily.decidedDensity_ge {n N : ℕ} (F : CertFamily O n N) :
    ((residueCard O : ℝ) ^ F.m * (Nat.card F.S : ℝ)) / (residueCard O : ℝ) ^ (n * N)
      ≤ decidedDensity O n F.σ

/-! ## §4 — `n = 2`: the tangency filtration and its exact level census (G.09–G.23) -/

/-- **G.09** Level-`N` classes admitting a lift with a centre of tangency depth `≥ t`. -/
def tangSet (π : O) (N t : ℕ) : Set (Coeff O 2 N) :=
  {c | ∃ a : Fin 2 → O, proj O 2 N a = c ∧ ∃ γ : O, Tang π a t γ}

/-- **G.10** -/
axiom tang_shift {a : Fin 2 → O} {t : ℕ} {γ γ' : O} (h : Tang π a t γ)
    (hδ : π ^ ((t + 1) / 2) ∣ (γ' - γ)) : Tang π a t γ'

/-- **G.11** -/
axiom tang_centre_unique (hπ : Irreducible π) {a : Fin 2 → O} {t : ℕ} {γ γ' : O}
    (h : Tang π a t γ) (h' : Tang π a t γ') : π ^ ((t + 1) / 2) ∣ (γ' - γ)

/-- **G.12** -/
axiom tang_of_proj_eq (hπ : Irreducible π) {N t : ℕ} (ht : t ≤ N) {a b : Fin 2 → O}
    (hab : proj O 2 N a = proj O 2 N b) {γ : O} (h : Tang π a t γ) : Tang π b t γ

/-- **G.13a** -/
axiom mem_tangSet_iff (hπ : Irreducible π) {N t : ℕ} (ht : t ≤ N) {c : Coeff O 2 N} :
    c ∈ tangSet π N t ↔ ∀ a : Fin 2 → O, proj O 2 N a = c → ∃ γ : O, Tang π a t γ

/-- **G.13b** -/
axiom tangSet_antitone (hπ : Irreducible π) {N t t' : ℕ} (h : t ≤ t') :
    tangSet π N t' ⊆ tangSet π N t

/-- **G.14a** The classes of valuation `≥ k`. -/
def dvdSet (π : O) (k N : ℕ) : Set (Res O N) :=
  {x | ∃ y : O, Ideal.Quotient.mk _ (π ^ k * y) = x}

/-- **G.14b** The classes of valuation exactly `k`. -/
def exactSet (π : O) (k N : ℕ) : Set (Res O N) := dvdSet π k N \ dvdSet π (k + 1) N

/-- **G.14c** -/
axiom card_dvdSet (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (dvdSet π k (k + r)) = residueCard O ^ r

/-- **G.14d** -/
axiom card_exactSet_add (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (exactSet π k (k + r + 1)) + residueCard O ^ r = residueCard O ^ (r + 1)

/-- **G.15** The admissible set of the depth-`t` family in `(value, derivative)` coordinates. -/
def tangAdm (π : O) (t N : ℕ) : Set (Res O N × Res O N) :=
  (dvdSet π t N) ×ˢ (dvdSet π ((t + 1) / 2) N)

/-- **G.16** -/
axiom card_tangAdm (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (tangAdm π t (t + r)) * residueCard O ^ ((t + 1) / 2)
      = residueCard O ^ (t + 2 * r)

/-- **G.17 — The tangency-filtration count.** At level `N = t + r`, exactly `q^(t+2r) = q^(2N−t)`
classes admit a centre of tangency depth `≥ t`. This is the level-exact form of W-11's per-node
drainage census, and its `r = 0` case is W-11 clause (iii)'s exact drainage law. -/
axiom card_tangSet (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (tangSet π (t + r) t) = residueCard O ^ (t + 2 * r)

/-- **G.18** The depth-`t` census datum: the three `card_certSet_gen` hypotheses, discharged,
together with the identification of the certified set with `tangSet`.

⚠ **DEFECT D1, repaired minimally.** The blueprint writes `resFactor _ g` on the right of each
equation; that placeholder is unsynthesizable (`don't know how to synthesize placeholder for
argument 'h'`, goal `(t + 1) / 2 ≤ t + r`) and the verbatim signature does not elaborate. Both
occurrences are filled with the `(by omega : …)` proof the blueprint already writes on the left;
the resulting type is the intended one (proof irrelevance). -/
axiom tangCert (hπ : Irreducible π) (t r : ℕ) :
    ∃ cert : Res O (t + r) → Coeff O 2 (t + r) → Prop,
      (∀ g c, cert g c ↔ readEquiv g c ∈ tangAdm π t (t + r))
      ∧ (∀ g g' c, cert g c → resFactor (O := O) (by omega : (t+1)/2 ≤ t + r) g'
            = resFactor (by omega : (t+1)/2 ≤ t + r) g → cert g' c)
      ∧ (∀ g g' c, cert g c → cert g' c → resFactor (O := O) (by omega : (t+1)/2 ≤ t + r) g'
            = resFactor (by omega : (t+1)/2 ≤ t + r) g)
      ∧ (∀ c, (∃ g, cert g c) ↔ c ∈ tangSet π (t + r) t)

/-- **G.19** Level-`N` classes whose maximal centre depth is exactly `t`. -/
def depthSet (π : O) (N t : ℕ) : Set (Coeff O 2 N) := tangSet π N t \ tangSet π N (t + 1)

/-- **G.20** -/
axiom card_depthSet (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (depthSet π (t + 1 + r) t) + residueCard O ^ (t + 2 * r + 1)
      = residueCard O ^ (t + 2 * r + 2)

/-- **G.21** The residual pair `(b₀, b₁)` read at a centre of even depth `2k`, in the residue
field. Landed in the **two-hypothesis form** mandated by blueprint §12 rule 2 (the displayed
SIGNATURE is declared defective by the blueprint itself). -/
noncomputable def residualPair {k : ℕ} {a : Fin 2 → O} {γ : O}
    (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ) :
    IsLocalRing.ResidueField O × IsLocalRing.ResidueField O :=
  (IsLocalRing.residue O h0.choose, IsLocalRing.residue O h1.choose)

/-- **G.22** Classes of depth exactly `2k` carrying the residual pair `p`. -/
def resStratum (π : O) (N k : ℕ) (p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O) :
    Set (Coeff O 2 N) :=
  {c | c ∈ depthSet π N (2 * k) ∧
    ∃ (a : Fin 2 → O) (γ : O), proj O 2 N a = c ∧ Tang π a (2 * k) γ ∧
      ∃ (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ), residualPair h0 h1 = p}

/- **G.23a — ⚠ WITHDRAWN: STATEMENT REFUTED** (blueprint AMENDMENT 2026-08-15 §A-1). The stub is
commented out rather than signed, because a refuted statement must not stand as a fleet contract.

    axiom card_resStratum (hπ : Irreducible π) {N k : ℕ} (hk : 2 * k < N)
        {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O}
        (hp : ∀ z : IsLocalRing.ResidueField O, p ≠ (z * z, z + z)) :
        Nat.card (resStratum π N k p) = residueCard O ^ (2 * N - 2 * k - 2)

The residual pair is not an invariant of the class: recentring by `γ + π^k·d` moves it by
`y ↦ y + d̄`, so the strata over one translation orbit are EQUAL and the true per-pair count is
`q^(2N−2k−1)/#Stab(p)` — `q^(2N−2k−1)` in residue characteristic ≠ 2 and `q^(2N−2k−1)/2` in
residue characteristic 2, agreeing with the withdrawn formula only at `q = 2`. Counterexample:
`O = ℤ_[3]`, `N = 1`, `k = 0`, `p = (1,0)` — the stratum is `{(1,0), (2,1), (2,2)}`, of size 3,
where the formula says 1. G.41/G.42's STATEMENTS are unaffected; their route is re-cut through a
translation-invariant residual CLASS (`AniForm` / `SepPair`) at centre modulus `m = k`. -/

/-- **G.23b** -/
axiom depthSet_eq_iUnion_resStratum (hπ : Irreducible π) {N k : ℕ} (hk : 2 * k < N) :
    depthSet π N (2 * k)
      = ⋃ p ∈ {p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O |
          ∀ z : IsLocalRing.ResidueField O, p ≠ (z * z, z + z)}, resStratum π N k p

/-! ## §5 — `n = 2`: type classification by depth (G.24–G.31) -/

/-- **G.24** -/
axiom certRam_of_depth_odd (hπ : Irreducible π) {N j : ℕ} {a : Fin 2 → O}
    (hmem : proj O 2 N a ∈ depthSet π N (2 * j + 1)) (hN : 2 * j + 2 ≤ N) :
    CertRam π a (2 * j + 2)

/-- **G.25** -/
axiom decidedAt_ram_of_depth_odd (hπ : Irreducible π) {N j : ℕ} {c : Coeff O 2 N}
    (hmem : c ∈ depthSet π N (2 * j + 1)) (hN : 2 * j + 2 ≤ N) :
    DecidedAt O 2 ramType N c

/-- **G.26** -/
axiom depth_even_dichotomy (hπ : Irreducible π) {N k : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a (2 * k) γ) (hmax : ¬ ∃ γ', Tang π a (2 * k + 1) γ')
    {b₀ b₁ : O} (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁) :
    Anisotropic ![b₀, b₁] ∨ ∃ z : O, π ∣ (z ^ 2 + b₁ * z + b₀) ∧ ¬ π ∣ (b₁ + 2 * z)

/-- **G.27** -/
axiom decidedAt_inert_of_ani (hπ : Irreducible π) {N k : ℕ} {a : Fin 2 → O} {γ : O}
    {b₀ b₁ : O} (hN : 2 * k + 1 ≤ N)
    (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁)
    (hani : Anisotropic ![b₀, b₁]) :
    DecidedAt O 2 inertType N (proj O 2 N a)

/-- **G.28** — window hypothesis AMENDED to `2 * k + 1 ≤ N` (was `2 * k + 2 ≤ N`) per blueprint
AMENDMENT 2026-08-15 §A-2: the node's own proof uses only `2 * k + 1 ≤ N`, `CertSplit` asks only
`2 * w + 1 ≤ N`, `CertSplit_congr` transports at equality, and `typeOf_of_certSplit` discards the
window bound — so the top even stratum `t = N − 1` is covered and G.42 is provable at `r = 0`. -/
axiom decidedAt_split_of_sep (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N k : ℕ} {a : Fin 2 → O} {γ z : O}
    {b₀ b₁ : O} (hN : 2 * k + 1 ≤ N)
    (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁)
    (hz : π ∣ (z ^ 2 + b₁ * z + b₀)) (hs : ¬ π ∣ (b₁ + 2 * z)) :
    DecidedAt O 2 splitType N (proj O 2 N a)

/-- **G.29** -/
axiom decidedAt_of_depth_lt (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N : ℕ} {c : Coeff O 2 N}
    (hc : c ∉ tangSet π N N) {a : Fin 2 → O} (ha : proj O 2 N a = c) :
    DecidedAt O 2 (typeOf (monicPoly a)) N c

/-- **G.30** -/
axiom depth_type (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {N t : ℕ} (ht : t < N) {c : Coeff O 2 N} (hc : c ∈ depthSet π N t) :
    (∃ j, t = 2 * j + 1 ∧ DecidedAt O 2 ramType N c)
      ∨ (∃ k, t = 2 * k ∧ (DecidedAt O 2 inertType N c ∨ DecidedAt O 2 splitType N c))

/-- **G.31a** The inert half of an even stratum. -/
def inertStratum (π : O) (N k : ℕ) : Set (Coeff O 2 N) :=
  {c ∈ depthSet π N (2 * k) | DecidedAt O 2 inertType N c}

/-- **G.31b** The split half of an even stratum. -/
def splitStratum (π : O) (N k : ℕ) : Set (Coeff O 2 N) :=
  {c ∈ depthSet π N (2 * k) | DecidedAt O 2 splitType N c}

/-- **G.31c** -/
axiom decidedSet_ram_eq (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    decidedSet O 2 ramType N = ⋃ j ∈ Finset.range N, depthSet π N (2 * j + 1)

/-! ## §6 — `n = 2`: the exact drainage law (G.32–G.37) -/

/-- **G.32** -/
axiom exists_aniForm_of_ne_zero (K : Type*) [Field K] [Finite K] {b₁ : K} (hb : b₁ ≠ 0) :
    ∃ b₀ : K, AniForm (b₀, b₁)

/-- **G.33** -/
axiom exists_split_lift (hπ : Irreducible π) {N : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a N γ) :
    ∃ b : Fin 2 → O, proj O 2 N b = proj O 2 N a ∧ typeOf (monicPoly b) = splitType

/-- **G.34** -/
axiom exists_inert_lift (hπ : Irreducible π) {N : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a N γ) :
    ∃ b : Fin 2 → O, proj O 2 N b = proj O 2 N a ∧ typeOf (monicPoly b) = inertType

/-- **G.35** -/
axiom undecidedSet_eq_tangSet (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    undecidedSet O 2 N = tangSet π N N

end Menu

/-- **G.36 — W-11 clause (iii), exactly: the `n = 2` σ-undecided count is `q^N`.** Every complete
DVR with finite residue field, every level `N`, both characteristics, wild residue characteristic
included. This is the exact form of the landed bound `undecidedCount_le` (which gives only
`q^(3M)` at level `2M`). -/
axiom undecidedCount_two_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    undecidedCount O 2 N = residueCard O ^ N

/-- **G.37a** -/
axiom undecidedSeq_two_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    undecidedSeq O 2 N = (1 / (residueCard O : ℝ)) ^ N

/-- **G.37b** -/
axiom gapSeq_two_le [IsAdicComplete (maximalIdeal O) O] (σ : FactorizationType) (N : ℕ) :
    gapSeq O 2 σ N ≤ (1 / (residueCard O : ℝ)) ^ N

/-! ## §7 — `n = 2`: exact counts, exact densities, the capstone slice (G.38–G.51) -/

namespace Menu

/-- **G.38** -/
axiom two_mul_card_aniForm (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {p : K × K // AniForm p} + Nat.card K = Nat.card K * Nat.card K

/-- **G.39a** `p = (b₀, b₁)` is a *separable-split* pair: `X² − b₁X + b₀` has two distinct
roots. -/
def SepPair {K : Type*} [Field K] (p : K × K) : Prop :=
  ∃ y z : K, y ≠ z ∧ p = (y * z, y + z)

/-- **G.39b** -/
axiom two_mul_card_sepPair (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {p : K × K // SepPair p} + Nat.card K = Nat.card K * Nat.card K

/-- **G.40a** -/
def DblPair {K : Type*} [Field K] (p : K × K) : Prop := ∃ y : K, p = (y * y, y + y)

/-- **G.40b** -/
axiom card_dblPair (K : Type*) [Field K] [Finite K] :
    Nat.card {p : K × K // DblPair p} = Nat.card K

/-- **G.40c** -/
axiom pair_trichotomy {K : Type*} [Field K] (p : K × K) :
    AniForm p ∨ SepPair p ∨ DblPair p

/-- **G.41** -/
axiom card_inertStratum (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (k r : ℕ) :
    2 * Nat.card (inertStratum π (2 * k + 1 + r) k) + residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ (2 * k + 2 * r + 2)

/-- **G.42** -/
axiom card_splitStratum (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (k r : ℕ) :
    2 * Nat.card (splitStratum π (2 * k + 1 + r) k) + residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ (2 * k + 2 * r + 2)

end Menu

/-- **G.43 — W-11's every-window identity, exactly:** at every level the split-decided and
inert-decided classes are equinumerous — not merely equal in the limit. The mechanism is the
residue-field coincidence `#{anisotropic pairs} = #{separable-split pairs} = q(q−1)/2`. -/
axiom decidedCount_split_eq_inert [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedCount O 2 splitType N = decidedCount O 2 inertType N

/-- **G.44a** -/
axiom decidedSeq_two_ram_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedSeq O 2 ramType N
      = ∑ j ∈ Finset.range ((N + 1) / 2),
          ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ (2 * j + 2)

/-- **G.44b** -/
axiom decidedSeq_two_inert_eq [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedSeq O 2 inertType N
      = ∑ k ∈ Finset.range ((N + 1) / 2),
          ((residueCard O : ℝ) - 1) / (2 * (residueCard O : ℝ) ^ (2 * k + 1))

namespace Menu

/-- **G.45** -/
axiom tendsto_geom_partial (c : ℝ) (d : ℕ) {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun N => ∑ i ∈ Finset.range (f N), c / (residueCard O : ℝ) ^ (2 * i + d)) atTop
      (𝓝 (c / (residueCard O : ℝ) ^ d * ((residueCard O : ℝ) ^ 2
        / ((residueCard O : ℝ) ^ 2 - 1))))

end Menu

/-- **G.46** -/
axiom decidedDensity_two_ram_eq [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1)

/-- **G.47a** -/
axiom decidedDensity_two_inert_eq [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))

/-- **G.47b** -/
axiom decidedDensity_two_split_eq [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))

/-- **G.48 — THE `n = 2` DENSITY FUNCTION, EXACTLY.** Over every complete DVR with finite residue
field, both characteristics, wild residue characteristic included. -/
axiom genuineDensity_two_exact [IsAdicComplete (maximalIdeal O) O] :
    genuineDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1)
    ∧ (∀ σ : FactorizationType, σ ≠ splitType → σ ≠ inertType → σ ≠ ramType →
        genuineDensity O 2 σ = 0)

/-- **G.49a** -/
axiom gate_two_padic_two_exact :
    genuineDensity ℤ_[2] 2 splitType = 1 / 3 ∧ genuineDensity ℤ_[2] 2 inertType = 1 / 3
      ∧ genuineDensity ℤ_[2] 2 ramType = 1 / 3

/-- **G.49b** -/
axiom gate_two_padic_three_exact :
    genuineDensity ℤ_[3] 2 splitType = 3 / 8 ∧ genuineDensity ℤ_[3] 2 inertType = 3 / 8
      ∧ genuineDensity ℤ_[3] 2 ramType = 1 / 4

/-- **G.50** -/
axiom degree_two_type_cases {σ : FactorizationType} (hσ : σ.degree = 2) :
    σ = splitType ∨ σ = inertType ∨ σ = ramType ∨
      (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        genuineDensity O 2 σ = 0)

/-- **G.51 — `UniformityStatement` at `n = 2`.** One rational function per degree-2 type, valid at
every complete DVR with finite residue field — wild residue characteristic included, both
characteristics. Unconditional: no drainage hypothesis, no axiom, Lean core only. -/
axiom uniformityStatement_two (σ : FactorizationType) (hσ : σ.degree = 2) :
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          genuineDensity O 2 σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)

/-! ## §8 — `n = 3`: the five types, the menu, the leaf certificates (G.52–G.61) -/

/-- **G.52a** `{(1,1),(1,1),(1,1)}` — three unramified linear factors. -/
def c3split : FactorizationType := ⟨{(1, 1), (1, 1), (1, 1)}⟩
/-- **G.52b** `{(1,1),(1,2)}` — a linear factor and an unramified quadratic. -/
def c3linInert : FactorizationType := ⟨{(1, 1), (1, 2)}⟩
/-- **G.52c** `{(1,3)}` — one unramified cubic factor. -/
def c3inert : FactorizationType := ⟨{(1, 3)}⟩
/-- **G.52d** `{(1,1),(2,1)}` — a linear factor and a ramified quadratic. -/
def c3linRam : FactorizationType := ⟨{(1, 1), (2, 1)}⟩
/-- **G.52e** `{(3,1)}` — one totally ramified cubic factor. -/
def c3ram : FactorizationType := ⟨{(3, 1)}⟩

/-- **G.52f** -/
axiom c3_degrees :
    c3split.degree = 3 ∧ c3linInert.degree = 3 ∧ c3inert.degree = 3
      ∧ c3linRam.degree = 3 ∧ c3ram.degree = 3

/-- **G.52g** The ten pairwise inequalities. Signature per blueprint **AMENDMENT §A-6** (D3 cured
2026-08-15): the placeholder `/- the ten inequalities -/ True` is replaced by the ten inequalities
themselves — the five cubic type constants pairwise distinct as `FactorizationType`s, in the
`leancheck/UniformityCheck/N3Base.lean` enumeration order. -/
axiom c3_pairwise_ne :
    c3split ≠ c3linInert ∧ c3split ≠ c3inert ∧ c3split ≠ c3linRam ∧ c3split ≠ c3ram
      ∧ c3linInert ≠ c3inert ∧ c3linInert ≠ c3linRam ∧ c3linInert ≠ c3ram
      ∧ c3inert ≠ c3linRam ∧ c3inert ≠ c3ram
      ∧ c3linRam ≠ c3ram

/-- **G.53 — Exactly five splitting types occur in degree 3.** No Newton polygon, no Hensel: the
statement is a consequence of `typeOf_degree` and the positivity of every `(e,f)` pair. -/
axiom typeOf_three_cases (a : Fin 3 → O) :
    typeOf (monicPoly a) = c3split ∨ typeOf (monicPoly a) = c3linInert
      ∨ typeOf (monicPoly a) = c3inert ∨ typeOf (monicPoly a) = c3linRam
      ∨ typeOf (monicPoly a) = c3ram

/-- **G.54a** -/
axiom coveringMenu_three :
    CoveringMenu O 3 ({c3split, c3linInert, c3inert, c3linRam, c3ram} : Finset FactorizationType)

/-- **G.54b** -/
axiom genuineDensity_three_eq_zero {σ : FactorizationType} (hs : σ ≠ c3split)
    (hi : σ ≠ c3linInert) (hc : σ ≠ c3inert) (hr : σ ≠ c3linRam) (ht : σ ≠ c3ram) :
    genuineDensity O 3 σ = 0

/-- **G.55** -/
axiom typeOf_split3_of_residue [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (ρ₁ ρ₂ ρ₃ : O) (h12 : IsUnit (ρ₁ - ρ₂)) (h13 : IsUnit (ρ₁ - ρ₃)) (h23 : IsUnit (ρ₂ - ρ₃))
    (hres : (monicPoly a).map (residue O)
      = (X - C (residue O ρ₁)) * (X - C (residue O ρ₂)) * (X - C (residue O ρ₃))) :
    typeOf (monicPoly a) = c3split

/-- **G.56** -/
axiom typeOf_linInert_of_residue [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    {ρ : O} {g₀ : Polynomial (ResidueField O)} (hg₀ : g₀.Monic) (hdeg : g₀.natDegree = 2)
    (hirr : Irreducible g₀)
    (hres : (monicPoly a).map (residue O) = (X - C (residue O ρ)) * g₀) :
    typeOf (monicPoly a) = c3linInert

/-- **G.57** -/
axiom typeOf_inert3_of_irreducible_map [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (h : Irreducible ((monicPoly a).map (residue O))) : typeOf (monicPoly a) = c3inert

/-- **G.58** -/
axiom typeOf_ram3_of_eisenstein {a : Fin 3 → O}
    (hlow : ∀ i : Fin 3, a i ∈ maximalIdeal O) (h0 : a 0 ∉ (maximalIdeal O) ^ 2) :
    typeOf (monicPoly a) = c3ram

/-- **G.59** -/
axiom typeOf_linRam_of_residue [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (h2 : IsUnit (a 2)) (h1 : a 1 ∈ maximalIdeal O) (h0 : a 0 ∈ maximalIdeal O)
    (h0' : a 0 ∉ (maximalIdeal O) ^ 2) : typeOf (monicPoly a) = c3linRam

namespace Menu

/-- **G.60a** -/
def NoRootCubic {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∀ y : K, y ^ 3 + c 2 * y ^ 2 + c 1 * y + c 0 ≠ 0

/-- **G.60b** -/
def LinAni {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∃ (ρ : K) (p : K × K), AniForm p ∧ c = ![-(ρ * p.1), p.1 + ρ * p.2, -(p.2 + ρ)]

/-- **G.60c** -/
def Split3 {K : Type*} [Field K] (c : Fin 3 → K) : Prop :=
  ∃ r s t : K, r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ c = ![-(r * s * t), r*s + r*t + s*t, -(r + s + t)]

/-- **G.60d** -/
axiom three_mul_card_noRootCubic (K : Type*) [Field K] [Finite K] :
    3 * Nat.card {c : Fin 3 → K // NoRootCubic c} + Nat.card K = Nat.card K ^ 3

/-- **G.60e** -/
axiom two_mul_card_linAni (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {c : Fin 3 → K // LinAni c} + Nat.card K ^ 2 = Nat.card K ^ 3

/-- **G.60f** -/
axiom six_mul_card_split3 (K : Type*) [Field K] [Finite K] :
    6 * Nat.card {c : Fin 3 → K // Split3 c} + 3 * Nat.card K ^ 2 = Nat.card K ^ 3 + 2 * Nat.card K

end Menu

/-- **G.61** -/
axiom lowers_three [IsAdicComplete (maximalIdeal O) O] :
    1 / (residueCard O : ℝ) ^ 9 ≤ decidedDensity O 3 c3split
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ) ^ 2) / (2 * (residueCard O : ℝ) ^ 3)
        ≤ decidedDensity O 3 c3linInert
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
        ≤ decidedDensity O 3 c3inert
    ∧ ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3linRam
    ∧ ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3ram

/-! ## §9 — the 53-family index and the HEX3 arithmetic layer (G.62–G.72) -/

namespace Menu

/-- **G.62a** The ANNEX-B index of the cubic core menu: 53 formal families in five tiers. This is
an INDEX, not a family: it carries no counts and no certificates. See the chapter honesty block
H-3. -/
inductive CubicFamilyIndex
  | sep    : Fin 3  → CubicFamilyIndex
  | dbl    : Fin 4  → CubicFamilyIndex
  | tierI  : Fin 11 → CubicFamilyIndex
  | tierII : Fin 11 → CubicFamilyIndex
  | bTier  : Fin 24 → CubicFamilyIndex
  deriving DecidableEq, Fintype

/-- **G.62b** The shape schema underlying each formal family (ANNEX B's "33 shape schemas").

Body per blueprint **AMENDMENT §A-5** (D2 cured 2026-08-15): the 53 → 33 assignment derived from
`EFF-HMENU3` ANNEX B. `Fin 33` is read as the five consecutive blocks `0–2` SEP, `3–6` DBL,
`7–13` tier I, `14–20` tier II, `21–32` B-tier (`EFF.HMENU3.69`'s schema column, `3+4+7+7+12`).
SEP and DBL are unrefined, so those fibers are singletons (`.69`, both rows "—"); each TRP tier's
four λ-free schemas (RAM3, 3LIN, LINRAM2, RAM2LIN) are singletons and its three λ-retaining
schemas VERT1/VERT2/FULL (`EFF.HMENU3.67`) carry fibers of size `#Λ₂ = 2`, `#Λ₂ = 2`, `#Λ₃ = 3`
(`EFF.HMENU3.68`); the twelve B-schemas each split into their `m = 0` / `m ≥ 1` regimes
(`EFF.HMENU3.69`, `.37`), giving `bTier i ↦ 21 + i / 2`. -/
def CubicFamilyIndex.schema : CubicFamilyIndex → Fin 33
  | .sep i    => ![0, 1, 2] i
  | .dbl i    => ![3, 4, 5, 6] i
  | .tierI i  => ![7, 8, 9, 10, 11, 11, 12, 12, 13, 13, 13] i
  | .tierII i => ![14, 15, 16, 17, 18, 18, 19, 19, 20, 20, 20] i
  | .bTier i  => ![21, 21, 22, 22, 23, 23, 24, 24, 25, 25, 26, 26,
                   27, 27, 28, 28, 29, 29, 30, 30, 31, 31, 32, 32] i

/-- **G.63a** -/
axiom card_cubicFamilyIndex : Nat.card CubicFamilyIndex = 53

/-- **G.63b** -/
axiom schema_surjective : Function.Surjective CubicFamilyIndex.schema

/-- **G.64** HEX3's `R(M)`: the `n = 2` conservative-drain count per centre at window `M`
(`EFF.HEX3.26`, LEMMA H-4). Pure arithmetic — this definition mentions no ring. -/
def hex3R (q M : ℕ) : ℕ := q ^ (M - 1) + ((M - 1) / 2) * ((q - 1) * q ^ (M - 2))

/-- **G.65** -/
axiom hex3R_rec (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M) :
    hex3R q M
      = q ^ (M - 1) + (q - 1) * ∑ j ∈ Finset.Icc 1 ((M - 1) / 2), q ^ j * hex3R q (M - 2 * j)

/-- **G.66** HEX3's `u(q, N)` — the per-centre conservative-undecided count of the cubic TRP
stratum (`EFF.HEX3.08`, THEOREM HEX3.A), in telescoped form. Pure arithmetic. -/
def hex3U (q N : ℕ) : ℕ :=
  q ^ (2 * N - 2)
    + (q - 1) * ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
        q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k))

/-- **G.67** -/
axiom hex3U_rec (q N : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) :
    hex3U q N + ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
        (q - 1) * q ^ (3 * k) * q ^ (2 * (N - 3 * k) - 2)
      = q ^ (2 * N - 2) + ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
          (q - 1) * q ^ (3 * k) * (hex3U q (N - 3 * k)
            + (q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k))

/-- **G.68** -/
axiom two_mul_hex3R_le (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M) :
    2 * hex3R q M ≤ (M + 1) * q ^ (M - 1)

/-- **G.69** -/
axiom hex3U_le (q N : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) :
    hex3U q N ≤ N * q ^ (2 * N - 2)

/-- **G.70** -/
axiom hex3U_div_tendsto_zero (q : ℕ) (hq : 2 ≤ q) :
    Filter.Tendsto (fun N : ℕ => (q * hex3U q N : ℝ) / (q : ℝ) ^ (3 * N))
      Filter.atTop (nhds 0)

end Menu

/-- **G.71** -/
axiom drainage_three_of_hex3_bound [IsAdicComplete (maximalIdeal O) O]
    (h : ∀ N : ℕ, (undecidedCount O 3 N : ℝ)
      ≤ (residueCard O : ℝ) * (Menu.hex3U (residueCard O) N : ℝ))
    (σ : FactorizationType) : UndecidedVanishes O 3 σ

/-- **G.72a** -/
axiom totalMass_three_of_drainage [IsAdicComplete (maximalIdeal O) O]
    (hd : ∀ σ : FactorizationType, UndecidedVanishes O 3 σ) :
    genuineDensity O 3 c3split + genuineDensity O 3 c3linInert + genuineDensity O 3 c3inert
      + genuineDensity O 3 c3linRam + genuineDensity O 3 c3ram = 1

/-- **G.72b** -/
axiom one_le_sum_three :
    1 ≤ genuineDensity O 3 c3split + genuineDensity O 3 c3linInert + genuineDensity O 3 c3inert
      + genuineDensity O 3 c3linRam + genuineDensity O 3 c3ram

/-! ## §10 — `n = 3`: the σ-undecided lower bound (G.73–G.77) -/

namespace Menu

/-- **G.73a** The `q^N`-element species of `EFF.HEX3.07` / LEMMA W12-S3.2: separation data
hidden, `b₂` free and visible. -/
def species3 (N : ℕ) : Set (Coeff O 3 N) := {c | c 0 = 0 ∧ c 1 = 0}

/-- **G.73b** -/
axiom card_species3 (N : ℕ) : Nat.card (species3 (O := O) N) = residueCard O ^ N

end Menu

/-- **G.74** -/
axiom exists_split3_lift {N : ℕ} {c : Coeff O 3 N} (hc : c ∈ Menu.species3 N) :
    ∃ a : Fin 3 → O, proj O 3 N a = c ∧ typeOf (monicPoly a) = c3split

/-- **G.75** -/
axiom exists_ram3_lift [IsAdicComplete (maximalIdeal O) O] (hπ : Irreducible π)
    {N : ℕ} {c : Coeff O 3 N} (hc : c ∈ Menu.species3 N) :
    ∃ a : Fin 3 → O, proj O 3 N a = c ∧
      (typeOf (monicPoly a) = c3ram ∨ typeOf (monicPoly a) = c3linRam)

/-- **G.76** The `n = 3` σ-undecided count is at least `q^N`: the `q^N` classes with both
separation coordinates hidden admit both a split lift and a ramified lift. -/
axiom card_le_undecidedCount_three [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    residueCard O ^ N ≤ undecidedCount O 3 N

/-- **G.77a** -/
axiom gate_three_padic_two :
    (1 : ℝ) / 512 ≤ decidedDensity ℤ_[2] 3 c3split
      ∧ (1 : ℝ) / 4 ≤ decidedDensity ℤ_[2] 3 c3linInert
      ∧ (1 : ℝ) / 4 ≤ decidedDensity ℤ_[2] 3 c3inert
      ∧ (1 : ℝ) / 16 ≤ decidedDensity ℤ_[2] 3 c3linRam
      ∧ (1 : ℝ) / 16 ≤ decidedDensity ℤ_[2] 3 c3ram

/-- **G.77b** -/
axiom gate_three_hmenu3_containment_two :
    (1 : ℝ) / 512 ≤ 4 / 93 ∧ (1 : ℝ) / 4 ≤ 28 / 93 ∧ (1 : ℝ) / 4 ≤ 8 / 31
      ∧ (1 : ℝ) / 16 ≤ 22 / 93 ∧ (1 : ℝ) / 16 ≤ 5 / 31

end Uniformity.Density
