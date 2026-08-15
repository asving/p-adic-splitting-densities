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

**Amended against blueprint AMENDMENT 2026-08-15, third append** (§A-7, G.31's dependency gap
cured): one **new** node, **G.30a** `depthSet_odd_eq_empty`, is signed below between G.30 and
G.31 — the supplier that justifies G.31's `Finset.range N` index set. Declaration count rises
**109 → 110**. Only the ODD form is signed: the general shape `depthSet π N t = ∅ for t ≥ N` that
wave-3 named as G.31's missing premise is **refuted** at even `t` in residue characteristic 2
(§A-7's `ℤ₂`, `N = 2`, `t = 2` counterexample), and must not be signed by any future node.

**Amended against blueprint AMENDMENT 2026-08-15, fourth append** (§A-8, the G.23 REPLACEMENT
ROUTE expanded into fireable nodes): **twelve new nodes G.23R1–G.23R12** carrying **25
declarations** are signed below, between G.23b and §5. §A-1 refuted G.23a and derived — in prose
only — a replacement route that certifies a *translation-invariant residual CLASS* at centre
modulus `m = k` instead of an individual pair; §A-8 turns that derivation into node entries and
lands all twelve in `leanfinal` in the same unit, so all 25 are written directly in the
retirement form. Declaration count rises **110 → 135**. The headline is **G.23R9**
`card_resClassSet` (`#resClassSet = #P · q^(2k+2r)`), which is what G.41 and G.42 consume in
place of the withdrawn G.23a. G.23a stays withdrawn and G.23b stays an unlanded `axiom` (true as
stated, union not disjoint, and no consumer needs it any more).

**This file is never imported by `leanfinal` or `leancheck`.** It carries `axiom`s by design; it
is an interface contract, not mathematics. Nothing here is proved.

**Environments.** The blueprint's ENV-A is the section `variable` block below; ENV-A' is ENV-A
with `(hπ : Irreducible π)`, which every node that names `π` takes explicitly; ENV-B adds
`[IsAdicComplete (maximalIdeal O) O]`, which every ENV-B signature carries inline; ENV-C binds its
own `(K : Type*) [Field K] [Finite K]` inline.

**Blueprint defects found at stub-landing** (stage-0e gate, 2026-08-14; recorded here and in the
0e report, NOT repaired in the blueprint — rule 3):

* **D1 — G.18 `tangCert`, ELABORATION FAILURE (verbatim form). ✅ CURED 2026-08-15 (wave-3,
  `leanfinal` G.18).** The two occurrences of `resFactor _ g` leave an unsynthesizable proof
  placeholder: `error: don't know how to synthesize placeholder for argument 'h'` with goal
  `(t + 1) / 2 ≤ t + r`. Landed below with the minimal repair — the same `(by omega : …)` proof
  the blueprint already writes on the left-hand side of each equation — which is type-identical by
  proof irrelevance; `Uniformity.ChapG.G18` lands the identical repair, confirmed byte-identical by
  the retirement-form 0e-diff. The blueprint entry still needs the placeholder filled in.
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
* **D4 — ENV-A under-binds `[Finite (ResidueField O)]` (systematic, 22 stubs). Does NOT block
  retirement (confirmed 2026-08-15, 0e-G unit).** Lean's variable-inclusion drops an
  instance-implicit section variable that the *statement* does not mention, but auto-includes it
  when the *proof* uses it (verified against the landed `Uniformity.Density.card_res`, whose
  statement has the same shape and which does carry the instance). Every count/density stub here
  therefore lacks a binder its `leanfinal` twin will have: `card_dvdSet`, `card_exactSet_add`,
  `card_tangAdm`, `card_tangSet`, `card_depthSet`, `card_resStratum`, `card_inertStratum`,
  `card_splitStratum`, `card_species3`, `tendsto_geom_partial`, `undecidedCount_two_eq`,
  `undecidedSeq_two_eq`, `gapSeq_two_le`, `decidedSeq_two_ram_eq`, `decidedSeq_two_inert_eq`,
  `decidedDensity_two_{ram,inert,split}_eq`, `genuineDensity_two_exact`, `lowers_three`,
  `drainage_three_of_hex3_bound`, `card_le_undecidedCount_three`. The textual arity mismatch is
  real (still worth fixing in the blueprint's ENV-A block, binding the instance in the SIGNATURE
  of every count node), but it turns out NOT to break the retirement-form 0e-diff: at the four
  such nodes landed so far (`card_dvdSet`, `card_exactSet_add`, `tendsto_geom_partial`,
  `card_species3` — see `Leanspec.lean`'s lifecycle-rule docstring for the mechanism), Lean
  auto-synthesizes the missing instance-implicit from the ambient section `variable` on
  application, exactly as at any ordinary call site, so `example : <stub-header type> :=
  <landedName> (arg := arg) ...` type-checks with no header change. Tested directly (see
  `git log` for the 0e-G unit) before relying on it.
* **D5 — G.03 `readEquiv`, cosmetic.** The declared `left_inv`/`right_inv` scripts need mathlib's
  `ring_nf` fallback rather than `ring1`; `ring` succeeds via its own fallback and emits a
  `Try this: ring_nf` suggestion. No failure.

G.21's signature defect was **pre-declared** by the blueprint and is handled per §12 rule 2 (the
two-hypothesis form is landed); it is not counted above.

**Name collisions with `leanfinal`: cured by the retirement-form lifecycle (0e-G unit,
2026-08-15), not avoided.** The original claim here ("none") held only while no node had yet
landed; once a chapter-G fleet lands a node, its `leanfinal` declaration and this file's
`axiom`/local-body stub share a name in an environment that already contains all of `leanfinal`
(this file imports `Uniformity` wholesale) — 33 such collisions were live at once by the time the
D2/D3 unit's report was written (one per landed node-file; 48 declarations across those 33
files). Every stub below is now in EXACTLY one of the two lifecycle states documented in
`Leanspec.lean`'s root docstring: `axiom` (UNLANDED) or `example := <name>` (LANDED, the
retirement form that cures the collision and machine-checks the type match). Landed as of this
unit (re-verified against `leanfinal/Uniformity/ChapG.lean`'s import list immediately before
finalizing): **G.01–G.07, G.09, G.10, G.12–G.15, G.19, G.21, G.26–G.29, G.32, G.33, G.38, G.39,
G.45, G.50, G.52, G.53, G.55–G.57, G.62, G.64, G.73** (wave-1/2, 33 node-files, 48 declarations),
**plus G.08, G.11, G.16, G.17, G.18, G.20, G.22, G.24, G.25, G.30, G.34, G.40, G.54, G.63** (wave-3,
2026-08-15, 14 node-files, 20 declarations — G.40 and G.63 split into three and two declarations
respectively), **plus G.30a and G.31** (2026-08-15, the G.31 cure unit, 2 node-files, 4
declarations), **plus G.35, G.36, G.37, G.58, G.59, G.65–G.72, G.74** (wave-5, 2026-08-15,
14 node-files, 17 declarations — G.37 and G.72 each split into two, G.66 is a `def` retired at
both strengths per the §A-5 precedent), **plus G.60, G.75, G.76** (wave-5-remainder / "wave-7",
2026-08-15, 3 node-files, 8 declarations — G.60 carries three `def`s and three `theorem`s) —
**66 node-files, 97 declarations retired** in total; see
the individual doc comments below for the retiring `example`. G.23 and G.31 were investigated in
wave-3 and found
BLOCKED. **G.31's block is CLEARED (blueprint AMENDMENT §A-7):** it needed `Finset.range N` in
`decidedSet_ram_eq` justified by showing `depthSet π N t = ∅` for `t ≥ N`, which was not among its
DEPENDS; that general form turns out to be **false** at even `t` in residue characteristic 2, and
the true ODD form — all the odd-indexed union consumes — is now the signed node G.30a, so G.31
landed at its **unchanged** statement. G.23 remains blocked (see the standing G.23a withdrawal
above). Everything else remains an
UNLANDED `axiom` or (for defs not yet landed) a real local body. The `leancheck`-shadowing
direction was checked separately (`leancheck` imports `leanfinal` and opens `Uniformity.Density`
while re-declaring `c3split`, `readEquiv`, `dvdSet`, … in `UniformityCheck`): current-namespace
resolution wins, so no ambiguity is introduced there either.
-/

namespace Uniformity.Density

open IsLocalRing Polynomial Filter Topology

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-! ## §3 — Chapter primitives and the certificate schema (G.01–G.08) -/

namespace Menu

/-- **G.01** `ExactVal π k x` : `x` has valuation exactly `k` with respect to the uniformizer
`π`. LANDED — retirement form (0e-diff against `Uniformity.ChapG.G01`). -/
example (π : O) (k : ℕ) (x : O) : Prop := ExactVal (π := π) (k := k) (x := x)

/-- **G.02a** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G02`). -/
example (hπ : Irreducible π) {k : ℕ} {x : O} :
    ExactVal π k x ↔ IsDiscreteValuationRing.addVal O x = (k : ℕ∞) :=
  exactVal_iff_addVal (hπ := hπ) (k := k) (x := x)

/-- **G.02b** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G02`). -/
example (hπ : Irreducible π) {k k' : ℕ} {x : O}
    (h : ExactVal π k x) (h' : ExactVal π k' x) : k = k' :=
  exactVal_unique (hπ := hπ) (k := k) (k' := k') (x := x) (h := h) (h' := h')

/-- **G.03** The `(value, derivative)` re-coordinatisation of the level-`N` box at the centre
class `γ`. LANDED — retirement form (0e-diff against `Uniformity.ChapG.G03`). -/
example {N : ℕ} (γ : Res O N) : Coeff O 2 N ≃ (Res O N × Res O N) := readEquiv (N := N) (γ := γ)

/-- **G.04** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G04`). -/
example {N : ℕ} (g : O) (a : Fin 2 → O) :
    readEquiv (Ideal.Quotient.mk _ g) (proj O 2 N a)
      = (Ideal.Quotient.mk _ (qval a g), Ideal.Quotient.mk _ (qder a g)) :=
  readEquiv_proj (N := N) (g := g) (a := a)

/-- **G.05a** A level-`N` certified family: a centre-indexed certificate that (i) reads through a
bijection, (ii) survives centre moves inside a fixed coset, (iii) pins the centre's coset, and
(iv) forces one splitting type on every lift. LANDED — retirement form (0e-diff against
`Uniformity.ChapG.G05`). A `structure`'s shape is asserted, per the lifecycle rule's
structures/inductives clause, via one representative field projection's type (`m`) rather than
the type-former itself (which is uninformative: every `structure` former ends in some `Sort`,
so asserting it checks nothing about the eleven fields' own types). -/
example {n N : ℕ} : CertFamily O n N → ℕ := CertFamily.m

/-- **G.05b** The set of level-`N` classes certified by some centre. LANDED — retirement form
(0e-diff against `Uniformity.ChapG.G05`). -/
example {n N : ℕ} (F : CertFamily O n N) : Set (Coeff O n N) := CertFamily.set (F := F)

/-- **G.06** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G06`). -/
example {n N : ℕ} (F : CertFamily O n N) {c : Coeff O n N}
    (hc : c ∈ F.set) : DecidedAt O n F.σ N c :=
  CertFamily.decidedAt (n := n) (N := N) (F := F) (c := c) (hc := hc)

/-- **G.07** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G07`). -/
example {n N : ℕ} (F : CertFamily O n N) :
    Nat.card F.set = residueCard O ^ F.m * Nat.card F.S :=
  CertFamily.card (n := n) (N := N) (F := F)

/-- **G.08** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G08`). -/
example {n N : ℕ} (F : CertFamily O n N) :
    ((residueCard O : ℝ) ^ F.m * (Nat.card F.S : ℝ)) / (residueCard O : ℝ) ^ (n * N)
      ≤ decidedDensity O n F.σ :=
  CertFamily.decidedDensity_ge (n := n) (N := N) (F := F)

/-! ## §4 — `n = 2`: the tangency filtration and its exact level census (G.09–G.23) -/

/-- **G.09** Level-`N` classes admitting a lift with a centre of tangency depth `≥ t`. LANDED —
retirement form (0e-diff against `Uniformity.ChapG.G09`). -/
example (π : O) (N t : ℕ) : Set (Coeff O 2 N) := tangSet (π := π) (N := N) (t := t)

/-- **G.10** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G10`). -/
example {a : Fin 2 → O} {t : ℕ} {γ γ' : O} (h : Tang π a t γ)
    (hδ : π ^ ((t + 1) / 2) ∣ (γ' - γ)) : Tang π a t γ' :=
  tang_shift (a := a) (t := t) (γ := γ) (γ' := γ') (h := h) (hδ := hδ)

/-- **G.11** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G11`). -/
example (hπ : Irreducible π) {a : Fin 2 → O} {t : ℕ} {γ γ' : O}
    (h : Tang π a t γ) (h' : Tang π a t γ') : π ^ ((t + 1) / 2) ∣ (γ' - γ) :=
  tang_centre_unique (hπ := hπ) (a := a) (t := t) (γ := γ) (γ' := γ') (h := h) (h' := h')

/-- **G.12** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G12`). -/
example (hπ : Irreducible π) {N t : ℕ} (ht : t ≤ N) {a b : Fin 2 → O}
    (hab : proj O 2 N a = proj O 2 N b) {γ : O} (h : Tang π a t γ) : Tang π b t γ :=
  tang_of_proj_eq (hπ := hπ) (N := N) (t := t) (ht := ht) (a := a) (b := b) (hab := hab)
    (γ := γ) (h := h)

/-- **G.13a** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G13`). -/
example (hπ : Irreducible π) {N t : ℕ} (ht : t ≤ N) {c : Coeff O 2 N} :
    c ∈ tangSet π N t ↔ ∀ a : Fin 2 → O, proj O 2 N a = c → ∃ γ : O, Tang π a t γ :=
  mem_tangSet_iff (hπ := hπ) (N := N) (t := t) (ht := ht) (c := c)

/-- **G.13b** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G13`). -/
example (hπ : Irreducible π) {N t t' : ℕ} (h : t ≤ t') :
    tangSet π N t' ⊆ tangSet π N t :=
  tangSet_antitone (hπ := hπ) (N := N) (t := t) (t' := t') (h := h)

/-- **G.14a** The classes of valuation `≥ k`. LANDED — retirement form (0e-diff against
`Uniformity.ChapG.G14`). -/
example (π : O) (k N : ℕ) : Set (Res O N) := dvdSet (π := π) (k := k) (N := N)

/-- **G.14b** The classes of valuation exactly `k`. LANDED — retirement form (0e-diff against
`Uniformity.ChapG.G14`). -/
example (π : O) (k N : ℕ) : Set (Res O N) := exactSet (π := π) (k := k) (N := N)

/-- **G.14c** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G14`). D4's
extra-instance concern (below) does not block this conversion: `[Finite (ResidueField O)]` is
auto-synthesized from the ambient section `variable` even though it is absent from this
declaration's own header, exactly as for an ordinary application. -/
example (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (dvdSet π k (k + r)) = residueCard O ^ r :=
  card_dvdSet (hπ := hπ) (k := k) (r := r)

/-- **G.14d** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G14`). -/
example (hπ : Irreducible π) {k r : ℕ} :
    Nat.card (exactSet π k (k + r + 1)) + residueCard O ^ r = residueCard O ^ (r + 1) :=
  card_exactSet_add (hπ := hπ) (k := k) (r := r)

/-- **G.15** The admissible set of the depth-`t` family in `(value, derivative)` coordinates.
LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G15`). -/
example (π : O) (t N : ℕ) : Set (Res O N × Res O N) := tangAdm (π := π) (t := t) (N := N)

/-- **G.16** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G16`). -/
example (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (tangAdm π t (t + r)) * residueCard O ^ ((t + 1) / 2)
      = residueCard O ^ (t + 2 * r) :=
  card_tangAdm (hπ := hπ) (t := t) (r := r)

/-- **G.17 — The tangency-filtration count.** At level `N = t + r`, exactly `q^(t+2r) = q^(2N−t)`
classes admit a centre of tangency depth `≥ t`. This is the level-exact form of W-11's per-node
drainage census, and its `r = 0` case is W-11 clause (iii)'s exact drainage law. LANDED
(wave-3, 2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G17`). -/
example (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (tangSet π (t + r) t) = residueCard O ^ (t + 2 * r) :=
  card_tangSet (hπ := hπ) (t := t) (r := r)

/-- **G.18** The depth-`t` census datum: the three `card_certSet_gen` hypotheses, discharged,
together with the identification of the certified set with `tangSet`.

⚠ **DEFECT D1, repaired minimally.** The blueprint writes `resFactor _ g` on the right of each
equation; that placeholder is unsynthesizable (`don't know how to synthesize placeholder for
argument 'h'`, goal `(t + 1) / 2 ≤ t + r`) and the verbatim signature does not elaborate. Both
occurrences are filled with the `(by omega : …)` proof the blueprint already writes on the left;
the resulting type is the intended one (proof irrelevance). LANDED (wave-3, 2026-08-15) —
retirement form (0e-diff against `Uniformity.ChapG.G18`); the D1 fill above is confirmed
byte-identical to the landed one by this very type-check. -/
example (hπ : Irreducible π) (t r : ℕ) :
    ∃ cert : Res O (t + r) → Coeff O 2 (t + r) → Prop,
      (∀ g c, cert g c ↔ readEquiv g c ∈ tangAdm π t (t + r))
      ∧ (∀ g g' c, cert g c → resFactor (O := O) (by omega : (t+1)/2 ≤ t + r) g'
            = resFactor (by omega : (t+1)/2 ≤ t + r) g → cert g' c)
      ∧ (∀ g g' c, cert g c → cert g' c → resFactor (O := O) (by omega : (t+1)/2 ≤ t + r) g'
            = resFactor (by omega : (t+1)/2 ≤ t + r) g)
      ∧ (∀ c, (∃ g, cert g c) ↔ c ∈ tangSet π (t + r) t) :=
  tangCert (hπ := hπ) (t := t) (r := r)

/-- **G.19** Level-`N` classes whose maximal centre depth is exactly `t`. LANDED (wave-2,
2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G19`). -/
example (π : O) (N t : ℕ) : Set (Coeff O 2 N) := depthSet (π := π) (N := N) (t := t)

/-- **G.20** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G20`). -/
example (hπ : Irreducible π) (t r : ℕ) :
    Nat.card (depthSet π (t + 1 + r) t) + residueCard O ^ (t + 2 * r + 1)
      = residueCard O ^ (t + 2 * r + 2) :=
  card_depthSet (hπ := hπ) (t := t) (r := r)

/-- **G.21** The residual pair `(b₀, b₁)` read at a centre of even depth `2k`, in the residue
field. Landed in the **two-hypothesis form** mandated by blueprint §12 rule 2 (the displayed
SIGNATURE is declared defective by the blueprint itself). LANDED — retirement form (0e-diff
against `Uniformity.ChapG.G21`). -/
noncomputable example {k : ℕ} {a : Fin 2 → O} {γ : O}
    (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ) :
    IsLocalRing.ResidueField O × IsLocalRing.ResidueField O :=
  residualPair (k := k) (a := a) (γ := γ) (h0 := h0) (h1 := h1)

/-- **G.22** Classes of depth exactly `2k` carrying the residual pair `p`. LANDED (wave-3,
2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G22`). -/
example (π : O) (N k : ℕ) (p : IsLocalRing.ResidueField O × IsLocalRing.ResidueField O) :
    Set (Coeff O 2 N) :=
  resStratum (π := π) (N := N) (k := k) (p := p)

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

/-! ### The G.23 REPLACEMENT ROUTE — nodes G.23R1–G.23R12 (blueprint AMENDMENT §A-8)

§A-1 refuted G.23a and derived a replacement route (certify a translation-invariant residual
CLASS at centre modulus `m = k`, not an individual pair). §A-8 expands that derivation into
twelve fireable nodes carrying **25 declarations**; all twelve landed in `leanfinal` in the same
unit that signs them here, so every stub below is written directly in the **retirement form**
`example : <signed type> := <landed name>`, which machine-checks the landed type against the
signed one. Contract count **110 → 135**.
-/

/-- **G.23R1a** The two-coordinate truncation, as an additive group homomorphism. LANDED
(2026-08-15, §A-8) — retirement form (0e-diff against `Uniformity.ChapG.G23R1`). -/
example {m₀ m₁ N : ℕ} (h₀ : m₀ ≤ N) (h₁ : m₁ ≤ N) :
    (Res O N × Res O N) →+ (Res O m₀ × Res O m₁) :=
  prodResFactor (O := O) (h₀ := h₀) (h₁ := h₁)

/-- **G.23R1b** The two-coordinate fibre count, subtraction-free. LANDED (2026-08-15, §A-8). -/
example {m₀ m₁ N : ℕ} (h₀ : m₀ ≤ N) (h₁ : m₁ ≤ N) (S : Set (Res O m₀ × Res O m₁)) :
    Nat.card (prodResFactor (O := O) h₀ h₁ ⁻¹' S) * (residueCard O ^ m₀ * residueCard O ^ m₁)
      = residueCard O ^ N * residueCard O ^ N * Nat.card S :=
  card_preimage_prodResFactor (h₀ := h₀) (h₁ := h₁) (S := S)

/-- **G.23R2a** Digit uniqueness. LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π) {j N : ℕ} (hj : j < N) {y y' : O}
    (h : (Ideal.Quotient.mk _ (π ^ j * y) : Res O N) = Ideal.Quotient.mk _ (π ^ j * y')) :
    IsLocalRing.residue O y = IsLocalRing.residue O y' :=
  residue_eq_of_mk_pow_mul_eq (hπ := hπ) (j := j) (N := N) (hj := hj) (y := y) (y' := y') (h := h)

/-- **G.23R2b** Digit realization. LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π) {j N : ℕ} (hN : N ≤ j + 1) {y y' : O}
    (h : IsLocalRing.residue O y = IsLocalRing.residue O y') :
    (Ideal.Quotient.mk _ (π ^ j * y) : Res O N) = Ideal.Quotient.mk _ (π ^ j * y') :=
  mk_pow_mul_eq_of_residue_eq (hπ := hπ) (j := j) (N := N) (hN := hN) (y := y) (y' := y') (h := h)

/-- **G.23R3a** The residual translation `y ↦ y + d` read on residual pairs. LANDED
(2026-08-15, §A-8). -/
example {K : Type*} [CommRing K] (d : K) (p : K × K) : K × K := transPair (d := d) (p := p)

/-- **G.23R3b** Translation-invariance of a residual class. LANDED (2026-08-15, §A-8). -/
example {K : Type*} [CommRing K] (P : Set (K × K)) : Prop := TransInvariant (P := P)

/-- **G.23R3c** LANDED (2026-08-15, §A-8). -/
example {K : Type*} [Field K] : TransInvariant {p : K × K | AniForm p} :=
  aniForm_transInvariant (K := K)

/-- **G.23R3d** LANDED (2026-08-15, §A-8). -/
example {K : Type*} [Field K] : TransInvariant {p : K × K | SepPair p} :=
  sepPair_transInvariant (K := K)

/-- **G.23R3e** LANDED (2026-08-15, §A-8). -/
example {K : Type*} [Field K] {p : K × K} (h : AniForm p) : ¬ DblPair p :=
  aniForm_not_dblPair (K := K) (p := p) (h := h)

/-- **G.23R3f** LANDED (2026-08-15, §A-8). -/
example {K : Type*} [Field K] {p : K × K} (h : SepPair p) : ¬ DblPair p :=
  sepPair_not_dblPair (K := K) (p := p) (h := h)

/-- **G.23R4a** The residual-class admissible set at the TOP levels `(2k+1, k+1)`. LANDED
(2026-08-15, §A-8). -/
example (π : O) (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k : ℕ) :
    Set (Res O (2 * k + 1) × Res O (k + 1)) := resTop (π := π) (P := P) (k := k)

/-- **G.23R4b** The residual-class admissible set at level `N`. LANDED (2026-08-15, §A-8). -/
example (π : O) (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k N : ℕ) :
    Set (Res O N × Res O N) := resAdm (π := π) (P := P) (k := k) (N := N)

/-- **G.23R4c** The level-`N` classes carrying a residual pair in `P` at a centre of depth
`≥ 2k`. LANDED (2026-08-15, §A-8). -/
example (π : O) (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k N : ℕ) :
    Set (Coeff O 2 N) := resClassSet (π := π) (P := P) (k := k) (N := N)

/-- **G.23R4d** LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)} {k N : ℕ}
    (h₀ : 2 * k + 1 ≤ N) (h₁ : k + 1 ≤ N) :
    resAdm π P k N = prodResFactor (O := O) h₀ h₁ ⁻¹' resTop π P k :=
  resAdm_eq_preimage (hπ := hπ) (P := P) (k := k) (N := N) (h₀ := h₀) (h₁ := h₁)

/-- **G.23R5** LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π)
    (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k : ℕ) :
    Nat.card (resTop π P k) = Nat.card P := card_resTop (hπ := hπ) (P := P) (k := k)

/-- **G.23R6** LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π)
    (P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)) (k r : ℕ) :
    Nat.card (resAdm π P k (2 * k + 1 + r)) = Nat.card P * residueCard O ^ (k + 2 * r) :=
  card_resAdm (hπ := hπ) (P := P) (k := k) (r := r)

/-- **G.23R7** The certificate bridge. LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)} {k N : ℕ}
    (h₀ : 2 * k < N) (h₁ : k < N) (γ : O) (a : Fin 2 → O) :
    readEquiv (Ideal.Quotient.mk _ γ) (proj O 2 N a) ∈ resAdm π P k N
      ↔ ∃ b₀ b₁ : O, qval a γ = π ^ (2 * k) * b₀ ∧ qder a γ = π ^ k * b₁ ∧
          (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) ∈ P :=
  resAdm_read_iff (hπ := hπ) (P := P) (k := k) (N := N) (h₀ := h₀) (h₁ := h₁) (γ := γ) (a := a)

/-- **G.23R8** The residual-class census datum at centre modulus `m = k`. LANDED
(2026-08-15, §A-8). -/
example (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)}
    (hP : TransInvariant P) (k r : ℕ) :
    ∃ cert : Res O (2 * k + 1 + r) → Coeff O 2 (2 * k + 1 + r) → Prop,
      (∀ g c, cert g c ↔ readEquiv g c ∈ resAdm π P k (2 * k + 1 + r))
      ∧ (∀ g g' c, cert g c → resFactor (O := O) (by omega : k ≤ 2 * k + 1 + r) g'
            = resFactor (by omega : k ≤ 2 * k + 1 + r) g → cert g' c)
      ∧ (∀ g g' c, cert g c → cert g' c → resFactor (O := O) (by omega : k ≤ 2 * k + 1 + r) g'
            = resFactor (by omega : k ≤ 2 * k + 1 + r) g)
      ∧ (∀ c, (∃ g, cert g c) ↔ c ∈ resClassSet π P k (2 * k + 1 + r)) :=
  resCert (hπ := hπ) (P := P) (hP := hP) (k := k) (r := r)

/-- **G.23R9 — THE COUNT FORMULA** of the replacement route, and G.23a's replacement on the
critical path: at level `N = 2k+1+r` the classes carrying a residual pair in a
translation-invariant class `P` at a centre of depth `≥ 2k` number `#P · q^(2k+2r)`, i.e.
`#P · q^(2N−2k−2)`. LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)}
    (hP : TransInvariant P) (k r : ℕ) :
    Nat.card (resClassSet π P k (2 * k + 1 + r))
      = Nat.card P * residueCard O ^ (2 * k + 2 * r) :=
  card_resClassSet (hπ := hπ) (P := P) (hP := hP) (k := k) (r := r)

/-- **G.23R10a** G.21's computation rule. LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π) {k : ℕ} {a : Fin 2 → O} {γ b₀ b₁ : O}
    (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ)
    (e0 : qval a γ = π ^ (2 * k) * b₀) (e1 : qder a γ = π ^ k * b₁) :
    residualPair h0 h1 = (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) :=
  residualPair_eq (hπ := hπ) (k := k) (a := a) (γ := γ) (b₀ := b₀) (b₁ := b₁)
    (h0 := h0) (h1 := h1) (e0 := e0) (e1 := e1)

/-- **G.23R10b** LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)} {k N : ℕ}
    {c : Coeff O 2 N} :
    c ∈ resClassSet π P k N
      ↔ ∃ (a : Fin 2 → O) (γ : O) (h0 : π ^ (2 * k) ∣ qval a γ) (h1 : π ^ k ∣ qder a γ),
          proj O 2 N a = c ∧ residualPair h0 h1 ∈ P :=
  mem_resClassSet_iff_residualPair (hπ := hπ) (P := P) (k := k) (N := N) (c := c)

/-- **G.23R11** LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π)
    {P : Set (IsLocalRing.ResidueField O × IsLocalRing.ResidueField O)}
    (hP : ∀ p ∈ P, ¬ DblPair p) {k N : ℕ} (hN : 2 * k + 1 ≤ N) :
    resClassSet π P k N ⊆ depthSet π N (2 * k) :=
  resClassSet_subset_depthSet (hπ := hπ) (P := P) (hP := hP) (k := k) (N := N) (hN := hN)

/-- **G.23R12a** LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π) (x : O) : IsLocalRing.residue O x = 0 ↔ π ∣ x :=
  residue_eq_zero_iff_dvd (hπ := hπ) (x := x)

/-- **G.23R12b** The anisotropy bridge. LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π) (b₀ b₁ : O) :
    Anisotropic ![b₀, b₁] ↔ AniForm (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁) :=
  aniso_iff_aniForm (hπ := hπ) (b₀ := b₀) (b₁ := b₁)

/-- **G.23R12c** The separable-split bridge. LANDED (2026-08-15, §A-8). -/
example (hπ : Irreducible π) (b₀ b₁ : O) :
    SepPair (IsLocalRing.residue O b₀, IsLocalRing.residue O b₁)
      ↔ ∃ z : O, π ∣ (z ^ 2 + b₁ * z + b₀) ∧ ¬ π ∣ (b₁ + 2 * z) :=
  sepPair_iff_exists_simple_root (hπ := hπ) (b₀ := b₀) (b₁ := b₁)

/-! ## §5 — `n = 2`: type classification by depth (G.24–G.31) -/

/-- **G.24** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G24`). -/
example (hπ : Irreducible π) {N j : ℕ} {a : Fin 2 → O}
    (hmem : proj O 2 N a ∈ depthSet π N (2 * j + 1)) (hN : 2 * j + 2 ≤ N) :
    CertRam π a (2 * j + 2) :=
  certRam_of_depth_odd (hπ := hπ) (N := N) (j := j) (a := a) (hmem := hmem) (hN := hN)

/-- **G.25** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G25`). -/
example (hπ : Irreducible π) {N j : ℕ} {c : Coeff O 2 N}
    (hmem : c ∈ depthSet π N (2 * j + 1)) (hN : 2 * j + 2 ≤ N) :
    DecidedAt O 2 ramType N c :=
  decidedAt_ram_of_depth_odd (hπ := hπ) (N := N) (j := j) (c := c) (hmem := hmem) (hN := hN)

/-- **G.26** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G26`). Named-argument
application throughout this file's conversions (not just here) is load-bearing, not stylistic:
`N` above is genuinely unused in the statement (also flagged by the linter on the landed
`Uniformity.ChapG.G26.lean`), so positional reapplication leaves its implicit metavariable
unsynthesizable — `example ... := depth_even_dichotomy hπ hT hmax h0 h1` fails with "don't know
how to synthesize implicit argument `N`"; binding every parameter by name sidesteps this
uniformly. -/
example (hπ : Irreducible π) {N k : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a (2 * k) γ) (hmax : ¬ ∃ γ', Tang π a (2 * k + 1) γ')
    {b₀ b₁ : O} (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁) :
    Anisotropic ![b₀, b₁] ∨ ∃ z : O, π ∣ (z ^ 2 + b₁ * z + b₀) ∧ ¬ π ∣ (b₁ + 2 * z) :=
  depth_even_dichotomy (hπ := hπ) (N := N) (k := k) (a := a) (γ := γ) (hT := hT) (hmax := hmax)
    (b₀ := b₀) (b₁ := b₁) (h0 := h0) (h1 := h1)

/-- **G.27** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G27`). -/
example (hπ : Irreducible π) {N k : ℕ} {a : Fin 2 → O} {γ : O}
    {b₀ b₁ : O} (hN : 2 * k + 1 ≤ N)
    (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁)
    (hani : Anisotropic ![b₀, b₁]) :
    DecidedAt O 2 inertType N (proj O 2 N a) :=
  decidedAt_inert_of_ani (hπ := hπ) (N := N) (k := k) (a := a) (γ := γ) (b₀ := b₀) (b₁ := b₁)
    (hN := hN) (h0 := h0) (h1 := h1) (hani := hani)

/-- **G.28** — window hypothesis AMENDED to `2 * k + 1 ≤ N` (was `2 * k + 2 ≤ N`) per blueprint
AMENDMENT 2026-08-15 §A-2: the node's own proof uses only `2 * k + 1 ≤ N`, `CertSplit` asks only
`2 * w + 1 ≤ N`, `CertSplit_congr` transports at equality, and `typeOf_of_certSplit` discards the
window bound — so the top even stratum `t = N − 1` is covered and G.42 is provable at `r = 0`.
LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G28`); the
amended window hypothesis above is confirmed byte-identical to the landed one by this very
type-check. -/
example (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N k : ℕ} {a : Fin 2 → O} {γ z : O}
    {b₀ b₁ : O} (hN : 2 * k + 1 ≤ N)
    (h0 : qval a γ = π ^ (2 * k) * b₀) (h1 : qder a γ = π ^ k * b₁)
    (hz : π ∣ (z ^ 2 + b₁ * z + b₀)) (hs : ¬ π ∣ (b₁ + 2 * z)) :
    DecidedAt O 2 splitType N (proj O 2 N a) :=
  decidedAt_split_of_sep (hπ := hπ) (N := N) (k := k) (a := a) (γ := γ) (z := z) (b₀ := b₀)
    (b₁ := b₁) (hN := hN) (h0 := h0) (h1 := h1) (hz := hz) (hs := hs)

/-- **G.29** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G29`). -/
example (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {N : ℕ} {c : Coeff O 2 N}
    (hc : c ∉ tangSet π N N) {a : Fin 2 → O} (ha : proj O 2 N a = c) :
    DecidedAt O 2 (typeOf (monicPoly a)) N c :=
  decidedAt_of_depth_lt (hπ := hπ) (N := N) (c := c) (hc := hc) (a := a) (ha := ha)

/-- **G.30** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G30`); confirms the withdrawn `⚠ BOUNDARY CONDITION` block (blueprint AMENDMENT
§A-2) is moot — the even branch needs only `t < N`, matching G.28's amended window. -/
example (hπ : Irreducible π) [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {N t : ℕ} (ht : t < N) {c : Coeff O 2 N} (hc : c ∈ depthSet π N t) :
    (∃ j, t = 2 * j + 1 ∧ DecidedAt O 2 ramType N c)
      ∨ (∃ k, t = 2 * k ∧ (DecidedAt O 2 inertType N c ∨ DecidedAt O 2 splitType N c)) :=
  depth_type (hπ := hπ) (N := N) (t := t) (ht := ht) (c := c) (hc := hc)

/-- **G.30a** *(NEW NODE — blueprint AMENDMENT 2026-08-15 §A-7, the dependency-gap cure for
G.31.)* Odd depth strata above the level-`N` window are empty. **Only the ODD form is signed:**
the general shape `depthSet π N t = ∅ for t ≥ N` — the one wave-3 booked as G.31's missing
premise — is REFUTED at even `t` in residue characteristic 2 (§A-7's `ℤ₂`, `N = 2`, `t = 2`
counterexample). G.31's union is odd-indexed, so this form is what it consumes. ENV-A' (no
completeness). LANDED (2026-08-15, G.31 cure unit) — retirement form (0e-diff against
`Uniformity.ChapG.G30a`). -/
example (hπ : Irreducible π) {N j : ℕ} (hN : N ≤ 2 * j + 1) :
    depthSet π N (2 * j + 1) = (∅ : Set (Coeff O 2 N)) :=
  depthSet_odd_eq_empty (hπ := hπ) (N := N) (j := j) (hN := hN)

/-- **G.31a** The inert half of an even stratum. LANDED (2026-08-15, G.31 cure unit) —
retirement form (0e-diff against `Uniformity.ChapG.G31`), in both available strengths: the
type-level `example` prescribed by the lifecycle rule for `def`s, plus a `rfl` check that the
landed BODY is the signed one (the §A-5 precedent — a type-only check cannot see body drift). -/
example (π : O) (N k : ℕ) : Set (Coeff O 2 N) := inertStratum (π := π) (N := N) (k := k)

example (π : O) (N k : ℕ) :
    inertStratum π N k = {c ∈ depthSet π N (2 * k) | DecidedAt O 2 inertType N c} := rfl

/-- **G.31b** The split half of an even stratum. LANDED (2026-08-15, G.31 cure unit) —
retirement form, type and body, as at G.31a. -/
example (π : O) (N k : ℕ) : Set (Coeff O 2 N) := splitStratum (π := π) (N := N) (k := k)

example (π : O) (N k : ℕ) :
    splitStratum π N k = {c ∈ depthSet π N (2 * k) | DecidedAt O 2 splitType N c} := rfl

/-- **G.31c** LANDED (2026-08-15, G.31 cure unit) — retirement form (0e-diff against
`Uniformity.ChapG.G31`). The node was BLOCKED at wave 3 for a missing premise, **not** a
statement defect: this type-check confirms the landed theorem is the one signed here, index set
`Finset.range N` included. The overshoot `N ≤ 2j+1` is discharged by G.30a above. -/
example (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    decidedSet O 2 ramType N = ⋃ j ∈ Finset.range N, depthSet π N (2 * j + 1) :=
  decidedSet_ram_eq (hπ := hπ) (N := N)

/-! ## §6 — `n = 2`: the exact drainage law (G.32–G.37) -/

/-- **G.32** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G32`). -/
example (K : Type*) [Field K] [Finite K] {b₁ : K} (hb : b₁ ≠ 0) :
    ∃ b₀ : K, AniForm (b₀, b₁) :=
  exists_aniForm_of_ne_zero (K := K) (b₁ := b₁) (hb := hb)

/-- **G.33** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G33`). -/
example (hπ : Irreducible π) {N : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a N γ) :
    ∃ b : Fin 2 → O, proj O 2 N b = proj O 2 N a ∧ typeOf (monicPoly b) = splitType :=
  exists_split_lift (hπ := hπ) (N := N) (a := a) (γ := γ) (hT := hT)

/-- **G.34** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G34`). The private Case-A helper `exists_inert_lift_of_ne_zero` is not part of
the blueprint's contract surface and is not re-signed here. -/
example (hπ : Irreducible π) {N : ℕ} {a : Fin 2 → O} {γ : O}
    (hT : Tang π a N γ) :
    ∃ b : Fin 2 → O, proj O 2 N b = proj O 2 N a ∧ typeOf (monicPoly b) = inertType :=
  exists_inert_lift (hπ := hπ) (N := N) (a := a) (γ := γ) (hT := hT)

/-- **G.35** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G35`). -/
example (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (N : ℕ) :
    undecidedSet O 2 N = tangSet π N N :=
  undecidedSet_eq_tangSet (hπ := hπ) (N := N)

end Menu

/-- **G.36 — W-11 clause (iii), exactly: the `n = 2` σ-undecided count is `q^N`.** Every complete
DVR with finite residue field, every level `N`, both characteristics, wild residue characteristic
included. This is the exact form of the landed bound `undecidedCount_le` (which gives only
`q^(3M)` at level `2M`). LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G36`), the chapter's headline node. -/
example [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    undecidedCount O 2 N = residueCard O ^ N :=
  undecidedCount_two_eq (N := N)

/-- **G.37a** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G37`). -/
example [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    undecidedSeq O 2 N = (1 / (residueCard O : ℝ)) ^ N :=
  undecidedSeq_two_eq (N := N)

/-- **G.37b** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G37`). -/
example [IsAdicComplete (maximalIdeal O) O] (σ : FactorizationType) (N : ℕ) :
    gapSeq O 2 σ N ≤ (1 / (residueCard O : ℝ)) ^ N :=
  gapSeq_two_le (σ := σ) (N := N)

/-! ## §7 — `n = 2`: exact counts, exact densities, the capstone slice (G.38–G.51) -/

namespace Menu

/-- **G.38** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G38`). -/
example (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {p : K × K // AniForm p} + Nat.card K = Nat.card K * Nat.card K :=
  two_mul_card_aniForm (K := K)

/-- **G.39a** `p = (b₀, b₁)` is a *separable-split* pair: `X² − b₁X + b₀` has two distinct
roots. LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G39`). -/
example {K : Type*} [Field K] (p : K × K) : Prop := SepPair (K := K) (p := p)

/-- **G.39b** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G39`). -/
example (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {p : K × K // SepPair p} + Nat.card K = Nat.card K * Nat.card K :=
  two_mul_card_sepPair (K := K)

/-- **G.40a** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G40`). -/
example {K : Type*} [Field K] (p : K × K) : Prop := DblPair (K := K) p

/-- **G.40b** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G40`). -/
example (K : Type*) [Field K] [Finite K] :
    Nat.card {p : K × K // DblPair p} = Nat.card K :=
  card_dblPair (K := K)

/-- **G.40c** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G40`). -/
example {K : Type*} [Field K] (p : K × K) :
    AniForm p ∨ SepPair p ∨ DblPair p :=
  pair_trichotomy (K := K) (p := p)

/-- **G.41** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G41`). -/
example (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (k r : ℕ) :
    2 * Nat.card (inertStratum π (2 * k + 1 + r) k) + residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ (2 * k + 2 * r + 2) :=
  card_inertStratum (hπ := hπ) (k := k) (r := r)

/-- **G.42** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G42`). -/
example (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (k r : ℕ) :
    2 * Nat.card (splitStratum π (2 * k + 1 + r) k) + residueCard O ^ (2 * k + 2 * r + 1)
      = residueCard O ^ (2 * k + 2 * r + 2) :=
  card_splitStratum (hπ := hπ) (k := k) (r := r)

end Menu

/-- **G.43 — W-11's every-window identity, exactly:** at every level the split-decided and
inert-decided classes are equinumerous — not merely equal in the limit. The mechanism is the
residue-field coincidence `#{anisotropic pairs} = #{separable-split pairs} = q(q−1)/2`.
LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G43`). -/
example [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedCount O 2 splitType N = decidedCount O 2 inertType N :=
  decidedCount_split_eq_inert (N := N)

/-- **G.44a** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G44`), **with the signed index set CORRECTED**: the stub read
`Finset.range ((N + 1) / 2)`, which is **FALSE at every odd `N`** — at `N = 1` the left-hand side
is `0` (`depthSet π 1 1 = ∅` by G.30a) while the signed right-hand side is `(q−1)/q² > 0`. The
refutation is machine-checked at `O := ℤ_[2]`. The genuine ram index set is
`{j | 2*j+2 ≤ N} = Finset.range (N / 2)`; the inert index set of G.44b is correct as signed.
See blueprint AMENDMENT §A-9.1. -/
example [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedSeq O 2 ramType N
      = ∑ j ∈ Finset.range (N / 2),
          ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ (2 * j + 2) :=
  decidedSeq_two_ram_eq (N := N)

/-- **G.44b** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G44`). Signed index set unchanged: `k < (N+1)/2 ↔ 2*k+1 ≤ N` is exact here. -/
example [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    decidedSeq O 2 inertType N
      = ∑ k ∈ Finset.range ((N + 1) / 2),
          ((residueCard O : ℝ) - 1) / (2 * (residueCard O : ℝ) ^ (2 * k + 1)) :=
  decidedSeq_two_inert_eq (N := N)

namespace Menu

/-- **G.45** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G45`). Another D4 node
(see G.14c): `[Finite (ResidueField O)]` is absent from this header but auto-synthesized from the
ambient section `variable` on application, so the conversion is unaffected. -/
example (c : ℝ) (d : ℕ) {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun N => ∑ i ∈ Finset.range (f N), c / (residueCard O : ℝ) ^ (2 * i + d)) atTop
      (𝓝 (c / (residueCard O : ℝ) ^ d * ((residueCard O : ℝ) ^ 2
        / ((residueCard O : ℝ) ^ 2 - 1)))) :=
  tendsto_geom_partial (c := c) (d := d) (f := f) (hf := hf)

end Menu

/-- **G.46** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G46`). -/
example [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1) :=
  decidedDensity_two_ram_eq (O := O)

/-- **G.47a** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G47`). -/
example [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1)) :=
  decidedDensity_two_inert_eq (O := O)

/-- **G.47b** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G47`). The node file lands this value TWICE by disjoint routes, as the blueprint
requires: `decidedDensity_two_split_eq` from G.43's every-window COUNT identity (new to the corpus)
and `decidedDensity_two_split_eq_of_total` by subtraction from the landed total mass (the
`leancheck` route). The signed contract is the first; the second is the mutual check. -/
example [IsAdicComplete (maximalIdeal O) O] :
    decidedDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1)) :=
  decidedDensity_two_split_eq (O := O)

/-- **G.48 — THE `n = 2` DENSITY FUNCTION, EXACTLY.** Over every complete DVR with finite residue
field, both characteristics, wild residue characteristic included. LANDED (wave-8, 2026-08-15) —
retirement form (0e-diff against `Uniformity.ChapG.G48`). -/
example [IsAdicComplete (maximalIdeal O) O] :
    genuineDensity O 2 splitType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 inertType = (residueCard O : ℝ) / (2 * ((residueCard O : ℝ) + 1))
    ∧ genuineDensity O 2 ramType = 1 / ((residueCard O : ℝ) + 1)
    ∧ (∀ σ : FactorizationType, σ ≠ splitType → σ ≠ inertType → σ ≠ ramType →
        genuineDensity O 2 σ = 0) :=
  genuineDensity_two_exact (O := O)

/-- **G.49a** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G49`). This closes the landed bracket `gate_bracket_padic_two` to a point. -/
example :
    genuineDensity ℤ_[2] 2 splitType = 1 / 3 ∧ genuineDensity ℤ_[2] 2 inertType = 1 / 3
      ∧ genuineDensity ℤ_[2] 2 ramType = 1 / 3 :=
  gate_two_padic_two_exact

/-- **G.49b** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G49`). -/
example :
    genuineDensity ℤ_[3] 2 splitType = 3 / 8 ∧ genuineDensity ℤ_[3] 2 inertType = 3 / 8
      ∧ genuineDensity ℤ_[3] 2 ramType = 1 / 4 :=
  gate_two_padic_three_exact

/-- **G.50** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G50`). -/
example {σ : FactorizationType} (hσ : σ.degree = 2) :
    σ = splitType ∨ σ = inertType ∨ σ = ramType ∨
      (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        genuineDensity O 2 σ = 0) :=
  degree_two_type_cases (σ := σ) (hσ := hσ)

/-- **G.51 — `UniformityStatement` at `n = 2`.** One rational function per degree-2 type, valid at
every complete DVR with finite residue field — wild residue characteristic included, both
characteristics. Unconditional: no drainage hypothesis, no axiom, Lean core only.
LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G51`).
**This is NOT `UniformityStatement`**, which quantifies over all `n > 0`; it is its `n = 2` slice.
-/
example (σ : FactorizationType) (hσ : σ.degree = 2) :
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧
      ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
        den.eval ((residueCard O : ℕ) : ℚ) ≠ 0 ∧
          genuineDensity O 2 σ
            = ((num.eval ((residueCard O : ℕ) : ℚ) / den.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) :=
  uniformityStatement_two (σ := σ) (hσ := hσ)

/-! ## §8 — `n = 3`: the five types, the menu, the leaf certificates (G.52–G.61) -/

/-- **G.52a** `{(1,1),(1,1),(1,1)}` — three unramified linear factors. LANDED — retirement form
(0e-diff against `Uniformity.ChapG.G52`). -/
example : FactorizationType := c3split
/-- **G.52b** `{(1,1),(1,2)}` — a linear factor and an unramified quadratic. LANDED — retirement
form (0e-diff against `Uniformity.ChapG.G52`). -/
example : FactorizationType := c3linInert
/-- **G.52c** `{(1,3)}` — one unramified cubic factor. LANDED — retirement form (0e-diff against
`Uniformity.ChapG.G52`). -/
example : FactorizationType := c3inert
/-- **G.52d** `{(1,1),(2,1)}` — a linear factor and a ramified quadratic. LANDED — retirement
form (0e-diff against `Uniformity.ChapG.G52`). -/
example : FactorizationType := c3linRam
/-- **G.52e** `{(3,1)}` — one totally ramified cubic factor. LANDED — retirement form (0e-diff
against `Uniformity.ChapG.G52`). -/
example : FactorizationType := c3ram

/-- **G.52f** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G52`). -/
example :
    c3split.degree = 3 ∧ c3linInert.degree = 3 ∧ c3inert.degree = 3
      ∧ c3linRam.degree = 3 ∧ c3ram.degree = 3 := c3_degrees

/-- **G.52g** The ten pairwise inequalities. Signature per blueprint **AMENDMENT §A-6** (D3 cured
2026-08-15): the placeholder `/- the ten inequalities -/ True` is replaced by the ten inequalities
themselves — the five cubic type constants pairwise distinct as `FactorizationType`s, in the
`leancheck/UniformityCheck/N3Base.lean` enumeration order. LANDED — retirement form (0e-diff
against `Uniformity.ChapG.G52`); the D3-cured signature above is confirmed byte-identical to the
landed one by this very type-check. -/
example :
    c3split ≠ c3linInert ∧ c3split ≠ c3inert ∧ c3split ≠ c3linRam ∧ c3split ≠ c3ram
      ∧ c3linInert ≠ c3inert ∧ c3linInert ≠ c3linRam ∧ c3linInert ≠ c3ram
      ∧ c3inert ≠ c3linRam ∧ c3inert ≠ c3ram
      ∧ c3linRam ≠ c3ram := c3_pairwise_ne

/-- **G.53 — Exactly five splitting types occur in degree 3.** No Newton polygon, no Hensel: the
statement is a consequence of `typeOf_degree` and the positivity of every `(e,f)` pair. LANDED
(wave-2, 2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G53`). -/
example (a : Fin 3 → O) :
    typeOf (monicPoly a) = c3split ∨ typeOf (monicPoly a) = c3linInert
      ∨ typeOf (monicPoly a) = c3inert ∨ typeOf (monicPoly a) = c3linRam
      ∨ typeOf (monicPoly a) = c3ram :=
  typeOf_three_cases (a := a)

/-- **G.54a** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G54`). -/
example :
    CoveringMenu O 3 ({c3split, c3linInert, c3inert, c3linRam, c3ram} : Finset FactorizationType) :=
  coveringMenu_three

/-- **G.54b** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G54`). -/
example {σ : FactorizationType} (hs : σ ≠ c3split)
    (hi : σ ≠ c3linInert) (hc : σ ≠ c3inert) (hr : σ ≠ c3linRam) (ht : σ ≠ c3ram) :
    genuineDensity O 3 σ = 0 :=
  genuineDensity_three_eq_zero (hs := hs) (hi := hi) (hc := hc) (hr := hr) (ht := ht)

/-- **G.55** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G55`). -/
example [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (ρ₁ ρ₂ ρ₃ : O) (h12 : IsUnit (ρ₁ - ρ₂)) (h13 : IsUnit (ρ₁ - ρ₃)) (h23 : IsUnit (ρ₂ - ρ₃))
    (hres : (monicPoly a).map (residue O)
      = (X - C (residue O ρ₁)) * (X - C (residue O ρ₂)) * (X - C (residue O ρ₃))) :
    typeOf (monicPoly a) = c3split :=
  typeOf_split3_of_residue (a := a) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃) (h12 := h12) (h13 := h13)
    (h23 := h23) (hres := hres)

/-- **G.56** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G56`). -/
example [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    {ρ : O} {g₀ : Polynomial (ResidueField O)} (hg₀ : g₀.Monic) (hdeg : g₀.natDegree = 2)
    (hirr : Irreducible g₀)
    (hres : (monicPoly a).map (residue O) = (X - C (residue O ρ)) * g₀) :
    typeOf (monicPoly a) = c3linInert :=
  typeOf_linInert_of_residue (a := a) (ρ := ρ) (g₀ := g₀) (hg₀ := hg₀) (hdeg := hdeg)
    (hirr := hirr) (hres := hres)

/-- **G.57** LANDED (wave-2, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G57`). -/
example [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (h : Irreducible ((monicPoly a).map (residue O))) : typeOf (monicPoly a) = c3inert :=
  typeOf_inert3_of_irreducible_map (a := a) (h := h)

/-- **G.58** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G58`), the cheapest cubic leaf certificate. -/
example {a : Fin 3 → O}
    (hlow : ∀ i : Fin 3, a i ∈ maximalIdeal O) (h0 : a 0 ∉ (maximalIdeal O) ^ 2) :
    typeOf (monicPoly a) = c3ram :=
  typeOf_ram3_of_eisenstein (a := a) (hlow := hlow) (h0 := h0)

/-- **G.59** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G59`). -/
example [IsAdicComplete (maximalIdeal O) O] {a : Fin 3 → O}
    (h2 : IsUnit (a 2)) (h1 : a 1 ∈ maximalIdeal O) (h0 : a 0 ∈ maximalIdeal O)
    (h0' : a 0 ∉ (maximalIdeal O) ^ 2) : typeOf (monicPoly a) = c3linRam :=
  typeOf_linRam_of_residue (a := a) (h2 := h2) (h1 := h1) (h0 := h0) (h0' := h0')

namespace Menu

/-- **G.60a** The monic cubic `X³ + c 2 X² + c 1 X + c 0` has no root in `K`. LANDED (wave-7,
2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G60`). -/
example (K : Type*) [Field K] (c : Fin 3 → K) : Prop := NoRootCubic (K := K) c

/-- **G.60b** LANDED (wave-7, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G60`). -/
example (K : Type*) [Field K] (c : Fin 3 → K) : Prop := LinAni (K := K) c

/-- **G.60c** LANDED (wave-7, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G60`). -/
example (K : Type*) [Field K] (c : Fin 3 → K) : Prop := Split3 (K := K) c

/-- **G.60d** LANDED (wave-7, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G60`): re-derived from `leancheck`'s `CubicCount.three_mul_card_noRootCubic`
against `leanfinal`'s own `AniForm` (G.38), not imported. -/
example (K : Type*) [Field K] [Finite K] :
    3 * Nat.card {c : Fin 3 → K // NoRootCubic c} + Nat.card K = Nat.card K ^ 3 :=
  three_mul_card_noRootCubic (K := K)

/-- **G.60e** LANDED (wave-7, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G60`). -/
example (K : Type*) [Field K] [Finite K] :
    2 * Nat.card {c : Fin 3 → K // LinAni c} + Nat.card K ^ 2 = Nat.card K ^ 3 :=
  two_mul_card_linAni (K := K)

/-- **G.60f** LANDED (wave-7, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G60`). -/
example (K : Type*) [Field K] [Finite K] :
    6 * Nat.card {c : Fin 3 → K // Split3 c} + 3 * Nat.card K ^ 2 = Nat.card K ^ 3 + 2 * Nat.card K :=
  six_mul_card_split3 (K := K)

end Menu

/-- **G.61** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G61`, whose five conjuncts are SPLIT-MANDATED across `G61a`…`G61e` over the
shared infrastructure `G61I`). **These are LOWER BOUNDS, not the densities** (chapter honesty block
H-4): HM3.D's five closed forms `q³(q²−q+1)/(6(q+1)Φ)`, `q³(q²+q+1)/(2(q+1)Φ)`, `q³(q+1)/(3Φ)`,
`q(q³+q+1)/((q+1)Φ)`, `(q²+1)/Φ` with `Φ = q⁴+q³+q²+q+1` are NOT proved here. -/
example [IsAdicComplete (maximalIdeal O) O] :
    1 / (residueCard O : ℝ) ^ 9 ≤ decidedDensity O 3 c3split
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ) ^ 2) / (2 * (residueCard O : ℝ) ^ 3)
        ≤ decidedDensity O 3 c3linInert
    ∧ ((residueCard O : ℝ) ^ 3 - (residueCard O : ℝ)) / (3 * (residueCard O : ℝ) ^ 3)
        ≤ decidedDensity O 3 c3inert
    ∧ ((residueCard O : ℝ) - 1) ^ 2 / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3linRam
    ∧ ((residueCard O : ℝ) - 1) / (residueCard O : ℝ) ^ 4 ≤ decidedDensity O 3 c3ram :=
  lowers_three (O := O)

/-! ## §9 — the 53-family index and the HEX3 arithmetic layer (G.62–G.72) -/

namespace Menu

/-- **G.62a** The ANNEX-B index of the cubic core menu: 53 formal families in five tiers. This is
an INDEX, not a family: it carries no counts and no certificates. See the chapter honesty block
H-3. LANDED — retirement form (0e-diff against `Uniformity.ChapG.G62`). Per the lifecycle rule's
structures/inductives clause, an `inductive`'s shape is asserted via its constructors' types —
here all five, since each fixes a different `Fin` arity (`3, 4, 11, 11, 24`) that is exactly the
five-tier count the node's own docstring states. -/
example : Fin 3 → CubicFamilyIndex := CubicFamilyIndex.sep
example : Fin 4 → CubicFamilyIndex := CubicFamilyIndex.dbl
example : Fin 11 → CubicFamilyIndex := CubicFamilyIndex.tierI
example : Fin 11 → CubicFamilyIndex := CubicFamilyIndex.tierII
example : Fin 24 → CubicFamilyIndex := CubicFamilyIndex.bTier

/-- **G.62b** The shape schema underlying each formal family (ANNEX B's "33 shape schemas").

Body per blueprint **AMENDMENT §A-5** (D2 cured 2026-08-15): the 53 → 33 assignment derived from
`EFF-HMENU3` ANNEX B. `Fin 33` is read as the five consecutive blocks `0–2` SEP, `3–6` DBL,
`7–13` tier I, `14–20` tier II, `21–32` B-tier (`EFF.HMENU3.69`'s schema column, `3+4+7+7+12`).
SEP and DBL are unrefined, so those fibers are singletons (`.69`, both rows "—"); each TRP tier's
four λ-free schemas (RAM3, 3LIN, LINRAM2, RAM2LIN) are singletons and its three λ-retaining
schemas VERT1/VERT2/FULL (`EFF.HMENU3.67`) carry fibers of size `#Λ₂ = 2`, `#Λ₂ = 2`, `#Λ₃ = 3`
(`EFF.HMENU3.68`); the twelve B-schemas each split into their `m = 0` / `m ≥ 1` regimes
(`EFF.HMENU3.69`, `.37`), giving `bTier i ↦ 21 + i / 2`. LANDED — retirement form (0e-diff
against `Uniformity.ChapG.G62`): this def carried a real body here even before landing (D2 cure,
no proof obligation), so its retirement is the ordinary definitional-stub case, not the
structure/inductive case above. -/
example : CubicFamilyIndex → Fin 33 := CubicFamilyIndex.schema

/-- **G.63a** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G63`). -/
example : Nat.card CubicFamilyIndex = 53 := card_cubicFamilyIndex

/-- **G.63b** LANDED (wave-3, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G63`). -/
example : Function.Surjective CubicFamilyIndex.schema := schema_surjective

/-- **G.64** HEX3's `R(M)`: the `n = 2` conservative-drain count per centre at window `M`
(`EFF.HEX3.26`, LEMMA H-4). Pure arithmetic — this definition mentions no ring. LANDED —
retirement form (0e-diff against `Uniformity.ChapG.G64`). -/
example (q M : ℕ) : ℕ := hex3R (q := q) (M := M)

/-- **G.65** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G65`). Proved via a parity-free "two-step" recursion
`hex3R q (M+2) = q²·hex3R q M + (q−1)·q^M`, not the parity case-split the blueprint suggested. -/
example (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M) :
    hex3R q M
      = q ^ (M - 1) + (q - 1) * ∑ j ∈ Finset.Icc 1 ((M - 1) / 2), q ^ j * hex3R q (M - 2 * j) :=
  hex3R_rec (q := q) (M := M) (hq := hq) (hM := hM)

/-- **G.66** HEX3's `u(q, N)` — the per-centre conservative-undecided count of the cubic TRP
stratum (`EFF.HEX3.08`, THEOREM HEX3.A), in telescoped form. Pure arithmetic. LANDED (wave-5,
2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G66`), in both available
strengths per the §A-5 precedent: the type-level `example` plus an `rfl` check that the landed
BODY is the signed one. -/
example (q N : ℕ) : ℕ := hex3U (q := q) (N := N)

example (q N : ℕ) :
    hex3U q N
      = q ^ (2 * N - 2)
        + (q - 1) * ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
            q ^ (4 * k - 1) * ((q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k)) := rfl

/-- **G.67** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G67`), the hardest node of the chain: the blueprint's double-sum telescoping
is landed via a coefficient-collapse lemma proved by a self-reflection bijection `k ↦ l−k`,
reducing to the standard finite geometric series. -/
example (q N : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) :
    hex3U q N + ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
        (q - 1) * q ^ (3 * k) * q ^ (2 * (N - 3 * k) - 2)
      = q ^ (2 * N - 2) + ∑ k ∈ Finset.Icc 1 ((N - 1) / 3),
          (q - 1) * q ^ (3 * k) * (hex3U q (N - 3 * k)
            + (q ^ (N - 3 * k) - 1) * hex3R q (N - 3 * k)) :=
  hex3U_rec (q := q) (N := N) (hq := hq) (hN := hN)

/-- **G.68** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G68`). -/
example (q M : ℕ) (hq : 2 ≤ q) (hM : 1 ≤ M) :
    2 * hex3R q M ≤ (M + 1) * q ^ (M - 1) :=
  two_mul_hex3R_le (q := q) (M := M) (hq := hq) (hM := hM)

/-- **G.69** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G69`), THEOREM HEX3.B's vanishing bound — proof-only (no battery touches it),
done entirely in `ℕ` (not `ℚ`/`ℝ` as the blueprint suggested) via a telescoping identity by
induction on the sum's upper bound. -/
example (q N : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) :
    hex3U q N ≤ N * q ^ (2 * N - 2) :=
  hex3U_le (q := q) (N := N) (hq := hq) (hN := hN)

/-- **G.70** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G70`). -/
example (q : ℕ) (hq : 2 ≤ q) :
    Filter.Tendsto (fun N : ℕ => (q * hex3U q N : ℝ) / (q : ℝ) ^ (3 * N))
      Filter.atTop (nhds 0) :=
  hex3U_div_tendsto_zero (q := q) (hq := hq)

end Menu

/-- **G.71** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G71`), the frontier interface node: names the `n = 3` hypothesis this chapter
does not discharge (H-1) and wires its consequence. -/
example [IsAdicComplete (maximalIdeal O) O]
    (h : ∀ N : ℕ, (undecidedCount O 3 N : ℝ)
      ≤ (residueCard O : ℝ) * (Menu.hex3U (residueCard O) N : ℝ))
    (σ : FactorizationType) : UndecidedVanishes O 3 σ :=
  drainage_three_of_hex3_bound (h := h) (σ := σ)

/-- **G.72a** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G72`). -/
example [IsAdicComplete (maximalIdeal O) O]
    (hd : ∀ σ : FactorizationType, UndecidedVanishes O 3 σ) :
    genuineDensity O 3 c3split + genuineDensity O 3 c3linInert + genuineDensity O 3 c3inert
      + genuineDensity O 3 c3linRam + genuineDensity O 3 c3ram = 1 :=
  totalMass_three_of_drainage (hd := hd)

/-- **G.72b** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G72`); unconditional, no drainage hypothesis. -/
example :
    1 ≤ genuineDensity O 3 c3split + genuineDensity O 3 c3linInert + genuineDensity O 3 c3inert
      + genuineDensity O 3 c3linRam + genuineDensity O 3 c3ram :=
  one_le_sum_three

/-! ## §10 — `n = 3`: the σ-undecided lower bound (G.73–G.77) -/

namespace Menu

/-- **G.73a** The `q^N`-element species of `EFF.HEX3.07` / LEMMA W12-S3.2: separation data
hidden, `b₂` free and visible. LANDED — retirement form (0e-diff against
`Uniformity.ChapG.G73`). -/
example (N : ℕ) : Set (Coeff O 3 N) := species3 (N := N)

/-- **G.73b** LANDED — retirement form (0e-diff against `Uniformity.ChapG.G73`). Another D4 node
(see G.14c): `[Finite (ResidueField O)]` is absent from this header but auto-synthesized on
application. -/
example (N : ℕ) : Nat.card (species3 (O := O) N) = residueCard O ^ N :=
  card_species3 (N := N)

end Menu

/-- **G.74** LANDED (wave-5, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G74`). -/
example {N : ℕ} {c : Coeff O 3 N} (hc : c ∈ Menu.species3 N) :
    ∃ a : Fin 3 → O, proj O 3 N a = c ∧ typeOf (monicPoly a) = c3split :=
  exists_split3_lift (hc := hc)

/-- **G.75** LANDED (wave-7, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G75`). Genuinely new construction (no `leancheck` target): both cases rescale
by `π^m` and choose the rescaled constant term's exponent to be `2 * N + 1`, decoupling the two
cases' parity bookkeeping from the blueprint's own sketch. -/
example [IsAdicComplete (maximalIdeal O) O] (hπ : Irreducible π)
    {N : ℕ} {c : Coeff O 3 N} (hc : c ∈ Menu.species3 N) :
    ∃ a : Fin 3 → O, proj O 3 N a = c ∧
      (typeOf (monicPoly a) = c3ram ∨ typeOf (monicPoly a) = c3linRam) :=
  exists_ram3_lift (hπ := hπ) (hc := hc)

/-- **G.76** The `n = 3` σ-undecided count is at least `q^N`: the `q^N` classes with both
separation coordinates hidden admit both a split lift and a ramified lift. LANDED (wave-7,
2026-08-15) — retirement form (0e-diff against `Uniformity.ChapG.G76`). -/
example [IsAdicComplete (maximalIdeal O) O] (N : ℕ) :
    residueCard O ^ N ≤ undecidedCount O 3 N :=
  card_le_undecidedCount_three (N := N)

/-- **G.77a** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G77`). -/
example :
    (1 : ℝ) / 512 ≤ decidedDensity ℤ_[2] 3 c3split
      ∧ (1 : ℝ) / 4 ≤ decidedDensity ℤ_[2] 3 c3linInert
      ∧ (1 : ℝ) / 4 ≤ decidedDensity ℤ_[2] 3 c3inert
      ∧ (1 : ℝ) / 16 ≤ decidedDensity ℤ_[2] 3 c3linRam
      ∧ (1 : ℝ) / 16 ≤ decidedDensity ℤ_[2] 3 c3ram :=
  gate_three_padic_two

/-- **G.77b** LANDED (wave-8, 2026-08-15) — retirement form (0e-diff against
`Uniformity.ChapG.G77`). This is the CONTAINMENT check against HMENU3's transcribed targets: it is
`norm_num` on rationals and proves nothing about densities. Its value is that a future change to
either side breaks the build. Re-run in exact rationals at blueprint AMENDMENT §A-9.2: all ten
inequalities hold at `q = 2` and `q = 3`, the tightest with a `0.41%` margin. -/
example :
    (1 : ℝ) / 512 ≤ 4 / 93 ∧ (1 : ℝ) / 4 ≤ 28 / 93 ∧ (1 : ℝ) / 4 ≤ 8 / 31
      ∧ (1 : ℝ) / 16 ≤ 22 / 93 ∧ (1 : ℝ) / 16 ≤ 5 / 31 :=
  gate_three_hmenu3_containment_two

end Uniformity.Density
