# M16-zf-serre — problem brief: the ℤ_p-bridge (e,f) laws ("zf laws")

*Self-contained problem statement. Assumes: p-adic fields, Newton polygons,
Okutsu–Montes/MacLane theory, ramification theory of local fields. Assumes NO
knowledge of this project's internal names — every internal object is unfolded.*

## 1. Context (two sentences)

The surrounding project formalizes, in Lean 4 + Mathlib (pinned toolchain
4.31.0-era), a theorem about densities of factorization types of monic degree-n
polynomials over ℤ_p. One interface of that formalization is a "bridge"
structure asserting that a certain abstract classifier's verdicts agree with
genuine ℤ_p[X]-factorization read through ramification data; the open
obligation M16 is the package of laws about the ramification/residue-degree
reading — stated precisely below.

## 2. The mathematical statement (normative content, unfolded)

Fix a prime p and n ≥ 1. All polynomials are in ℤ_p[X]; "coercion to ℚ_p[X]"
means applying the inclusion ℤ_p ↪ ℚ_p coefficientwise.

For a monic h ∈ ℤ_p[X] whose image in ℚ_p[X] is irreducible, write

- K_h := ℚ_p[X]/(h)  (a finite field extension of ℚ_p of degree deg h),
- O_h := the integral closure of ℤ_p in K_h,
- e(h) := the ramification index of the maximal ideal of O_h over p·ℤ_p,
- f(h) := the residue degree [O_h/m_{O_h} : F_p].

**Obligation M16.** Prove (or identify as exact literature statements, with a
faithfulness analysis of any excess) the following, for every monic g ∈ ℤ_p[X]
with deg g = n:

- **(M16-existence)** For each monic ℚ_p-irreducible factor h, the ring O_h is
  a discrete valuation ring (equivalently: the objects e(h), f(h) above are
  well-formed as stated). This existence/structure content is what the pinned
  Mathlib cannot supply (see §5.4).
- **(M16-pos)** ("zf_pos") e(h) ≥ 1 and f(h) ≥ 1 for every monic
  ℚ_p-irreducible factor h of g.
- **(M16-pointwise)** e(h) · f(h) = deg h for every such factor.
- **(M16-factor)** ("zf_factor") There exists a multiset {h_1, …, h_r} of monic
  polynomials in ℤ_p[X] such that
  1. the coercion of g to ℚ_p[X] equals the product of the coercions of the h_i;
  2. each h_i is monic and its coercion is irreducible in ℚ_p[X];
  3. the reading function (defined in §3) sends g to the multiset
     {(e(h_i), f(h_i))}_i;
  4. the multiset {e(h_i)·f(h_i)}_i equals the multiset {deg h_i}_i
     (the "aggregate degree conjunct"; the project record notes this is weaker
     than (M16-pointwise) — a permutation of equal products satisfies it — and
     the pointwise form is the one queued for a statement upgrade).

The intended witnesses in conjunct (M16-factor) are the monic irreducible
factors of g in the UFD ℤ_p[X], rescaled monic; their existence, product law,
monicity, ℤ_p[X]-irreducibility, positive degree, and ℚ_p-irreducibility
(Gauss transfer) are ALREADY machine-proved (§5.1) — the open content of M16
is (M16-existence), (M16-pos), (M16-pointwise), and the assembly.

## 3. The Lean form (the normative statements)

### 3.1 The bridge structure carrying the laws

`lean/LeanUrat/MovesU/DefsLedger.lean:721` (statement-frozen file):

```lean
structure ZpBridge (X : ClassifierSpec n p) where
  zfType : Polynomial ℤ_[p] → Multiset (ℕ × ℕ)
  zf_pos : ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    ∀ ef ∈ zfType g, 1 ≤ ef.1 ∧ 1 ≤ ef.2
  zf_factor : ∀ g : Polynomial ℤ_[p], g.Monic → g.natDegree = n →
    ∃ factors : Multiset (Polynomial ℤ_[p]),
      g.map (PadicInt.Coe.ringHom)
          = (factors.map (Polynomial.map PadicInt.Coe.ringHom)).prod ∧
      (∀ h ∈ factors, h.Monic ∧ Irreducible (h.map PadicInt.Coe.ringHom)) ∧
      zfType g = factors.map (fun h => (MovesT.ramIdx h, MovesT.resDeg h)) ∧
      (zfType g).map (fun ef => ef.1 * ef.2) = factors.map Polynomial.natDegree
  lift_exists : …   -- not part of M16 (proved: §5.1)
  lift_true : …     -- not part of M16 (separate obligation)
```

Here `PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]` is the subring inclusion (proved
equal, by `rfl`, to `algebraMap ℤ_[p] ℚ_[p]`). `ClassifierSpec n p` is an
abstract interface (two maps `Fin n → ZMod (p^N)` → `Option (SplittingType n)`
+ a stability law); its content is irrelevant to M16 — the zf laws do not
mention `X`. `SplittingType n` is the subtype of `Multiset (ℕ × ℕ)` whose
entries are ≥ (1,1) componentwise and satisfy Σ eᵢ·fᵢ = n.

An instance of `ZpBridge` must supply `zfType` together with the laws. The
intended instance takes `zfType g := (monicFactors g).map (fun h =>
(MovesT.ramIdx h, MovesT.resDeg h))` where `monicFactors g` is the (already
constructed, §5.1) multiset of monic-rescaled irreducible ℤ_p[X]-factors of g —
so conjunct 3 of `zf_factor` is definitional for that instance, and the load
is carried by (M16-existence)/(M16-pos)/(M16-pointwise).

### 3.2 The reading functions — current (refuted) and adjudicated form

Current definitions, `lean/LeanUrat/MovesT/Defs.lean:1107/1116` (total
functions with junk value 0 off the guard):

```lean
noncomputable def ramIdx (g : Polynomial ℤ_[p]) : ℕ :=
  if h : IsLocalRing (AdjoinRoot g) then
    Ideal.ramificationIdx
      (IsLocalRing.maximalIdeal ℤ_[p]) (IsLocalRing.maximalIdeal (AdjoinRoot g))
  else 0
-- resDeg: same dispatch, Ideal.inertiaDeg
```

`AdjoinRoot g = ℤ_p[X]/(g)` is the ORDER generated by one root — in general a
NON-MAXIMAL order of K_g. A compiled countermodel
(`lean/LeanUrat/MovesU/BridgeE0_zpCountermodel.lean`, p = 3, h = X² + 3²·1,
i.e. X² − p²c with c a non-square unit) shows: `AdjoinRoot h` IS local, the
order-level reading gives `ramIdx h = 1`, `resDeg h = 1`, yet deg h = 2, and
`e0_no_zpBridge : IsEmpty (ZpBridge 2 3 X)` for every `X` — the structure is
UNINSTANTIABLE with the order-level reading (the true field invariants of
ℚ_3(√{−1}·3⁰…)/ℚ_3, an unramified quadratic, are (e,f) = (1,2)).

The project's adjudicated repair (ratified 2026-07-30/31, execution
concurrent with this brief) re-points `ramIdx`/`resDeg` at the INTEGRAL
CLOSURE, through the existing bundle vocabulary of
`lean/LeanUrat/OM/QpType.lean`:

```lean
structure LocalFactorData (p : ℕ) [Fact p.Prime] (g : ℤ_[p][X]) where
  L : Type                                  -- the local factor field
  [fieldL : Field L] [algQL : Algebra ℚ_[p] L] [algZL : Algebra ℤ_[p] L]
  [towerZQL : IsScalarTower ℤ_[p] ℚ_[p] L]
  finrank_eq : Module.finrank ℚ_[p] L = g.natDegree
  hasRoot : ∃ x : L, Polynomial.aeval x (g.map (algebraMap ℤ_[p] ℚ_[p])) = 0 ∧
    Algebra.adjoin ℚ_[p] {x} = ⊤
  O : Type                                  -- "the integers of L"
  [crO : CommRing O] [domO : IsDomain O] [dvrO : IsDiscreteValuationRing O]
  [algZO : Algebra ℤ_[p] O] [algOL : Algebra O L]
  [towerZOL : IsScalarTower ℤ_[p] O L]
  [intClosure : IsIntegralClosure O ℤ_[p] L]
  [liesOver : (IsLocalRing.maximalIdeal O).LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

noncomputable def eOf … (D : LocalFactorData p g) : ℕ :=
  Ideal.ramificationIdx (IsLocalRing.maximalIdeal ℤ_[p]) (IsLocalRing.maximalIdeal D.O)
noncomputable def fOf … (D : LocalFactorData p g) : ℕ :=
  (IsLocalRing.maximalIdeal ℤ_[p]).inertiaDeg (IsLocalRing.maximalIdeal D.O)
```

(`Ideal.LiesOver P p` means `p = comap (algebraMap) P`.) The repaired
`ramIdx`/`resDeg` read `eOf`/`fOf` off a bundle for the factor (classical
choice from bundle-existence on the guard locus; junk 0 off it). The M16 laws
are to be understood AT THE REPAIRED READING, i.e. exactly as the standard
invariants e(h), f(h) of §2.

### 3.3 The Mathlib primitives, unfolded (pinned Mathlib)

- `Ideal.ramificationIdx p P := sSup {k | map (algebraMap R S) p ≤ P^k}`
  (ℕ-valued sSup: 0 if the set is unbounded, e.g. when P = ⊥ or p = ⊥).
- `Ideal.inertiaDeg p P := if comap (algebraMap) P = p then
  finrank (R⧸p) (S⧸P) else 0` (note: `finrank` is 0 for an
  infinite-dimensional extension — finiteness of the residue extension is part
  of what makes f ≥ 1 non-trivial as a Lean statement).

## 4. What a solution must deliver

Any of:

1. **Literature identification** (the obligation is flagged
   literature-axiom-eligible under the project's axiom policy): for EACH of
   (M16-existence), (M16-pos), (M16-pointwise), (M16-factor) either a full
   proof from pinned-Mathlib primitives, or an exact literature statement
   (book/paper, theorem number, hypotheses) that implies it, PLUS a
   faithfulness analysis: does the Lean form ask for anything MORE than the
   cited statement gives (quantifier scope, junk-value conventions, totality,
   choice of reading, the aggregate-vs-pointwise distinction)? The minimal
   axiom candidate is the inhabitation of `LocalFactorData p h` for monic h
   with ℚ_p-irreducible image; the analysis must audit every field of that
   bundle against the citation.
2. **Informal-rigorous proof** of the four items from standard local-field
   theory, structured so each step is either a pinned-Mathlib lemma or an
   explicitly displayed open lemma.
3. **Counterexample** to any of the items as stated at the repaired reading
   (this would be a stop-the-line event: it would mean the repair is
   mis-targeted).

## 5. What is already proved in the corpus (usable, machine-checked)

### 5.1 Factorization side — axiom-free, `lean/LeanUrat/MovesU/BridgeZp.lean`

- `monicFactors g` : multiset of monic-rescaled `UniqueFactorizationMonoid.factors`
  of g; `monicFactors_prod : (monicFactors g).prod = g` (g monic);
  `monicFactors_monic`; `monicFactors_irreducible` (in ℤ_p[X]);
  `monicFactors_natDegree_pos`.
- `monic_irreducible_map_coe` (Gauss transfer): monic + irreducible in ℤ_p[X]
  + positive degree ⟹ irreducible over ℚ_p (via
  `Monic.irreducible_iff_irreducible_map_fraction_map` at the verified
  instance `IsFractionRing ℤ_[p] ℚ_[p]`). The iff also gives the converse.
- `ip1_holds` / `isLocalRing_adjoinRoot`: for h monic with ℚ_p-irreducible
  image, `IsLocalRing (AdjoinRoot h)` — proved via: h prime in the UFD;
  `AdjoinRoot h` free finite over ℤ_p (power basis); adic completeness
  transfers along the coordinates (two general helpers
  `isAdicComplete_of_linearEquiv`, `isAdicComplete_pi_of_fintype` are proved
  there); hence Henselian; residue ring finite hence Artinian; two maximal
  ideals would give a nontrivial idempotent
  (`exists_nontrivial_idempotent_of_two_maximal`, proved), Hensel-liftable
  along X² − X into the domain — contradiction.
- `bridge_lift_exists` (the `lift_exists` field), and the uniqueness feeding
  `lift_true` (`zpReads_bridgeZfType_unique`).

### 5.2 The refutation at the order-level reading

`BridgeE0_zpCountermodel.lean` (see §3.2): `e0_ramIdx = 1`, `e0_resDeg = 1`,
`e0_zf_factor_false`, `e0_no_zpBridge`. So M16 is FALSE at the un-repaired
defs; the obligation lives at the integral-closure reading only.

### 5.3 The bundle vocabulary and its non-vacuity

`OM/QpType.lean` (axiom-free): `LocalFactorData`, `eOf`, `fOf`,
`QpFactorization`, `qpType`; witness `trivialFactorData` inhabits the bundle
at g = X (L = ℚ_p, O = ℤ_p) with `eOf = fOf = 1` proved. A separately declared
project axiom (`OM/OmLeafFaithful.lean`, cited to Guàrdia–Montes–Nart's
higher-order-Newton-polygon theorems plus the standard structure theory of
local fields) already CARRIES bundle-existence, but only scoped to the fibers
of a specific n = 2 classifier menu — it does not cover M16's general monic h.

### 5.4 The documented gap at the pinned Mathlib

The pinned Mathlib has: DVR/PID/UFD instances for ℤ_p, `IsFractionRing ℤ_[p]
ℚ_[p]`, Dedekind-domain theory, `Ideal.ramificationIdx`/`inertiaDeg` with the
fundamental-identity file (`Mathlib/NumberTheory/RamificationInertia/Basic.lean`),
Henselian rings (`IsAdicComplete.henselianRing`). It has NO
`IsNonarchimedeanLocalField`, NO finite-extension `Valued`/extension-of-
valuation theory for ℚ_p, and NO instance or theorem giving
`IsDiscreteValuationRing (integralClosure ℤ_[p] L)` for a finite extension
L/ℚ_p (grep-verified at the pin). This is the wall the project record calls
"integralClosure-DVR-ness at wild deg ≥ 2".

## 6. Conventions and traps for the solver

- Everything is at a FIXED prime p; n is arbitrary. "Wild" (p ∣ e) cases are
  in scope — nothing may assume tameness or p ∤ n.
- ℚ_p has characteristic 0: every finite extension is separable. (Residue
  fields are perfect too, but the needed statements should be checked at the
  stated generality, not assumed.)
- Degenerate quantifier corners: deg-0 factors cannot occur (monic degree-0 =
  1 is a unit, and units are excluded by irreducibility — proved, §5.1);
  n = 0 makes `zf_pos`/`zf_factor` vacuous over the empty factor multiset
  (g = 1); the laws quantify over ALL monic g of degree n, reducible included.
- The (e,f) reading in `zf_factor` conjunct 3 must be THE SAME total function
  `MovesT.ramIdx`/`resDeg` used by `zfType` — a proof may not substitute a
  different (even provably-equal-on-the-locus) reading without a statement
  change.
- `Ideal.inertiaDeg`'s `finrank` is 0 unless the residue extension is
  finite-dimensional; `Ideal.ramificationIdx`'s sSup is 0 if the exponent set
  is unbounded. Both junk conventions must be discharged, not assumed away.
- Multiset equality in conjunct 4 is aggregate, not pointwise (§2); do not
  silently prove the pointwise law and cite it as conjunct 4 or vice versa —
  both are wanted, separately labeled.
