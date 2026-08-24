# U11 — the MacLane chain-realization carrier

Date: 2026-08-24  
Status: **DESIGN DECIDED; signatures elaborate; full source instance remains OPEN**

## 1. Decision in one paragraph

Use a **new layered `ChainRealization` over `DeepTower`**. Do not add fields to C.83's
`DeepTower`. The layer owns the polynomial key chain, an integer/Laurent normalizer, legal
node points and their stage value/digit reads, the inherited threshold and window, the two
deliberately separate residue reads, and the source-side FGMN objects and laws. An
input-specific `RealizedInput` reuses I.10 freeze-v2's `ArisingCore`; the tower-wide layer
reuses its `TerminalReceiver`. Nothing in the carrier has an I.10 socket, `HVarthetaRes`,
`VarthetaRes`, or `FGMNCalculus` as a field.

The direct map to A-C.11's class is then ordinary packaging: `ExactGrade` and `AboveGrade`
are definitions from the realized next valuation, scalar `Rgr` is coefficient zero of the
polynomial-valued source residual, and the remaining laws are transports of named FGMN
clauses. The same layer makes C.130b--k stateable without pretending that `(e,f,u,ψ)` alone
determines keys, points, digits, or a threshold.

The elaboration authority for all signatures and the packaging theorem is
`leanfinal/scratch/U11_carrier_check.lean`. It contains no `sorry` or axiom and checks with

```text
cd leanfinal
lake env lean scratch/U11_carrier_check.lean
```

at exit 0.

## 2. Why this is layered, not an extension of `DeepTower`

The count was made before choosing. At HEAD,

```text
rg -l 'DeepTower' leanfinal/Uniformity/ChapC --glob '*.lean'
```

returns **nine** chapter-C files: C73, C83, C84, C87, C97, C123, C130b, C130d, and C130f.
There are two actual structure-producing sites: C.83's `DeepTower.trunc` and C.97's
`s2Witness`. I.10FreezeV2 additionally mentions it in `TerminalReceiver` and `ArisingCore`.
Adding any missing realization data to `DeepTower` would therefore force at least both
constructors to change, would make every truncation transport polynomial keys, node points,
thresholds, and FGMN data, and would falsely claim that every abstract C.83 telescope is a
legal MacLane/node-point realization.

That last issue is decisive. C.83 intentionally carries only `(e,f,u,ψ)`, field telescopes,
and arithmetic. C130A found that it does not determine `Φ_i`, stage valuations/digits, or an
EFF.T2.11 threshold. U7/U9 found that it does not determine an FGMN MacLane calculus. These
are extra mathematical structures on a tower, not forgotten projections of the existing
structure.

The conservative design also gives the right truncation behavior. `DeepTower.trunc` remains
cheap and total. A future `ChainRealization.trunc` must be a theorem requiring source
truncation dictionaries; it must not be obtained automatically by weakening C.83 range
hypotheses.

## 3. Reuse boundary

The production declaration must reuse, not clone:

- `Tower.StageLive`, `GaugeLive`, and `DeepLive`;
- `Tower.TerminalReceiver` for the common terminal receiver and step squares;
- `Tower.ArisingCore` for the DVR/frame/tower/input/degree/key-free core;
- `Ladder.DeepTwistConjunctLive` as I.10b's live-range target.

Those names currently live in `Uniformity.ChapI.I10FreezeV2`. A chapter-C implementation
cannot import chapter I without reversing the dependency. The first transcription node must
therefore **move the unchanged declarations** `StageLive`, `GaugeLive`, `DeepLive`,
`TerminalReceiver`, and `ArisingCore` to C.130a (or a neutral pre-I module), and change
I10FreezeV2 to import/re-export them. There must never be a second structure with the same
meaning.

## 4. Decided Lean signatures

Names are provisional, but the types below are the elaborated U11 types. Universes are fixed
as in freeze v2: `O : Type`, `W : DeepTower.{0,uKt}`, terminal `Kt : Type uKt`, and ambient
`L : Type uL`.

### 4.1 Polynomial chain and Laurent normalizer

```lean
structure KeyChain (W : DeepTower.{0, uKt} F H₀ hpin r) where
  keyAt : ℕ → Polynomial O
  keyAt_one : keyAt 1 = F.key
  keyAt_monic : ∀ i, StageLive r i → (keyAt i).Monic
  keyAt_degree : ∀ i, StageLive r i →
    (keyAt i).natDegree = W.Dcum i

structure LaurentNormalizer (W : DeepTower.{0, uKt} F H₀ hpin r) where
  norm : (i : ℕ) → ℤ → LevelExponentLattice i
  norm_zero : ∀ i, norm i 0 = 1
  exact_height : ∀ i, StageLive r i → ∀ k : ℤ,
    levelExponentHeight W i (norm i k) = Multiplicative.ofAdd k
```

`KeyChain` is OPEN-DICT-1 and C.130b. At depth two its second key is exactly
EFF.HETOW.13's wrap-corrected `composedKey`; at general depth its constructor is the
EFF.GENTOW5 S2.1 composed-key recipe (the effective s1of2.18 row). EFF.GENTOW5.21 is only
the worked `n̂₃(85)`/`n̂₂(21)` regression and must not be cited as the general key theorem.
`LaurentNormalizer` is the missing source carrier identified by C130B. It intentionally has
no false field saying that it equals C.83's
natural/truncated `towerNorm` for every nonnegative height. Compatibility with `towerNorm`
may later be proved only on a named nontruncation domain.

### 4.2 Legal point, stage carrier, threshold, and the two reads

The complete elaborated signature is in the scratch file; its public shape is:

```lean
structure NodePointSource
    (W : DeepTower.{0, uKt} F H₀ hpin r)
    {Kt : Type uKt} [Field Kt] {L : Type uL} [Field L] [Algebra Kt L]
    (receiver : TerminalReceiver F H₀ hpin r W Kt) (K : KeyChain W) where
  Point : Type
  Pt : ℕ → Point → Prop
  point_exists : ∀ i, StageLive r i → Nonempty {x : Point // Pt i x}
  coeffHom : O →+* L
  coord : Point → L
  valueOn : ℕ → L → WithTop ℤ
  value_zero : ∀ i, StageLive r i → valueOn i 0 = ⊤
  value_mul : ∀ i, StageLive r i → ∀ a b,
    valueOn i (a * b) = valueOn i a + valueOn i b
  value_add_ge : ∀ i, StageLive r i → ∀ a b,
    min (valueOn i a) (valueOn i b) ≤ valueOn i (a + b)
  value_add_eq : ∀ i, StageLive r i → ∀ a b,
    valueOn i a ≠ valueOn i b →
      valueOn i (a + b) = min (valueOn i a) (valueOn i b)

  hgt : ℕ → Polynomial O → WithTop ℤ
  dig : (i : ℕ) → Polynomial O → W.fld i
  pointHgt : ℕ → Point → Polynomial O → WithTop ℤ
  pointDig : (i : ℕ) → Point → Polynomial O → W.fld i
  pointHgt_eval : ∀ i x A,
    pointHgt i x A = valueOn i (Polynomial.eval₂ coeffHom (coord x) A)
  slot_value : ∀ i (_ : StageLive r i) x, Pt i x → ∀ A,
    A ≠ 0 → A.natDegree < W.Dcum i → pointHgt i x A = hgt i A
  slot_digit : ∀ i (_ : StageLive r i) x, Pt i x → ∀ A,
    A ≠ 0 → A.natDegree < W.Dcum i → pointDig i x A = dig i A

  hgt_zero : ∀ i, StageLive r i → hgt i 0 = ⊤
  dig_zero : ∀ i, StageLive r i → dig i 0 = 0
  hgt_ne_top : ∀ i, StageLive r i → ∀ A,
    A ≠ 0 → A.natDegree < W.Dcum i → hgt i A ≠ ⊤
  dig_ne_zero : ∀ i, StageLive r i → ∀ A,
    A ≠ 0 → A.natDegree < W.Dcum i → dig i A ≠ 0
  hgt_add_ge : ∀ i, StageLive r i → ∀ A B,
    min (hgt i A) (hgt i B) ≤ hgt i (A + B)
  hgt_add_eq : ∀ i, StageLive r i → ∀ A B,
    hgt i A ≠ hgt i B → hgt i (A + B) = min (hgt i A) (hgt i B)
  dig_add : ∀ i, StageLive r i → ∀ A B k,
    hgt i A = (k : WithTop ℤ) → hgt i B = (k : WithTop ℤ) →
    dig i A + dig i B ≠ 0 →
      hgt i (A + B) = (k : WithTop ℤ) ∧ dig i (A + B) = dig i A + dig i B
  Full : ℕ → ℤ → Prop
  lift : ∀ i, StageLive r i → ∀ k, Full i k → ∀ c : W.fld i, c ≠ 0 →
    ∃ A : Polynomial O, A ≠ 0 ∧ A.natDegree < W.Dcum i ∧
      hgt i A = (k : WithTop ℤ) ∧ dig i A = c

  thresholdZ : ℕ → ℤ
  thresholdNat : ℕ → ℕ
  threshold_nonneg : ∀ i, StageLive r i →
    (thresholdNat i : ℤ) = thresholdZ i
  window : ∀ i, StageLive r i → ∀ x, Pt i x →
    (thresholdZ i : WithTop ℤ) < pointHgt i x (K.keyAt i) ∧
      pointHgt i x (K.keyAt i) ≠ ⊤

  ambientLetter : ℕ → Lˣ
  key_value : ∀ i, GaugeLive r i → ∀ x, Pt i x →
    pointHgt i x (K.keyAt i) = (W.u (i + 1) : WithTop ℤ)
  psi_root : ∀ i, GaugeLive r i →
    Polynomial.eval₂ ((algebraMap Kt L).comp (receiver.levelHom i))
      (ambientLetter i : L) (W.ψ i) = 0
  canonicalRead : (i : ℕ) →
    MonoidHom.ker (levelExponentHeight W i) →* Lˣ
  arenaRead : (i : ℕ) →
    MonoidHom.ker (levelExponentHeight W i) →* Ktˣ
  towerRead : (i : ℕ) → LevelExponentLattice i → Kt
  peelUnit : ℕ → Ktˣ
```

The stage laws are source obligations, not a copy of `SlotCarrier`: they are a tower-indexed
EFF.T2 source family. `pointHgt_eval` makes the point read an actual polynomial evaluation,
and `slot_value`/`slot_digit` tie the stage tables to legal points. C.130c derives
`Ladder.SlotCarrier` from these fields. `canonicalRead` and `arenaRead` are deliberately
different fields and there is no equation or Kt-preimage field between them.

The integer threshold and its natural-valued repository avatar are both explicit. The equality
`threshold_nonneg` is the dictionary obligation forced by the current natural-valued
`BlockData.T`. If an effective source instance has a genuinely negative inherited threshold,
that field will be uninhabitable and E.11 must be re-signed to `ℤ`; no truncation to zero is
allowed.

### 4.3 Source-side FGMN data and law package

```lean
structure FGMNSourceData (W : DeepTower.{0, uKt} F H₀ hpin r)
    (K : KeyChain W) (e' f' u' : ℕ) where
  nextValue : Polynomial O → WithTop ℤ
  gradedResidual : ℕ → Polynomial O → Polynomial (W.fld r)
  normalizedResidual : Polynomial O → Polynomial (W.fld r)
  keyPolynomial : Polynomial O → Prop
  initialEquiv : Polynomial O → Polynomial O → Prop
  letter : ℕ → W.fld r

def FGMNSourceData.ExactGrade (S : FGMNSourceData W K e' f' u')
    (β : ℕ) (g : Polynomial O) : Prop :=
  S.nextValue g = (β : WithTop ℤ)

def FGMNSourceData.AboveGrade (S : FGMNSourceData W K e' f' u')
    (β : ℕ) (g : Polynomial O) : Prop :=
  (β : WithTop ℤ) < S.nextValue g
```

`FGMNSourceLaws W K e' f' u' S` carries exactly these named source obligations:

| field | source obligation |
|---|---|
| `graded_zero_of_above` | FGMN Lemma 3.14, polynomial-valued |
| `graded_add` | Corollary 4.12(1), polynomial-valued |
| `graded_mul` | Corollary 4.12(2), polynomial-valued, with exact-grade product |
| `graded_scalar_nonzero` | Theorem 4.1 + Corollary 4.9(1), in `deg g < deg keyAt r` scope |
| `normalized_mul` | Corollary 4.12(3) |
| `normalized_recipe` | Definition 1.6, Definition 3.13, equation (11), Corollary 4.12(1)/(2) |
| `normalized_exists` | Theorem 5.7 construction, with monic irreducible residual input |
| `key_criterion` | Lemma 5.2(2), Corollary 4.9, Theorem 5.7 degree display |
| `key_irreducible` | Lemma 1.8 + Corollary 1.10 + the landed Gauss transport |
| `carried_key_is_key` | Proposition 1.7(4) |
| `carried_key_residual` | equation (11), fenced by `0 < r` |
| `initial_iff_residual` | Proposition 5.6(2) iff (3) |
| `letter_ne_zero` | published section 3.3 |

These are not copied scalar `FGMNCalculus` laws: `gradedResidual` is source-polynomial-valued,
and scalar `Rgr` is derived as its coefficient zero. They nevertheless remain genuine source
hypotheses until the cited clauses and OPEN-DICT transports are transcribed. The carrier does
not turn them into Lean-core facts.

### 4.4 The assembled layer and input occurrence

```lean
structure ChainRealization
    (W : DeepTower.{0, uKt} F H₀ hpin r)
    (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L] [Algebra Kt L]
    (e' f' u' : ℕ) where
  receiver : TerminalReceiver F H₀ hpin r W Kt
  keys : KeyChain W
  normalizer : LaurentNormalizer W
  node : NodePointSource (L := L) W receiver keys
  fgmn : FGMNSourceData W keys e' f' u'
  fgmnLaws : FGMNSourceLaws W keys e' f' u' fgmn
  grade_compat : ∀ x : node.Point, node.Pt r x → ∀ g,
    fgmn.nextValue g = node.pointHgt r x g
  letter_compat : ∀ i, StageLive r i →
    algebraMap Kt L (receiver.topEquiv (fgmn.letter i)) =
      (node.ambientLetter i : L)

structure RealizedInput
    {n e' f' u' : ℕ} (core : ArisingCore Kt L n)
    (A : ChainRealization (F := core.F) (H₀ := core.H₀)
      (hpin := core.hpin) core.T Kt L e' f' u') where
  receiver_eq : A.receiver = core.receiver
  stageKey_eq : core.stageKey = A.keys.keyAt core.i
  stageDeg_eq : core.stageDeg = core.T.Dcum core.i
  point : A.node.Point
  point_mem : A.node.Pt core.i point
```

`grade_compat` is OPEN-DICT-2. `letter_compat` is OPEN-DICT-4. Sharing `keys` between the
node and FGMN parts is OPEN-DICT-1; `TerminalReceiver` and the polynomial-valued residual
codomains provide the OPEN-DICT-3 transport boundary. `RealizedInput` adds only dictionary
equalities and a selected legal point to `ArisingCore`; it does not contain `SlotCarrier`,
`BlockData`, a socket, or a consumer conclusion.

## 5. Threshold decision

EFF.T2.04 says the carrier has an **inherited** integer threshold. EFF.T2.11 asserts

```text
T < d(Φ(ρ)) < ∞.
```

Neither row gives a formula for `T`, and C130A correctly found no function of
`(DeepTower,i,F₀)` that determines it. Therefore the threshold is an extra carrier input:
`thresholdZ i`. The window is a source law field. `thresholdNat i` and
`threshold_nonneg` are only the repository dictionary needed to fill E.11's current
`BlockData.T : ℕ`.

C.130d should not introduce an opaque predicate which can be inhabited by an arbitrary
numeral. Its eventual theorem should be tied to a realized occurrence, schematically:

```lean
def CanonicalThresholdAt (X : RealizedInput core A) (T : ℕ) : Prop :=
  T = A.node.thresholdNat core.i ∧
  (A.node.thresholdZ core.i : WithTop ℤ) <
      A.node.pointHgt core.i X.point (A.keys.keyAt core.i) ∧
  A.node.pointHgt core.i X.point (A.keys.keyAt core.i) ≠ ⊤
```

The proof is projection plus the dictionary equality; the mathematical content is the
EFF.T2.11 `window` obligation in `NodePointSource`. `F₀` enters through `ArisingCore`'s
development, degree, and key-free obligations, not by pretending to determine the inherited
threshold.

## 6. Depth-two instantiability check

There are three distinct existing objects and they must not be conflated:

- C.80's `s2Tower` and C.53c's `linTower` are `TowerDatum`, not `DeepTower`;
- C.97's `s2Witness ... : DeepTower ... 3` is landed;
- `TowerDatum.deepTower hπ` exists only as an unlanded leanspec axiom at present.

The checked S2 depth-two object is

```lean
def s2DepthTwo := (s2Witness h2 hq 1 (s2Frame_pin h2 hq)).trunc 2 (by omega)
```

and the checked key chain is

```text
keyAt 1 = (s2Frame h2 hq).key
keyAt 2 = composedKey (s2Tower h2 hq).
```

`s2DepthTwoKeyChain` in the scratch file proves, without `sorry` or axiom, monicity at both
live levels and

```text
natDegree (keyAt i) = s2DepthTwo.Dcum i,  i = 1,2.
```

The level-two degree proof uses landed `composedKey_natDegree_D₂`; the right side reduces to
the same S2 numerals. This is the non-vacuity check for the structural front of the design.

The honest full-instance ledger is:

| field group | S2 supply now | remaining obligation |
|---|---|---|
| `KeyChain` | **PROVED in U11 scratch** | the general-depth EFF.GENTOW5.18 recipe theorem |
| `DeepTower` | `s2DepthTwo` from landed `s2Witness.trunc` | the general `TowerDatum.deepTower` bridge is still unlanded |
| `TerminalReceiver` | terminal equivalence may be `RingEquiv.refl`; step data are in `DeepTower` | C.130a's recursively composed `levelHom` and squares |
| stage monicity/degrees | landed at levels 1 and 2 | none for the S2 key front |
| stage `hgt`/`dig`/`Full` | C.46/C.47/C.127 provide pieces | assemble the full EFF.T2.04/.05/.09 family and legal-point equalities |
| Laurent normalizer | exponent data exist | construct an integer solution; C130B refuted the naive `towerNorm` extension |
| legal point and node read | `ψ₂`, its irreducibility, and its nonzero constant are landed | actual P-locus point, exact key value, root transport, canonical L-read |
| threshold | no formula and no landed term | supply inherited `thresholdZ`, prove nonnegative dictionary and WINDOW |
| FGMN source data/laws | key indices are fixed by U9 | source valuation/residual objects, FGMN clauses, OPEN-DICT-2--4 |

Thus no claim is made that a bare landed tower already inhabits the **full** realization: the
audits prove that it cannot. “Instantiable” here means that a concrete landed tower fills the
structural parameters with no type/universe/index obstruction and that every remaining
constructor argument is a named source or dictionary obligation. There is no `False`, empty
live guard, arbitrary residual table, or socket conclusion available as a filler. The first
full instance target remains freeze-v2's `s2Witness`/`s2Tower` pair.

`linTower` can receive the same depth-two key-chain constructor once a corresponding
`DeepTower` bridge is landed. It currently cannot do so because it has no landed
`TowerDatum.deepTower`; inventing one inside this carrier would duplicate C.130b's bridge.

## 7. Consumer map A — `FGMNCalculus`

The elaborated scratch theorem is

```lean
theorem chainRealization_calculus_nonempty
    (A : ChainRealization W Kt L e' f' u') :
    Nonempty (FGMNCalculusCheck W e' f' u') :=
  ⟨A.toCalculus⟩
```

`FGMNCalculusCheck` is an exact local repeat of enacted A-C.11. In production the codomain is
the actual `FGMNCalculus`.

The projection map is:

| A-C.11 field | construction |
|---|---|
| `keyAt` | `A.keys.keyAt` |
| `keyAt_one`, `keyAt_deg` | theorems/projections of `KeyChain` (OPEN-DICT-1) |
| `ExactGrade` | definition `fgmn.nextValue g = β` after clearing |
| `AboveGrade` | definition `β < fgmn.nextValue g` |
| `Rgr β g` | `(fgmn.gradedResidual β g).coeff 0` |
| `Rres` | `fgmn.normalizedResidual` |
| `KP` | source `fgmn.keyPolynomial` |
| `nuEquiv` | source `fgmn.initialEquiv` |
| `letterZ` | `fgmn.letter`, with `letter_compat` proving OPEN-DICT-4 |
| all thirteen law fields | coefficient-zero theorems or direct transports from `fgmnLaws` |

For example, `Rgr_mul` takes polynomial-valued `graded_mul` and applies `coeff 0`; Lean's
polynomial multiplication at coefficient zero proves the scalar product. `Rgr_add` and
`Rgr_zero_of_above` are the same projection. This is why the map is packaging, not a new cite.

What remains hypothesis/source work:

- the thirteen fields of `FGMNSourceLaws` until their named published clauses are transcribed;
- `grade_compat`, coefficient-field/scalar specialization, and `letter_compat` for
  OPEN-DICT-2--4;
- the general key recipe/index bridge for OPEN-DICT-1.

The numerical hypotheses `he'`, `hf'`, `hcop`, and `hfloor` belong to construction of the
source model/law package. They are not used by the final record-packaging function. There is
still no faithful theorem from a bare `DeepTower` to `Nonempty FGMNCalculus`.

## 8. Consumer map B — C.130 and the chapter-I sockets

Against C130A/C130B's exact blockers:

| layer | what the carrier supplies / theorem to transcribe |
|---|---|
| C.130b `stageKey`, `stageDeg` | `keys.keyAt`; `KeyChain.keyAt_monic/keyAt_degree`; depth two is checked against `composedKey s2Tower`. |
| C.130c `stageHgt`, `stageDig`, `stageCarrier` | `node.hgt`, `node.dig`; build `SlotCarrier` as a theorem from the EFF.T2.04/.05/.09 fields. `Full` is live and source-bound, not `True`. |
| C.130d `CanonicalThresholdAt` | `thresholdZ`, `thresholdNat`, `threshold_nonneg`, and `window`; no inferred formula. |
| C.130e `inputBlock` | reuse `ArisingCore`; use B.02/B.05/B.06 `dev`, `core.keyfree`, the generic `A₀ ≠ 0` lemma, and `thresholdNat`. No block is stored in the carrier. |
| C.130f exact normalizer | retain landed `LevelExponentLattice`/`GaugeLattice`; replace the refuted exactness attempt by `LaurentNormalizer.norm/exact_height`. Compatibility with `towerNorm` is range-qualified. |
| C.130g `NodePointDatum`, legality | `Point`, `Pt`, `point_exists`, `key_value`, `ambientLetter`, and `psi_root`; these are the legal P-locus clauses omitted by C.83. |
| C.130h `canonicalRes` | restrict/export `canonicalRead` to the synchronized product and prove its generator views. It remains L-valued and has no Kt-descent field. |
| C.130i arena family | combine `LaurentNormalizer.exact_height` with the separate `arenaRead` to build `GaugeArena`; export `towerRead` and `peelUnit`. No equality with `canonicalRead`. |
| C.130j arising/export | `RealizedInput core A`; derive `SlotViewEq`, `BlockViewEq`, `GaugeFamilyViewEq`, and `ArenaFamilyViewEq` only on live indices. |
| C.130k transports | use `receiver`, its step squares, and the existing ULift `gaugeLatticeEquiv`; prove the cross-universe carrier/block/arena transports as theorems. |
| C.130gate | build the full S2 `ChainRealization` and `RealizedInput`, then the two literal socket applications. The U11 key-chain proof is its first landed-compatible subterm. |

Once C.130j/k exist, the socket bodies remain freeze-v2's existential views. They quantify over
`RealizedInput`/the shared export witness; they do **not** quantify over a record containing
`LadderSupply` or `DeepTwistConjunctLive`. I.10a is fed by the derived slot/block/gauge views.
I.10b uses the same witness plus the separately derived arena views. Its implication to I.10a
is still `And.left`.

This carrier does not discharge OM-8 L3. In particular it has neither

```text
canonicalRead = algebraMap ∘ arenaRead
```

nor a Kt preimage for an ambient letter. Therefore unpacking a socket still leaves exactly the
descent/agreement goal required by `HVarthetaRes`, as freeze v2 requires.

## 9. Field-by-field honesty classification

Every field falls in one of two allowed classes.

**Source obligations:** Laurent exactness (EFF.T2.07, GENTOW5.15); legal points, key values,
roots, and letters (GENTOW5.16/.19 and S2.3); slot value/digit/full/lift laws
(EFF.T2.04/.05/.09); threshold/window (EFF.T2.04/.11); separate arena data
(EFF.T1.01--.03, D.07/D.08/D.44, EFF.T3.21); and the thirteen FGMN clauses listed above.

**Repository dictionaries:** `keyAt_one`, `keyAt_degree`, terminal receiver maps and squares,
`threshold_nonneg`, `grade_compat`, `letter_compat`, `receiver_eq`, `stageKey_eq`, and
`stageDeg_eq`.

No field is a socket conclusion, `FGMNCalculus`, `SlotCarrier`, `BlockData`, `HVarthetaRes`,
`VarthetaRes`, `WFrame`, or `Nonempty` of any consumer class. Derived consumer structures are
theorems.

## 10. Transcription node plan

Each node is sized for 30--60 minutes and has one independently checkable exit condition.

| node | minutes | dependencies | deliverable / exit condition |
|---|---:|---|---|
| CC-0 core re-home | 30 | none | Move the five freeze core declarations unchanged to a pre-I/C.130a module; I10FreezeV2 still checks and has no duplicate names. |
| CC-1 carrier skeleton | 45 | CC-0, landed C130f | Land `KeyChain`, `LaurentNormalizer`, `NodePointSource`, and live-lint helpers with the U11 signatures only. |
| CC-2 S2 key bridge | 45 | CC-1, C47, C53b, C80, C97 | Promote U11's `s2DepthTwoKeyChain`; prove the full `s2Witness.trunc 2`/`s2Tower` `(e,f,u,ψ,step)` bridge. |
| CC-3 terminal maps | 45 | CC-0, C83 | Construct the recursive `TerminalReceiver` with `Kt = W.fld r`; prove every step square and injectivity. |
| CC-4 Laurent solve | 60 | CC-1, C83, C130f | Construct integer exponents by Bézout/rung recursion; prove exact height for all `ℤ`; state only guarded compatibility with `towerNorm`. |
| CC-5 stage source transcription | 60 | CC-1, EFF.T2.04/.05/.09 | Land the indexed stage value/digit/full/lift source interface and the theorem producing `SlotCarrier`. |
| CC-6 S2 stage regression | 60 | CC-2, CC-5, C46/C47/C127 | Fill every stage-source field at the S2 level-2 occurrence, or issue a precise BLOCKED verdict naming the missing point theorem. |
| CC-7 threshold | 30 | CC-5, EFF.T2.11 | Land integer/natural threshold dictionary and `CanonicalThresholdAt`; no numeral and no function of `(W,i,F₀)`. |
| CC-8 input block | 45 | CC-2, CC-5, CC-7, E10/E11 | Land `RealizedInput` and theorem `inputBlock`; derive development, key-free, `A₀`, and threshold views. |
| CC-9 legal node points | 60 | CC-2, CC-3, GENTOW5.16/.19/S2.3 | Land `Point/Pt`, exact key values, transported `ψ`-root, and ambient letters; exclude all descent claims. |
| CC-10 canonical L-read | 45 | CC-4, CC-9 | Construct/export `canonicalRead` on level kernels and synchronized product; prove distinguished-generator views. |
| CC-11 separate arena | 45 | CC-3, CC-4, CC-9 | Construct `arenaRead`, `GaugeArena`, `towerRead`, and `peelUnit`; audit that no canonical/arena agreement is present. |
| CC-12 transports/views | 60 | CC-5, CC-8, CC-10, CC-11 | Land four live-only view equalities and cross-universe transports; add off-range lint. |
| CC-13 FGMN source carrier | 45 | CC-1, CC-2, U9 | Land `FGMNSourceData`, exact/above definitions, polynomial-valued residual, and OPEN-DICT signatures. |
| CC-14 FGMN laws A | 60 | CC-13 | Transcribe Lemma 3.14, Cor. 4.12(1)--(3), Thm. 4.1/Cor. 4.9 scalar scope; coefficient-zero regressions pass. |
| CC-15 FGMN laws B | 60 | CC-13 | Transcribe recipe/existence/key criterion/irreducibility/key residual/equivalence/letters with U9 scopes. |
| CC-16 FGMN packaging | 30 | CC-14, CC-15 | Replace `FGMNCalculusCheck` by actual A-C.11 class; `ChainRealization → Nonempty FGMNCalculus` checks with no new axiom. |
| CC-17 full S2 carrier | 60 | CC-3--CC-12, CC-13--CC-15 | Construct one named full S2 `ChainRealization` and `RealizedInput`; print axioms and list every cite used. |
| CC-18 socket gate | 45 | CC-12, CC-17 | Land both literal I.10 socket applications, I.10b-to-I.10a refinement, non-swallowing audit, and live-range lint. |

Parallelism: after CC-1/CC-2, CC-3, CC-4, CC-5, CC-9, and CC-13 can run independently.
CC-14 and CC-15 can run in parallel. CC-17 and CC-18 are deliberately serial acceptance
gates.

## 11. Final rulings

1. **Layered vs extended:** layered, for both ripple control and mathematical truth.
2. **Depth two:** the S2 polynomial chain is concretely inhabitable and elaboration-checked;
   the full carrier has a finite, source-labelled constructor ledger and is not claimed landed.
3. **Threshold:** extra inherited field, with WINDOW as a source law; not derivable from
   `(DeepTower,i,F₀)`.
4. **Both consumers:** FGMN is coefficient-zero packaging from source data/laws; C.130b--k are
   derived layer by layer, after which the shared `RealizedInput` feeds both I.10 sockets.

This is the smallest design found that can reach both consumers without changing C.83,
inventing a threshold, identifying the two residue reads, or storing a consumer's conclusion.
