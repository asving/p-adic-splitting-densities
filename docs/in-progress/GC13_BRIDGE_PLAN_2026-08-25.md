# GC-13 PARTITION-RECORD INSTANCE BRIDGE — Sonnet-executable node plan (unit DEC1, 2026-08-25)

**What this plan converts.** The named blocker for chapter E's `BlockSplitTarget` (E.57) —
and, one genre over, `peel_row_law` (E.51) — is the **GC-13 instance bridge**: chapter C's
partition record ⇒ the E-shadow's typed partition leg at instantiated rows. The schema half
is DONE (landed 2026-08-24, `leanfinal/Uniformity/ChapE/E57p.lean`): `PartitionLeg I` is the
typed carrier for E.57's former `hpart : True` socket, `PartitionLeg.toBlockSuite` assembles
the re-signed conclusion, and `block_split_of_partitionLeg` is PROVED with `hpart` typed at
`Nonempty (PartitionLeg I)`. The leanspec twin + `BlockSplitTarget` re-sign are enacted
(A-E.7, `leanspec/Leanspec/ChapE.lean:1253–1351`). What E57p deliberately did NOT attempt —
its docstring: *"The instance bridge (C-record ⇒ this E-shadow leg at each instantiated row)
is an E.22/E.23-genre INSTANCE obligation"* — is decomposed here into seven 30–45-minute
Sonnet nodes plus a named list of what is genuinely missing for anything stronger.

**Elaboration check (deliverable 4).** Every node signature below is pinned as a named
`Prop`/spec in `leanfinal/scratch/DEC1_check.lean` — `lake env lean scratch/DEC1_check.lean`
exit 0, zero `sorry`, zero non-core axiom (all declarations Lean-core
`{propext, Classical.choice, Quot.sound}`). Two joints are TERM-checked there, not just
stated: `DEC1Check.legOfSpecs` proves the N3+N4 field-group specs are **jointly exactly
`PartitionLeg`'s constructor** (the decomposition is lossless), and the closing `example`
type-checks the assembly nodes' firing route verbatim against the landed
`block_split_of_partitionLeg`.

---

## 1. Gap analysis — the E57p correspondence table as a supplier checklist

The checklist is E57p.lean's own "Field ↔ source ↔ C-record correspondence" table. For each
`PartitionLeg` field: the C-record supplier named there, and its ACTUAL status in
`leanfinal` today. Vocabulary: **LANDED** = exists in `leanfinal` with proof (or as a
sanctioned definitional twin); **SIGNED-ONLY** = exists only as a `leanspec` axiom stub;
**REFUTED** = machine-refuted in `leanfinal`; **MISSING** = no signed object exists at all.

| `PartitionLeg` field | named C-record carrier (E57p table) | supplier status |
|---|---|---|
| `cls`, `hclsLin`, `hclsHi` | C.63 `classSize_separable`'s `s : Finset` | **SIGNED-ONLY** — `leanspec/Leanspec/ChapC.lean:2264` (axiom). No `leanfinal` object under any name (`rg classSize_separable leanfinal/Uniformity` → nothing). `HX_SWEEP_2026-08-20.md` row: carries `IsPure Polynomial.X`, status "—" (unadjudicated). |
| `blk` (the per-class `BlockData`/`RungInterface` pair) | C.63's `Fac : … → Polynomial O` + the per-factor `typeOf` read | **SIGNED-ONLY for `Fac`** (same C.63 clause) **+ MISSING for the interface half**: no object anywhere converts a `typeOf (Fac r)` singleton into a `RungInterface` for the block. That conversion is the **arena bridge** (§2 below) — the genuinely missing object. Also note: C.63's `typeOf (Fac r) = ⟨{(e₁ℓ, f₁·deg r)}⟩ ∧ Irreducible (Fac r)` clause is CONDITIONAL on the inertia rider `∀ g' ∈ monicFactors (Fac r), (F.f₁ * r.natDegree) ∣ inertiaDegOf g'` — any consumer must thread it. |
| `hprod` | C.63's `g = ∏ r ∈ s, Fac r` | **SIGNED-ONLY** (same axiom, unconditional clause). |
| `hdisj` | "distinct monic irreducible factors are coprime over `Frac(O)`" | **NOT a C.63 clause at all** (C.63 yields irreducibility only under the rider above). The E-side schema supplier IS LANDED: `Uniformity/ChapE/E36.lean` `coprime_of_not_dvd` (A-E.3 re-signed, `[IsIntegrallyClosed O]`) + `coprime_of_not_dvd_of_descent`. At concrete rows an explicit Bézout witness is cheaper (used below). |
| `hdeg` | `(Fac r).natDegree = (e₁f₁)·ℓ·deg r` (C.63) re-exported through C.69 | **SIGNED-ONLY via C.63 clause 1; the C.69 re-export is POISONED** — see the stop-the-line finding below. The tie `classWeight = (e₁f₁)·ℓ·deg r` at the parent is the instance's arithmetic (free at concrete rows). |
| `hone`, `hpureLin`, `hpureHi` | the one-entry `typeOf` singleton, pure in the parent's `r` | **SIGNED-ONLY + rider-conditional** (same C.63 clause as `blk`); the adjacent C.61 `tier1_typeOf` is **BLOCKED at general `L.ℓ`** in `leanfinal` (`C61_BLOCKED_2026-08-20.md`: proved at `L.ℓ = 1` as `tier1_typeOf_of_ell_one`; general case two nodes deep behind C.59/C.27). `hpureHi`'s `2 ≤ q.1` is `1 < deg r`, free at instances. |
| `hthr` | "the level frame `L` is fixed" | definitional at any instance (no supplier needed). |

### ⚠ Stop-the-line-grade finding (for the orchestrator, not for this plan's nodes):
### leanspec `classSize_supply` (C.69) is refuted-by-instance

`ClassSizeSupplyData.read_form` (leanspec `ChapC.lean:2359`+, twin landed at
`leanfinal/Uniformity/ChapC/C140defs.lean:90–93`) quotes the NAKED C.64 law

```
BlockContext L f → (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f
```

with **no riders**. That exact naked law is machine-REFUTED in leanfinal:
`Uniformity/ChapC/C64.lean` `blockDegEq_false` (at `(s2Frame, L₀, g₀)` over `ℤ_[2]`,
`3 = 2·1` fails while `BlockContext` holds). Instantiating `read_form` at that probe frame
refutes `ClassSizeSupplyData (L₀ h2_padic rc2)`, hence the leanspec axiom
`classSize_supply : ∀ L, ClassSizeSupplyData L` (ChapC.lean:2387) **is false**. A-C.10
(2026-08-24) re-signed the standalone `blockDeg_eq` axiom with the `hlab`/`hdvd` riders
(`blockDeg_eq_resigned` proved on the spot) but did NOT touch the C.69 bundle's quoting
clause — C.69 is out of sync with the A-C.10 re-sign. Consequences:

* **This plan's bridge cites C.63 clauses only, never the bundle name `classSize_supply`.**
* E57p's docstring column header "C-record carrier (C.63/C.69)" should be read as C.63;
  the C.69 half needs a companion re-sign (thread `hlab`/`hdvd` into `read_form`, exactly
  A-C.10's repair) before anything may consume the bundle. That re-sign is an
  orchestrator/amendment item (leanspec edits are outside DEC1's write authority), flagged
  in `runs/wave-b/verdict_DEC1.md`. The `mixed_tie` clause is NOT affected (it carries only
  the floor conjunct `mult₂ L f = m`, which `C67.lean` `mult₂_g₀` shows TRUE at the probe).
* The landed structure twin in `C140defs.lean` is harmless as a definition (a `Prop`-former
  may be uninhabited); the falsity lives in the leanspec ∀-axiom.

---

## 2. Two bridge levels — what is executable now vs. what must exist first

**(a) The SHADOW-instance bridge (this plan, N1–N7).** Both landed non-vacuity gates in
E57p (`E57pCert.pure` positive, `dup_partitionLeg_empty` negative) live at the flat carrier
`E57pCert.flatCarrier : SlotCarrier ℤ ℚ` (`D = 1`, height 0/⊤, constant-term digits). The
E.22/E.23-genre obligation "C-record ⇒ E-shadow leg at each instantiated row" is executable
TODAY at concrete flat-carrier rows whose numerical shadow mirrors a C-record row field by
field: the C.63 content (the Finset `s` of residual labels, `Fac`, the product law, the
degree law, the one-entry `typeOf` per factor) is established by direct computation at the
row — no appeal to the SIGNED-ONLY C.63 axiom. This is exactly how E.22/E.23 discharge
instance obligations (per-row, supplier named per field), executed in Lean rather than as a
table. Crucially, the existing positive gate is a ONE-class row (leg = the state itself,
E39a's honest residue); the bridge content starts at genuinely MULTI-class and hi-class
rows, which no landed gate exercises.

**(b) The ARENA bridge (NOT planned — missing objects named).** Consuming the actual
chapter-C declarations (`classSize_separable` at a `LevelDatum` over a DVR, namespace
`Uniformity.Density.Tower`) to produce a `PartitionLeg` (namespace
`Uniformity.Density.Ladder`) requires two objects that DO NOT EXIST, in order:

1. **C.63 landed in leanfinal.** `classSize_separable` is a leanspec axiom only. It must
   either be proved (research-scale: the residual-factorization engine) or declared as a
   cited axiom with a published-source citation + faithfulness entry + owner sign-off
   (the repo's axiom policy; cite-imports are one of the two owner gates). Until then no
   leanfinal theorem may consume it.
2. **The arena functor** `Tower → Ladder`: a construction taking a chapter-C row
   (`KeyFrame F`, `LevelDatum L`, a C.63 output `(s, Fac)`) to a `SlotCarrier`/`BlockData`/
   `RungInterface` triple with `linFac`/`classCount` read off the `dvResPoly` factorization
   and a `PartitionLeg` read off `(s, Fac)`. **No blueprint node signs this object** —
   E.22/E.23 are declaration-free tables precisely because it is absent. It needs a
   blueprint amendment (design + signatures) before any node plan can be written for it.
   This is an honest MISSING, not an unlanded signature.

Deliverable-list note: no `PartitionLeg` field's supplier is MISSING at level (a) — every
field is dischargeable at concrete rows. The MISSING objects (arena functor; landed C.63)
block only level (b).

---

## 3. The node plan (level (a)) — seven nodes, two concrete rows

**Arena for all nodes:** `leanfinal/`, namespace `Uniformity.Density.Ladder`, new
sub-namespace `E57iCert` ("i" = instance). All rows over the LANDED
`E57pCert.flatCarrier`. Imports: `Uniformity.ChapE.E57p` only (plus each other as listed).
Acceptance for every node: `lake env lean Uniformity/ChapE/<file>.lean` exit 0; zero
`sorry`/`axiom`/`unsafe`; `#print axioms` Lean-core only; the node's closing `example`
proves its `DEC1_check` target **with the target's body copied byte-verbatim** from
`leanfinal/scratch/DEC1_check.lean` (the check file is scratch — not importable — so the
byte-copy is the anti-drift pin). Statement-fence: nothing in `E57p.lean`, `E12.lean`,
leanspec, or any landed file is edited; all nodes only ADD new files.

**The two rows** (both mirror rows of C.63's separable-side law at `D = e₁f₁ = 1`,
`ℓ = 1`, i.e. the level-1 shadow):

* **SPLIT row** — parent `F = X² − 1 = (X+1)(X−1)`, one side `(1,1)`, TWO linear classes,
  labels `1`, `−1` (= the factors' digits), class weight `D·ℓ·deg r = 1` each. This is the
  om4 countermodel's interface SHAPE (one side, two unit-weight linear classes — exactly
  where `hpart : True` made re-signed E.57 FALSE and where `dup_partitionLeg_empty` shows
  the typed leg empty at `F = X²`) at a LEGAL polynomial: the leg becomes inhabited, so the
  pair (dup row, split row) machine-checks that the leg is precisely the separability
  detector. C-record reading: `s` = {residual roots `1`, `−1`}, `Fac` = the linear factors,
  `deg (Fac r) = 1·1·1`.
* **HI row** — parent `F = X² + X + 1`, one side `(1,1)`, ONE higher class `(deg, mult) =
  (2, 1)`, class weight `D·ℓ·deg = 2`, block = the row itself. The inert shape. This
  exercises `hclsHi`/`hpureHi`/`dvd_classCount_hi` — the branch NO landed gate touches
  (`pure` is lin-only; the countermodel is lin-only).

### DEC1-N1 — the split row's parent (`mixBlock`, `mixIface`) [30–45 min]

* **File:** `leanfinal/Uniformity/ChapE/E57i1.lean` (new). Import `Uniformity.ChapE.E57p`.
* **Deliverables:** `noncomputable def mixBlock : BlockData E57pCert.flatCarrier` with
  `Φ = X`, `F = X ^ 2 - 1`, `μ = 2`, `A := fun j => if j = 0 then -1 else 0`, `T = 0`;
  `noncomputable def mixIface : RungInterface.{0,0,0} E57pCert.flatCarrier mixBlock` with
  `sides = {(1,1)}`, `len ≡ 2`, `linFac ≡ {((1:ℚ),1), ((-1:ℚ),1)}`, `hiFac ≡ 0`,
  `rootCount ≡ 2`, `classCount ≡ 1`, `classCountHi ≡ 1`, `W = Unit` (E57p's trivial rank).
  Closing `example : DEC1Check.N1_target-body` (byte-copied ∃-statement) `:=
  ⟨mixBlock, mixIface, rfl, rfl, …⟩`.
* **Template (this is a TRANSCRIPTION node):** `E57pCert.dupBlock`/`dupIface`
  (E57p.lean:633–700) are the SAME interface shape (labels `0`,`1`, `F = X²`); copy field
  by field, changing only `F`, `A`, the two labels, and the `F`-touching proofs.
* **The three F-touching proofs:** `hdev`: `X^2 - 1 = X^2 + ∑ j ∈ Finset.range 2, A j * X^j`
  — `simp [Finset.sum_range_succ]; ring`. `hkeyfree`:
  `IsCoprime ((X^2-1).map …) (X.map …)` — integer Bézout witness `⟨-1, X⟩`
  (`(−1)(X²−1) + X·X = 1`): `refine ⟨-1, X, ?_⟩;
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one];
  ring`. `hA0 : (-1 : Polynomial ℤ) ≠ 0` — `by norm_num` (or `neg_ne_zero.mpr one_ne_zero`).
* **Interface laws** are label-independent numerics identical to `dupIface`'s
  (`1·(1+1+0)=2`, `rootCount = 1·2`, `1 ≤ 1`, `1·1 ≤ 1`, `1+1 = 2`): reuse its proofs.

### DEC1-N2 — the second child (`pureBlock₂`, `pureIface₂`) [30 min]

* **File:** `leanfinal/Uniformity/ChapE/E57i2.lean` (new). Import `Uniformity.ChapE.E57p`.
* **Deliverables:** `pureBlock₂ : BlockData E57pCert.flatCarrier` with `Φ = X`,
  `F = X - 1`, `μ = 1`, `A := fun _ => -1`, `T = 0`; `pureIface₂ :
  RungInterface.{0,0,0} E57pCert.flatCarrier pureBlock₂` with `sides = {(1,1)}`, `len ≡ 1`,
  `linFac ≡ {((-1:ℚ),1)}`, `hiFac ≡ 0`, `rootCount ≡ 1`, `classCount ≡ 1`. Closing
  `example : DEC1Check.N2_target-body := ⟨pureBlock₂, pureIface₂, …⟩`.
* **Template:** `E57pCert.pureBlock`/`pureIface` (E57p.lean:535–591) verbatim with
  `1 → -1` in `A`, `F`, and the label. `hkeyfree` witness `⟨-1, 1⟩`
  (`(−1)(X−1) + 1·X = 1`). `hdeg`-relevant fact `(X - 1 : Polynomial ℤ).natDegree = 1`:
  `X - 1 = X + C (-1)` then `natDegree_X_add_C` (pureBlock used `natDegree_X_add_C (1 : ℤ)`;
  here `simpa using natDegree_X_add_C (-1 : ℤ)` after rewriting `sub_eq_add_neg` /
  `map_neg` on `C`). The label-`1` child is NOT rebuilt — the landed
  `E57pCert.pureBlock`/`pureIface` is reused as-is by N3–N5.

### DEC1-N3 — ledger + product + disjointness field-group at the split row [30–45 min]

* **File:** `leanfinal/Uniformity/ChapE/E57i.lean` (new; N3, N4, N5 append to it in
  order). Imports `Uniformity.ChapE.E57i1`, `Uniformity.ChapE.E57i2`.
* **Named inputs:** `mixBlock`/`mixIface` (N1), `pureBlock₂`/`pureIface₂` (N2), landed
  `E57pCert.pureBlock`/`pureIface`, `ClassIx`, `classWeight` (E57p).
* **Deliverables:** the row data
  `def a1 : ClassIx ℚ := ((1,1), Sum.inl ((1:ℚ), 1))`,
  `def a2 : ClassIx ℚ := ((1,1), Sum.inl ((-1:ℚ), 1))`,
  `def splitCls : Finset (ClassIx ℚ) := {a1, a2}`,
  `noncomputable def splitBlk : ClassIx ℚ → Σ B' : BlockData E57pCert.flatCarrier,
  RungInterface.{0,0,0} E57pCert.flatCarrier B' := fun c => if c = a1 then
  ⟨E57pCert.pureBlock, E57pCert.pureIface⟩ else ⟨pureBlock₂, pureIface₂⟩`
  (`DecidableEq (ClassIx ℚ)` is instance-found), and
  `theorem split_N3 : DEC1Check.N3_spec-body applied at (mixIface, splitCls, splitBlk)`
  (byte-copy the four conjuncts from `N3_spec`, substituting the three concrete names).
* **Proof shapes:** `hclsLin`/`hclsHi` iffs — `intro p q; simp [splitCls, a1, a2,
  mixIface]` then `constructor`/`omega`-free case bash (the dup proof at
  E57p.lean:716–733 is the exact template, including the `Multiset.insert_eq_cons`
  simp set). `a1 ≠ a2`: `by simp [a1, a2]` (labels `1 ≠ −1` in ℚ; the dup file's `hne`
  is the template). `hprod`: `Finset.prod_pair hne`, `simp [splitBlk, a1, a2]` to expose
  `(X+1)*(X-1)`, close by `ring` against `mixBlock.F = X^2 - 1`. `hdisj`: reduce by cases
  to the single pair (both orders); witness
  `⟨Polynomial.C ((2 : FractionRing ℤ)⁻¹), -(Polynomial.C ((2 : FractionRing ℤ)⁻¹)), ?_⟩`
  — `c(X+1) − c(X−1) = 2c = 1`. Needs `(2 : FractionRing ℤ) ≠ 0`: via
  `IsFractionRing.injective ℤ (FractionRing ℤ)` on `(2 : ℤ) ≠ 0` (push `2` through
  `map_ofNat`); then `field_simp`/`mul_inv_cancel₀`. Fallback if the Bézout push-through
  fights: search `Polynomial.pairwise_coprime_X_sub_C` (candidate name — VERIFY with
  `lean_local_search`/loogle before use), noting `map (X+1) = X − C (−1)`,
  `map (X−1) = X − C 1`, distinct constants; use `IsCoprime.symm` for the flipped order.

### DEC1-N4 — degree + purity + threshold field-group at the split row [30 min]

* **File:** `E57i.lean` (append after N3). **Named inputs:** N3's `a1/a2/splitCls/splitBlk`.
* **Deliverable:** `theorem split_N4 : DEC1Check.N4_spec-body at (mixIface, splitCls,
  splitBlk)` — five conjuncts.
* **Proof shapes:** all five are two-case (`c = a1`/`c = a2`) computations:
  `hdeg`: `natDegree (X+1) = 1 = classWeight mixIface a1` (`classCount ≡ 1`;
  `natDegree_X_add_C`, and N2's `X − 1` degree fact); `hone`: child `sides = {(1,1)} =
  {c.1}` — `rfl` per case; `hpureLin`: `⟨1, le_rfl, rfl, rfl⟩` per case (child `linFac ≡
  {(label,1)}` matches the parent's label BY CONSTRUCTION — this is the field where a
  label mismatch would be caught); `hpureHi`: vacuous — `intro p q h; simp [splitCls, a1,
  a2] at h` (no `Sum.inr` address in the ledger); `hthr`: `rfl` per case (`T = 0`
  everywhere).

### DEC1-N5 — ASSEMBLY at the split row + firing `block_split_of_partitionLeg` [30 min]

* **File:** `E57i.lean` (append after N4). **Named inputs:** `split_N3`, `split_N4`,
  landed `block_split_of_partitionLeg`, `PartitionLeg.supplies_hblocks`/`_hblocksHi`,
  `PartitionLeg.dvd_classCount_lin`.
* **Deliverables (this is the plan's deliverable 3):**
  1. `noncomputable def splitLeg : PartitionLeg mixIface :=
     ⟨splitCls, split_N3.1, split_N3.2.1, splitBlk, split_N3.2.2.1, split_N3.2.2.2,
     split_N4.1, split_N4.2.1, split_N4.2.2.1, split_N4.2.2.2.1, split_N4.2.2.2.2⟩`
     — the anonymous constructor in exactly `DEC1Check.legOfSpecs`'s field order
     (term-checked in the check file; if N3/N4 were landed as separate conjunct lemmas
     instead of packed ∧-chains, adjust projections only).
  2. `theorem split_partitionLeg_nonempty : Nonempty (PartitionLeg mixIface) := ⟨splitLeg⟩`
     — **`Nonempty (PartitionLeg I)` at the concrete row**: the typed `hpart` socket
     DISCHARGED at an instance for the first time beyond the one-class residue.
  3. `theorem split_blockSuite : Nonempty (BlockSuite mixIface) :=
     block_split_of_partitionLeg mixIface splitLeg.supplies_hblocks
     splitLeg.supplies_hblocksHi ⟨splitLeg⟩` — the corrected E.57 statement FIRED
     end-to-end at the row (the check file's closing `example` is this term verbatim).
  4. Teeth: `example : splitCls.card = 2 := by decide`-or-`simp [splitCls, a1, a2]`
     (genuinely multi-class — strictly beyond `E57pCert.pure`); the closing
     `example : DEC1Check.N5_target-body := ⟨mixBlock, mixIface, rfl, rfl,
     split_partitionLeg_nonempty, split_blockSuite⟩`.
  * Honest note to carry in the file: at `D = 1` the E-D15 divisibility reads
    (`dvd_classCount_lin`: `1·1 ∣ 1`) are numerically trivial; the hi row (N7) carries the
    non-trivial one.

### DEC1-N6 — the hi row (`hiBlock`, `hiIface`) [30–45 min]

* **File:** `leanfinal/Uniformity/ChapE/E57ih.lean` (new; N6 + N7). Import
  `Uniformity.ChapE.E57p` only (independent of N1–N5).
* **Deliverables:** `hiBlock : BlockData E57pCert.flatCarrier` with `Φ = X`,
  `F = X ^ 2 + X + 1`, `μ = 2`, `A := fun j => if j = 0 then 1 else if j = 1 then 1 else 0`,
  `T = 0`; `hiIface : RungInterface.{0,0,0} E57pCert.flatCarrier hiBlock` with
  `sides = {(1,1)}`, `len ≡ 2`, `linFac ≡ 0`, `hiFac ≡ {(2, 1)}`, `rootCount ≡ 2`,
  `classCount ≡ 1`, `classCountHi ≡ 2`. Closing `example : DEC1Check.N6_target-body`.
* **Proof shapes:** template again `dupBlock`/`dupIface` with the hi-side laws now live:
  `hdev`: `A 0 = 1`, `A 1 = 1` — `simp [Finset.sum_range_succ]; ring`. `hkeyfree`: integer
  witness `⟨1, -(X + 1)⟩` (`F − (X+1)·X = 1`). `hresdeg`: `1 * (0 + (2*1)) = 2` — `simp`.
  `haccount`: `2 = 1 * 2`. `hnonempty` hi: `1 ≤ 2`. `hforce` hi: `1*1*2 ≤ 2` — `le_rfl`
  after `simp [E57pCert.flatCarrier]`. `hexhaust`: `0 + 2 = 2`. Lin clauses all vacuous
  (`linFac ≡ 0` — `simp at hq` pattern from `pureIface.hnonempty`).

### DEC1-N7 — ASSEMBLY at the hi row + firing [30–45 min]

* **File:** `E57ih.lean` (append). **Named inputs:** `hiBlock`/`hiIface` (N6), landed
  `block_split_of_partitionLeg`, `PartitionLeg.dvd_classCount_hi`.
* **Deliverables:** `def ah : ClassIx ℚ := ((1,1), Sum.inr (2, 1))`; `hiLeg :
  PartitionLeg hiIface` with `cls = {ah}`, `blk := fun _ => ⟨hiBlock, hiIface⟩` (the
  one-class residue is HONEST here exactly as E39a disclosed for `pure`: an inert row's
  single block IS the row); `hprod` — `Finset.prod_singleton`; `hdisj` — vacuous
  (singleton); `hdeg` — `(X^2+X+1).natDegree = 2 = classWeight hiIface ah`
  (route: `(hiBlock.natDegree_F).1` gives `natDegree = μ·D = 2·1` — avoids
  `compute_degree`); `hone`/`hthr` — `rfl`; `hpureLin` — vacuous; `hpureHi` —
  `⟨1, le_rfl, by norm_num, rfl, rfl⟩` (`k = 1`, `2 ≤ 2`). Then
  `hi_partitionLeg_nonempty : Nonempty (PartitionLeg hiIface)`,
  `hi_blockSuite : Nonempty (BlockSuite hiIface)` via the same firing term, and teeth:
  `example : (1 * 1 * 2 : ℕ) ∣ hiIface.classCountHi (1,1) (2,1)` read through
  `hiLeg.dvd_classCount_hi (1,1) … (2,1) …` — the E-D15 hi divisibility consumed at a row
  where it says something (`2 ∣ 2` from the leg, not from `norm_num`). Closing
  `example : DEC1Check.N7_target-body`.

### DAG and dispatch

```
wave 1 (parallel):  N1 (E57i1.lean)   N2 (E57i2.lean)   N6 (E57ih.lean, part 1)
wave 2 (parallel):  N3 → N4 (E57i.lean, sequential, may be one agent)   N7 (E57ih.lean, part 2)
wave 3:             N5 (E57i.lean, final section)
```

Three files never share a writer within a wave. Total ≈ 7 node-slots, ≈ 4 agent-sessions
if N3+N4 and N6+N7 are paired. Every node commits its own file section when green
(survival discipline). If any `simp`-set fights for more than ~3 repair rounds, the
executor must fall back to the corresponding dup/pure proof text (E57p.lean is the
canonical template) rather than invent new automation.

### After landing (orchestrator items, NOT fleet nodes)

1. Update `Uniformity/ChapE/E23.lean`'s ⚠ mixed-node row: the schema supplier is
   `block_split_of_partitionLeg` (landed) and the shadow-instance bridge is
   E57i/E57ih (landed); the ARENA legs remain C-PLACEHOLDER (§2(b) objects).
2. The C.69 companion re-sign (§1 finding) — leanspec edit + A-C.11-style record.
3. `BlockSplitTarget` itself stays NOT ASSERTED in leanspec (it is a named `Prop`, and
   asserting it ∀-over-interfaces is FALSE-adjacent by design — assertion happens per
   instance, which is exactly what N5/N7 do through the landed theorem).
4. E.51's `hpeel : True` is the OTHER GC-13 socket — same treatment, separate
   decomposition: it needs a typed `PeelLeg` against E.37 `peel_once` (landed) with the
   HE6R1-3 emission record as the C-side carrier (C-PLACEHOLDER per E.23's table). Not
   planned here.

---

## 4. Elaboration-check record (deliverable 4)

`leanfinal/scratch/DEC1_check.lean` — run 2026-08-25, `lake env lean scratch/DEC1_check.lean`
→ **exit 0**; no `sorry`, no `axiom`, no `unsafe`; `#print axioms` on `splitCls`,
`N1_target`, `N3_spec`, `N4_spec`, `N5_target`, `N7_target`, `legOfSpecs` all report at most
`{propext, Classical.choice, Quot.sound}`. Contents: `N1`–`N7` targets/specs as above,
`legOfSpecs` (N3+N4 = the `PartitionLeg` constructor, term-checked), and the firing-route
`example` (the N5/N7 term against the landed `block_split_of_partitionLeg`, type-checked
with binders abstract).
