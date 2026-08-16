# RESCHEDULE record — NODE E.57 (`block_split`), Chapter-E fleet wave 7, agent 3

**Date.** 2026-08-16. **Verdict.** **BLOCKED at the GC-13 resolution pre-check**, twice over:
the chapter-C anchor the socket must be typed against is **not landed in `leanfinal`** (the
E.51 situation, one node over), and — the new finding, machine-checked — **typing the socket
would not unblock the node anyway**, because E.57's committed CONCLUSION is a theorem of Lean
core. Nothing was weakened, nothing was proved at the `True` placeholder, no declaration was
added to any built module. The evidence file is
`leanfinal/Uniformity/ChapE/E57_VACUITY.lean.txt` (`.lean.txt`, so no build picks it up).

## What was asked, and the precedent it follows

Wave 7's charge: land E.57 as a PLACEHOLDER SOCKET on the **E.61/E.62 precedent** (commits
`4137d3cf`, `87ec412b`) — those two `supplied : True` sockets of §9 were TYPED at the
GC-13/GC-14 resolution against chapter D's **landed** carriers (`HVarthetaRes` at
`ChapD/D62.lean`; `Wle`/`GentowW` at `ChapD/D55.lean`/`D44.lean`), each binding machine-checked
as an `Iff` unit test inside the node file. That pass runs only when the supplier chapter is
landed. Chapter D is complete (2026-08-16); **chapter C is not**, which already blocked E.51
(`leanfinal/notes/RESCHEDULE_E51_2026-08-16.md`, commit `ce61e801`).

## The committed stub (verbatim, `leanspec/Leanspec/ChapE.lean:1154-1171`)

```lean
-- BLOCKED: GC-13 resolution (§12 BLOCKED-UNTIL-RESOLUTION; `hpart : True` placeholder —
-- the product/disjointness carrier leg, typed against chapter C's partition record at freeze.
-- The fleet must NOT fire on E.57 before that pass.)
/-- **E.57** [theorem, HARD] The mixed-node block split (ANNEX-LEMMA HE7-13′(a), schema
form) — the PROVED level-≥2 counterpart of `(LB1)`. -/
axiom block_split {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K]
    {C : SlotCarrier O K} {B : BlockData C} (I : RungInterface C B)
    -- carrier legs (C-supplied at instances; the schema's explicit hypotheses):
    (hblocks : ∀ p ∈ I.sides, ∀ q ∈ I.linFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCount p q)
    (hblocksHi : ∀ p ∈ I.sides, ∀ q ∈ I.hiFac p,
      ∃ Fpq : Polynomial O, Fpq.Monic ∧ Fpq ∣ B.F ∧
        Fpq.natDegree = I.classCountHi p q)
    (hpart : True)  -- the product/disjointness leg; typed at GC-13 resolution
    : ∃ blocks : List (Polynomial O),
        B.F = blocks.prod ∧
        (blocks.map Polynomial.natDegree).sum = B.F.natDegree
```

Blueprint twin: `blueprint/CHAP-E_sigma_ladder.md` §8 NODE E.57 (lines ~3934-4005), whose
SIGNATURE NOTE reads *"typed at GC-13 resolution — the node is BLOCKED for the fleet until
then (§12)"*, and whose §12 entry reads *"BLOCKED-UNTIL-RESOLUTION (do NOT stub as provable):
… E.57 (`hpart : True`)"*.

## BLOCK 1 — the anchor: chapter C's class-partition record is not landed

The leg `hpart` stands for is named in the §11 cross-chapter ledger (line ~4571):
*"`EFF.HE7.06`-Pt / `.29`-Galois / **`.96`-partition legs** `[supplied-by: chapter C]` (E.23,
E.36, **E.57**)"*, and in the node's own SIGNATURE NOTE: *"the classes partition the roots —
`EFF.HE7.96`(a)'s 'the label's factor is the minimal polynomial' argument, K-theoretic,
C-supplied"*. The chapter-C record carrying exactly that content is **C.63
`classSize_separable`** — the only signed statement in either chapter whose conclusion IS a
per-class product decomposition,

```lean
      g = ∏ r ∈ s, Fac r ∧
      ∀ r ∈ s, (Fac r).Monic ∧
        (Fac r).natDegree = (F.e₁ * F.f₁) * L.ℓ * r.natDegree ∧ …
```

(`blueprint/CHAP-C_tower_grammar.md` §7 NODE C.63, lines ~3992-4055; stub twin
`leanspec/Leanspec/ChapC.lean:2014`) — re-exported for downstream chapters as **C.69
`classSize_supply` / `ClassSizeSupplyData`**, the node CHAP-C itself labels *"TERMINAL SUPPLY:
THE CLASS-SIZE/BLOCK-LENGTH BUNDLE … chapter E's `EFF.HE6.30`/`.32` pin anchors ([F1]
resolution: they resolve HERE) … have ONE name to cite"* (lines ~4352-4400; stub twin
`leanspec/Leanspec/ChapC.lean:2098`/`:2125`).

Pre-check evidence, this tree, 2026-08-16 (`grep -rn <name> leanfinal --include="*.lean"`):

| needed | where it is signed | landed in `leanfinal`? |
| --- | --- | --- |
| `classSize_separable` (C.63 — the partition/product law itself) | `leanspec/Leanspec/ChapC.lean:2014` | **NO** — zero hits; no `ChapC/C63.lean` |
| `classSize_supply` / `ClassSizeSupplyData` (C.69 — the terminal-supply name E is told to cite) | `leanspec/Leanspec/ChapC.lean:2098`, `:2125` | **NO** — zero hits; no `ChapC/C69.lean` |
| `tier1_typeOf` (C.61 — the per-class singleton `typeOf`, C.63's per-block input, and the source of clause (ii)'s pure-residual read) | `leanspec/Leanspec/ChapC.lean:1973` | **NO** — zero hits |
| `BlockContext` (C.33/C.34 — the block/label heredity context C.63's proof runs in) | `leanspec/Leanspec/ChapC.lean:912` | **NO** — zero hits |
| `blockFactor`, `mult₂` (C.35 — the block vocabulary) | leanspec §5 (body elided; A-C.1 defect D2: *"the single highest-value missing signature in the signed half of the chapter"*) | **NO** — prose mentions only (`ChapC/C09.lean:66-67`, `ChapC/C38a.lean:43`) |
| `SlotCarrier`, `BlockData`, `RungInterface` (E.10/E.11/E.12 — E.57's OWN binders) | this chapter | **yes** (`ChapE/E10.lean:75`, `E11.lean:109`, `E12.lean:130`) |

`leanfinal/Uniformity/ChapC.lean` carries 48 node imports and jumps `C60 → C71 → C83`; §7's
Tier-1 layer (C.61-C.65, C.67) and the supply bundle (C.69) are absent as a block, exactly as
§5's block layer (C.33-C.40) is.

**RESCHEDULE: needs `Uniformity.Density.Tower.classSize_separable` (C.63) — or its terminal
re-export `Uniformity.Density.Tower.classSize_supply` / `ClassSizeSupplyData` (C.69) — which in
turn need `tier1_typeOf` (C.61), `BlockContext` (C.33/C.34) and `blockFactor`/`mult₂` (C.35).**

## BLOCK 2 — the socket typing is orthogonal to the node's strength (machine-checked)

Even with C.63 landed, a socket swap would leave E.57 vacuous. The committed conclusion

```lean
    ∃ blocks : List (Polynomial O),
        B.F = blocks.prod ∧ (blocks.map Polynomial.natDegree).sum = B.F.natDegree
```

is satisfied by `blocks := [B.F]`: `List.prod_singleton` gives the first clause,
`List.sum_singleton` the second. `E57_VACUITY.lean.txt` proves three statements, all
Lean-core-axiom-clean at the repo pin:

* `block_split_IS_A_THEOREM` — the committed signature byte-for-byte, proved outright; the
  linter flags `hblocks`, `hblocksHi` and `hpart` as all unreferenced;
* `block_split_conclusion_from_nothing` — the same conclusion for an arbitrary polynomial over
  an arbitrary `CommRing`, with no carrier, no block, no interface, no `IsDomain`;
* `socket_typing_is_orthogonal` — `∀ P : Prop`, the committed shape with `hpart : P` is
  provable by ignoring `hpart`. So no typing of the socket can add strength.

This is the genre **OM-4 FINDING 0** caught at E.39/E.40/E.44
(`docs/openmath-campaign/OM-4_lb1-mp1_2026-08-16.md` §2.3; witness
`verification/om4_shadow_vacuity.lean`), where the SIGNATURE-NOTE abbreviations had removed the
clauses carrying the strength and **AMENDMENT A-E.2** re-signed the nodes at their full
`BlockSuite`/`MidPeelEmission` records. E.57's SIGNATURE NOTE says the same thing about itself
in advance — *"the conclusion shape displayed is the PRODUCT/EXHAUSTION layer; the full contract
adds, per block, the single-side and pure-residual interface clauses of (ii)–(iv) as a
`BlockSuite` record (the E.39 note's structure, INSTANTIATED here rather than hypothesized)"* —
so the gap is disclosed, not hidden; what is new is the machine proof that the displayed layer
is empty rather than weak.

**Consequence for the resolution pass.** E.57 needs an **amendment**, not a socket swap: the
conclusion must be re-signed to carry clauses (ii)–(iv) per block (single side of slope `p`,
length `L_{p,q} = deg f_{p,q} / (C.D …)`, pure residual shadow with multiplicity
`k = L_{p,q}/(p.2 · deg q) ≥ 1`, side-length additivity `Σ_q L_{p,q} = len p`, and the
trichotomy gate `L_{p,q} = k·p.2·deg q ≥ 4` feeding E.59). Only clause (iv)'s arithmetic is
E-internal today (`block_jump_gate`, landed at `ChapE/E59.lean:63`); (i)–(iii) are what the
chapter-C partition record supplies.

## Why not a restatement, and why not "prove it anyway"

1. **No machine-checkable binding.** What made E.61/E.62 honest is the `Iff` unit test against
   the landed chapter-D declaration, so the socket cannot drift from its supplier. With C.63
   absent there is nothing to prove an `Iff` against, and a hand-copied conclusion is the
   shared-extraction shape that inherits any corruption in the copy (MEMORY: extraction-
   corruption decorrelation).
2. **It would re-sign the node over chapter C's tower parameter block.** C.63 is stated over
   `O`, `π`, `F : KeyFrame O π`, `H₀`, `hpin`, `L : LevelDatum …`, `dvSideSet`/`dvResPoly`
   data — none of which appears in E.57's committed binders, which live over `SlotCarrier` /
   `BlockData` / `RungInterface`. Importing them is an amendment, not a resolution pass.
3. **Proving the committed form is explicitly forbidden and would be worse than useless.**
   §12: *"BLOCKED-UNTIL-RESOLUTION (do NOT stub as provable)"*. BLOCK 2 shows why: landing
   `block_split` at the committed conclusion would put a green, Lean-core-clean, HARD-node
   check-mark on a statement that says nothing, and chapter I would consume it as the
   level-≥2 counterpart of `(LB1)`.

## Two signature observations for the amendment (not blockers, not patched here)

* **`hblocks`/`hblocksHi` are individually weak in the same direction.** Each asserts, per
  class, the EXISTENCE of a monic divisor of `B.F` of the right degree — with no injectivity
  across classes and no coprimality, so the same `Fpq` may serve every class. The product
  clause therefore does not follow from them even in spirit; it is `hpart`'s whole job, and
  `hpart` is `True`. The amendment should carry the family as one function
  `Fac : Σ p ∈ sides, … → Polynomial O` with the product law, C.63's shape.
* **`I.classCount`/`I.classCountHi` are already pinned by E.12.** `hforce` + `hexhaust` +
  `haccount` saturate the per-side counts (E.12's gate (b′) proves the saturation:
  `c ≤ a, 2c ≤ b, a + b = 3c ⊢ a = c ∧ b = 2c`). So the degree data clauses (ii)/(iii) of the
  amendment are constrained by the interface the node already takes — the amendment does not
  need new numerical hypotheses, only the honest conclusion.

## Status

No file in any built module was touched. Committed by this record: this note and
`leanfinal/Uniformity/ChapE/E57_VACUITY.lean.txt`. E.57 remains an `axiom` stub in
`leanspec/Leanspec/ChapE.lean` with its `-- BLOCKED: GC-13 resolution` header intact.
