/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/

/-!
# Uniformity.ChapE.E23 — the LEVEL-TWO and TOWER instance records (HE7 / HETOW / GENTOW4), as an obligation table

**Chapter E, NODE E.23** [instance-record] [fresh] (`blueprint/CHAP-E_sigma_ladder.md` §4 — the
master HE7.A suite, level two). ENVIRONMENT: n/a.

**NO Lean declaration, by signature.** The blueprint signs this node `SIGNATURE. none
(obligation record)`, `PROOF. n/a`, and the leanspec census names E.22 and E.23 as the chapter's
only two declaration-free nodes ("**109 signed blueprint declarations** … Nodes with NO
declaration: **E.22** and **E.23**, the two instance-records, which the blueprint itself signs as
tables"). The artifact IS the table below. Like `Uniformity.ChapE.E22` and
`Uniformity.ChapD.D64`, this file deliberately **imports nothing and defines nothing**, so it can
never become a silent dependency of a proof.

## What is being instantiated (`EFF.T2.35`/`.36`/`.37`, the boxed displays)

Three records instantiate the §4 structures (E.10 `SlotCarrier`, E.11 `LadderKeyData`/block
layer, E.12 `RungInterface`) at level two and in the towers. Their frame data, transcribed from
the source's own boxes:

| | `EFF.T2.35` HE7-INSTANCE (S3.3) | `EFF.T2.36` HETOW-INSTANCE (S3.4) | `EFF.T2.37` GENTOW4-INSTANCE (S3.5) |
|---|---|---|---|
| `K_𝒞` | `K₂` | `K₂ ≅ 𝔽_{Q^{f₁f₂}}` | `K₂` |
| `Φ` | `Ψ_{λ,r}` | `Φ₂` | `Φ₂` |
| `D` | `D″ = D′ℓd_r` | `D₂ = D′e₂f₂` | `D₂ = D′e₂f₂` |
| `(e_𝒞, f_𝒞)` | `(e₁ℓ, f₁d_r)` | `(e₁e₂, f₁f₂)` | `(e₁e₂, f₁f₂)` |
| `d` | `dv₂ = ℓ·dv = ℓe₁v` | `dv₂ = e₁e₂v` | `dv₂ = e₁e₂v` |
| `T` | `T₂ = ℓd_r u` | `T₂ = e₂f₂u₂` | `T₂` |

with the block reads `|S_{λ₂,r₂}| = D″ℓ₂ deg r₂`, `e = e₁ℓℓ₂`, `f = f₁d_r deg r₂` (`.35`);
`e = e₁e₂ℓ₂`, `f = f₁f₂ deg r₂` and the frame conversion `R_{λ₂}(Z) = τ(H₀)·R̂_{λ₂}(Z/δ)`,
`δ = τ(u₃) ∈ K^×` (`.36`); and `μ₂* = Σ_{λ₂>T₂} L_{λ₂}(f)`, `deg f_S = D₂μ₂*` (`.37`).
`EFF.T2.35` adds: *"The key `Ψ_{λ,r}` is monic. Its irreducibility is not a premise."*

## The obligation map (one row per §4 field, transcribed from the blueprint)

**The decisive difference from E.22**: most field suppliers here are E's OWN §5 nodes — the
level-two machinery is HE7's, ruled into chapter E — so the third column is checkable against
`leanfinal`, and the fourth column records the check. (Rows whose supplier is a chapter-C
`[supplied-by: chapter C]` GC-13 placeholder are marked C-PLACEHOLDER: nothing in `leanfinal`
is expected, and none is claimed.)

| field | supplier | citation form | landed status (checked at this landing) |
|---|---|---|---|
| `hgt`/`dig` + slot laws | (SLOT₂) = E.29 (schema) over the level-1 carrier; normalizer system `n₂` | E.29; carrier data `EFF.HE7.06 [supplied-by: chapter C]` for the `Pt`-evaluation legs | E.29 LANDED — `twisted_slot_spec` **at the A-E.4 re-signed type**, plus `attainer_in_class`, `twisted_slot_spec_of_attain_value`; `Pt`-evaluation legs C-PLACEHOLDER |
| `Full`/`hlift` | (LIFT₂) = E.31, thresholds E.08, margins E.09 | E-internal | E.31 `twisted_lift`, E.08 `lift_threshold_step`, E.09 `useSite_margin` — all LANDED |
| `sides` etc. at level 2 | the `P₂` polygon of the Ψ-development, read off `f` when the block is proper: LEMMA HE6R1-2 (with the CORRECTED per-side scalar `γ_g·β^{c₁(m₁^{f_S}, c_g)}`, honesty E-1's HE7 residual noted) | `EFF.HE6R1 [supplied-by: chapter C]`; the scalar's exponent arithmetic = E.04/E.33 | HE6R1-2 C-PLACEHOLDER; the arithmetic half LANDED — E.04 `cocycle_exp_mem`/`cocycle_carry`, E.33 `coc`/`coc_cocycle`/`theta_telescope`/`coc_of_hom` |
| `haccount` | `(†₂-count)` + HE6-3 sampling (`EFF.HE7.41`'s proof) | the derivation is C's (polygon sampling); its termwise output `n_{λ₂} = D″L_{λ₂}` enters as the field | C-PLACEHOLDER (derivation); the field itself is E.12's `haccount`, LANDED as a field of `RungInterface` |
| `hforce` | LEMMA HE7-5 = local forcing (key-free) | `EFF.HE7.29 [supplied-by: chapter C]` for the Galois/valuation legs; GC-3 rank form at the `e·f` read | C-PLACEHOLDER; the `e·f` read's schema shape LANDED at E.15 `ef_forcing`/`multiset_sandwich` |
| `hnonempty`/`hexhaust` | LEMMAS HE7-9/HE7-10 + COROLLARY HE7-7″ (licensed by R2-a = E.36) | schema shape E.14–E.16; carrier legs C placeholders | schema LANDED — E.14 `RungInterface.SepSide`/`forced_sum_eq`, E.15, E.16 `he7a_clause12`; E.36 LANDED **at the A-E.3 re-signed type** (`coprime_of_not_dvd` now carries `[IsIntegrallyClosed O]`); carrier legs C-PLACEHOLDER |
| `(SEC-RANK)` | LEMMA HE7-8 = E.55 (well-foundedness form) at a DEFINITION HE6-1 key; at the COMPOSED key via `HETOW-A`(ii)/`GENTOW-4-A`(iii) + the W+w fold (E.42) | E.55/E.42 + `EFF.T2.52`'s two composed-key bullets → `[supplied-by: chapter C]` for the HETOW/GENTOW4 clauses | E.55 LANDED **at the A-E.5 re-signed type** — the signed name `refine_chain_finite` declared over `refine_chain_finite_of_key`, with the two added binders `hkey`/`hAdeg`; E.42 `s18b_fold` LANDED; HETOW/GENTOW4 clauses C-PLACEHOLDER |
| `(RISE)`/`(REF-HT)` | LEMMA HE7-12/13 = E.38/E.56; the derivation E.56 | E-internal (schema) | E.38 `slot_fold` (+ E.38a `offdisk_positivity`), E.56 `same_digit_rises`/`chain_invariant`/`chain_invariant_pairwise` — all LANDED |
| the peel at Ψ | LEMMA HE6R1-3 + the convention chain = E.37 (licensed by R2-a = E.36) | `EFF.HE6R1 [supplied-by: chapter C]` for HE6R1-3's own proof | E.37 `peel_once` LANDED; HE6R1-3's own proof C-PLACEHOLDER |
| mixed-node blocks | ANNEX-LEMMA HE7-13′ = E.57 | E-internal (schema) + C legs | **E.57 IS BLOCKED — see the stop-the-line row below.** No Lean supplier exists for this row |

## ⚠ THE ONE ROW THAT IS NOT MERELY OWED: E.57 (mixed-node blocks)

E.57 is **BLOCKED**, on two independent grounds recorded at
`leanfinal/notes/RESCHEDULE_E57_2026-08-16.md` and machine-checked in
`leanfinal/Uniformity/ChapE/E57_VACUITY.lean.txt` (kept as `.lean.txt` so no build picks it up):

1. **the anchor is not landed** — `hpart`'s GC-13(c) `[supplied-by: chapter C]` leg (the
   `EFF.HE7.96` partition record: `classSize_separable` = C.63, re-exported as
   `classSize_supply`/`ClassSizeSupplyData` = C.69) is absent from `leanfinal`, together with
   `tier1_typeOf` (C.61), `BlockContext` (C.33/C.34) and `blockFactor`/`mult₂` (C.35);
2. **typing `hpart` would not make the node contentful** — the committed CONCLUSION is a theorem
   of Lean core (`blocks := [B.F]`, `List.prod_singleton`, `List.sum_singleton`), proved there
   for an arbitrary polynomial over an arbitrary commutative ring with no interface in scope.
   So the resolution owed is an AMENDMENT (re-sign the conclusion at the per-block
   `BlockSuite`/single-side/pure-residual record), not a GC-13 socket swap.

**Consequence for this record, stated plainly.** The mixed-node-block row of the table above has
**no supplier**, in `leanfinal` or in a chapter-C placeholder that could be filled by the GC-13
pass alone. Any consumer of E.23's obligation map that needs mixed-node blocks is consuming an
OPEN row. This record does not close it and does not disguise it. Nothing here is weakened to
make the table look complete: the row is transcribed at full strength and marked.

## Fences carried verbatim

* `EFF.T2.35` (CONDITIONALITY): *"Residual labels are irreducible; the current key need not be.
  If the underlying level-one key was recentered, S1.8C transports the HE3+HE6 frame with its
  existing `(LB1)`/`(MP1)` triggers."*
* `EFF.T2.36` (CONDITIONALITY): *"Any proper-gcd key boundary uses T2.KEY-BOUNDARY"* (= E.21,
  landed as `key_boundary`); *"Raw and coherent coefficient arrays are not identified"*; *"Any
  HE3-dependent recentered-level-one history retains the HE3 grade cap."*
* `EFF.T2.37` (CONDITIONALITY): *"Per selected bouquet block; no whole-polynomial monicity or
  length transfer without proof; proper-gcd boundaries use T2.KEY-BOUNDARY"*, and the canonical
  fence *"The count-side mixed-multiplicity tie, partial-side budgets, and density laws are not
  conclusions of this σ-decision instance"* — those are chapter C/D objects.
* `EFF.T2.54`, GENTOW4's reading directive (a declination, not a consumption): clause 4.A(ii)'s
  parenthetical *"top coefficient NOT monic — the partial-side signature"* is **SUPERSEDED** by
  the 2026-08-10 TOWERRAT2-C dated correction, which governs. *"This master consumes from clause
  (ii) only `μ₂* = Σ_{λ₂>T₂} L_{λ₂}` and `deg f_S = D₂μ₂*`, never the top-coefficient
  parenthetical"*; S3.5 states the complementary restraint, *"No whole-polynomial monicity or
  length hypothesis is transferred to `f_S` without proof"*. The superseded parenthetical is
  NEVER consumed by any chapter-E node.

## The three `(SEC-RANK)` discharge bullets (`EFF.T2.52`), quoted at this row per the blueprint

`(SEC-RANK)` is a **named carrier hypothesis**, not a derived component: *"Component three is
**not** derived … Its instance status:"*

1. **Level one** (S3.1/S3.2): *"supplied inside the existing pin `HE3-A-PROOF`, whose §S6.3
   stage-α passage reads 'Termination: each refine strictly increases the floor λ and dv-heights
   are bounded by the leaf's window (GENHN-3(a)), so the chain is finite' — an **N**-valued
   instance of `(SEC-RANK)` (window bound minus current floor)."* (That is E.22's row, not this
   node's.)
2. **Level two at a DEFINITION HE6-1 key** (S3.3): *"supplied by **LEMMA HE7-8 ((REF-TERM))**,
   pinned as `HE7-REF-TERM` … the record's key is `Ψ_{λ,r}`, a DEFINITION HE6-1 member, so the
   lemma applies with no transfer. It discharges `(SEC-RANK)` in its well-foundedness form rather
   than by an **N**-valued rank … Accordingly `(SEC-RANK)` is stated above with `W_𝒞` merely
   well-founded, not **N**; an instance may discharge it either way."* — E.55's row.
3. **Level two at the composed key** (S3.4/S3.5): *"**not** supplied by instantiating HE7-8,
   whose hypothesis names the chain's base key … It is supplied instead by the clause of each
   record's own already-listed pin that states the conclusion at `Φ₂`: `HETOW-A` clause (ii) …
   and `GENTOW-4-A` clause (iii) … the transfer … is performed inside those theorems' proofs, by
   `HETOW-KEY-BRIDGE` and by `GENTOW-4-1` clause (c), and is not performed by this master."*

and the closing fence: *"No instance is claimed to discharge `(SEC-RANK)` by an argument this
master reproduces."* `EFF.T2.52`'s CONDITIONALITY adds: *"any instance that cannot supply it does
not instantiate HE7.A"* — it is a carrier hypothesis, not an open obligation, and *"fences no
read"*.

## Five reading notes the landed copy must carry

1. **Nothing in this table is discharged by chapter E.** Every row names a supplier, and the
   E-internal ones supply the SCHEMA half only — the arithmetic, the fold, the termination shape
   — never the carrier content. A fleet agent who finds a chapter-E node that appears to *prove*
   one of the C-PLACEHOLDER rows has found a defect, not a discharge. (E.22's reading note 1, at
   level two.)
2. **Three supplier signatures MOVED on 2026-08-16, after this table was written**, and the
   table's citation-by-node-ID survives all three, but the *strength* read must use the amended
   forms. Read the amendment before consuming the row:
   * **A-E.3** — E.36's `coprime_of_not_dvd` was FALSE over a bare domain; re-signed with
     `[IsIntegrallyClosed O]`, which every consumer gets free in the DVR arena (ENV-E2 derives it
     by instance search). The blueprint states explicitly that *"the instance rows E.22/E.23 are
     the same"* — i.e. this record instantiates in that arena, so **no row moves**.
   * **A-E.4** — E.29's `twisted_slot_spec` was FALSE at its committed `hatt` (the truncating
     `ℕ`-division rounded an OUT-OF-CLASS slot into the class ladder); re-signed at the ATTAINED
     VALUE, with the class location now a CONCLUSION (`attainer_in_class`). The blueprint's own
     consumer audit records this node's disposition verbatim: *"**E.23** (instance record,
     'SIGNATURE: none') cites E.29 as the `(SLOT₂)` schema over the level-1 carrier; a table row,
     no type to move."* The DAG edge `BP.E.23 → BP.E.29` is UNCHANGED.
   * **A-E.5** — E.55's `refine_chain_finite` was refuted TWICE at its committed type; re-signed
     with two SOURCE binders restored (`hkey : C.D ≤ Ψ.natDegree`, `hAdeg : ∀ j m,
     (A j m).natDegree < C.D`). The `(SEC-RANK)` row above therefore cites the A-E.5 contract,
     and an instance that cannot supply those two frame data does not supply the row.
3. **Honesty E-1's HE7-side residual rides every row whose supplier is an HE7 unit citing an HE6
   span** (HYP.150 is scoped to T2 only): those rows carry the flag
   `[HE6-A3-UNADJUDICATED FOR HE7]` and state content from HE7's own displays, never from HE6
   frozen text. In this table that is the HE6R1-2 and HE6R1-3 rows, and the corrected per-side
   scalar `γ_g·β^{c₁(m₁^{f_S}, c_g)}` is quoted with the twice-corrected form the ledger's
   dated corrections (`EFF.HE7.136`/`.137`) fix — the superseded scalars are NEVER consumed.
4. **`EFF.T2.38`'s grade cap rides through.** HE3 is consumed at attempt grade 0/2 (clean 1/2);
   every level-two chain consuming the level-one instance through S1.8C *"remains capped there"*.
   Recorded for chapter I's conditionality bookkeeping, **NOT as a Lean object**.
5. **E.23 routes no side condition for the σ-product node** (§12(a)7, executed at the 0e gate):
   the landed `typeOf_mul` has **monicity only** — no coprimality, no root-set disjointness — so
   the `hcond : True` slot stood for nothing and was dropped. *"There is nothing for the ladder's
   blocks to supply and E.23 routes no side condition for this node."* A future reader must not
   re-introduce one here.

**DEPENDS.** E.10–E.12, E.29, E.31, E.36–E.38, E.42, E.55–E.57; chapter-C placeholders as listed.
No Lean dependency: this file imports nothing, so the DEPENDS list is a documentation edge only
and E.57's BLOCKED status cannot leak into any build.

**SOURCE.** `EFF.T2.35` (HE7-INSTANCE, boxed); `.36` (HETOW-INSTANCE, boxed, incl. the frame
conversion `R_{λ₂}(Z) = τ(H₀)·R̂_{λ₂}(Z/δ)`, `δ = τ(u₃) ∈ K^×` — a `(FRAME)` instance,
σ-invariant per E.54, landed as `ladderSigma_frame_invariant`); `.37` (GENTOW4-INSTANCE);
`EFF.T2.52` (the three `(SEC-RANK)` discharge bullets, quoted above); `EFF.T2.54` (the GENTOW4
reading directive, quoted above); `EFF.T2.56` (the per-record Source-pin discipline this table
mirrors).

**TEETH.** live cocycle carry; mixed block; level-two peel; refine-chain termination; HETOW frame
gate; composed-key/C-A gate → dispositions distributed to the supplying nodes' TEETH fields; the
GENTOW4 perimeter row enters §13. This landed copy discharges no tooth.

## Status

No declarations, hence nothing to check: no `sorry`, no `axiom`, no import, and no axiom
footprint block (there is no name to print). The file elaborates as pure documentation.

The one mechanical check this landing DID execute is the fourth column of the obligation map: for
every E-internal supplier row, the cited node's signed declaration was located in `leanfinal` by
name (E.04 `cocycle_exp_mem`/`cocycle_carry`, E.08 `lift_threshold_step`, E.09 `useSite_margin`,
E.10 `SlotCarrier`, E.11 `BlockData`, E.12 `RungInterface`, E.14 `forced_sum_eq`, E.15
`ef_forcing`, E.16 `he7a_clause12`, E.21 `key_boundary`, E.29 `twisted_slot_spec`, E.31
`twisted_lift`, E.33 `coc_cocycle`, E.36 `coprime_of_not_dvd`, E.37 `peel_once`, E.38
`slot_fold`, E.42 `s18b_fold`, E.54 `ladderSigma_frame_invariant`, E.55 `refine_chain_finite`,
E.56 `same_digit_rises`) — **all present except E.57, which is BLOCKED**. That is a
declaration-existence check ONLY: it does not verify that any located declaration has the
strength its row needs. Three of them (E.29, E.36, E.55) reached their present form only through
amendments A-E.3/A-E.4/A-E.5 on the same day, so the strength reading is owed at chapter E's
freeze, not here.
-/
