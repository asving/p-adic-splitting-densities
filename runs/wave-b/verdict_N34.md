# Verdict: DEC1-N3 + DEC1-N4 (GC-13 bridge plan, wave-2 sequential pair)

**Plan:** `docs/in-progress/GC13_BRIDGE_PLAN_2026-08-25.md` §3, nodes `DEC1-N3` (ledger +
product + disjointness field-group) and `DEC1-N4` (degree + purity + threshold
field-group), both at the SPLIT row (`F = X² − 1 = (X + 1)(X − 1)`, one side `(1,1)`, two
unit-weight linear classes labeled `1`, `−1`). Per the wave-2 dispatch note
("N3 → N4 (E57i.lean, sequential, may be one agent)"), both nodes were executed by one
unit into the shared file.

**File delivered:** `leanfinal/Uniformity/ChapE/E57i.lean` (new; imports the landed
wave-1 files `E57i1.lean` (`mixBlock`/`mixIface`) and `E57i2.lean`
(`pureBlock₂`/`pureIface₂`), plus `E57p.lean` transitively for
`E57pCert.pureBlock`/`pureIface`, `PartitionLeg`, `ClassIx`, `classWeight`). N5 (assembly +
firing, a separate node/agent) is expected to append a further section to this same file —
nothing here forecloses that.

## DEC1-N3 — ledger + product + disjointness

**Contents (namespace `Uniformity.Density.Ladder.E57iCert`):**
* `a1 : ClassIx ℚ`, `a2 : ClassIx ℚ` — the split row's two class addresses (side `(1,1)`,
  labels `1` and `−1`), and `splitCls : Finset (ClassIx ℚ) := {a1, a2}`, matching the
  plan's row data verbatim.
* `a1_ne_a2 : a1 ≠ a2` — `simp [a1, a2]` then `norm_num` on the residual `¬(1:ℚ) = -1`.
* `splitBlk : ClassIx ℚ → Σ B', RungInterface … B'` — `a1 ↦ ⟨E57pCert.pureBlock,
  E57pCert.pureIface⟩` (the landed label-`1` child, reused, not rebuilt), everything else
  (i.e. `a2`) `↦ ⟨pureBlock₂, pureIface₂⟩` (N2's label-`−1` child), plus two `@[simp]`
  unfolding lemmas `splitBlk_a1`/`splitBlk_a2` (the `if`-branches, `if_neg` needing
  `a1_ne_a2`).
* `split_N3` — a single theorem bundling all four `N3_spec` conjuncts
  (`hclsLin`/`hclsHi`/`hprod`/`hdisj`), stated with the plan's names substituted
  (`I → mixIface`, `cls → splitCls`, `blk → splitBlk`, `B → mixBlock`) **byte-verbatim**
  against `scratch/DEC1_check.lean:66–71`'s `N3_spec` body (checked by direct comparison,
  not just claimed).
  * `hclsLin`/`hclsHi`: case-bashed via `simp only` on `splitCls`/`a1`/`a2`/`mixIface` plus
    `Finset.mem_insert`, `Multiset.insert_eq_cons`/`mem_cons`/`mem_singleton`,
    `Prod.mk.injEq`, `Sum.inl.injEq`, `and_or_left` (the `hclsLin` iff normalizes to the
    same disjunctive normal form on both sides and closes by `simp only` alone; `hclsHi`
    is vacuous on both sides, closed by plain `simp`).
  * `hprod`: `Finset.prod_pair a1_ne_a2` + `splitBlk_a1`/`_a2` exposes
    `(X+1)*(X-1)`, closed against `mixBlock.F = X^2-1` by `ring`.
  * `hdisj`: reduced to the single unordered pair via `rcases … <;> rcases …` (4 cases,
    2 trivial `absurd rfl hne`, 2 symmetric); the live case is
    `IsCoprime ((X+1).map (algebraMap ℤ (FractionRing ℤ))) ((X-1).map …)`, witnessed by
    Bézout coefficients `C ((2:FractionRing ℤ)⁻¹)` / `-C ((2:FractionRing ℤ)⁻¹)`
    (`c·(X+1) − c·(X−1) = 2c`, then `← Polynomial.C_add`, `2·c⁻¹-cancel` via
    `mul_inv_cancel₀`, `Polynomial.C_1`). **Deviation from the plan's sketched witness**
    (`⟨C(2⁻¹), -C(2⁻¹), …⟩` closed by `ring`+`push_cast`): the plan's suggested
    `field_simp`/direct-`ring`-through-`C` route does not typecheck as sketched (`ring`
    treats `Polynomial.C` as an opaque atom and cannot push a numeral through it, and
    `field_simp` is not in scope without an explicit import); the working route needed
    `import Mathlib.Algebra.CharP.Algebra` for `CharZero (FractionRing ℤ)` (via
    `IsFractionRing.charZero`, giving `(2 : FractionRing ℤ) ≠ 0` by `norm_num`) plus an
    explicit `Polynomial.C_add`/`C_1` rewrite instead of relying on `ring` to cross the
    homomorphism. Mechanism (Bézout witness, the pair `(1, -1, 2)`) is exactly as the plan
    specified; only the closing tactic sequence differs.

## DEC1-N4 — degree + purity + threshold

**Contents (same namespace, same file, appended after N3):**
* `natDegree_X_sub_one : (X - 1 : Polynomial ℤ).natDegree = 1` — a small helper not named
  in the plan's node list but needed for `hdeg`'s second case (`X - 1 = X + C(-1)` then
  `natDegree_X_add_C`), proved exactly per the plan's hint.
* `split_N4` — a single theorem bundling all five `N4_spec` conjuncts
  (`hdeg`/`hone`/`hpureLin`/`hpureHi`/`hthr`), stated **byte-verbatim** against
  `scratch/DEC1_check.lean:81–89`'s `N4_spec` body under the same name substitution.
  * `hdeg`: two cases (`a1`/`a2`), `(X+1).natDegree = 1` / `(X-1).natDegree = 1` (via
    `natDegree_X_add_C`/`natDegree_X_sub_one`) against `classWeight mixIface a_i =
    mixIface.classCount (1,1) (±1,1) = 1` (`simp [mixIface]`).
  * `hone`: two cases, `pureIface.sides = {a1.1}` / `pureIface₂.sides = {a2.1}`, both
    `simp [pureIface/₂, a1/a2]` (both reduce to `{(1,1)} = {(1,1)}`).
  * `hpureLin`: two cases via `Prod.mk.injEq`/`Sum.inl.injEq` case-split on membership,
    `k := 1` per the plan, `linFac`/`hiFac` read off `pureIface`/`pureIface₂` by `simp`.
  * `hpureHi`: vacuous — `(p, Sum.inr q) ∈ splitCls` is impossible (no `Sum.inr` address
    in the ledger); closed by `rcases … <;> (exfalso; simp at hq)` (plain `simp`
    discriminates the `Sum.inl`/`Sum.inr` constructor mismatch — no need to name `a1`/`a2`
    in that inner call, since they were already substituted by the outer `simp only`).
  * `hthr`: two cases, both `rfl` (`T = 0` on `mixBlock`, `pureBlock`, `pureBlock₂` alike).

## Build

From `leanfinal/`:

```text
lake env lean Uniformity/ChapE/E57i.lean
lake build Uniformity.ChapE.E57i
```

Both exit 0. Zero `sorry`, zero new `axiom`, zero `unsafe`. Only the pre-existing
repo-wide `linter.style.show` hints fire (the same "use `change` instead of `show`" style
note that `E57p.lean` itself carries throughout — not silenced there, not silenced here,
no error). `#print axioms`:

```
'Uniformity.Density.Ladder.E57iCert.splitCls' depends on axioms: [propext, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.splitBlk' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.split_N3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Ladder.E57iCert.split_N4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lean-core only, as required. (`splitCls` doesn't need `Classical.choice` — a `Finset`
literal over a decidable-equality carrier — the others do, inherited from the underlying
`noncomputable`/classical instances on `RungInterface`/`BlockData`.)

## Statement fence / scope discipline

Only `leanfinal/Uniformity/ChapE/E57i.lean` written (new file), plus this verdict. No
edits to `E57p.lean`, `E57i1.lean`, `E57i2.lean`, `leanspec/`, roll-ups, or any other
unit's files. No C.63/C.69 clause consumed — level (a) (shadow-instance bridge) needs none;
all row data is direct polynomial computation over the landed flat carrier. No `git`
operations performed (per instructions — no commit).

## Status

DEC1-N3 and DEC1-N4 COMPLETE, landed in one file per the wave-2 dispatch note. Ready for
DEC1-N5 (assembly + firing `block_split_of_partitionLeg` at the split row) to append to
`E57i.lean`, consuming `split_N3`/`split_N4`'s four+five conjuncts by projection
(`split_N3.1`, `.2.1`, `.2.2.1`, `.2.2.2`; `split_N4.1`, `.2.1`, `.2.2.1`, `.2.2.2.1`,
`.2.2.2.2`) exactly as the plan's `legOfSpecs` anonymous-constructor route prescribes.
