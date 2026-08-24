# Unit CC08 verdict — chain-carrier node CC-8 (the realized input block)

## Verdict: LANDED

One new file, `leanfinal/Uniformity/ChapC/C130in.lean` (imports C130fg, C130th, E11, B05/B06,
HenselFactorization).  Sorry-free; no new axiom; no `unsafe`; no `True` body; **no numeral and
no threshold formula** — the block's `T` is a projection of the inherited `thresholdNat`
(CC-7's dictionary).  This is the carrier-level cure of freeze-v2 layer C.130e (BLOCKED at
C130A, recorded in `C130d.lean`): its three named missing carriers — C.130c `stageCarrier`,
C.130b `stageKey`, the source-pinned threshold — are now consumed from CC-5, `ArisingCore`,
and CC-7 respectively.  No block is stored in any carrier; nothing here inhabits
`NodePointSource`/`ChainRealization`/`RealizedInput`.

## Declarations

Generic development supply (namespace `Uniformity.Density.Leaf`, B.02/B.05/B.06 companions):

* `natDegree_dev_lt` — B.03's degree bound in `natDegree` form
* `dev_top_eq_one` — the top `dev` coefficient of a monic `F` of exact degree `μ·deg Φ` is `1`
  (via B.06 `dev_unique` on the family `1`-at-`μ` / `dev Φ (F − Φ^μ)` below)
* `sum_dev_eq_monic_top` — `(DEV)`: `F = Φ^μ + Σ_{j<μ} dev Φ F j · Φ^j` (EFF.W12.23/EFF.T2.11)
* `dev_zero_ne_zero_of_isCoprime` — ★ the GENERIC `A₀ ≠ 0` lemma: `(KEY-FREE)` (E.11's
  `IsCoprime`-over-`FractionRing` spelling) implies `dev Φ F 0 ≠ 0` — EFF.T2.11's own
  derivation, proved, never assumed

Namespace `Uniformity.Density.Tower`:

* `ArisingCore.F₀_natDegree` — `deg F₀ = μ · deg stageKey` (core's own ledger)
* `RealizedInput` — ★ the CC-8 record, fields BYTE-IDENTICAL to the elaboration authority
  `scratch/U11_carrier_check.lean`: three repository dictionaries (`receiver_eq`,
  `stageKey_eq`, `stageDeg_eq`) + the selected legal point (`point`, `point_mem`); no
  `SlotCarrier`, `BlockData`, socket, or consumer conclusion
* `RealizedInput.stageKey_natDegree` / `.stageKey_natDegree_pos` — the realized degree
  dictionary; positivity is NOT an `ArisingCore` field (it needs `stageDeg_eq` + `Dcum_pos`),
  which is exactly why the block exists only at a `RealizedInput`
* `RealizedInput.F₀_dev` / `.F₀_dev_zero_ne_zero` — `(DEV)` and `A₀ ≠ 0` in core vocabulary
* `RealizedInput.CanonicalThresholdAt` + `canonicalThresholdAt_def` — design §5's realized
  predicate as the DEFINITIONAL specialization of C130th's carrier predicate at
  `(A.node, core.i, X.point)`; the pin is `Iff.rfl`, byte-for-byte §5's display
* `RealizedInput.inputBlock` — ★ the producing theorem: every realized input yields E.11's
  `Ladder.BlockData` over CC-5's `stageCarrier core.i core.hi`.  Provenance per design §8 row
  C.130e: `Φ/F/μ` + laws from `core`; `A j = dev Φ F₀ j` below `μ`, `0` above (E.11's
  convention enforced); `hdev` = monic-top identity; `hkeyfree` = `core.keyfree` VERBATIM;
  `hA0` = the generic lemma; `T` = inherited `A.node.thresholdNat core.i`
* anti-drift pins (all `rfl`): `inputBlock_Φ`, `inputBlock_F`, `inputBlock_μ`, `inputBlock_T`,
  plus dictionary pin `inputBlock_Φ_eq_keyAt` (`stageKey_eq`)
* **the four views** (row CC-8's exit condition):
  1. development — `inputBlock_dev`, `inputBlock_A_eq_dev`, `inputBlock_A_of_le`
  2. key-free — `inputBlock_keyfree`, `inputBlock_keyfree_core`, `inputBlock_keyfree_keyAt`
  3. `A₀` — `inputBlock_A0_ne_zero`, `inputBlock_A0_eq_dev`
  4. threshold — `inputBlock_canonicalThreshold` (the block's `T` IS canonical at the realized
     occurrence), `canonicalThresholdAt_iff_inputBlock` (rigidity: nothing else is),
     `inputBlock_window` (`(WINDOW)` at the block's OWN key, through `stageKey_eq`)

## Verification

Run from `leanfinal/`:

```text
lake env lean Uniformity/ChapC/C130in.lean    # exit 0, zero errors/warnings
lake build Uniformity.ChapC.C130in            # completed, 8637 jobs
```

`#print axioms` (in-file) for all 29 new declarations prints exactly
`[propext, Classical.choice, Quot.sound]` — Lean core only.  Anti-drift diff of
`RealizedInput`'s binders/fields against `scratch/U11_carrier_check.lean`: identical (the
`Kt/L` binders arrive as section variables; same elaborated type).

## Notes for downstream nodes

* CC-12's `BlockViewEq` can quantify over `RealizedInput` and read `inputBlock`; CC-17's full
  S2 instance must supply the two carrier records before any `RealizedInput` exists.
* The E.11 convention "`A j = 0` for `j ≥ μ`" is enforced (field value, `inputBlock_A_of_le`),
  not left informal.
* No other file touched; nothing committed.
