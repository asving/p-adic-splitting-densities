# Verdict — unit C131ae (Chapter C, NODES C.131ae′–af′)

Deliverable: `leanfinal/Uniformity/ChapC/C131ae.lean` (only new file written by this unit).

## C.131ae′ (`mem_towerLocus_of_budget`, C.52 Step 2, `EFF.GENTOW1.21`) — **LANDED**

Statement (byte-identical to the C52_OPEN_2026-08-18.lean.txt draft / the `TowerBudgetIff`
direction named in `C53.lean`): budget floors on every two-key development digit of `f`
imply `f ∈ towerLocus T μ₂`.

Proved in full, no `sorry`, no statement weakening. The proof required building a genuinely
new mechanism the 2026-08-18/08-20 records (`C52_BLOCKED_2026-08-18.md`, `C53.lean`'s
`TowerBudgetIff`) both flagged as absent: an ADDITIVE perturbation-stability law for
`IsDvPure`/`dvResPoly` at the `dv`-carrier (chapter B has this for `suppVal`/`gaussVal`/
`resMk` — B32a/B32b/B35a — but chapter C never turned that crank at the `dv`-carrier). The
route taken is lighter than replicating B41a's `pure_add_of_lt` (which would need an
unlanded dv-level `sideMin_of_pure`/`height_eq_of_pure`/`resPoly_coeff_of_pure` cluster):

* an ultrametric **equality-off-ties** law for `suppVal`/`stageHeight`/`dvHgt`, proved from
  the already-landed inequality (B32b's `min_suppVal_le_suppVal_add`) plus a
  negation-invariance lemma (`addVal_neg`, `suppVal_neg`);
* a **slot-read invariance** law: `KeyFrame.slotRes`/`KeyFrame.twistRead` at height `k` are
  unchanged by adding a polynomial of `stageHeight` strictly above `k` — the ADD analogue of
  C.26's *private* `slotRes_eq_zero_of_lt`, independently re-derived here from public
  primitives (`KeyFrame.slotRes`, `C109asm.digAt_congr`) since the private original is not
  importable;
* a two-variable-lift bridge (`Qg`) turning `hbud`'s per-digit floor into a `DvAbove` floor
  of `μ₂E₂+1` on `g := f − Φ₂^{μ₂}`, via C.131ad's `dev_coeff_floor` and C.131u's
  `dvAbove_of_forall_coeff_floor`;
* the exact value `dvSupp(Φ₂^{μ₂}) = μ₂E₂` (read off the top digit via `dev_top_eq_one`,
  C.131v — no need for the general `IsTestKey` height formula);
* a uniform tie-break argument identifying `f`'s side set with `Φ₂^{μ₂}`'s exactly (every
  abscissa, not just the two purity endpoints), which is what let this stay a single
  self-contained file instead of a second B41a-sized development.

**Declarations proved** (all in `Uniformity.Density.Tower.C131ae` unless noted):
`addVal_neg`, `gaussVal_neg`, `dev_neg_of_monic`, `suppVal_neg`,
`suppVal_add_eq_left_of_lt`, `stageHeight_add_eq_left_of_lt`, `dvHgt_add_eq_left_of_lt`,
`dvHgt_add_ge`, `dv_term_add_ge`, `stageHeight_one`, `slotRes_add_eq_left_of_lt`,
`twistRead_add_eq_left_of_lt`, `qgInner`/`Qg` (defs), `eval_qgInner`, `eval_qgInner_eq`,
`eval_Qg`, `le_WT_Qg`, `dvAbove_g`, plus private helpers (`addVal_neg_one`, `dev_zero_any`,
`digAt_index_spec`, `gaussVal_C`, `dvd_of_le_addVal`, `addVal_coeff_of_stageHeight_lt`,
`natDegree_dev_lt'`, `budgetFloor_wtCoeff_bound`, `composedKey_natDegree_pos`) — and the
NODE itself, `Uniformity.Density.Tower.mem_towerLocus_of_budget`.

**Axiom footprint** (machine-checked, see the file's AxCheck footer):
* every declaration EXCEPT `mem_towerLocus_of_budget` — Lean-core only:
  `[propext, Classical.choice, Quot.sound]`.
* `mem_towerLocus_of_budget` — Lean-core **plus** `Uniformity.Density.Tower.fgmn_dv_exact_mul`
  (the DECLARED gate-(b) cite, C66b). This is inherited by design: the node's ONLY use of
  the exact half is `composedKey_pow_mem_towerLocus` (C.131ac), which itself carries the
  cite. `le_WT_Qg`/`dvAbove_g` (the `hbud`-only half) do NOT carry it, confirming the cite
  enters exactly once, exactly where the blueprint says it must (Step 1, not Step 0).

## C.131af′ (`budget_of_mem_towerLocus`, C.52 Step 3, `EFF.GENTOW1.22`) — **BLOCKED**

Not attempted beyond design. No `sorry`, no axiom, no statement weakening: the declaration
is simply absent from the landed file.

**Precise missing object.** The direction needed is the REVERSE of C.131ae′: given
`f ∈ towerLocus T μ₂` (an assertion about `f`'s OWN single-key `F.key`-adic side data), derive
a floor on `f`'s TWO-KEY (`composedKey T`-then-`F.key`) development digit
`(dev F.key (dev (composedKey T) f j) b).coeff a` for every `j < μ₂`. This needs a genuine
digit CORRESPONDENCE between the flat `F.key`-adic index and the double
`(composedKey, F.key)`-indexed coordinate — exactly the "triangular/unipotent digit
dictionary" `C53.lean` isolates as `TriangularDigitRead`, at the level of a single scalar
digit rather than a counted class. `C53.lean`'s own header names this as obstruction 4 of
`C52_BLOCKED_2026-08-18.md`, still unfilled; the v2 engine doc explicitly instructs
**not** to use C.53b's measure-preserving transport for this (it is a counting statement,
not a pointwise one). The only apparatus in the repo that performs a comparable digit
correspondence is C.131v's shadow/census identification (`shadowDev`,
`taggedOuterNF`, `censusOverflow`, `shadow_discrepancy`) — built for a DIFFERENT direction
(identifying a shadow read with an honest one at a FIXED `f`, not recovering `f`'s own raw
digits from side data) and consumed by the separately in-flight `C.131w′`
(`shadow_floor`, `C131w.lean`). Reusing or adapting that apparatus for C.131af′ is a second
undertaking of comparable size to the one completed above for C.131ae′; nothing already
landed supplies it.

## Verification

```sh
cd leanfinal
lake env lean Uniformity/ChapC/C131ae.lean   # 0 errors, 7 style/deprecation warnings, exit 0
lake build Uniformity.ChapC.C131ae           # builds green, AxCheck footer printed
```

No file other than `leanfinal/Uniformity/ChapC/C131ae.lean` was created or modified by this
unit.
