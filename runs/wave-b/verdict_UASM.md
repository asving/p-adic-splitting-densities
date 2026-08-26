# verdict_UASM — af′ reverse plan, unit U-ASSEMBLE

**Node:** AF-6a / AF-6b (`docs/in-progress/AF_REVERSE_PLAN_2026-08-25.md` §3, unit
U-ASSEMBLE), i.e. NODE C.131af′ (`budget_of_mem_towerLocus`) and NODE C.131ag′
(`towerLocus_iff_budget`, the byte-mirror of leanspec `ChapC.lean:2030`'s signed
`axiom towerLocus_iff_budget`).
**File:** `leanfinal/Uniformity/ChapC/C131ag.lean` (extended, stage 2 — added
`import Uniformity.ChapC.C131af` plus the two root-namespace theorems; U-ARITH's stage-1
`AF-5a`/`AF-5b` untouched).
**Build:** `cd leanfinal && lake env lean Uniformity/ChapC/C131ag.lean` — exit 0, zero
errors, zero `sorry`, zero new `axiom`. `lake build Uniformity.ChapC.C131af
Uniformity.ChapC.C131ag` — 8744/8744 jobs, green (the only warnings are the three
pre-existing `show`-vs-`change` linter notes from U-SIDE's stage-1 code in `C131af.lean`,
already reported in `verdict_UHEART.md`; nothing new from this unit).

## Delivered

* `Uniformity.Density.Tower.budget_of_mem_towerLocus` (AF-6a, ★ NODE C.131af′): for
  `f ∈ towerLocus T μ₂` and `j < μ₂` (with unused range binders `ha : a < F.e₁*F.f₁`,
  `hb : b < T.e₂*T.f₂` kept to match the signed shape, silenced via
  `set_option linter.unusedVariables false in`), `budgetFloor T μ₂ j a b ≤
  addVal O ((dev F.key (dev (composedKey T) f j) b).coeff a)`. Proof: U-HEART's AF-4
  (`towerLocus_dev_strict_floor`) gives the strict `dv2Hgt` floor on `dev Φ₂ f j`;
  flattened via `C131t.dv2Hgt_eq_WT_phiNF` (level-two height = two-index weight of `xNF`),
  `C131a.WT_le_wtCoeff` (weight ≤ any selected coefficient's `wtCoeff`), and
  `C131k.xNF_coeff` + `xDigit_eq_dev` (the `xNF` coefficient at `b` is exactly
  `dev F.key (dev (composedKey T) f j) b`); the resulting `wtCoeff` floor is converted to
  the `budgetFloor`-vs-`addVal` shape by U-ARITH's AF-5b
  (`budgetFloor_le_addVal_of_wtCoeff`). Compiled first attempt, no repair needed.
* `Uniformity.Density.Tower.towerLocus_iff_budget` (AF-6b, ★ NODE C.131ag′): the iff,
  `⟨fun hmem j a b hj ha hb => budget_of_mem_towerLocus T hπ hh hμ₂ hmem j a b hj ha hb,
  fun hbud => mem_towerLocus_of_budget T hπ hh hμ₂ hf hdeg hbud⟩` — assembled directly from
  AF-6a (→) and the already-landed `Uniformity.Density.Tower.mem_towerLocus_of_budget`
  (C131ae.lean, ←; untouched, called as-is). No new proof content.

Both signatures checked byte-for-byte against `leanfinal/scratch/DEC2_check.lean`'s
`SIG_AF6a`/`SIG_AF6b` (mod. the `∀`-vs-explicit-binder / `def Prop`-vs-`theorem` wrapper
difference already present for AF-5a/AF-5b), and `towerLocus_iff_budget`'s statement is
byte-identical to leanspec `ChapC.lean` NODE C.52 (line 2030) modulo `axiom → theorem` and
namespace (no `LeanspecC` wrapper here; binders, hypothesis order, and the RHS `∀ j a b ...`
clause are unchanged).

## Cite inheritance per declaration

* `AF-5a`, `AF-5b` (U-ARITH, unchanged this unit): Lean-core only (`propext,
  Classical.choice, Quot.sound`; `AF-5a` even drops `Classical.choice`).
* `budget_of_mem_towerLocus` (AF-6a): Lean-core + `fgmn_dv_exact_mul` — inherited from AF-4
  (`towerLocus_dev_strict_floor`, U-HEART), which inherits it from AF-3
  (`dvSupp_sub_composedKey_pow`), which consumes the declared cite `fgmn_dv_exact_mul`
  (C66b, allowlist member 7) exactly once, through `composedKey_pow_mem_towerLocus`
  (C.131ac′). AF-6a does not call the cite-bearing chain a second time; the flattening
  chain (`dv2Hgt_eq_WT_phiNF`, `WT_le_wtCoeff`, `xNF_coeff`, `xDigit_eq_dev`, AF-5b) is all
  Lean-core.
* `towerLocus_iff_budget` (AF-6b): Lean-core + `fgmn_dv_exact_mul` — the forward branch
  carries it (via AF-6a, as above); the reverse branch
  (`mem_towerLocus_of_budget`) is Lean-core only per `verdict_C131ae.md`'s own footprint, so
  the iff's footprint is exactly the union: `[propext, Classical.choice, Quot.sound,
  fgmn_dv_exact_mul]`, confirmed by `#print axioms` in-file.

No new axiom anywhere; the single non-core dependency is the already-declared, faithfulness-
reviewed C66b cite (`docs/AXIOM_FAITHFULNESS.md`), not freshly consumed by this unit — it
was already landed in `C131af.lean` by U-HEART.

## Deviations from the plan

None. The chain assembled exactly per §2/§3's route script on the first compile attempt;
no repair rounds were needed for either theorem.

## Scope discipline

Only `leanfinal/Uniformity/ChapC/C131ag.lean` (U-ARITH/U-ASSEMBLE's plan-assigned file,
extended per the plan's stage-2 assignment) and this verdict were written. Did not touch
`leanspec/`, `C131af.lean` (U-SIDE/U-HEART's file, read-only here), any roll-up, or any
PK12-owned file (`C130fg`/`pk`/`s17`/`s18`/`vw`). No `git commit` taken. U-FEED
(`C123r2.lean`, feeding C123R's band-budget gap per the plan's §4) is next in the plan's
sequencing and is NOT started here.
