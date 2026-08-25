# Verdict — unit RP23: S2-source plan nodes RP-2 (add-law remainder) + RP-3 (CORE 1/4)

Date: 2026-08-25 · Plan: `docs/in-progress/S2_SOURCE_PLAN_2026-08-24.md` §6, rows RP-2
("zero/add laws" — the zero law landed at RP-1; this unit lands the ADD remainder) and RP-3
("graded product endpoints", CORE 1/4 of `graded_mul`). File created (the ONLY repo file
touched): `leanfinal/Uniformity/ChapC/C130rp2.lean` (1211 lines, 48 public declarations + 6
private helpers; not added to `Uniformity/ChapC.lean` or any roll-up; probe kept at
`leanfinal/scratch/rp23_probe.lean`).

## RP-2 remainder (`graded_add`) — LANDED, in two strengths

★ `s2GradedRes_add_of_le` (STRONG): `R_β(g+h) = R_β(g) + R_β(h)` whenever BOTH inputs have
cleared value ≥ β (`(β:ℕ∞) ≤ dvSupp`, exact OR above) — NO hypothesis on the sum, so the
cancellation case (both summands on-line, sum priced above) is an instance, not an exclusion.
★ `s2GradedRes_add` (FIELD SHAPE): C130fg's `graded_add` binder pattern verbatim at S2 —
exact + exact + exact-sum (published Cor 4.12(1)); the exact-sum binder is carried for shape
fidelity only (the strong form shows it unneeded). Engine, all new and generic-frame:
`twistRead_add_of_le`/`slotRes_add_of_le` (ϖ-read additivity at a common height floor, via
B.22 `digAt_add` at the exact digit levels — the two-sided law whose `>` degenerations are
C131y's landed one-sided laws), `twistRead_zero`/`twistRead_eq_zero_of_lt` (an above-line
slot reads 0 through the SAME formula — why cancellation needs no case split),
`le_dvHgt_of_le_dvSupp` (the per-slot floor), and the bridge
`s2GradedCoeff_eq_twistRead_of_le` (gated coefficient = ϖ-read at the on-line height, on OR
above the gate). Teeth: `tooth_gradedRes_add_cancel` (`R₅(Φ′+Φ′) = 1+1` — cancellation genre,
`h₂(Φ′+Φ′) = h₂(C 2·Φ′) = 9 > 5` via `dvSupp_C_two = 4`); ★ `tooth_char_two` (`1+1 = 0` in
K₂ DERIVED from zero law + add law alone — the coherence check, reproducing C130s6's card-2
collapse at the operator level); and the NON-VACUOUS exact-sum instance
`tooth_gradedRes_add_exact`: `R₁₀(Φ′² + 4x) = X + 1 = R₁₀(Φ′²) + R₁₀(4x)` through the
FIELD-shape law itself (`tooth_C4X_grade`/`tooth_sum_exact`: `h₂(4x) = 10` with line slot at
abscissa 0, DISJOINT from Φ′²'s abscissa 2 — the one way exact-sum survives char 2).

## RP-3 (graded product endpoints, CORE 1/4) — LANDED

The chain RP-4 consumes, each stage a named public lemma:
1. ★ `dev_mul_endpoint_split` (GENERIC, exported from NV-3's internals): at the endpoint slot
   `jg+jz` (the chosen minimizers), `dev (g·z) = (dev g jg · dev z jz) %ₘ Φ′ + R` with EVERY
   other convolution term priced strictly above (`Hg+Hz+1 ≤ dv(R)`) — UNCONDITIONAL (NV-3's
   `hsurv` is only needed to read the split, not to have it).
2. The S2 read normal form: `s2_stageLetter_eq_one` (`η = 1` from `|K₁| = 2`, C.80 + C.19),
   `slotIdx_eq`/`twistExp_eq`/`slotWindow_eq` (`i(k) = k%2`, `q(k) = k/2`, window `{0}` at
   every k), ★ `s2_twistRead_eq_digAt`: EVERY S2 ϖ-read is one digit of one coefficient,
   `twistRead k A = digAt 2 (k/2) (A.coeff (k%2))` transported (RP-4's vocabulary).
3. ★ `s2_twistRead_mul_modByMonic` (the survival core at the RESIDUAL-READ level — the
   brief's "twistRead of the surviving term = product of the twistReads"): for deg ≤ 1 and
   height FLOORS `Ha ≤ dv(a)`, `Hb ≤ dv(b)`,
   `twistRead (Ha+Hb) ((a·b) %ₘ Φ′) = twistRead Ha a · twistRead Hb b` — C130nv3's four
   parity genres redone at the digit level; odd×odd is the genuine x²≡2 carry
   (`digAt (m+n+1) (2a₁b₁) = digAt m a₁ · digAt n b₁`).
4. ★ `s2_twistRead_dev_mul_endpoint` (1+2+3 through C131y's `twistRead_add_deep`): the
   endpoint read of `g·z` is the product of the factors' endpoint reads.
5. ★ **headline** `s2GradedCoeff_mul_endpoint`: at exact grades β, β′,
   `Rgc_{β+β′}(g·z)((jg+jz)/2) = Rgc_β(g)(jg/2) · Rgc_{β′}(z)(jz/2)` — with the parity CARRY
   visible in the y-power arithmetic `(jg+jz)/2 = jg/2 + jz/2 + (β%2)(β′%2)`. Plus the slot
   dictionary `s2SlotOnGrade_iff_dvOnSide` (at exact grade, the grade line IS C.07's side —
   RP-4's slot indexing). Teeth: `tooth_endpoint_mixed` ((2,5): `1 = 1·1`, no carry, via new
   `tooth_gradedRes_X` = eq (11) at s=0 and minimizer computations `dvSideMin_X = 0`,
   `dvSideMin_key = 1`) and `tooth_endpoint_carry` ((5,5): y-power `1 = 0+0+1` — the carry).

## ⚠ Recorded finding (machine-checked): plain-product `graded_mul` shape REFUTED at RP-1's operator

`tooth_graded_mul_plain_shape_refuted`: `R₁₀(Φ′·Φ′) = X ≠ 1 = R₅(Φ′)·R₅(Φ′)` (both sides
landed RP-1 teeth). C130fg's `graded_mul` field AS TYPED
(`gradedResidual (β+β′) (g·h) = gradedResidual β g * gradedResidual β′ h`) is therefore NOT
satisfiable by the RP-1 concrete operator: the grade-anchored Def 3.12 line offset
`s₂(β) = β%2` makes the product law carry `y^{(β%2)(β′%2)}` (two odd offsets merge into one
extra y). **Corrected S2 target for RP-4/RP-6**:
`R_{β+β′}(g·h) = X^{(β%2)·(β′%2)} · R_β(g) · R_{β′}(h)` — the headline is its endpoint
instance. Whether the published Cor 4.12(2) wording anchors per-polynomial (making the plain
form true THERE) is left as a cite-review question for CC-14/FD-0; the finding here is about
the C130fg field shape at the RP-1 operator, and it is machine-checked. (RP-6's assembly
row should either retype the field with the carry factor or route through the NORMALIZED
residual, where the strip absorbs it.)

## What was deliberately NOT claimed

No full `graded_mul` (RP-4 convolution over non-endpoint slots; RP-5 inner residual beyond
the f₁=1 monomial case; RP-6 assembly); no `graded_scalar_nonzero` (RP-7); no
`normalizedResidual` (RP-8); no `FGMNSourceData/Laws` instance (FD-0). The ϖ-read ↔
`ε(α)·R(a)(z)` dictionary stays on C.22/C.25's recorded faithfulness boundary. The S2 read
normal form and `η = 1` are S2-frame facts, not general-frame claims. Flagged for human
review (new general statements): `twistRead_add_of_le`, `twistRead_eq_zero_of_lt`,
`dev_mul_endpoint_split` (generic frames, strict admissibility as in NV-3).

## Verification

`cd leanfinal && lake env lean Uniformity/ChapC/C130rp2.lean` — CLEAN (exit 0, 0 errors, 0
warnings, 0 sorry). `lake build Uniformity.ChapC.C130rp2` — success (8742 jobs). 50
`#print axioms` rows, ALL `[propext, Classical.choice, Quot.sound]` (Lean-core only); no new
axiom, no `unsafe`, no statement touched, no other file modified (spec/ modifications in
`git status` pre-date this unit). No git commit (per brief).
