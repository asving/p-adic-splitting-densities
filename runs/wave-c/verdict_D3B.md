# Verdict D3B — the μ₄ operator stack's middle tranche: D3-05..D3-09

Date: 2026-08-28
Target: `leanfinal/Uniformity/ChapC/C136d1.lean` (new file; nothing else touched)

## ACCEPTANCE — STATUS FIRST

| row | status | exact result |
|---|---|---|
| **D3-05 valuation/grades** | **GREEN — UNCONDITIONAL** | `s2Hgt₄_one_eq_zero` (fresh `h1`-tooth) + `s2AddVal₄ : AddValuation (Polynomial O) (WithTop ℤ)` built DIRECTLY from `AddValuation.of` at D3-04's already-unconditional `s2Hgt₄_mul_all` — no nonemptiness-gap machinery needed (unlike `C132nv6` one level down). Plus the full `S2Mu4ExactGrade`/`S2Mu4AboveGrade` grade-predicate bank (iff-forms, existence/uniqueness, unconditional `_mul`, zero/⊤ edge cases, `AddValuation` tie, and the `tooth_g8 : S2Mu4ExactGrade 85 g8` numeral pin) — mirror of `C132rp0` wholesale. |
| **D3-06 grade-line/epsilon** | **GREEN** | `S2Mu4SlotOnGrade β g s := 2·μ₃(A_s) + 85·s = β` (the μ₄ gate) at gate numerals `(e₄,h₄)=(2,85)`, plus Def 3.12's line arithmetic at `i=4` (`s2Mu4_def312_level4`) and `i=3` (`s2Mu4_def312_level3`, ε-data, Bézout pair `(1,-10)` — `s2Mu4_bezout_level3`), the iff/parity/inner-exact/support-bound bank, and the ε-exponent/collapse (`s2Mu4EpsExp`, `s2Mu4EpsOf_eq_one`) REUSING `C132rp1.s2Fld₂_eq_one_of_ne_zero`/`s2Mu3_eval_letter_pinned` directly (field-generic facts, not level-specific — no re-derivation). |
| **D3-07 recursive coefficient** | **GREEN** | `s2Mu4Coeff` reads the landed μ₃-level GRADED operator `s2Mu3GradedRes` (`C132rp2`) at the on-line inner grade; `s2Mu4Coeff_letter_display`, `s2Mu4Coeff_eq_eval`, and the graded/normalized collapse `s2Mu4Coeff_eq_eval_normRes` (reading `C132rp8.s2Mu3NormRes` instead) all land, plus the four finite-support/above-grade zero laws and `s2Mu4Coeff_slot`. |
| **D3-08 total graded operator/add** | **GREEN** | `s2Mu4GradedRes` assembly + master coefficient law + range independence + finite support (packaged and raw) + zero-above + zero tooth (mirror of `C132rp2`), PLUS the exact-grade additivity engine: `le_dv3Pin_of_le_dv3Supp` (built directly off the ALREADY-LANDED `C136d0.dv3Supp_le_term`, unlike `C132rp3`'s private re-derivation one level down), `s2Mu4Coeff_eq_eval_of_le`, `s2Mu4Coeff_add`, `s2Mu4GradedRes_add_of_le`, and the `FGMNSourceLaws.graded_add`-shaped `s2Mu4GradedRes_add` (mirror of `C132rp3`). |
| **D3-09 carry arithmetic** | **GREEN — numeral-only** | `s2Mu4Carry`/`s2Mu4Carry_eq_zero_or_one`/`s2Mu4Carry_parity` (the `h`-independent `e=2` carry identity, reproved standalone per the corpus's private-copy convention), `s2Mu4_abscissa_sum`, the gate-level `s2Mu4SlotOnGrade_abscissa_sum` (building on D3-06's `s2Mu4SlotOnGrade_parity`), and `s2Mu4_def312_add` (REUSING D3-06's `s2Mu4_def312_level4` twice, at `h₄=85`). |

## What lands (all Lean-core, all sorry-free)

56 new declarations across the five rows, listed in the file's own AxCheck footer. Every
`def`/`theorem` is the exact one-level-up mirror of a landed μ₃-campaign declaration
(`C132rp0`/`C132rp1`/`C132rp2`/`C132rp3`/`C132rp4`), substituting: inner key `Φ₂ ↦ g8`;
outer side `(u₃,ℓ₃)=(21,2) ↦ (u₄,ℓ₄)=(85,2)`; ε-data numerals `(e₂,h₂)=(2,5) ↦
(e₃,h₃)=(2,21)` (Bézout pair `(1,-2) ↦ (1,-10)`); inner graded/normalized read
`s2GradedRes`/`s2NormRes` (μ₂-level, `C130rp1`/`C130rp8`) ↦ the landed μ₃-level
`s2Mu3GradedRes`/`s2Mu3NormRes` (`C132rp2`/`C132rp8`). The residue-field codomain stays
`(s2DepthTwo h2 hq).fld 2` throughout every row — checked explicitly in the file docstring:
`s2Fld₂_card`'s own proof is `C80.card_K₁ h2 hq` regardless of the index, confirming
`.fld i` is definitionally the same type at every `i` in S2's constant residue tower, so no
field-index bump was needed anywhere in the port.

Two genuine (small) departures from a byte-for-byte port, both flagged in the file
docstring:
* D3-05 needed NO nonemptiness-gap-closing machinery (`C132nv6`'s Parts 1–2, one level
  down) because D3-04 (`C136d3ad.s2Hgt₄_mul_all`) already landed the fully unconditional
  `hmul` shape — `s2AddVal₄` is a direct `AddValuation.of` application, not a conditional
  wrapper.
* D3-08's floor bridge cites the ALREADY-LANDED `C136d0.dv3Supp_le_term` (D3-02) directly,
  rather than re-deriving a private S2-specialized copy the way `C132rp3` had to one level
  down (no such generic lemma was landed at the μ₂→μ₃ layer at the time).

## What this unit does NOT claim (honesty scope)

No multiplicativity/convolution (D3-10, superseded by the [DWR] §11.7 L2E shared engine),
no normalization of the μ₄ operator (D3-11/D3-12), no `FGMNSourceData`/`FGMNSourceLaws`
record (D3-18/19). The OPEN-RP1-TRANSPORT faithfulness split (the landed μ₃-level read's
own paper fidelity) is exactly as `C132rp1`/`C132rp2`/`C132rp8` left it — inherited as a
citation, never re-derived or re-opened. Part-4 "computation teeth" at concrete landed
numerals (the μ₃ campaign's `C132rp1` Part 4 genre) are NOT reproduced: no row in this
unit's scope consumes them.

## Verification and footprint

Required command, run after the skeleton and after each fill increment:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C136d1.lean
```

Final exit status: `0`; zero errors, zero warnings, zero `sorry`. The AxCheck footer prints
all 56 public declarations at exactly `[propext, Classical.choice, Quot.sound]` (Lean core)
or with NO axioms at all (`s2Mu4EpsExp`, `s2Mu4Carry` — pure numeral/`ℤ` definitions). No
landed or leanspec file was edited (`git status`: the new file is the unit's only
footprint). No git operation was run.

Repair log: 2 issues total across the whole unit, both on the FIRST full-file compile —
(1) a missing `open Uniformity.Density.Tower.C80` (the source of `s2Tower`, not re-exported
by `C130s2`; every model file the unit ports from opens it explicitly, this file's initial
open list omitted it); (2) one `linter.unusedVariables` warning on `s2Mu4GradedRes_add`'s
carried-for-shape-fidelity `hgh` hypothesis, silenced with the SAME `set_option` the model
file (`C132rp3.s2Mu3GradedRes_add`) already carries. No proof-content repair was needed —
every mirrored tactic block matched its model verbatim (mod the numeral/name substitutions
above).

## Trust boundary

New statement shapes flagged for human review (every `def` introducing a new predicate/
operator, and the fresh numeral pins): `S2Mu4ExactGrade`, `S2Mu4AboveGrade`,
`S2Mu4SlotOnGrade`, `s2Mu4EpsExp`, `s2Mu4EpsOf`, `s2Mu4Eps`, `s2Mu4Coeff`,
`s2Mu4GradedRes`, `s2Mu4Carry`, `tooth_g8`, `s2Mu4_bezout_level3`, `s2Mu4_def312_add`, and
`s2AddVal₄`'s built-in `AddValuation.of` application (the four-field `f0/f1/hadd/hmul`
supply, all cited from D3-04/D3-05's own landed facts, no fresh assumption).
