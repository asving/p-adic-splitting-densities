# C106 verdict — the §10 GENTOW2 supply manifest (NODE C.106)

**PARTIAL, honest: 7 of 10 signed `#check` rows landed; 3 recorded as open, not 2.**
Deliverable: `leanfinal/Uniformity/ChapC/C106m.lean` (new file, imports `C97`, `C98`, `C99r`,
`C102gt`, `C105`; no other file touched). `lake env lean Uniformity/ChapC/C106m.lean` exits 0,
zero stderr. No `sorry`, no new axiom, no `unsafe`, no statement weakening.

## Correction to the dispatch note

The brief named C.100/C.102 as "the two open rows." `rg` on all ten manifest names found a
**third**: `theta_letter_valued` — a second axiom bundled inside leanspec's NODE C.99 block
(`ChapC.lean:2483-2499`, "the γ-calculus companion"), distinct from `gentow2_Bpp`, and with no
leanfinal declaration anywhere. C.99's manifest row is only half-landed. Reported rather than
matched to the stated count.

## Per-row disposition (all ten, `rg`-verified)

| # | name | node | verdict | file / gap tag |
|---|---|---|---|---|
| 1 | `s2Witness` | C.97 | LANDED | `C97.lean`, `Uniformity.Density.Tower` |
| 2 | `shear_onesided_iff` | C.98 | LANDED | `C98.lean`, `Uniformity.Density.Tower` |
| 3 | `gentow2_Bpp` | C.99 | LANDED | `C99r.lean`, `...Tower.C99r` (A-C.12 re-sign) |
| 4 | `theta_letter_valued` | C.99 companion | **HOLD** | `OPEN-LETTERS` (γ-recursion/exponent-lattice dictionary absent) |
| 5 | `gentow2_Bp` | C.100 | **HOLD** | `OPEN-EVAL-ISO` (no field ties `ρ` to canonical eval map) |
| 6 | `gentow2_B` | C.101 | LANDED | `C99r.lean`, `...Tower.C99r` (A-C.12 re-sign) |
| 7 | `letter_formula` | C.102 | **HOLD** | `OPEN-EVAL-ISO` + `OPEN-LETTERS` |
| 8 | `gentow2_A` | C.103 | LANDED | `C99r.lean`, `...Tower.C99r` (A-C.12 re-sign) |
| 9 | `repoRead` | C.104 | LANDED | `C102gt.lean`, `Uniformity.Density.Tower` |
| 10 | `wconj_invariants` | C.105 | LANDED | `C105.lean`, `Uniformity.Density.Tower` |

The signed shape is an unconditional flat 10-line `#check` block, no partial-form provision;
checking all ten verbatim would fail to build (3 names are unknown identifiers in leanfinal,
not false statements). Landed the 7 real `#check`s; kept the 3 HOLD rows as commented-out
lines tagged with their audited gap, per the C.116 precedent for un-checkable manifest rows
(comment + name the reason, never delete the row).
