# Unit AC14 verdict — amendment A-C.14 enacted (the GENTOW5 supply-hypothesis cascade) + landings

Date: 2026-08-25. Authority: delegated enactment (unit mandate), `runs/wave-b/verdict_GT5.md`
(the three blocks), `docs/in-progress/GENTOW2_ADJUDICATION_2026-08-24.md` §2 "Cascade flag" /
§10 item 3 (the predicted follow-up), A-C.12/A-C.13 comment style as template.

## Verdict

**A-C.14 ENACTED** — the three named leanspec axioms re-signed
(`leanspec/Leanspec/ChapC.lean`, nothing else in leanspec touched), `lake build Leanspec.ChapC`
GREEN (9276 jobs). **Landings: 2 of 3 FULL, 1 conditional-form + adjudicated HOLD** in the new
file `leanfinal/Uniformity/ChapC/C107ac14.lean` (`lake env lean` exit 0; every declaration
Lean-core). No `sorry`, no new `axiom`, no `unsafe`, no statement weakening.

| node | signed name | A-C.14 re-sign | leanfinal twin |
|---|---|---|---|
| C.89 | `gentow5w_two` | four supply binders added | **LANDED** (`C107ac14.gentow5w_two`) |
| C.89 | `gentow5w_one_shape` | four supply binders added | **HOLD** (OPEN-LETTERS, adjudicated); conditional form **LANDED** (`gentow5w_one_shape_of_letter_tie`) |
| C.90 | `gentow5_key_certificate` | `hadm` 3rd conjunct + `hr3 : 3 ≤ r` + recipe coupling `c`/`hψc`/`hres` | **LANDED** (`C107ac14.gentow5_key_certificate`) |

## Per-axiom diff summary (quoted sources)

### C.89 `gentow5w_two` — the four `gentow2_Bpp` supply families added

Added binders (byte-parallel with the [A-C.12]/[A-C.13] re-signed `gentow2_Bpp`, read at
depth 2):

```lean
    (hprev : I.PrevGrade u')
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNorm 2 (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNorm 2 (d * u')).natDegree < (I.keyAt 2).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNorm 2 (d * u') ≠ 0)
```

Source: this axiom's documented route is "(i) the `i = 2` discharge from C.99" (the C.89
header), and the re-signed C.99 consumes exactly these; the standing adjudication predicted
the cascade verbatim (`GENTOW2_ADJUDICATION_2026-08-24.md` §2):

> "**Cascade flag (not enacted here):** C.89's `gentow5w_two` (docstring: "the i = 2 discharge
> from C.99") and `gentow5w_one_shape` will need the same three families when their landing
> unit runs; flagged for the next A-C amendment."

B-1 source quote as at C.99 (GENTOW2_PROOF S5.2 proof, ll.740–744): "N := n̂₂(u₃),
M := n̂₂(u₃d): ladder monomials, deg < m₃, single-point N₃-polygon, exact grades κ̄ resp. β_t
(B-1)". `hprev` per [A-C.13] (restored Cor 4.12(2) scope premise at the iterated grade `u'`).

### C.89 `gentow5w_one_shape` — the same four families, at depth 1

Identical four binders with `chainNorm 1`/`keyAt 1` (the cascade flag names BOTH axioms). The
LETTER clause — the tie `Rgr u' (chainNorm 1 u') = letterZ 1 ^ k` — is deliberately NOT added
as a hypothesis: it is the axiom's remaining open content, the audited
**OPEN-LETTERS/OPEN-EVAL-ISO** gap (`runs/wave-b/verdict_GTB.md`, C.102 row: "No class field
relates `letterZ` to `ρ` or to `AdjoinRoot.root T.ψ₂`"), whose hold is adjudicated.

### C.90 `gentow5_key_certificate` — three hunks

**(i) The named repair — `hadm`'s omitted third conjunct** (the A-C.12 `gentow2_A` repair,
identically):

```lean
    (hadm : Irreducible ((I r le_rfl).Rres Φnext) ∧
      ((I r le_rfl).Rres Φnext).natDegree = f' ∧
      ((I r le_rfl).Rres Φnext).coeff 0 ≠ 0) :
```

Source (GENTOW5_PROOF_2026-08-09.md ll.793–796, read and quoted per the mandate):

> "psi_{i+1}^{(w_i)} is GENTOW2-A-ADMISSIBLE at each value of w_i — monic irreducible of
> degree f_{i+1} with nonzero constant term (y -> w*y is a substitution automorphism; B'' +
> the PE5 verification "psi_3^{(w)} is verifiably admissible for every w in K_2^x", ...)"

— i.e. the source's admissibility notion is `KP_criterion`'s full five-conjunct package; the
signed `hadm` dropped the fifth antecedent (GT5's block, GTB's genre for C.103).

**(ii) The depth-3 scope binder** `(hr3 : 3 ≤ r)`. The C93 census records this node as
"item (6)(α): depth-3 scope, 𝒲-conditional"; the 𝒲 law is consumed at the TOP rung `r` and
`Wle` only carries rungs `3 ≤ i`, so without it the `hW` binder is vacuous at the consumed
rung. Also repairs verdict_GT5.md's secondary observation ("`KP_criterion`'s degree antecedent
additionally needs `keyAt_deg` at `1 ≤ r`, a binder `gentow5_key_certificate` also never
supplies (`r = 0` is not excluded)").

**(iii) The recipe coupling of `ψ'` to `Φnext`** — a NEW false-shape finding by this unit
(not in GT5's verdict), repaired in the same enactment under the honesty invariant
("known-overclaiming statements do not stay signed", GSW §3) and the standing statement-change
authority:

* **Finding.** The A-C.1 signing left `ψ'` a FREE binder (only `Monic` + `natDegree = f'`)
  tied to `Φnext` by nothing. Instantiating `ψ' := X ^ f'` forces the conclusion's second
  clause to `Rres Φnext = wconj w (X ^ f') = X ^ f'` (any `w ≠ 0`), contradicting `hadm`'s
  irreducibility at `f' ≥ 2` — and, once (i) is enacted, the coeff-0 conjunct at EVERY
  `f' ≥ 1`. So the pre-A-C.14 axiom derives `False` at any inhabited configuration with
  `f' ≥ 2`: the GSW-§7 genre (an untied quantifier collapsing the statement). Enacting (i)
  alone would have WIDENED the contradictory range — the coupling repair is not optional.
* **Source.** The source ties them by construction: "keys Phi_1, ..., Phi_r built by THE
  RECIPE [GT5-r1: in its GAUGE-CORRECTED form — the S2.1 pin's vartheta-twisted khat_t]"
  (GENTOW5_PROOF S3 statement) and clause (a)'s display "R_{nu_i}(Phi_{i+1}) =
  psi_{i+1}^{(w_i)} := w_i^{f_{i+1}} * psi_{i+1}(y / w_i)" (ll.785–786).
* **Enacted binders** (the C.101-`hunit` discharge-node style — explicit supply, delete by
  follow-up amendment when the general-depth B-law lands):

```lean
    (c : ℕ → (W.trunc r le_rfl).fld r)
    (hψc : ψ' = Polynomial.X ^ f'
      - ∑ t ∈ Finset.range f', Polynomial.C (c t) * Polynomial.X ^ t)
    (hres : (I r le_rfl).Rres Φnext
      = Polynomial.X ^ f' - ∑ t ∈ Finset.range f',
          Polynomial.C ((I r le_rfl).Rgr ((f' - t) * u')
              ((I r le_rfl).chainNorm r ((f' - t) * u'))
            * (I r le_rfl).thetaRatio (f' - t) * c t) * Polynomial.X ^ t)
```

`hres` is exactly the depth-`r` B-law display (its landed depth-2 instance is C.101,
`C99r.gentow2_B`, with the gauge-correcting ϑ-twist of the recipe's khat_t appearing as the
`thetaRatio` factor); `hψc` names `ψ'` as the digit-string polynomial. With them the ∃`w`
clause is a THEOREM of the 𝒲 hypothesis (below), which is what makes this a supply re-sign
and not a conclusion-as-hypothesis bridge: the single `w`, its nonvanishing, and the
`wconj` conjugation display are all genuinely derived.

## Per-theorem landings (`leanfinal/Uniformity/ChapC/C107ac14.lean`, new file)

| declaration | status | proof route | axioms |
|---|---|---|---|
| `gentow5w_two` | **LANDED** (byte-faithful twin) | witness `w := Rgr u' (chainNorm 2 u')`, nonzero by `Rgr_ne_zero` at the `d = 1` supply rows; per-`t` law = `C99r.gentow2_Bpp` at `r = 2` (the documented C.99 route) | Lean core |
| `gentow5w_one_shape_of_letter_tie` | **LANDED** (conditional form, distinct name) | private `ratio_power_law` (the C99r algebra, fence-free — machine-checked class-field algebra, no open law asserted) + the explicit tie `htie` | Lean core |
| `gentow5w_one_shape` (byte-faithful twin) | **HOLD — the one remaining hold** | missing law, exactly: `∃ k : ℕ, I.Rgr u' (I.chainNorm 1 u') = I.letterZ 1 ^ k` (OPEN-LETTERS/OPEN-EVAL-ISO; adjudicated — not bridged) | — |
| `gentow5_key_certificate` | **LANDED** (byte-faithful twin) | KP: `KP_criterion` at `hmon`/`hdeg`-via-`keyAt_deg`(`1 ≤ r` from `hr3`)/`hadm.1`/`hadm.2.1`/`hadm.2.2`; ∃`w`: `hW r hr3` yields the single `w ≠ 0`, `hres` rewritten through the 𝒲 law, closed by the private `wconj_X_pow_sub_sum` (`wconj w (X^f' − Σ C(c t)X^t) = X^f' − Σ C(w^(f'-t)c t)X^t`) | Lean core |

## Build results

* `cd leanspec && lake build Leanspec.ChapC` — **GREEN**, "Build completed successfully
  (9276 jobs)" (run twice: after the re-signs, and after a cite-line precision fix in a
  comment). No other leanspec module references the three names (`rg` over `leanspec/Leanspec/`
  hits only `ChapC.lean`, whose own C93Census `#check` re-elaborates green).
* `cd leanfinal && lake env lean Uniformity/ChapC/C107ac14.lean` — **exit 0**, output exactly:

```text
'Uniformity.Density.Tower.C107ac14.gentow5w_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C107ac14.gentow5w_one_shape_of_letter_tie' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C107ac14.gentow5_key_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `rg -n "sorry|^axiom|unsafe" leanfinal/Uniformity/ChapC/C107ac14.lean` — docstring prose
  only; no live declaration.

## Follow-ups (recorded, not enacted)

1. **C.90 `hres` discharge** — when the general-depth B-law (the 𝒲-family analogue of C.101)
   lands, `hres`/`hψc`/`c` discharge and can be deleted by a recorded amendment (the C.101
   `hunit` precedent).
2. **OPEN-LETTERS carrier** — when it lands, `htie` discharges and the byte-faithful
   `gentow5w_one_shape` twin is one application of `gentow5w_one_shape_of_letter_tie` away.
3. **C.106 manifest** — `gentow5w_two`/`gentow5_key_certificate` now have leanfinal twins;
   the census assembly unit can consume them.
