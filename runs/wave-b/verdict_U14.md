# Verdict — U14: Corollary 4.12 grade anchoring

Date: 2026-08-25

Status: **DECIDED — restore the source restriction; do not re-anchor RP-1**

The printed operator `R_{r,α}` is grade-anchored. Definition 3.13 parametrizes its monomials
by the fixed line `L_α`, starting at `s_r(α)`. The per-polynomial left-endpoint shift is the
separate normalized operator `R_r = R_{r,α}/y^{⌊s(g)/e_r⌋}` (Definition 3.15).

Published Corollary 4.12(2) does **not** assert unrestricted plain multiplication. It says:

> “If `β ∈ Γ_{r−1}`, then `R_{r,α+β}(gh) = R_{r,α}(g)R_{r,β}(h)` ...”

and the proof uses the restriction verbatim: “because `s_r(β) = 0`”. The arXiv-v3 copy has
the same result as Corollary 4.7(2).

For arbitrary grades the same proof gives a carry factor. At S2 this is

```text
R_{β+β'}(gh) = X^((β%2)(β'%2)) R_β(g) R_β'(h).
```

Thus RP23's twist is a correct S2 **generalization**, not a transcription of Corollary
4.12(2). RP-1's operator should remain unchanged. `C130fg.lean`'s `graded_mul` should regain
`PrevGrade β'` (equivalently `e' ∣ β'` once OPEN-DICT-2 certifies the cleared coordinate).

The coefficient-zero scalar does not survive odd-by-odd carry:
`coeff 0 (X P Q) = 0`, while RP23 has `coeff 0(1) * coeff 0(1) = 1`. Therefore the current
unrestricted A-C.11 `Rgr_mul` cannot be obtained from the twisted graded law. Either restrict
that scalar field by `PrevGrade`, or deliberately change the unrestricted consumer scalar to
the constant coefficient of the normalized residual and cite Corollary 4.12(3).

`normalized_mul` is unaffected: its `y`-power stripping absorbs exactly the carry, and the
printed Corollary 4.12(3) remains
`R_r(gh) = R_r(g)R_r(h)` for all polynomials.

Full print-read, proof calculation, and diff proposal:
`docs/in-progress/COR412_ADJUDICATION_2026-08-25.md`.

No Lean source, roll-up, or git history was changed.
