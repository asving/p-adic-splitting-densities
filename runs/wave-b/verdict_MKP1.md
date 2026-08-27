# MKP1 verdict — M3-KP1 LANDED

Node: **M3-KP1 residual divisibility** (`GENUINELY-NEW`), 2026-08-27.

## Outcome

Landed `leanfinal/Uniformity/ChapC/C132kp1.lean`, with zero `sorry` and zero new axiom.
Both requested directions are proved:

- `mu3NormRes_dvd_of_S2Mu3Dvd`: universal forward translation
  `g ∣μ₃ a → R₄(g) ∣ R₄(a)`;
- `S2Mu3Dvd_of_mu3NormRes_dvd`: backward translation for monic `g` with
  `g.natDegree ≤ 8` and nonunit normalized residual;
- `S2Mu3Dvd_iff_mu3NormRes_dvd`: the packaged equivalence in that honest monic scope.

Supporting declarations establish normalized-residual transport under μ₃ initial
equivalence and the new degree-`<8` constant/unit residual mechanism.

## Informal argument / minimality audit

Forward uses the landed normalized convolution/product theorem: from
`a ∼μ₃ gq`, normalized residuals agree and `R₄(gq) = R₄(g)R₄(q)`.

Backward uses monic division `a = r + gq`. If `μ₃(r) > μ₃(gq)`, this is the desired
initial equivalence. If not, the strong graded-add law plus the graded product law makes
`R₄(g)` divide the exact graded residual of `r`. Monic division gives
`deg r < deg g ≤ 8`; since the μ₃ development key has degree four, only development slots
zero and one remain, and the parity-two grade line sees at most one. Thus a nonzero
remainder has a nonzero constant graded residual, forcing `R₄(g)` to be a unit, contrary
to the hypothesis.

`S2Mu3Minimal` does not enter either direction. The concrete degree/nonunit fences supply
the remainder contradiction directly; minimality is downstream of this translation.

**BLOCKED-BECAUSE: none.** No statement beyond the cited landed inputs was required.

## Verification

From `leanfinal/`:

```text
lake build Uniformity.ChapC.C132kp0 Uniformity.ChapC.C132rp3
Build completed successfully (8792 jobs).

lake env lean Uniformity/ChapC/C132kp1.lean
exit 0
```

The scoped build was used only to materialize missing `.olean` files for the fresh landed
inputs; no bare `lake build` was run.

## AxChk footer

Verbatim from the green `lake env lean Uniformity/ChapC/C132kp1.lean` run:

```text
'Uniformity.Density.Tower.C132kp1.s2Mu3NormRes_eq_of_initialEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132kp1.mu3NormRes_dvd_of_S2Mu3Dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132kp1.s2Mu3GradedRes_eq_C_of_natDegree_lt_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132kp1.s2Mu3NormRes_isUnit_of_natDegree_lt_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Uniformity.Density.Tower.C132kp1.S2Mu3Dvd_of_mu3NormRes_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Uniformity.Density.Tower.C132kp1.S2Mu3Dvd_iff_mu3NormRes_dvd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
