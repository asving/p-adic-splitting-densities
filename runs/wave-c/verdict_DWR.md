# Verdict DWR — revised deep-witness blueprint

**Date:** 2026-08-28  
**Verdict:** **STOP-LINE FOR MP1 UNDER THE CURRENT PAYLOAD.  A DISTINCT-FACTOR INPUT
PASSES THE EXTENDED FORMAL CERTIFICATE, BUT GN INDEX ALIGNMENT IS STRUCTURALLY
IMPOSSIBLE.**

## What changed

The DWC tower survives unchanged, but its MP1 input and its campaign accounting do not.
`leaf²` is now a mandatory rejected control.  The revised numerical candidate is

```text
k = keyAt 4
Λ = chainNormBelow 4 171
leaf = k - Λ
h = k + 1
F0 = leaf * h
B'.Φ = quot.Φ = leaf
B'.F = quot.F = h.
```

This keeps parent mass two and makes the quotient a distinct degree-16 polynomial.  It
repairs both defects the old sparse certificate missed, but it is only a formal control
candidate, not an honest GN occurrence.

The mass-one alternative is formally impossible.  `I10RecenterLive.MP1StepCore.hmass`
demands `deg quot.F + D = deg B.F`; every quotient `BlockData` has degree at least `D`, so a
degree-`D` input would require `D+D=D`.

The blueprint was revised in place by preserving DWC §§1–10 as history, adding a binding
`[DWR 2026-08-28]` §11, and inserting visibly marked `[DWR]` rows in the original gate,
D3, realization, and consumer tables.  No DWC text was silently rewritten.

## Extended certificate

`verification/dwc_tower_cert.py` now checks exact sparse-polynomial gcds over `ℚ`, both
parent and quotient key-freeness, residual factor order, and the mass-one obstruction in
addition to all previous tower numerics.

Fresh run from the repository root:

```text
proper_stages=4
live_deep_levels=1
full_input_mass=2
input_degree=32
leaf_degree=16
cofactor_degree=16
quotient_mass=1

accepted F0=leaf*(keyAt4+1):
  exact_quotient=keyAt4+1
  parent_keyfree=True
  quotient_keyfree=True
  hmass=16+16=32
  ord_psi(residual)=1

rejected leaf^2 control:
  parent_keyfree=True
  exact_quotient=leaf
  quotient_keyfree=False
  ord_psi(residual)=2

rejected mass-one control:
  minimum quotient degree 16 gives 16+16 != 16
```

Command: `python3 verification/dwc_tower_cert.py` — **exit 0**.

The certificate deliberately models the cofactor residual by the unit `1`; it is not a
substitute for G8/G9 and cannot see GN's factor-indexing obstruction.

## Corrected key-free and multiplicity route

The planned Lean proof has four separate coprimality facts:

1. `k` and `k+1` have explicit Bézout difference one.
2. `k` and `leaf` are distinct monic irreducibles of degree 16.
3. `leaf` and `k+1` are coprime because equality would force the degree-15 `Λ` to equal
   `-1`.
4. Product coprimality then supplies parent `BlockData.hkeyfree`; item 3 supplies quotient
   `BlockData.hkeyfree`.

In the formal residual control, `R(k+1)=c` with `c≠0` gives
`R(F0)=(X+1)c`, so `ord_(X+1)=1`.  For `leaf²`, multiplicativity gives `(X+1)²`, order
two, as DWV required the certificate to expose.  The formal improvement does not change
which factor GN indexes by a finite slope.

## Stop-line finding: no honest current-payload occurrence

`GNCitePayload` receives `phi := B'.Φ`.  Its `exactLeaf` identifies the theorem-selected
`g_{λ,ψ}` with that same `phi`, while `leaf_dvd_input` and `RecenterStep` require
`phi ∣ B.F`.  In GN's factorization, literal `phi` divisors form the separate key-power
term.  The polynomial `phi` itself has no finite principal Newton side relative to its own
`phi`-development, so it cannot simultaneously be a finite-slope selected
`g_{λ,ψ}`.

This defeats every input under the current identification, not just `leaf²`: replacing
`leaf²` by `leaf*h` reduces the literal key power from two to one but does not turn that
copy into a slope-residual-selected factor.  Consequently no source-faithful MP1 occurrence
exists in this tower under the present payload shape.  Reconsidering that shape or replacing
the GN leg with the direct key-irreducibility route is A-I.8-grade; DWR flags it and does not
enact it.

## Added gates and provenance

| gate | binding acceptance condition |
|---|---|
| **G7 quotient key-free** | Literal `quot.F=k+1`, `quot.Φ=leaf` satisfies `BlockData.hkeyfree`; `leaf²` fails. |
| **G8 residual order one** | Actual `R_λ(F0)=ψ*c`, `c≠0`, for the same input/slope used by GN. |
| **G9 GN alignment — RED** | Current surface requires finite-slope `g_{λ,ψ}=leaf=φ` and `φ∣F0`; GN places that literal divisor in the separate key-power term. |
| **G10 occurrence→universal** | Per-witness exporters quantify over every `DeepLive` level and every same-witness exported recenter step. |

The revised `RecenterStep` design must bind the non-key fields by

```text
step.quot.F = B'.F
B'.T = B.T
step.quot.T = B.T
B.F = B'.Φ * B'.F.
```

At the occurrence, `B'.F=k+1`.  Binding `B'.F=B.F` is explicitly rejected because
`B'.Φ∣B.F` would contradict `B'.hkeyfree`.

One occurrence now yields only nonvacuity.  The honest universal surfaces are
`DeepLevelPerWitnessExporter X` and `MP1EmissionPerWitnessExporter X`; a later
`LadderSupplyLive₂` assembly additionally needs its independent HE7A `package` and `lb1`
fields.  C6r therefore no longer claims a ladder record from C3/C5r alone.

## Re-graded node/gate summary

| node/group | revised grade |
|---|---:|
| G0 principal polygon/slope residual | research, 5–15 working days |
| G1 selected factor/completion descent | research, 5–15 working days |
| G2 reviewed statement/provenance amendment | 2–5 days after G0/G1 shapes |
| shared L2E engine replacing D3-03/D3-10 | research, 8–15 working days |
| C3 tau triangular spanning | research, 5–12 working days |
| R3 valuation realization | research, 3–8 working days |
| R4 source thresholds/windows | research, 3–7 working days |
| R5 canonical letters/dictionary | research, 5–12 working days |
| C4r honest GN occurrence | **REFUTED under current payload / A-I.8 review** |
| G10 universal exporters | theorem family, 2–4 working days after producers |

All unaffected arithmetic and packaging rows retain their 30–60 minute transcription
grade.  The conditional post-A-I.8 count is **83 planned nodes** (`69 - 2 + 12 + 4`).
R8r/C4r/C5r/C6r replace old rows and do not increase the count.  The current MP1 branch is
stopped at G9.

## Shared level-2 engine sub-blueprint

The one generic engine serves D3-03/D3-10 and F1.4–F1.6:

| node | output |
|---|---|
| L2E-00 | Reviewed level-2 slot-carry/twist statement shapes in `LevelDatum` vocabulary. |
| L2E-01 | Full level-2 coefficient read underlying `dv2Res`. |
| L2E-02 | Level-2 key-root vanishing and exact key-height pin. |
| L2E-03 | Digit survival strengthened from height to nonzero residue read. |
| L2E-04 | Reduced-digit `dv2Res` product with exact root/cocycle factor. |
| L2E-05 | Level-2 pair convolution pricing and endpoint uniqueness. |
| L2E-06 | Generic `dv2Supp_mul` equality. |
| L2E-07 | `dv2SideMin_mul`, `dv2SideMax_mul`, and `dv2SideDeg_mul` equalities. |
| L2E-08 | Product pin-height addition. |
| L2E-09 | Coefficientwise `dv2ResPoly` product law over `AdjoinRoot L.r`. |
| L2E-10 | Complement specialization giving the exact `γg * root^cocycle` scalar. |
| L2E-11 | D3 adapters plus all signed acceptance tests. |

Acceptance tests are exact C.39 `dv2ResPoly_scalar`, C.64 `mult₂_readable`, C.38
`dv2ResPoly_radical_eq`, D3-03 residue survival, and D3-10 μ4 convolution.  The route is the
level-2 twin of `C133mh3`'s full-read/key-root/coefficientwise proof, using
`C134dv2g` only for its already-landed support and no-interaction shell.

## Highest risk

The single highest-risk node is **G9: GN valuation/key-index alignment**, and it is already
**RED**.  The current surface equates a finite-slope selected factor with the literal test-key
divisor in GN's separate key-power term.  G0 remains a major missing analytic engine, but
building it cannot repair that identification.  L2E is larger in algebraic volume but has
the landed level-1 §3 route as a concrete template.

## Files and rules

Changed only:

- `verification/dwc_tower_cert.py`
- `docs/in-progress/DEEP_WITNESS_CAMPAIGN_2026-08-28.md`
- `runs/wave-c/verdict_DWR.md`

No landed `.lean` or leanspec file was edited.  No owner's-paper citation was used.  No git
commit was made.
