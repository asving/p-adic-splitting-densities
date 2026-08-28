# Verdict SRX — S2 recenter export

**Date:** 2026-08-28  
**Unit:** SRX  
**Verdict:** **NOT CONSTRUCTIBLE AT THE LANDED S2 OCCURRENCE; two stronger obstructions are machine-proved.**

## Result

The C132 μ₃ bank does contain a genuine proper depth-two key that the earlier REX prefix
missed:

```text
g₈ = Φ₂² - 2⁴Φ′.
```

`scratch/SRX_probe.lean` proves, sorry-free, that `g₈` is monic of degree `8`, its normalized
μ₃ residual is `X+1`, it is an `S2Mu3KeyPoly`, and it is not μ₃-initial-equivalent to the
carried `Φ₂`.  Thus the key-polynomial and tangent-class mathematics really is landed for
the bank's proper successor.

That successor cannot inhabit the production `RecenterStep` at the landed socket.  The
external block key is degree `4`, and subtracting `Λ` of degree `< 4` leaves degree `4`, so
it cannot equal degree-8 `g₈`.  Also the landed input is the degree-4 polynomial `Φ₂+1`, so
`g₈` cannot divide it.

There is an independent, universal blocker: production `RecenterStep` includes
`Nonempty (MP1StepCore B B')`.  Since the landed parent has `B.μ=1`, every quotient block
has degree at least `D`, while `MP1StepCore.hmass` requires
`deg quot.F + D = deg B.F = D`.  The probe proves:

```lean
s2_mp1StepCore_empty : ∀ B', ¬ Nonempty (IFC5.MP1StepCore B2 B')
s2_recenterStep_empty : ∀ B' Λ, ¬ IFC5.RecenterStep C2 B2 B' ... 4 Λ
s2_mp1CarrierLive_vacuous : IFC5.MP1CarrierLive C2 B2 ... 4
```

The final theorem is a vacuity certificate, not the requested first honest inhabitant
route.  Accordingly, no `s2RecenterStep` declaration is claimed.

## Per-field status

| Field / clause | Landed discharge or precise gap | Status |
|---|---|---|
| `e'`, `f'`, `u'` | `C132fd0.s2SourceDataTwo`, numerals `(2,1,21)` | **PROVED** |
| `source` | `C132fd0.s2SourceDataTwo` on the exact depth-two tower and key chain | **PROVED as Lean data**; GN analytic dictionary open |
| `sourceLaws` | `s2SourceLawsTwo_of` fired by `C132rp10b.s2Mu3_hex` and `C132kp6b.s2Mu3_hconv`; probe `s2SourceLaws` | **PROVED as Lean laws**; GN analytic dictionary open |
| `keyPolynomial` | probe `mu3SuccessorKey_isKey`, assembled from `s2Mu3_key_criterion`, `s2Mu3NormRes_g8`, and `s2Mu3_X_add_one_irreducible` | **PROVED for degree-8 `g₈`**, not for an outer degree-4 recenter |
| `tangentClass` | probe `mu3SuccessorKey_tangentClass`: `R(g₈)=X+1 ≠ 1=R(Φ₂)`; carried `Φ₂` fails by reflexivity | **PROVED for `g₈`**, unavailable at the external key |
| `monicInput` | `C130s17.s2InputPolynomial_monic`; probe `s2Input_monic` | **PROVED over `O[x]`**; completion dictionary open |
| `slope`, `slope_pos` | no Newton-polygon slope-membership predicate; probe `payloadWithArbitraryPositiveSlope` replaces the value arbitrarily | **STATEMENT-SURFACE GAP** |
| `residual` | `s2Mu3NormRes_g8 = X+1` is the candidate key's normalized residual, not `R_{r+1,λ}(B.F)` | **GAP / wrong operator for GN indexing** |
| `psi_monic` | `ψ=X+1` | **PROVED intrinsically** |
| `psi_irreducible` | `C132rp10.s2Mu3_X_add_one_irreducible` | **PROVED intrinsically** |
| `residual_factorization` | synthetic `X+1=(X+1)·1` is available, but `residual` is not bound to the input's slope residual | **NOT honestly discharged** |
| `residual_multiplicity_one` | synthetic `¬(X+1)∣1` is available; no multiplicity theorem for an actual selected slope residual | **GAP** |
| `leaf_monic` | `g₈` monic | **PROVED for candidate** |
| `leaf_dvd_input` | probe `mu3SuccessorKey_not_dvd_s2Input` | **REFUTED for `g₈`** |
| `exactLeaf` | no relation to the theorem-selected `g_{λ,ψ}` is present; candidate also fails divisibility | **GAP; mandatory** |
| outer exact recentering | probe `mu3SuccessorKey_not_recentered` | **REFUTED for `g₈`** |
| outer divisibility | candidate does not divide the landed input | **REFUTED for `g₈`** |
| `MP1StepCore` | probe `s2_mp1StepCore_empty`, for every successor block | **REFUTED universally at S2** |
| same-witness views | existing `S2`/`X2` realization and the landed socket views | **PROVED**, but irrelevant to the contradiction |

## Faithfulness check

Guàrdia–Nart, *Genetics of polynomials over local fields*, Contemporary Mathematics 637
(2015), Theorem 2.3, author PDF p. 10, says:

* `μ` is an inductive valuation equipped with a MacLane chain (1.1);
* `φ ∈ KP(μ)` and `φ ≁_μ φ_r`;
* `g` is monic in the completed valuation ring `O_v[x]`;
* `-λ` ranges over the slopes of `N^-_{r+1}(g)=N^-_{v_r,φ}(g)`;
* `ψ` ranges over the prime factors of
  `R_{r+1,λ}(g)=R_{v_r,φ,λ}(g)`;
* if `ord_ψ(R_{r+1,λ}(g))=1`, then the selected `g_{λ,ψ}` is irreducible in `O_v[x]`.

The proof on the same page specifies `g_{λ,ψ}` as the product of the prime factors whose
Newton polygon is one-sided of slope `-λ` and whose slope residual is a power of `ψ`.

The production `GNCitePayload` is therefore **not one-to-one with Theorem 2.3**:

1. `slope_pos` omits membership among the slopes of the principal Newton polygon.
2. `residual` is an arbitrary polynomial, with no equality to the slope residual of the same
   `source`, `g`, `phi`, and `slope`.
3. Hence `psi` is not asserted to be a prime factor of the theorem's residual.
4. `leaf_dvd_input` and `exactLeaf` identify an arbitrary named divisor with `phi`, not with
   the theorem's selected `g_{λ,ψ}`.
5. The payload uses `Polynomial O`; the theorem factors over the completion `O_v[x]`, and no
   completion/base-change field is present.

The multiplicity encoding `residual = psi * residualQuot` plus
`¬ psi ∣ residualQuot`, with irreducible `psi`, is faithful once `residual` is correctly
bound.  The missing binding is the defect.

The brief says the PDF is repo-local, but it is absent from `docs/references/`; the two FGMN
PDFs there are the different *Residual ideals of MacLane valuations*.  The clause was checked
against the primary author copy:
`https://upcommons.upc.edu/bitstream/handle/2117/28206/GeneticsCM.pdf`.

No owner's-paper citation is used.

## Exact named opens

### `SRX-RECENTER-STEP-SPLIT`

Current machine theorem:

```lean
∀ (B' : Ladder.BlockData C2) (Λ : Polynomial O2),
  ¬ IFC5.RecenterStep C2 B2 B' G2 K2 L2 N2 v2 rho2 q2 4 Λ
```

The next statement amendment must split the pre-cite producer export from `MP1StepCore`,
with a terminal-leaf outcome at `B.μ=1`, or fence peel steps by `2 ≤ B.μ`.  Keeping
`MP1StepCore` inside `RecenterStep` cannot yield an honest S2 inhabitant.

### `SRX-GN-SLOPE-RESIDUAL-BIND`

Add fields with the exact mathematical content

```text
-slope ∈ slopes (N^-_{r+1}(g))
residual = R_{r+1,slope}(g)
```

for the payload's same source, chain, `g`, and `phi`.  A positive rational alone is
insufficient.

### `SRX-GN-SELECTED-LEAF-BIND`

Add a relation identifying `leaf` with Theorem 2.3's factor `g_{slope,psi}`—for example via
the proof's exact prime-factor characterization—and add the `O_v[x]` to `O[x]` dictionary
needed by downstream `BlockData`.

### `SRX-S2-NONTERMINAL-OCCURRENCE`

Land a realized input with degree at least `8` / parent mass at least `2`, an actual selected
slope residual containing `X+1` to order one, and a selected factor equal to the exported
successor.  The current degree-4, mass-one acceptance input cannot support the proper key.

## Probe status

Required command executed exactly from `leanfinal`:

```bash
timeout 580 ~/.elan/bin/lake env lean scratch/SRX_probe.lean
```

**Exit 0.**  Zero `sorry`; all eight printed declarations report exactly
`[propext, Classical.choice, Quot.sound]`.

Files delivered:

* `leanfinal/scratch/SRX_probe.lean` — new probe;
* `docs/in-progress/LADDER_SUPPLY_2026-08-27.md` — this unit's dated append;
* `runs/wave-c/verdict_SRX.md` — this verdict.

No landed `.lean`, leanspec, or existing scratch file was edited.  No git commit was made.
