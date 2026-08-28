# Verdict G5F — μ5 unit refinement admissibility

**Date:** 2026-08-28  
**Gate:** DWC §6.1 G5  
**Adjudication:** **PASS** for source admissibility and operator-level classification.
The stop-if-false condition is not triggered.

No owner's-paper citation is used.  The literature evidence below is confined to the two
supplied primary-source PDFs.

## 1. Result

The row `(e',f',u')=(1,1,171)` is a source-faithful parameter row for an equal-key-degree
ordinary augmentation/refinement over the depth-four valuation:

```text
old cleared key value = 170 < 171 = new absolute value
e' = 1
f' = degree(linear residual factor) = 1
gcd(u',e') = gcd(171,1) = 1
new key degree = e' f' D4 = 1*1*16 = 16 = D4.
```

It is therefore a refinement/operator at the existing depth-four level.  It is not a fifth
proper tower stage.  A stage-five encoding is ruled out by the landed type itself.

## 2. Exact FGMN evidence

Source: Fernández--Guàrdia--Montes--Nart, *Residual ideals of MacLane valuations*,
`docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`.

| PDF page | exact clause | consequence for G5F |
|---:|---|---|
| 5 | Definition 1.6 constructs the augmented valuation `[μ;(φ,ν)]` for `φ∈KP(μ)` and `ν>0`. | Augmentation itself has no strict key-degree-growth premise. |
| 11 | §3: *“A valuation μ ∈ V is called inductive if it is attained after a finite number of augmentation steps starting with μ₀.”* | Equal-degree ordinary augmentations are not excluded from inductivity. |
| 11 | §3.1 calls a chain MacLane when consecutive keys are not initially equivalent; it separately calls it **optimal** when key degrees grow strictly. | Strict growth is an optimal-chain/rung normalization, not an augmentation-admissibility condition. |
| 12 | Lemma 3.4: two consecutive augmentations with `deg φ'=deg φ` collapse to `[μ;(φ',ν+ν')]`. | Same-degree augmentation is valid but does not create a new optimal depth. |
| 14 | §3.2, equation (7): `m_i=e_{i-1}f_{i-1}m_{i-1}`. | `e'=f'=1` forces unchanged key degree. |
| 23 | Theorem 5.7 proof constructs the residual lift with degree `e_r (deg ψ) m_r`. | For `e_r=1` and linear `ψ`, the lifted key has the old degree. |

This source gives both halves needed here: FGMN residual/key operators accept the unit
degree multiplier, while an optimal chain compresses the equal-degree augmentation rather
than counting it as another proper level.

## 3. Exact GN/MLV evidence

Source: Alberich-Carramiñana--Guàrdia--Nart--Poteaux--Roé--Weimann, *Polynomial
Factorization Over Henselian Fields*, `docs/references/s10208-024-09646-x.pdf`.

| PDF page (journal page) | exact clause | consequence for G5F |
|---:|---|---|
| 14 (644) | §3.1 constructs `[μ;φ,γ]` when `μ(φ)<γ` and states `deg(ν)=deg(φ)`. | `170<171` is the required positive augmentation increment in the campaign's cleared normalization. |
| 15 (645) | Definition 3.2 requires `deg(μ_n)<deg(μ_{n+1})` for an ordinary augmentation retained as an MLV-chain step. | An equal-degree refinement is not appended as a new MLV rung. |
| 25 (655) | The worked example says the equal-degree chain is not MLV, calls the non-growing case a refinement, and goes back to the earlier type with the improved key. | A refinement replaces key/type data at the same effective depth. |
| 35 (665) | Definition 5.5: *“A refinement step ... yields a unique new type ... with moreover `deg(ϕ)=deg(φ)`.”* | No key-degree growth is the defining refinement condition. |
| 35 (665) | Immediately after Definition 5.5: refinement is characterized by a one-sided principal polygon with `e_rel(μ_λ)=1` and residual `(y-ζ)^ℓ`, `ζ∈κ(μ_λ)^*`. | The refinement has relative ramification `1` and a linear irreducible residual factor, hence `f'=1`. |

Thus GN's inductive-valuation machinery expressly admits refinement operations in which the
key degree does not grow; it keeps the MLV chain strict by replacing/compressing rather than
adding a level.

## 4. Landed Lean boundary

The landed interfaces reproduce that division:

* `leanfinal/Uniformity/ChapC/C130pk.lean:110-111` has
  `FGMNCalculus W e' f' u'`, parameterized over an already existing
  `W : DeepTower ... r`.  The operator parameters do not increment `r`.
* `leanfinal/Uniformity/ChapC/C83.lean:148-150` requires
  `DeepTower.hproper : 2 ≤ e i * f i` for every tower stage `i≥2`.
* A fifth row with `e 5=f 5=1` would demand `2≤1`; independently,
  `D5=D4*(1*1)=16`, so strict degree growth fails.

The row therefore **MUST** remain an `FGMNCalculus (s2DepthFour ...) 1 1 171`-style
operator/refinement parameterization.  It cannot inhabit a fifth `DeepTower` rung.

## 5. Machine check

Probe: `leanfinal/scratch/G5F_probe.lean`.

It proves:

* `unit_row_not_a_proper_stage` directly from `DeepTower.hproper`;
* `one_one_one_seventy_one_not_stage_five` for a hypothetical depth-five tower;
* `1*1*16=16` and failure of `16 < 1*1*16`.

Required per-file command:

```text
cd leanfinal && timeout 580 ~/.elan/bin/lake env lean scratch/G5F_probe.lean
```

Result: exit code `0`.

## 6. Scope fence

PASS does not mean that the triple alone proves an actual OM refinement occurrence for a
chosen input polynomial.  Definition 5.5 additionally requires the unique-new-type,
one-sided-principal-polygon, and residual pure-power facts.  Those are polynomial-specific
analytic/provenance obligations assigned elsewhere in the blueprint (or bypassed by §12's
superseding direct-key route).

Accordingly:

* **proved:** the unit row is a legitimate FGMN/GN refinement parameter shape and an
  inductive ordinary-augmentation input;
* **proved:** it is operator data over depth four and cannot be a fifth proper stage;
* **not claimed:** the missing GN occurrence facts follow from `(1,1,171)` alone.

The exact false overreach would be to use this G5F PASS as the one-sided-polygon/residual
occurrence witness.  The campaign does not receive that witness from G5F.
