# U12 — the level-general C.90 carrier

Date: 2026-08-24  
Status: **DESIGN DECIDED; signatures elaborate; full source construction is a new heavy-math layer**

## 1. Verdict

The landed CC wave removes about half of U7's old blocker list, but it does **not** make
published FGMN Corollary 6.3 a theorem about a bare `ChainRealization`.

What has landed is the repository side of the dictionary: the polynomial key chain, a Laurent
normalizer, level residue fields and their terminal receiver, stage value/digit tables, legal
residual node points, and one **terminal/next-augmentation** FGMN residual package. What is still
missing is target-specific and source-side: the complete chain of inductive valuations
`μ₀,…,μ_r`, their augmentation laws, all source residual fields/operators, the actual Newton
polygons, a prime target `F`, a root `θ` in an algebraic closure of the completed valued fraction
field, the valuation of that root ambient, and the top key/divisibility/non-equivalence
hypotheses.

The category distinction is decisive. `ChainRealization.node` uses

```lean
Kt = the terminal residue field,  L / Kt = a residual-field ambient.
```

FGMN uses `θ ∈ K̄_v`, where `K_v` is the completed valued fraction field. Thus
`A.node.coord x : L` is **not** an FGMN root and `A.node.pointHgt` is not the root evaluation
`v(g(θ))`. Reusing it as such would be a false dictionary, even though the types `Field L` and
`WithTop ℤ` look superficially convenient.

The design is consequently another conservative layer, not an extension of `DeepTower` or
`ChainRealization`:

```text
ChainRealization A
       + CompletedRootAmbient B
       + MacLaneChainSource M
       + LevelGeneralDictionary D
       + target-specific LevelGeneralInput X
       -- published Corollary 6.3 --> Cor63Conclusion X
       -- Lean-core dictionary transport --> C90LevelGeneralPackage X
```

`Cor63Conclusion` is a theorem **codomain**. None of its conclusions is a field of the input
carrier. The elaboration authority is `leanfinal/scratch/U12_check.lean`; it contains no
`sorry` and no axiom declaration. At HEAD:

```text
cd leanfinal
lake env lean scratch/U12_check.lean

'...Cor63Conclusion.toC90' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

## 2. Published statement, print-read

Primary source: J. Fernández, J. Guàrdia, J. Montes, E. Nart, *Residual ideals of MacLane
valuations*, J. Algebra 427 (2015), 30–75; repository author PDF
`docs/references/FGMN_residual_ideals_2015_authorpdf.pdf`, SHA-256
`33b849ce6784f4bad8368d83b5b725b4545eebdd79918e3ee5dfafd1791daeda`.

Theorem 6.2 was visually print-read on published p. 25 (PDF page 25):

> “Let `F ∈ P` be a prime polynomial and `θ ∈ K̄_v` a root of `F`. Let `φ` be a key
> polynomial for the inductive valuation `μ`. Then, `φ |μ F` if and only if
> `v(φ(θ)) > μ(φ)`. Moreover, if this condition holds, then:
> (1) Either `F = φ`, or the Newton polygon `N_{μ,φ}(F)` is one-sided of slope `−ν`, where
> `ν = v(φ(θ)) − μ(φ) ∈ Q_{>0}`.
> (2) Let `ℓ = ℓ(N_{μ,φ}(F))`. Then, `F ∼μ φ^ℓ` and `deg F = deg φ^ℓ`. In particular,
> `R(F)` is a power of the maximal ideal `R(φ)`.”

Corollary 6.3 was visually print-read on published p. 26 (PDF page 26):

> “With the above notation, suppose that `φ |μ F` and `μ` admits a MacLane chain of length
> `r` as in (4) such that `φ ≁μ φ_r`. Then, for any `1 ≤ i ≤ r`, the Newton polygon
> `N_i(F)` is one-sided of slope `−ν_i`, we have `v(φ_i(θ)) = μ(φ_i)` and
> `F ∼_{μ_{i−1}} φ_i^{ℓ_i}`, `deg F = deg φ_i^{ℓ_i}`,
> `R_{i−1}(F) = (ψ_{i−1})^{ℓ_i}`,
> where `ℓ_i := ℓ(N_i(F))`. In particular, `ℓ_i = e_i f_i ℓ_{i+1}` for all
> `1 ≤ i < r`.”

These are not merely six unrelated equalities. Their objects come from earlier definitions:

* Definition 1.1, published p. 3, says verbatim:

  > “Let `V` be the set of discrete valuations, `μ : K(x)* → Q`, such that `μ|K = v`
  > and `μ(x) ≥ 0`.”

  This is why every `PolynomialValuation` is finite away from zero and why
  `MacLaneChainSource` records both `mu_restricts` and `mu_X_nonnegative` rather than merely
  an arbitrary function satisfying multiplicativity.

* Definition 1.2, published p. 4, says verbatim:

  > “We say that `g,h ∈ K[x]` are `μ`-equivalent, and we write `g ∼μ h`, if
  > `H_μ(g) = H_μ(h)`. Thus, `g ∼μ h` if and only if
  > `μ(g − h) > μ(g) = μ(h)` or `g = h = 0`.”

  and

  > “We say that `g` is `μ`-divisible by `h`, and we write `h |μ g`, if `H_μ(g)` is
  > divisible by `H_μ(h)` in `Gr(μ)`. Thus, `h |μ g` if and only if `g ∼μ hf` for some
  > `f ∈ K[x]`.”

  This is why U12 defines `MuEquiv` by the paper's displayed value criterion and
  `MuDivides` by the displayed factor criterion; neither is ordinary polynomial divisibility.

* Definition 1.6, published p. 5, says verbatim:

  > “If `g = Σ_{0≤s} a_s φ^s` is the `φ`-expansion of `g`, then
  > `μ′(g) = min_{0≤s}{μ′(a_s φ^s)}`. Equivalently,
  > `μ′(g) = min_{0≤s}{μ(a_s φ^s) + sν}`. We use the notation
  > `μ′ = [μ; (φ,ν)]`.”

  Hence `MacLaneChainSource.augmentation` is an equation to the actual canonical `dev`
  coefficients, not an opaque `IsAugmentation` flag.

* Section 3.1, published p. 11, says verbatim:

  > “A chain of augmented valuations as in (4) is called a MacLane chain (of length `r`) if
  > `φ_{i+1} ≁_{μ_i} φ_i` for all `1 ≤ i < r`.”

  This is exactly `MacLaneChainSource.macLane`.

* Section 3.2, published p. 14, introduces the fields verbatim:

  > “`F_0 := Im(F → Δ_0)`, `F_i := Im(Δ_{i−1} → Δ_i)`, `1 ≤ i ≤ r`.”

  It then says:

  > “we consider as inclusions the canonical embeddings:
  > `F = F_0 ⊂ F_1 ⊂ ··· ⊂ F_r`.”

  Thus the family of source residual fields and the transition maps are genuine source
  objects; terminal `W.fld r` alone is insufficient.

* Section 3.3, published p. 15, says verbatim:

  > “`z_i ∈ F_{i+1}`, the image of `y_i` under `Δ_i → Δ_{i+1}`,
  > `ψ_i ∈ F_i[y]`, the minimal polynomial of `z_i` over `F_i`.”

  This is the source of `residueHom`, `letter`, `psi`, `psi_root`, and `psi_minimal`.

* Section 3.4, published p. 16, introduces the level operators verbatim:

  > “We consider Newton polygon operators
  > `N_i := N_{μ_{i−1},φ_i} : K[x] → 2^(R²)`, `0 ≤ i ≤ r`,
  > and residual polynomial operators:
  > `R_{i,α} : P_α(μ_i) → F_i[y]`, `0 ≤ i ≤ r`, `α ∈ Γ_i`,
  > `R_i : K[x] → F_i[y]`, `0 ≤ i ≤ r`.”

  Therefore neither a boolean `OneSided` table nor the terminal
  `FGMNSourceData.normalizedResidual` can stand for the level-general objects.

Finally, the root ambient is fixed at the start of §6, published p. 25:

> “Let `F ∈ P` be a prime polynomial and fix `θ ∈ K̄_v` a root of `F`.”

That printed type is the reason for the new `CompletedRootAmbient`; it cannot be supplied by the
landed residual-field ambient.

## 3. Gap analysis against the landed CC layer

| Corollary 6.3 ingredient | landed CC supply | verdict after CC |
|---|---|---|
| Repository polynomial keys at every live level | `KeyChain.keyAt`, `keyAt_monic`, `keyAt_degree`; S2 depth-two bridge landed | **CARRIED** on the repo side. Still needs the equality to the source `φ_i ∈ K_v[x]`. |
| Every truncated valuation `μ_i` | `NodePointSource.hgt i` and terminal `FGMNSourceData.nextValue` | **MISSING.** `hgt i` has stage laws but no Definition 1.6 augmentation equation; `nextValue` is only the one terminal/next valuation. |
| MacLane-chain condition | key sharing only | **MISSING.** No `μ_i`, hence no source `φ_{i+1} ≁_{μ_i} φ_i`. |
| Numerical `ν_i,e_i,f_i` | `W.u`, `W.e`, `W.f`, `W.ehat`; exact Laurent solve landed | **CARRIED numerically**, but the equations identifying them with the source MacLane invariants are **missing dictionaries**. |
| Newton polygons `N_i(F)` | per-level value tables; old `dv` polygons at special repository levels | **MISSING level-generally.** No target-specific `N_{μ_{i−1},φ_i}(F)` tied to a canonical key expansion. |
| Side lengths `ℓ_i` | no field or definition | **MISSING.** They are theorem outputs, not tower inputs. |
| Source residual fields `F_i` | abstract repo fields `W.fld i`, base/step equivalences, `TerminalReceiver` | **PARTLY CARRIED.** The repo tower exists; source `F_i` and the per-level equivalences/transition compatibility do not. |
| Per-level residual operators `R_{i−1}` | `FGMNSourceData.gradedResidual` and `normalizedResidual` only at the terminal/next augmentation | **MISSING level-generally.** A truncation family cannot be reconstructed from the terminal operator. |
| Per-level `z_i,ψ_i` | repo `W.ψ i`, `ambientLetter`, `psi_root`, `letter_compat` | **PARTLY CARRIED.** Repo letters/minimal polynomials exist on their live range; the source `F_i` objects and the twist/index dictionaries remain missing. |
| Prime target `F` and top key `φ` | terminal `keyPolynomial` predicate; C.90(a)'s candidate `Φnext` | **MISSING as a Cor 6.3 occurrence.** No target-specific prime/root/`μ`-divisibility/non-equivalence bundle exists. |
| `θ ∈ K̄_v`, `F(θ)=0`, extended valuation `v` | `NodePointSource.Point`, `coord : Point → L`, `valueOn` | **Genuinely missing and not reusable.** `L` is over a residue field, not the completed fraction field. |
| Exact values `v(φ_i(θ))` | `NodePointSource.key_value` at legal residual node points | **MISSING for FGMN roots.** The landed equality is about a different ambient and different points. |
| `F ∼_{μ_{i−1}} φ_i^{ℓ_i}` and degree equality | terminal `initialEquiv`; ordinary polynomial degree APIs | **MISSING level-generally.** Only the degree arithmetic is already available after the source equivalence is supplied. |
| Residual powers and length recurrence | terminal residual multiplicativity; `W.e`,`W.f` | **MISSING as Cor 6.3 outputs.** They must not be input fields. |

The useful CC contribution is nevertheless large: the new layer does not need to redesign keys,
normalizers, residue towers, stage reads, or terminal calculus packaging. It only adds the source
objects and the dictionaries that U7 could not previously even name.

## 4. Decided Lean signatures

### 4.1 Definitions that prevent opaque predicates

The scratch file defines, with actual bodies:

```lean
structure PolynomialValuation (K : Type uKv) [Field K] where
  toFun : Polynomial K → WithTop ℚ
  map_zero : toFun 0 = ⊤
  map_one : toFun 1 = 0
  finite_iff : ∀ g, toFun g = ⊤ ↔ g = 0
  map_mul : ∀ g h, toFun (g * h) = toFun g + toFun h
  map_add_ge : ∀ g h, min (toFun g) (toFun h) ≤ toFun (g + h)
  map_add_eq : ∀ g h, toFun g ≠ toFun h →
    toFun (g + h) = min (toFun g) (toFun h)

def MuEquiv (μ : PolynomialValuation K) (g h : Polynomial K) : Prop :=
  (μ.toFun (g - h) > μ.toFun g ∧ μ.toFun g = μ.toFun h) ∨ (g = 0 ∧ h = 0)

def MuDivides (μ : PolynomialValuation K) (φ g : Polynomial K) : Prop :=
  ∃ q, MuEquiv μ g (φ * q)

noncomputable def IsAugmentation
    (μ μ' : PolynomialValuation K) (φ : Polynomial K) (ν : ℚ) : Prop :=
  ∀ g,
    μ'.toFun g = (Finset.range (g.natDegree + 1)).inf fun s =>
      μ.toFun (dev φ g s) + s • (μ.toFun φ + (ν : WithTop ℚ))
```

`IsKeyPolynomial` is likewise a definition: monicity, `μ`-minimality, and primality for the
explicit `MuDivides` relation. `NewtonOneSided μ φ g ν ell` is tied pointwise to

```lean
newtonOrdinate μ φ g s = μ (dev φ g s) + s • μ φ
```

and asserts finite nonzero endpoints, no coefficients after `ell`, endpoint collinearity of
slope `-ν`, and the above-line inequality at every intermediate abscissa. Hence no free polygon
or free `OneSided` predicate occurs in the carrier.

### 4.2 New root and MacLane source layers

The exact elaborated fields are in the scratch authority. The public signatures are:

```lean
structure CompletedRootAmbient where
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O
  Kv : Type uKv
  [kvField : Field Kv]
  [kvAlgebra : Algebra O Kv]
  [kvFraction : IsFractionRing O Kv]
  Omega : Type uOmega
  [omegaField : Field Omega]
  [omegaAlgebra : Algebra Kv Omega]
  [omegaAlgClosed : IsAlgClosed Omega]
  [omegaAlgebraic : Algebra.IsAlgebraic Kv Omega]
  coeffHom : O →+* Omega
  coeffHom_eq : coeffHom = (algebraMap Kv Omega).comp (algebraMap O Kv)
  value : Omega → WithTop ℚ
  value_zero : value 0 = ⊤
  value_one : value 1 = 0
  value_finite_iff : ∀ a, value a = ⊤ ↔ a = 0
  value_mul : ∀ a b, value (a * b) = value a + value b
  value_add_ge : ∀ a b, min (value a) (value b) ≤ value (a + b)
  value_add_eq : ∀ a b, value a ≠ value b →
    value (a + b) = min (value a) (value b)
  value_restricts : ∀ a : O,
    value (coeffHom a) = natTopToRat (IsDiscreteValuationRing.addVal O a)
```

```lean
structure MacLaneChainSource (B : CompletedRootAmbient (O := O)) (r : ℕ) where
  mu : ℕ → PolynomialValuation B.Kv
  mu_restricts : ∀ i (a : B.Kv),
    (mu i).toFun (Polynomial.C a) = B.value (algebraMap B.Kv B.Omega a)
  mu_X_nonnegative : ∀ i, 0 ≤ (mu i).toFun Polynomial.X
  key : ℕ → Polynomial B.Kv
  nu : ℕ → ℚ
  nu_pos : ∀ i, StageLive r i → 0 < nu i
  key_is_key : ∀ i, StageLive r i → IsKeyPolynomial (mu (i - 1)) (key i)
  augmentation : ∀ i, StageLive r i →
    IsAugmentation (mu (i - 1)) (mu i) (key i) (nu i)
  macLane : ∀ i, GaugeLive r i → ¬ MuEquiv (mu i) (key (i + 1)) (key i)
  ramification residueDegree : ℕ → ℕ
  ramification_pos : ∀ i, StageLive r i → 0 < ramification i
  residueDegree_pos : ∀ i, StageLive r i → 0 < residueDegree i
  residualField : ResidualFieldFamily
  residual : (i : ℕ) → Polynomial B.Kv → Polynomial (residualField.carrier i)
  residueHom : (i : ℕ) → residualField.carrier i →+* residualField.carrier (i + 1)
  letter : (i : ℕ) → residualField.carrier (i + 1)
  psi : (i : ℕ) → Polynomial (residualField.carrier i)
  psi_spec : ∀ i, i < r →
    (psi i).Monic ∧ Irreducible (psi i) ∧ (psi i).coeff 0 ≠ 0
  psi_root : ∀ i, i < r →
    Polynomial.eval₂ (residueHom i) (letter i) (psi i) = 0
  psi_minimal : ∀ i, i < r → ∀ q,
    q ≠ 0 → Polynomial.eval₂ (residueHom i) (letter i) q = 0 →
      (psi i).natDegree ≤ q.natDegree
```

The separate `ResidualFieldFamily` is a bundled `ℕ → Type` with a `Field` instance at every
index. This is the object U7's “per-level residual fields” row required.

### 4.3 Repository dictionary and theorem input

`LevelGeneralDictionary A B M` carries exactly these identifications:

```lean
key_compat
stage_value_compat
slope_compat
ramification_compat
residueDegree_compat
residueEquiv
repoResidual
repoPsi
omega
repoPsi_twisted
residual_compat
psi_compat
```

Their important types are:

```lean
key_compat : ∀ i, StageLive r i →
  M.key i = (A.keys.keyAt i).map (algebraMap O B.Kv)

stage_value_compat : ∀ i, StageLive r i → ∀ g : Polynomial O,
  (M.mu (i - 1)).toFun (g.map (algebraMap O B.Kv)) = intTopToRat (A.node.hgt i g)

residueEquiv : (i : ℕ) → StageLive r i →
  M.residualField.carrier (i - 1) ≃+* W.fld i

residual_compat : ∀ i (hi : StageLive r i) (g : Polynomial O),
  (M.residual (i - 1) (g.map (algebraMap O B.Kv))).map
      (residueEquiv i hi).toRingHom = repoResidual i g

psi_compat : ∀ i (hi : StageLive r i),
  (M.psi (i - 1)).map (residueEquiv i hi).toRingHom = repoPsi i

repoPsi_twisted : ∀ i, GaugeLive r i →
  repoPsi i = wconj (omega i : W.fld i) (W.ψ i)
```

The `i-1 ↔ W.fld i` shift is explicit. It is the terminal GENTOW5 display's dictionary:
source `R_{i-1}`/`ψ_{i-1}` is read at repo level `i`. The top `repoPsi r` is not falsely
identified with `W.ψ r`, whose C.83 law is live only below `r`; target-specific
`terminalPsi_compat` identifies it with C.90's supplied `ψ'` instead.

The target occurrence is:

```lean
structure LevelGeneralInput
    (A : ChainRealization W Kt L e' f' u')
    (B : CompletedRootAmbient (O := O)) (M : MacLaneChainSource B r)
    (D : LevelGeneralDictionary A B M) (G topKey : Polynomial O)
    (terminalPsi : Polynomial (W.fld r)) where
  depth_pos : 0 < r
  target_monic : G.Monic
  target_prime : Irreducible (G.map (algebraMap O B.Kv))
  theta : B.Omega
  target_root : Polynomial.eval₂ B.coeffHom theta G = 0
  topKey_is_key : IsKeyPolynomial (M.mu r) (topKey.map (algebraMap O B.Kv))
  topKey_divides_target :
    MuDivides (M.mu r) (topKey.map (algebraMap O B.Kv))
      (G.map (algebraMap O B.Kv))
  topKey_not_equiv_last :
    ¬ MuEquiv (M.mu r) (topKey.map (algebraMap O B.Kv)) (M.key r)
  terminalPsi_compat : D.repoPsi r = terminalPsi
```

For GENTOW5's Theorem 6.2 special case, instantiate `G = topKey = Φnext`. Keeping the two
parameters separate preserves the full printed theorem and prevents that special case from
silently becoming the definition of the interface.

### 4.4 The cited output is not a carrier field

`Cor63Conclusion X` has exactly the six decided outputs:

```lean
ell
ell_pos
polygon_oneSided
root_value
initial_equiv
degree_eq
residual_power
length_recurrence
```

Here `ell` is data and `ell_pos` is its source-forced positivity; the remaining fields are the
five displays of Corollary 6.3, with one-sidedness and length kept together. The proposed
literature transcription has the shape

```lean
theorem fgmn_cor63 (X : LevelGeneralInput A B M D G topKey terminalPsi) :
    Cor63Conclusion X
```

and must be a faithful cite theorem. It is deliberately **not declared** in the scratch file.

`C90LevelGeneralPackage X` repeats the full output after repository transport. In particular its
residual clause is

```lean
D.repoResidual i G = D.repoPsi i ^ ell i
```

and its recurrence is

```lean
ell i = W.e i * W.f i * ell (i + 1).
```

The checked definition `Cor63Conclusion.toC90` proves these by `residual_compat`, `psi_compat`,
`ramification_compat`, and `residueDegree_compat`. This is packaging, not a second cite.

## 5. Honest field classification

No row below is a consumer conclusion.

| field group | class | exact source clause or repo role |
|---|---|---|
| `complete`, `Kv`, fraction-field algebra | repository/environment dictionary | C.90 already assumes adic completeness; `Kv = Frac(O)` models `K_v` only under that complete-DVR scope. |
| `Omega`, algebraic/algebraically closed structure, `coeffHom`, `value`, valuation laws, `value_restricts` | source obligation | §6 opening `θ ∈ K̄_v`; Theorem 6.2's `v(φ(θ))`; valuation extension/restriction to `v`. |
| `mu`, polynomial-valuation laws, `mu_restricts`, `mu_X_nonnegative` | source obligation | Definition 1.1's valuations extending `v` with `μ(x) ≥ 0`; inductive valuations in §3 and Theorem 6.2. |
| `key`, `key_is_key` | source obligation | §1.2 definition of key polynomials; no opaque `KP` predicate is introduced here. |
| `nu`, `nu_pos`, `augmentation` | source obligation | Definition 1.6 and chain display (4). |
| `macLane` | source obligation | §3.1's verbatim `φ_{i+1} ≁_{μ_i} φ_i`. |
| `ramification`, `residueDegree`, positivity | source obligation | §3.2 definitions of `e_i,f_i`. |
| `residualField`, `residueHom` | source obligation | §3.2's `F_i` and canonical embeddings. |
| `residual` | source obligation | §3.4's `R_i : K[x] → F_i[y]`; a future implementation must add the full Definition 3.13/3.15 construction laws needed by the cite proof. |
| `letter`, `psi`, `psi_spec`, `psi_root`, `psi_minimal` | source obligation | §3.3's `z_i` and “minimal polynomial of `z_i` over `F_i`”. |
| `key_compat` | repo dictionary LG-D1 | source `φ_i` equals the mapped landed `KeyChain.keyAt i`. |
| `stage_value_compat`, `slope_compat` | repo dictionary LG-D2 | source `μ_{i-1}`/`ν_i` normalization equals the landed stage read and `u_i/ê_i`. |
| `ramification_compat`, `residueDegree_compat` | repo dictionary LG-D3 | source `e_i,f_i` equal `W.e i,W.f i`. |
| `residueEquiv`, `residual_compat` | repo dictionary LG-D4 | source `F_{i-1},R_{i-1}` transport to `W.fld i` and `repoResidual i`. |
| `repoPsi`, `omega`, `repoPsi_twisted`, `psi_compat` | repo dictionary LG-D5 | source `ψ_{i-1}` transports to the post-D3i GENTOW5 twisted polynomial; no on-the-nose untwisted equality is assumed. |
| `target_monic`, `target_prime`, `theta`, `target_root` | source occurrence hypotheses | Theorem 6.2's prime `F` and `θ ∈ K̄_v` root. |
| `topKey_is_key`, `topKey_divides_target` | source occurrence hypotheses | Theorem 6.2's key and `φ |μ F`. |
| `topKey_not_equiv_last` | source occurrence hypothesis | Corollary 6.3's `φ ≁μ φ_r`. |
| `terminalPsi_compat` | repo dictionary LG-D6 | the terminal source minimal polynomial is C.90's supplied `ψ'`, not junk `W.ψ r`. |

Specifically absent from every input structure: `Cor63Conclusion`, `C90LevelGeneralPackage`,
`FGMNCalculus`, `SlotCarrier`, `BlockData`, a `OneSided` lookup table, root-value equalities,
residual-power equalities, side lengths, and length recurrences.

## 6. C.90 and the actual GENTOW5 consumers

### 6.1 What the signed Lean statement currently consumes

The enacted `leanspec` declaration `gentow5_key_certificate` is only C.90(a). Its conclusion is

```lean
(I r le_rfl).KP Φnext ∧
∃ w, w ≠ 0 ∧ (I r le_rfl).Rres Φnext = wconj w ψ'.
```

It projects only terminal `KP` and `Rres`. There is **no term-level Corollary 6.3 conclusion in
the current signature**, and `rg` finds no downstream term use of a C.90(b) theorem because that
theorem was never signed. Therefore the minimal fragment needed merely to elaborate today's
signed consumers is: **none**. The landed CC-16 `ChainRealization.toCalculus` already supplies
the conditional A-C.11 class used by C.90(a).

This does not dispose the booked mathematical clause. U9's Q7 decision and the blueprint require
the full C.90(b) package.

### 6.2 What the intended GENTOW5 proof actually uses

The terminal EFF.GENTOW5 clause (b) consumes all of the following:

1. the actual per-level polygon and one-sided slope;
2. the side length, including its `e_i f_i` recurrence;
3. exact intermediate root values, used to put recipe roots in the `P_i` loci and to obtain
   their nonemptiness;
4. `μ`-equivalence and the degree equality;
5. per-level residual powers, after the repo `wconj` dictionary;
6. the common prime/root occurrence tying all levels together.

The later intended proof of GENTOW5(c) uses the residual powers and one-sidedness in its
bottom-up deeper-read ascent before it says Theorem 6.2/Corollary 6.3 “pins the factor's data”.
The depth-four witness uses clause (b)+(e) for the exact value ladder and its polygon regression.
Thus a residual-power-only structure would not serve the intended consumers and would violate
the adjudicated Q7 decision.

### 6.3 Discharge route

For a C.90 occurrence, construct

```lean
X : LevelGeneralInput A B M D Φnext Φnext ψ'
```

from the key certificate and source dictionaries. Apply the faithful literature theorem to get

```lean
h63 : Cor63Conclusion X.
```

Then

```lean
h63.toC90 : C90LevelGeneralPackage X
```

is the entire Lean-side discharge. Interior residual polynomials rewrite through
`repoPsi_twisted`; the terminal polynomial rewrites through `X.terminalPsi_compat`. The
one-sidedness, exact root values, initial equivalence, degree equality, and recurrence remain
visible projections. C.90(a) and C.90(b) should be conjoined only in the eventual amended C.90
theorem; the source carrier itself contains neither conclusion.

## 7. Heavy-math cost and the minimal faithful stopping point

### 7.1 Exact cost of constructing the full source instance

The signatures elaborate with one new mathlib import,
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, but **constructing** an instance is much more
than an import change.

1. Mathlib supplies `AlgebraicClosure (FractionRing O)`, its `Field`, `IsAlgClosed`, and
   `Algebra.IsAlgebraic` instances.
2. Mathlib supplies the DVR valuation on a fraction field through
   `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`.
3. `Mathlib.RingTheory.Valuation.Extension` supplies the class
   `Valuation.HasExtension vR vA` and elementary consequences. At pinned v4.31.0, the file does
   **not** supply an existence theorem extending an arbitrary DVR valuation to
   `AlgebraicClosure (FractionRing O)`. That construction or a literature-backed replacement is
   a new theorem.
4. The repo has no general Lean definition of MacLane inductive valuations, their augmented
   valuations, graded algebras, Newton polygon operators, or FGMN residual polynomial operators.
   All of `MacLaneChainSource` therefore needs either a new formalization or carefully audited
   source obligations at the realization boundary.
5. The bridge from `[IsAdicComplete (maximalIdeal O) O]` to the completed valued fraction field,
   and the additive rational normalization of its algebraic-closure valuation, is not present in
   the CC layer.

This is not a 30–60 minute transcription. A concrete full `LevelGeneralInput` constructor is a
separate multi-day/multi-unit valuation-theory development, even before the FGMN theorem proof
is transcribed.

### 7.2 Minimal faithful fragment

The minimal faithful near-term landing is precisely the split checked here:

* land the explicit helper definitions and the **input-side** structures;
* keep `LevelGeneralInput` as an explicit hypothesis;
* declare a reviewed literature theorem only from that input to `Cor63Conclusion`;
* prove `Cor63Conclusion.toC90` in Lean core;
* keep current consumers conditional until a concrete source realization exists.

This fragment is useful: it makes C.90(b) stateable, preserves every published conclusion, and
exposes every missing construction as a named source or dictionary obligation. It does **not**
claim that the landed CC tower already realizes an algebraic-closure root or a MacLane calculus.

There is no honest smaller fragment for the adjudicated C.90(b). For the currently compiled
C.90(a)-only signature, no Corollary 6.3 fragment is needed at all.

## 8. 30–60 minute node plan

These nodes land the interface and conditional theorem route. They do not pretend that the full
source instance is a short-node task.

| node | minutes | dependencies | deliverable / exit condition |
|---|---:|---|---|
| LG-0 source predicates | 45 | C130fg, B.02 `dev` | Land `PolynomialValuation`, `MuEquiv`, `MuDivides`, `IsKeyPolynomial`, `IsAugmentation`, `newtonOrdinate`, `NewtonOneSided`; every predicate has a body and expansion pins. |
| LG-1 root ambient | 45 | LG-0, algebraic-closure import | Land `CompletedRootAmbient`; lint that no `Kt`, `L`, `NodePointSource.Point`, or residual letter is used as `θ`. |
| LG-2 residual-field family | 45 | LG-0 | Land `ResidualFieldFamily` and the `residueHom/letter/psi/root/minimal` portion of `MacLaneChainSource`; dependent-field instances elaborate. |
| LG-3 MacLane chain | 60 | LG-0, LG-2 | Land `mu/key/nu/augmentation/macLane/e/f`; Definition 1.6 and §3.1 anti-drift examples elaborate. |
| LG-4 dictionary A | 45 | LG-3, C130k/C130st | Land key, stage-value, slope, `e`, and `f` compatibilities; no theorem conclusion in the structure. |
| LG-5 dictionary B | 60 | LG-2, C105, C130tr/C130pt | Land source-field equivalences, per-level residual/psi transport, interior `wconj` law, and the terminal-psi fence. |
| LG-6 target input | 30 | LG-1, LG-3, LG-5 | Land `LevelGeneralInput`; check the GENTOW special case `G = topKey = Φnext` is typeable without asserting an inhabitant. |
| LG-7 theorem codomain | 30 | LG-6 | Land `Cor63Conclusion` and `C90LevelGeneralPackage`; audit that the former occurs only as a codomain and the latter only as a derived result. |
| LG-8 transport | 30 | LG-7 | Land `Cor63Conclusion.toC90`; `#print axioms` is Lean core only and all six clauses project. |
| LG-9 faithfulness entry | 45 | LG-7, paper print-read | Draft the exact `fgmn_cor63` cite statement and add the clause-by-clause faithfulness record; verify published numbering 6.2/6.3 and equation (23). |
| LG-10 C.90 amendment draft | 45 | LG-8, LG-9 | Draft, but do not silently enact, the C.90(a)+(b) signature using `C90LevelGeneralPackage`; consumer diff shows current C.90(a) unchanged. |
| LG-11 GENTOW5 consumer lint | 60 | LG-10 | Wire projection-only test theorems for P-locus/root values, residual powers, degree/length recurrence; prove no consumer can use a residual-only package as the full clause. |

Parallelism: LG-1 and LG-2 can follow LG-0 in parallel; LG-4 and LG-5 can follow LG-2/LG-3 in
parallel. LG-6–LG-11 are serial acceptance gates.

The concrete-instance campaign starts only after LG-11 and needs a separate design: valuation
extension to the algebraic closure, general augmented valuations, residual operators, and the
CC dictionary proofs. It must not be hidden as one nominal “LG-12, 60 minutes” node.

## 9. Final rulings

1. **U7 partially superseded:** keys, normalizers, repo residue fields, legal residual points,
   terminal transport, and one terminal FGMN package now exist.
2. **OPEN-LEVEL-GENERAL remains real:** truncated inductive valuations, target Newton polygons,
   source residual operators at every level, the completed-valued root ambient, and root
   evaluations still do not exist.
3. **No ambient reuse:** CC's `L` and node points are residual objects, not `K̄_v` and `θ`.
4. **Full output retained:** C.90(b) gets one-sided polygons, lengths, root values,
   `μ`-equivalence, degrees, residual powers, and the recurrence.
5. **No consumer conclusions in inputs:** the literature result is a separate codomain and
   `toC90` is Lean-core transport.
6. **Near-term honest landing:** the conditional source/input/result interface is feasible in
   the listed short nodes; construction of a full source instance is a separate heavy-math
   campaign.
