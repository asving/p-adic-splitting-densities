# MovesD RATIFICATION — Codex verdict (deferred final, 2026-07-28)
# Charge: as-built statement ratification vs §D4-R 4580-5436 + W4-SYNC seam types
# ORCHESTRATOR ADJUDICATION: D1 OVERRULED (two-scale convention, C.1.0(c)); D3 core OVERRULED (eta-granularity + PresentNorm dictionary), residue accepted; D2/D4/D5/D6 ACCEPTED. Repair charge: /tmp/ratrepair_d_charge.md (executed this session).

I’ll audit the typed interfaces rather than proof bodies, with special attention to quantifier ranges, empty/degenerate models, and the four W4 seam contracts. I’ll treat the seam’s deliberate openness as permitted and report only type mismatches or core semantic defects.

The first high-risk issues are in the shared vocabulary, not the algebraic proofs: the encoded shape’s γ law differs from the note once the accumulated stretch is nontrivial, and the unified empty-prefix event is split into incompatible Lean objects. I’m checking whether the surrounding bridge declarations genuinely repair those meanings or only repair selected counts.

The bridge work does repair some arithmetic (notably `C_∅ = 1` and the standalone full-box count), but it does not repair the meanings of `Presented.event` and `Presented.mult` at the empty shape. I also found that the finite-level wrapper uses the geometric `NPband` threshold without a typed `NP_ID` premise, exactly where the blueprint says equivalence to L12 is conditional.

## Findings

### 1. CRITICAL ERROR — γ has an extra stretch factor

Lean:

```lean
gamTie : ∀ (r : ℕ) (hr : r < P.reads.length),
  (((P.reads[r]'hr).gam : ℤ) : ℚ)
    = ((P.reads[r]'hr).e : ℚ) * ((P.strS r : ℚ) * (P.reads[r]'hr).ustar)
      + ... * ((P.reads[r]'hr).h : ℚ)
```

Note L3:

```text
γ_r := e_r·u*_r + j*_r·h_r
```

Lean asserts `γ = e·STR·u* + j*h`, while the note asserts `γ = e·u* + j*h`. These differ whenever `strS r ≠ 1`. Because `ShapeWF.gamTie` restricts the quantified shape universe and `anchorTie` consumes `gam`, this changes the meaning of later-read shapes rather than merely changing a derived presentation.

Both concrete gates have `strS = 1`, so they cannot detect this defect.

### 2. CRITICAL ERROR — the offset-P policy is not a typed hypothesis

Lean admits every lift-blind deterministic rule:

```lean
structure CanonPolicy ... where
  liftOf : Node p F → Polynomial ℤ_[p]
  blind : ∀ (ν : Node p F) (t : Polynomial ℤ_[p]),
    liftOf { ν with lift := t } = liftOf ν
```

All principal results quantify over an arbitrary:

```lean
{pol : CanonPolicy p F}
```

Note L1/L2:

```text
The classifier is run with ONE lift rule: ... the (S6b) OFFSET-P-LIFT realizer ...
All histories in this note carry these lifts and no others.
```

`blind` says only that the rule does not inspect the existing lift. It does not type the offset-P formula, prescribed residual class, weight law, or L1 totality property. `Presented.hnorm` also contains none of those conditions.

Thus the corpus’s `PrefSet`, `CD`, and mass laws are policy-parametric objects, not the fixed canonical-policy objects of §D4-R. The comments’ references to “POL-PIN/HC-1” do not supply the required typed hypothesis package.

### 3. CRITICAL ERROR — `PrefIdx` adds normalization and an image quotient

Lean first strengthens canonicality:

```lean
noncomputable def CanonPolicy.IsCanonPres ... :=
  pol.IsCanon H ∧
  ∀ r hr,
    (((H.nodes[r]'hr).zbar : Fˣ) : F) = canonRoot (H.nodes[r]'hr)
```

and then defines the counted type as an image:

```lean
abbrev PrefIdx ... :=
  ↥(etaData (P : ShapePrefix) '' PrefSet n pol P)
```

The purported counting theorem is definitionally tautological:

```lean
theorem card_classes (hnorm : PresentNorm n pol P) :
    Nat.card (PrefIdx n pol P)
      = Nat.card ↥(etaData (P : ShapePrefix) '' PrefSet n pol P) :=
  rfl
```

Note L3:

```text
Pref(P̂) := { η : shape(η) = P̂, η realizable, canonical lifts },
C_P̂(p) := #Pref(P̂).
```

and:

```text
C_P̂(p) a literal finite count of realized value prefixes — no quotient
```

The note fixes canonical lifts only; it does not impose `zbar = canonRoot`, and it counts the literal prefix set rather than the image of that set under a reduced data map.

`PresentNorm` does not state a bijection between the note’s literal prefixes and `PrefIdx`; in particular, it does not give injectivity of `etaData` on `PrefSet`. Therefore neither the extra normalization nor possible image collapse is eliminated by a typed theorem.

### 4. CRITICAL ERROR — the empty-prefix event and multiplicity are wrong

Lean proves that its history-level prefix set is empty:

```lean
theorem Pref_empty_shape ... :
    PrefSet n pol P = ∅ ∧ P.CD pol = 1
```

But the main event and multiplicity remain indexed by `PrefIdx`:

```lean
def Presented.event (S : Presented ...) : Set (Box p m) :=
  ⋃ i, S.fiber i

noncomputable def Presented.mult ... (x : Box p m) : ℕ :=
  Nat.card {i : PrefIdx n pol P // x ∈ S.fiber i}
```

Consequently, at `P̂ = ∅`, `Presented.event = ∅` and `Presented.mult x = 0`.

Note L5/L6/L12:

```text
S(∅,⊤) = the FULL BOX
Pref(∅) = {∅}
```

and hence:

```text
mult_∅(f) = #{η ∈ {∅} : η ∈ T_can(f)} = 1.
```

`PrefOpt` and `emptyFiber` separately encode the right objects, but they are not wired into `Presented.event`, `Presented.mult`, or `Presented.fiber`. The standalone `emptyShape_law` repairs one numerical identity only; it does not repair the definitions advertised as the uniform event and multiplicity.

This is also a concrete non-vacuity failure: an empty-shape `Presented` object can have an empty event even though the note requires the full box.

### 5. CRITICAL ERROR — D4R.4 uses `NPband` without typed `NP_ID`

Lean defines:

```lean
noncomputable def Shape.NP ... :=
  if Nonempty (PrefIdx n pol P)
  then (P : ShapePrefix).NPband n
  else 1
```

and states:

```lean
theorem D4R4_all ... :
  ∀ (N : ℕ) (hNP : P.NP pol ≤ N), ...
```

Note L12 instead defines:

```text
N(P̂) := max_{η ∈ Pref(P̂)} N(η, ⊤)
```

on the nonempty branch.

The seam contract explicitly records that replacing this maximum by `NPband` is valid only through the typed pin:

```text
NP-ID ... every transported-system equation level is a band level and conversely
```

No `NP_ID` declaration or hypothesis occurs in the corpus. Indeed `Defs.lean` says:

```text
NP-ID (W4-4) is a ledger pin, no Lean object
```

Therefore the quantifier range in `D4R4_all` is not the range displayed in L12. A comment pointing to W4-4 cannot serve as the required typed conditionality package.

### 6. GAP — the sealed gate is only partially stated

`G1_gates.lean` expressly omits:

```text
the classifier-side gate numbers
(C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1)
... not statable as closed shape arithmetic here.
```

But §D4-R.6 displays typed mathematical obligations including:

```text
C_P̂*(2) = 3 and C_P̂*(3) = 48
```

the four exact finite-level event counts, `mult_P̂* ≡ 1`, and the FC8/FC9 partition checks.

The corpus types and proves only the shape-side values such as `W = 7`, `M = 1`, `A = 11`, and `NPband = 5`. This leaves the sealed classifier-side falsifiers unrepresented. It is an incomplete gate interface, though it does not falsify the shape arithmetic that is present.

## Seam assessment

- W4-1 and W4-2 are absent consistently with the seam split; I did not count their deliberate openness or the resulting structural `TreeModel` degeneracy against the E-phase core.
- W4-3’s existing pins `D4R_CYL` and `ClassFiberWelldef` have the recorded consumer-side types.
- W4-4 is not merely open: its named typed pin is absent while `D4R4_all` uses the replacement threshold. That is finding 5.

The remaining top-locus, Theorem-C specialization, finite-prefix, pool/rank encoding, sum, union-bound, equality-criterion, fresh-band, coarse-bound, and structural prefix-closure statements match their cited displays or are faithful auxiliary lemmas.

Counts: 5 critical errors, 1 gap.

REJECT (5 crit / 1 gap)