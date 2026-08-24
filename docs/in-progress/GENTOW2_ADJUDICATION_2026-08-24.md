# GSW — GENTOW2 signed-shape adjudication (proposed amendment A-C.12)

Date: 2026-08-24
Unit: GSW (statement adjudication, not transcription)
Status: **DECIDED** — 5 statements RE-SIGN (exact diffs below, orchestrator enacts), 5 HOLD
(named unformalized source math), 1 no-action manifest.
Elaboration authority: `leanfinal/scratch/GSW_check.lean` (`lake env lean` exit 0, zero
warnings; the one proof in it is Lean-core).

## 0. Verdict table

| node | signed name | verdict | one-line reason |
|---|---|---|---|
| C.99 | `gentow2_Bpp` | **RE-SIGN (a)** | add the source-stated B-1 normalizer supply; then a THEOREM of the A-C.11 class fields — **machine-certified** (`gentow2_Bpp_resigned_provable`, Lean-core) |
| C.99 | `theta_letter_valued` | **RE-SIGN (shape) + still BLOCKED (proof)** | same B-1 supply + exponents ℕ→ℤ (the signed ℕ-form overclaims the source); letter clause stays OPEN-LETTERS |
| C.100 | `gentow2_Bp`, `gentow2_Bp_unit_iff` | **HOLD (c)** | IS the B′ lemma itself; needs OPEN-EVAL-ISO (Prop 1.15/Thm 4.8 carrier) + polynomial-valued graded laws; no honest antecedent short of the conclusion |
| C.101 | `gentow2_B` | **RE-SIGN (a)** | add the source-stated recipe data + the per-slot B′ unit law as an explicit discharge-node hypothesis; then provable from `Rres_recipe` alone |
| C.102 | `letter_formula` | **HOLD (c)** | needs the γ-dictionary (OPEN-LETTERS) + OPEN-EVAL-ISO; U7 §8.4: the formula must be a THEOREM of that dictionary |
| C.103 | `gentow2_A` | **RE-SIGN (a)** | add the omitted `ψ₃(0) ≠ 0` antecedent + the recipe degree bounds; then provable from `KP_criterion`/`KP_irred`/`KP_keyAt`/`Rres_keyAt`/`nuEquiv_iff_Rres` |
| C.85 | `theta_dictionary` | **FALSE-AS-SIGNED (plausible) → RE-SIGN (a)** | GTC's s=t=0 collapse stands; counterexample construction specified (§7); re-signed with height-tied quantifiers |
| C.88 | `tower_slot_exact` | **HOLD (c)** | needs HE7 ANNEX R1-b/R1-c (untranscribed) + the norm↔root-value bridge (OPEN-ROOT-EVAL genre; U12's `CompletedRootAmbient` is the designed home) |
| C.88 | `tower_lift` | **HOLD (c)** | needs R1-c + the polynomial-valued graded expansion laws (eq (14) power reads, Cor 4.4(3) y-degree bounds, Lemma 3.17) absent from class AND carrier |
| C.106 | `#check` manifest | **NO ACTION** | derivative; assembles when its ten names land (GTC's disposition stands) |

## 1. The (b) RE-BASE option is rejected globally — CC-17 evidence

The mandate's option (b) was to re-sign consumers from `[FGMNCalculus …]` onto a
`ChainRealization` context so the OPEN-DICT laws become available as fields. Two facts kill
it:

1. **CC-17's verdict landed mid-adjudication** (`runs/wave-b/verdict_CC17.md`): the S2
   `ChainRealization` is NOT unconditionally inhabited. Its repository half is fully
   inhabited (`s2RepositoryRealization`), but `node`, `fgmn`, `fgmnLaws`, `grade_compat`
   (OPEN-DICT-2) and `letter_compat` (OPEN-DICT-4) are a blocked source frontier
   (`S2SourceFrontier`). Re-basing swaps one hypothesis carrier for another exactly as
   hypothetical today, gaining nothing on discharge.
2. **The carrier adds no law the blocked proofs need.** Its thirteen `FGMNSourceLaws` are
   field-for-field the A-C.11 class laws (CC-16 packaging, `C130pk.lean` design-§7 table);
   `grade_compat` ties `nextValue` to the node point read and `letter_compat` ties
   `fgmn.letter` to the ambient node letter — neither supplies the evaluation isomorphism
   (Prop 1.15/Thm 4.8), the γ-recursion (Def 3.12), eq (14) power reads, or Cor 4.4(3)
   y-degree bounds that C.100/C.102/C.88 consume. The two residue reads of `node` are
   *deliberately unrelated* (CHAIN_CARRIER_DESIGN §8).

So every decision below is (a) or (c), and the §10 statements stay conditional on
`[FGMNCalculus …]` — consistent with the enacted A-C.11 orchestrator decision
(PROJECT_STATE §3).

## 2. C.99 `gentow2_Bpp` — RE-SIGN, machine-certified provable

**GTA's block:** "The source assumes exact-grade ladder monomials and nonzero graded reads,
but the signature supplies no `ExactGrade` facts for `chainNorm`."

**Source quote (the added antecedents are EXACTLY these inputs)** — GENTOW2_PROOF S5.2
proof, ll.740–744:

> "Fix t, write d := f₃ − t ≥ 1, N := n̂₂(u₃), M := n̂₂(u₃d): ladder monomials, deg < m₃,
> single-point N₃-polygon, exact grades κ̄ resp. β_t (B-1)."

Three binder families transcribe this (grades in the cleared integer convention,
β_t = (f'−t)·u', κ̄ = u'):

```lean
    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNorm r (d * u')))
    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
      (I.chainNorm r (d * u')).natDegree < (I.keyAt r).natDegree)
    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNorm r (d * u') ≠ 0)
```

("exact grades … (B-1)" → `hnorm`; "deg < m₃" → `hnormdeg` (m₃ = deg φ₃ = `keyAt r`);
"ladder monomials" (nonzero, single-point polygon — their nonzero read is Cor 4.4(1) via
`Rgr_ne_zero`, which additionally needs `g ≠ 0`) → `hnormz`.)

**Provability certificate (the decisive check):**
`GSW_check.gentow2_Bpp_resigned_provable` PROVES the re-signed statement from the A-C.11
class fields alone — `Rgr_mul` iterated for the power law, `Rgr_ne_zero` at the B-1 supply,
field cancellation. `#print axioms` = Lean core. Note the certificate does not even consume
`hr`, `he'`, `hcop`, `hfloor` — the re-signed axiom keeps them (recorded scope; removing
binders is a different amendment).

**Suppliers.** Any honest instance realizes `chainNorm` monomials as actual ladder
normalizers, where B-1 (GENHN-2′ exactness, accepted corpus) states all three facts. At S2
concretely: the CC-17 `S2SourceFrontier` package (once inhabited, `grade_compat` +
`nextValue` realize `ExactGrade`; C130k's `LaurentNormalizer.exact_height` and C.97's
`s2Witness` ladder rows are the height side). The hypotheses travel with the instance, so
every §10 consumer that can produce `I` can produce them.

**Cascade flag (not enacted here):** C.89's `gentow5w_two` (docstring: "the i = 2 discharge
from C.99") and `gentow5w_one_shape` will need the same three families when their landing
unit runs; flagged for the next A-C amendment.

## 3. C.99 `theta_letter_valued` — RE-SIGN shape, proof stays BLOCKED

Two recorded shape defects repaired now (honesty invariant: known-overclaiming statements do
not stay signed), proof still blocked:

1. **Missing B-1 supply** — its first conjunct `thetaRatio 1 = 1` is the d = 1 cancellation
   of §2's algebra; unprovable without the same three families. Added.
2. **ℕ exponents overclaim the source.** S5.2's γ-calculus: "ϑ(t) = z₁^j z₂^k for
   grade-determined INTEGERS j, k"; at the LP1 pin ϑ(0) = z₂⁻¹z₁⁻⁵. The signed
   `∃ j k : ℕ` is equivalent only over fields where the letters have finite order — but the
   abstract-`W` statement carries no `Finite` instance. Re-signed to `∃ j k : ℤ` (zpow).

**Still BLOCKED (OPEN-LETTERS):** the letter clause needs the value-0-monomial residue laws
(Def 3.12 γ-construction + the exponent-lattice split "the value-0 Laurent monomials
x^i π^a Φ′^b form exactly the group ⟨γ₁, γ₂⟩", S5.2) — U7 §5's OPEN-LETTERS row verbatim:
"`letterZ` only supplies the final values after the missing transport". No class field, and
no `ChainRealization` field (`letter_compat` is a compatibility signature, not the
γ-recursion), expresses this. Cure: the U12-genre `MacLaneChainSource` letter/psi layer +
its dictionary (LEVEL_GENERAL_DESIGN §4.2/§4.3).

## 4. C.100 `gentow2_Bp` / `gentow2_Bp_unit_iff` — HOLD

C.100 is not a consumer of B′ — it IS LEMMA GENTOW2-B′(3)+(4) in ratio form
(`Rgr β g = u(β) · transported digit` with `u(β) = Rgr β (chainNorm 2 β)`). Its source proof
(S5.1) consumes, beyond the class:

* the **canonical evaluation identification** — "(R-repo) digit(g) := res(g(x₀)/n̂₂(β̂)(x₀))
  ∈ k(L2) ≅ K₂ … through the CANONICAL EVALUATION identification k(L2) ≅ F₃ [Prop
  1.15(1)/(2)]" and the grade-0 read law "R_{3,0}(ẑ_d) = d: the grade-0 degree-0 read is
  the F₃-algebra residue (Thm 4.8)" — U7 §5's **OPEN-EVAL-ISO** row verbatim: "the bridge
  used in the proof of C.100 … cannot be expressed by `ρ : W.fld 2 ≃+* AdjoinRoot T.ψ₂`
  alone";
* the **h-step division bookkeeping** (S5.1 (h-i)–(h-iv)): Lemma 3.17, Cor 4.4(1)/(3)
  y-degree arguments, eq (14) power reads — all POLYNOMIAL-valued graded facts invisible to
  the scalar class `Rgr` and absent from `FGMNSourceLaws`' thirteen fields;
* **B-1's no-cancellation clause** (digit 0 ⟹ strictly above) — the dv₂↔grade dictionary,
  OPEN-DICT-2 in dv₂ vocabulary.

Why not (a): any "added antecedent" strong enough to make the proof go through is B′(3)
itself (the statement), or the OPEN-EVAL-ISO laws as opaque hypotheses — exactly what U7 §5
fences ("do not create opaque fields for … Prop 1.12 or Theorem 4.3"). Why not (b): §1.
The A-C.11/Q6 re-sign (`hdeg : g.natDegree < T.D₂`, `hfree` deleted) is CORRECT and
preserved — GTA confirmed it survives; the block is the missing machinery, not the scope.

**Cure, named:** an evaluation-identification layer of the U12 genre — `residueEquiv` +
`residual_compat` (LG-D4) + a grade-0 evaluation law (Thm 4.8's transcription) over the
realized source package, plus the polynomial-valued "graded expansion pack" (eq (14),
Cor 4.4(3), Lemma 3.17) as `FGMNSourceLaws` extensions. When that lands, C.100 fires and
§5's `hunit` discharges.

## 5. C.101 `gentow2_B` — RE-SIGN

**GTA's block:** `Rres_recipe` requires exact-grade and degree-bound premises for every
`k2DigitLift`; the signed theorem omits them; and the conclusion's coefficient shape needs
the per-slot unit law (OPEN-EVAL-ISO inheritance).

**Source quotes.** Recipe data (S5 statement, ll.307–309):

> "Let the recipe data be as in the r3 box: k̂_t ∈ K[x] with deg k̂_t < deg Φ₂, dv₂-height
> u₃(f₃ − t), and K₂-digit residual class c_t ∈ K₂ = F₃ (a GENHN-2′ ladder lift; …)"

→ `hlift` (exact grade (f'−t)·u' per slot) and `hliftdeg` (deg < D₂ = deg Φ₂). The per-slot
unit law (S5 proof, the B′ consumption):

> "By LEMMA GENTOW2-B′(3)+(4) (S5.1, derived from the accepted corpus), with β = β_t the
> slot's grade: R_{3,β_t}(k̂_t) = u(β_t)·digit(k̂_t) = u(β_t)·c_t, the recipe's k̂_t having
> repo digit c_t by construction."

→ `hunit`. This is NOT silent bridging: B′ is the sibling node C.103's… i.e. node C.100,
HELD (§4); per the standing rule carried hypotheses must be discharge nodes — `hunit` IS
C.100 instantiated at `g := k2DigitLift T (c t) ((f'−t)·u')` composed with the k2DigitLift
read companion `repoRead (k2DigitLift T c β̂) = c` (the "repo digit c_t by construction"
clause — a C56a-deferred companion lemma, named below). When C.100 + that companion land,
`hunit` discharges and can be deleted by a recorded follow-up amendment.

**Provability after re-sign (sketch, class-level only):** rewrite `recipe3` by
`hkey : keyAt 2 = composedKey T`; fire `Rres_recipe` at `khat t := k2DigitLift T (c t)
((f'−t)·u')` (grades = `hlift`; degrees = `hliftdeg` converted through
`composedKey_natDegree_D₂` — landed, leanfinal C53c-consumed — via `hkey`); rewrite each
coefficient by `hunit`; `Finset.sum_congr`. No new mathematics.

**Zero-digit scope finding (recorded, no enactment):** the source recipe sets "k̂_t = 0 when
c_t = 0", but the signed `recipe3` applies `k2DigitLift` unconditionally and
`k2DigitLift T 0 m ≠ 0` in general (its `k2Coord` branch takes a choice-representative of
0), while `Rres_recipe` demands exact grades at ALL slots. The re-signed C.101 is therefore
honestly scoped to digit strings whose lifts all sit on-grade (suppliers with some c_t = 0
cannot prove `hlift` there). A zero-digit-faithful `recipe3` variant (sum over the support)
is a possible future re-sign if a consumer needs vanishing interior digits; at the current
consumers (f' = 1 witnesses; prescribed strings with a_t ≠ 0) the scope suffices.

**Suppliers:** `hlift`/`hliftdeg` — B-1 at the digit lifts (the k2DigitLift grade/degree
companions C56a explicitly defers; source states them as recipe data); `hunit` — C.100
(post-§4 cure) + the read companion.

## 6. C.103 `gentow2_A` — RE-SIGN

**GTB's block:** the only route to `I.KP g` is `KP_criterion`, whose 5th antecedent is
`(Rres g).coeff 0 ≠ 0`; the signed `hadm` omits the source's `ψ₃(0) ≠ 0`. Also the
Monic/natDegree legs need the k2DigitLift degree companion.

**Source quote (S4, ll.187–189):**

> "**THEOREM GENTOW2-A.** Let ψ₃ ∈ F₃[y] = K₂[y] be monic irreducible of degree f₃ ≥ 1
> with ψ₃(0) ≠ 0, …"

and its proof's (a): "R₃(Φ₃) = ψ₃ irreducible, ψ₃ ≠ y (ψ₃(0) ≠ 0)". Since the signed
statement names the residual `I.Rres (recipe3 …)` (hypothesis (ii) internalized via `hadm`),
the faithful transcription is a third `hadm` conjunct:
`(I.Rres (recipe3 T e' f' u' c)).coeff 0 ≠ 0`. This is exactly GTB's option (a).

The Monic/degree legs: rather than wait for the C56a-deferred `k2DigitLift` degree
companion, the source-stated recipe bound "deg k̂_t < deg Φ₂" is added as the antecedent
`hliftdeg` (same family as C.101's — one supplier serves both). With it, `Monic (recipe3 …)`
and `natDegree (recipe3 …) = e'·f'·(keyAt 2).natDegree` are mathlib degree arithmetic
(leading term `composedKey^(e'f')` monic of degree e'f'·D₂ via `composedKey_monic` +
`composedKey_natDegree_D₂` + `hkey`; every subtracted term has degree
≤ (D₂−1) + e't·D₂ < e'f'·D₂ since t < f').

**Provability after re-sign (sketch, class-level only):**
KP: `KP_criterion` (Monic ✓, degree ✓, `hadm.1`, `hadm.2.1`, `hadm.2.2`).
Irreducible: `KP_irred` (KP ✓, Monic ✓).
Non-equivalence — the source's own paragraph goes through: `KP (composedKey T)` from
`KP_keyAt (0 < 2)` + `hkey`; `nuEquiv_iff_Rres`; `Rres (keyAt 2) = 1` (`Rres_keyAt`); and
`Rres (recipe3 …) ≠ 1` since its natDegree is f' > 0 (`hadm.2.1`, `hf'`) while
`natDegree 1 = 0`. (Source: "R₃(Φ₂) = 1 by eq (14), while R₃(Φ₃) = ψ₃ with deg ψ₃ = f₃ ≥ 1
… so Φ₃ ≁_ν Φ₂ by Prop 5.7 (2)⇔(3)".)

**Suppliers:** the coeff-0 conjunct comes from the re-signed C.101's conclusion + `hc0`
(constant coefficient `Rgr (f'·u') (chainNorm 2 (f'·u')) · ρ.symm(…(c 0))`, nonzero by the
C.99-genre nonzero read and ring-equiv injectivity); `hliftdeg` as in §5.

## 7. C.85 `theta_dictionary` — FALSE AS SIGNED (plausible); RE-SIGN with tied quantifiers

**Step 1 — the falsity adjudication (mandate: decide first).** GTC's collapse argument is
CORRECT as logic: instantiating the signed `∀ s t A B` at `s = t = 0` with `θ 0 = 1` forces

    dv2Res (A·B) = dv2Res A · dv2Res B   for EVERY A, B with both reads nonzero,

i.e. the signed form is provable only if `dv2Res` (C38a) is exactly multiplicative on its
nonzero-read domain — and then θ collapses to 1 and the "dictionary" is empty. Verdict:
**plausible-but-unproven FALSE**. The source's own machine data exhibits the
multiplicativity defect ≠ 1 at tied heights:

* **Counterexample construction (specified, not yet Lean-realized).** Frame: the PE4 LP1
  tower (GENTOW2_PROOF S5.2 machine block): f₁ = 2 over q = 2 (z₁ ∈ F₄∖F₂, z₁³ = 1),
  level-2 data u₂ = 9, e₂ = 2 (γ₁ = x²/2, γ₂ = Φ′²/x⁹). Take A = B = n̂₂(19) = 4xΦ′ (the
  ladder normalizer at exact dv₂-height 19). The sealed decode pin (gentow2_pe4_decode.py,
  COC row, GREEN 14/0 under seal 23def87): res(n̂₂(19)²/n̂₂(38)) = z₁² ≠ 1 — the coherent
  digit of A² at height 38 is z₁² while each factor's digit is 1. If C38a's `dv2Res`
  returns the coherent digits at these three polynomials (its dvResPoly branch at the level
  side (9,2) must be evaluated — the remaining verification burden, hence
  plausible-but-unproven), then `dv2Res(A²) = z₁² · (dv2Res A)² ≠ (dv2Res A)²`, refuting
  the s = t = 0 instance. A decide-style Lean refutation at a concrete ℤ₂-witness DVR is an
  optional tooth; not required, since the re-sign supersedes the untied form.

**Step 2 — the tied re-sign (per the source).** The cited proof (EFF.GENTOW5.06–.10,
LEMMA GENTOW5-A1 = `spec/EFF-GENTOW5.md` .08) is graded:

> "c_j = iota(gamma_j) * theta_{mu2-j}^{-1}, theta_t := [n2hat(lam)(x0)]^t *
> [n2hat(t*lam)(x0)]^{-1} … with vartheta_t independent of x0 … given by the telescoping
> vartheta_{t+1} = vartheta_t * res(tau(t*lam, lam)) where tau(a,b) :=
> n2hat(a)n2hat(b)/n2hat(a+b) is the ladder cocycle."

θ is a function of the HEIGHT (the defect of the normalizer system under addition of
heights), so the quantifiers must tie `s`, `t` to the dv₂-heights of `A`, `B` — and the
product's exact height + pinned-ness are carried as hypotheses (the source gets them from
A0/GENHN-2′ ON THE LOCUS; the signed statement has no locus binder, so they are honest
hypotheses, suppliable by consumers on the locus). The re-signed form is §9's diff; the PE4
counterexample mode is absorbed exactly (at (s,t) = (19,19): θ(19)²/θ(38) = z₁²).
`θ 1 = 1` is retained: any solution re-gauges by a hom `χ(m) = c^m` to normalize θ(1)
without disturbing the law.

**Proof-readiness caveat (recorded):** even the tied form's proof needs the dv₂
grid-read ↔ graded-point dictionary (the dv-graded engine v2's C-carrier vocabulary,
`DV_GRADED_ENGINE_V2_2026-08-24.md`). Recommend: adjudicate the tied form against the
landing C.131′ engine before fleeting a proof unit — the engine's graded normal form is its
natural home. The re-sign removes the refutable collapse NOW; it does not claim
landability now.

## 8. C.88 `tower_slot_exact` / `tower_lift` — HOLD (both)

Source: EFF.GENTOW5.22 (LEMMA GENTOW5-C, (SLOT_i)+(LIFT_i)), whose proof is "ANNEX-THEOREM
R1-b/R1-c's proofs, re-based" (HE7_PROOF ANNEX R) — no Lean transcription of the annex
exists (GTC), and the four-clause instantiation consumes:

* `tower_slot_exact`: additionally the **norm↔root-value bridge** — the signed conclusion is
  in `addVal O (Algebra.norm O (AdjoinRoot.mk g C))` vocabulary; no class or carrier field
  mentions `addVal`/`Algebra.norm` (GTC checked all thirteen laws). This is the
  OPEN-ROOT-EVAL genre (U7 §5 Q9 row); the designed future home is U12's
  `CompletedRootAmbient` + `Cor63Conclusion.root_value` (LEVEL_GENERAL_DESIGN §4.2/§4.4)
  plus a Σ-over-roots norm lemma.
* `tower_lift`: the R1-c construction (normalizer at every height k > boundRec — the
  Frobenius-semigroup arithmetic, provable but unlanded — times inverse-twisted grade-0
  lifts, REDUCED below `Dcum r`); the reduction step is S5.1's h-step, needing eq (14)
  power reads, Cor 4.4(3) y-degree bounds, and Lemma 3.17 — polynomial-valued graded laws
  in neither `FGMNCalculus` nor `FGMNSourceLaws`. A re-sign that assumes the reduced
  realizer directly IS the conclusion; no honest (a) exists. (`boundRec` itself landed,
  GTC; its recursion matches .22's acceptance-fold display
  `bound_{i+1} = (l_{i+1}−1)u_{i+1} + e_{i+1}·bound_i` with l = e·f.)

**Cure, named:** (i) transcribe HE7 ANNEX R1-b/R1-c (a chapter-E-adjacent unit; the fold in
.22 records the annex at acceptance grade 2/2, so this is transcription, not new math);
(ii) extend `FGMNSourceLaws` by the graded expansion pack (eq (14)/Cor 4.4(3)/Lemma 3.17,
all published FGMN); (iii) for `slot_exact`, the U12 root ambient + norm bridge.

## 9. A-C.12 — exact unified diff (leanspec/Leanspec/ChapC.lean; orchestrator enacts)

All five hunks; context lines are byte-exact against HEAD. Elaboration authority for every
new shape: `leanfinal/scratch/GSW_check.lean` (stand-ins documented there: `W₂` for the
unlanded `T.deepTower hπ`; a local byte-mirror of `recipe3`).

### Hunk 1 — NODE C.99 `gentow2_Bpp`

```diff
     (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
-    (hfloor : e' * W.Econst r < u') {t : ℕ} (ht : t < f') :
+    (hfloor : e' * W.Econst r < u')
+    -- [A-C.12, 2026-08-24 RE-SIGN — GSW] the source-stated B-1 normalizer supply
+    -- (GENTOW2_PROOF S5.2 proof, ll.740–744: "N := n̂₂(u₃), M := n̂₂(u₃d): ladder
+    -- monomials, deg < m₃, single-point N₃-polygon, exact grades κ̄ resp. β_t (B-1)"):
+    -- the slot normalizer monomials sit at their exact grades, below the key degree,
+    -- and are nonzero.  Provability certificate: leanfinal/scratch/GSW_check.lean
+    -- `gentow2_Bpp_resigned_provable` (Lean-core, from the A-C.11 class fields alone).
+    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNorm r (d * u')))
+    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
+      (I.chainNorm r (d * u')).natDegree < (I.keyAt r).natDegree)
+    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNorm r (d * u') ≠ 0)
+    {t : ℕ} (ht : t < f') :
     I.Rgr ((f' - t) * u') (I.chainNorm r ((f' - t) * u')) * I.thetaRatio (f' - t)
       = (I.Rgr u' (I.chainNorm r u')) ^ (f' - t)
```

### Hunk 2 — NODE C.99 `theta_letter_valued`

```diff
     (hr : r = 2)   -- the same depth-2 scope fence as gentow2_Bpp
     (he' : 0 < e') (hf' : 0 < f') (hcop : Nat.Coprime u' e')
-    (hfloor : e' * W.Econst r < u') :
+    (hfloor : e' * W.Econst r < u')
+    -- [A-C.12 RE-SIGN — GSW] the same B-1 normalizer supply as gentow2_Bpp (the first
+    -- conjunct is its d = 1 cancellation; the letter clause reads the same monomials).
+    (hnorm : ∀ d, 0 < d → d ≤ f' → I.ExactGrade (d * u') (I.chainNorm r (d * u')))
+    (hnormdeg : ∀ d, 0 < d → d ≤ f' →
+      (I.chainNorm r (d * u')).natDegree < (I.keyAt r).natDegree)
+    (hnormz : ∀ d, 0 < d → d ≤ f' → I.chainNorm r (d * u') ≠ 0) :
     I.thetaRatio 1 = 1 ∧
-    ∀ t : ℕ, ∃ j k : ℕ, I.thetaRatio t = I.letterZ 1 ^ j * I.letterZ 2 ^ k
+    -- [A-C.12 RE-SIGN — GSW] exponents ℤ, not ℕ: the γ-calculus produces
+    -- "grade-determined INTEGERS j, k" (S5.2), negative at the LP1 pin
+    -- (ϑ(0) = z₂⁻¹z₁⁻⁵); over an abstract `W.fld r` the ℕ-form overclaims.
+    -- Letter clause remains BLOCKED on OPEN-LETTERS (GSW adjudication §3).
+    ∀ t : ℕ, ∃ j k : ℤ, I.thetaRatio t = I.letterZ 1 ^ j * I.letterZ 2 ^ k
```

### Hunk 3 — NODE C.101 `gentow2_B`

```diff
     (hcop : Nat.Coprime u' e')
-    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0) :
+    (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0)
+    -- [A-C.12 RE-SIGN — GSW] the source-stated recipe data (GENTOW2_PROOF S5,
+    -- ll.307–309: "k̂_t ∈ K[x] with deg k̂_t < deg Φ₂, dv₂-height u₃(f₃ − t), and
+    -- K₂-digit residual class c_t"):
+    (hlift : ∀ t, t < f' →
+      I.ExactGrade ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u')))
+    (hliftdeg : ∀ t, t < f' →
+      (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂)
+    -- — and the per-slot B′ unit law (S5 proof: "R_{3,β_t}(k̂_t) = u(β_t)·c_t"), the
+    -- C.100 discharge node applied at the used slots, carried EXPLICITLY because C.100
+    -- is HELD on OPEN-EVAL-ISO (GSW adjudication §4; delete by follow-up amendment when
+    -- C.100 + the k2DigitLift read companion land):
+    (hunit : ∀ t, t < f' →
+      I.Rgr ((f' - t) * u') (k2DigitLift T (c t) ((f' - t) * u'))
+        = I.Rgr ((f' - t) * u') (I.chainNorm 2 ((f' - t) * u'))
+          * ρ.symm ((towerLabelEquiv T hπ) (c t))) :
     I.Rres (recipe3 T e' f' u' c)
```

### Hunk 4 — NODE C.103 `gentow2_A`

```diff
     (c : ℕ → AdjoinRoot (towerLabel T)) (hc0 : c 0 ≠ 0)
+    -- [A-C.12 RE-SIGN — GSW] the source-stated recipe degree bound (S5 ll.307–309,
+    -- "deg k̂_t < deg Φ₂") — types KP_criterion's Monic/degree legs:
+    (hliftdeg : ∀ t, t < f' →
+      (k2DigitLift T (c t) ((f' - t) * u')).natDegree < T.D₂)
     (hadm : Irreducible (I.Rres (recipe3 T e' f' u' c)) ∧
-      (I.Rres (recipe3 T e' f' u' c)).natDegree = f') :
+      (I.Rres (recipe3 T e' f' u' c)).natDegree = f' ∧
+      -- [A-C.12 RE-SIGN — GSW] the omitted source antecedent (GENTOW2_PROOF S4,
+      -- ll.187–188: "monic irreducible of degree f₃ ≥ 1 with ψ₃(0) ≠ 0") —
+      -- KP_criterion's fifth antecedent; GTB's option (a):
+      (I.Rres (recipe3 T e' f' u' c)).coeff 0 ≠ 0) :
     I.KP (recipe3 T e' f' u' c) ∧ Irreducible (recipe3 T e' f' u' c) ∧
     ¬ I.nuEquiv (recipe3 T e' f' u' c) (composedKey T)
```

### Hunk 5 — NODE C.85 `theta_dictionary`

```diff
 axiom theta_dictionary {F : KeyFrame O π} {H₀ : ℕ} {hpin : F.Pin H₀}
     (T : TowerDatum F H₀ hpin) (hπ : Irreducible π) (hh : 1 ≤ F.h)
     [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)] :
+    -- [A-C.12 RE-SIGN — GSW] quantifiers TIED to the dv₂-heights per the source
+    -- (EFF.GENTOW5.08: θ_t is the normalizer-system defect at the HEIGHTS, telescoped
+    -- through the ladder cocycle τ(a,b) = n̂₂(a)n̂₂(b)/n̂₂(a+b)); the untied A-C.1 form
+    -- collapses at s = t = 0 to exact multiplicativity of dv2Res — plausibly FALSE
+    -- (PE4 LP1 cocycle pin res(n̂₂(19)²/n̂₂(38)) = z₁² ≠ 1; GSW adjudication §7).
+    -- Product exactness/pinned-ness carried as hypotheses (on-locus facts).
     ∃ θ : ℕ → AdjoinRoot (T.levelDatum hπ).r,
       θ 0 = 1 ∧ θ 1 = 1 ∧ (∀ t, θ t ≠ 0) ∧
       ∀ (s t : ℕ) (A B : Polynomial O),
-        dv2Res (T.levelDatum hπ) A ≠ 0 → dv2Res (T.levelDatum hπ) B ≠ 0 →
+        dv2Hgt (T.levelDatum hπ) A = (s : ℕ∞) →
+        dv2Hgt (T.levelDatum hπ) B = (t : ℕ∞) →
+        dv2Hgt (T.levelDatum hπ) (A * B) = ((s + t : ℕ) : ℕ∞) →
+        dv2Res (T.levelDatum hπ) A ≠ 0 → dv2Res (T.levelDatum hπ) B ≠ 0 →
+        dv2Res (T.levelDatum hπ) (A * B) ≠ 0 →
         θ (s + t) * dv2Res (T.levelDatum hπ) (A * B)
           = θ s * θ t * (dv2Res (T.levelDatum hπ) A * dv2Res (T.levelDatum hπ) B)
```

## 10. Shared findings and follow-ups (no enactment here)

1. **`TowerDatum.deepTower` preamble** (leanspec ll.2420–2427) is still unlanded in
   leanfinal (GTA/GTB's mechanical prerequisite) — C.100–C.103 cannot even be STATED there
   until a construction node builds the depth-2 `DeepTower` from `T`'s data. Independent of
   every verdict above; needs its own unit.
2. **`Rres_recipe` zero-digit scope** (§5's finding) — an A-C.11 class-field scope note,
   recorded here; revisit only if a consumer needs vanishing interior digits.
3. **C.89 cascade** — `gentow5w_two`/`gentow5w_one_shape` consume the C.99 genre and will
   need the B-1 supply binders when their unit runs.
4. **C.106** — assemble the `#check` manifest after the GTA/GTB/GSW-enacted names land.
5. **Refutation tooth (optional)** — a decide-style Lean evaluation of §7's LP1
   counterexample against C38a's `dv2Res` would upgrade "plausibly false" to
   machine-refuted; not required post-re-sign.
