# OM-8 — the deep-twist `∀ i ≥ 3` conjunct — unit note, 2026-08-16

**Charge.** Ledger rows **HYP.57** (`(H-VARTHETA-RES)_i`) and **HYP.63** (`[GENTOW5-W(i)]` /
`𝒲_(≤i)`) — the two halves of Display A's `∀ i ≥ 3 ((H-VARTHETA-RES)_i ∧ 𝒲_(≤i))` conjunct,
consumed at the **A-D.2 sitewise carrier form ONLY** (CHAP-D DECISION D-2, 2026-08-16: the
carrier is D.62's `HVarthetaRes G K L N v ρ q` against a GIVEN ambient residue datum `ρ` at the
level's use-height `q`; the committed existential form is `HVarthetaResVoided` and is VOID —
CHAP-I I.10's dated consumption note item 2 is the governing fence). Mandate: outline from
sources; certify per step (exact numerics at deep letter-live frames, both characteristics,
plus constructed-counterexample attacks with defeat systems solved or proved infeasible);
prove certified steps (the `i ∈ {1,2}` corpus proofs may transcribe; the `∀ i ≥ 3` law is
expected CARRY — narrow it and pin the exact residual).

**Statuses used:** PROVED / CERTIFIED-OPEN / REFUTED(+repair) / REDUCES-TO(<node>) /
CITE-CANDIDATE.

**Verdict summary (details in §3):**

| row | obligation | verdict |
|---|---|---|
| HYP.57 | `(H-VARTHETA-RES)_i`, `∀ i ≥ 3` | **REDUCES-TO(letter-lattice factorization) on the tower path; the S2.1-discharge adjudication (the row's own CARRY task) is performed: YES at DEF GENTOW5-1 instantiations, NO abstractly** (§3.1). The reduction theorem ϑ→τ→letters and the `i = 1` discharge are PROVED in Lean (`D62w.lean`); the depth-lattice factorization is PROVED in Lean at the exponent level for every depth (`latticeFactor`, §3.3); the abstract sitewise carrier stays genuinely ρ-dependent (defeat instance at REAL frame data, §2.3) — the residual is exactly chapter C's obligation to instantiate ρ as the canonical node-point residue read |
| HYP.63 | `𝒲_(≤i)`, `∀ i ≥ 3` | **REDUCES-TO(interleaved induction: base = landed GENTOW2 (b)@2; step = WI lemma [SOL row 18, 2/2]; chain = frozen GENTOW5's `𝒲_{≤n} ⟹ (a)@n ⟹ Cor 6.4 ⟹ (b)@n`)** — T5 S12.1's named re-verification obligation ("the induction closing the conjuncts from the empty base ... NOT performed by the companion as written") is PERFORMED here: footprint walk §3.2, induction skeleton PROVED in Lean (`wle_of_interleaved`), new machine coverage at the WI honesty-box's named gaps (≥3 slots, deeper alphabet, equal characteristic — §2.2) |

---

## §1. HIGH-LEVEL OUTLINE (what each row claims, exactly, from the sources)

### 1.1 HYP.57 — `(H-VARTHETA-RES)_i` — the row and its display

Ledger row verbatim (`spec/HYPOTHESIS_LEDGER.md`):

> HYP.57  `(H-VARTHETA-RES_i)`
> WHERE: `T1_GAUGE_COCYCLE_2026-08-12.md`, L3523–3541/§5 item 21; T5 honesty item 13.
> STATEMENT: For i≥3 and s≥0, res(n̂_i(u_(i+1))^s/n̂_i(su_(i+1)))∈K_i.
> CONSUMED BY: T1 B-law and C3-key, T5 consumers, and general tower path.
> CLASS: hypothesis-box
> PROPOSED DISPOSITION: CARRY — technical unit to adjudicate whether T5 S11.2 §S2.1 implies
> it; not an owner question.

The display of record, `EFF.T1.09` (unit [definition], `spec/EFF-T1.md`):

> ϑ_{i,s} = res( n̂_i(u_{i+1})^s / n̂_i(s·u_{i+1}) ) ∈ K_i^×    (C2-vartheta)
>
> "The membership ϑ_{i,s} ∈ K_i^× displayed in (C2-vartheta) is proved only at i ∈ {1,2}."
>
> At depth i≥3, every consumer must carry:
> (H-VARTHETA-RES)_i : res( n̂_i(u_{i+1})^s / n̂_i(s·u_{i+1}) ) ∈ K_i    (s ≥ 0).
>
> CONDITIONALITY: The quotient and residue exist from exact-height arithmetic. `K_i^×`
> membership is unconditional only for `i=1,2`, and supplier-dependent for `i≥3`.

**The `i ∈ {1,2}` corpus proofs (the transcribable slice), located.** T1 R9-2's fence text
(`lean/notes/openmath/T1_GAUGE_COCYCLE_2026-08-12.md`, the R9-2 block) names both:

> "at i=1 by direct evaluation ((C2-level-1): ϑ_{1,s} = η^{⌊s·i(u₂)/e₁⌋}, a power of
> η ∈ K₁^×); at i=2 by the accepted LEMMA GENTOW2-B″ γ-calculus (S5.2), which writes the
> value-zero n̂₂-quotient as a letter monomial and specializes it into K₂^×. At i≥3, T1 does
> not prove that the residue lies in K_i."

and classifies the general claim: "standard MacLane residual specialization, unproved here.
Under (H-VARTHETA-RES)_i, value zero makes the residue nonzero, whence ϑ_{i,s} ∈ K_i^×."

**The T5 carry (`EFF.T5.10` [hypothesis], verbatim core):**

> "Every i≥3 use of Θ_i(t) in this note carries the named hypothesis (H-VARTHETA-RES)_i
> alongside 𝒲_{≤i}. Whether S11.2's S2.1 monomial-quotient computation discharges that
> hypothesis is not adjudicated here."

with the conditionality rider: "This is a SECOND conditional stack on the same displays and
must not be conflated with 𝒲_{≤i}." That adjudication — HYP.57's disposition names it as the
technical unit's task, and CHAP-D routes it OPEN at D.64 ("that adjudication is nobody's in
this chapter") — is §3.1's business.

**The A-D.2 carrier (what "consumed at the sitewise form" means).** CHAP-D DECISION D-2
(blueprint, 2026-08-16): the Lean carrier is `EFF.T1.09`'s display verbatim, over the level's
height data `(N, v)` and a GIVEN ambient residue datum `ρ : ker v →* Lˣ`, at the level's fixed
use-height `q = u_{i+1}`:

```lean
def HVarthetaRes (G ...) (K ...) (L ...) [Algebra K L] (N : NormSection G)
    (v : G →* Multiplicative ℤ) (ρ : MonoidHom.ker v →* Lˣ) (q : ℤ) : Prop :=
  ∀ s : ℕ, ∃ (h : N.varthetaEl q s ∈ MonoidHom.ker v) (u : Kˣ),
    ((ρ ⟨N.varthetaEl q s, h⟩ : Lˣ) : L) = algebraMap K L (u : K)
```

Grounds 3 of D-2 (non-fabricability): "With ρ GIVEN, the trivial-hom trick dies: the
carrier's truth depends on where ρ sends the ϑ-quotients" — machine-certified FALSE at a
concrete instance (`verification/om4_resign_nontriviality.lean`). So the abstract carrier is
NOT a theorem of exact-height arithmetic; its truth is a property of the datum `(N, v, ρ)`.
The mathematical question is therefore: **for the data the corpus actually consumes — tower
normalizers with ρ = the node-point residue read — does the membership hold at every i ≥ 3?**

### 1.2 The S2.1 computation (the candidate discharge, quoted)

`GENTOW5_PROOF_2026-08-09.md` S2.1 (DEF GENTOW5-1) defines the tower-based normalizers by the
greedy ladder recursion,

> n̂_{i+1}(k) := n̂_i(m_i(k)) · Φ_i^{b_i(k)},  e_{i+1}·m_i(k) + b_i(k)·u_{i+1} = k,
> 0 ≤ b_i(k) < e_{i+1}   (unique since gcd(u_{i+1}, e_{i+1}) = 1)
> Unrolled: n̂_i(m) = π^a x^{i₀} Φ_1^{b_1} ... Φ_{i-1}^{b_{i-1}}, i₀ < e₁, b_j < e_{j+1}

the cocycle and the letters,

> τ_i(a, b) := n̂_i(a) n̂_i(b) / n̂_i(a+b); the level letters Λ_i := Φ_i^{e_{i+1}} /
> n̂_i(u_{i+1}) (dv-value 0 at level-(i+1) points), β_{i,ξ} := res(Λ_i(ξ))

and asserts, at the recipe display:

> "vartheta_{i,s} := res(n̂_i(u_{i+1})^s / n̂_i(s·u_{i+1})) in K_i^× is the FIXED telescope
> unit of the tau_i-cocycle ... At i ≥ 2, vartheta_{i,s} is the fixed letter monomial in
> η, β_1, ..., β_{i-1} through ι^{(i)} (S2.3 step (3)'s computation)."

S2.3 step (3) (LEMMA GENTOW5-C's proof, the τ_i-cocycle letter computation, accepted at the
annex acceptance grade — "the annex stack is now ACCEPTED 2/2"):

> "each theta_t has residue a fixed K_i^×-unit by the S1.2-style cocycle computation run at
> level i (the letter monomial — tau_i is a Laurent monomial in pi, x, Phi_1, ..., Phi_{i-1}
> of dv-value 0, residue a fixed product of the letters beta_1 ... beta_{i-1} through
> iota^{(i)})"

The WI note's step (iv) consumes exactly this shape at level i (its N^d/M is the s = d
ϑ-quotient inverse): "N^d/M is a value-0 Laurent monomial in pi, x, Phi_1, ..., Phi_{i-1}
..., so its residue is a FIXED letter unit by the level-i gamma-calculus."

**The mathematical core, isolated (this unit's organizing lemma).** Write the exponent
lattice ℤ^{i+1} for Laurent monomials π^v x^a Φ_1^{J_1}⋯Φ_{i-1}^{J_{i-1}}, and the dv_i
height functional

  φ_i(v, a, J_1, …, J_{i-1}) = ê_i·v + (ê_i/e₁)h·a + Σ_{j<i} (ê_i/ê_{j+1})u_{j+1}·J_j .

Distinguished value-zero vectors: the wrap `W₀ := x^{e₁}/π^h` and the letters
`Λ_j := Φ_j^{e_{j+1}}/n̂_j(u_{j+1})` (j = 1..i−1). **LATTICE FACTORIZATION:** if
gcd(h, e₁) = 1 and gcd(u_{j+1}, e_{j+1}) = 1 for all j, then every φ_i-value-zero vector is a
UNIQUE ℤ-combination of W₀, Λ_1, …, Λ_{i-1} (triangular descent: the top coordinate J_{i-1}
satisfies u_i·J_{i-1} ≡ 0 mod e_i because every other φ_i-coefficient is divisible by
e_i = ê_i/ê_{i-1}, so e_i | J_{i-1}; divide out Λ_{i-1}^{J_{i-1}/e_i} and recurse; the base
i = 1 case is e₁ | a from gcd(h, e₁) = 1, then the π-exponent vanishes identically). Hence
for ρ multiplicative on value-zero elements with ρ(W₀) = η, ρ(Λ_j) = β_j:

  res(any value-zero monomial) = η^{c₀}·β_1^{c_1}⋯β_{i-1}^{c_{i-1}} ∈ K_i^×,

since η ∈ K_1^× and β_j ∈ K_{j+1}^× ⊆ K_i^× (each β_j is a ψ_{j+1}-root — the P-locus
clause — and ψ_{j+1}(0) = c₀ ≠ 0 keeps it a unit). The ϑ-quotient n̂_i(u)^s/n̂_i(su) is such
a monomial (value s·u − s·u = 0), so (H-VARTHETA-RES)_i follows — indeed the K_i^×-form. This
is exactly "standard MacLane residual specialization" (R9-2's phrase) made into two
independently checkable legs: (L1) the lattice descent [pure ℤ-arithmetic, §3.3 Lean];
(L2) residue-hom multiplicativity + the letters' K_i-membership [the node-point read;
chapter C's instantiation data].

### 1.3 HYP.63 — `𝒲_(≤i)` — the row and the exact carry reason

Ledger row verbatim:

> HYP.63  `[GENTOW5-W(i)]` / 𝒲_(≤i)
> WHERE: `T5_WFRAME_2026-08-12.md`, L616, L926–930, L1499–1500; `Q4_output.log`.
> STATEMENT: Cumulative 𝒲_(≤i) required by frozen GENTOW5 holds for every i≥3.
> CONSUMED BY: T3/T5 higher-depth laws and G5-COND ride list.
> CLASS: conditional-theorem-leg
> PROPOSED DISPOSITION: CARRY — WI proves only the induction step, not induction from empty
> base.

The single-level law (the C.89 carrier's content; `GENTOW5_WI_2026-08-10.md` S1, byte-matching
GENTOW5_PROOF S11.2 @ b0e5c648 L1912–1913):

> [GENTOW5-W(i)]   u_i(β_t) = θ_i(t) · w_i^{f_{i+1}-t},   w_i = R_{i+1,k̄_i}(n̂_i(u_{i+1}))

The WI companion PROVES this at every level 3 ≤ i < r of a DEF GENTOW5-1 tower datum
(S2's four-step computation; SOL certification row 18, 2026-08-12: **CERTIFIED 2/2** — the
note-internal S7 "grade 0/2" box is stale, ledger HYP.140). What the ledger still carries is
T5 S12.1's governing caution (T5_WFRAME L920–930):

> "its r1 nonemptiness derivation does not survive as written (its clause-(b)-at-index-i leg
> now sits behind 𝒲_{≤i}, which would be circular there), so S1's 'with P_{i+1} nonempty'
> reverts to a recorded setting assumption. Whether that conditional step, and the induction
> closing the conjuncts from the empty base, survives on the companion's full footprint is
> the companion's own re-verification obligation; it is NOT performed by the companion as
> written and NOT assumed here."

with the frozen dependency chain displayed at T5 §4:

> 𝒲_{≤n} ⟹ (a)@n ⟹ Corollary 6.4 ⟹ (b)@n ⟹ S11.1.1/S11.1.3 ⟹ (c)@n ⟹ (e)@n ⟹ the
> next automatic floor.    (WF-chain)

So HYP.63's open content is NOT the single-level lemma (accepted) — it is the **closure
question**: does W(i) for all i ≥ 3 follow simultaneously, given that the WI step at level i
consumes clause (b) at index i−1 (its census item C-5), while (b)@(i−1) itself sits at the
end of the WF-chain from 𝒲_{≤i-1}? §3.2 answers by exhibiting the interleaved induction and
walking the footprint; the skeleton is proved in Lean.

### 1.4 The E/I consumption sockets (what downstream reads)

* CHAP-E E.61/E.62 (`leanspec/Leanspec/ChapE.lean`): BLOCKED sockets
  `structure VarthetaRes (i : ℕ) : Prop where supplied : True` (+ `WFrame i`), packaged as
  `DeepTwistConjunct : Prop := ∀ i, 3 ≤ i → VarthetaRes i ∧ WFrame i`, carrying the A-D.2
  fence comment: when typed, the socket MUST bind `LeanspecD.HVarthetaRes` (sitewise form)
  with the level-i instantiation data.
* CHAP-D D.63: `VarthetaWConjunct (HVR W : ℕ → Prop) (i : ℕ) : Prop := HVR i ∧ Wle W i`,
  instantiated at the A-D.2 sitewise `HVarthetaRes` + `W q := GentowW (level-q data)`.
* CHAP-I I.10: the `ladder` field's `.vartheta` projection reads BOTH rows at the re-signed
  forms only (the dated consumption note, item 2). Per the Part V owner ruling the conjunct's
  terminal disposition in chapter I is DISCHARGE NODE or LITERATURE CITE.
* CHAP-C C.89: the `𝒲` family — clause (i) `i = 2` discharged (`gentow5w_two`), clause (ii)
  `i = 1` shape with the `u1 = w₁` tie OPEN, clause (iii) `i ≥ 3` OPEN by design ("the
  definition IS the carrier; no axiom asserts it").

---

## §2. CERTIFICATION (exact numerics + attacks)

*Instrument:* `verification/om8_vartheta_deep.py` (predictions in the docstring, committed
before the run). **Run record: run 1 RED KEPT** (`logs/om8_vartheta_deep_output_run1_RED.txt`,
md5 `4276cb42` — both defects instrument-side: a gp `t_POL % t_INT` type error on the letter
digits, and a denominator typo `3^17·x·Φ₂` vs the LEG-A-verified `n̂₃(81) = 3¹⁷Φ₂`; two more
gp-dialect repairs, all comparison-side); **final run GREEN 52 checks / 0 failures,
bit-identical isolated re-run** (`logs/om8_vartheta_deep_output.txt`, md5 `47a0d42e`; runner
md5 `543a1dff`).

### 2.1 The lattice-factorization law (LEG A, characteristic-blind)

* **A1** — the F-LW3/F-P5 exponent chain (`e = (2,2,2,1)`, `h = 1`, `u = (1,5,21,43)`) and
  the F-A9 chain (`e = (2,1,2,1)`, `u = (1,3,13,27)`): the WI note's hand-derived lattice
  values reproduced by an independently re-derived descent (`n̂₃(43) = πxΦ₁Φ₂`,
  `n̂₃(86) = π⁹xΦ₁`, `n̂₃(129) = π¹³xΦ₂`; `θ₃(0)`-split `(−1,−1,−1)` = WI P-A3;
  `ϑ_{3,2}`-split `(1,1,1)`, `ϑ_{3,3}`-split `(2,2,1)`; A9-chain splits `(1,0,1)`/`(2,0,1)`),
  plus the recursion consistency `ϑ_{s+1} = ϑ_s·τ(su,u)` at exponent level for `s = 0..8`.
* **A2** — the sweep: **400 random valid tower data** (depths 3–6, `e_j, f_j ∈ 1..3` with
  `l_j ≥ 2`, `h ∈ {1,2,3}` with `gcd(h,e₁) = 1`, floor chain + gcd chain enforced), every
  level `i ∈ [3, depth]`, `s ∈ 0..6`: **7007 ϑ-quotient rows, every one value-zero and every
  one descending over `(γ₁..γ_i)` with integer exponents and zero remainder.** This is the
  defeat-system sweep: within the grammar, NO instance fails — the descent (§1.2's lemma) is
  the infeasibility proof, and the sweep is its executable shadow.
* **A3 (tooth)** — the gcd mutant `gcd(u₃, e₃) = 2` (`u = (1,5,22,45)`): the ladder/descent
  BREAKS. The grammar's coprimality is load-bearing — the fence is real, not decorative.

### 2.2 Mixed-characteristic oracle rows (LEG B, PARI — decorrelated from LEG A)

The genuine containment content of `(H-VARTHETA-RES)_i` is `K_i ⊂ L` with `L = K_{i+1}` the
AMBIENT residue field at the level-`(i+1)` points — so the ϑ-oracle rows run at the
DEPTH-4 fields, where the containment is proper.

* **B-LW3** (`p = 3`; WI's frame, reproduction + new containment rows): `Φ₄` has one prime,
  `(e,f) = (8,2)`, ladder `(4,10,21,43)`; letters `(2,2,2)`;
  `ϑ_{3,2} = res(n̂₃(43)²/n̂₃(86)) = 2 ∈ F₃ ⊂ F₉` and `ϑ_{3,3} = 2 ∈ F₃` — the
  membership measured AT the deep prime; NONMEMBER tooth: the level-4 class
  `Y = res(Φ₃/n̂₃(43))` generates `F₉` (the membership test discriminates); the WI W-law
  reproduced (`tr Y = w₃ = 1`, `norm Y = 2`).
* **B-P5** (`p = 5`; NEW frame — **the first `f₄ = 3` three-slot deep frame on the record**,
  closing the WI honesty-box item (4) slot-count gap): `Φ₁ = x²−10`, `Φ₂ = Φ₁²−50x`,
  `Φ₃ = Φ₂²−1250Φ₁`; depth-3 field `(e,f) = (8,1)`, ladder `(4,10,21)`, letters MEASURED
  `(2,2,2)`; `ϑ_{3,2} = 3`, `ϑ_{3,3} = 2` (letter-monomial values `2·2·2 = 8 ≡ 3`,
  `4·4·2 = 32 ≡ 2 mod 5`); coherent key `Φ₄ = Φ₃³ − 2·5⁹xΦ₁·Φ₃ − 3·5¹³xΦ₂`
  (`ψ₄ = y³+y+1`, digits `c_t·ϑ_{3,3−t}` from the MEASURED letters): **one prime,
  `(e,f) = (8,3)`**, ladder `(4,10,21,43)`; `ϑ_{3,2}, ϑ_{3,3} ∈ F₅ ⊂ F₁₂₅` measured at the
  deep prime, equal to the letter-monomial values; letter transport depth-3 → depth-4 prime
  exact. **The three-slot W-law**: `Y` generates `F₁₂₅`; `tr(Y) = 0` (slot `t = 2`,
  `c₂ = 0`); a UNIQUE `w ∈ F₅ˣ` has `ψ₄^{(w)}(Y) = 0` (measured `w₃ = 1`); `e₂(Y) = w²`
  (slot `t = 1`) and `norm(Y) = 4w³` (slot `t = 0`) — `[GENTOW5-W(3)]` at three slots.
  **Gauge-naive twin** (`digits 4,4`, no ϑ-twist): `factorpadic` SPLITS it — 2 primes,
  `(e,f) = (16,1) + (8,1)` — the certificate dies at composition, the strongest twin kill
  on the record (LW3's twin still had a single prime with wrong `f`).
* **B-A9** (`p = 3`; NEW frame — **the first deep ϑ measured OUTSIDE the prime field**,
  closing the WI honesty-box item (4) alphabet gap): `Φ₁ = x²−6`, `Φ₂ = Φ₁²−27`
  (`ψ₂ = y²+1` — `K₂ = K₃ = F₉`), `Φ₃ = Φ₂²−243Φ₁` (`ψ₃ = y − z₂`,
  `k̂₀ = lift₂(z₂;13) = 3⁵Φ₁`): one prime, `(e,f) = (4,2)`, ladder `(2,6,13)`; letters
  `g₁ = 2`, `g₂` a `ψ₂`-root (`g₂² = −1`, `g₂ ∉ F₃`), `g₃ = g₂` (`w₂ = 1` recorded);
  `ϑ_{3,2} = g₁g₃ = 2z₂` and `ϑ_{3,3} = g₁²g₃ = z₂` — **both in `F₉ ∖ F₃`**, equal to the
  letter-monomial values: the deep-twist membership `∈ K_i` is now measured at a frame where
  it is NOT a prime-field statement. (The A9 depth-4 containment row `F₉ ⊂ F₈₁` was not run
  — disclosed; the containment coverage is B-LW3's and B-P5's.)

### 2.3 Equal characteristic (LEG C — the first equal-char deep-twist rows)

F-EC3 over `F₃((t))`: `Φ₁ = x²−2t`, `Φ₂ = Φ₁²−2t²x`, `Φ₃ = Φ₂²−2t⁴Φ₁`,
`Φ₄ = Φ₃² − txΦ₁Φ₂·Φ₃ − 2t⁹xΦ₁` (the LW3 mirror; `ψ₄ = y²−y−1`). All rows by
`polresultant` over `F₃[t]` (`v_t(Res(Φ₄, g)) = 2·v_s(g)`): ladder `v_s = (4,10,21,43)`
exact; **membership rows `ϑ_{3,2} = 2 ∈ F₃` and `ϑ_{3,3} = 2 ∈ F₃`** (via
`v_s(Q − 2) > 0`, value-sharp against `r = 1`); NONMEMBER tooth: `Y = Φ₃/n̂₃(43)` avoids
every `F₃`-residue (generates `F₉`). Both characteristics now covered at `i = 3`.

### 2.4 The defeat systems (LEG D + A3)

* **D1 (within-grammar): INFEASIBLE.** The defeat system {DEF GENTOW5-1 datum, level
  `i ≥ 3`, `s ≥ 0`, `res(ϑ-quotient) ∉ K_i`} is infeasible: the lattice factorization
  (§1.2, PROVED — §3.3's Lean) forces `res = η^{c₀}∏β_j^{c_j}`, a `K_i^×` letter monomial,
  whenever the residue read is multiplicative and the letters are the node-point classes.
  The infeasibility IS the lemma (per the constructed-counterexamples discipline); the
  sweep (A2, 7007 rows) and the gcd-mutant tooth (A3) are its executable shadow and its
  boundary: drop one rung's coprimality and the ladder itself breaks.
* **D2 (the ρ-twist, at REAL frame data): the abstract carrier genuinely FAILS.** On
  F-LW3's actual value-zero exponent lattice (free basis `γ₁, γ₂, γ₃` — pivots
  `e₁e₂e₃ = 8 ≠ 0`), the adversarial datum `ρ′: (γ₁, γ₂, γ₃) ↦ (2, 2, ω)` with
  `ω ∈ F₉ ∖ F₃` is a legitimate MonoidHom on `ker v` (exact-height untouched), and
  `ρ′(ϑ_{3,2}\text{-element}) = ω ∉ F₃` — the sitewise carrier FAILS at the same exponents
  where the canonical read gives `2 ∈ F₃`. This is `om4_resign_nontriviality`'s mechanism
  executed at real tower exponents: **no exact-height argument can discharge the A-D.2
  carrier without pinning `ρ` to the canonical node-point read.** That pinning is exactly
  chapter C's instantiation obligation (and the E.61 socket-typing fence, §4).

---

## §3. ADJUDICATIONS, PROOFS, AND THE PINNED RESIDUALS

### 3.1 HYP.57 — the S2.1-discharge adjudication (the row's named CARRY task, performed)

**The question** (row disposition: "technical unit to adjudicate whether T5 S11.2 §S2.1
implies it"; `EFF.T5.10`: "Whether S11.2's S2.1 monomial-quotient computation discharges
that hypothesis is not adjudicated here"; CHAP-D routes it OPEN at D.64/D.62's SOURCE:
"that adjudication is nobody's in this chapter").

**VERDICT: YES at every DEF GENTOW5-1 instantiation with the canonical node-point residue
read — for ALL `i ≥ 3` and ALL `s ≥ 0` simultaneously — and NO for the abstract sitewise
carrier at an arbitrary ambient datum `ρ` (machine-refuted, §2.4 D2). The discharge
decomposes into three legs, each independently certified:**

* **(L1) The lattice factorization** (the mathematical core, isolated in §1.2 and PROVED —
  the general-`i` argument in full): under the grammar's gcd chain
  (`gcd(h,e₁) = gcd(u_{j+1}, e_{j+1}) = 1`), every `dv_i`-value-zero Laurent monomial in
  `(π, x, Φ₁, …, Φ_{i−1})` — in particular every ϑ-quotient and every τ-value — factors
  UNIQUELY over the letter generators `W₀ = x^{e₁}/π^h`, `Λ_j = Φ_j^{e_{j+1}}/n̂_j(u_{j+1})`
  by triangular descent (top coordinate: `u_i·J_{i−1} ≡ 0 mod e_i` because every other
  `dv_i`-coefficient is divisible by `e_i`, then `e_i | J_{i−1}` by coprimality; divide out
  `Λ_{i−1}` and recurse; base `i = 1` is `e₁ | a` from `gcd(h,e₁) = 1`). This is EXACTLY
  GENTOW5_PROOF S2.3 step (3)'s "τ_i is a Laurent monomial … of dv-value 0, residue a fixed
  product of the letters" — accepted at the annex grade — INDEPENDENTLY re-derived here and
  now doubly machine-legged: Lean-general (`triangular_descent` + `dvd_stage`,
  `leanfinal/Uniformity/ChapD/D62w.lean` §5), Lean-concrete at depths 2 and 3
  (`deep2_tau_descent`, `deep3_tau_descent` — ALL heights, not just the consumed ones), and
  swept at 400 random frames / 7007 rows (§2.1).
* **(L2) Residue multiplicativity at node points**: at `ξ ∈ P_{i+1}` every monomial factor
  sits at its exact value (the P-locus clauses), so the value-zero quotient is a unit of the
  local ring at `ξ` and its residue is the product of the factors' residues — standard
  valuation theory, the leg S2.3 step (3) consumes silently. Machine-covered: the direct
  PARI/equal-char residue measurements (§2.2/§2.3) agree with the letter-monomial values at
  every frame, both characteristics.
* **(L3) The letters lie in `K_i`**: `β_j = res(Λ_j(ξ))` is (a `w_j`-twisted) `ψ_{j+1}`-root
  — the P-locus/realized-residual clause — hence in `K_{j+1}ˣ ⊆ K_iˣ` (nonzero because
  `ψ_{j+1}(0) = c₀ ≠ 0`, and a `w`-twist multiplies by `w_j ∈ K_jˣ`). Measured: `(2,2,2)`
  at LW3 and P5; `(2, z₂, z₂)` at A9 — the first non-prime-field instance.

Under (L1)–(L3), `res(n̂_i(u_{i+1})^s/n̂_i(su_{i+1})) = η^{c₀}∏β_j^{c_j} ∈ K_iˣ` — the
displayed `(H-VARTHETA-RES)_i`, in its `K_iˣ` form, for every `i ≥ 3` and `s ≥ 0` at once.

**The two honest caveats (why the row still carries):**

1. **ρ-dependence (the A-D.2 boundary).** The sitewise carrier is a property of the datum
   `(N, v, ρ)`; §2.4 D2 exhibits a legitimate `ρ′` at REAL tower exponents where it fails.
   So S2.1 discharges the carrier exactly AT the canonical read — when E.61's BLOCKED socket
   is typed (GC-13/GC-14), it must bind chapter C's canonical node-point residue data;
   binding an unpinned `ρ` would leave the conjunct undischargeable, and the I.10 fence
   (no voided form) stays as is.
2. **T1's own normalizer convention.** T1's sites read T1's `n̂` system (HE7-2′-based),
   which "differ[s] per height by a fixed unit" from the tower system (S2.3's remark, proved
   at level 1). At general depth the bridge REDUCES TO (L1) itself: both systems' normalizers
   are ladder monomials in `(π, x, Φ_j)`, so the per-height discrepancy unit is a value-zero
   monomial and its residue is a letter monomial by the same lattice lemma — the ϑ's of the
   two systems differ by a `K_iˣ` factor, and membership transfers. (This resolves the
   convention bridge in principle; the SITE-BY-SITE check that every T1 `i ≥ 3` consumption
   presents a ladder-monomial system is not re-walked here — it is the same walk as T1's own
   `(C3)` bundle supply, riding the D.29-instantiation obligation at D.64's OPEN-CALL-5 row.)

**Row effect.** The adjudication the disposition asked for is DONE (recorded §4). The
conjunct itself stays CARRY — its Lean discharge is now a WIRING obligation (type E.61's
socket at the A-D.2 carrier with the canonical instantiation data; instantiate
`hvarthetaRes_deep3`-style letter-membership hypotheses from chapter C's letter layer), not
an open depth-`i` residue law. That is the narrowing: **before this unit the `∀ i ≥ 3`
ϑ-half was an unproved deep-residue law fenced per depth; after it, the law is proved at
the tower path (three legs, each double-checked), and what remains open is (i) the canonical-
read pinning at socket-typing time and (ii) the T1 site-by-site convention walk — both
supply-side, neither a new mathematical unknown.**

### 3.2 HYP.63 — the induction from the empty base (T5 S12.1's named obligation, performed)

**The question.** T5 S12.1 (the governing text for the row's CARRY): "Whether that
conditional step, and the induction closing the conjuncts from the empty base, survives on
the companion's full footprint is the companion's own re-verification obligation; it is NOT
performed by the companion as written and NOT assumed here."

**The interleaved-induction shape** (now PROVED as a skeleton — `wle_of_interleaved`,
`D62w.lean` §4). Instantiate `W i := [GENTOW5-W(i)]` at the datum and `B j :=` clause (b) of
THEOREM GENTOW5-B at index `j` (recipe roots of `Φ_{j+1}` are `P_{j+1}` node points with
exact monomial values). Then:

* **base `B 2`** — the landed GENTOW2 record (accepted; `(b)@2` unconditional);
* **step `Wle W (i−1) → B (i−1) → W i`** — the WI companion's lemma (SOL row 18,
  CERTIFIED 2/2); its consumption census places its point-evaluation input at index `i−1`
  (C-5: "clause (b) of THEOREM GENTOW5-B at index i-1 — Phi_i-roots are P_i points with
  exact monomial values … consuming it here is NOT circular");
* **chain `Wle W i → B i`** — frozen GENTOW5's own dependency, displayed at T5 §4:
  `𝒲_{≤n} ⟹ (a)@n ⟹ Corollary 6.4 ⟹ (b)@n` (WF-chain);

and the skeleton closes `𝒲_{≤n}` for EVERY `n` from the empty base `𝒲_{≤2}` (vacuous —
`wle_two`, proved). The interleaving dissolves the circularity T5 flagged: `B i` is never
consumed before `W i` — the order is `B 2 → W 3 → 𝒲_{≤3} → B 3 → W 4 → …`.

**The footprint walk (the "companion's full footprint" leg).** WI's census items, checked
for index alignment:

* C-2 (the `u_i`-family: per-grade fixedness, x0-freeness, factorization) — S11.2's PROVED
  side, "independently of 𝒲_{≤i}"; its evaluation point `x0` is a `Φ_i`-root in `P_i`,
  supplied by `(b)@(i−1)` — index `i−1`. ✓
* C-3 (LEMMA GENTOW5-C's value clause) — the census names it "(B-1 at level i)"; the
  instance the S2 proof consumes turns evaluation heights AT `x0 ∈ P_i` into exact
  `μ_i`-values (step (iv)) — i.e. C's statement instantiated with points in `P_i`, which is
  C at statement-index `i−1`. The "level i" in the census names the AMBIENT level, not the
  point locus. ✓ (This index-alignment reading is THIS unit's; flagged as the one remaining
  audit degree below.)
* C-4 (the S2.1 reciprocity `θ_i(t) = ϑ_{i,f_{i+1}−t}^{-1}`) — S11.2's proved side, and now
  independently exponent-level (§2.1 A1's reciprocity rows). ✓
* C-5 (clause (b) at index `i−1`) — the census's own noncircularity walk. ✓
* C-6..C-8 — accepted/source-side, level-general in their own quantifiers (the census's
  leg (b)). ✓ C-9 — deliberately empty. ✓
* The S1 recital "with `P_{i+1}` nonempty": **nowhere consumed by the S2 proof body** — the
  proof's only point evaluations are at `x0 ∈ P_i`; steps (0)–(iii) are point-free
  graded/valuation facts of `μ_{i+1}` (which exists from the chain data alone). The r1
  append's derivation of `P_{i+1} ≠ ∅` (via `(b)@i`) is the leg T5 S12.1 flagged as
  circular-at-index-`i`; in the interleaved order it is HARMLESS AND UNNEEDED for the
  induction — `(b)@i` arrives after `W i` via the chain, at which point the r1 derivation
  is sound as a POST-HOC fact. The recital reverts to a setting phrase, exactly as T5 wrote.

**Row effect.** The re-verification obligation T5 S12.1 recorded is now performed: the
closure arithmetic is machine-checked (`wle_of_interleaved`, Lean-core), the footprint walk
is written down with quotes, and the numeric leg adds the two coverage gaps WI's honesty box
disclosed (three slots at `f₄ = 3`; `w₂`/letters at a non-prime-field alphabet) plus both
drain teeth re-fired at the new frames (the naive twin splits). The row stays CARRY — the
FROZEN GENTOW5/T5 statements retain their explicit `𝒲_{≤i}` hypotheses (T5 S12.1:
"Certification of the WI companion does not discharge these conjuncts from the frozen
GENTOW5 statements"), and consumption must route through the composed chain
{base = GENTOW2, step = WI, chain = frozen GENTOW5's (a)→(b)} + this skeleton. **The
narrowing: the residual is no longer "the induction from the empty base is not performed" —
it is (i) the three suppliers at their existing accepted/certified grades, and (ii) one
fresh-context hostile pass on THIS unit's index-alignment reading of C-3/C-5 (the walk
above), which chapter I's discharge node should commission when it composes the citation.**

### 3.3 Lean landings (all sorry-free, Lean-core `{propext, Classical.choice, Quot.sound}`)

* `leanfinal/Uniformity/ChapD/D62.lean` — **NODE D.62 at the A-D.2/DECISION-D-2 re-signed
  signature**: `HVarthetaRes` (byte-matching the leanspec landing modulo namespace),
  `hvarthetaRes_of_arena_agree` PROVED, `GaugeArena.varthetaEl_mem_ker` PROVED (D.08's fact,
  local pending D.08). The VOIDED existential form is deliberately NOT re-landed (I.10 fence:
  no consumer may cite it; the refutation record stays leanspec/verification-side).
* `leanfinal/Uniformity/ChapD/D62w.lean` — the OM-8 witness layer (D-adjacent appendix per
  the H09w/H73w/H89w precedent), five layers:
  1. `hvarthetaRes_of_tau_letters` — the ϑ→τ reduction (arena-free; D.05's recursion +
     induction);
  2. `hvarthetaRes_levelOne` — the `i = 1` corpus proof transcribed (D.17's `levelOneArena`,
     the η-power read, at every height `q`);
  3. `deep3Section`/`deep3_exact_height`/`deep3_tau_descent`/`hvarthetaRes_deep3` — the
     `i = 3` letter-lattice model on the F-LW3/F-P5/F-EC3 exponent chain: the greedy `n̂₃`
     with its exact-height law, the factorization for ALL heights, and
     `(H-VARTHETA-RES)₃` reduced to the three letter-memberships;
  3′. `deep2Section`/`deep2_tau_descent`/`hvarthetaRes_deep2` — the `i = 2` transcription
     (`EFF.GENTOW2.42`'s γ-calculus at exponent level);
  4. `Wle` (leanspec-byte-matching), `wle_two` PROVED (an `axiom` stub in leanspec),
     `wle_of_interleaved` — the HYP.63 empty-base induction skeleton;
     `VarthetaWConjunct` (D.63's signature);
  5. `SuppLE`/`dvd_stage`/`triangular_descent` — **the general-depth structural core**: the
     letter-lattice factorization at EVERY depth (triangular descent against per-stage
     divisibility) + the per-rung gcd law. The chain-indexed instantiation (greedy `n̂` over
     stage lists + its exact-height law, general depth) is left to the ChapD fleet —
     depths 2/3 show the shape.
* `leanfinal/Uniformity/ChapD.lean` roll-up wired (D62, D62w). Build: 8,566 jobs green.

**What is NOT claimed** (the file's faithfulness block, restated): the deep models are the
EXPONENT-LEVEL shadow; the bridge to the p-adic/Laurent fields is the corpus's evaluation
leg (accepted S2.3(3)) — machine-covered at the same exponent chains by §2's oracles, not
Lean-checked; no claim for arbitrary `ρ` (§2.4 D2); the FULL theorem's status is unchanged
(capstone discipline per repo CLAUDE.md).

---

## §4. LEDGER EFFECTS + BOOKKEEPING

* **HYP.57** — stays **CARRY**, with the row's own named task (the S2.1-implication
  adjudication) now PERFORMED and recorded (ARC NOTE at the row): YES at DEF GENTOW5-1
  instantiations with the canonical read (three legs, §3.1), NO abstractly (ρ-defeat at real
  exponents). Residual pinned: socket-typing at the canonical read (GC-13/GC-14 wiring) +
  the T1 site-by-site convention walk (D.64 OPEN-CALL-5's existing route). No conjunct
  added, none silently discharged.
* **HYP.63** — stays **CARRY**, with T5 S12.1's named re-verification obligation now
  PERFORMED (ARC NOTE at the row): interleaved-induction skeleton PROVED
  (`wle_of_interleaved`), footprint walk written with quotes, WI's two disclosed machine
  gaps closed (three slots; non-prime-field alphabet). Residual pinned: the suppliers'
  grades + one fresh-context hostile pass on the C-3/C-5 index-alignment reading, to be
  commissioned by chapter I's discharge node.
* **CHAP-D** — dated OM-8 note appended at D.64 (the routing table's owner for the S2.1
  adjudication and OPEN-CALL 5): the adjudication row is resolved as above; D.62's Lean
  landing in `leanfinal` recorded.
* **CHAP-I** — dated ARC NOTE at the §3.4 HYP.57/HYP.63 rows + the I.10 consumption note's
  region: the `∀ i ≥ 3` conjunct's carriers now have leanfinal homes (D62/D62w) and the
  discharge routes are pinned; the consumption fence (A-D.2 form only, canonical read) is
  unchanged and now has a machine-checked reason (the ρ-defeat at real exponents).
* **E.61 socket (fence restated)**: when typed, bind `HVarthetaRes` with chapter C's
  CANONICAL residue data — an unpinned `ρ` leaves the conjunct undischargeable (§2.4 D2);
  `hvarthetaRes_deep3`'s hypothesis shape (three letter-memberships) is the template.
* **Artifacts**: `verification/om8_vartheta_deep.py` (`543a1dff`) +
  `verification/logs/om8_vartheta_deep_output.txt` (`47a0d42e`, GREEN 52/0, bit-identical
  re-run) + `..._run1_RED.txt` (`4276cb42`, kept);
  `leanfinal/Uniformity/ChapD/D62.lean`, `D62w.lean`, roll-up wiring.
* **Commits**: `9e0e7f3a` (note skeleton), `f3f02caf` (instrument seal), `bed8d978`
  (run-1 RED + repair), `a7904c18` (numeric GREEN), `0c4b1dbc` (D62/D62w landings + roll-up),
  `55374a52` (i = 2 layer), `5f185b38` (general-depth core), + the bookkeeping commit(s)
  carrying this section, the ledger ARC NOTEs, and the blueprint notes.
