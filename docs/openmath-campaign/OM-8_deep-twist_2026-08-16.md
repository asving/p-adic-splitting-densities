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

*Instrument:* `verification/om8_vartheta_deep.py` (see §2.4 for the run record).

### 2.1 The ϑ-membership at deep letter-live frames (HYP.57's numeric leg)

[filled at §2.4 — frames, predictions, results]

### 2.2 The W-law's new machine coverage (HYP.63's numeric leg)

[filled at §2.4]

### 2.3 Constructed-counterexample attacks (the defeat systems)

[filled at §2.4]

### 2.4 Run record

[filled after the run]

---

## §3. ADJUDICATIONS, PROOFS, AND THE PINNED RESIDUALS

### 3.1 HYP.57 — the S2.1-discharge adjudication (the row's named task)

[filled]

### 3.2 HYP.63 — the induction from the empty base (T5 S12.1's named obligation)

[filled]

### 3.3 Lean landings

[filled]

---

## §4. LEDGER EFFECTS + BOOKKEEPING

[filled]
