# DU-LEMMA — the (DMULT-s) upgrade: ∂u ≡ 1 for the JC-SCAL unit cochain, PROVED on the measured perimeter by the WM-COB route (route (a)); route (b) — the FGMN eq-(14) citation route — honestly BOXED at the dictionary, with the exact FGMN hypotheses displayed and a derived CONSTRAINT on any future dictionary closure

**Unit:** DU-LEMMA (the (DMULT-s) upgrade), dispatched by the orchestrator per
the four-line reduction of `BRIDGE_ADJUDICATIONS_2026-07-30.md`, entry
"NUMBERING-LEG PRELIMINARY, PART 4" (commit 436b9c6). **Attempt counter 0/2
(intermediate lemma per the effort directive 2026-08-05: disclosure-grade
honesty, no 2-clean arc owed).** Machine leg:
`verification/openmath/dulemma_checks.py`, two-commit seal (§8).

**PROVENANCE (disclosure).** A first DU-LEMMA dispatch died to an API error
mid-composition on 2026-08-07, leaving an uncommitted partial (archived out of
the repo at `/tmp/dulemma_partial_archive/`, per the ledger entry at the W-10
fold). THIS note is the clean redo: every consumed statement was re-read from
the accepted corpus in this session (GRTJC §§0–4, WELDMASTER S2, the FGMN
layout at its pinned lines, the engine's `eps`/`read_coeffs`/`split`/`tanch`
code itself), and the proof of DU-A below was re-derived against the engine
definitions line by line (including the on-line sub-lemma DU-A0, which the
partial had left to "the engine asserts it"). Where the redo and the partial
agree, that is because the mathematics agreed on re-derivation, and the
machine leg (fresh, smoke-disclosed) checks every link.

**DO-NOT-TOUCH DISCIPLINE.** GRTJC (`GRTJC_PROOF_2026-08-08.md`) is ACCEPTED
at 2/2 and frozen; nothing in it is edited. The upgrade lives in THIS note;
the proposed one-line annex for GRTJC's tail is displayed verbatim in §9 for
the ORCHESTRATOR to apply at the next fold.

---

## §0. THE STATEMENT, THE VERDICT, AND THE REDUCTION (read first)

**Context re-grounding.** GRTJC (accepted) states composite-stage digit
multiplicativity in two tiers. With 𝑅_λ the corpus's level-(m+1) digit
polynomial at line λ (GRTJC §1) and δ(λ,μ) := (s_NR(λ)+s_NR(μ)−s_NR(λ+μ))/e_m
∈ {0,1}:

    (DMULT-w)  [DERIVED, citable]   𝑅_{λ+μ}(fg) = ω(λ,μ)·y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g)
               for a unit ω(λ,μ) ∈ K_m^* independent of f and g;
    (DMULT-s)  [was MEASURED only]  ω(λ,μ) ≡ 1
               (R1-DMULT 2,784/0; the r2 dense bilinear leg 3,655/0).

The orchestrator's reduction (ledger, PART 4): writing 𝑅_λ = u_λ·𝑅_λ^{gauge}
against ANY exactly-multiplicative reference gauge (e.g. the eq-(14)-normalized
FGMN operator, where the transport W-1 delivers one), the (DMULT-s) multiplier
is EXACTLY the coboundary

    ω(λ,μ) = ∂u(λ,μ) := u_{λ+μ}/(u_λ·u_μ),

so **(DMULT-s) ⟺ ∂u ≡ 1** — strictly weaker than u ≡ 1. Note ω itself is
harness-observable (no gauge needed to state it); ∂u ≡ 1 is its gauge-keyed
reading, the same for every exact reference gauge simultaneously. This note
therefore proves ω ≡ 1 directly; the ∂u-form follows for every gauge at once.

**VERDICT (this unit).**

* **THEOREM DU (§4): ∂u ≡ 1 is PROVED on the measured perimeter** — every
  window line pair (λ, μ) in [ILN]†'s scored stratum, on towers with m ≥ 1 and
  e_m ≥ 2 — by **route (a)**, the WM-COB structural route. The proof is the
  orchestrator's predicted 4-line compose, made valid by ONE new lemma:
  **DU-A (§3): the harness anchor constant IS the composite ε-kit cochain,
  a_γ = E(γ)** — plus the witness reduction DU-B (§2).
* **Route (b)** (anchor-generator verification via FGMN eq (14)) is **BOXED
  (§5)**: its generator-verification step is VALID in the (f,g)-slot
  (displayed with the exact reason, §2) and eq (14) does pin the FGMN side of
  the key-powers, but converting the FGMN-gauge computation into the harness ω
  needs the W-1/TR-3′-GEN dictionary with EXACT (multiplier-1) unit control,
  which is OPEN beyond {all order-2} ∪ {order-3 all-e_j = 1}; assuming the
  dictionary's unit system multiplicative is assuming ∂u ≡ 1 — circular. Per
  the charge's escape hatch, the proof runs on route (a); §5 boxes route (b)
  with FGMN's hypotheses stated exactly and extracts a derived constraint
  (DU-C) on any future dictionary closure.
* **The upgrade licensed (§7): (DMULT-s) MEASURED → PROVED on the perimeter
  above — DERIVED (corpus-internal), NOT CITED.** The ledger's hoped-for
  "MEASURED → CITED (FGMN Cor 4.7(2)(3) + Lemma 5.13 + eq (14))" does NOT
  land: no FGMN citation delivers the harness multiplier (§5, including why
  Lemma 5.13 is structurally the wrong tier). JC-COB's sharp
  u = a_γ·a_{γ′} rides up with it, same perimeter (§4, COROLLARY DU-COB).

**THE FOUR-LINE PROOF (displayed here, justified in §§2–4).** For a window
pair (λ,μ) in the scored stratum, e_m ≥ 2, with u_span(λ,μ) := the slot-δ
unit of JC-SPAN (𝑅_{λ+μ}(φ_λφ_μ) = u_span·y^δ):

    ω(λ,μ) = u_span(λ,μ) / (a_λ·a_μ)                    [DU-B(i): anchor witness]
           = a_{λ+μ}·∏_{j=1}^{m} z_j^{D_j} / (a_λ·a_μ)  [GRTJC THEOREM JC-INNER]
           = a_{λ+μ}·(∂E)(λ,μ) / (a_λ·a_μ)              [WELDMASTER WM-COB(ii)]
           = 1                                           [DU-A: a_γ = E(γ)].

**Conditionality, one line.** THEOREM DU rides
`[ILN]† ACCEPTED (value law, scored stratum) + GRTJC ACCEPTED (JC-INNER = W-8 ∘ value law; (DMULT-w) = the FGMN citation via W-1 ATTEMPT; JC-SPAN; JC-PER/JC-PIINV/JC-ANCHMON) + WELDMASTER ACCEPTED (WM-COB(ii), riding [ILN]† SHIFT-(n)/D_j-INT/EXP-KIT(a), unconditional legs) + DU-A/DU-B (NEW, proved here on (IN-5)-layer definitions only)`,
inheriting every fence of those suppliers (notably e_m ≥ 2, the scored
stratum, and W-1's attempt-grade transport inside (DMULT-w)). Off the
stratum and at e_m = 1 the claim stays measured/boxed (§6). This note's own
arc: 0/2.

---

## §1. SETTING AND CONSUMED INPUTS (nothing new defined except names)

Fix a standard-lift tower T of the [ILN]† class (reads (e_j,h_j,g_j),
j = 0..m; NR = m+1; E = e_0⋯e_m), with GRTJC §1's objects: keys Φ_j, weights
w = w_{m+1}, split γ ↦ (s_1..s_NR, u_1) by iterated eq-12 with per-level split
weights β_j(γ) (top: (s_NR, u_NR) = eq12(γ, e_m, h_m), β_m = u_NR − s_NR·wΦ_m;
downward: (s_j, u_j) = eq12(β_j, e_{j−1}, h_{j−1}), β_{j−1} = u_j − s_j·wΦ_{j−1}),
window W = {γ : u_1(γ) ≥ 0}, anchors φ_γ = π^{u_1}∏_{j=0}^{m}Φ_j^{s_{j+1}}
(γ ∈ W), the level read and its digit polynomial 𝑅_λ(f) ∈ K_m[y], and the
anchor constants a_λ := 𝑅_λ(φ_λ) ∈ K_m^* (JC-ANCHMON(c)).

**The ε-kit ([ILN]† S0.2 / EXP-KIT(a); engine `Tower.eps`).** For level
j = 1..m and β ∈ ℤ, with (s, u) := eq12(β, e_{j−1}, h_{j−1}) — i.e.
β = s·h_{j−1} + u·e_{j−1}, 0 ≤ s < e_{j−1} — and the Bezout pair
ℓ_{j−1}h_{j−1} + ℓ′_{j−1}e_{j−1} = 1 (0 ≤ ℓ_{j−1} < e_{j−1}):

    ε_j(β) := z_j^{ ℓ′_{j−1}·s − ℓ_{j−1}·u } = z_j^{ −t_j(β) },
    t_j(β) := (ℓ_{j−1}β − s)/e_{j−1} = ℓ_{j−1}·u − ℓ′_{j−1}·s ∈ ℤ

(the two exponent forms agree by ℓh + ℓ′e = 1; t_j is WELDMASTER's print-twist
cochain, and this is the engine's `eps` byte-for-byte). ε_j(0) = 1; ε_0 := 1.
**The composite ε-kit cochain (WELDMASTER S0, consumed verbatim):**

    E(γ) := ∏_{j=1}^{m} ε_j(β_j(γ))   ∈ K_m^*   (each factor embedded),
    (∂E)(γ,γ′) := E(γ)·E(γ′)/E(γ+γ′).

**Consumed statements (with owners and grades):**

* **(C-1) (DMULT-w)** [GRTJC §2.10, DERIVED there from the FGMN citation +
  §0's W-1 transport (ATTEMPT grade, inherited)]: the §0 display; ω(λ,μ)
  depends only on the lines, not on f, g.
* **(C-2) JC-SPAN** [GRTJC §2.7, PROVED]: for γ,γ′ ∈ W with γ+γ′ ∈ W and
  e_m ≥ 2, 𝑅_{γ+γ′}(φ_γφ_{γ′}) = u_span·y^δ with u_span ∈ K_m^* (slot set
  exactly {δ}); at e_m = 1, slot set ⊆ {0,1} only (fence).
* **(C-3) THEOREM JC-INNER** [GRTJC §3.3, PROVED on its fences]: on [ILN]†'s
  scored stratum (all D_j integral, pair off DCX), γ,γ′ ∈ W, γ+γ′ ∈ W,
  e_m ≥ 2: **u_span = a_{γ+γ′}·∏_{j=1}^{m}z_j^{D_j} in K_m^***. (Its proof =
  W-8 composed with [ILN]†'s accepted value law; per GRTJC §2.10's
  tier-consumption census — the PE2 blast-radius check — W-8 rides
  (DMULT-w), NOT (DMULT-s); no circularity, see §4 remark.)
* **(C-4) WM-COB(ii)** [WELDMASTER S2, ACCEPTED; footprint = [ILN]†
  SHIFT-(n) + D_j-INT + EXP-KIT(a), all unconditional legs]: for every pair
  with S0.3 data (δ, S_j, D_j), D_j integral, and every level j:
  z_j^{D_j} = ε_j(β_j)·ε_j(β′_j)·ε_j(β″_j)^{−1}. Taking the product over
  j = 1..m (each factor embedded into K_m):
  **∏_{j=1}^{m} z_j^{D_j} = (∂E)(γ,γ′)** — WM-COB(iii)'s first half, before
  the value-law substitution.
* **(C-5) JC-PER / JC-PIINV / JC-ANCHMON / JC-FIB** [GRTJC §§2.3–2.5, 2.10,
  PROVED]: φ_{λ+E} = π·φ_λ byte-for-byte; 𝑅_{λ+E}(πf) = c_π·𝑅_λ(f) with ONE
  row constant c_π ∈ K_m^*; a_λ ∈ K_m^* (single Φ_m-digit, slot set {0});
  s_NR is E-periodic; deg tanch(γ, r−1) < deg Φ_r at every level r ≤ m
  (JC-ANCHMON(a), whose telescoping proof works at every truncation level).
* **(C-6) The corpus read definition** [(IN-5) layer, definitions not
  claims]: GRTJC §1 / engine `read_coeffs`/`read`/`eps`/`split`/`tanch` —
  used ONLY in DU-A's proof, which is definition-unfolding plus induction.
* **(C-7) [ILN]† Lemma WINDOW-(n)** [ACCEPTED, generic unconditional]: sums
  of window lines are window lines (used only to know the grids below are
  total; the machine leg censuses it: 0 off-window sums).

Everything below is stated for m ≥ 1. (At m = 0 there is no inner factor and
no unit cochain; the last-read layer is (IN-2)'s CARRY-1, already exact —
§6 box B-4.)

---

## §2. LEMMA DU-B — the anchor-witness reduction (and WHY generator-verification is valid, and in which slot)

**LEMMA DU-B.** Let λ, μ ∈ W with λ+μ ∈ W, e_m ≥ 2. Then:

    (i)  ω(λ,μ) = u_span(λ,μ)/(a_λ·a_μ);
    (ii) ω(λ+E, μ) = ω(λ,μ) = ω(λ, μ+E)  (E-periodicity in each argument).

*Proof.* (i) (DMULT-w)'s ω is independent of (f,g); instantiate the display at
the witness pair (f,g) = (φ_λ, φ_μ): w(φ_λ) = λ, w(φ_μ) = μ (the anchor law,
= DU-A0(c) below), both digit polynomials are the nonzero constants a_λ, a_μ
(JC-ANCHMON(c)), and the left side is u_span·y^δ (JC-SPAN). Compare
coefficients of y^δ: u_span = ω·a_λ·a_μ; both a's are units, divide.
(ii) Replace λ by λ+E in (i): δ(λ+E,μ) = δ(λ,μ) (s_NR is E-periodic,
JC-PER/JC-FIB); φ_{λ+E}φ_μ = π·φ_λφ_μ (JC-PER), so 𝑅_{λ+μ+E}(φ_{λ+E}φ_μ) =
c_π·𝑅_{λ+μ}(φ_λφ_μ) (JC-PIINV(b)), i.e. u_span(λ+E,μ) = c_π·u_span(λ,μ);
and a_{λ+E} = c_π·a_λ (JC-PIINV(b) applied to f = φ_λ, plus JC-PER). The c_π
cancels in (i). Symmetrically in μ. ∎

**The generator-verification question, answered exactly (the charge's
proviso).** Two different "verify on generators, extend by (DMULT-w)
bilinearity" arguments must be separated:

* **The (f,g)-slot: VALID.** ω(λ,μ) does not depend on the polynomials —
  that is (DMULT-w)'s content, DERIVED at citable tier — so ONE witness pair
  with nonzero digit polynomials decides ω(λ,μ) for the whole line pair, and
  the anchors are such witnesses. This is what "verification on the anchor
  generators suffices" legitimately means, and it is the reduction step (i)
  above. Its price: (DMULT-w), hence the FGMN citation + W-1 ATTEMPT ride in.
* **The line-slot: NOT valid as an extension mechanism, and NOT used.** A
  symmetric 2-cocycle on the line lattice is NOT determined by its values on
  a generating set of line PAIRS by any "bilinearity" — there is no
  bilinearity in the lines. What IS true (and is how the machine leg becomes
  per-row exhaustive, COROLLARY DU-FIN §4): ∂u ≡ 1 is equivalent to λ ↦ u_λ
  being multiplicative, and ω's proved E-periodicity (ii) reduces all window
  pairs of a row to the finite representative grid. That argument consumes
  the cochain-hood of u (a genuine function of the line) and the PROVED
  periodicity — not a generating-set principle for cocycles. Route (b)'s
  charge wording ("extend by (DMULT-w) bilinearity") is therefore honest
  ONLY in the (f,g)-slot reading; this note uses exactly that reading.

---

## §3. LEMMA DU-A — the harness anchor constant IS the composite ε-kit cochain (the one new identity)

**LEMMA DU-A.** For every γ ∈ W:  **a_γ = E(γ) = ∏_{j=1}^{m} ε_j(β_j(γ))**,
each factor embedded in K_m. In particular a_0 = 1 when 0 ∈ W (all split data
vanish and ε_j(0) = 1), and a_{γ+E}/a_γ = ρ_T := ∏_{j=1}^{m}
z_j^{−ℓ_{j−1}E_{j−1}} (E_{j−1} := e_0⋯e_{j−2}; WELDMASTER WM-RHO's constant)
— so JC-PIINV's row constant c_π and WM-RHO's ρ_T are ONE object:
**c_π = ρ_T**.

The proof is a downward induction through the read definition along the
anchor's single-digit chain. Write the truncated anchors
A_r := π^{u_1}∏_{j=0}^{r}Φ_j^{s_{j+1}} = tanch(γ, r), so φ_γ = A_m and
A_r = A_{r−1}·Φ_r^{s_{r+1}}, with A_{−1} := π^{u_1}.

**SUB-LEMMA DU-A0 (the chain is single-digit ON ITS LINE, at every level).**
For γ ∈ W and 1 ≤ r ≤ m: (a) the Φ_{r−1}-development of A_{r−1} is the single
digit A_{r−2} at abscissa s_r; (b) w_r(A_{r−1}) = β_r(γ), where β_r is the
split's level-r weight (convention β_{NR} := γ, i.e. at r = m+1 clause (b)
reads w(φ_γ) = γ, the anchor law).

*Proof.* (a) is JC-ANCHMON(a) at truncation level r: Σ_{j<r−1}s_{j+1}degΦ_j
< deg Φ_{r−1} (the telescoping bound stops at r−1), so
A_{r−1} = A_{r−2}·Φ_{r−1}^{s_r} with deg A_{r−2} < deg Φ_{r−1} — that IS the
development. (b) By induction upward. Base r = 1: w_1(A_0) =
e_0·w_0(π^{u_1}) + s_1·γ_1 = e_0u_1 + s_1h_0 = β_1, the eq-12 identity at the
bottom of the split (γ_1 = h_0). Step: assuming w_r(A_{r−1}) = β_r,

    w_{r+1}(A_r) = e_r·w_r(A_{r−1}) + s_{r+1}·γ_{r+1}       [single digit, (a)]
                 = e_r·β_r + s_{r+1}·(e_r·wΦ_r + h_r)        [γ_{r+1} = e_rwΦ_r + h_r]
                 = e_r·(β_r + s_{r+1}wΦ_r) + s_{r+1}h_r
                 = e_r·u_{r+1} + s_{r+1}h_r = β_{r+1}        [split: β_r = u_{r+1} − s_{r+1}wΦ_r;
                                                              eq-12: β_{r+1} = s_{r+1}h_r + u_{r+1}e_r].

At the top the same computation gives w_{m+1}(A_m) = γ. Each digit therefore
sits ON its line, with slot index (s_r − s_r)/e_{r−1} = 0 at every level. ∎
(These are the corpus's own split/R2 laws — (IN-5); displayed here so the
proof of DU-A stands on identities, not on engine assertions.)

*Proof of DU-A.* Unfold the read definition (C-6) down the chain. At the top
(level NR, line γ): by DU-A0 the only on-line digit of φ_γ = A_m is A_{m−1}
at abscissa s_NR = the line's base abscissa, slot 0, digit weight β_m; the
read definition packs it as

    a_γ = 𝑅_γ(φ_γ)|_{slot 0} = ε_m(β_m) · read_m(β_m, A_{m−1}),

where the ε applied is the DIGIT level's kit at the digit's weight (engine
`read_coeffs(m′, λ, f)` applies `eps(m′−1, sw)`; here m′ = NR, sw = β_m).
Inductively, for 1 ≤ r ≤ m, DU-A0 gives read_{r}(β_r, A_{r−1}) =
ε_{r−1}(β_{r−1})·read_{r−1}(β_{r−1}, A_{r−2}) (single digit, slot 0, embedded
upward as the values pack), down to the base: read_1(β_1, A_0) =
ε_0(u_1)·read_0(u_1, π^{u_1}) = 1·1 = 1 — the level-0 read of π^{u_1} at
weight u_1 is the residue of π^{u_1}/π^{u_1} = 1 (this is where γ ∈ W, i.e.
u_1 ≥ 0, is used: off the window there is no level-0 residue and no anchor).
Assembling,

    a_γ = ε_m(β_m)·ε_{m−1}(β_{m−1})·⋯·ε_1(β_1)·1 = E(γ).

The a_0 = 1 rider is ε_j(0) = 1. The period rider: by DU-A just proved,
a_{γ+E}/a_γ = E(γ+E)/E(γ) = ρ_T by WM-RHO (WELDMASTER S2.1, ACCEPTED:
γ ↦ γ+E shifts each β_j by E_j := e_0⋯e_{j−1} keeping every s_j fixed, so
t_j picks up exactly ℓ_{j−1}E_{j−1}); and JC-PIINV(c) gives a_{γ+E} = c_π·a_γ,
whence c_π = ρ_T. ∎

*Grade.* PROVED from (IN-5)-layer definitions + JC-ANCHMON + the split laws
(DU-A0) + WM-RHO for the period rider; **no literature input, no (DMULT)
tier, no [ILN]† value law** — DU-A is unconditional on the [ILN]† class.
*Machine:* families **DU-EPS** (a_γ == E(γ) with E computed from the fresh
t-cochain, and slot set {0}, on 2E lines per row plus the on-demand λ+μ
lines) and **DU-RHO** (a_{γ+E} == ρ_T·a_γ with ρ_T the CLOSED form — this
simultaneously re-reads c_π and ρ_T as one constant), with tooth **DU-T2**
(a sign-flipped kit must be caught) — §8.

*Remark (what DU-A adds over the corpus).* GRTJC treats a_λ as an opaque
measured unit (the anchor's own digit constant) and separately proves the
ε-kit laws; WELDMASTER's E is a cochain of split data with no read attached.
DU-A is the missing identification — the reason JC-COB's measured inner
factor (a_γa_{γ′}/a_{γ+γ′}) and WM-COB's coboundary ∂E could agree
numerically on every pair ever tested is that **the cochains are equal, not
just cohomologous.** (JC-PIINV's measured c_π values — 1, z̄, z̄², up to z̄⁸
across the roster — are now the closed form ρ_T; the z̄-monomial prints are
K_m-elements rendered in the top field on g_m = 1 rows and z_m-monomials
generally.)

---

## §4. THEOREM DU — ∂u ≡ 1 on the measured perimeter (route (a)), with corollaries

**THEOREM DU.** Let T be a standard-lift tower of the [ILN]† class with
m ≥ 1 and **e_m ≥ 2**. Let (λ,μ) be a window pair (λ, μ, λ+μ ∈ W) in
**[ILN]†'s scored stratum** (all D_j(λ,μ) integral, pair off DCX). Then

    ω(λ,μ) = 1,

i.e. ∂u(λ,μ) = 1 for the JC-SCAL unit cochain against any exact reference
gauge. Consequently **(DMULT-s) holds — 𝑅_{λ+μ}(fg) = y^{δ}·𝑅_λ(f)·𝑅_μ(g)
exactly, multiplier 1 — for ALL f, g ∈ O[x] whose weight pair
(w(f), w(g)) = (λ,μ) is as above** (every attained weight pair of integral
polynomials is a window pair: gr_γ = 0 off W, GRTJC JC-BOX-7).

*Proof.* The §0 display: ω(λ,μ) = u_span/(a_λa_μ) by DU-B(i);
u_span = a_{λ+μ}·∏_{j=1}^{m}z_j^{D_j} by JC-INNER (C-3; its fences are the
theorem's fences); ∏_{j=1}^{m}z_j^{D_j} = (∂E)(λ,μ) = E(λ)E(μ)/E(λ+μ) by
WM-COB(ii) (C-4; the stratum gives D_j integral); and a_ν = E(ν) at all three
lines by DU-A (λ+μ ∈ W is part of the hypothesis). Multiply out:

    ω = a_{λ+μ}·(∂E)/(a_λa_μ) = E(λ+μ)·[E(λ)E(μ)/E(λ+μ)]/(E(λ)E(μ)) = 1. ∎

*No circularity.* The suppliers' tier bookkeeping (GRTJC §2.10, "who consumes
which tier", the PE2 blast-radius check) certifies that W-8, JC-INNER,
JC-SPAN and (DMULT-w) ride only the citable tier — none consumes (DMULT-s)
or JC-COB's sharp form. The only (DMULT-s)-tier statements in the corpus
were CONSUMERS, not inputs. So the compose is well-founded.

**COROLLARY DU-COB (JC-COB's sharp form, upgraded).** On THEOREM DU's
perimeter, u_span(λ,μ) = a_λ·a_μ, and hence GRTJC's COROLLARY JC-COB display
c_{m+1}(γ,γ′) = (a_γa_{γ′}/a_{γ+γ′})·z̄^δ holds at **PROVED (conditional as
§0), no longer MEASURED-tier**. (Proof: ω = 1 in DU-B(i); or directly
u_span = a_{λ+μ}·∂E = E(λ)E(μ) = a_λa_μ by DU-A.) Equivalently, with DU-A
the inner factor of the accepted cocycle is ∏z_j^{D_j} = ∂a = ∂E — one
coboundary with two previously separate names.

**COROLLARY DU-FIN (finite per-row decision).** On a fixed tower T, ω is
E-periodic in each argument (DU-B(ii)), and every window line of class ν is
σν + kE with k ≥ 0 (σ the minimal window section). Hence ω is decided by its
values on the finite grid {(G0+r, G0+r′) : r, r′ ∈ [0,E)} of window
representatives (G0 a window base with G0 ≡ 0 mod E): the machine leg's
full-grid family DU-COBW does not sample — it **decides ∂u ≡ 1 for every
attained line pair of that row** whose class pair is scored, including — as
MEASUREMENT — the e_m = 1 row, where the theorem's proof does not run.
(Stratum membership is class-invariant: the S0.3 constants descend to ℤ/E,
[ILN]† S2 descent.)

---

## §5. ROUTE (b) — the FGMN citation route: BOXED, with the exact hypotheses displayed

**What route (b) would be.** Verify the multiplier on the anchor generators
in the FGMN gauge via eq (14)'s normalization, then extend by (DMULT-w)'s
(f,g)-independence. Step one of that plan is DU-B(i) (valid, §2). Step two
splits into an FGMN-internal half (A) and a transport half (B); (A) is a
genuine citation, (B) is the blocker.

**The FGMN package, stated exactly** (print: `docs/references/
fgmn_residual_ideals_1305.0775v3_layout.txt`; the layout line numbers are the
orchestrator's pins, re-read this session):

* **eq (14)** [line ~1004]: for 1 ≤ i ≤ r and any abscissa s ≥ 0, with
  α := μ_i(φ_i^s) = s(w_i + λ_i):
  **R_{i,α}(φ_i^s) = y^{⌊s/e_i⌋}, R_i(φ_i^s) = 1** — the key-power
  normalization (whence "R_r(g) monic", via Cor 4.4).
* **Corollary 4.7** [line 1121]: let 0 ≤ i ≤ r and α ∈ Γ_i. **(1)**
  R_{i,α}(g+h) = R_{i,α}(g) + R_{i,α}(h) for all g, h ∈ **P_α(μ_i)**;
  **(2)** if **β ∈ Γ_{i−1}**, then R_{i,α+β}(gh) = R_{i,α}(g)·R_{i,β}(h) for
  all g ∈ **P_α(μ_i)**, h ∈ **P_β(μ_i)**; **(3)** R_i(gh) = R_i(g)·R_i(h)
  for ALL g, h ∈ K[x]. Hypotheses carried: the P_α-memberships (μ_i(g) ≥ α;
  for the graded reading one takes α = μ_i(g) exactly), and — clause (2)
  only — **β ∈ Γ_{i−1}**, which FGMN's proof uses precisely as s(β) = 0
  ("the second equality proves item 2 because s(β) = 0, and this leads to
  s(α+β) = s(α), u(α+β) = u(α) + u(β)"). Clause (2) is the exact
  multiplier-1 graded multiplicativity — OF FGMN'S OWN OPERATOR.
* **Theorem 4.2** [line 1028]: H_μ(g) = φ_r(α)·R_{r,α}(g)(y_r) for
  α = μ(g); in particular P_α(μ)/P_α^+(μ) = φ_r(α)·Δ is free of rank one
  over Δ.  **Theorem 4.8** [line 1136]: R_{r,0} : Δ → F_r[y] is an
  isomorphism of F_r-algebras, (R_{r,0})^{−1} determined by y ↦ y_r.
* **Corollary 2.7** [line 525]: S_λ(gh) = S_λ(g) + S_λ(h) (Newton-segment
  additivity; in coordinates s(gh) = s(g)+s(h), u(gh) = u(g)+u(h)).
* **Lemma 5.13** [line 1403]: for nonzero g, h ∈ K[x] with **g μ-PROPER**
  (Cor 5.12: φ proper ⟺ some MacLane chain has φ ≁_μ φ_r; properness enters
  the proof ONLY to force s(g) = 0 when e_r > 1, making the ceiling identity
  (21) ⌈(s(g)+s(h))/e⌉ = ⌈s(g)/e⌉ + ⌈s(h)/e⌉ hold), one has
  **R(gh) = R(g)·R(h)** — the residual-IDEAL operator.

**(A) The FGMN-internal half: a genuine citation, nothing to verify.** In
FGMN's own gauge the anchors' memberships hold on the nose (each factor sits
at its own value: g = φ_γ-analogues have μ(g) = its value, and the level-<r
factors have values in Γ_{r−1}, so Cor 4.7(2)'s β ∈ Γ_{r−1} side condition is
met by the sub-key part of an anchor while the top key-power carries the α),
and eq (14) pins the key-power values. Consequently the FGMN-gauge multiplier
is 1 **tautologically** — that IS Cor 4.7(2). Route (b)'s "verify the
multiplier on the anchor generators via eq (14)" has, FGMN-internally, no
content beyond the citation itself.

**(B) The transport half: the blocker.** The harness operator is priced by
the corpus as 𝑅_λ = c_λ·σ(R^{FGMN}_λ) with c a LINE-WISE unit ((IN-3)'s own
wording; W-1 ATTEMPT). Substituting into (A):

    ω(λ,μ) = ∂c(λ,μ) · ω^{FGMN}(λ,μ) = ∂c(λ,μ).

So route (b) reduces the harness (DMULT-s) to **∂c ≡ 1 for the dictionary's
unit system — which IS the statement being proved** (the ledger's u, read in
the FGMN gauge). Citing FGMN can never discharge it; only a dictionary
closure with EXACT unit control can. The dictionary of record is **open
lemma TR-3′-GEN** (`GRB_ORDER2_2026-08-05.md` §S3.4), whose closed scope of
record is **{all order-2} ∪ {order-3 all-e_j = 1}** (GRTJC §2.10 [r3, G-6]);
the accepted order-2 closures deliver exactness (TR3-S1: "σ₁(R^F₂(f)) =
R_λ(f) EXACTLY"; TR3-S3 likewise with "per-argument units ≡ 1"), and GRTJA's
acceptance did not widen this: JA-RES (accepted) is a PER-SLOT
character-gauge law with a per-digit proviso ((VD-m) at m ≥ 2), not an exact
line-wise identification. **BOXED**: route (b) is unavailable as a general
proof; the escape hatch to route (a) is taken.

**Remark DU-D (where route (b) DOES close — consistency, not the proof).**
On TR-3′-GEN's closed strata the exact closures give c ≡ 1, so ω = ω^{FGMN}
= 1 by Cor 4.7(2) directly: on {all order-2} ∪ {order-3 all-e_j = 1} the
(DMULT-s) identity also follows by citation + closed dictionary. THEOREM DU
agrees there (its perimeter contains those strata at e_m ≥ 2) — two
independent routes on the overlap, one route (a) everywhere.

**DU-C (the derived constraint on any future dictionary closure —
display-level, new).** THEOREM DU + the exhaustive grid measurement force:
**any TR-3′-GEN closure (any level-compatible family σ_j with per-line units
c_λ making the FGMN side-read correspond to the harness 𝑅) must have
∂c ≡ 1 on the scored stratum** — the unit system is multiplicative, i.e. a
character of the line lattice there. Any candidate closure whose unit
coboundary is nontrivial on the stratum is refuted IN ADVANCE. Sketch-grade
corollary of the same arithmetic: a closure built from JA-RES's per-slot
characters alone contributes to c_λ an anchor factor of the shape
z_{m−1}^{−s_NR(λ)·A_{m−1}}, whose coboundary is z_{m−1}^{−δ·e_m·A_{m−1}} ≠ 1
on δ = 1 pairs whenever the letter's order does not divide e_m·A_{m−1} — so
such a closure MUST pair the character with a compensating cochain (the
print's own t(i)-twist is the natural candidate, per WELDMASTER LAW-3).
[Honestly graded: the constraint ∂c ≡ 1 is THEOREM-grade (it is THEOREM DU
restated); the JA-RES-defect sketch is a remark, not a proof, and is flagged
as such.]

---

## §6. HONEST BOXES (everything that resists, with its exact edge)

* **DU-BOX-1 (e_m = 1).** JC-SPAN gives only slot set ⊆ {0,1} and JC-INNER
  is fenced at e_m ≥ 2, so THEOREM DU's proof does not run on e_m = 1 rows
  (roster: C4H only). There the machine grid DECIDES ω ≡ 1 per row
  (DU-FIN), so the verdict is MEASURED — same epistemic state GRTJC's
  JC-BOX-4 already documents for that row.
* **DU-BOX-2 (off the scored stratum).** For pairs with some D_j
  non-integral or on DCX, [ILN]†'s value law — hence JC-INNER and
  WM-COB(ii)'s composite reading — has no content. (DMULT-w) still applies,
  so ω(λ,μ) EXISTS there (JC-CARRY-m proves the constant exists on every
  window pair); its VALUE is OPEN — neither proved nor measured (the roster
  grids contain 0 such pairs; the runner censuses dint-skips explicitly).
* **DU-BOX-3 (the W-1 attempt grade rides inside (DMULT-w)).** DU-B(i)
  consumes (DMULT-w), which GRTJC derived from the FGMN citation through the
  W-1 transport (ATTEMPT, 0/2 as priced there). If (DMULT-w) failed at
  composite order, DU-B(i) collapses and THEOREM DU with it — while the
  battery's direct grid checks would survive as pure measurement. The
  conditionality line (§0) displays this inheritance.
* **DU-BOX-4 (m = 0).** No inner factor, no unit cochain; (IN-2)'s CARRY-1
  is already exact at the last-read layer. Out of scope by design, not a
  gap.
* **DU-BOX-5 (the CITED upgrade does not land).** The ledger's PART-2 hope
  "(DMULT-s) upgrades MEASURED → CITED (FGMN Cor 4.7(2)(3) + Lemma 5.13 +
  eq (14))" is REFUTED as stated: Cor 4.7(2)(3) is exact only for FGMN's own
  operator (§5(B)); **Lemma 5.13 is structurally the wrong tier** — it is an
  identity of residual IDEALS, whose own proof proceeds "up to factors in
  F_r^*" and whose μ-proper hypothesis governs the CEILING normalization
  (21), not any unit; a unit-multiplier statement cannot be extracted from
  an operator that is unit-blind by construction. The upgrade lands as
  DERIVED instead (§7). GRTJC's standing printed-source citation-precision
  leg (JC-BOX-3 item 2, the Codex queue) is unaffected and still owed.
* **DU-BOX-6 (no Lean layer).** Per the math-first directive (2026-08-04)
  this unit ships prose + machine leg only; formalization waits for the
  weld-residue fold.
* **DU-BOX-7 (trivial-cochain rows).** On rows with |K_m^*| = 1 (roster:
  C2I's K_m = F_2) every unit cochain is trivial, so ∂u ≡ 1 is trivially
  true AND the fake-cochain tooth is structurally silent; the runner
  censuses these rows rather than pretending tooth coverage.

---

## §7. THE UPGRADE LICENSED (and what does NOT change)

**(DMULT-s): MEASURED → PROVED, conditional, on the perimeter** {[ILN]†
scored stratum} × {m ≥ 1, e_m ≥ 2} — DERIVED corpus-internally via route
(a), NOT CITED. Conditionality stack (verbatim from §0): [ILN]† ACCEPTED +
GRTJC ACCEPTED (with W-1 ATTEMPT inside (DMULT-w)) + WELDMASTER ACCEPTED +
DU-A/DU-B new at 0/2. Off-perimeter: e_m = 1 MEASURED (DU-BOX-1),
off-stratum OPEN (DU-BOX-2).

**Riders upgraded with it:**
* **COROLLARY JC-COB's sharp form** u = a_γ·a_{γ′} (and the §4.1 restatement
  and second half GRTJC re-fenced onto the exact tier): now PROVED
  conditional on the same stack (COROLLARY DU-COB) — no longer the one
  MEASURED-tier consumer.
* **The unification riders:** ∏_j z_j^{D_j} = ∂a = ∂E (one coboundary, three
  names) and c_π = ρ_T (one period constant, two names) — DU-A's structural
  dividends.
* **The weld's open-surface list** (ledger, all-six entry): "the ∂u ≡ 1
  lemma ((DMULT-s) MEASURED → PROVED)" leaves the list on the stated
  perimeter; W2-OPEN-2/OPEN-2a and the Codex ratification legs remain.

**What does NOT change.** GRTJC's text and grades are FROZEN (the annex
line, §9, is the only pointer, applied by the orchestrator). W-1/W-2/J-B
attempt-grades and their fences are untouched. J-D0 and W-10 already deleted
(DMULT-s) from their hypothesis sets — no downstream re-grade. The
faithful-citation Codex leg (JC-BOX-3 item 2) still rides. Nothing here is
unconditional: the stack above is the price, displayed at every claim.

---

## §8. MACHINE BRACKET — `verification/openmath/dulemma_checks.py` (two-commit seal)

### 8.1 SEALED PREDICTIONS (commit 1; the full battery NOT yet run)

The runner's docstring is the authoritative preregistration; summary:

| family | tests | predicted violations |
|---|---|---|
| DU-PIN | md5 pins of the 4 frozen imports (engine cae45db2…, probe/roster 03811b69…, r1 helpers 7f896bfa…, engine_ext d7eba6ac…) | 0 |
| EXT-GATE | engine_ext install + check_pins + agreement_gate | 0 |
| DU-EPS | DU-A on the nose: a_γ == E(γ) (fresh t-cochain kit) ∧ slot set {0}, γ ∈ [G0, G0+2E) per row + on-demand λ+μ lines | 0 |
| DU-RHO | a_{γ+E} == ρ_T·a_γ, ρ_T the CLOSED form (c_π = ρ_T unification) | 0 |
| DU-COBW | ∂u ≡ 1 decided on the FULL grid {G0+r}×{G0+r′}, r,r′ ∈ [0,E): 𝑅_{λ+μ}(φ_λφ_μ) == {δ: a_λa_μ} exact; ALL 29 rows incl. C4H (measured tier there) | 0 |
| DU-CHAIN | the compose link-by-link on every scored pair: ∏z_j^{D_j} == ∂E (WM-COB(ii)); slot set == {δ} ∧ u_span == a_{λ+μ}·∏z_j^{D_j} (JC-SPAN + JC-INNER) at e_m ≥ 2; weakened slot predicate at e_m = 1 | 0 |
| DU-DENSE | the r2 lesson: dense×dense, dense×PhiTop, PhiTop×PhiTop, dense×anchor pairs under the exact (DMULT-s) predicate (frozen surj_build/pmul/pshift); deg-2 targets SCORED | 0 |

Census obligations (printed, not violation-keyed except where stated):
off-window grid sums PREDICTED 0; dint-skips census-only; e_m = 1 rows
census (expected: C4H); both-dense pair count; tooth-ineligible rows.

Teeth (silent = RED): **DU-T1-FAKEU** (the charge's tooth: a fake unit
cochain c^{ind(γ)}, ind = [γ ≡ 0 mod E], with ∂ind ≠ 0 at (G0,G0) — the
regauged (DMULT-s) predicate must FAIL there; fires ≥ 1 on every row with
|K_m^*| ≥ 2, ineligible rows censused, total ≥ 1); **DU-T2-FAKEKIT**
(sign-flipped ε-kit vs DU-EPS; fires on every runtime-eligible row, total
≥ 1); **DU-T3-SHIFT** (y^{δ+1} mutation; fires ≥ 1 per row). Exit code =
violations + silent teeth.

Pre-seal smoke (disclosed in the docstring, part of this seal): one --smoke
run on C2A/C2I/C3A/C4H — 0 violations, teeth as predicted with C2I
T1-ineligible and C2I/C4H T2-ineligible; no scored predicate weakened
post-smoke.

### 8.2 VERDICT (commit 2 — written FROM the committed artifacts)

**PENDING at commit 1.**

---

## §9. PROPOSED ANNEX FOR GRTJC (verbatim; the ORCHESTRATOR applies at the next fold — this note edits nothing in the frozen file)

The following single line is proposed for the tail of
`GRTJC_PROOF_2026-08-08.md`, after its acceptance record:

> **[ANNEX 2026-08-08, orchestrator, post-acceptance] (DMULT-s) — §2.10's MEASURED tier — is PROVED-conditional on the measured perimeter (the [ILN]† scored stratum, m ≥ 1, e_m ≥ 2) by `DULEMMA_PROOF_2026-08-08.md` THEOREM DU (∂u ≡ 1 via the four-line WM-COB compose; the one new identity a_γ = E(γ), LEMMA DU-A), riding [ILN]†+GRTJC+WELDMASTER as accepted plus DU-A/DU-B at 0/2 — machine leg `dulemma_checks.py` two-commit seal, all families green; COROLLARY JC-COB's sharp u = a_γa_{γ′} inherits (DU-COB); the e_m = 1 row stays measured and off-stratum pairs stay open (DU-BOX-1/2); no text of this note is edited.**

(If the battery had come back non-green the annex would not be proposed;
see §8.2 for the verdict this line is conditioned on.)
