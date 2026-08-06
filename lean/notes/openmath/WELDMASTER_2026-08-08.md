# WELD MASTER-TRANSPORT — the four junctions as faces of ONE anchored graded transport (M0–M4), the coboundary display c_{n+1} = z̄^δ·∂E (the [ILN]† inner factor IS the coboundary of the eq-12 cochain), and the ONE-PERIMETER fence ((C-coll) / (R-coll) / (VD-m) as three specializations of one character-triviality condition)

**Unit:** WELD MASTER-TRANSPORT COMPOSER (dispatched by the synthesis
adjudication, ledger 7724c20, from `docs/in-progress/
WELD_SYNTHESIS_2026-08-05.md` commit f71cd68 §4(i)). **Genre: CONSOLIDATION
THEOREM note in the LEDGER-Λ genre** (`LEDGERLAMBDA_2026-08-08.md` is the
model): one theorem whose faces are already-composed notes, consumed at
their own grades; ONE genuinely new display (S2's coboundary theorem, with
its complete proof); ONE fence surface (S3). Acceptance counter **0/2** —
no hostile pass has run on THIS note. Author: Fable, campaign date
2026-08-08 (wallclock 2026-08-06).

**SCOPE AND FENCES (stated before anything else).**

* **CONSUMPTION-ONLY.** No accepted or committed statement is touched. This
  note CONSOLIDATES the four junction notes (they become faces of one
  theorem); it does not edit, bracket, retire, or supersede them.
  Supersession brackets happen at the NEXT FOLD, never here (the LEDGER-Λ
  precedent verbatim: "it does not edit, bracket, or retire them").
* **THE GRADE-CAP SENTENCE.** Every clause below rides the four junction
  notes at ATTEMPT grade 0/2 each, with their full conditionality ledgers
  carried verbatim; [ILN]† is the sole ACCEPTED engine input. Nothing here
  upgrades anything, discharges any open leg, or retires any consumer gate.
* **The synthesis spot checks (6 families, 7,999 samples, 0 violations on
  T2A/T2C/T3A/T3E/I4B — WELD_SYNTHESIS Appendix A) are cited as MEASURED
  SUPPORT ONLY**: a scratch instrument, no seal, no teeth. This note's own
  sealed battery is S5.
* **OUT OF SCOPE (queued separately, not attempted):** the a_λ/E(λ)
  multiplicativity target (synthesis §2.5 — would move (DMULT-s) toward
  PROVED) and the χ-from-S closed form (synthesis §4(iii)3). The J-D block
  is untouched (blueprint route per the adjudication; H3's character-count
  shortcut stays REFUTED).

**Incorporation convention (dagger forms, declared once).**
**[W2]†** = `GRTW2_PROOF_2026-08-08.md` (attempt 0/2): clauses W2-C1/C2/C3,
the §3.4 (ξ,w) closed form, (C-coll), (HR-REC), W2-BOX-1, W2-OPEN-1 (OPEN).
**[JA]†** = `GRTJA_PROOF_2026-08-08.md` (post-r1, 0/2): JA-PIN, JA-VAL,
JA-EPS, JA-GRID, JA-RES, JA-VDIND, (R-coll), JA-BOX-1..5.
**[JB]†** = `GRTJB_PROOF_2026-08-08.md` (post-r4, 0/2): JB-DEV, JB-AFF,
JB-VTX, JB-TREE, LEMMA JB-EPS, JB-CREAD, the §0M conditionality matrix.
**[JC]†** = `GRTJC_PROOF_2026-08-08.md` (post-r2, 0/2): W-6..W-9, JC-LOC,
JC-LOAD, JC-PSIKER, JC-F1/JC-F2, the (DMULT-w)/(DMULT-s) tier split, LAW
JC-CYC. **[ILN]†** = `ITERLAWN_PROOF_2026-08-08.md`, **ACCEPTED**
(2-clean): the S0.1 class pin, S0.3 recursion (δ, S_j, D_j), Lemma
SHIFT-(n) and Lemma D_j-INT ("PROVED, generic, unconditional" — its S2
scope: γ, γ′ ∈ ℤ arbitrary), the value law c_{n+1} = z̄^δ·∏_j z_j^{D_j} on
the scored stratum. **[SYN]** = `WELD_SYNTHESIS_2026-08-05.md` (adjudication
note, f71cd68): the H1/H2 verdicts and derivation sketches this note
executes. **LED-Λ†** = `LEDGERLAMBDA_2026-08-08.md` (attempt): genre model
+ the line-face bookkeeping [JB]† already consumes.

**THE EXTRACTION-DECORRELATION LAW, obeyed as follows.** S2's cochain is
implemented FRESH in the sealed runner (`t(β) = (ℓβ − s)/e` from the raw
read integers, not imported from any committed eps); the committed engine's
`Tower.eps` / `Tower.constants` / `Tower.split` enter only as the OTHER leg
of each comparison. The non-textual leg is
`verification/openmath/weldmaster_checks.py` (S5) on the FROZEN
`grt_jc_probe.ROSTER` (29 towers, md5-pinned), two-commit sealed.

## S0. Setting (all consumed; nothing new defined until S1)

Tower T of the [ILN]† S0.1 class with reads (e_j, h_j, g_j), j = 0..n
(NR = n+1 reads), normalized Bézout ℓ_j h_j − ℓ′_j e_j = ±1 form as pinned
(`bez`), weights γ_1 = h_0, γ_{j+1} = e_j·w_jΦ_j + h_j, W_j := w_jΦ_j =
e_{j−1}g_{j−1}γ_j; letters z_j ∈ K_j (units, ψ(0) ≠ 0), z̄ := z_{n+1},
K := K_{n+1}; E_0 := 1, E_j := e_0⋯e_{j−1}, E := E_{n+1}. Split
γ ↦ (s_1..s_{n+1}, u_1) by iterated eq-(12); β_j(γ) = the split's own
level-j weight; the split abscissa satisfies s_j(γ) = ℓ_{j−1}β_j(γ) mod
e_{j−1} (eq-12 at read (e_{j−1}, h_{j−1})). [ILN]† S0.3 pair data:
δ := ⌊(s_{n+1}+s′_{n+1})/e_n⌋, S_n := δγ_{n+1}, and for j = n..1

    D_j := (s_j-defect + ℓ_{j−1}S_j)/e_{j−1},   s_j-defect := s_j + s′_j − s″_j,
    S_{j−1} := D_jγ_j + S_j·(ℓ′_{j−1} − ℓ_{j−1}W_{j−1}).

**THE WELD COCHAIN (the one new name; content = [JA]†'s JA-EPS).** Per
level j (read (e_{j−1}, h_{j−1})), for β ∈ ℤ:

    t_j(β) := (ℓ_{j−1}·β − s(β))/e_{j−1} ∈ ℤ,    s(β) := ℓ_{j−1}β mod e_{j−1},
    ε_j(β)  = z_j^{−t_j(β)}                       [JA-EPS, PROVED in [JA]†],
    E(γ)   := ∏_{j=1}^{n} ε_j(β_j(γ))             (embedded in K; γ ∈ ℤ),
    A_j    := ℓ_{j−1}·g_{j−1}·γ_j  (j ≥ 1;  A_j = 0 ⟺ e_{j−1} = 1).

t_j is exactly the print twist exponent in eq12-canonical coordinates
(JA-EPS's sign convention — the Prop-`construct` CHILD orientation, [JA]†
§3.2's display; NOT Def-`t(i)`'s opposite sign). Nothing in this note
re-proves JA-EPS; the field identifications below consume it.

## S1. THEOREM WELD-M (the master transport; four faces, each a citation)

**THEOREM WELD-M.** For every tower T of the [ILN]† S0.1 class realized as
a principal-read OM type via the dictionary map T(t) (JA-PIN — the DOMAIN
identification, consumed: every class-pin clause forced by the print's own
hypotheses, lift clause = W-2), there is ONE transport 𝕋 between the
harness calculus (Φ-developments, weights w_m, reads R_m v, the ε-kit,
canonical lifts) and the classifier/print calculus (φ-adic developments,
v_{m+1}, residual operators, t(i)-twists, GMN keys), with five clauses:

    (M0) [substrate]      𝕋 is the IDENTITY on the underlying division
         arithmetic: the same canonical division chain by the same monic
         key at the admissible representative.
    (M1) [gradings]       𝕋 preserves weights in the sheared frame
         (w_m = v_{m+1}), and its induced map on polygon/grading data is
         the explicit affine shear Σ_q(i,u) = (i, e_q·u + h_q·i) — lower
         hulls to lower hulls, vertex-for-vertex, slope law s ↦ e_q s + h_q.
    (M2) [reads/operators] 𝕋 acts on packed read data by explicit PER-SLOT
         z-characters generated by ONE 1-cochain — the S0 weld cochain
         t_j/ε_j: scalar per slot exactly on the S3 perimeter, exact
         recursion ((HR-REC) genre) elsewhere. Never slot-independent
         (JA-BOX-1 inherited verbatim).
    (M3) [multiplication] 𝕋 transports multiplication up to the carry
         cocycle: on B_n coordinates the target is the twisted group
         algebra K^c[ℤ/E] with c = z̄^δ·∏_j z_j^{D_j} on the scored
         stratum, and harness-val = TC-read.
    (M4) [covariance]     𝕋 is covariant in the lift/representative
         choice: changing the representative acts on (M2)–(M3) by the
         (ξ, w) character system, with ψ-transport making the two chains
         carry the same type.

*Proof = the face table.* Each clause IS the cited composed theorem, at
that theorem's own grade and on its own perimeter; the identifications in
the middle column are the domain/codomain pins the synthesis adjudicated
(SUBSUMED-PLUS-SHARPENING at all four junctions, [SYN] §1.2).

| clause | citation (proof of the clause) | identification displayed | conditionality carried verbatim |
|---|---|---|---|
| (M0) | **[JB]† JB-DEV(i)** (same division, digit-for-digit) + **[JA]† JA-PIN** clauses 1–7 (domain) + **[W2]† W2-C1** (representative legitimacy) | JA-PIN: T(t) satisfies every class-pin clause except the lift clause (= W-2); the representative is φ_{q+1} := Φ_q^har | W-2 clause 1's perimeter; JB §0M rows 1–2; byte clause on `P≤q` only |
| (M1) | **[JA]† JA-VAL** (w_m = v_{m+1}) + **[JB]† JB-AFF + JB-VTX** (H(f) = Σ_q(U(f)) vertex-for-vertex; the sheared frame IS the print's own next-level bookkeeping) + **[JA]† JA-GRID** (grid face: eq-(12-int) = T-side initial point; carry = lattice crossing) | the shear Σ_q is the induced affine map on gradings; the read side is horizontal at height w_{q+1}(f) in the sheared frame | shared-key perimeter `P<q`, 0 ≤ q ≤ qcap; JA-GRID(a)'s u ≥ 0 proviso (undischarged, JB §0M col (b)); JB-VTX(d4) NO-LEG rides |
| (M2) | **[JA]† JA-EPS** (ε_m = z^{−t_m}: the cochain identification) + **JA-RES** (per-slot law c_i = z_{m−1}^{−i·A_{m−1}}·C_i, unconditional at m = 2) + **[W2]† W2-C2/(HR-REC)** (exact recursion; scalar form on (C-coll)) | the ε-kit IS the print's t(i)-twist in eq12-canonical coordinates; all transport characters are values/differences of ONE cochain (S2, S3) | JA-RES per-digit proviso at m ≥ 3 / (R-coll); (C-coll) at m ≥ 2; W2-BOX-1 mod-wrap; JA-BOX-1: PER-SLOT, never scalar |
| (M3) | **[JC]† W-6/W-7/W-8/W-9** (target exists; Ψ iso with inner normalization ∏_{j≤m} z_j^{D_j} on the scored stratum; harness-val = TC-read; K^c[ℤ/E]) | **JC-LOC (the CODOMAIN pin): B = gr(w)[in(π)^{−1}] ≅ gr_{K[x]}(w) — "B *is* the object FGMN's theorems speak about"**; 𝒜(T) = the whole transported ring (JC-F2's corrected display) | [ILN]† scored stratum; (DMULT-w) CITED / (DMULT-s) MEASURED tier split; GRB §0 ladder; JC-BOX-2/-4/-8 |
| (M4) | **[W2]† W2-C2 + §3.4** (the (ξ, w) closed form: ξ_{m+1} = χ_m^{γ_{m+1}}·z_m^{−e_m A_m}, w_{m+1} = χ_m^{−g_mγ_{m+1}}, the χ-chain; print tie z_m^{−A_m} = c₁) + **W2-C3** (ψ-transport: strict representative at every level of the transported chain, no weight/support splits) | the covariance seed is the cochain at the key weight: c₁ = ε_m(W_m) (S3's seed identity); the χ-multiplier = the [ILN]† shift-chain descent operator (byte-identical displays, [W2]† §3.4 rk. 1) | scalar closed form on (C-coll) only (exact law = (HR-REC)); §4.3 ℓ-orbit convention fence; **W2-OPEN-1 (value layer) OPEN — inherited displayed** |

∎ (each row = consumption; no row is re-proved here).

**Remark (what WELD-M is and is not — the honest-content sentence,
[SYN] §1.3 verbatim in substance).** WELD-M is an ORGANIZING UMBRELLA
engineered so that the four composed junction theorems are its faces; it
proves no new instance and discharges no open leg (W2-OPEN-1, the (VD-m)
strata, (DMULT-s), JB's rows 5/12/22 evidence frontier all ride). Its net
new content is exactly two displays: S2 (the coboundary theorem — the one
theorem-shaped new item) and S3 (the one-perimeter fence). What each
junction note carries BEYOND its face (its closed forms, boundary censuses,
box systems) remains in that note and is NOT absorbed.

## S2. THEOREM WM-COB — the coboundary display (the new 3-line theorem)

**THEOREM WM-COB.** Let (γ, γ′) be a pair with [ILN]† S0.3 data
(δ, S_j, D_j) and per-level split weights β_j := β_j(γ), β′_j := β_j(γ′),
β″_j := β_j(γ+γ′).

**(i) [integer form — footprint: [ILN]† SHIFT-(n) + D_j-INT only, both
unconditional; γ, γ′ ∈ ℤ arbitrary, ALL pairs incl. DCX].** For every
level j = 1..n:

    D_j  =  t_j(β″_j) − t_j(β_j) − t_j(β′_j)   =: (∂t_j)(γ, γ′).

**(ii) [field form — adds JA-EPS, PROVED in [JA]† at 0/2].** In K_j:

    z_j^{D_j} = ε_j(β_j)·ε_j(β′_j)·ε_j(β″_j)^{−1}.

**(iii) [composite display — adds the [ILN]† VALUE LAW, scored stratum].**
With ∂E(γ,γ′) := E(γ)E(γ′)/E(γ+γ′):

    c_{n+1}(γ, γ′)  =  z̄^δ · (∂E)(γ, γ′).

THE ENTIRE INNER FACTOR OF THE ACCEPTED COCYCLE IS A COBOUNDARY — of the
composite ε-kit cochain E. The outer letter z̄^δ is NOT a coboundary of
this cochain (it lives in the NEXT letter; see the residue fence below).

*Proof.* (i) Abbreviate ℓ := ℓ_{j−1}, e := e_{j−1}, s(·) := the level-j
cochain remainder. Two consumed inputs: (a) the split abscissa tie
s_j(γ) = s(β_j) (S0: the split computes s_j by eq-12 at β_j, and eq-12's
abscissa is ℓβ mod e — a definition, not a claim); (b) [ILN]† Lemma
SHIFT-(n): β″_j = β_j + β′_j + S_j, unconditional. Compute:

    t_j(β_j) + t_j(β′_j) − t_j(β″_j)
      = [ ℓ(β_j + β′_j − β″_j) − (s(β_j) + s(β′_j) − s(β″_j)) ] / e
      = [ −ℓ·S_j − s_j-defect ] / e                    [(b), then (a)]
      = −D_j                                            [S0.3's definition].

Every step is integer arithmetic; t_j(β) ∈ ℤ always (s(β) ≡ ℓβ mod e).
(ii): raise z_j to (i) and apply JA-EPS (ε_j = z_j^{−t_j}). (iii): multiply
(ii) over j = 1..n inside K (each ε_j embedded) — the product telescopes to
∂E — and substitute into the accepted value law c_{n+1} = z̄^δ·∏_j
z_j^{D_j} on its own stratum. ∎

**Remark (relation to [ILN]†'s integer layer).** The congruence at the
heart of [ILN]† Lemma D_j-INT (s_j-defect + ℓS_j ≡ 0 mod e via SHIFT) is
precisely the statement that (∂t_j) is an integer; WM-COB(i) REFINES it by
identifying WHICH integer: the coboundary of the print-twist cochain at the
split's own arguments. Nothing in [ILN]† is re-proved or amended; the
identity gives its integer layer a second, cohomological reading. Note the
footprint ordering ([SYN] §2.2 LAW-1): (i)–(ii)'s conditionality is
STRICTLY SMALLER than the cocycle value law's own (no stratum needed).

**The four normalization laws as faces of the one cochain (the [SYN] §2
dictionary, consumed as displays; grades ride the owning notes).**
LAW-2 (J-B): LEMMA JB-EPS is WM-COB(i) with S_j ≡ 0 — the PLAIN coboundary
∂t_m(V,V′) = ε′ = ⌊(s^wt(V)+s^wt(V′))/e⌋; [ILN]†'s restart case (S_j = 0 ⟹
D_j = δ^pl) is the same face. LAW-3 (J-A): the JA-RES character exponent
i·A_{m−1} is the cochain's first difference along the key sublattice
(t_m(V + kW_m) = t_m(V) + kA_m, carry-free since s(W_m) = 0). LAW-4 (W-2):
the covariance seed c₁ = z_m^{−A_m} = ε_m(W_m) is the cochain at the key
weight, and the χ-chain multiplier is the [ILN]† shift-chain descent
operator. LAW-1 is WM-COB itself.

### S2.1 LEMMA WM-RHO (the period constant of the composite cochain)

For every γ ∈ ℤ:  E(γ + E)/E(γ) = ρ_T, the γ-INDEPENDENT constant

    ρ_T := ∏_{j=1}^{n} z_j^{ −ℓ_{j−1}·E_{j−1} }.

*Proof.* γ ↦ γ+E shifts β_n by E/e_n = E_n (top eq-12: s_{n+1} unchanged
since ℓ_n E ≡ 0 mod e_n, u_{n+1} shifts by E/e_n), and inductively β_j by
E_j (E_j ≡ 0 mod e_{j−1} keeps every s_j fixed, u_j shifts by E_{j−1}). So
t_j(β_j + E_j) = t_j(β_j) + ℓ_{j−1}E_{j−1}, and each ε_j picks up the fixed
factor z_j^{−ℓ_{j−1}E_{j−1}}. ∎ [Machine: WM-RHO.]

### S2.2 COROLLARY WM-CLASS (the cohomological corollary — this EXPLAINS JC-F1)

Let σ : ℤ/E → W be the minimal window section (the engine's
`window_reps`), Ẽ := E∘σ (a genuine ℤ/E-cochain), and κ(ν,ν′) :=
(σν + σν′ − σ(ν+ν′))/E ∈ ℤ_{≥0} (the section carry; census S5). Then
∂Ẽ = ∂E·ρ_T^{κ} on classes, hence on the scored stratum (where the value
law holds and c descends to ℤ/E, [JC]† W-9(i)):

    c(ν, ν′) = z̄^{δ(ν,ν′)} · ρ_T^{−κ(ν,ν′)} · (∂Ẽ)(ν,ν′),   i.e.
    [c] = [ z̄^δ · ρ_T^{−κ} ]   in H²(ℤ/E, K^*).

The full inner word ∏_j z_j^{D_j} is PURE GAUGE: the class of the twisted
algebra K^c[ℤ/E] = 𝒜(T) is carried by the outer letter z̄ (through δ) and
the single period constant ρ_T (through the section carry) alone. **This
explains FINDING JC-F1 cohomologically**: 𝒜(T) ≅ K[v]/(v^E − ζ_T)
abstractly at every composite stage BECAUSE twisting by a coboundary does
not change the algebra class — only the outer/period data can obstruct
cyclicity, and it never does abstractly. It is CONSISTENT with the cyclic
fence: (CYC) is a property of the anchor-indexed PRESENTATION (the specific
cochain), and coboundaries are exactly what presentations see and classes
do not — the fence and the abstract cyclicity are the two sides of "cochain
vs cohomology class", not a tension. Grade: rides [ILN]† value law + [JC]†
W-9 (0/2) + WM-COB; display-level, review-owed like every new statement
here. [Machine: WM-RHO + the κ census; the class identity itself is
arithmetic from WM-COB + WM-RHO, no separate leg.]

### S2.3 The residue fence (what is NOT a cochain value)

**J-B's C-READ constant c_m = ψ_{m,0} = −z_{m+1} is the OUTER letter, not
a value of the weld cochain.** The level-≤m cochain generates only
monomials in z_1..z_m; c_m is the NEXT residual letter — TC-3's defining
relation at g_m = 1 (ψ_m(z̄) = 0 ⟺ z̄ = −ψ_{m,0}) surfacing as a transport
constant ([JB]† §5; [JC]† §3.3's germ split: CONFIRMED as value law on all
27 eligible stages, REFUTED as inner-factor reading, 138/669). Assignment:
c_m belongs to the z̄^δ family — the part WM-COB(iii) shows is NOT ∂E.
Likewise the mod-wrap boundary (W2-BOX-1's I4B r = 5 witness) and the
χ-chain at m ≥ 2 are NOT reduced to cochain values by this note — the wrap
is where the scalar one-cochain picture fails, and it fails at the SAME
boundary in all four notes (S3's caveat). FENCED; no claim otherwise.

## S3. THEOREM WM-FENCE — the one-perimeter fence

**Definition (the level-μ transport character family; μ ≥ 1).**

    χ^{(μ)}_i := z_μ^{ −i·A_μ }   (i ∈ ℤ),      A_μ = ℓ_{μ−1}g_{μ−1}γ_μ.

**Seed identities (the fence characters ARE cochain data; both consumed
proved, [JA]† JA-EPS + W2-L2):** χ^{(μ)}_i = ε_μ(β + i·W_μ)/ε_μ(β) for
every β (the key-lattice first difference: t_μ(β + iW_μ) = t_μ(β) + iA_μ,
carry-free); and z_μ^{−A_μ} = ε_μ(W_μ) = c₁, Theorem-`phir`'s constant.
[Machine: WM-FENCE-XI.]

**(PERIM-μ on S), the one condition:** χ^{(μ)}_i = 1 for every i ∈ S,
S ⊆ ℤ a set of abscissas. Absolute form: ord(z_μ) | A_μ (then S = ℤ);
slot-grid form: ord(z_μ) | e_μ·A_μ (then S = e_μℤ). Absolute ⟹ slot-grid;
the converse fails in general (the honest gap, censused in S5).

**THEOREM WM-FENCE.** The three collapse fences of the weld are three
specializations of (PERIM):

**(a) [(R-coll), J-A].** JA-VDIND's absolute character-triviality at read
level m — "z_{m−1}^{i·A_{m−1}} = 1 for every attained abscissa i" — IS
(PERIM-(m−1) on the attained abscissa set of the object). (R-coll) at level
m is its every-recursion-node form (2 ≤ q ≤ m−1). *Proof: citation;
[JA]† §3.4's display is this condition verbatim.*

**(b) [the (VD-m) proviso, J-B].** JB-CREAD's governing fence consumes
JA-VDIND verbatim ([JB]† §0M column (c): "at every m ≥ 2 a HYPOTHESIS —
JA-VDIND's ABSOLUTE character-triviality"); hence = (a) = (PERIM) at the
same attained sets. Unconditional at m ≤ 1 only ((VD-1) = W2-L3). *Proof:
citation of the r1/F1-repaired fence.*

**(c) [(C-coll), W-2].** (C-coll) demands every interior junction character
trivial: ξ_Q = 1, ξ_Q = χ_{Q−1}^{γ_Q}·z_{Q−1}^{−e_{Q−1}A_{Q−1}} ([W2]†
§3.4). AT TRIVIAL LOWER χ-CHAIN (χ_{Q−1} = 1 — e.g. every m = 2 junction,
where χ_1 := 1):

    ξ_Q = z_{Q−1}^{ −e_{Q−1}·A_{Q−1} } = χ^{(Q−1)}_{e_{Q−1}} = ϑ_Q,

exactly JA-VDIND's slot character ϑ — so (C-coll) at that level is
(PERIM-(Q−1) on the junction slot grid e_{Q−1}·ℤ): the SLOT-GRID
specialization (W-2's junction slots sit at s + j·e_{Q−1}; the j-dependent
character part is ϑ_Q^j). *Proof: read off the §3.4 display at χ = 1; the
grid statement is [W2]† §3.2's letter-twist sentence.*

**The honest caveat (carried, not erased — [SYN] §1.3's own words).** The
alignment is exact only MODULO the χ-chain corrections at deeper levels
(χ_{Q−1} ≠ 1 makes ξ_Q a χ-corrected character, not a bare χ^{(μ)} value)
and the MOD-WRAP boundary (W2-BOX-1's I4B r = 5 witness: a support-
invisible interior character re-emerging through monomial reduction). The
one-perimeter statement does NOT scalarize the wrap; the exact law off the
perimeter remains (HR-REC) [W-2] / the per-slot recursion [J-A] — and the
scalar forms of all four notes die together at this same boundary, which is
the one-perimeter observation seen from the failure side.

**THE THREE-MASTER-FENCE SURFACE (what a consumer of WELD-M carries,
replacing four per-note fence systems as a READING AID — the four notes'
own surfaces stay authoritative until the next fold):**

    (F-a) the SHARED-KEY / BYTE perimeter — (M0)'s hypothesis: `P<q` for
          the (VAL)/(GRID) layers, `P≤q` for the (RES) layer ([JB]† §0M
          (a1)/(a2)); off it the print frame is a different computation.
    (F-b) the COLLAPSE perimeter — THIS section's (PERIM) condition at the
          appropriate abscissa sets ((a)/(b)/(c) above), with the χ-chain
          and mod-wrap caveat displayed.
    (F-c) the LITERATURE/CONVENTION fence — (DMULT-w) CITED / (DMULT-s)
          MEASURED ([JC]† tier split), the unpinned-ℓ orbit convention
          (JA-BOX-3 / [W2]† §4.3), the FGMN numbering re-verification owed,
          and the [RMG]/LED-Λ attempt grades where [JB]† consumes them.

**Consequence for the four notes' fence surfaces.** Each note's collapse
fence becomes a DERIVABLE DISPLAY of (F-b): (C-coll) = slot-grid (PERIM) +
χ-corrections; (R-coll) = absolute (PERIM) at recursion nodes; (VD-m) =
absolute (PERIM) at attained sets. **No note is edited by this
consolidation** — the four fence surfaces stand as committed; if a future
fold brackets them onto (F-b), that fold cites this section. (The campaign
motivation, recorded: JB's r1–r4 arc exists because per-site fence patching
did not converge — "a fifth sweep would find a sixth site"; one perimeter
stated once is the same medicine at campaign level.)

## S4. HONEST GRADE — the full conditionality stack

**One line.**
`[ILN]† ACCEPTED (SHIFT-(n)/D_j-INT unconditional; value law on the scored
stratum; residuals (RM-m ≥ 2), (W-MULT-DCX-m), standard-lift) + W-2/J-A/
J-B/J-C at ATTEMPT 0/2 each (their boxes verbatim: (C-coll)+W2-BOX-1+
W2-OPEN-1; JA-BOX-1..5+(R-coll); JB §0M incl. rows 5/12/22 NO-LEG; JC's
(DMULT-w/s) tiers + GRB ladder + JC-BOX-2/4/8 + JC-F1/F2 review-owed) +
GRB/CARRY-1/D-REAL accepted-conditional + FGMN cites (numbering
re-verification owed) + LED-Λ attempt ⟹ this note, own arc 0/2.`

Itemized honesty:

* **Per-claim footprints differ and are displayed at the claim.** WM-COB(i)
  rides [ILN]† alone (unconditional); (ii) adds JA-EPS ([JA]† 0/2); (iii)
  adds the value law (scored stratum); WM-CLASS adds [JC]† W-9; WELD-M's
  faces ride their notes wholesale; WM-FENCE(a)/(b) are citations, (c) is a
  one-line derivation from [W2]†'s display.
* **The synthesis spot checks** (7,999/0, 5 towers, 6 families) are
  MEASURED SUPPORT for S2's dictionary, cited as such — a scratch
  instrument with no seal and no teeth. This note's own evidence leg is S5.
* **NOT claimed, NOT discharged, NOT retired:** W2-OPEN-1 (the transported
  value layer) stays OPEN; the (VD-m) strata stay conditional exactly as
  [JB]† §0M has them; (DMULT-s) stays MEASURED-only; JB rows 5/12/22 stay
  NO-LEG; the J3b BLOCKED-ON-CARRIER-TIE gate stands; hExhaust and every
  Phase-B Lean obligation untouched; the P0 application gate stands. NO
  consumer retirements: nothing that today cites a junction note may
  re-point to this note at better grade (there is none to give).
* **No grade upgrade by composition.** A theorem whose proof is a citation
  table is exactly as conditional as its worst-cited row.

## S5. MACHINE BRACKET — weldmaster_checks.py (two-commit seal)

**Runner:** `verification/openmath/weldmaster_checks.py`. Commit 1 = this
note + the runner, battery UNRUN on the full roster (pre-seal smoke on the
4-row subset {C2A, C2I, C3A, I4B} disclosed in the docstring: all families
0 violations, all four teeth firing); commit 2 appends the verdict below
FROM the committed artifacts (`weldmaster_checks_output.txt` /
`weldmaster_checks_results.json`).

**Roster:** `grt_jc_probe.ROSTER`, imported FROZEN and md5-pinned (29
towers: m ≤ 3, NR ≤ 4, p ∈ {2,3,5}, d₀ ≤ 3, wild e_j = p legs incl. p = 5,
g_j = 2 branching rows, eq-char F_p[[t]] rows, flat legs, I4A/I4B/I4C) —
the sealed J-C instrument's tower-construction path (`ITL.build_tower`)
verbatim. ≥ 25 towers incl. wild legs, as charged.

**Decorrelation:** the cochain t is implemented FRESH from raw read
integers; `Tower.eps`/`Tower.constants`/`Tower.split` are the committed
engine leg of each comparison; the M1 shear leg uses a FRESH monotone-chain
lower hull with exact Fraction slopes (its min tie recomputes the engine's
own weight recursion — disclosed as a sanity leg, not IND).

**Families and SEALED PREDICTIONS (any observed count differing from its
prediction is RED):**

    WM-PIN       md5 pins on iterlawn_pe_reimpl.py + grt_jc_probe.py.
                                                          PREDICTED 0.
    WM-EPS       committed eps == z^{−t}, t FRESH (JA-EPS re-keyed).
                                                          PREDICTED 0.
    WM-COB-I     WM-COB(i): D_j == ∂t_j, every level, every sampled pair
                 (dint_ok gate reported).                 PREDICTED 0.
    WM-COB-OFFW  the same on off-window pairs (γ−E legs) — the "γ,γ′ ∈ ℤ
                 arbitrary" scope of [ILN]† S2.           PREDICTED 0.
    WM-COB-F     WM-COB(ii) in K_j.                       PREDICTED 0.
    WM-COB-C     WM-COB(iii): inner == ∂E in the top field AND the full
                 z̄^δ display.                             PREDICTED 0.
    WM-RHO       LEMMA WM-RHO: E(γ+E)/E(γ) == ρ_T (constant, closed
                 form); κ census reported for WM-CLASS.   PREDICTED 0.
    WM-FENCE-XI  seed identities: t(kW) = kA (integers), ε(W) = z^{−A}
                 (c₁ tie), ε(eW) = z^{−eA} (slot char).   PREDICTED 0.
    WM-FENCE-EQ  brute character triviality == ord-divisibility criteria
                 (absolute + slot forms); absolute ⟹ slot asserted;
                 strict-gap census reported.              PREDICTED 0.
    WM-SHEAR     M1 re-key: fresh-hull(Σ_q(U)) == fresh-hull(H)
                 vertex-for-vertex + slope law + min tie. PREDICTED 0.

**Teeth (each must fire ≥ 1 GLOBALLY or the battery is RED):**

    WM-T-SIGN    Def-t(i)-sign cochain must break WM-COB-I.   FIRES ≥ 1.
    WM-T-DELTA   z̄^{δ+1} must break the composite display.    FIRES ≥ 1.
    WM-T-SHEAR   garbled shear (h_q+1) must break the vertex law.
                                                              FIRES ≥ 1.
    WM-T-XI      A_μ+1 must break the c₁ tie.                 FIRES ≥ 1.

**[VERDICT — appended at commit 2 from the committed artifacts
(`weldmaster_checks_output.txt` / `weldmaster_checks_results.json`; runner
md5 6b406f81c250d25f615f715fa9eff474, byte-unchanged seal → verdict).]**

**ALL GREEN — 0 violations across all 10 families, every sealed prediction
met; all four teeth fired.** The battery: **29/29 roster towers built**
(NR = 2/3/4; E up to 24; wild p ∈ {2,3,5} legs; d₀ ≤ 3; eq-char rows;
I4A/I4B/I4C), **7,208 samples total** — WM-PIN 2 (both md5s intact) ·
WM-EPS 615 · WM-COB-I 1,885 (every level of every dint_ok pair; the
dint_ok gate never excluded a pair, consistent with D_j-INT) ·
WM-COB-OFFW 513 (off-window γ−E legs, the "γ,γ′ ∈ ℤ arbitrary" scope) ·
WM-COB-F 1,885 · WM-COB-C 897 (the full z̄^δ·∂E display, top-field
composite) · WM-RHO 87 (the period constant exact on every sampled γ of
every tower) · WM-FENCE-XI 349 · WM-FENCE-EQ 171 · WM-SHEAR 804 hulls
(342 with ≥ 2 vertices — the shear law exercised on genuinely multi-vertex
polygons). Teeth: WM-T-SIGN 374 · WM-T-DELTA 861 · WM-T-SHEAR 514 ·
WM-T-XI 47 — all ≥ 1, battery has teeth on every new display. Census
(reported, not violation-keyed): fence rows **22 absolute-(PERIM) / 9
SLOT-ONLY / 26 neither** — the 9 slot-only rows are the machine-realized
honest gap between (C-coll)'s slot-grid form and (R-coll)'s absolute form
(S3's "the converse fails in general", now instance-backed); κ section-
carry histogram {0: 292, 1: 87, 2: 18, 3: 37, 4: 6, 5: 9, 6: 2, 7: 6} —
κ is NOT {0,1}-valued (WM-CLASS correctly makes no such claim). Elapsed
0.6 s; deterministic, exact arithmetic.

## S6. Claims table, dependency line

| # | claim | status | rests on |
|---|---|---|---|
| WM1 | THEOREM WELD-M (M0)–(M4), faces = the four composed junction theorems, identifications displayed | PROVED-BY-CITATION at the cited grades (0/2 each) | [W2]†+[JA]†+[JB]†+[JC]†, [ILN]† |
| WM2 | WM-COB(i) integer coboundary D_j = ∂t_j | PROVED (complete proof, S2) | [ILN]† SHIFT-(n)+D_j-INT (unconditional) |
| WM3 | WM-COB(ii) field form | PROVED | WM2 + JA-EPS ([JA]† 0/2) |
| WM4 | WM-COB(iii) c_{n+1} = z̄^δ·∂E | PROVED on the scored stratum | WM3 + [ILN]† value law |
| WM5 | LEMMA WM-RHO period constant ρ_T | PROVED (complete proof) | S0 arithmetic |
| WM6 | COROLLARY WM-CLASS [c] = [z̄^δ·ρ_T^{−κ}]; explains JC-F1 | DISPLAY (review-owed) | WM4+WM5+[JC]† W-9 |
| WM7 | residue fence: c_m = −z_{m+1} is the outer letter, NOT a cochain value; mod-wrap/χ-chain not reduced | FENCE (displayed) | [JB]† §5, [JC]† §3.3, W2-BOX-1 |
| WM8 | WM-FENCE (a)/(b): (R-coll), (VD-m) = absolute (PERIM) at attained sets | PROVED-BY-CITATION | [JA]† JA-VDIND, [JB]† §0M(c) |
| WM9 | WM-FENCE (c): (C-coll) at trivial lower χ = slot-grid (PERIM); caveat carried | PROVED (one line) + caveat | [W2]† §3.2/§3.4/W2-BOX-1 |
| WM10 | three-master-fence surface (F-a/b/c) as consumer reading aid; four notes' surfaces untouched | DISPLAY + FENCE | S3 |
| WM11 | machine leg: 10 families + 4 teeth on the frozen 29-tower roster, two-commit sealed | [commit 2] | S5 |
| WM12 | consumption-only; no retirements; out-of-scope items queued | FENCE | header |

**Dependency line.** [ILN]† (ACCEPTED) ⟶ WM-COB ⟵ JA-EPS ([JA]† 0/2);
WELD-M ⟵ all four junction notes at 0/2 (the grade cap); WM-CLASS ⟵ [JC]†
W-9. Downstream (design, not executed): the four hostile ARCS remain the
campaign's gating work — this note must not displace them; the J-D block
(J-D0 → W-10 at the (2,1,1) shape → W-11) consumes WM-FENCE's (F-b)-freedom
observation only through the already-adjudicated (J-D0) route; supersession
brackets for the four fence surfaces happen at the next fold, citing S3.

— WELD MASTER-TRANSPORT COMPOSER, campaign date 2026-08-08 (wallclock
2026-08-06).
