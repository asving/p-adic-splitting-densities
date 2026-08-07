# OPEN2ATTACK — the W2-OPEN-2/OPEN-2a box attacked examples-first: the defeat-equation reduction, the σ′-covariance mechanism, and the m ≥ 2 battery

**Unit:** W2-OPEN-2 ATTACK (Asvin's examples-first directive 2026-08-05;
constructed-counterexamples directive 2026-08-04). **Genre: ATTACK NOTE at
attempt grade (acceptance counter 0/2; no hostile pass run; disclosure-grade
honesty).** The target note `GRTW2_PROOF_2026-08-08.md` is ACCEPTED-FROZEN
and is NOT edited by this unit; anything here that closes or narrows its box
is delivered as PROPOSED ANNEX TEXT (§7) for the orchestrator.

**Target.** W2-OPEN-2/OPEN-2a (GRTW2 §5.2, accepted AS A BOX): canonical-lift
covariance above ξ ≠ 1 twist junctions, whose premise sub-clause (OPEN-2a) —
the FORWARD direction of the recorded-ξ/byte-divergence identification — is
PROVED at m = 1 (LEMMA W2-ID1) and OPEN at m ≥ 2:

> **(OPEN-2a)** at a junction at level m+1 with m ≥ 2, keys below
> byte-shared and recorded ξ = 1, the raw print key is byte-equal to the
> harness key.

The converse (recorded ξ ≠ 1 ⟹ byte-RED) is UNPROVED at every m with PE3's
counter-instance displayed at GRTW2 §5.2; this unit does not touch that
verdict (it extends its instance geography to m ≥ 2, §5).

**Machine bracket:** `verification/openmath/open2attack_checks.py` (this
unit; outputs `open2attack_output.txt`, `open2attack_results.json`).
Engine = committed `iterlawn_pe_reimpl` verbatim + `TowerX` (a DISCLOSED
copy of the Tower constructor with the ψ-degree validation generalized from
the hard-coded g ≤ 2 to a brute-force irreducibility test, and RAW
coefficient specs — the two changes are marked `[disclosed change]` in the
source); classifier = the sealed probe's `GmnLeg` verbatim; junction
helpers (`orbit_scan`, `actual_ratios`, `junction_data`, `orbit_satisfies`)
imported verbatim from the sealed `grt_w2_checks.py`. "Recorded" below
always means the SEALED scan semantics (first satisfying ξ in `F.elems()`
enumeration order), exactly as frozen.

---

## §1. The reduction: strictness ⟺ the simultaneous-defeat equations

Setting: a junction at level m+1 (GMN r = m+2) with keys byte-shared below
(φ_q^cls = Φ_{q−1}^har for 2 ≤ q ≤ r−1); slot field K_m, modulus ψ = ψ_m,
g = g_m, e = e_m; supp := {j < g : ψ_{m,j} ≠ 0} (0 ∈ supp by the class pin).
Both keys are (key)^{eg} + Σ_j (slot digit)·(key)^{ej}: harness digits
C_j = realize_m(ε_m(β_j)^{−1}ψ_{m,j}, β_j), print digits P_j (Prop-
`construct` children), shared monic top digit 1 at abscissa eg. Write

    ρ_j := R_m v(P_j) / R_m v(C_j)          (slot read ratio, j ∈ supp;
                                             ρ_top := 1 — shared digit),
    R_j := slot-j coefficient of rres(r−1, Φ_{m+1}^har)
           (the PRINT residual of the HARNESS lift — what the recorded
            pair sees),
    δ_j := R_j · ρ_j / (c · ψ_{m,j})        (the GAUGE DISCREPANCY),

c = Thm-`phir`'s constant. δ_j has the invariant meaning: the print
evaluator applied to the two builders' slot digits, each normalized by its
harness read — δ_j = [Prnt_j(C_j)/R_m v(C_j)] / [Prnt_j(P_j)/R_m v(P_j)],
where Prnt_j is the rres slot evaluator at ordinate u_j and
Prnt_j(P_j) = c·ψ_{m,j} is Thm-`phir` (machine family OA-PHIR).

**LEMMA OA-L1 (top tie).** R_top = c. *Proof.* The two keys' dev digits at
abscissa eg are the identical byte 1 with identical ordinate u_top, so the
rres slot evaluator computes the identical value on both; on the print key
that value is c·ψ_{m,g} = c (Thm-`phir`). ∎ [Machine: OA-TOPRES.]

**LEMMA OA-L2 (gauge factorization).** R_j = δ_j·c·ψ_{m,j}/ρ_j for every
j ∈ supp — the definition of δ_j read as a factorization of the recorded
residual through the slot ratios. [Machine: definitionally exact; the
content is OA-PHIR + OA-TOPRES.]

**LEMMA OA-L3 (strictness = the defeat equations).** The junction is STRICT
(∃ unit w: rres(Φ^har) = w·ψ coefficientwise — equivalently the recorded
pair CAN be (1, w); recorded ξ = 1 always implies strict) iff

    (DEFEAT)      δ_j = ρ_j   for every j ∈ supp.

*Proof.* Strict at the top slot forces w = R_top = c (OA-L1); then
R_j = c·ψ_{m,j} ⟺ δ_j·c·ψ_{m,j}/ρ_j = c·ψ_{m,j} ⟺ δ_j = ρ_j (OA-L2,
ψ_{m,j} ≠ 0 on supp). ∎

**LEMMA OA-L4 (byte law).** The junction is byte-equal iff ρ_j = 1 for
every j ∈ supp. *Proof sketch (attempt grade).* (⟹) trivial. (⟸) Slot by
slot: C_j and P_j are exactly-on-line built objects at the same weight β_j
with equal level-m reads. Claim: a realize output and a construct output
(over byte-shared keys) with equal (weight, read) are byte-equal — by
induction on the level: the packed read Σ_{i<g_{q−1}} c_i z_q^i determines
its K_{q−1}-coordinates uniquely (deg ψ_{q−1} = g_{q−1}); both builders
place level-(q−1) children at the same grid abscissas (eq12 for realize,
W2-L0 for construct) with the same exact child weights, and the child
reads are the ε-corrected coordinates on BOTH sides (REALIZE R3 for the
harness; (HR-REC) for the print), hence equal; descend; at level 0 the
digit π^u·lift(res) is determined by (weight, read) under (P-lift); the
assemblies then agree since the keys below are byte-shared. Consumes:
(HR-REC), W2-L0, REALIZE R1–R3 — all accepted GRTW2/[ILN]† content. ∎
[Machine: OA-RHOBYTE.]

**COROLLARY OA-C1 (the counter-instance normal form).** A counter-instance
to (OPEN-2a) in strict form — a shared-below junction that is strict yet
byte-RED — is EXACTLY a solution of the simultaneous system

    δ_j = ρ_j  (∀ j ∈ supp)   with   ρ_{j*} ≠ 1  (some j* ∈ supp),

and any counter-instance to the box's literal premise clause (recorded
ξ = 1, byte-RED) is in particular one of these (recorded triviality ⟹
strict). Conversely byte-equal ⟹ strict with w = c (OA-PHIR + OA-L4;
machine OA-BWD) — so on any instance domain the whole identification
census is determined by the (δ, ρ) table. This is the constructed-
counterexamples directive's target system: solve (DEFEAT) with ρ ≢ 1, or
prove it infeasible.

**Remark (where W2-ID1 sits).** At m = 1 the gauge is the scalar ε-kit
(W2-L3): δ_j ≡ 1, so (DEFEAT) forces ρ_j = 1 — byte-equality; that is
exactly LEMMA W2-ID1's strict-form content in this calculus. At m ≥ 2 on
(C-coll) the gauge is scalar (GRTW2 §3.3(b)) and the same collapse runs.
The OPEN region is δ ≠ 1 territory: interior twists OFF (C-coll).

---

## §2. The mechanism candidate: σ′-covariance of the gauge

Fix m = 2 (levels compose at m ≥ 3, measured separately). Let
θ := z₁^{A₁e₁} (A₁ = ℓ₀g₀γ₁ — the interior mismatch character of the
level-2 junction, GRTW2 §3.4's ξ₂ = θ^{−1}), and define the K₁-linear
coordinate map on K₂ = K₁[z₂]/(ψ₁):

    σ′( Σ_{i<g₁} x_i z₂^i ) := Σ_i x_i θ^i z₂^i        (z₂ ↦ θ·z₂).

**LEMMA OA-M1 (the premise makes σ′ an automorphism).** If the r = 3
junction below is byte-equal (which the shared-below premise gives), then
σ′ ∈ Aut_{K₁}(K₂). *Proof.* The m = 1 byte law (GRTW2 §3.4 rk. 3) at the
r = 3 junction says θ^{j−g₁} = 1 for every j ∈ supp(ψ₁) ∩ [0, g₁); at
j = 0 (ψ₁(0) ≠ 0) this gives θ^{g₁} = 1 and then θ^j = 1 on supp(ψ₁). So
ψ₁(θ·z) = θ^{g₁}z^{g₁} + Σ_{j∈supp} ψ_{1,j}θ^j z^j = ψ₁(z): the twist
respects the defining relation of K₂, and z₂ ↦ θz₂ extends to a
K₁-algebra endomorphism, bijective since θ is a unit. ∎

**CANDIDATE LAW (OA-SIGMA; the mechanism to be read off the table).** On
gap-free m = 2 rows (gap = a dev-tree node of a slot digit whose attained
initial abscissa exceeds its eq12 grid start — the runner's gap ledger):

    (Σ-LAW)      δ_j = ρ_j / σ′(ρ_j)      (sign variant recorded;
                                            both ρ^{1−σ′} and ρ^{σ′−1}
                                            are keyed per row).

*Derivation sketch (why this is expected).* Both evaluators are
ledger-weighted sums over the same on-line dev tree of a slot digit A: per
K₁-coordinate i the print/harness weight ratio collapses by W2-L2
(ε·z^T = z^{A·k} per node) to (i-free unit)·θ^i, so
Prnt_j(A) = u_j·σ′(R_m v(A)) with u_j independent of A — WHEN every node's
attained initial abscissa equals its grid start (no gaps). Then

    δ_j = [u_j σ′(x)]·ρ_j / [u_j σ′(y)]  = ρ_j·σ′(x/y) = ρ_j/σ′(ρ_j),

x := R_m v(C_j), y := R_m v(P_j) = ρ_j·x. Support gaps shift individual
t-exponents by the gap amounts and break the u_j-cancellation — the
honest correction term, keyed by the gap ledger. This derivation is at
SKETCH grade; the battery is the arbiter and §4 records the verdict.

**COROLLARY OA-C2 (defeat infeasibility on the Σ-LAW perimeter).** Given
(Σ-LAW) and OA-M1: (DEFEAT) ⟺ σ′(ρ_j) = 1 ∀ j ∈ supp ⟺ ρ_j = 1 ∀ j
(σ′ injective) ⟺ byte-equal. Hence **strict ⟹ byte-equal — (OPEN-2a) at
m = 2, strict form, on the Σ-LAW perimeter** — and the counter-instance
system of OA-C1 is INFEASIBLE there. The infeasibility is structural:
byte-shared lower keys make the junction's gauge discrepancy
σ′-covariant, and a coboundary ρ/σ′(ρ) can never equal ρ itself except at
ρ = 1. This is the WHY the examples-first directive asked for.

---

## §3. Stage-1 battery design (preregistration)

Genres (all deterministic; specs in `gen_battery()`; the moduli are
enumerated/validated by the general irreducibility test):

* **B5-ROSTER** — the 16 committed towers, all junctions: reproduction of
  the GRTW2 census (22 walked r ≥ 3 rows + 6 SKIP; recorded ξ ≠ 1 ⟺
  byte-RED two-sidedly on this roster).
* **B1** — the F₉ exhaustive slice: chamber ℤ₃, reads (2,1,1)+(3,1,2),
  ψ₀ = y+1, ψ₁ = y²+1 — interior character θ = −1 NONTRIVIAL and
  support-invisible (r = 3 byte-equal): the I4B invisible-twist genre
  engineered at m = 2, the exact "read-invisible deeper divergence" threat
  named in GRTW2 §5.2. Top read (e₂,h₂) ∈ {(1,1),(2,1),(3,1),(3,2),(2,3)}
  × ψ₂ over K₂ = F₉: ALL monic deg-1, ALL irreducible deg-2 on the
  wrap-active rows (12-sample elsewhere), deg-3 trinomial sample, deg-4
  binomials y⁴+c — the PE4 (F₉, g = 4, supp {0,4}) spurious geography one
  level up.
* **B1F** — flat control: same chamber with read1 = (1,1,2) (wrap-dead,
  interior character still −1): separates wrap-activity from
  θ-nontriviality.
* **B4** — (C-coll) control: read0 = (1,1,1) (A₁ = 0).
* **B2** — the F₆₄ slice: chamber ℤ₂, reads (2,1,2)+(2,1,3), ψ₀ = y²+y+1,
  ψ₁ = y³+ζ — the PE3 counter-instance chamber genre (g₁ = 3, θ of order
  3), instantiating PE4 o-e's "append any third read"; the y³+c top moduli
  are the cube-root-stabilizer spurious genre at m = 2.
* **B3B/B3A** — stacked m = 3: the I4B chamber (3,2,1)+(2,1,1)+(1,1,2) and
  the I4A chamber with read-3 swept — the EXACT geography of GRTW2's two
  instance-warranted junction-levels (I4A/I4B r = 5); **B3D** — the B1
  chamber extended by (2,1,1)/ψ₂ = y+z₂ (byte-equal, doubly twisted).

Check families and preregistered predictions (verbatim from the runner
docstring; '?' = THE QUESTION, no confident preregistration — labelled
EXPLORATORY where post-hoc):

| family | claim | prereg |
|---|---|---|
| OA-ADM | vok+onesided at every shared-below junction (W2-C1a scope) | 0 |
| OA-PHIR | rres(φ^cls) = c·ψ (Thm-`phir` reproduction) | 0 |
| OA-TOPRES | R_top = c (OA-L1) | 0 |
| OA-RHOBYTE | byte-equal ⟺ ρ ≡ 1 (OA-L4) | 0 |
| OA-BWD | byte-equal ⟹ strict (OA-C1 converse-free half) | 0 |
| OA-GAUGE | (C-coll) rows: δ ≡ 1 (GRTW2 §3.3(b)) | 0 |
| OA-XI | (C-coll) rows: the §3.4 formula pair satisfies the orbit equations (sealed CK-XI semantics; TEETH-2 surface) | 0 |
| OA-FWD-M1 | m = 1: strict ⟹ byte-equal (W2-ID1 strict form) | 0 |
| OA-FWD-M2/M3 | m ≥ 2: strict ⟹ byte-equal — **THE QUESTION** | ? |
| OA-FWD-REC | recorded ξ = 1 ⟹ byte-equal (the box's literal premise clause, sealed selection semantics) | ? |
| OA-SIGMA | gap-free m = 2 rows: (Σ-LAW), either sign | 0 |
| OA-SPURGEO | spurious recording (byte-equal ∧ recorded ξ ≠ 1) ⟺ d-torsion precedes 1 in enumeration, d = gcd of pairwise differences of supp ∪ {g} (PE4's selection geography lifted to a byte-equal-junction statement at every m) | 0 |
| OA-SPUR | census of spurious rows at m ≥ 2 | ≥ 1 predicted (B2 y³+c or B1 y⁴+c genre) |
| TEETH-1 | print leg garbled (`mut_droptwist`) on T2C+T3C: caught | 0 (= caught on both) |
| TEETH-2 | harness ε garbled (`MutHTower` refuted reading) on T2A+T2B: caught via OA-XI | 0 (= caught on both) |

**Smoke disclosure.** Before sealing, the runner was smoke-run
(`--smoke`: roster subset T2A/T2C/I4B + ~20 battery rows + both teeth;
1.7 s) to shake out indexing errors and to verify the teeth bite. The
smoke subset behaved: all prereg-0 families green, both teeth caught, the
m ≥ 2 QUESTION rows 0 violations, and ONE spurious row (the B2 chamber's
own r = 3 — the PE3 counter-instance reproduced by construction). The
(Σ-LAW) both-signs degeneracy on ord-2 characters (ρ/σ′(ρ) = σ′(ρ)/ρ when
everything is ±1) was noticed in smoke; the F₆₄ rows are the sign
separator. Nothing else was tuned post-hoc; the full battery is UNRUN at
commit 1 (two-commit seal).

---

## §4. RESULTS (commit 2; from the committed artifacts)

**PENDING at commit 1.** To be filled verbatim from
`open2attack_output.txt` / `open2attack_results.json`: the family table,
the censuses (walked/strict/byte per m-stratum; δ-nontrivial rows; gap
rows; σ-law sign census; partial-defeat rows; spurious rows), the
mechanism verdict, and the stage-2 outcome.

---

## §5. The converse boundary at m ≥ 2 (census; no verdict change)

**PENDING at commit 1.** The spurious-selection census (OA-SPUR/
OA-SPURGEO) extends PE3/PE4's m = 1 converse boundary geography to m ≥ 2;
GRTW2's converse verdict (UNPROVED at every m) is untouched either way.

---

## §6. Stage-2 outcome (the proof attempt)

**PENDING at commit 1.** The skeleton, fixed in advance: given the
battery confirms (Σ-LAW) on its perimeter, the deliverable is LEMMA
OPEN-2a-M2 (strict ⟹ byte-equal at m = 2 on the Σ-LAW perimeter) via
OA-L1–L4 + OA-M1 + OA-C2, with the honest boxes: (B1) the per-coordinate
ledger identity Prnt_j(A) = u_j·σ′(R_m v(A)) at proof grade including the
exact gap-correction form; (B2) gap rows; (B3) the m ≥ 3 composition;
(B4) the sign convention. If the battery instead finds a (DEFEAT)
solution, the deliverable is the counter-instance, displayed.

---

## §7. Proposed annex text for GRTW2 (orchestrator action; only if §4
confirms)

**PENDING at commit 1.**

— W2-OPEN-2 ATTACK unit, campaign date 2026-08-08; commit 1 (seal).
