# Verdict — unit MLIFT (H.116b4 research cores II-a + II-b), 2026-08-26

Deliverables: `docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md` (the proofs),
`verification/openmath/h116b4_lift_cert.py` + `runs/wave-b/out_MLIFT_cert.log`
(ALL CHECKS PASSED, exit 0). No statement touched; fence A-H.7/F1 respected (all
counting is inside raw presentation towers; no fibre-to-fibre map anywhere).

## II-a (row GR-9, one-grade nonlinear lifting) — **PROVED**

Over every DVR (completeness and residue finiteness not consumed by the identities;
finiteness only to count), doc §§1–3:

* The planted factor is EXACTLY affine: P(b) = (X−ŵπ^k)^μ + Σ b_j π^{k(μ−j)}(X−ŵπ^k)^j,
  pinned two-legged (landed `alphaParent`/`alphaFrame` text + executable model; cert C1).
* **Lemma FE**: Φ(x+π^i δ) ≡ Φ(x) + π^i T_x(δ) (mod π^{2i+1}) — the filtration estimate,
  with one spare grade from child column contents (every ≥2-fold term has a child block).
* **Lemma DS**: T_x mod π^{j+1} depends only on x mod π^j; the grade map is one fixed T̄.
* **Lemma GRADE** (new, stronger than the outline asked): T̄ is the explicit cofactor
  embedding — child digits ↦ 0, cofactor digit c ↦ X^{s+c}; image = W (dim r), kernel =
  child digits, so K = q^{Σμ_p} at EVERY level and node. Derives all battery |image|/K
  numbers (2/1/1 and 4/81/16) in closed form; cert C2 confirms as maps, not just sizes.
* **Theorem 3.2** (= outline `card_factorisation_lifts_succ`): exact 0/K dichotomy —
  live iff the obstruction class ω_n(x) ∈ 𝔽^m/W vanishes; live nodes have exactly
  K = q^{Σμ_p} lifts, an affine ker(T̄)-translate. NO set identification with the linear
  kernel is made or needed (CELL-2 separator respected). GR-9 clauses 1–3 discharged;
  clause 4 (cofactor automorphism) shown NOT NEEDED on the raw pair space.
* Formalization-trivial node chain MLIFT-a1..a5 supplied (doc §3.5), ~280 Lean lines.

## II-b (rows GR-10/11, pushforward induction) — **PARTIAL** (sharply decomposed)

PROVED (doc §§4–5, 8): the invariant U(n|F) ("ω_n uniform on its image") is EQUIVALENT
to the battery's aggregate law and yields the count recursion
#S_N(F) = q^{s(N−1)}/∏ I_n(F) (reproduces 32/59049/8192 exactly); the tower reduction —
across each K-fibre, ω_n shifts by the FIXED rank-≤1 map −σ(u)X^{m−1} mod W (cert C4/C5
pin sign and grade) — reduces U(n) to uniformity of a coarsened map on the previous live
set; **U(n) is proved unconditionally for n ≤ 3** (and for all n in the affine ranges,
e.g. all n ≤ 1+min(k_p+k_p') when r = 0). Assembly theorem: MLIFT-1 + MLIFT-2 + MSMITH
interface ⟹ the signed count with G = q^{s(N−1)}/∏ q^{dim V_n}, positive,
genre-determined.

OPEN (named, doc §6): **MLIFT-1** — U(n|F) for n ≥ 4 (evidence now says likely for ALL
targets: cert C6 finds sibling uniformity holds even at a non-genre tower);
**MLIFT-2** — the schedule I_n = #V_n(T_x), the saturated grade-n image of the restricted
Sylvester lattice mod W. NEW quantitative law, now certified honestly (cert C3): the
observed I_n equals #V_n computed from the fibre-base Smith data at EVERY level of all
three cells — including CELL-4's pauses (exponents [2,3,5,7] ⟹ 1,2,4,4,8,8). MSMITH's
restricted-Smith rigidity is stated exactly as interface 6.5 and consumed, not proved.

REFUTED (doc §7, recorded as a fence): any target-blind global straightening /
Hensel-count mechanism (Φ = F₀ + T₀∘Θ) — it would force one multiplicity across all
genres, contradicting the battery's own CELL-1 histogram (96 classes, 4096 raw
presentations, 96 ∤ 4096). II-b's uniformity is irreducibly per-level/per-sibling; the
genre enters only through the schedule.

## Status per brief claim

| claim | verdict |
|---|---|
| II-a affine law + level-fixed T_n + 0/K liveness, arbitrary complete DVR | **PROVED** |
| II-a filtration estimates + base stability | **PROVED** (FE, DS — stronger form) |
| count-not-set caution honored | yes (no set identification anywhere) |
| II-b invariant propagates level-to-level | **PARTIAL**: proved n ≤ 3 + reductions; OPEN MLIFT-1/2 with the schedule law newly certified |
| MSMITH interface cited precisely, not proved | yes (doc 6.5) |
| downstream assembly mechanical | **PROVED as implication** (doc 8.1) |
