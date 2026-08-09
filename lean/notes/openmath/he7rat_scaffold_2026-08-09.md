# HE7-CODEX-RATIFICATION — orchestrator pre-verdict scaffold

Written DURING the Codex run (session 019fe4c6-4ae2-7053-95f9-d5c5cc0d58d1, log
`/tmp/codex_he7rat_stdin_1786249627.log`), BEFORE reading any Codex output.
Committed as-is. Predictions per attack point, from my own full read of
`HE7_PROOF_2026-08-08.md` (all 1,969 lines incl. ANNEX F-1) plus the pasted
suppliers.

## P-1 (attack 1: HE7-12(c) items 1/7/9/10 — the never-audited four)

All four survive; expected worst grade MINOR.

* **Item (1)** — checked: (SLOT₂)/(LIFT₂) statements quantify over C ∈ O[x],
  deg C < D″, Φ′-slots, level-2 points; the level-2 point set (DEF HE7-1) is
  defined by level-1 data (dv(Φ′(ξ)) = λ, ι_ξ(r)(β_ξ) = 0) — genuinely
  key-free. CLEAN.
* **Item (7)** — HE7-6's proof consumes HE6-2″/HE6-5/HE6-0′ only (level 1,
  key-free): CLEAN. The HE6R1-2 half is the weakest of the four as WORDED:
  its proof (PASTE C) also consumes LEMMA HE6-4 + HE6-2′ at level 1 AND
  LEMMA HE7-9(a) + THEOREM HE7.A(1) at level 2 (in clause (b)), not "only
  the HE7-7/7′ analogues, items (5)–(6)". Both extras are in the package
  (items 8/10 + level-1 key-free), so content survives; candidate MINOR
  (citation completeness).
* **Item (9)** — Ψ − w ∈ O[x] with Galois-fixed coefficients (both Ψ, w ∈
  O[x]); n₂ g-fixed. HE7-11's proof consumes nothing else. CLEAN.
* **Item (10)** — the §S5.7 sandwich at Ψ^(w) composes items (4),(8),(9)
  plus (6) (HE7-7″, audited at PE2) and item (2)'s test family. CLEAN;
  possible nit that the item's list omits (2)/(6).

## P-2 (attack 2: ANNEX-LEMMA HE7-13′(a) at inseparable R_λ)

Survives. My own re-derivation: HE7-7″'s label partition is
separability-free (minimal-polynomial reading; the separability sentence in
7″ is a remark about A(2), not a hypothesis); HE7-10's strict-excess
argument nowhere uses multiplicity 1; the r′ = r step is the
two-minimal-polynomials argument and is complete; k = L_C/(ℓ₂ deg r) ∈ ℤ
from ℓ₂ | L_C (integer endpoints) and R^(C) = c·r^k. Candidate MINORs:
(i) HE7.A(1)/HE7-9 applied to f_C needs Ψ̃ ∤ f_C — one line (Ψ̃ ∤ f_S and
f_C | f_S), not displayed; (ii) f_C inherits "every root a level-2 point +
disc ≠ 0" — displayed. Clause (c)'s translation automorphism and (e)'s
residue algebra: CLEAN.

## P-3 (attack 3: δ₂ = κ₂ boundary, HE7-7 Step 2)

Survives. δ₂ > κ₂ ⟹ term values ℓ₂[(d₂−t)κ₂ + tδ₂] strictly increasing in
t ⟹ unique finite min at t = 0, NEEDS C₀ ≠ 0 — supplied by r₂(0) ≠ 0
(DEF HE7-3 hypothesis) but not cited at the step: candidate MINOR (display).
δ₂ < κ₂ ⟹ strictly decreasing ⟹ unique min at monic t = d₂ (always
present). δ₂ = ∞ (ξ a root of Ψ) lands in the δ₂ > κ₂ branch, t = 0 term
finite ⟹ no root of Ψ₂ is a root of Ψ — consistent. Vanishing middle C_t
harmless (contribute ∞; monotonicity is endpoint-anchored). Twist algebra
re-derived: c_t ∈ ℤ because s(k) ≡ ku^{−1} mod ℓ makes the numerator ≡ 0
mod ℓ; res(τ_t) = β_ξ^{c_t} via two applications of the §S1 cocycle
(n₂(u₂)^t fold + the product fold), and the inverse-twist prescription
cancels to ι(β^{c_{d₂}})·r₂(β₂,ξ) exactly as displayed; t = d₂ endpoint
self-consistent (c_{2,d₂} = 1, exponent 0). CLEAN.

## P-4 (attack 4: §S7 verbatim-reuse ℓ ≥ 2 → ℓd_r ≥ 2)

Survives. Both displays re-derived: μ ≥ L_λ = ℓ·deg R_λ ≥ ℓmd_r ≥ 4 (uses
Σ_λL_λ = μ, standing Φ′ ∤ f convention); μ₂ ≤ n_λ/(D′ℓd_r) = deg R_λ/d_r ≤
μ/(ℓd_r) ≤ μ/2 (uses |S| ≤ n_λ and HE6-3(b)'s n_λ = D′L_λ — statement given,
not pasted in the brief: adjudicate any "HE6-3 unavailable" finding as a
brief artifact, not a note defect). Iteration 4 ≤ μ_J ≤ μ/2^{J−1} ⟹
J ≤ log₂μ − 1: no off-by-one (jump AT level J needs μ_J ≥ 4). Interleaved
non-jump steps only decrease μ, so halving composes — implicit; candidate
MINOR. n = 8 forcing (D′ = 2, μ = 4, μ₂ ≤ 2) and n = 16 (μ ≥ 8) exact.
Hidden-ℓ≥2 hunt: peel decreases μ (1 per level, §S6(i)); block split
decreases degree; found none.

## P-5 (free hunt candidates — mine)

* (S6.3)'s cascade: the ε_j = 0 case needs δ_{j+1} ≤ T_{j+1} (level-j disk
  criterion at a non-level-(j+1) point) and ρ_j ≥ 0 inductively — I
  re-derived both index-exactly; the display compresses this; MINOR at most.
* DEFINITION HE7-2's "w_i = c_i·v … (integer-valued on the relevant
  elements)" is vague as a definition clause — display nit.
* LEMMA HE7-8's "after recentering all these values strictly increase" —
  decorative clause; the limit argument doesn't need it.
* W₂'s display (§S4.2): fine as stated (sufficient-not-necessary is
  explicit).
* Brief artifact to watch: HE6-3/HE6-4/HE6-5/HE6.A statements were NOT
  pasted (PASTE B stops at HE6-2′); Codex findings of the form "cited
  lemma not supplied" are N/A-brief, not note defects.

## Expected outcome

RATIFIED or RATIFIED-WITH-ANNEX: a handful of MINORs (citation
completeness at HE7-12(c)(7), C₀ ≠ 0 display at the δ₂-boundary, Ψ̃ ∤ f_C
line in the annex, S7 interleaving sentence), no GAP-or-worse expected on
the four named attack surfaces. Confidence moderated by the HE6PE1
precedent (Codex exceeded the same-side key twice there).
