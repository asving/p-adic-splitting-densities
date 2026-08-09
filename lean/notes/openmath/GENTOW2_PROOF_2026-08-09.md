# GENTOW-2: [GENHN-TOW-1] item (6)(α) — the iterated key's
# intermediate one-sidedness DISCHARGED BY FAITHFUL CITE
# (FGMN Theorem 6.3 + Corollary 6.4), 2026-08-09

STATUS SKELETON — sections land in per-section commits.

Charge (BOX-CLOSURE item (6), LITERATURE-FIRST): the r3 T(b)″
attempt (commit 08ec526, GENHN_PROOF S9.1 [GENHN-TOW-1] item (6))
derived the iterated data (ladder normalizers n̂₂(m) = π^a x^i Φ′^b;
iterated key Φ₃ = Φ₂^{e₃f₃} − Σ_t k̂_t Φ₂^{e₃t}) and left ONE hole,
(α): the Φ′-adic development of Φ₃ is ONE-SIDED of slope κ₂ with
residual a ψ₂-power — true at the constructed witnesses, unproved.
This note discharges (α) from the local FGMN print
(docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt,
numbering verified at ledger 63091ce; the source is arXiv
1305.0775v3, Fernández–Guàrdia–Montes–Nart, "Residual ideals of
MacLane valuations" — NOT the excluded 2212.00294).

## S1. STEP-1 VERDICT: the FGMN theorem EXISTS

**YES.** The needed statement is an instance of **FGMN Theorem 6.3 +
Corollary 6.4** (one-sidedness of N_i(F) at EVERY intermediate level
i of the MacLane chain, with the residual power law R_{i−1}(F) =
ψ_{i−1}^{ℓ_i} and the exact intermediate values µ(φ_i) = v(φ_i(θ))),
applied with F = φ = Φ₃ once Φ₃ is a key polynomial for the tower's
terminal inductive valuation ν. The key-polynomial certificate for
the T(b)″-recipe Φ₃ is **FGMN Lemma 5.3(2)** via the degree-forcing
argument displayed inside the proof of **Theorem 5.8** (itself fed by
**Corollary 4.12**, whose construction g = φ_r^{e_r f} + g₀ IS the
recipe's shape). One bridge clause is repo-side and is proved below
from the accepted corpus (S5): the recipe's level-3 residual read
R_ν(Φ₃) = ψ₃, which is GENHN-2′'s digit grammar + FGMN's additivity
(Cor 4.7(1)) + eq (14). No FGMN statement is stretched: the quotes,
the instantiation map, and the faithfulness paragraph are below.

## S2. THE TOWER ↔ MACLANE-CHAIN DICTIONARY

Repo tower (r3 box, GENHN_PROOF S9.1 item (6); GENTOW-1 S0 notation)
vs FGMN chain (display (4), layout L610–615; data table L785–803).

FGMN chain for the depth-2 tower's terminal valuation ν:

    µ₀ −(φ₁,λ₁)→ µ₁ −(φ₂,λ₂)→ µ₂ −(φ₃,λ₃)→ µ₃ = ν,   r = 3,

| repo object | FGMN object | witness value (genre (2,1,4)→(2,1,2), 3rd stage) |
|---|---|---|
| base key x, slope h/e₁ | φ₁ = x, λ₁ = h/e₁ | λ₁ = 1/2 (e₁ = 2, h = 1) |
| level-1 key Φ′ | φ₂ | Φ′ = x² − 2 |
| composed key Φ₂ | φ₃ | Φ₂ = Φ′² − 4x |
| iterated key Φ₃ | the key φ ∈ KP(ν), φ ≁_ν φ₃ | Φ₃ = Φ₂² − 16Φ′ |
| ψ₂ (residual of Φ₂'s Φ′-read) | ψ₂ = R₂(φ₃) (Cor 5.6(2)) | T + 1 |
| ψ₃ (stage-3 residual) | the prescribed ψ, R₃(Φ₃) = ψ | T − 1 |
| repo e₂, f₂ | FGMN e₂ = denom(e(µ₁)λ₂), f₂ = deg ψ₂ | 2, 1 |
| repo e₃, f₃ | FGMN e₄-level data of [ν;(Φ₃-side)] | 2, 1 |
| u₂ = dv₂(Φ′) | e(µ₂)(w₂ + λ₂), w₂ = µ₁(φ₂) | 5 |
| v(Φ′(ξ)) = u₂/(e₁e₂) | µ(φ₂) = w₂ + λ₂ (Cor 6.4) | 5/4 |
| κ₂ (repo Φ′-side slope) | e(µ₁)(w₂ + λ₂) | 5/2 |
| κ₃ (repo Φ₂-side slope) | e(µ₂)(w₃ + λ₃), w₃ = µ₂(φ₃) | 21/2 |
| dv₁, dv₂ ladders | e(µ₁)·v, e(µ₂)·v | 2v, 4v |

NORMALIZATION SHEAR (the repo polygon = FGMN polygon, one affine map).
The repo's "Φ′-adic development" plots pins (j, dv₁(a_j)) for the
Φ′-expansion Φ₃ = Σ_j a_j Φ′^j (deg a_j < deg Φ′). FGMN's N₂(Φ₃) :=
N_{µ₁,φ₂}(Φ₃) (operator definition at L871) plots (j, µ₁(a_j Φ′^j))
= (j, µ₁(a_j) + j·w₂). Since dv₁ = e(µ₁)·v and µ₁(a_j) = dv₁(a_j)/e(µ₁)
on coefficients of degree < deg Φ′ (the ladder value = the µ₁ value:
GENHN-2′'s slot separation, accepted corpus), the invertible affine
map (j, y) ↦ (j, y/e(µ₁) + j·w₂) carries the repo pin cloud onto the
FGMN pin cloud, sends lines to lines and preserves on/on-or-above.
Hence: repo development one-sided of slope κ₂ ⇔ N₂(Φ₃) one-sided of
slope −λ₂, under κ₂ = e(µ₁)(w₂ + λ₂). (FGMN's own shear-invariance
statement is Lemma 2.4, L464; witness check: κ₂ = 5/2 ↔ λ₂ = 1/4,
pins (4,0),(2,7),(0,10) ↦ (4,4),(2,11/2),(0,5).)

## S3. VERBATIM QUOTES AT THE VERIFIED NUMBERING

All quotes from docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt
(print numbering verified at ledger 63091ce); Lxxxx = layout line.

**[Q1] Lemma 1.11 (L275).** "Every φ ∈ KP(µ) is irreducible in Kv [x]."

**[Q2] Corollary 1.13 (L315).** "KP(µ) ⊂ O[x]."

**[Q3] Definition 5.2 (L1238–1239).** "For a non-zero g ∈ K[x], we say
that Nµ,φ (g) is one-sided of slope −λ if Nµ,φ (g) = Sλ (g), s(g) = 0
and s′ (g) > 0."

**[Q4] Lemma 5.3 (L1240–1244).** "A monic polynomial g ∈ K[x] belongs
to KP(µ) if and only if either: (1) deg g = mr and g ∼µ φr , or
(2) s(g) = 0, deg g = s′ (g)mr and Rr (g) is irreducible in Fr [y].
In the last case, deg g = er (deg Rr (g))mr , Nr (g) is one-sided of
slope −λr , and Rr (g) ∈ Fr [y] is monic."

**[Q5] Corollary 4.12 (L1161–1163).** "Let ψ ∈ Fr [y] be a monic
polynomial of degre f such that ψ(0) 6= 0. Then, for any α ∈ Γ(µ)
there exists g ∈ K[x] monic such that deg g = er f mr , µ(g) =
er f (wr + λr ) and Rr (g) = ψ." — and its proof's construction
(L1164–1166): "... we may assume that deg g0 < er f mr . Then,
g = φr^{er f} + g0 satisfies what we want."

**[Q6] Theorem 5.8, proof, the degree-forcing display (L1296–1302).**
"If ψ 6= y, then there exists a monic polynomial φ ∈ K[x] of degree
deg φ = er (deg ψ)mr such that Rr (φ) = ψ ... As a general fact,
deg φ ≥ s′ (φ)mr . By Corollary 4.4, s′ (φ) − s(φ) = er deg ψ; thus:
deg φ ≥ s′ (φ)mr ≥ (s′ (φ) − s(φ))mr = er (deg ψ)mr = deg φ.
Hence, s(φ) = 0 and deg φ = s′ (φ)mr . Therefore, φ satisfies
condition (2) of Lemma 5.3, and it is a key polynomial for µ."

**[Q7] Proposition 5.7 (L1276–1281).** "Let φ, φ′ ∈ KP(µ). The
following conditions are equivalent: (1) R(φ) = R(φ′ ). (2) Rr (φ) =
Rr (φ′ ). (3) φ ∼µ φ′ . (4) Hµ (φ) and Hµ (φ′ ) are associate in
Gr(µ). (5) φ |µ φ′ ." — with eq (14) (L1004): "Ri,α (φsi ) = y^{⌊s/ei⌋},
Ri (φsi ) = 1, 1 ≤ i ≤ r."

**[Q8] Corollary 4.7 (L1121–1126).** "Let 0 ≤ i ≤ r and α ∈ Γi .
(1) Ri,α (g + h) = Ri,α (g) + Ri,α (h) for all g, h ∈ Pα (µi ).
(2) If β ∈ Γi−1 , then Ri,α+β (gh) = Ri,α (g)Ri,β (h) for all
g ∈ Pα (µi ), h ∈ Pβ (µi ). (3) Ri (gh) = Ri (g)Ri (h) for all
g, h ∈ K[x]."

**[Q9] Theorem 6.3 (L1458–1464).** "Let F ∈ P be a prime polynomial
and θ ∈ K̄v a root of F . Let µ be an inductive valuation and φ a key
polynomial for µ. Then, φ |µ F if and only if v(φ(θ)) > µ(φ).
Moreover, if this condition holds, then: (1) Either F = φ, or the
Newton polygon Nµ,φ (F ) is one-sided of slope −λ, where λ =
v(φ(θ)) − µ(φ) ∈ Q>0 . (2) Let ℓ = ℓ(Nµ,φ (F )). Then, deg F =
ℓ deg φ and F is µ-minimal. (3) F ∼µ φ^ℓ , so that R(F ) is a power
of the maximal ideal R(φ)." — its proof opens (L1465): "If F = φ,
then both conditions φ |µ F and v(φ(θ)) > µ(φ) hold."

**[Q10] Corollary 6.4 (L1523–1527) — THE theorem.** "With the above
notation, suppose that φ |µ F and µ admits a MacLane chain of length
r as in (4) such that φ 6∼µ φr . Then, for any 1 ≤ i ≤ r, the Newton
polygon Ni (F ) is one-sided of slope −λi , we have µ(φi ) = v(φi (θ))
and
(23)  F ∼µi−1 φi^{ℓi} ,  deg F = ℓi deg φi ,  Ri−1 (F ) = (ψi−1 )^{ℓi} ,
where ℓi := ℓ(Ni (F )). In particular, ℓi = ei fi ℓi+1 for all
1 ≤ i < r."

Supporting notation quotes: N_i := N_{µ_{i−1},φ_i} (L871); ψ_i ∈
F_i[y] the minimal polynomial of z_i over F_i (L862) with R_i(φ_{i+1})
= ψ_i (Cor 5.6(2), L1263–1265); the numerical data e_i, f_i, m_i,
w_i := µ_{i−1}(φ_i), λ_i = h_i/(e₀···e_i) (L785–803); MacLane chain +
optimality (Def 3.1, L608–615).
## S4. THEOREM GENTOW-2 (item (6)(α)) + proof via the cite     [TODO]
## S5. The bridge clause: the T(b)″ recipe is a Cor-4.12 lift  [TODO]
## S6. Faithfulness paragraph (AXIOM_FAITHFULNESS discipline)  [TODO]
## S7. What remains of item (6): (β) rides item (1)            [TODO]
## S8. Machine battery (gentow2_checks.py): 5 committed + 2 NEW[TODO]
