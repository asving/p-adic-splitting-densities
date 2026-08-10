# GENTOW-2: [GENHN-TOW-1] item (6)(α) — the iterated key's
# intermediate one-sidedness DISCHARGED BY FAITHFUL CITE
# (FGMN Theorem 6.3 + Corollary 6.4), 2026-08-09

**STATUS: COMPOSED, item (6)(α) PROVED-VIA-CITE (THEOREM GENTOW2-A +
LEMMA GENTOW2-B), battery GREEN (41 checks/0 violations, teeth T1 +
T2′ fired; T2 = disclosed failed design). Grade 0/2 (attempt; hostile
arc later). Unit: GENTOW-2, BOX-CLOSURE campaign.
[r1 2026-08-09, post-PE1 repair round: F1 PDF-provenance leg CLOSED
(S6.1 table; arXiv fetch bit-identical), F2 B-2 partially derived +
honestly re-attributed (LEMMA GENTOW2-B′, S5.1), F3 fallback clause
corrected to the true transformation law, F4/F5/F6 minors cured;
record in S9. Sealed machine artifacts untouched. Grade stays 0/2;
PE2 next.]**

Charge (BOX-CLOSURE item (6), LITERATURE-FIRST): the r3 T(b)″
attempt (commit 08ec526, GENHN_PROOF S9.1 [GENHN-TOW-1] item (6))
derived the iterated data (ladder normalizers n̂₂(m) = π^a x^i Φ′^b;
iterated key Φ₃ = Φ₂^{e₃f₃} − Σ_t k̂_t Φ₂^{e₃t}) and left ONE hole,
(α): the Φ′-adic development of Φ₃ is ONE-SIDED of slope κ₂ with
residual a ψ₂-power — true at the constructed witnesses, unproved.
This note discharges (α) from the local FGMN print
(docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt; [r1]
provenance: the 12 consumed statements + eq (14) verified against
the arXiv v3 PDF itself by visual page read — 13-row table in S6.1,
local PDF bit-identical to arXiv's serving copy, fetch disclosed
there; the source is arXiv 1305.0775v3, Fernández–Guàrdia–Montes–
Nart, "Residual ideals of MacLane valuations" — NOT the excluded
2212.00294).

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
| ψ₂ (residual of Φ₂'s Φ′-read, = minpoly(η₂)) | FGMN ψ₂ = R₂(φ₃) = minpoly(z₂) (Cor 5.6(2)); canonically z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋} (S5.1 LETTER FORMULA) [r2, PE2 F1: equal to the repo ψ₂ up to the z₁-twist; on the nose when z₁^{⌊ℓ₁u₂/e₁⌋} = 1, e.g. f₁ = 1 over q = 2] | T + 1 (f₁ = 1, q = 2 ⟹ z₁ = 1: twist trivial) |
| ψ₃ (stage-3 residual) | the prescribed ψ, R₃(Φ₃) = ψ | T − 1 |
| repo e₂, f₂ | FGMN e₂ = denom(e(µ₁)λ₂), f₂ = deg ψ₂ | 2, 1 |
| repo e₃, f₃ | FGMN (e₃, f₃): e₃ = e(µ₃)/e(µ₂) = denom. data of the λ₃-augmentation, f₃ = deg ψ₃ = [F₄:F₃]; the pair with m₄ = e₃f₃m₃ per eq (9) (PDF pp.15–16) — deg Φ₃ = m₄. [r1, PE1 F6: the pre-repair label "e₄-level data" named the F₄ residue-field LEVEL and was undefined; witness re-derivation: ν(Φ₂) = 21/8, denom 8 = e(µ₃) over e(µ₂) = 4 gives e₃ = 2] | 2, 1 |
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

All quotes from docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt;
Lxxxx = layout line. [r1] Numbering AND statement content of each
quote below re-verified directly against the arXiv v3 PDF (visual
page read, decorrelated from the pdftotext extraction the layout
pins live in) — per-statement table in S6.1. The pre-repair pointer
"numbering verified at ledger 63091ce" over-claimed: that ledger
entry was local-extraction-only and covered GRTJC's cite set (only
Cor 4.7 + eq (14) overlap this note's) — PE1 finding F1, cured here.

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
## S4. THEOREM GENTOW2-A (item (6)(α) DISCHARGED)

Setting: a depth-2 tower per T(b)′ (S8 annex, accepted), FGMN chain
as in S2's dictionary: µ₀ →(x, λ₁) µ₁ →(Φ′, λ₂) µ₂ →(Φ₂, λ₃) µ₃ = ν,
an optimal MacLane chain (deg x < deg Φ′ < deg Φ₂ — the tower's
stages are proper, e₂f₂ ≥ 2 in repo names). Base field K = ℚ (or a
number field), v = the p-adic valuation, K_v complete discrete —
FGMN's standing setting (their §6 header, L1433, PDF p.27 [r1: pin
corrected from L1434, PE1 F5]).

**THEOREM GENTOW2-A.** Let ψ₃ ∈ F₃[y] = K₂[y] be monic irreducible
of degree f₃ ≥ 1 with ψ₃(0) ≠ 0, and let e₃ ≥ 1 be given with
e₃f₃ ≥ 2 (proper third stage). Let Φ₃ ∈ K[x] be ANY monic polynomial
with

  (i) deg Φ₃ = e₃f₃ · deg Φ₂, and
  (ii) R_ν(Φ₃) = ψ₃  (the level-3 FGMN residual; e_r := e₃ at ν's
       augmentation data),

— in particular the T(b)″-recipe polynomial Φ₃ = Φ₂^{e₃f₃} −
Σ_{t<f₃} k̂_t Φ₂^{e₃t}, which satisfies (i) by construction and (ii)
by LEMMA GENTOW2-B (S5). Then:

  (a) Φ₃ ∈ KP(ν), and Φ₃ is a PRIME POLYNOMIAL: monic, coefficients
      in O_v, irreducible in K_v[x];
  (b) [the (α) polygon clause] the Φ′-adic development of Φ₃ is
      ONE-SIDED of repo-slope κ₂ = e(µ₁)(w₂ + λ₂): FGMN N₂(Φ₃) =
      N_{µ₁,Φ′}(Φ₃) is one-sided of slope −λ₂, of length ℓ₂ =
      e₂f₂e₃f₃, and the S2 shear transports one-sidedness to the
      repo pin plot;
  (c) [the (α) residual clause] R₂(Φ₃) = ψ₂^{ℓ₃} with ℓ₃ = e₃f₃ —
      the residual of the Φ′-side is the ψ₂-POWER the r3 box asked
      for;
  (d) [the forced intermediate data] for every root ξ of Φ₃ in K̄_v:
      v(Φ′(ξ)) = ν(Φ′) = w₂ + λ₂ = u₂/(e₁e₂) EXACTLY, and likewise
      v(x(ξ)) = λ₁ = h/e₁ and v(Φ₂(ξ)) = ν(Φ₂) = w₃ + λ₃ = κ₃/(e₁e₂);
  (e) [bonus, the recipe's own polygon] N₃(Φ₃) = N_{µ₂,Φ₂}(Φ₃) is
      one-sided of slope −λ₃, length e₃f₃, residual R₃(Φ₃) = ψ₃.

**Proof.**

*(a) Key certificate.* Φ₃ is monic with deg Φ₃ = e₃(deg ψ₃)m₃
(m₃ := deg Φ₂) and R₃(Φ₃) = ψ₃ irreducible, ψ₃ ≠ y (ψ₃(0) ≠ 0). The
degree-forcing display quoted at [Q6] applies verbatim to Φ₃ in the
role of its φ: deg Φ₃ ≥ s′(Φ₃)m₃ ≥ (s′(Φ₃) − s(Φ₃))m₃ =
e₃(deg ψ₃)m₃ = deg Φ₃ (the middle equality is Cor 4.4(4), L1089),
forcing s(Φ₃) = 0 and deg Φ₃ = s′(Φ₃)m₃ — condition (2) of Lemma 5.3
[Q4], so Φ₃ ∈ KP(ν). Then Φ₃ is irreducible in K_v[x] by Lemma 1.11
[Q1] and has O-coefficients by Cor 1.13 [Q2]; monic by hypothesis;
hence Φ₃ ∈ P, a prime polynomial in FGMN's Definition 6.1 sense.

*Non-equivalence to the top key.* R₃(Φ₂) = R₃(φ₃¹) = 1 by eq (14)
[Q7], while R₃(Φ₃) = ψ₃ with deg ψ₃ = f₃ ≥ 1; if e₃ = 1 and f₃ = 1
were both allowed the degrees would still differ (ψ₃ ≠ 1), but under
the properness proviso e₃f₃ ≥ 2 we simply have deg Φ₃ > deg Φ₂, and
in all cases R₃(Φ₃) ≠ R₃(Φ₂), so Φ₃ ≁_ν Φ₂ by Prop 5.7 (2)⇔(3) [Q7].
[r1, PE1 F4] Prop 5.7 requires BOTH arguments in KP(ν): Φ₃ ∈ KP(ν)
by (a) above, and Φ₂ = φ₃ ∈ KP(ν) by Lemma 5.3(1) [Q4] — deg φ₃ =
m₃ and φ₃ ∼_ν φ₃ (reflexivity of ∼_ν).

*(b)+(c)+(d) The cite fires.* Apply Theorem 6.3 [Q9] with F = φ =
Φ₃, µ = ν: F = φ, so φ |_ν F holds (the proof's opening line, quoted
at [Q9]). Now Corollary 6.4 [Q10] applies: φ |_ν F, ν has the length-3
MacLane chain of S2, and φ = Φ₃ ≁_ν φ₃ = Φ₂ (previous paragraph).
Its conclusions, instantiated:

  • i = 2 clause: N₂(Φ₃) one-sided of slope −λ₂ — clause (b), with
    the S2 shear giving the repo statement at slope κ₂. Length:
    ℓ₂ = e₂f₂ℓ₃ (the "in particular" of [Q10]) and ℓ₃ = deg Φ₃/deg Φ₂
    = e₃f₃ (from (23) at i = 3), so ℓ₂ = e₂f₂e₃f₃.
  • (23) at i = 3, residual part: R₂(Φ₃) = ψ₂^{ℓ₃} = ψ₂^{e₃f₃},
    where FGMN's ψ₂ = R₂(φ₃) = minpoly(z₂) (Cor 5.6(2)) is the
    z₁^{⌊ℓ₁u₂/e₁⌋}-twist of the repo ψ₂ = minpoly(η₂) — S5.1's
    LETTER FORMULA z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋} [r2, PE2 F1: the
    pre-repair "is the repo ψ₂" is on the nose exactly when the
    twist fixes ψ₂, e.g. z₁ = 1 at f₁ = 1 over q = 2 — true at
    the S2 witness and at the 13 standing machine witnesses] —
    clause (c) in the twist-aware form; the consumption note
    below carries it through T(b)′. (Consistency: FGMN Cor 4.4(4)
    gives deg R₂(Φ₃) = (s′−s)/e₂ = ℓ₂/e₂ = f₂e₃f₃ =
    deg(ψ₂^{e₃f₃}) — the twist preserves the degree f₂. ✓)
  • the middle clause "µ(φᵢ) = v(φᵢ(θ))" at i = 1, 2, 3: v(x(ξ)) =
    ν(x) = λ₁, v(Φ′(ξ)) = ν(Φ′) = w₂ + λ₂ = u₂/e(µ₂) = u₂/(e₁e₂),
    v(Φ₂(ξ)) = ν(Φ₂) = w₃ + λ₃ — clause (d). (These hold for each
    root θ = ξ of F = Φ₃ separately: Theorem 6.3/Cor 6.4 are stated
    for a fixed root θ, and every root of the irreducible F is such
    a θ.)
  • i = 3 clause: N₃(Φ₃) one-sided of slope −λ₃, ℓ₃ = e₃f₃; its
    residual R₃(Φ₃) = ψ₃ is hypothesis (ii) — clause (e). ∎

*Consumption note.* Clause (d) + (c) are exactly the two inputs the
r3 T(b)″ ascent needed at a Φ₃-root ξ ("v(Φ′(ξ)) = u₂/(e₁e₂) exact
with η₂(ξ) a ψ₂-root, the input (ii)'s slot lemma needs at ξ" —
GENHN_PROOF S9.1 item (6)(α), L1419–1423): the residual power
ψ₂^{e₃f₃} has no root besides ψ₂'s, so the level-2 residual class
η₂(ξ) read through T(b)′(ii)'s slot lemma is a ψ₂-root. [r2, PE2
F1 — letter-twist robustness of this consumption: FGMN's clause is
in the z₂-letter, the repo consumption in the η₂-letter, and the
two differ by S5.1's LETTER FORMULA (z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}).
Both ride the ONE field embedding σ: F₃ → k(L₃) that the level-3
leaf read fixes: η₂ = z₂·z₁^{⌊ℓ₁u₂/e₁⌋} in F₃ is by definition a
root of the repo ψ₂ = minpoly(η₂), and η₂(ξ) = σ(η₂), so "η₂(ξ)
is a repo-ψ₂-root" holds with ψ₂'s coefficients read through the
same σ — no clause of GENTOW2-A consumes an equality of the two
letters.] The PE3-F1
correction's mechanism attribution ("the carry terms CLEAR the side")
is now a THEOREM, not bookkeeping: Cor 6.4 forces every pin strictly
above the side except the on-side residue pattern of ψ₂^{e₃f₃}.

## S5. LEMMA GENTOW2-B (the bridge clause): the T(b)″ recipe
## satisfies R_ν(Φ₃) = ψ₃

**LEMMA GENTOW2-B [r3 RESTATED — PE4 F1: the pre-repair conclusion
"R_ν(Φ₃) = ψ₃" for the PER-HEIGHT digit string is machine-refuted
at letter-live frames (LD2, honesty box); the lemma now carries the
MEASURED transformation law and the prescription that realizes any
admissible target].** Let the recipe data be as in the r3 box:
k̂_t ∈ K[x] with deg k̂_t < deg Φ₂, dv₂-height u₃(f₃ − t), and
K₂-digit residual class c_t ∈ K₂ = F₃ (a GENHN-2′ ladder lift;
k̂_t = 0 when c_t = 0, c₀ ≠ 0), where u₃ = e₃·κ₃, gcd-normalized so
the pins (e₃t, u₃(f₃−t)) lie on the line through (e₃f₃, 0) of
dv₂-slope κ₃, with κ₃ > e₂f₂u₂ (equivalently λ₃ := κ₃/(e₁e₂) −
ν_{µ₂}(Φ₂)... > 0; the positivity is the [r1]-style node-floor
arithmetic, here an explicit HYPOTHESIS). Then Φ₃ := Φ₂^{e₃f₃} −
Σ_{t<f₃} k̂_t Φ₂^{e₃t} satisfies

  (B-law)  R_ν(Φ₃) = y^{f₃} − Σ_{t<f₃} u(β_t)·c_t·y^t,
           u(β_t) = ϑ(t)·w^{f₃−t},

where u(β_t) := R_{3,β_t}(n̂₂(u₃(f₃−t))) is B′'s per-grade unit
(S5.1), ϑ(t) := res((n̂₂(u₃(f₃−t))/n̂₂(u₃)^{f₃−t})(x₀)) is the
repo-derivable n̂₂-cocycle (grade-determined, x₀-free, a z₁^j z₂^k
letter monomial — LEMMA GENTOW2-B″, S5.2; ϑ(f₃−1) = 1), and
w := R_{3,κ̄}(n̂₂(u₃)) ∈ K₂^× is a single slot-independent unit
(κ̄ := u₃/e(µ₂), the top slot's grade). Consequently, given a
TARGET ψ₃ = y^{f₃} − Σ_{t<f₃} a_t y^t ∈ K₂[y] monic irreducible
with ψ₃(0) ≠ 0, the MULTIPLICATIVE-CONVENTION prescription
c_t := ϑ(t)^{−1}·a_t realizes

  R_ν(Φ₃) = w^{f₃}·ψ₃(y/w) =: ψ₃^{(w)},

monic irreducible of degree f₃ with ψ₃^{(w)}(0) = w^{f₃}ψ₃(0) ≠ 0
(the substitution y ↦ wy preserves monicity after the
renormalization displayed, irreducibility, degree, and the nonzero
constant) — an ADMISSIBLE residual, so the recipe realizes
THEOREM GENTOW2-A's hypothesis (ii) with residual ψ₃^{(w)} for any
admissible target ψ₃. The unadjusted PER-HEIGHT prescription
(c_t = a_t) realizes ψ₃ itself iff u(β_t) = 1 at each used slot —
holding at each letter-dead slot the standing record tested, and
failing at PE4's letter-live LD2 (honesty box below).

**Proof.** Write α := e₃f₃(w₃... (FGMN: α = e_r f(w_r + λ_r) with
e_r = e₃, f = f₃, w_r = w₃ = µ₂(Φ₂), λ_r = λ₃). Each term lies in
P_α(ν): ν(Φ₂^{e₃f₃}) = e₃f₃(w₃ + λ₃) = α, and ν(k̂_t Φ₂^{e₃t}) =
ν(k̂_t) + e₃t(w₃ + λ₃) = α exactly because dv₂(k̂_t) = u₃(f₃ − t) is
the on-line height (dv₂ = e(µ₂)v and ν(k̂_t) = µ₂(k̂_t) =
dv₂(k̂_t)/e(µ₂) for deg k̂_t < deg Φ₂ — GENHN-2′'s ladder = the
µ₂-value, accepted corpus; the k̂_t are Φ₂-free so their ν- and
µ₂-values agree, FGMN Prop 1.9/L258). By Cor 4.7(1) [Q8] (additivity
on P_α(µ₃)):

  R_{3,α}(Φ₃) = R_{3,α}(Φ₂^{e₃f₃}) − Σ_{t<f₃} R_{3,α}(k̂_t Φ₂^{e₃t}).

Eq (14) [Q7] gives R_{3,α}(Φ₂^{e₃f₃}) = y^{f₃}. For the correction
terms, Cor 4.7(2) [Q8] (multiplicativity) with g = k̂_t ∈ P_β(µ₃)
(β = ν(k̂_t) ∈ Γ₂) and h = Φ₂^{e₃t}: R_{3,α}(k̂_t Φ₂^{e₃t}) =
R_{3,β}(k̂_t) · y^t (eq (14) again for the power; the abscissa
bookkeeping s_j = s(α) + je₃ with s(α) = 0 places the t-th
contribution at y^t). Here R_{3,β}(k̂_t) ∈ F₃ is the degree-0
residual of a polynomial of degree < deg Φ₂ = m₃ whose N₃-polygon is
the single point (0, β): by Definition 3.16 (L916–923) its value is
the K₂-digit class of k̂_t up to the unit constant ε₂(β) ∈ F₃*.
[r3 — the pre-repair step identified that value with c_t ON THE
NOSE (= B-2), machine-refuted at LD2; corrected step:] By LEMMA
GENTOW2-B′(3)+(4) (S5.1, derived from the accepted corpus), with
β = β_t the slot's grade: R_{3,β_t}(k̂_t) = u(β_t)·digit(k̂_t) =
u(β_t)·c_t, the recipe's k̂_t having repo digit c_t by construction.
Summing: R_{3,α}(Φ₃) = y^{f₃} − Σ u(β_t)c_t y^t — the (B-law) —
and LEMMA GENTOW2-B″ (S5.2) factors u(β_t) = ϑ(t)·w^{f₃−t}. With
the multiplicative prescription c_t = ϑ(t)^{−1}a_t the sum is
y^{f₃} − Σ a_t w^{f₃−t} y^t = w^{f₃}ψ₃(y/w) = ψ₃^{(w)}. Since the
constant term u(β₀)c₀ ≠ 0 (u a unit, c₀ ≠ 0) we get R₃(Φ₃) =
R_{3,α}(Φ₃) (Def 3.18, L994–1000, j₀ = 0). ∎

*Honesty box for GENTOW2-B [r1 REWRITTEN — PE1 F2 (provenance) +
F3 (false fallback clause) cured].* Two repo-side identifications
carry this proof:

(B-1) the dv₂ ladder value of a deg < D₂ ladder element equals its
µ₂-value, exactly, with digit-0 meaning strictly-above (GENHN-2′'s
two-step class separation + no-cancellation — LEMMA GENHN-T(b)′
(ii), S8 annex, accepted corpus).

(B-2) [r3 REFUTED AT LETTER-LIVE GRADES, REPLACED BY THE MEASURED
COCYCLE FORM — PE4 F1, machine]. The identification this box
asserted through PE3 — "the repo K₂-digit of a Φ₂-free ladder
element equals the ε₂-normalized F₃-coordinate of FGMN's Def 3.16
at its grade, ON THE NOSE" — is FALSE at letter-live grades: at the
first letters × depth contact (LP1 tower, stage-3 recipe e₃ = 1,
f₃ = 2, κ₃ = 19; z₁ ∈ F₄∖F₂), frame LD2's per-height digit string
(z₁, z₁²), prescribing the SPLIT ψ₃ = y²+z₁y+z₁² = (y+1)(y+z₁²),
realized a SINGLE (4,4) prime with realized residual y²+z₁y+1
(sealed fresh route RED 62/9, each of the 9 misses a
B-2-on-the-nose prediction — runner gentow2_pe4_fresh.py, seal
23def87, output kept as-is; decode probe gentow2_pe4_decode.py
GREEN 14/0 first-run-under-its-seal; PE4 report §E/[F1]). What
replaces the assertion — DERIVED in S5.1 + S5.2 from the accepted
corpus, not asserted: B′(3)'s per-grade unit at the recipe's used
slots factors as

    u(β_t) = ϑ(t) · w^{f₃−t}          (LEMMA GENTOW2-B″, S5.2)

where ϑ(t) := res((n̂₂(u₃(f₃−t))/n̂₂(u₃)^{f₃−t})(x₀)) is the
repo-internal n̂₂-COCYCLE — grade-determined, x₀-free, and
LETTER-VALUED: a z₁^j z₂^k monomial by S5.2's γ-calculus; at the
PE4 frames ϑ(0) = z₂^{−1}z₁^{−5} = z₁ (LP1 has z₂ = 1), matching
the machine pin res(n̂₂(19)²/n̂₂(38)) = z₁² = ϑ(0)^{−1} (decode COC
checks, both frames) — and w := R_{3,κ̄}(n̂₂(u₃)) ∈ K₂^× is a
SINGLE slot-independent unit, the honest cross-frame residue
(consumer-invisible: it acts by the grade-covariant substitution
y ↦ wy, which preserves irreducibility and factor degrees; not
computed anywhere in the corpus — see S5.1's re-scoped residue
paragraph). Verdict-level machine data (prime-split patterns) is
w-blind and constrains ϑ only: the standing 13-witness record's
green B-routes support ϑ = 1 at each of its own tested slots, and
LD1/LD2 measure ϑ(0) = z₁ ≠ 1 letter-live. The recipe-grammar
consequence is LEMMA GENTOW2-B as RESTATED above (the
multiplicative-convention prescription); the per-height on-the-nose
reading survives only where the slot's letter monomial is trivial.
[r1] Provenance history (stands as dated): the on-the-nose
identification was FIRST MADE IN THIS NOTE. The pre-repair pointer ("the [W-2] graded-dictionary
identification at level 2, the same one T(b)′'s proof already
uses") was wrong on both legs — GRTW2's dictionary targets a
different source text and GENHN/T(b)′ has no Def-3.16 contact (PE1
F2). What the accepted corpus DOES derive is now separated out as
LEMMA GENTOW2-B′ (S5.1): B-2 holds UP TO an x₀-free, g-free unit
family u(β) ∈ K₂^× (u(β) = the FGMN coordinate of the repo ladder
normalizer at grade β). [r3] The residue "u(β) = 1 at each grade
the recipe uses", consumed DISCLOSED-NOT-DERIVED through PE3, is
now REFUTED (LD2, above) and is CONSUMED NOWHERE: the restated
lemma consumes only B′(3)–(5) + B″, all derived. Machine-support
history (accurate as dated, per PE4 §S): the sealed battery (41/0)
+ the PE1 fresh route (20/0) sit at 10 witnesses whose B-route
factorizations were predicted with u ≡ 1, including the
F₄ × f₃ = 2 corner pair F2/F3 where flipping one digit flips
irreducible ↔ split — twist families u that would alter those
verdicts at the tested grades are excluded by that record; [r3]
read via B″, that record supports ϑ = 1 at those tested slots and
was structurally w-blind and z₁-blind (letter-dead).
[r2] Scope disclosure (PE2 F1's letter-blindness point — PROVED
PRESCIENT by PE4 [F1], which found the box's scope warning
load-bearing, not boilerplate): the 13 witnesses standing at PE2
(those 10 + the 3 PE2-fresh f₃ = 3 ones) each sit at f₁ = 1 over
q = 2, where z₁ = 1 — the record supports u ≡ 1 on letter-dead
geography only. The first letter-live machine contact is the r2
probe (gentow2_r2_letter_probe.py, S10), which tests S5.1's LETTER
FORMULA itself at f₁ = 2 (z₁ ∈ F₄∖F₂), not B-2; the first
letter-live B-2 contact is PE4's LD1/LD2 — the tooth that bit.

(B-2-fallback, the TRUE transformation law) [r3: THE FALLBACK
FIRED — PE4's LD2 realized exactly this clause's u ≢ 1
grade-varying (ϑ-cocycle) mode, and the clause's survival analysis
(re-parameterization c_t ↦ u(β_t)^{−1}c_t; GENTOW2-A untouched) is
now PROMOTED into the restated LEMMA GENTOW2-B above and made
effective by B″ (S5.2), which computes the needed u(β_t) up to the
consumer-invisible w. Kept below as composed, the record of the r1
correction.] [r1: the pre-repair
clause — a fixed-unit discrepancy acts by "ψ₃ ↦ y ↦ εy
substitution" and "every clause of GENTOW2-A survives verbatim" —
was FALSE at f₃ ≥ 2: a fixed δ multiplies every non-leading digit,
giving R = y^{f₃} − δ·Σ c_t y^t, which is not a y ↦ εy
substitution (that one scales coefficient t by ε^{t−f₃}, the
grade-covariant pattern; the two agree only at f₃ ≤ 1), and
irreducibility can die: over K₂ = F₄, ψ₃ = y² + ωy + 1 is
irreducible while the δ = ω twist y² + ω²y + ω has the root y = 1
(PE1 F3's counter-instance).] Corrected clause: if a future audit
finds ε-normalized digit = u(β)·(repo digit) — B′(3)'s own
direction, R_{3,β}(g) = u(β)·digit(g) [r2, PE2 F3: the pre-repair
hypothesis wrote the INVERSE convention (repo = u·ε-normalized);
harmless in substance since u ranges over arbitrary unit families
and c_t ↦ u^{−1}c_t absorbs either reading, but the box now
matches the lemma it cites] — with u ≢ 1 — fixed OR
grade-varying (the latter is the ϑ-cocycle mode of GENTOW5-A1's
repo-internal dictionary, GENTOW-4's η₂-cocycle finding) — then by
LEMMA GENTOW2-B′(5) the recipe at digit string (c_t) realizes
R_ν(Φ₃) = y^{f₃} − Σ u(β_t)c_t y^t. Since u is x₀-free and the
digit string is freely prescribable, re-parameterizing c_t ↦
u(β_t)^{−1}c_t realizes any admissible target ψ₃ (monic
irreducible, ψ₃(0) ≠ 0, degree f₃): THEOREM GENTOW2-A is untouched
(it consumes only hypothesis (ii), never a digit string), LEMMA
GENTOW2-B survives with the re-parameterized prescription, and the
only casualty of u ≢ 1 would be the cosmetic claim that the repo
digit string spells ψ₃'s coefficients. At f₃ ≤ 1 no
re-parameterization is even needed for clause survival: y − δc₀
stays monic irreducible with nonzero constant.

Neither identification touches the FGMN citation itself.

### S5.1 [r1] LEMMA GENTOW2-B′ — what the corpus derives toward
### B-2 (the graded-frame computation PE1 F2 asked for)

Fix a grade β ∈ Γ₂ (so s₃(β) = 0: eq (12) at i = 3 with
gcd(h₃, e₃) = 1 forces s ≡ 0, the S5 abscissa bookkeeping). Two
reads are in play on Φ₂-free elements g (deg g < m₃ = deg Φ₂) of
exact grade ν(g) = β:

  (R-FGMN)  R_{3,β}(g) ∈ F₃ = K₂ — Def 3.16 at i = 3, single
            j = 0 term: R_{3,β}(g) = ε₂(β)·R_{2,β}(g)(z₂), the
            ε₂-normalized coordinate;
  (R-repo)  digit(g) := res(g(x₀)/n̂₂(β̂)(x₀)) ∈ k(L2) ≅ K₂ — the
            GENHN-2′ coherent read against the ladder normalizer
            n̂₂(β̂) = π^a x^i Φ′^b at dv₂-height β̂ = e(µ₂)β,
            through the CANONICAL EVALUATION identification
            k(L2) ≅ F₃ [r2, PE2 F1]: Prop 1.15(1)/(2) (PDF p.7,
            S6.1 row 17) — F₃ := Im(∆₂ → ∆₃) ≅ F_{φ₃} = k(L2) by
            g + P₀⁺ ↦ res(g(x₀)), x₀ a Φ₂-root; FGMN make this
            identification themselves at §3.2 (PDF p.15: "By
            Proposition 1.15, Fᵢ is a field which may be
            identified with the residue class field F_{φᵢ}"). The
            pre-repair parenthetical here — "T(b)′(iii)'s
            identification (η₂ ↔ z₂)" — was wrong on both legs:
            T(b)′(iii) defines the repo leaf read and the repo
            field K₂ = F_Q(η, η₂) with no FGMN contact, and under
            the canonical identification the LETTERS do not
            correspond in general — the letter formula below gives
            z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋}.

**LEMMA GENTOW2-B′.** There is a unit u(β) ∈ K₂^× = F₃^*,
depending only on the grade β (not on g, not on x₀), namely
u(β) := R_{3,β}(n̂₂(β̂)), such that for each Φ₂-free g of exact
grade β:

  (3)  R_{3,β}(g) = u(β) · digit(g).

Consequently: (4) per grade β: (the repo read = the ε₂-normalized
coordinate on the Φ₂-free elements of exact grade β) ⟺ u(β) = 1
— B-2 as stated quantifies this over its per-grade families, and
the recipe consumes it only at its used grades β_t, so the
CONSUMED form of B-2 is u(β_t) = 1 there [r2, PE2 F4: the
pre-repair "(4) B-2 ⟺ u(β) = 1 at each grade the recipe uses"
conflated B-2's stated scope with the consumed scope; the
honest-residue paragraph below already carried the consumed form];
and (5) with arbitrary u, GENTOW2-B's sum gives R_{3,α}(Φ₃) =
y^{f₃} − Σ_{t<f₃} u(β_t)·c_t y^t (the honesty box's transformation
law).

*Proof.* u(β) ≠ 0: the ladder monomial n̂₂(β̂) has exact grade β
(B-1) and single-pin N₃-polygon {(0, β̂/e(µ₂))}, so R_{3,β}(n̂₂) ≠ 0
by Cor 4.4(1) [L1089 region, PDF p.21]. Now take g with digit d :=
digit(g) ∈ K₂^× and let ẑ_d be a grade-0 ladder lift of d (grade-0
lifts exist and read to d: T(b)′(iii), accepted — a repo-internal
supply, no FGMN contact). [r2, PE2 F2 — the pre-repair step applied
B-1 to h := g − ẑ_d·n̂₂(β̂) directly, outside B-1's deg < D₂
scope: deg(ẑ_d·n̂₂(β̂)) reaches m₃ = D₂ at the record's own N1
frame (worked trace below). Repaired h-step:] Divide the lift
product by Φ₂:

    ẑ_d·n̂₂(β̂) = q·Φ₂ + ρ,   deg ρ < m₃,   deg q ≤ m₃ − 2

(both factors have deg ≤ m₃ − 1). Then:

  (h-i) digit(ρ) = d and ν(ρ) = β exactly: x₀ is a Φ₂-root, so
        evaluation kills the qΦ₂ term — ρ(x₀) = ẑ_d(x₀)·n̂₂(β̂)(x₀)
        — hence res(ρ(x₀)/n̂₂(β̂)(x₀)) = res(ẑ_d(x₀)) = d ≠ 0, and
        B-1 (deg ρ < D₂: IN scope) turns the nonzero read into
        ν(ρ) = µ₂(ρ) = β exact.
  (h-ii) ν(qΦ₂) ≥ β: qΦ₂ = ẑ_d·n̂₂(β̂) − ρ, a difference of two
        elements of ν-value β.
  (h-iii) ν(qΦ₂) > β STRICTLY, so R_{3,β}(qΦ₂) = 0 by Lemma 3.17
        [L982, PDF p.19, [r1]-added cite]. Two legs (q ≠ 0 WLOG,
        else the term is absent). Leg e₃ ≥ 2: ν(qΦ₂) = ν(q) + w₃
        + λ₃ with ν(q) = µ₂(q) ∈ Γ₂ (deg q < m₃, Φ₂-free, Prop
        1.9) and w₃ ∈ Γ₂ but λ₃ ∉ Γ₂ (gcd(h₃, e₃) = 1, e₃ ≥ 2),
        so ν(qΦ₂) ∉ Γ₂ ∋ β and (h-ii)'s ≥ sharpens to >. Leg
        e₃ = 1 — the unit-q corner PE2 F2 flagged as unfenced,
        CLOSED here rather than fenced: suppose ν(qΦ₂) = β.
        Additivity gives R_{3,β}(ẑ_d·n̂₂(β̂)) = R_{3,β}(ρ) +
        R_{3,β}(qΦ₂). The left side and R_{3,β}(ρ) have y-degree
        0 (a grade-0 × single-pin product, resp. a deg < m₃
        single-point-polygon element — Cor 4.4(3)); but Cor
        4.7(2) at the Γ₂-graded factor q plus eq (14) [Q7] give
        R_{3,β}(qΦ₂) = R_{3,ν(q)}(q)·R_{3,w₃+λ₃}(Φ₂) =
        R_{3,ν(q)}(q)·y^{⌊1/e₃⌋} = R_{3,ν(q)}(q)·y at e₃ = 1,
        of y-degree exactly 1 with coefficient R_{3,ν(q)}(q) ≠ 0
        (Cor 4.4(1): exact grade, single-point polygon). A
        y-degree-0 identity cannot carry a nonzero y-linear term:
        contradiction, hence ν(qΦ₂) > β at e₃ = 1 too.
  (h-iv) B-1, now in scope: h′ := g − ρ has deg < D₂ and repo
        digit d − d = 0 at grade β (by (h-i)), hence ν(h′) > β by
        B-1's no-cancellation clause — h′ ∈ P_β^+(µ₃) — so
        R_{3,β}(h′) = 0 by Lemma 3.17.

Additivity (Cor 4.7(1) [Q8], twice: g = h′ + ρ and ẑ_d·n̂₂(β̂) =
qΦ₂ + ρ, with (h-iv) and (h-iii) killing the h′ and qΦ₂ terms)
gives R_{3,β}(g) = R_{3,β}(ρ) = R_{3,β}(ẑ_d·n̂₂(β̂)), and
multiplicativity at a grade-0 factor (Cor 4.7(2) [Q8], β′ = 0 ∈ Γ₂
— Cor 4.7 carries no degree hypothesis, so the deg = m₃ product is
legitimate HERE, unlike in B-1) factors it as
R_{3,0}(ẑ_d)·R_{3,β}(n̂₂(β̂)). Finally R_{3,0}(ẑ_d) = d: the
grade-0 degree-0 read is the F₃-algebra residue (Thm 4.8 [L1136,
PDF p.22, [r1]-added cite]), and under the canonical evaluation
identification (Prop 1.15(1), the (R-repo) display) that residue
IS res(ẑ_d(x₀)) = d — no letter correspondence enters [r2, PE2
F1: the pre-repair sentence attributed this step to "T(b)′(iii):
η₂ ↔ z₂", wrong on both legs — see (R-repo) and the letter
formula below]. Hence R_{3,β}(g) =
d·u(β) = u(β)·digit(g). x₀-freeness of u is by inspection: u(β) =
R_{3,β}(n̂₂(β̂)) never sees x₀. (4): the recipe's k̂_t has digit
c_t by construction (a K₂-digit lift), so R_{3,β_t}(k̂_t) =
u(β_t)c_t, and B-2's on-the-nose form is exactly u(β_t) = 1. (5):
substitute into the Cor-4.7(1) sum of GENTOW2-B's proof;
non-emptiness of each grade is Cor 3.3 [L647, PDF p.12, [r1]-added
cite] or the ladder itself. ∎

*[r2] Worked trace of the repaired h-step at the frame PE2 F2
exhibited (N1, K₂ = F₄, grade β̂ = 7 — the PE1-digit-table grade).*
Frame data recomputed this round: Φ′ = x² − 2 (w₂ = 1, λ₂ = 1/2,
µ₂(Φ′) = 3/2), Φ₂b = Φ′² − 2xΦ′ − 8 (m₃ = 4, w₃ = 3, λ₃ = 1/4,
e₃ = 2, e(µ₂) = 2, Γ₂ = ½ℤ). ẑ_{η₂} = xΦ′/4 (ν = 1/2 + 3/2 − 2 =
0; the minimal grade-0 monomial lift of an F₄∖F₂ class there),
n̂₂(7) = 8x (dv₂ = 2(3 + 1/2) = 7), product = 2x²Φ′ of deg 4 = m₃
— B-1 inapplicable as written, the PE2 finding. Division:
2x²Φ′ = 2·Φ₂b + (4xΦ′ + 4Φ′ + 16), so q = 2, ρ = 4xΦ′ + 4Φ′ + 16,
deg ρ = 3 < 4 ✓. (h-i): dv₂-pins of ρ — 4Φ′ ↦ 7 (the single
on-grade monomial), 4xΦ′ ↦ 8, 16 ↦ 8 — so ν(ρ) = 7/2 = β exact;
digit(ρ) = res(4Φ′(x₀)/(8x₀)) = res(ẑ_{η₂}(x₀))·res(2/x₀²) =
d·z₁^{−1} = d (this frame: z₁ = 1, and independently x₀² = 2 +
O(v > 1) forces res(x₀²/2) = 1 — note the z₁-power surfacing in a
digit comparison, the F1 letter mechanism in miniature). (h-iii),
e₃ = 2 leg: ν(2Φ₂b) = 1 + 13/4 = 17/4 ∉ Γ₂, dv₂ = 17/2 > 7 ✓
strict. [The PE2 report's sketch wrote "dv₂(2Φ₂b) = 2 + 7 = 9";
recomputed here dv₂(Φ₂b) = e(µ₂)(w₃ + λ₃) = 2·(13/4) = 13/2 — its
9 should be 17/2; the inequality 17/2 > 7 holds and the repair is
unaffected.] (h-iv): h′ = g − ρ, deg < 4, digit 0, B-1 in scope. ✓

*The letter formula ([r2] — PE2 F1's canonical identification).*
Under the (R-repo) evaluation identification the two level-2
letters are related by an explicit z₁-twist, derived from the PDF
data (sources PDF-verified this round, S6.1 rows 17–19):

    z₂ = η₂ · z₁^{−⌊ℓ₁u₂/e₁⌋}      (LETTER FORMULA)

*Derivation.* FGMN's letter is z₂ := the image of y₂ = H_{µ₂}(γ₂)
under ∆₂ → ∆₃ (PDF p.17 display), where γ₂ = φ₂^{e₂}π₂^{−u₂} with
u₂ := e₂V₂ + h₂ (Def 3.12, p.16: γᵢ = (Φᵢ)^{eᵢ}(πᵢ)^{−hᵢ},
Φᵢ = φᵢπᵢ^{−Vᵢ}; the §3.2 data V₂ = e(µ₁)w₂, h₂ = e(µ₂)λ₂ with
eq (9), pp.15–16, give e₂V₂ + h₂ = e(µ₂)(w₂ + λ₂) = the S2
dictionary's u₂ = dv₂(Φ′)), and π₂ = Φ₁^{ℓ₁}π^{ℓ′₁} = x^{ℓ₁}π^{ℓ′₁}
(§3.3, p.16: ℓ₁h₁ + ℓ′₁e₁ = 1, 0 ≤ ℓ₁ < e₁; Φ₁ = x since V₁ =
e(µ₀)µ₀(x) = 0). Under Prop 1.15(1) (p.7) the class evaluates:
z₂ = res(γ₂(x₀)) = res(Φ′(x₀)^{e₂}/π₂(x₀)^{u₂}). The repo letter
is η₂ = res(Φ′(x₀)^{e₂}/n̂(u₂)(x₀)) with n̂(u₂) = x^iπ^a the
letter-free ladder normalizer at dv₁-height u₂, 0 ≤ i < e₁
(T(b)′(i) normal form). The ratio n̂(u₂)/π₂^{u₂} = x^{i−ℓ₁u₂}
π^{a−ℓ′₁u₂} is a value-0 monomial, and a value-0 monomial
x^{e₁k}π^{−h₁k} = γ₁^k has residue z₁^k (γ₁ = x^{e₁}π^{−h₁},
Def 3.12 at i = 1). Both n̂(u₂) and π₂^{u₂} sit at dv₁-height u₂
(dv₁(π₂) = ℓ₁h₁ + ℓ′₁e₁ = 1), so ih₁ ≡ ℓ₁h₁u₂ mod e₁, i.e.
i ≡ ℓ₁u₂ mod e₁ (gcd(h₁, e₁) = 1); with 0 ≤ i < e₁ this pins
k = (i − ℓ₁u₂)/e₁ = −⌊ℓ₁u₂/e₁⌋. Multiplying the two residues
gives the display. ∎ At the S2 witness (e₁ = 2, h₁ = 1, u₂ = 5,
ℓ₁ = 1 ⟹ π₂ = x; i = 1, a = 2): z₂ = η₂·z₁^{−2}.

*Consequences ([r2]).* (i) FGMN's ψ₂ = minpoly(z₂) is the
z₁^{⌊ℓ₁u₂/e₁⌋}-twist of the repo ψ₂ = minpoly(η₂); the two agree
on the nose exactly when the twist fixes ψ₂ — in particular when
z₁^{⌊ℓ₁u₂/e₁⌋} = 1 (e.g. ℓ₁ = 0, or f₁ = 1 over q = 2 which
forces z₁ = 1). (ii) LETTER-BLINDNESS of the record, stated
honestly: the 13 machine witnesses standing at PE2 (5 committed +
2 battery-new + 3 PE1-fresh + 3 PE2-fresh) each sit at f₁ = 1
over q = 2, where z₁ = 1 and the twist is invisible — the record
could not have caught the pre-repair "η₂ ↔ z₂" parenthetical; the
r2 probe (S10, gentow2_r2_letter_probe.py) is the first
letter-live (f₁ = 2, z₁ ∈ F₄∖F₂) machine contact and tests the
LETTER FORMULA itself at a frame where the twist acts. (iii) B′
SURVIVES the canonical identification (re-derived this round, per
the PE2 charge): the lemma's statement and proof consume only the
evaluation identification — never a letter correspondence — at
exactly two sites (the (R-repo) display and the R_{3,0}(ẑ_d) = d
step), both now labeled Prop 1.15; u(β), (3), (4), (5) and the
x₀-/g-freeness inspection stand as displayed. The downstream
consumption "η₂(ξ) is a ψ₂-root" survives the twist by the S4
consumption note's [r2] clause (single-embedding coherence).

*What remains new (the honest B-2 residue).* Pinning u ≡ 1 is a
cross-frame comparison: by Thm 4.2's normal form H_µ(g) =
x₃^{s}p₃^{u}R_{3,β}(g)(y₃), u(β) is the coordinate of the repo
ladder monomial π^a x^i Φ′^b in FGMN's canonical homogeneous frame
x₃, p₃, y₃ — an explicit z₁, z₂-monomial per grade, computable
grade-by-grade but not computed anywhere in the corpus. GENTOW5's
LEMMA GENTOW5-A1 does NOT supply it: its fixed-unit ϑ_t dictionary
compares two REPO conventions (per-height coherent digits vs the
multiplicative side residual), both built on the same ladder
normalizers — a repo-internal cocycle, not the cross-frame unit
u(β). The derivation therefore stops at (3)–(5), which is enough
to make every consumer of GENTOW2-A robust to u ≢ 1 (see the
corrected fallback clause); u ≡ 1 itself stands as this note's own
disclosed identification, machine-supported as recorded in the
honesty box.

## S6. FAITHFULNESS PARAGRAPH (AXIOM_FAITHFULNESS discipline)

**Source.** Fernández, Guàrdia, Montes, Nart, "Residual ideals of
MacLane valuations", arXiv:1305.0775v3
(published J. Algebra 427 (2015) 30–75); local print
docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt. NOT
the excluded 2212.00294; no statement from 2212.00294 is consumed.

[r1] The pre-repair sentence here read "numbering verified against
the arXiv v3 PDF at ledger 63091ce" — an over-claim on both method
and scope (PE1 F1): ledger 63091ce's check was against the LOCAL
TEXT EXTRACTION (its own disclosed caveat), and its scope was
GRTJC's cite set, of which only Cor 4.7 and eq (14) overlap this
note's. The corrected provenance is S6.1 below, which closes the
PDF leg directly.

### S6.1 [r1] PDF-PROVENANCE TABLE (the r1 repair of PE1 F1)

**Method.** (i) Identity: docs/references/
fgmn_residual_ideals_1305.0775v3.pdf (md5
da846c82f1fcb619cefb3feb8164191e, sha256
651b0cef64e6aea11526965d3ef7879d69ce7c0a31af497978c3e6192f615f35,
518,522 bytes) was compared 2026-08-09 against a fresh fetch of
https://arxiv.org/pdf/1305.0775v3 — BIT-IDENTICAL (same md5, same
size); PDF page 1 carries the stamp "arXiv:1305.0775v3 [math.NT]
26 Jul 2013" and the title/author block. (ii) Statement check: each
row below was read VISUALLY off the rendered PDF page (Read-tool
page extraction) and compared against the S3 quote — a leg
decorrelated from the pdftotext layout extraction that the Lxxxx
pins index (the extraction-corruption rule's independent leg).
Verdict vocabulary: MATCH = statement content AND numbering agree
with the S3 quote/instantiated use.

| # | statement (S3 tag) | PDF page | layout pin | verdict |
|---|---|---|---|---|
| 1 | Lemma 1.11 [Q1] | 6 | L275 | MATCH |
| 2 | Cor 1.13 [Q2] | 7 | L315 | MATCH |
| 3 | Def 5.2 [Q3] | 24 | L1238–1239 | MATCH |
| 4 | Lemma 5.3 [Q4] | 24 | L1240–1244 | MATCH |
| 5 | Cor 4.4 (item 4 used) | 21 | L1089 | MATCH |
| 6 | Cor 4.7 [Q8] | 21–22 | L1121–1126 | MATCH |
| 7 | Cor 4.12 + proof constr. [Q5] | 22 | L1161–1166 | MATCH (incl. the print's "degre" typo, visually present in the PDF) |
| 8 | Prop 5.7 [Q7] | 25 | L1276–1281 | MATCH |
| 9 | eq (14) [Q7] | 19 | L1004 | MATCH |
| 10 | Cor 5.6 | 24 | L1263–1265 | MATCH |
| 11 | Thm 5.8 + degree-forcing display [Q6] | 25 | L1296–1302 | MATCH |
| 12 | Thm 6.3 + proof opening [Q9] | 28 | L1458–1465 | MATCH |
| 13 | Cor 6.4 + eq (23) [Q10] | 29 | L1523–1527 | MATCH |
| 14 | Cor 3.3 (S5.1 [r1] cite) | 12 | L647 | MATCH |
| 15 | Lemma 3.17 (S5.1 [r1] cite) | 19 | L982 | MATCH |
| 16 | Thm 4.8 (S5.1 [r1] cite) | 22 | L1136 | MATCH |
| 17 | Prop 1.15 (S5.1 [r2] identification + letter formula) | 7 | L340–344 | MATCH |
| 18 | Def 3.12 + §3.3 ℓᵢ, ℓ′ᵢ data (S5.1 [r2] letter formula) | 16 | L813–821 | MATCH |
| 19 | eq (9) + §3.2 data defs (S5.1 [r2] letter formula; S2 (e₃,f₃) row) | 15–16 | L785–806 | MATCH |

Supporting pins also PDF-verified on the same pass: Prop 1.9 (p.6),
Lemma 2.4 (p.9), Def 3.1 + display (4) (p.12), the §3.2 numerical
data table (pp.15–16), the N_i/R_{i,α} operator definitions + eq
(12) (p.17), Def 3.15 (the ε_i(α) constants) + Def 3.16 (p.18),
Def 3.18 + j₀ formula (p.19), the §6 header (bottom of p.27 —
layout L1433; the pre-repair pin "L1434" was off by one, PE1 F5).
[r2] Rows 17–19 were added in the PE2 repair round and verified by
the SAME two-leg method (fresh visual reads of PDF pp.7, 15, 16,
17 against the layout pins), together with three [r2] supporting
pins: the z_i/ψ_i definition display + y_i = H_{µ_i}(γ_i) (p.17,
L855–863), Lemma 3.13 (µᵢ(γᵢ) = 0, µᵢ(πᵢ₊₁) = 1/e(µᵢ); p.16,
L836–840), and §3.2's own Prop-1.15 identification sentence ("Fᵢ
... may be identified with the residue class field F_{φᵢ}", p.15).

**Statements consumed** (each quoted verbatim in S3): Lemma 1.11,
Cor 1.13, Def 5.2, Lemma 5.3, Cor 4.4, Cor 4.7, Cor 4.12 (+ its
proof's construction), Prop 5.7 + eq (14), Cor 5.6, Thm 5.8 (proof
display only, used as an argument-schema on our concrete Φ₃, not as
a statement), Thm 6.3, Cor 6.4. [r1] Added by the S5.1 derivation
(LEMMA GENTOW2-B′): Cor 3.3, Lemma 3.17, Thm 4.8 — each
PDF-verified, rows 14–16 of S6.1. [r2] Added by the S5.1 canonical
identification + LETTER FORMULA (PE2 F1): Prop 1.15, Def 3.12
(+ §3.3's ℓᵢ, ℓ′ᵢ), eq (9) with the §3.2 data definitions — each
PDF-verified, rows 17–19 of S6.1.

**Hypothesis audit** (why each FGMN hypothesis holds at our
instance): (H-a) v discrete, K_v complete: v = v_p on ℚ. (H-b) ν
inductive with a MacLane chain of length 3: the tower construction
IS such a chain; optimality (deg strictly grows) from stage
properness e₂f₂ ≥ 2 (T(b)′ setting) — and Cor 6.4 needs only "a
MacLane chain", not optimality. (H-c) F ∈ P: from GENTOW2-A(a),
which uses only [Q1],[Q2],[Q4],[Q6] + GENTOW2-B. (H-d) φ key for ν
with φ|_ν F: F = φ. (H-e) φ ≁_ν φ_r: proved in S4 from ψ₃ ≠ y via
[Q7]. (H-f) ψ₃(0) ≠ 0, monic irreducible /K₂, e₃f₃ ≥ 2: PROVISOS of
GENTOW2-A, discharged at every tower stage the repo constructs
(stage residuals are minimal polynomials of nonzero residue classes;
a proper stage has e₃f₃ ≥ 2 by definition — an improper "stage"
(e₃f₃ = 1) is a refinement, not a level, per FGMN Lemma 3.5/Prop 3.7
collapsing).

**Direction of fit.** The citation is consumed in the DEDUCTIVE
direction only: FGMN theorem → our instance. No repo lemma is used
to justify an FGMN statement. The two repo-side inputs (B-1)/(B-2)
enter only the bridge LEMMA GENTOW2-B (the recipe realizes (ii)),
never the citation's own hypotheses.

**What the cite does NOT give.** (i) It does not price any σ or
count: it feeds T(b)″'s ascent inputs only. (ii) It does not supply
the depth-3 node floor κ₃ > e₂f₂u₂ (item (6)(β)): positivity of λ₃
is a HYPOTHESIS of the augmentation and its provenance at tower
leaves is item (1)'s composed entry budgets. (iii) It does not prove
GENHN-2′ or the slot grammar — those are accepted corpus.

## S7. WHAT REMAINS OF ITEM (6) AFTER THIS NOTE

Item (6) = the iterated depth-≥3 carrier/slot/read (T(b)″). Its r3
residue was (α) + (β):

* **(α) — DISCHARGED here** (THEOREM GENTOW2-A(b)(c)(d) via FGMN
  Cor 6.4; bridge LEMMA GENTOW2-B). The ascent that forces a
  Φ₃-root's intermediate data now has its inputs as theorems.
* **(β) — rides item (1)**, exactly as the r3 box said: the floor
  κ₃ > e₂f₂u₂ (= λ₃ > 0, GENTOW2-B's hypothesis) at ACTUAL tower
  leaves needs the composed entry budgets. GENTOW-1 (in-flight this
  wave, same campaign: GENTOW1_PROOF_2026-08-09.md, status table
  rows "item (1) PROVED (S2)" + "COR GENTOW-1.1 (the depth-3 floor
  rider (6)(β)) PROVED (S2.4)", grade 0/2, hostile arc pending)
  supplies it; this note cites it AS IN-FLIGHT and does not
  re-derive it.
* **Depth ≥ 4**: GENTOW2-A is stated at the third stage but its
  proof pattern is level-uniform — Cor 6.4 is proved for chains of
  any length r, and the recipe/bridge argument reads verbatim with
  r+1 in place of 4 PROVIDED the level-r analogues of (B-1)/(B-2)
  (the deeper ladder grammar) are proved; those are the item-(2)
  inner-refine-transfer territory at depth ≥ 4 and are NOT claimed
  here. Scope of this note's theorem: the third stage (first live
  n = 16), which is what item (6) boxed.

Assembly consequence (display, not a new claim): with (α) proved and
(β) = COR GENTOW-1.1 (in-flight), T(b)″'s remaining content is pure
T(b)′-mechanism iteration (carrier via GENTOW2-A(a), slot inputs via
(c)+(d), read via T(b)′(iii) at the level-3 basis), i.e. item (6)
reduces to the SAME acceptance state as items (1)–(5): no residue
special to depth ≥ 3 remains open beyond them.
## S8. MACHINE BATTERY (gentow2_checks.py): 5 committed + 2 NEW

**SEAL STATE: VERDICT (read off the run artifacts).**

* **Sealed run** (gentow2_checks_output.txt, runner as sealed at
  commit c33f10e): **40 scored checks, 0 violations** — every pin
  table, one-sidedness, on-side residual support, and Bareiss
  resultant valuation EXACT on the A-route, and every PARI sig +
  nfeltval intermediate triple EXACT on the B-route, at W1, W2,
  W3–W5, N1, N2. TOOTH T1 FIRED (the floor-breaching recipe u₃ = 9
  < 10 is flagged NOT one-sided — pin (3,2) below the chord —
  machine-coupling (α)'s theorem to the (β) floor hypothesis).
  **TOOTH T2 FAILED AS DESIGNED** (machine sig [(8,1)], predicted
  [(4,1),(4,1)]): the design mis-read Lemma 5.3 — R = (y+1)² is a
  prime POWER (one residual ideal), and FGMN Thm 6.6 splits only
  across DISTINCT (λ, L) pairs, so non-key does NOT imply reducible;
  Φ₂² − 64x is irreducible with e = 8 and the tower simply refines
  further. As-sealed verdict: RED on the tooth criterion, with all
  40 scored checks green. Disclosed, kept as a record row.
* **Corrected tooth T2′** (preregistered before ITS first run,
  commit after the disclosure; run artifact
  gentow2_checks_output_run2.txt): at the N1 profile K₂ = F₄, the
  residual y² + y + 1 = (y+ω)(y+ω²) SPLITS, so
  Φ₂b² − 8xΦ₂b − 128 has a ONE-SIDED full-support polygon yet must
  factor [(2,2),(2,2)] — and DID: T2′ FIRED. Hypothesis (ii)'s
  irreducibility-over-K₂ is machine-load-bearing; the polygon side
  alone certifies nothing.
* **Re-run verdict: GREEN — 41 checks, 0 violations, teeth T1 + T2′
  both fired** (T2 recorded, not scored).
* New-witness yields: N2 is the FIRST machine witness of the
  f₃ ≥ 2 K₂-digit branch (the gap PE3 remark R1 disclosed as
  machine-unwitnessed anywhere); N1 is the first depth-3 contact at
  an f₂ = 2 tower (K₂ = F₄), residual ψ₂² = T⁴ + T² + 1 read off
  the machine side exactly as Cor 6.4 predicts.

Runner:
verification/openmath/gentow2_checks.py, preregistered predictions in
its module docstring (P-W1/P-W2/P-W3/4/5/P-N1/P-N2 + TOOTH-T1/T2),
written BEFORE the first full run. Witness inventory: the 5 committed
ones (W1 = the r3 box witness Φ₂² − 16Φ′; W2 = the PE3-F1/FR3
uncancelled-carry key Φ₂² − 16xΦ′; W3–W5 = the three SUPP-C n = 16
leaves) + 2 NEW depth-3 witnesses at other (e_i, f_i) profiles
(N1: the f₂ = 2 tower (2,1,1,2,2,1), Φ₃ = (Φ′²−2xΦ′−8)² − 64x;
N2: the f₃ = 2 branch (2,1,2,1,1,2), Φ₃ = Φ₂² − 2xΦ′Φ₂ − 32x — the
first machine witness ANYWHERE of the K₂-digit f₃ ≥ 2 clause, the
gap PE3 remark R1 disclosed). Oracle A = exact integer pins/hull/
residual-support/Bareiss-resultants; oracle B = PARI/gp
(factorpadic → per-factor idealprimedec + nfeltval intermediate
triples). Teeth: T1 = a floor-breaching recipe (u₃ = 9 < 10) whose
Φ′-development must be flagged NOT one-sided (machine-couples (α) to
the (β) floor); T2 = a reducible-residual recipe (R = (y+1)²) that
must factor [(4,1),(4,1)] — the polygon side alone must NOT certify.

## S9. [r1] PE1 REPAIR RECORD (2026-08-09)

Verifier: GENTOW2_passPE1_report.md (commit 61daa69; target blob at
531c212). Charge honored: repairs RE-DERIVED (the PDF pages were
re-read visually; the B′ bridge and the F6 row were recomputed at
the witness), sealed machine artifacts byte-untouched this round
(gentow2_checks.py, both run outputs, gentow2_pe1_fresh.py + its
output — zero diffs under verification/openmath/ in the r1 commits).

* **F1 (GAP, provenance over-claim) → CURED at the strongest
  available grade.** The actual arXiv paper was fetched
  (https://arxiv.org/pdf/1305.0775v3, 2026-08-09) and found
  BIT-IDENTICAL to the local docs/references PDF (md5
  da846c82f1fcb619cefb3feb8164191e, 518,522 bytes, both). The 12
  consumed statements + eq (14) were then each verified against the
  rendered PDF pages — content AND numbering — by a visual read
  decorrelated from the pdftotext layout extraction: 13/13 MATCH
  (table S6.1), plus 3 [r1]-added cites (rows 14–16) and 8
  supporting pins. The three ledger-claim sentences (S1, S3, S6)
  now state the true method and scope. Commit 1e091d1.
* **F2 (GAP, B-2 provenance pointer) → CURED: partially derived +
  honestly re-attributed.** New LEMMA GENTOW2-B′ (S5.1) derives
  from accepted corpus (B-1 + T(b)′(iii) + Cor 4.7/Lemma 3.17/
  Thm 4.8): repo digit and FGMN ε₂-coordinate agree up to an
  x₀-free, g-free unit family u(β) = R₃,β(n̂₂(β̂)). B-2's residue
  — u = 1 at the grades used — is re-attributed as FIRST MADE IN
  THIS NOTE, disclosed-not-derived, with its machine support stated
  as support. GENTOW5-A1 checked and shown repo-internal (its ϑ_t
  compares two repo conventions; it cannot supply the cross-frame
  u). Commit dd44d20.
* **F3 (GAP, false fallback clause) → CURED.** The y ↦ εy sentence
  is deleted; the corrected clause displays the true transformation
  law (B′(5): R = y^{f₃} − Σ u(β_t)c_t y^t), the digit
  re-parameterization c_t ↦ u(β_t)^{−1}c_t that keeps GENTOW2-A
  and its consumers intact under BOTH discrepancy modes (fixed and
  grade-varying/cocycle), the verifier's F₄ counter-instance, and
  the f₃ ≤ 1 scope where the old clause was right. Commit dd44d20.
* **F4 (MINOR) → CURED**: Φ₂ = φ₃ ∈ KP(ν) via Lemma 5.3(1) added
  where Prop 5.7 fires (S4). This commit.
* **F5 (MINOR) → CURED**: §6-header pin corrected L1434 → L1433
  (PDF p.27). Commit 1e091d1.
* **F6 (MINOR) → CURED**: the S2 (e₃, f₃) row now defines its
  target — FGMN (e₃, f₃) with m₄ = e₃f₃m₃ (eq (9)); the undefined
  "e₄-level data" label retired; witness denominator recomputed
  (ν(Φ₂) = 21/8 → e₃ = 2). This commit.

Grade: attempt 0/2 unchanged after r1. Next: PE2 (second hostile
pass) on the repaired note.

## S10. [r2] PE2 REPAIR RECORD (2026-08-09)

Verifier: GENTOW2_passPE2_report.md (commit aff457c). Verdict
there: NOT CLEAN — 0 CRITICAL, 2 GAP (both inside the [r1]-new
LEMMA GENTOW2-B′), 2 MINOR; 16/16 provenance rows, the theorem
chain, the machine legs, and the f₃ = 3 fresh route HELD. Charge
honored this round: the canonical formula was RE-DERIVED from the
PDF (not copied from the report), the three F1 sources were
PDF-verified by the two-leg method and added as S6.1 rows 17–19,
and the F2 repair was re-derived at the record's own N1 grade-7
frame. Sealed machine artifacts byte-untouched (zero diffs under
verification/openmath/ for the sealed files in the r2 commits);
machine support this round is ADDITIVE only.

* **F1 (GAP, the "(η₂ ↔ z₂)" identification parenthetical) →
  CURED.** The identification B′ consumes is restated as the
  canonical evaluation isomorphism (Prop 1.15(1)/(2), PDF p.7 —
  FGMN's own §3.2 identification sentence, p.15), at both of its
  use sites ((R-repo); the R_{3,0}(ẑ_d) = d step). The
  mis-attribution to T(b)′(iii) is corrected (T(b)′(iii) supplies
  only the repo-side lift existence + read — no FGMN contact).
  The LETTER FORMULA z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋} is derived in S5.1
  from Def 3.12 + eq (9)/§3.2 data + §3.3 + Prop 1.15 (S6.1 rows
  17–19, PDF-verified pp.7/15/16 + p.17 z_i pins); at the S2
  witness z₂ = η₂·z₁^{−2}. Propagated: the S2 ψ₂-row and the S4
  clause-(c) bullet now state "equal up to the z₁-twist, on the
  nose when the twist fixes ψ₂"; the S4 consumption note carries
  the single-embedding robustness of "η₂(ξ) is a repo-ψ₂-root".
  Letter-blindness disclosed (honesty box + S5.1): the 13 standing
  witnesses sit at f₁ = 1 over q = 2 (z₁ = 1). B′ SURVIVAL under
  the canonical identification re-derived in S5.1 consequences
  (iii). This commit.
* **F2 (GAP, B-1 applied outside its deg < D₂ scope in B′'s
  h-step) → CURED, corner CLOSED.** The h-step now divides the
  lift product by Φ₂ (ẑ_d·n̂₂(β̂) = qΦ₂ + ρ, deg ρ < m₃): digit(ρ)
  = d via the Φ₂-root evaluation, B-1 applies to g − ρ in scope,
  and the qΦ₂ term dies by Lemma 3.17 after the strictness
  ν(qΦ₂) > β — leg e₃ ≥ 2 by the value group (λ₃ ∉ Γ₂), leg
  e₃ = 1 by a y-degree contradiction (Cor 4.7(2) + eq (14) put
  R_{3,β}(qΦ₂) at y-degree 1 with nonzero coefficient inside a
  y-degree-0 identity). The e₃ = 1 unit-q corner the report
  flagged as unfenced is thereby CLOSED, not fenced. Worked trace
  at the N1 grade-7 frame (q = 2, ρ = 4xΦ′ + 4Φ′ + 16) with the
  report-sketch arithmetic slip corrected (dv₂(2Φ₂b) = 17/2, not
  9; inequality unaffected). This commit.
* **F3 (MINOR, u-direction slip) → CURED**: the fallback clause's
  hypothesis now reads in B′(3)'s direction (ε-normalized =
  u·repo). This commit.
* **F4 (MINOR, B′(4) scope conflation) → CURED**: B′(4) restated
  per-grade with the consumed scope (u(β_t) = 1 at used grades)
  separated from B-2's stated scope. This commit.
* **[r2] MACHINE LEG (additive; the PE2 report's disclosed PE3
  fresh-route need): LETTER-LIVE PROBE GREEN — 21 checks, 0
  violations, first run under seal.** Runner
  verification/openmath/gentow2_r2_letter_probe.py (sealed at
  commit d56e439 with preregistered predictions; no smoke run),
  output gentow2_r2_letter_probe_output.txt. Frame LP1 = the
  record's first f₁ = 2 contact (base slope 1/2, ψ₁ = y² + y + 1,
  Φ′_LP1 = x⁴ + 2x² + 4, Φ₂_LP1 = Φ′² − 8x³, (e, f) = (4, 2)
  confirmed): the LETTER FORMULA fired LIVE — z₁ ∈ F₄∖F₂
  (z₁² + z₁ + 1 = 0), η₂ = z₁, z₂ = 1 = η₂·z₁^{−4} at
  ⌊ℓ₁u₂/e₁⌋ = ⌊9/2⌋ = 4 — and the TOOTH fired: η₂ ≠ z₂, i.e. the
  pre-repair "η₂ ↔ z₂" parenthetical is machine-refuted at LP1
  while the canonical formula holds exactly. Dual routes: exact
  integer v₂-resultants (4, 18, 8, 26, 32) + the polynomial
  identity x⁶ − 8 = (x² − 2)Φ′_LP1 (an exact-algebra proof of
  z₂ = 1) on the A-side, PARI factorpadic/idealprimedec/nfeltval/
  nfmodpr on the B-side.

Grade: attempt 0/2 unchanged (the counter starts only on a CLEAN
pass; PE2 was NOT CLEAN). Next: PE3 (hostile pass on the
r2-repaired note; the letter-live geography now has a committed
machine foothold at LP1, and HETOW's frame-Y/R family remains the
candidate for a deeper letter-live route).

### Dated corrections (2026-08-09, post-PE3)

*Source: `GENTOW2_passPE3_report.md` @ 92ac16b — verdict CLEAN
(0 CRITICAL, 0 GAP, 2 MINOR); the r2 surfaces (LETTER FORMULA,
h-step corner, LP1 probe) held under independent re-derivation, and
the PE3 fresh route (first z₂ ≠ 1 letter-live contacts, p = 3/F₉)
came back 50/0 GREEN first-run-under-seal. Per the arc the item-(6)
acceptance counter moved 0/2 → **1/2 and HOLDS AT 1/2**: the two
cures below are dated appends to MINOR findings, not a scoring
round; one further clean pass on a fresh surface is required for
acceptance. The body above is BYTE-FROZEN — each correction below
supersedes its referenced text of record. Sealed machine artifacts
untouched by this append.*

**C-m1 (cures PE3 [m1] — the implicit evaluation-extension line in
the S5.1 letter-formula derivation).** The derivation's first
display ("Under Prop 1.15(1) (p.7) the class evaluates: z₂ =
res(γ₂(x₀)) = res(Φ′(x₀)^{e₂}/π₂(x₀)^{u₂})") applies Prop 1.15(1)
— stated for POLYNOMIAL classes g + P₀⁺ ↦ g(θ) + m_φ — to the
rational class of γ₂ = Φ′^{e₂}π₂^{−u₂}. The denominator-clearing
bridge, now displayed: pick a polynomial representative b of the
letter class, H_{µ₂}(b) = y₂, i.e. (clearing the monomial
denominator) µ₂(b·π₂^{u₂} − Φ′^{e₂}) > µ₂(Φ′^{e₂}) = e₂(w₂ + λ₂).
Evaluating at the Φ₂-root x₀ with v ≥ µ₂ on polynomials gives
v(b(x₀)π₂(x₀)^{u₂} − Φ′(x₀)^{e₂}) > e₂(w₂ + λ₂); the denominator's
value is EXACT and stable, v(π₂(x₀)) = 1/e(µ₁) (Lemma 3.13(1), the
[r2] supporting pin, PDF L836–840; dv₁(π₂) = 1), so v(π₂(x₀)^{u₂})
= u₂/e(µ₁) = e(µ₂)(w₂ + λ₂)/e(µ₁) = e₂(w₂ + λ₂) exactly (e(µ₂) =
e₂·e(µ₁), §3.2 data). Dividing: v(b(x₀) − γ₂(x₀)) > e₂(w₂ + λ₂) −
e₂(w₂ + λ₂) = 0, hence res(b(x₀)) = res(γ₂(x₀)), and Prop 1.15(1)
applied to the polynomial b yields the display. The γ₁^k residue
step admits the same line verbatim with denominator a monomial in
π₂ and π at exact values (v(π) = 1, π a base uniformizer — no
stability input needed there). PE3 checked this line goes through
([m1]); the formula's conclusion is additionally machine-true at
LP1 and at both LV frames. The two other identification use-sites
((R-repo); the R_{3,0}(ẑ_d) = d step) apply Prop 1.15/Thm 4.8 to
polynomial classes and need no bridge.

**C-m2 (cures PE3 [m2] — the STATUS header's arc bracket, stale at
r2).** The header's closing bracket ("[r1 …; record in S9 … Grade
stays 0/2; PE2 next.]") is SUPERSEDED by the arc through r2/PE3:

> [r1 2026-08-09, post-PE1 repair round: F1 PDF-provenance leg
> CLOSED, F2 B-2 partially derived + honestly re-attributed (LEMMA
> GENTOW2-B′, S5.1), F3 fallback clause corrected, F4/F5/F6 minors
> cured; record in S9. Grade stays 0/2.]
> [r2 2026-08-09, post-PE2 repair round: F1 canonical
> identification CURED — Prop 1.15 evaluation isomorphism + S5.1
> LETTER FORMULA z₂ = η₂·z₁^{−⌊ℓ₁u₂/e₁⌋} (S6.1 rows 17–19); F2
> h-step CURED with the e₃ = 1 corner CLOSED; F3/F4 minors cured;
> LETTER-LIVE PROBE LP1 GREEN 21/0 (first f₁ = 2 contact; TOOTH
> η₂ ≠ z₂ machine-refutes the pre-repair parenthetical); record in
> S10. Grade stays 0/2.]
> [PE3 2026-08-09: CLEAN — 0C/0G/2m (report @ 92ac16b); fresh route
> 50/0 GREEN, first z₂ ≠ 1 letter-live contacts (p = 3/F₉, teeth on
> both frames, direction opposite to LP1); acceptance counter
> 0/2 → 1/2, HOLDS AT 1/2; the 2 MINORs cured in this dated
> section. Next: acceptance attempt (second clean pass on a fresh
> surface).]
