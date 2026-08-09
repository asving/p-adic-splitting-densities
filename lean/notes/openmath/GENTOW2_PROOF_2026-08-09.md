# GENTOW-2: [GENHN-TOW-1] item (6)(α) — the iterated key's
# intermediate one-sidedness DISCHARGED BY FAITHFUL CITE
# (FGMN Theorem 6.3 + Corollary 6.4), 2026-08-09

**STATUS: COMPOSED, item (6)(α) PROVED-VIA-CITE (THEOREM GENTOW2-A +
LEMMA GENTOW2-B), battery GREEN (41 checks/0 violations, teeth T1 +
T2′ fired; T2 = disclosed failed design). Grade 0/2 (attempt; hostile
arc later). Unit: GENTOW-2, BOX-CLOSURE campaign.**

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
## S4. THEOREM GENTOW2-A (item (6)(α) DISCHARGED)

Setting: a depth-2 tower per T(b)′ (S8 annex, accepted), FGMN chain
as in S2's dictionary: µ₀ →(x, λ₁) µ₁ →(Φ′, λ₂) µ₂ →(Φ₂, λ₃) µ₃ = ν,
an optimal MacLane chain (deg x < deg Φ′ < deg Φ₂ — the tower's
stages are proper, e₂f₂ ≥ 2 in repo names). Base field K = ℚ (or a
number field), v = the p-adic valuation, K_v complete discrete —
FGMN's standing setting (their §6 header, L1434).

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
    where FGMN's ψ₂ = R₂(φ₃) is the repo ψ₂ by Cor 5.6(2) — clause
    (c). (Consistency: FGMN Cor 4.4(4) gives deg R₂(Φ₃) =
    (s′−s)/e₂ = ℓ₂/e₂ = f₂e₃f₃ = deg(ψ₂^{e₃f₃}). ✓)
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
η₂(ξ) read through T(b)′(ii)'s slot lemma is a ψ₂-root. The PE3-F1
correction's mechanism attribution ("the carry terms CLEAR the side")
is now a THEOREM, not bookkeeping: Cor 6.4 forces every pin strictly
above the side except the on-side residue pattern of ψ₂^{e₃f₃}.

## S5. LEMMA GENTOW2-B (the bridge clause): the T(b)″ recipe
## satisfies R_ν(Φ₃) = ψ₃

**LEMMA GENTOW2-B.** Let ψ₃ = y^{f₃} − Σ_{t<f₃} c_t y^t ∈ K₂[y]
(monic, c_t ∈ K₂ = F₃), and let the recipe data be as in the r3 box:
k̂_t ∈ K[x] with deg k̂_t < deg Φ₂, dv₂-height u₃(f₃ − t), and
K₂-digit residual class c_t (a GENHN-2′ ladder lift; k̂_t = 0 when
c_t = 0), where u₃ = e₃·κ₃, gcd-normalized so the pins (e₃t,
u₃(f₃−t)) lie on the line through (e₃f₃, 0) of dv₂-slope κ₃, with
κ₃ > e₂f₂u₂ (equivalently λ₃ := κ₃/(e₁e₂) − ν_{µ₂}(Φ₂)... > 0; the
positivity is the [r1]-style node-floor arithmetic, here an explicit
HYPOTHESIS). Then Φ₃ := Φ₂^{e₃f₃} − Σ_{t<f₃} k̂_t Φ₂^{e₃t} satisfies
R_ν(Φ₃) = ψ₃.

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
the K₂-digit class of k̂_t up to the unit constant ε₂(β) ∈ F₃* —
and the repo's "K₂-digit lift with class c_t" is DEFINED through the
same graded read (T(b)′(ii)'s slot grammar = GENHN-2′, accepted
2026-08-09 corpus), i.e. the recipe prescribes the digit in the
ε-normalized coordinate, making R_{3,β}(k̂_t) = c_t on the nose.
Summing: R_{3,α}(Φ₃) = y^{f₃} − Σ c_t y^t = ψ₃, and since
ψ₃(0) = −c₀ ≠ 0 we get R₃(Φ₃) = R_{3,α}(Φ₃) = ψ₃ (Def 3.18,
L994–1000, j₀ = 0). ∎

*Honesty box for GENTOW2-B.* Two repo-side identifications carry
this proof and are consumed AS ACCEPTED CORPUS, not re-proved here:
(B-1) the dv₂ ladder value of a deg < D₂ ladder element equals its
µ₂-value (GENHN-2′'s two-step class separation — LEMMA GENHN-T(b)′
(ii), S8 annex, accepted); (B-2) the repo's K₂-digit alphabet is the
ε₂-normalized F₃-coordinate of FGMN's Def 3.16 (this is the [W-2]
graded-dictionary identification at level 2, the same one T(b)′'s
proof already uses to read residuals; if a future audit finds the
repo digit differs from the ε-normalized digit by a fixed unit, the
recipe's c_t simply re-parameterizes — ψ₃ changes by the
substitution y ↦ εy, staying monic-irreducible of the same degree
after renormalization, and every clause of GENTOW2-A survives
verbatim since GENTOW2-A takes (ii) R_ν(Φ₃) = irreducible-with-
nonzero-constant as its only residual input). Neither identification
touches the FGMN citation itself.

## S6. FAITHFULNESS PARAGRAPH (AXIOM_FAITHFULNESS discipline)

**Source.** Fernández, Guàrdia, Montes, Nart, "Residual ideals of
MacLane valuations", arXiv:1305.0775v3
(published J. Algebra 427 (2015) 30–75); local print
docs/references/fgmn_residual_ideals_1305.0775v3_layout.txt,
numbering verified against the arXiv v3 PDF at ledger 63091ce. NOT
the excluded 2212.00294; no statement from 2212.00294 is consumed.

**Statements consumed** (each quoted verbatim in S3): Lemma 1.11,
Cor 1.13, Def 5.2, Lemma 5.3, Cor 4.4, Cor 4.7, Cor 4.12 (+ its
proof's construction), Prop 5.7 + eq (14), Cor 5.6, Thm 5.8 (proof
display only, used as an argument-schema on our concrete Φ₃, not as
a statement), Thm 6.3, Cor 6.4.

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
