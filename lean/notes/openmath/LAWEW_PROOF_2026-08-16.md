# LAW E-W — the K2-division boundary identity, PROVED — 2026-08-16, unit EWBS2

**Provenance.** OM-10 LEG E (unit note `docs/openmath-campaign/OM-10_n8-boxes_2026-08-16.md`
§2.4; battery `verification/openmath/om10_cert.py`) certified, 54/54 crossing reads at the
W1/W2 genres and tight per T-E-BOUND, the law

> for an in-budget single-entry member `f = Φ₂^{μ₂} + c·π^α·x^a·Φ′^b·Φ₂^{j′}`, a
> coordinate-0 entry never crosses; a crossing entry (`a + i₂ ≥ D′`, `j′ = 1`) produces
> discrepancy at EVERY coordinate with `mindiff_j = Θ_j + (entry height − side height)`,

and named its proof "one careful page at the K2-division bookkeeping" (HYP.71 ARC NOTE).
This note is that page. Every display below was certified BEFORE this note was composed —
not just the pin law but the exact quotient/remainder slot dictionaries, bit-exact on 281
crossing rows at 11 frames spanning `D′ ∈ {3,4,5,6}`, `i₂ ∈ {1,2}`, `m ∈ {3,4,5}`,
`μ₂ ∈ {2,3}`, `p ∈ {2,3,5}`, `ω ≠ 1`, wrap offset `s ∈ {0,1}` — strictly beyond OM-10's
sweep (`verification/openmath/ewbs2_lawew_cert.py`, GREEN 2796/0, 5/5 teeth; §6).

**Status: THEOREM (proved below), at the scope of §0.** What it converts: HYP.71(b)'s
refutation-repair and HYP.78's single-crossing classification move CERTIFIED → PROVED at
this geography class (§5 consumption map). What stays open is listed in §4, item by item.

---

## §0. Frame class, instrument, statement

Throughout, `O` is a complete DVR with uniformizer `π`, residue characteristic `p`, and
`v = v_π` the normalized valuation. (The certified frames are `O = ℤ_p`, `π = p`.)

**Frame hypotheses (the trinomial single-crossing geography).** Fix integers
`D′ ≥ 2, m ≥ 2, i₂ ≥ 1, v₂ ≥ 1, v₀ ≥ 1, μ₂ ≥ 2` and units `ω, ĉ₂, ĉ₀ ∈ O^×` with:

* **(F1)** `Φ′ = x^{D′} − πω` — the level-1 key (`e₁ = D′`, `f₁ = 1`, `h = 1`; Eisenstein,
  one-sided of slope `1/D′`).
* **(F2)** `Φ₂ = Φ′^m + P·Φ′^{m−1} + c₀` with `P := ĉ₂ π^{v₂} x^{i₂}`, `c₀ := ĉ₀ π^{v₀}`
  — the level-2 key in trinomial developed form (`e₂ = 1`, `f₂ = m`); the sole
  `x`-carrying entry sits at Φ′-power `m − 1`.
* **(F3)** on-side: `u₂ := D′v₂ + i₂` and `D′v₀ = m·u₂` (both K2 entries sit ON the
  level-2 side of height `E₂ := m·u₂`).
* **(F4)** `δ := u₂ − D′ ≥ 1` (the frame margin; `Frame.delta` in the instrument).
* **(F5)** in-grid: `μ₂·i₂ < D′`.

*Remark (why `e₂ = 1` is not a loss here).* In the general instrument the on-side
condition for an entry at Φ′-power `m − 1` reads `(e₁e₂)v₂ + i₂e₂h = u₂`, so `e₂ ∣ u₂`;
with the level-2 slope in lowest terms (`gcd(u₂, e₂) = 1`) this forces `e₂ = 1`. The
geography class of (F1)–(F5) is the whole single-crossing trinomial family with the
crossing entry adjacent to the monic term, not a convenience slice of it.

**The instrument (verbatim `om10_cert.py :: Frame`, route E).** Write `D₂ := mD′`.
* *Grid and heights.* A **slot vector** is an element of `⊕_{b′<m} O[x]_{<D′}` — slots
  `(a′, b′)` with `0 ≤ a′ < D′`, `0 ≤ b′ < m`, the value at `(a′,b′)` being the
  `x^{a′}`-coefficient of the `b′`-component. The **height** of a nonzero value `λ` at
  slot `(a′,b′)` is `ht := D′·v(λ) + a′ + b′u₂` (the frame's `ee·v + a′e₂h + b′u₂` at
  `ee = D′`, `e₂ = h = 1`). The **pin** of a slot vector is the min height over its
  nonzero slots (undefined if empty).
* *dev.* Every `g ∈ O[x]` has a unique Φ′-adic development `g = Σ_{b′} g_{b′}Φ′^{b′}`,
  `deg g_{b′} < D′`; for `deg g < D₂` this is a slot vector `dev(g)`. The map is
  `O`-linear (uniqueness of remainders).
* *red.* For an `x`-polynomial `z`, `red(z) :=` the remainder of `z` mod `Φ′` — the
  quotient is DISCARDED (the instrument's defining lossiness). On monomials:
  `red(λx^N) = λ(πω)^{⌊N/D′⌋} x^{N mod D′}` (iterate `x^{D′} ≡ πω`); `red(Φ′·z) = 0`;
  `red(z) ≡ z (mod Φ′)`; red is `O`-linear.
* *Honest ledger.* For monic `f` of degree `μ₂D₂`: `f = Σ_{j≤μ₂} H_j Φ₂^j`,
  `deg H_j < D₂`, `H_{μ₂} = 1`. Honest coordinate `j` (`j < μ₂`) is `dev(H_j)`.
* *Shadow ledger (route E).* Let `A(Y) := Σ_i A_i Y^i ∈ O[x][Y]` be the full Φ′-adic
  development of `f` read as a `Y`-polynomial (so `A(Φ′) = f`, `deg_x A_i < D′`, monic
  top). Set `K(Y) := Y^m + P·Y^{m−1} + c₀` (monic in `Y`). Iterated division in
  `(O[x])[Y]` gives the unique **chain**
  `A = Σ_{j=0}^{μ₂} R_j(Y)·K(Y)^j` with `deg_Y R_j < m` for `j < μ₂` and `R_{μ₂} = 1`.
  Shadow coordinate `j` is `red(R_j)` slotwise.
* *Discrepancy.* `Δ_j := red(R_j) − dev(H_j)`; `mindiff_j := pin(Δ_j)`.
* *Floors.* `Θ_j := (μ₂ − j)E₂ + δ` (the frame's `theta`).

**Member class.** `f = Φ₂^{μ₂} + C·Φ₂^{j′}` with `C = c·π^α·x^a·Φ′^b`, `c ∈ O^×`
(WLOG — `v(c)` folds into `α`), `α ≥ 0`, `0 ≤ a < D′`, `0 ≤ b < m`, `j′ ∈ {0, 1}`.
Write the **entry height** `H_C := D′α + a + b·u₂` and, when `j′ = 1`, the **excess**
`ε := H_C − (μ₂ − 1)E₂` (entry height minus side height; the identity below is
polynomial and needs NO sign assumption on `ε` — the leaf-locus reading is `ε ≥ 1`).

> **THEOREM (LAW E-W).** Under (F1)–(F5), for every member of the class above:
>
> **(a) No crossing.** If `j′ = 0`, or `a + i₂ < D′`, then `Δ_j = 0` for every
> `j < μ₂`: the shadow ledger equals the honest ledger exactly.
>
> **(b) Single crossing.** If `j′ = 1` and `a + i₂ ≥ D′`, put `s := a + i₂ − D′` and
> `g := c·ĉ₂·π^{α+v₂}·x^s`. Then `Δ_j = 0` for `2 ≤ j < μ₂`, while
>
> ```
> Δ₁ = red( Σ_{k=0}^{b} (−1)^k     g P^k      Y^{b−k} )
> Δ₀ = red( (−1)^{b+1} g P^{b+1} Y^{m−1}
>            + Σ_{k=0}^{b} (−1)^{k+1} g P^k c₀ Y^{b−k} )
> ```
>
> every slot of `Δ₁` is nonzero of height exactly `H_C + δ`; every slot of `Δ₀` is
> nonzero of height exactly `H_C + E₂ + δ`, except that at `b = m − 1` the two
> `Y^{m−1}`-deposits merge into the single slot `(s, m−1)` with value
> `g·π^{v₀}·((−1)^m ĉ₂^m ω^{mi₂/D′} − ĉ₀)`, of height `≥ H_C + E₂ + δ` (possibly
> higher or vanishing); the slots `k = 1, …, b` are unaffected. Consequently
>
> `mindiff₁ = Θ₁ + ε` and `mindiff₀ = Θ₀ + ε`, exactly.
>
> At `μ₂ = 2` — the certified genre — that is every coordinate: OM-10's LAW E-W.

The certified sweeps sit inside this class: W1/W2 are (F1)–(F5) at
`(D′, i₂, m, v₂, v₀) = (3, 1, 3, 3, 10)`, `p ∈ {2,3}`, `μ₂ = 2`.

---

## §1. Three preliminary lemmas

**LEMMA 0 (route agreement — the instrument's R-route computes the same slots).** The
implementation also carries a route R (reduce every generated coefficient mod `Φ′`
immediately). Claim: route R's output equals `red`(route E's output) slotwise. *Proof.*
Both routes execute the identical top-down index schedule; the branch test ("skip if the
current coefficient is zero") differs between them only when one side's coefficient is a
nonzero `Φ′`-multiple, and moving/subtracting a `Φ′`-multiple changes any stored
coefficient by a `Φ′`-multiple. Inductively, every stored coefficient of route R is
congruent mod `Φ′·O[x]` to its route-E counterpart: each step moves a top coefficient
into the quotient (congruent moves) and adds `−c·K2_k` to lower slots (`c_R ≡ c_E`
implies congruent results; `red(z) ≡ z`). Route R's emitted coordinates are reduced
(`deg < D′`) by construction; `red`(route E's) are reduced; two reduced polynomials
congruent mod the degree-`D′` monic `Φ′` are equal. ∎
(Measured: 39 DUAL checks in OM-10 + 11 here, all bit-equal.)

**LEMMA 1 (chain linearity and the base chain).** For fixed monic `K`, quotient and
remainder are `O[x]`-linear in the dividend (uniqueness of monic division), hence so is
each chain coordinate `R_j` (a composition of remainder- and quotient-maps). Moreover
the chain of `K^{μ₂} + E′Y^bK^{j′}` (`E′ ∈ O[x]`, `deg_Y` of the tail `< m + j′·m ≤ μ₂m`)
is: `R_{j′} = E′Y^b`, `R_j = 0` for `j ≠ j′, μ₂`, `R_{μ₂} = 1`. *Proof.* Direct
telescoping: `K^{μ₂} + E′Y^bK^{j′} = Σ_j R_jK^j` with the displayed `R_j` is an identity,
`deg_Y R_j < m` throughout, and the chain decomposition is unique. ∎

**LEMMA 2 (the trace half dies).** For any `M ∈ O[x][Y]`, every chain coordinate of
`Φ′·M` is `Φ′·(chain coordinate of M)` — `Φ′` is an `O[x]`-scalar for the `Y`-division —
hence dies under `red`. ∎

---

## §2. Proof of (a)

`dev` of the pure power: `K(Y)^{μ₂}` has coefficients that are `ℤ`-combinations of
products of at most `μ₂` entries from `{P, c₀}`, of `x`-degree at most `μ₂i₂ < D′`
by (F5); since `K(Φ′)^{μ₂} = Φ₂^{μ₂}` and the coefficients are in-grid, uniqueness of
the development gives `A(Φ₂^{μ₂}) = K^{μ₂}`.

`dev` of the entry term: at `j′ = 0`, `C = cπ^αx^aΦ′^b` is itself a development slot
(`a < D′`). At `j′ = 1` with `a + i₂ < D′`, `C·Φ₂ = E′Y^bK(Y)|_{Y=Φ′}` with
`E′ := cπ^αx^a` and coefficients `E′·{1, P, c₀}` of `x`-degrees `{a, a+i₂, a}`, all
in-grid: `A(CΦ₂) = E′Y^bK`.

So in both cases `A(f) = K^{μ₂} + E′Y^{b}K^{j′}` (reading `E′Y^bK^0 = C`'s slot at
`j′ = 0`), and by LEMMA 1 the chain is `R_{j′} = dev(C)`, `R_j = 0` otherwise. The
honest ledger of `f` is `H_{j′} = C` (degree `a + bD′ ≤ D₂ − 1 < D₂`), `H_j = 0`
otherwise. All chain coefficients are in-grid, so `red` is the identity on them:
`Δ_j = 0` for all `j`. (Route R runs the same in-grid computation, LEMMA 0.) ∎

---

## §3. Proof of (b)

**Step 1 (the development identity — where the crossing seed is born).** Now
`a + i₂ ≥ D′`; note `s = a + i₂ − D′ ≤ i₂ − 1 < D′` and `a + i₂ < 2D′`. The single
over-grid coefficient of the formal `E′Y^bK` is `E′P = g·x^{D′}` at `Y^{b+m−1}`. From
`x^{D′} = Φ′ + πω`:

```
A(CΦ₂) − E′Y^bK = g·(Y + πω − x^{D′})·Y^{b+m−1} = g·(Y − Φ′)·Y^{b+m−1} =: G ,
```

an identity in `O[x][Y]` (the left side's two extra slots `g·Y^{b+m}` and
`gπω·Y^{b+m−1}` are in-grid, so the left side IS the development). Hence

```
A(f) = K^{μ₂} + E′Y^bK + G .
```

**Step 2 (localizing Δ).** By LEMMA 1 (linearity + the base chain) and the honest
ledger `H₁ = C`: for every `j`, `Δ_j = red(chain_j(G))`. By LEMMA 2 applied to
`G = g·Y^{b+m} − Φ′·(g·Y^{b+m−1})`, the second half contributes nothing after `red`:

```
Δ_j = red( chain_j( g·Y^{b+m} ) ) .
```

Since `deg_Y(gY^{b+m}) = b + m ≤ 2m − 1`, one division by `K` leaves a quotient `q` of
`Y`-degree `b < m`; the chain is therefore `chain₀ = r`, `chain₁ = q`, `chain_j = 0`
for `j ≥ 2` — proving the `Δ_j = 0` clause for `2 ≤ j < μ₂` — where
`g·Y^{b+m} = q·K + r` is THE monic division.

**Step 3 (the division census — one telescoping display).** Claim:

```
q = Σ_{k=0}^{b} (−1)^k g P^k Y^{b−k}
r = (−1)^{b+1} g P^{b+1} Y^{m−1} + Σ_{k=0}^{b} (−1)^{k+1} g P^k c₀ Y^{b−k} .
```

*Verification.* `q·K = Σ_k (−1)^k gP^k Y^{b+m−k} + Σ_k (−1)^k gP^{k+1} Y^{b+m−1−k}
+ Σ_k (−1)^k gP^k c₀ Y^{b−k}`. Reindexing the middle sum by `l = k + 1` turns it into
`−Σ_{l=1}^{b+1} (−1)^l gP^l Y^{b+m−l}`; against the first sum everything cancels except
the `k = 0` head and the `l = b+1` tail:
`q·K = g·Y^{b+m} + (−1)^b gP^{b+1}Y^{m−1} + Σ_k (−1)^k gP^k c₀ Y^{b−k}`,
whence `g·Y^{b+m} − q·K = r` as displayed. `deg_Y r ≤ m − 1` (as `b ≤ m − 1`), so by
uniqueness of monic division these ARE the quotient and remainder. ∎

**Step 4 (slots, heights, collisions).** Each displayed term is a single monomial;
`red` keeps it a single monomial: `gP^k = cĉ₂^{k+1}π^{α+(k+1)v₂}x^{s+ki₂}` reduces to
value `±cĉ₂^{k+1}ω^{w_k}π^{α+(k+1)v₂+w_k}` at slot `((s+ki₂) − D′w_k,\ ·)` with
`w_k := ⌊(s+ki₂)/D′⌋`. Heights, using `u₂ = D′v₂ + i₂` (F3) and
`D′v₂ + s = a + u₂ − D′ = a + δ` (F4):

* `Δ₁`, slot `k` at `Y^{b−k}`:
  `ht = D′(α+(k+1)v₂+w_k) + (s+ki₂−D′w_k) + (b−k)u₂ = D′α + (D′v₂+s) + k·u₂ + (b−k)u₂
  = D′α + a + bu₂ + δ = H_C + δ` — the same for every `k`.
* `Δ₀`, `c₀`-family slot `k`: the extra factor `c₀ = ĉ₀π^{v₀}` adds `D′v₀ = E₂` (F3):
  `ht = H_C + δ + E₂`, every `k`.
* `Δ₀`, the `P`-chain deposit at `Y^{m−1}`: `ht = D′α + (D′v₂+s) + (b+1)u₂ + (m−1)u₂
  = H_C + δ + E₂` as well.

*Non-collision.* Within `Δ₁` the slots have pairwise distinct `Y`-powers `b−k`: no
collisions, all `b+1` slots are unit-times-`π`-power, nonzero, at height exactly
`H_C + δ`. Within `Δ₀` the `c₀`-family likewise; the `P`-chain deposit can collide only
with the family's `k = 0` slot and only when `b = m − 1` — and THEN it always does:
its `x`-power is `(s + mi₂) mod D′ = s` because `D′ ∣ mi₂` (from
`D′v₀ = mu₂ = mD′v₂ + mi₂`, (F3)). The two deposits there are the `k = 0` value
`−gc₀` and the `P`-chain value `(−1)^{b+1}gP^{b+1} = (−1)^m gP^m`, which reduces to
`(−1)^m g ĉ₂^m ω^{mi₂/D′} π^{v₀}` (its `π`-power is `mv₂ + mi₂/D′ = v₀`, again (F3));
the merged slot value is `g π^{v₀}((−1)^m ĉ₂^m ω^{mi₂/D′} − ĉ₀)`, of height
`≥ H_C + E₂ + δ`, with equality iff `p ∤ ((−1)^m ĉ₂^m ω^{mi₂/D′} − ĉ₀)`. (At W1 this
unit-difference is `−1 − 1 = −2`: the height jumps by exactly `D′` at `p = 2` —
measured, tooth T-EW-COLLIDE.) At `b = m − 1 ≥ 1` the slots `k = 1, …, b` are
untouched, single, nonzero, at height exactly `H_C + E₂ + δ`; at `b < m − 1` every
slot is. In all cases `Δ₀ ≠ 0` and `Δ₁ ≠ 0`.

**Step 5 (pins).** `pin(Δ₁) = H_C + δ` and `pin(Δ₀) = H_C + E₂ + δ` (all slots at the
displayed heights; the one possibly-degraded slot only rises). Against the floors:
`Θ₁ + ε = (μ₂−1)E₂ + δ + H_C − (μ₂−1)E₂ = H_C + δ` and
`Θ₀ + ε = μ₂E₂ + δ + H_C − (μ₂−1)E₂ = H_C + E₂ + δ`. ∎ **(Theorem proved.)**

---

## §4. Corollaries (each with its machine leg)

**C1 (tightness — T-E-BOUND is a theorem).** The proof never used a sign on `ε`; at an
ON-side entry (`ε = 0`) the pins are `Θ_j` exactly. The Θ-floor is tight; the
witness-infeasibility below is the locus fence, not slack. [Machine: EW-TIGHT, 40
boundary rows, every frame with an integral boundary.]

**C2 (witness infeasibility — HYP.71(b), now for the FULL in-budget locus at μ₂ = 2).**
Let `f = Φ₂² + C₁Φ₂ + C₀` (`deg C_{j′} < D₂`) be any member whose development slots all
sit strictly above their sides: every nonzero slot `(a, b)` of `C_{j′}` of value `λ` has
`D′v(λ) + a + bu₂ ≥ (2−j′)E₂ + 1`. By linearity of the honest ledger, `A(·)`, the chain
(LEMMA 1), and `red`, `Δ_j(f)` is the sum over the slots of `C₁, C₀` of the
single-entry discrepancies. Slots of `C₀` and non-crossing slots of `C₁` contribute `0`
(clause (a)); each crossing slot contributes a slot vector supported at heights
`≥ Θ_j + ε_i ≥ Θ_j + 1`. Sums cannot lower heights (equal-slot values add, so
valuations only rise; distinct slots are untouched): `mindiff_j ≥ Θ_j + 1` at every
coordinate, or `Δ_j` is empty. **No in-locus member attains the Θ-floor** — OM-10's
E-INFEAS, proved, and now for arbitrarily many entries (the sweep certified one and
two). [Machine: E-INFEAS 54-row sweep min gap 1 (OM-10); EW-MERGE; EW-2SLOT.]

**C3 (single-crossing membership classification — HYP.78's surface at μ₂ = 2).** For a
member as in C2: if no slot of `C₁` crosses, the shadow is faithful (`Δ = 0`
everywhere). If EXACTLY ONE slot of `C₁` crosses, `Δ_j ≠ 0` at both coordinates with
`mindiff_j = Θ_j + ε` of that slot. (Two crossing coefficients at the SAME `(a,b)` are
one slot — their coefficients merge before the theorem applies; E-LIN's measured
deepening is the theorem at the merged valuation.) If several distinct slots cross with
pairwise DISTINCT excesses, the discrepancy is the dict-sum and
`mindiff_j = Θ_j + min ε_i`, exactly (distinct heights cannot cancel). **The
above-floor membership classification is COMPLETE at this geography except for
equal-excess multi-crossing ties** — the census hard-unit's obstruction, previously
localized by OM-10 to multi-crossing geographies, is now localized to equal-excess
ties. [Machine: 281 crossing + 1465 non-crossing rows; EW-MERGE; EW-2SLOT.]

**C4 (unit-independence — E-S4).** The pins depend on the entry only through
`(j′, a, b, α)`; the unit `c` multiplies every slot value. [Machine: E-S4 (OM-10) +
the dict formulas.]

---

## §5. Scope honesty and consumption map

**Proved scope.** (F1)–(F5) frames; members with entries at `j′ ∈ {0, 1}`; route E
(route R by LEMMA 0). At `μ₂ = 2` this is the full member grid, hence the full OM-10
LEG E surface. In particular:

* **HYP.71(b) — REFUTED(+repair), the refutation leg now PROVED.** The infeasibility
  record (no in-locus Θ-attainment at the all-in-grid W-geography) is COROLLARY C2; the
  tightness tooth is C1. The dated repair (re-scope GENTOW-3(iv)-sharpness to
  certificate-carrying geographies) now stands on a proved base. Conjunct (a)
  (genre-general nonvanishing) is UNTOUCHED; HYP.112's fence untouched.
* **HYP.78 — the single-crossing classification now PROVED** (C3), with the open case
  narrowed: multi-crossing with equal excesses (the free-digit-mixing ties), plus
  everything below (μ₂ ≥ 3 entries at `j′ ≥ 2`, and non-trinomial keys).

**Open beyond this note (named, with the measured boundary where one exists).**
1. **`j′ ≥ 2` entries (live only at `μ₂ ≥ 3`).** The wrap then spawns a SECOND seed
   (`E′P²` also over-grid), and the naive per-coordinate law genuinely FAILS at `p = 2`:
   the battery's measure-only leg found `pin = Θ_j + ε + D′` (one grade high) at
   exactly the `(a, b) = (3, 0)`, `j = j′ = 2` rows of the `V1p2m3` frame — the
   `2·q_G` cross-term loses its grade at `p = 2` — while all 92 `p = 3` reads agree
   with `Θ + ε`. A `j′ ≥ 2` law must carry the two-seed interference term; this is a
   CONSTRUCTED refutation of the naive extension, kept.
2. **Non-trinomial keys** (extra constant entries): the `Δ₁` census survives verbatim
   (the telescoping display gains more families), but the `Δ₀` collision analysis needs
   the general path census; equal-height path collisions can cancel. Open.
3. **Equal-excess multi-crossing ties** (C3's residue). Open — the census hard-unit.
4. **`f₁ ≥ 2`, `h ≥ 2`, or `e₂ ≥ 2` level-1 frames**: `Φ′` is then not a binomial and
   `red`'s monomial form fails; the crossing entry off `t₂ = m−1` re-opens `e₂` (§0
   remark). Open.
5. **LAW B-S2** (the P-BINOM cascade pair-or-triple law, OM-10 §2.2) is NOT proved by
   this note; it concerns the pure power's own reads at a different geography and
   remains CERTIFIED-OPEN (7/7).

**Fences.** No sealed display is edited. Nothing here consumes `[GENTOW5-W]`, the
WELD-ZERO arc, or HYP.112's candidate fence (the theorem produces non-attainment, not
candidates). Statement-fence: this note adds a proof; it weakens nothing.

---

## §6. Certification record

* `verification/openmath/om10_cert.py` LEG E (OM-10, committed): the pin law 54/54
  crossing reads at W1/W2, E-NOX/E-INFEAS/E-LIN/E-S4, teeth T-E-BOUND, T-E-CHI.
* `verification/openmath/ewbs2_lawew_cert.py` → `ewbs2_lawew_output.txt` (this unit):
  **GREEN, 2796 checks, 0 violations, 5/5 teeth killed** (script md5 `9a61aa63…`,
  output md5 `b0d77b83…`). Composition: EW-Q/EW-R 281+281 crossing rows with the §3
  closed-form dicts BIT-EXACT (the proof's Step 3/Step 4 displays, checked before the
  proof was written); EW-NOX 1465 (clause (a)); EW-PIN 522 + EW-TIGHT 40 (Step 5 + C1);
  EW-HI 39 (`Δ_{≥2} = 0`); EW-PURE 11 + DUAL 11 (§2, LEMMA 0); EW-MERGE, EW-2SLOT (C3);
  EW3-FLOOR 138 + the `j′ = 2` measured tables (§5 item 1). Frames: W1, W2, W5o
  (`p = 5`, `ω = 2`, non-1 units), V1p2/V1p3 (+`μ₂ = 3` variants), V2p2/V2p3
  (`i₂ = 2`, `s ∈ {0,1}`), V3p2/V3p3. Teeth: T-EW-DELTA (margin-forgotten pin law),
  T-EW-J0 (`j′`-blind crossing predicate), T-EW-SIGN (sign-stripped census),
  T-EW-WRAP (`ω`-stripped reduction), T-EW-COLLIDE (the `b = m−1` collision is seen,
  with its measured valuation jump at W1).
