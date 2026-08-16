# LAW B-S2 — the P-BINOM cascade pair-or-triple attainment law, PROVED at the D′ = 2 cascade geography — 2026-08-16, unit C.128

**Provenance.** OM-10 LEG B (unit note `docs/openmath-campaign/OM-10_n8-boxes_2026-08-16.md`
§2.2; battery `verification/openmath/om10_cert.py` B-LAW) certified, 7/7 frames at two
primes (B3/B4/B5 at `q = 2`, BP3–BP6 at `q = 3`, BP3 reproducing the GENTOW6_PROOF r1
bracket record bit-exactly), the law

> at the cascade geography (`e₂(f₂ − t*) = 1`, the `t*`-entry carrying x-power exactly 1),
> the pure power `Φ₂^{μ₂}` attains its top-coordinate floor iff `p ∤ binom(μ₂,2)` OR
> `p ∤ binom(μ₂,3)` — the PAIR and TRIPLE slots are the only floor carriers,

with the naive "any in-band k-diagonal" candidate REFUTED at B4 (`binom(4,4) = 1` a unit
yet `pin = Θ + 1`). NODE C.128 (blueprint A-C.4) signed it as a LAW CANDIDATE and named
its expected proof route "C.127's census one Φ₂-division deeper". This note is that
census. Every display below was certified BEFORE this note was composed — the exact
top-coordinate slot dictionary, bit-exact on 47 binomial-key frames at `μ₂ = 2..9`,
`p ∈ {2,3,5}`, `h ∈ {1,3}`, `ω ∈ {1,2}`, unit/sign sweeps, plus 6 non-binomial (`κ₁ ≠ 0`)
frames with the refined display bit-exact — strictly beyond OM-10's sweep
(`verification/openmath/bs2_lawbs2_cert.py`, GREEN 666/0, 6/6 teeth; §9).

**Status: THEOREM (proved below) at the scope of §0 — `D′ = 2`, `f₂ = 2`, which contains
the ENTIRE certified surface.** What it converts: HYP.79's cascade half and NODE C.128
move CERTIFIED → PROVED at this geography. What it does NOT prove, it refutes or fences:
the leanspec stub `lawBS2_pair_or_triple` AS STATED (which leaves `D′` and `f₂` free) is
**REFUTED on two constructed axes** (`D′ = 4`: empty top band; `D′ = 3`: the merged digit
is unit-dependent — §7), and the `f₂ ≥ 3, D′ = 2` slice stays measured-open (§7.3). The
required stub narrowing is flagged in §8 — flagged, not executed.

---

## §0. Frame class, instrument, statement

Throughout, `O` is a complete DVR with uniformizer `π`, residue characteristic `p` (mixed
or equal characteristic), and `v = v_π`. An integer `n` is a unit of `O` iff `p ∤ n`. The
certified frames are `O = ℤ_p`, `π = p`.

**Frame hypotheses (the D′ = 2 cascade geography).** Fix `h ≥ 1` odd, `v₂ ≥ 1`,
`μ₂ ≥ 2`, units `ω, ĉ₂, ĉ₀ ∈ O^×`, and `κ₁ ∈ O` with:

* **(G1)** `Φ′ = x² + κ₁x − π^hω` — the level-1 key: `D′ = e₁ = 2`, `f₁ = 1`, `h` odd
  (= `Coprime h e₁`), one-sided of slope `h/2`, which is exactly `v(κ₁) ≥ (h+1)/2`.
  The BINOMIAL subclass is `κ₁ = 0` (all previously certified frames).
* **(G2)** `Φ₂ = Φ′² + P·Φ′ + c₀` with `P = ĉ₂π^{v₂}x` and `c₀ = ĉ₀π^{v₀}` — the level-2
  key (`e₂ = 1`, `m := f₂ = 2`, `t* = 1`), the `t*`-entry carrying x-power exactly 1
  (`slotIdx(u₂) = 1`, i.e. `i₂ = 1`).
* **(G3)** on-side: `u₂ := 2v₂ + h` and `v₀ = u₂` (both entries sit ON the level-2 side
  of height `E₂ := 2u₂`). *These are not extra hypotheses at the Lean carrier:
  `composedKey T` (C.43) builds every entry as the `stageLiftO` monomial at exactly the
  on-side height, and at `D′ = 2` the x-freeness of `c₀` is automatic
  (`slotIdx(2u₂) = 0` since `2u₂ ≡ 0` and `h` is odd), as is `v₀ = u₂`.*
* **(G4)** `δ := u₂ − 2h ≥ 1` (the frame margin `T.margin`; automatic from `T.hfloor`).

Write `ee := e₁e₂ = 2`; the top coordinate is `j* := μ₂ − 1`, which is the leanspec
stub's `(μ₂ − 2) + (2e₂t* + 1)/(e₂f₂) = (μ₂ − 2) + 3/2 = μ₂ − 1` (ℕ-division; machine:
BS2-STUBJ, 47 frames). Floors: `Θ_j := (μ₂ − j)E₂ + δ`; in particular
`Θ_{j*} = E₂ + δ = 3u₂ − 2h`.

**The instrument (verbatim `om10_cert.py :: Frame`, route E; = LAWEW_PROOF §0 at
`D′ = m = 2`).** Slots `(a′, b′)`, `0 ≤ a′ < 2`, `0 ≤ b′ < 2`; the height of a nonzero
value `λ` at slot `(a′, b′)` is `ht := ee·v(λ) + a′·e₂h + b′u₂ = 2v(λ) + a′h + b′u₂`; the
**pin** of a slot vector is the min height over its nonzero slots. `dev` is the Φ′-adic
development; `red(z)` the remainder of `z` mod `Φ′`; `A(Y) ∈ O[x][Y]` the full Φ′-adic
development of `f` read as a `Y`-polynomial (`A(Φ′) = f`, `deg_x` coefficients `< 2`,
monic top); `K(Y) := Y² + PY + c₀`; the **chain** of `A` is the unique
`A = Σ_{j≤μ₂} R_j(Y)K(Y)^j` with `deg_Y R_j < 2` for `j < μ₂`, `R_{μ₂} = 1` (iterated
monic division). Shadow coordinate `j` is `red(R_j)` slotwise. Since the honest ledger of
the pure power is `H_{μ₂} = 1`, `H_j = 0` (`j < μ₂`), the discrepancy at `j < μ₂` is

```
Δ_j = red( R_j( A(Φ₂^{μ₂}) ) ) .
```

`TouchCert T hπ μ₂ j` (C.74) is exactly `pin(Δ_j) = Θ_j` (the instrument's
`dv2Hgt(shadowDev − dev) = theta`, with `dv2Hgt(0) = ⊤ ≠ Θ_j` when `Δ_j` is empty).

> **THEOREM (LAW B-S2 at the D′ = 2 cascade geography).** Under (G1)–(G4), for every
> `μ₂ ≥ 2`, writing `b_k := binom(μ₂, k)` (`= 0` for `k > μ₂`) and
> `M := b₃ − (μ₂ − 1)b₂`:
>
> **(i) The exact top census.** `Δ_{μ₂−1}` is supported on at most three slots, with the
> EXACT values
>
> ```
> (0,1) ↦ b₂·ĉ₂²·π^{2v₂}
> (1,0) ↦ M·ĉ₂³·π^{3v₂}
> (0,0) ↦ b₄·ĉ₂⁴·π^{4v₂} − κ₁·b₃·ĉ₂³·π^{3v₂}
> ```
>
> (a slot is absent iff its displayed value is `0`; at the binomial subclass `κ₁ = 0`
> the `(0,0)` slot is the pure quad digit, present iff `μ₂ ≥ 4`).
>
> **(ii) Heights (of each PRESENT slot).** Whenever the respective displayed value is
> nonzero — automatic for `(0,1)` and `(1,0)` in mixed characteristic (`b₂ ≠ 0 ≠ M` in
> `ℤ` for `μ₂ ≥ 2`); in equal characteristic `p ∣ digit` makes the slot ABSENT instead,
> with the same verdict in (iii) — `ht(0,1) = Θ_{j*} + ee·v(b₂)`,
> `ht(1,0) = Θ_{j*} + ee·v(M)`, and `ht(0,0) ≥ Θ_{j*} + min(δ, 2v(κ₁) − h) ≥ Θ_{j*} + 1`:
> a present `(0,0)` slot NEVER touches the floor (and an absent one a fortiori).
>
> **(iii) The law.** `pin(Δ_{μ₂−1}) = Θ_{j*}` ⟺ `p ∤ b₂ ∨ p ∤ M` ⟺
> `p ∤ binom(μ₂,2) ∨ p ∤ binom(μ₂,3)` — i.e. `TouchCert T hπ μ₂ (μ₂−1)` iff the
> pair-or-triple right-hand side.
>
> **(iv) Floors.** At every coordinate `j < μ₂`, every slot of `Δ_j` has height
> `≥ Θ_j` (GENTOW-3(i) at this geography, self-contained).

The certified sweeps sit inside this class: OM-10's B/BP are (G1)–(G4) at
`(h, v₂, ĉ₂, ĉ₀, κ₁) = (1, 1, −1, −1, 0)`, `p ∈ {2, 3}`, `μ₂ ≤ 6`.

*Remark (why the mixed digit may be read as `b₃`).* The `(1,0)` value is NOT the triple
digit alone: it is the triple deposit PLUS the pair's quotient cross-term (§4), merged as
the integer `M = b₃ − (μ₂−1)b₂` (closed form `6M = μ₂(μ₂−1)(1−2μ₂)`; machine: BS2-SWAP,
tooth T-BS2-MIX — at BP3 the naive `b₃`-digit reads `−27`, the measured value is `135`).
But in the VERDICT `M` is interchangeable with `b₃`: if `p ∣ b₂` then `M ≡ b₃ (mod p)`,
which is §5's congruence swap and the reason OM-10's table read off the (correct)
pair-or-triple form.

---

## §1. Preliminary lemmas

LEMMAS 0–2 are LAWEW_PROOF_2026-08-16.md §1, used verbatim (their statements do not
consume the in-grid hypothesis (F5), which FAILS here — the pure power is over-grid, that
is the whole point). LEMMA 0 (route agreement: route R = `red`(route E) slotwise;
measured here as 61 DUAL checks). LEMMA 1 (chain linearity in the dividend, over `O[x]`).
LEMMA 2 (every chain coordinate of `Φ′·M` is `Φ′·(chain coordinate of M)`, hence dies
under `red`). On the Lean side the corresponding API is landed at
`leanfinal/Uniformity/ChapC/C127.lean` (`devQ_add`, `devQ_mul_pow`, `devQ_eq_zero_of_lt`,
`biRead_eval_eq_map`).

**LEMMA 3 (the weight grading).** Assign to a monomial `λx^aY^b` (`λ ∈ O`) the weight
`wt := ee·v(λ) + a·e₂h + b·u₂ = 2v(λ) + ah + bu₂`, and to a sum of monomials the min of
the weights (finite or `⊤`). Then:

* **(3a)** `K` is weight-homogeneous of weight `E₂ = 2u₂`: `wt(Y²) = 2u₂`,
  `wt(PY) = (2v₂ + h) + u₂ = 2u₂` by (G3), `wt(c₀) = 2u₂` by (G3).
* **(3b)** monic division by `K` respects the grading: if `V = qK + r` then
  `wt(q) ≥ wt(V) − E₂` and `wt(r) ≥ wt(V)`; hence `wt(R_j(V)) ≥ wt(V) − jE₂` for every
  chain coordinate. *Proof.* Each division step subtracts `c·Y^{d−2}·K` where `c` is the
  current top coefficient; by induction every intermediate dividend has weight `≥ wt(V)`
  (the subtrahend's monomials have weight `≥ wt(cY^{d−2}) + E₂ = wt(cY^d) ≥ wt(V)` by
  (3a)), and every quotient deposit `cY^{d−2}` has weight `≥ wt(V) − E₂`. Iterate. ∎
* **(3c)** `red` never lowers weight: on the reduced locus it is the identity; one
  reduction step replaces `x²` by `π^hω − κ₁x`, with `wt(π^hω) = 2h = wt(x²)` and
  `wt(κ₁x) = 2v(κ₁) + h ≥ 2h + 1` by (G1). ∎
* **(3d)** for a reduced slot vector, `pin = wt` (each slot is a monomial and the pin is
  the min of exactly the monomial weights). ∎

**LEMMA 4 (the top-band chain of a monomial).** For the trinomial `K = Y² + PY + c₀`
(any `P, c₀ ∈ O[x]`, μ₂ ≥ 2):

* **(4a)** `R_{μ₂−1}(x^aY^N) = 0` for `N < 2μ₂ − 2` (the `(μ₂−1)`-th iterated quotient
  of a degree-`N` polynomial has `Y`-degree `N − 2(μ₂−1) < 0`, i.e. is `0`). ∎
* **(4b)** `R_{μ₂−1}(Y^{2μ₂−2}) = 1`. *Proof.* `Y² = K − (PY + c₀)`, so
  `Y^{2μ₂−2} = Σ_{t} binom(μ₂−1,t)(−1)^{μ₂−1−t}K^t(PY+c₀)^{μ₂−1−t}`. Chain coordinates
  peel `K`-powers exactly (`R_j(K^tW) = R_{j−t}(W)` for `j ≥ t`, `= 0` for `j < t`, by
  uniqueness of the exact divisions), so the `t`-term contributes
  `R_{s}((PY+c₀)^{s})` at `s := μ₂−1−t`, which vanishes for `s ≥ 1` by (4a)-type degree
  counting (`deg_Y = s < 2s`). Only `t = μ₂−1` survives: `R_0(1) = 1`. ∎
* **(4c)** `R_{μ₂−1}(Y^{2μ₂−1}) = Y − (μ₂−1)P`. *Proof.* Multiply the display in (4b)
  by `Y`; now the `t`-term carries `Y(PY+c₀)^s` of degree `s + 1`, vanishing at
  coordinate `s` unless `s ≤ 1`. `s = 0` gives `Y`; `s = 1` gives
  `−(μ₂−1)·R_1(PY² + c₀Y)` and `PY² + c₀Y = P·K + (c₀ − P²)Y − Pc₀`, whose chain-1
  coordinate is `P`. Total: `Y − (μ₂−1)P`. ∎

---

## §2. The development identity — the wrap-seed sum

Expand the pure power multinomially, as an identity in `O[x][Y]`:

```
K(Y)^{μ₂} = Σ_{k+l+r=μ₂} C(μ₂; k,l,r) · P^l c₀^r · Y^{2k+l},      P^l c₀^r = ĉ₂^l ĉ₀^r π^{lv₂+rv₀} x^l .
```

A coefficient is over-grid iff `l ≥ 2` (`D′ = 2`). Develop each over-grid `x^l` by
iterating `x² = Φ′ + π^hω − κ₁x`: writing `l = 2w + ρ` (`ρ ∈ {0,1}`), at the binomial
subclass this is exactly `x^l = x^ρ Σ_{j=0}^{w} binom(w,j)(π^hω)^{w−j}Φ′^j`; at `κ₁ ≠ 0`
each `κ₁`-branch consumes one x-power without producing a `Φ′`, so the `Φ′`-count of any
branch is still `≤ ⌊l/2⌋` and each `κ₁`-use raises weight by `2v(κ₁) − h ≥ 1` (3c).
Summing the developed terms gives a `Y`-polynomial `A` with in-grid coefficients, monic
of degree `2μ₂`, with `A(Φ′) = Φ₂^{μ₂}`; by uniqueness of the development, `A` IS
`A(Φ₂^{μ₂})`, and

```
A(Φ₂^{μ₂}) = K^{μ₂} + T,     T ≡ T̂  (mod Φ′·O[x][Y]),
```

where the **seed sum** `T̂` collects, per over-grid term and per `Φ′`-depth `j ≥ 1`, the
monomial `(coefficient)·x^{ρ'}·Y^{2k+l+j}` — the `Y^{i+j} − Φ′^jY^i` halves of the wrap,
the `Φ′`-multiple halves being discarded into the congruence. At the binomial subclass:

```
T̂ = Σ_{l≥2} Σ_{j=1}^{w} C(μ₂;k,l,r) binom(w,j) ĉ₂^lĉ₀^r ω^{w−j} π^{lv₂+rv₀+h(w−j)} x^ρ Y^{2k+l+j} .
```

By LEMMA 1 (chain linearity), `R_j(K^{μ₂}) = 0` for `j < μ₂`, and LEMMA 2 (the
`Φ′`-multiple half dies under `red`):

```
Δ_j = red( R_j( T̂ ) )      for every j < μ₂ .
```

This is C.127's Step 1–Step 2 mechanism run on the pure power itself — the seeds are
born from the power's own diagonals instead of an entry, and there are μ₂-many divisions
instead of one.

---

## §3. The weight calculus — wrap depth is graded layer

Compute the weight (LEMMA 3) of the depth-`j` seed of the `(k,l,r)` term at the binomial
subclass, using (G3) twice (`2v₂ = u₂ − h`, `v₀ = u₂`) and `l = 2w + ρ`:

```
wt = 2[lv₂ + rv₀ + h(w−j)] + ρh + (2k+l+j)u₂
   = (2μ₂ + j)u₂ − 2jh + ee·v(integer coefficients)
   ≥ μ₂E₂ + j·δ .
```

**The wrap depth `j` sets the graded layer: depth-`j` seeds sit exactly `jδ` above the
pure power's own weight `μ₂E₂`, plus whatever the integer coefficients
`C(μ₂;k,l,r)·binom(w,j)` contribute.** At `κ₁ ≠ 0` every `κ₁`-decorated seed sits at
least one grade higher still (3c). Two consequences:

* **The floor (Theorem (iv)).** Every seed has `j ≥ 1`, hence weight `≥ μ₂E₂ + δ`; by
  (3b) every chain coordinate `R_j(T̂)` has weight `≥ μ₂E₂ + δ − jE₂ = Θ_j`; by (3c)+(3d)
  every slot of `Δ_j` has height `≥ Θ_j`. [Machine: BS2-FLOOR, 262 rows.]
* **The Θ-layer is depth-1 only.** Content at exactly the floor layer `μ₂E₂ + δ` can
  come only from depth-`1` seeds with UNIT integer coefficients and no `κ₁`-decoration —
  because `δ ≥ 1` and each `κ₁`-use costs `≥ 1`.

---

## §4. The top-coordinate census — exactly three branches

Which seeds have `R_{μ₂−1} ≠ 0`? By (4a), the seed's `Y`-power `N = 2k + l + j
= 2μ₂ − l − 2r + j` must be `≥ 2μ₂ − 2`, i.e. `j ≥ l + 2r − 2`, against `j ≤ w = ⌊l/2⌋`:

* `r ≥ 1` forces `j ≥ l > ⌊l/2⌋` — impossible. **No `c₀`-carrying diagonal reaches the
  top coordinate.**
* `r = 0` forces `⌈l/2⌉ ≤ 2`, i.e. `l ∈ {2, 3, 4}`:

| branch | `(k,l,r)` | depth `j` | seed (binomial subclass) | `N` | layer |
|---|---|---|---|---|---|
| PAIR | `(μ₂−2, 2, 0)` | `1` (= w) | `b₂ĉ₂²π^{2v₂}·Y^{2μ₂−1}` | `2μ₂−1` | `μ₂E₂ + δ` |
| TRIPLE | `(μ₂−3, 3, 0)` | `1` (= w) | `b₃ĉ₂³π^{3v₂}·x·Y^{2μ₂−2}` | `2μ₂−2` | `μ₂E₂ + δ` |
| QUAD | `(μ₂−4, 4, 0)` | `2` (= w) | `b₄ĉ₂⁴π^{4v₂}·Y^{2μ₂−2}` | `2μ₂−2` | `μ₂E₂ + 2δ` |

(The quad's depth-1 seed has `N = 2μ₂ − 3`: it does NOT reach the top coordinate. All
three surviving seeds have `binom(w,j) = 1` and `(π^hω)^{w−j} = 1` — the top census is
`ω`-FREE; tooth T-BS2-OMEGA.) At `κ₁ ≠ 0` the wrap developments of `x²`, `x³`, `x⁴` are,
exactly:

```
x² = Φ′ + (π^hω − κ₁x)
x³ = (x − κ₁)·Φ′ + ((π^hω + κ₁²)x − κ₁π^hω)
x⁴ = Φ′² + (2π^hω + κ₁² − 2κ₁x)·Φ′ + (in-grid)
```

so the ONLY `κ₁`-decorated top-band content is the triple's `−κ₁` (its depth-1
`Φ′`-coefficient is `x − κ₁`); the pair and quad top-band coefficients are exactly `1`;
`l ≥ 5` never reaches the top band even with `κ₁`-branches (the `Φ′`-count bound
`j ≤ ⌊l/2⌋` is `κ₁`-robust, §2).

Apply LEMMA 4 and `red` (identity here — every output below is already reduced):

* PAIR: `b₂ĉ₂²π^{2v₂}·(Y − (μ₂−1)P)` → slot `(0,1)` value `b₂ĉ₂²π^{2v₂}`, slot `(1,0)`
  value `−(μ₂−1)b₂ĉ₂³π^{3v₂}` (the quotient cross-term, `P = ĉ₂π^{v₂}x`).
* TRIPLE: `(x − κ₁)b₃ĉ₂³π^{3v₂}·1` → slot `(1,0)` value `+b₃ĉ₂³π^{3v₂}`, slot `(0,0)`
  value `−κ₁b₃ĉ₂³π^{3v₂}`.
* QUAD: `b₄ĉ₂⁴π^{4v₂}·1` → slot `(0,0)` value `b₄ĉ₂⁴π^{4v₂}`.

Merging the `(1,0)` deposits gives the integer digit `M = b₃ − (μ₂−1)b₂` — **Theorem (i)
is proved.** [Machine: BS2-DICT, 47 binomial frames bit-exact; BS2-TAUR, 6 `κ₁ ≠ 0`
frames bit-exact, e.g. T3m4's measured `(0,0) = −243 = 81 − 324
= b₄π⁴ − κ₁b₃π³` at `κ₁ = 3`.]

---

## §5. Heights, the law, and the congruence swap

Heights (Theorem (ii)), using `4v₂ + u₂ = 3u₂ − 2h = Θ_{j*}` and `6v₂ + h = Θ_{j*}`
(both are (G3)+(G4) arithmetic):

* `(0,1)`: `2(2v₂ + v(b₂)) + u₂ = Θ_{j*} + 2v(b₂)`;
* `(1,0)`: `2(3v₂ + v(M)) + h = Θ_{j*} + 2v(M)`;
* `(0,0)`: the value is the sum of TWO deposits, whose individual heights follow from
  the same arithmetic (`8v₂ = 4(u₂ − h) = Θ_{j*} + δ` and `6v₂ = 3(u₂ − h) = Θ_{j*} − h`):
  - the quad deposit `b₄ĉ₂⁴π^{4v₂}` at height `Θ_{j*} + δ + 2v(b₄)`,
  - the `κ₁`-triple deposit `−κ₁b₃ĉ₂³π^{3v₂}` at height `Θ_{j*} + (2v(κ₁) − h) + 2v(b₃)`;
  the slot height is the min of the two when their valuations differ, and only rises
  when they collide, so in all cases
  `ht(0,0) ≥ Θ_{j*} + min(δ + 2v(b₄), (2v(κ₁) − h) + 2v(b₃)) ≥ Θ_{j*} + min(δ, 2v(κ₁) − h)
  ≥ Θ_{j*} + 1`, using `δ ≥ 1` (G4) and `2v(κ₁) − h ≥ 1` (G1). ∎
  [Machine: binomial heights BS2-HT 124; `κ₁ ≠ 0` heights BS2-TAUH 6 — equality with
  the min on every row whose two deposit valuations DIFFER, and the `≥ Θ + 1` bound on
  the collision rows, where the height is `≥` the min and can strictly rise (measured:
  T3m4 and T3m5 both collide at common deposit valuation `4`; T3m4's merged
  `−243 = −3⁵` jumps a grade, T3m5's `−405 = −3⁴·5` stays at the min) — + BS2-TAUG
  (every non-floor slot `≥ Θ + 1`) + BS2-TAUR (the exact `(0,0)` value, from which the
  height is arithmetic).]

**The law (Theorem (iii)).** `pin(Δ_{μ₂−1}) = Θ_{j*}` iff some slot sits at exactly
`Θ_{j*}`; by (ii) only `(0,1)` and `(1,0)` can, and they do iff `v(b₂) = 0` resp.
`v(M) = 0`, i.e. iff `p ∤ b₂` resp. `p ∤ M` (an integer is a unit of `O` iff `p` does
not divide it — mixed AND equal characteristic; in equal characteristic `p ∣ n` makes
the digit vanish identically rather than merely deepen, with the same verdict). If both
die, every slot is `≥ Θ_{j*} + 1` — including `(0,0)`, by (ii), REGARDLESS of `b₄` —
or `Δ_{μ₂−1}` is empty; either way `pin ≠ Θ_{j*}`. [Machine: BS2-LAW, 53 frames.]

**The congruence swap.** If `p ∣ b₂` then `M = b₃ − (μ₂−1)b₂ ≡ b₃ (mod p)`; hence

```
p ∤ b₂  ∨  p ∤ M      ⟺      p ∤ b₂  ∨  p ∤ b₃ ,
```

(if `p ∤ b₂` both sides hold; if `p ∣ b₂` the second disjuncts agree). This is why the
measured law came out in the pair-or-triple form although the `(1,0)` slot's digit is
`M`, not `b₃`. **Theorem (iii) is proved; with §4 and §3, the THEOREM.** ∎
[Machine: BS2-SWAP — the closed form `6M = μ₂(μ₂−1)(1−2μ₂)` and the verdict equivalence,
`μ₂ ≤ 3000`, all `p ≤ 199`.]

---

## §6. The B4 refutation, EXPLAINED — where the k ≥ 4 branch loses the floor

The charge required the proof to explain, not avoid, the TEETH row: `binom(4,4) = 1` is
a unit, yet B4 measures `pin(ShC_3) = 8 = Θ + 1`.

The mechanism: to reach the top coordinate, the `l`-diagonal `b_l·P^l·Y^{2μ₂−l}` must
climb `l − 2` Y-powers (`l + 2r − 2` in general), and each wrap converts TWO x-powers
into ONE Y-power, so at most `⌊l/2⌋` climbs exist. The branch reaches the top band iff
`⌊l/2⌋ ≥ l − 2`, i.e. `l ≤ 4`:

* `l ≥ 5`: **never reaches** — no digit of the `k ≥ 5` diagonals appears at the top
  coordinate at ANY height (the census (i) has no trace of `b₅, b₆, …`; the dicts are
  bit-exact, so this is measured, not just unrefuted).
* `l = 4`: reaches ONLY at full depth `j = 2 = w`, hence (§3) at layer `μ₂E₂ + 2δ` —
  slot height `Θ_{j*} + δ + ee·v(b₄)`, at least `δ ≥ 1` above the floor EVEN WHEN
  `b₄` is a unit. The unitness of `binom(μ₂,4)` is real but irrelevant: the branch pays
  its floor-loss in WRAP DEPTH, not in digit valuation.

At B4 (`δ = 1`, `b₄ = 1`): the `(0,0)` slot value is `1·ĉ₂⁴·2⁴ = 16`, a unit digit at
height exactly `Θ + δ = 8` — which is exactly the measured `pin = 8 = Θ + 1`, since the
pair (`b₂ = 6`) and mixed (`M = −14`) digits are both even. The refutation value IS the
quad's depth-2 layer. [Machine: tooth T-BS2-QUAD — the refuted any-k mutant fails at B4,
B5, F5m6 while the B4 `(0,0)` slot is pinpointed as `16` at `Θ + δ`; tooth T-BS2-WDEPTH —
the depth-blind weight mutant predicts `pin(B4) = Θ` and is killed.]

*(The B4 refutation display from OM-10 §2.2 / NODE C.128's TEETH row is hereby preserved
verbatim in its consequence and given its mechanism; nothing is weakened.)*

---

## §7. The stub-gap: what the hypothesis set of `lawBS2_pair_or_triple` also admits

The leanspec stub (`leanspec/Leanspec/ChapC.lean :: lawBS2_pair_or_triple`) hypothesizes
`e₂(f₂ − t*) = 1`, `slotIdx((f₂−t*)u₂) = 1`, `f₁ = 1`, `μ₂ ≥ 3` — leaving `D′ = e₁` and
`f₂` FREE. The theorem above covers `e₁ = 2 ∧ f₂ = 2`. The rest of the hypothesis set is
NOT a proof gap; it is refuted or measured-open, as follows. (All frames below are
PARI-validated keys: `factorpadic` confirms the `(e, f)` invariants, so `hψirr` holds.)

**7.1 `D′ = 4` (frame P4: `Φ′ = x⁴ − 5` over `ℤ₅`, `Φ₂ = Φ′² + 5xΦ′ + 25x²`, PARI
`(4,2)`) — REFUTED, empty band.** All stub hypotheses hold (`slotIdx(u₂) = slotIdx(5)
= 1` at `e₁ = 4, h = 1`; `hfloor: 4 < 5`). At `D′ = 4` a wrap climbs 1 Y-power per FOUR
x-powers: the top-band condition `j ≥ l + 2r_x − 2` against `j ≤ ⌊x\text{-content}/4⌋`
has NO solutions — no seed reaches the top coordinate at all. Measured: `Δ_{j*} = ∅` at
`μ₂ = 3, 4, 5`, so `TouchCert` is FALSE, while the stub's right-hand side is TRUE at
`μ₂ ∈ {3, 4}` (`5 ∤ binom(3,2) = 3`, `5 ∤ binom(4,3) = 4`). **The stub as stated is
false.** [Machine: BS2-STUBGAP, hard rows P4m3/P4m4.]

**7.2 `D′ = 3` (frames D3: `Φ′ = x³ − p`, `Φ₂ = Φ′² + pxΦ′ + ĉ₀p²x²`, PARI `(3,2)`) —
REFUTED, unit-dependent census.** At `D′ = 3` the PAIR diagonal is IN-GRID (`x² < x³`):
no pair seed exists. The same census method (over-grid = x-content `≥ 3`, noting `c₀`
carries `x²` since `slotIdx(2u₂) = 2`) yields exactly TWO depth-1 top-band seeds — the
triple diagonal and the `P·c₀` CROSS-diagonal — merging into the single slot

```
(0,0) ↦ (b₃·ĉ₂² + μ₂(μ₂−1)·ĉ₀)·ĉ₂·π^{3v₂} ,
```

certified bit-exact on three valid keys (D3m7's measured `9625 = (35 + 42)·5³` decodes
as `b₃(7) + 7·6`). This law is **unit-DEPENDENT** (`ĉ₀` enters the digit), while
pair-or-triple is unit-independent — so a unit choice killing the merged digit refutes
the stub. At `p = 13`, `μ₂ = 3`, `ĉ₀ = 2`: digit `= (1 + 12)·13³ = 13⁴` (dead, height
`12 > Θ = 9`), residual discriminant `−7 ≡ 6` a non-QR mod 13 (valid key, PARI `(3,2)`),
`b₂ = 3` a 13-unit (stub RHS TRUE). Measured: `TouchCert` FALSE. [Machine: BS2-STUBGAP,
hard row D3r13.] *Disclosed near-miss:* at `p = 5, μ₂ = 3` the digit-death congruence
`ĉ₂² + 6ĉ₀ ≡ 0` COINCIDES mod 5 with the residual degeneracy `ĉ₂² − 4ĉ₀ ≡ 0`, so `hψirr`
rescues the stub there (both attempted `ĉ₀ ∈ {4, −1}` gave PARI `(6,1)` — invalid keys;
kept in the battery's comments as the reason the refutation needed `p = 13`).

**7.3 `f₂ = 3` at `D′ = 2` (frame P32: `Φ′ = x² − 5`, `Φ₂ = Φ′³ + 5xΦ′² + 5⁴x`, PARI
`(2,3)`) — measured-open, structurally different.** Here `c₀` carries `x`
(`slotIdx(3u₂) = 1`), and the measured (frozen) top census has `Θ`-layer carriers the
`f₂ = 2` law does not have: at `μ₂ = 3`, carriers `{(0,0), (0,2)}` — the `(0,2)` slot
is the pair digit `75 = b₂·5²` one `Y`-power up, the `(0,0)` slot is a `P·c₀`-cross
family value `40625 = 5⁵·13`; at `μ₂ = 4`, FIVE slots with THREE carriers
`{(0,0), (0,2), (1,1)}` (`118750 = 2·5⁵·19`, `150 = b₂·5²`, `−1750 = −2·5³·7`). The
verdicts AGREE with pair-or-triple on the two probe rows (both attain, the pair digit
among the carriers); no refutation is claimed, and no proof either: the `f₂ ≥ 3` slice
is OPEN with a genuinely different Θ-layer census. [Machine: PROBE 5 — key validity,
the frozen dicts, and the carrier locations, hard-checked.]

---

## §8. Scope honesty, consumption map, and the flagged stub repair

**Proved scope.** (G1)–(G4), `μ₂ ≥ 2` — i.e. the stub's hypothesis set PLUS `F.e₁ = 2`
AND `T.f₂ = 2`, over any complete DVR, any one-sided degree-2 key (binomial or not), any
on-side units, any odd `h`. This contains the ENTIRE certified surface of LAW B-S2
(OM-10's 7 rows and this unit's 47 + 6 rows are all `e₁ = f₂ = 2`).

**Consumption map.**
* **NODE C.128**: law-candidate → **PROVED at the `e₁ = f₂ = 2` cascade geography**;
  the node's TEETH (the B4 refutation) EXPLAINED (§6), verbatim-preserved. The node
  statement's geography reading (`e₂(f₂ − t*) = 1` with `D′`, `f₂` free) is exactly the
  stub's, hence carries the same two refutation axes — the blueprint annotation records
  the narrowing with this note as source.
* **HYP.79 ARC**: the cascade half of the 2026-08-16 ARC NOTE moves CERTIFIED → PROVED
  (this note); the single-slot half (9/9) and the lower-coordinate rider are untouched.
* **The leanspec stub `lawBS2_pair_or_triple`** — FLAG ONLY (not executed, per the
  charge): the promotion path must ADD the hypotheses `he₁ : F.e₁ = 2` and
  `hf₂ : T.f₂ = 2` (every other binder verbatim; `hμ₂ : 3 ≤ μ₂` may stay although the
  proof covers `μ₂ = 2`; `hslot` stays — an x-free `t*`-entry makes the pure power
  in-grid and the shadow empty, refuting attainment trivially). WITHOUT the narrowing
  the axiom-stub is FALSE (§7.1, §7.2) — this is the same failure genre as C.127's
  landed scope-fence repair (the `j′ ≤ 1` hypothesis missing from `lawEW_faithful_of_nox`'s
  stub), caught here BEFORE transcription. A Lean proof of the narrowed statement can
  reuse C.127's landed `devQ` API for §§1–2, but §3's weight calculus needs the same
  missing `stageHeight`-of-a-monomial layer that blocks `lawEW_pin`
  (`leanfinal/notes/C127_PIN_BLOCKED_2026-08-16.md`) — the two nodes share their Lean
  bottleneck.

**Fences.** No sealed display is edited; the B4/B5 refutation record is preserved
verbatim; nothing here touches the single-slot law, HYP.78's residue, HYP.112, or the
WELD-ZERO arc. Statement-fence: this note adds a proof and two refutations of an
UNSIGNED-as-theorem axiom-stub's excess generality; the signed node statement is what
is proved, at its certified geography.

**Open beyond this note (named).**
1. `f₂ ≥ 3` at `e₁ = 2` (§7.3): the mixed `P·c₀` cross-families join the Θ-layer; a law
   there must carry the cross digits (`~ μ₂(μ₂−1)` and beyond). Measured, open.
2. `e₁ ≥ 3` cascade laws (§7.1–7.2): at `e₁ = 3` the census is the single merged
   unit-dependent digit above; at `e₁ ≥ 4` the top band is EMPTY and attainment needs
   entry-driven members (LAW E-W territory), not the pure power. Both are laws ABOUT
   different objects, not extensions of pair-or-triple.
3. Lower coordinates `j < μ₂ − 1` at `p ∣ binom` (HYP.79's rider): untouched.
4. The equal-excess multi-crossing ties and the other LAWEW §5 opens: untouched.

---

## §9. Certification record

* `verification/openmath/om10_cert.py` LEG B (OM-10, committed): B-LAW 7/7, B-FLOOR,
  B-TOP, teeth T-B-COEF, T-B-ALLM; the sealed anchors.
* `verification/openmath/bs2_lawbs2_cert.py` → `bs2_lawbs2_output.txt` (this unit):
  **GREEN, 666 checks, 0 violations, 6/6 teeth killed** (script md5 `dae0e27c…`, output
  md5 `59b479b2…`). Composition: BS2-ANCH 8 (om10 frame ties + BP3's sealed
  `{(0,1): 27, (1,0): 135}`); DUAL 61; BS2-STUBJ 47; BS2-FLOOR 262; **BS2-DICT 47**
  (the §4 dict bit-exact: B2–B8, BP2–BP9, F5m3–8, F5om3–5, H3m3–5 (`h = 3`,
  `Φ′ = x² − 8`), V2m3–4 (`v₂ = 2`), 18 unit-sweep frames — including BP9, F5m5, F5m6:
  the FIRST `p = 3` and `p = 5` non-attainment rows); BS2-HT 124 (binomial heights);
  BS2-LAW 53; BS2-SWAP 1 (integer grid `μ₂ ≤ 3000`, `p ≤ 199`); BS2-TAUG 18 +
  BS2-TAUR 12 + BS2-TAUH 6 (`κ₁ ≠ 0` frames T2m3–5, T3m3–5: Θ-layer graded-exact, the
  full refined dict bit-exact, and the `(0,0)` height min-formula — equality on the
  valuation-distinct rows, `≥ Θ + 1` on the collision rows per §5); BS2-STUBGAP 16
  (P4 + D3 axes, PARI-validated); PROBE 5 (P32: key validity + frozen dicts +
  Θ-carrier locations).
* Teeth: T-BS2-QUAD (the REFUTED any-k law fails at B4/B5/F5m6; B4's `(0,0)` pinpointed
  as unit `16` at `Θ+δ`), T-BS2-WDEPTH (depth-blind weight mutant), T-BS2-MIX (the
  naive-`b₃` digit, `−27` vs measured `135` at BP3), T-BS2-SIGN (`ĉ₂ ↦ −ĉ₂` flips
  `(1,0)`, fixes `(0,1)`/`(0,0)`), T-BS2-OMEGA (F5/F5o: top dicts equal, lower
  coordinate differs — the battery sees `ω`), T-BS2-TAU (the binomial dict fails
  bit-exactly at every `κ₁ ≠ 0` frame — the τ-tail is real and the refined display is
  needed).
