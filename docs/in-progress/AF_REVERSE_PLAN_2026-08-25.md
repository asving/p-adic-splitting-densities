# AF-REVERSE PLAN — `budget_of_mem_towerLocus` (NODE C.131af′) + `towerLocus_iff_budget` (C.131ag′)

**Author:** DECOMPOSER unit DEC2, 2026-08-25.
**Blocker converted:** `runs/wave-b/verdict_C131ae.md` §C.131af′ — "locus ⟹ budget floors
needs a reverse triangular-digit correspondence (C.53's `TriangularDigitRead`, pointwise
form) that nothing landed supplies."
**Elaboration check:** `leanfinal/scratch/DEC2_check.lean` — `lake env lean` exit 0, zero
errors, no `sorry`, no `axiom`. Every landed input below is pinned there at the exact type
this plan claims for it, and every planned signature elaborates (`SIG_AF*` Prop defs).

---

## 1. THE DESIGN DECISION: the pointwise TriangularDigitRead is SUPERSEDED

**Verdict: DERIVABLE.** No pointwise triangular/unipotent digit dictionary needs to be
built. The reverse direction decomposes into a WEAK part that C.131w′'s ledgers already
supply, plus a single STRICTNESS increment (`+1`) that is absorbed by comparing `f` against
the landed reference object `Φ₂^{μ₂} = composedKey T ^ μ₂` (C.131ac′'s
`composedKey_pow_mem_towerLocus`) at the residual level, using C.26's twenty-months-landed
residual teeth. Three observations make this work; all three are `rfl`- or
elaboration-checked in `DEC2_check.lean`:

1. **The carriers already coincide.** `dv2Hgt (T.levelDatum hπ) A = dvSupp F A T.u₂ T.e₂`
   by `rfl` (BRIDGE 1), and `dv2Pin (T.levelDatum hπ) (composedKey T) f j
   = dv2Hgt (T.levelDatum hπ) (dev (composedKey T) f j)` by `rfl` (BRIDGE 3). So C.131w′'s
   `dv2Hgt` kit (built for `shadow_floor`) speaks DIRECTLY about the C.51 locus's own
   level-one side data and about the two-key digits the budget clause reads. The
   C131ae-verdict's framing ("the shadow/census apparatus was built for the opposite
   direction") was about the SHADOW half; the two C131w LEDGERS
   (`towerLocus_entry_floor`, `dv2Hgt_dev_floor`) are direction-agnostic floors and are
   exactly the reverse transport, minus the `+1`.

2. **`budgetFloor` = weak floor + 1, exactly.** For `w := slotOffset T a b ≤ X := (μ₂−j)E₂`
   and `d := e₁e₂`: `budgetFloor = ⌈(X−w)/d⌉ + [d ∣ X−w] = ⌈(X+1−w)/d⌉`. So the whole
   budget clause is equivalent to the STRICT per-digit floor
   `(μ₂−j)E₂ + 1 ≤ dv2Hgt (dev Φ₂ f j)` — which is (BRIDGE 3) exactly C.54(c)'s node floor
   `towerLocus_node_floor`, strict form. Landed inputs give `(μ₂−j)E₂` (entry floor `μ₂E₂`
   pushed down the honest-digit ledger at cost `jE₂`); ONLY the `+1` is new content.

3. **The `+1` needs no digit dictionary — only a residual comparison.** The `+1` is where
   the residual pin (`dvResPoly f = towerLabel^μ₂`) must be consumed. Consume it by
   PERTURBATION, the same move C.131ae′ used in the forward direction: set
   `g := f − Φ₂^{μ₂}`. Both `f` and `Φ₂^{μ₂}` lie in `towerLocus T μ₂`
   (`composedKey_pow_mem_towerLocus`), hence have IDENTICAL side data: `dvSideMin = 0`,
   `dvSupp = μ₂E₂`, `dvSideDeg = μ₂f₂`, and — the pin — identical residual polynomials
   `towerLabel^μ₂`, hence identical ϖ-reads at EVERY lattice point of the side. Flat
   development digits subtract exactly (`dev` is `O`-linear: `C131v.dev_sub`,
   `dev_add_of_monic`), and ϖ-reads are additive at a common height floor
   (`C130rp2.twistRead_add_of_le`, GENERIC). So every on-line read of `g` is a difference
   of two equal reads = `0`. But C.26 (`natDegree_dvResPoly`, clause (iii)) says a
   polynomial whose side set is NONEMPTY has a NONZERO read at its left endpoint. Hence
   `g`'s side set at level `μ₂E₂` is empty: `dvSupp g ≥ μ₂E₂ + 1` STRICTLY. Then
   `dev Φ₂ f j = dev Φ₂ g j` for `j < μ₂` (`dev_sub` + `dev_pow_self` Kronecker), and
   `C131w.dv2Hgt_dev_floor` pushes `μ₂E₂+1` down to `(μ₂−j)E₂+1` at every digit. Done.

**Why this is faithful (not a weakening).** The signed statement (leanspec `ChapC.lean`
NODE C.52, `towerLocus_iff_budget`, line 2030) is untouched: the plan proves it
byte-identically (modulo `axiom → theorem`), with `mem_towerLocus_of_budget` (landed,
byte-frozen) as the `←` direction. The blueprint's "triangularity note" (CHAP-C
blueprint, NODE C.52 SIGNATURE block) was a note about HOW the raw digit coordinates were
chosen (`c_{j,a,b}` = x-coefficients of the two-key development) — that choice is already
frozen into the signed statement itself; no separate triangular READ theorem is signed
anywhere (C.53's landed replacement C53b uses measure transport for the COUNT, and the v2
engine doc §5 row C.131af′ explicitly forbids using it pointwise — this plan doesn't).
The perturbation route proves the same signed inequality about the same signed digits.
The mathematical content of the old TriangularDigitRead (base-ψ₂ uniqueness of the
residual assembly) is not skipped — it is absorbed into the pair (exact residual of the
reference `Φ₂^{μ₂}` [the C66b cite, entering exactly once, at the same Step-1 entry point
the forward direction already uses] + C.26's left-endpoint nonvanishing). A general
residual product law (`R(A·Φ₂^j) = R(A)·ψ₂^j` for non-pure `A`) is NEVER needed, because
we never decompose `f` digit-by-digit at the residual level — we compare it to a single
reference whose residual is already landed.

**Cite footprint (disclosed up front):** AF-3/AF-4/AF-6/AF-7 inherit the DECLARED cite
`fgmn_dv_exact_mul` (C66b, allowlist member 7) through `composedKey_pow_mem_towerLocus` —
the SAME single entry point as the landed forward direction. AF-1/AF-2/AF-5 are Lean-core.
No new axiom anywhere.

---

## 2. The route, exactly (what each unit proves)

Notation (re-bound): `Φ₂ := composedKey T`; `Φ′ := F.key`; `E₂ = e₂f₂u₂` (`rfl`);
`dv2Hgt (T.levelDatum hπ) = dvSupp F · T.u₂ T.e₂` (`rfl`);
`dvHgt F f i = F.stageHeight (dev Φ′ f i)` (`rfl`);
`wtCoeff T c a b = (e₁e₂) • addVal O c + slotOffset T a b` (`rfl`),
`slotOffset T a b = a·(e₂h) + b·u₂`.

```
locus data of f                         locus data of Φ₂^μ₂  (C131ac, CITE)
   │  AF-1: dvSideMin = 0, dvSupp = μ₂E₂,  dvSideDeg = μ₂f₂   (both members)
   │  AF-2: on-line left endpoint of any support-μ₂E₂ poly is e₂t₀, height μ₂f₂u₂ − t₀u₂
   ▼
AF-3a: reads of f and Φ₂^μ₂ agree at every lattice point  (residual pins, both = ψ₂^μ₂)
   ▼
AF-3:  dvSupp (f − Φ₂^μ₂) ≥ μ₂E₂ + 1      ← the +1; C26 nonzero-endpoint vs zero read
   ▼
AF-4:  dv2Hgt (dev Φ₂ f j) ≥ (μ₂−j)E₂ + 1  ∀ j < μ₂   ← dev_sub + dev_pow_self + C131w ledger
   ▼                                        (= C.54(c) node floor, STRICT — bonus consumer)
AF-6a: budget clause  ← flatten: C131t.dv2Hgt_eq_WT_phiNF → C131a.WT_le_wtCoeff
   │                     → xNF_coeff/xDigit_eq_dev → AF-5 ceiling arithmetic
   ▼
AF-6b: towerLocus_iff_budget := ⟨AF-6a, mem_towerLocus_of_budget⟩   (signed C.52, closed)
   ▼
AF-7:  s2 non-drain witness + C123R band-gap disposal (§4)
```

---

## 3. Unit plan (Sonnet-executable; each stage 30–45 min)

Five units, three files. Sequencing: U-SIDE ∥ U-ARITH first (independent), then U-HEART,
then U-ASSEMBLE, then U-FEED. Every unit: `cd leanfinal && lake env lean <file>` must exit
0 with zero errors; commit-worthy increments per the survival discipline; `#print axioms`
footer per file; do NOT touch `leanspec/`, roll-ups, or any other unit's file.

### U-SIDE — file `leanfinal/Uniformity/ChapC/C131af.lean` (stage 1), 40–45 min

Imports: `Uniformity.ChapC.C131ae`, `Uniformity.ChapC.C131w`, `Uniformity.ChapC.C130rp2`,
`Uniformity.ChapC.C26`, `Uniformity.ChapC.C35` (this exact list elaborates together —
DEC2_check.lean uses it). Helpers in `namespace Uniformity.Density.Tower.C131af`.

* **AF-1b `dvSideMin_eq_zero_of_isDvPure`** (SIG_AF1b): `IsDvPure F g u ℓ →
  dvSideMin F g u ℓ hne = 0`. Proof: `IsDvPure.1 : 0 ∈ dvSideSet`;
  `Finset.min'_le _ 0 h.1` + `Nat.le_zero`.
* **AF-1a `towerLocus_dvSupp_eq`** (SIG_AF1a): locus member ⟹
  `dvSupp F f T.u₂ T.e₂ = μ₂E₂` EXACTLY. Proof: destructure
  `hf = ⟨hmon, hdeg, hpure, hres⟩`. `≤`: the top abscissa `i := μ₂e₂f₂` has
  `dev Φ′ f i = 1` (`C131v.dev_top_eq_one F.hmonic F.natDegree_key_pos` with
  `hdeg` rearranged: `f.natDegree = (μ₂e₂f₂)·Φ′.natDegree` via `TowerDatum.D₂` +
  `F.hdeg : F.key.natDegree = F.e₁*F.f₁` — copy C131ae's `hXtop` block, lines 554–561,
  swapping `Φ₂^μ₂ ↦ f`), so `dvHgt f i = 0` (`C131ae.stageHeight_one`), and
  `Finset.inf_le (i ∈ range)` gives `dvSupp ≤ u₂·μ₂e₂f₂ = μ₂E₂` (`E₂` is `rfl`-equal
  to `e₂*f₂*u₂`; `push_cast; ring_nf`). `≥`: `C131w.towerLocus_entry_floor T hπ hf`
  (already states `μ₂E₂ ≤ dv2Hgt f`, `rfl`-equal to `dvSupp`).
* **AF-1c `towerLocus_dvHgt_zero_pin`** (SIG_AF1c): `dvHgt F f 0 = μ₂f₂u₂`. Proof: `0 ∈
  dvSideSet` (hpure.1) → `dvOnSide_of_mem_dvSideSet` (C35, public) →
  `dvSupp = e₂ • dvHgt f 0 + 0` → AF-1a → cancel the `e₂`-smul (case `dvHgt f 0`
  top/coe via `ENat.recTopCoe`; coe case `exact_mod_cast` + `Nat.eq_of_mul_eq_mul_left
  T.he₂`; top case contradicts finiteness). Write the smul-cancel as a private helper
  `le_of_nsmul_eq` — grep `C131p`/`C131r` first for an existing ℕ∞ utility.
* **AF-1d `towerLocus_dvSideDeg`** (SIG_AF1d): `dvSideDeg F f T.u₂ T.e₂ hne = μ₂f₂`.
  Proof: build the pin `hp : dvHgt f (dvSideMin f) = μ₂f₂u₂` by `rw [AF-1b hne]` then
  AF-1c; then `(natDegree_dvResPoly F hπ H₀ hpin T.he₂ T.hcop hne hp).1` +
  `hres hne _ hp : dvResPoly … = towerLabel^μ₂` + `Polynomial.natDegree_pow` over the
  stage FIELD (`towerLabel` monic & `natDegree = f₂` from `towerLabel_spec T hπ`;
  monic power degree: `Polynomial.Monic.natDegree_pow`).
* **AF-2a `dvSideSet_nonempty_of_dvSupp_eq_coe`** (SIG_AF2a): finite `dvSupp` is
  attained. Proof: `Finset.exists_mem_eq_inf (Finset.range (g.natDegree+1))
  ⟨0, mem_range…⟩ _` gives `i` with `dvSupp = e₂ • dvHgt g i + u₂i`; `dvHgt g i ≠ ⊤`
  (else RHS `= ⊤ ≠ coe`, using `0 < ℓ` so the smul of `⊤` is `⊤`); so
  `DvOnSide F g u ℓ i` holds and `i ∈ dvSideSet` by `Finset.mem_filter`.
* **AF-2b `towerLattice_solve`** (SIG_AF2b): if `dvSupp g = μ₂E₂` then
  `dvSideMin g = e₂t₀` with `t₀ ≤ μ₂f₂` and
  `dvHgt g (dvSideMin g) = μ₂f₂u₂ − t₀u₂`. Proof: `dvSideMin ∈ dvSideSet`
  (`Finset.min'_mem`) → `dvOnSide_of_mem_dvSideSet` → the equation
  `e₂ • H + u₂·s = μ₂E₂` with `H ≠ ⊤`; cast to ℕ; `e₂ ∣ u₂·s` (since `e₂ ∣ μ₂E₂` and
  `e₂ ∣ e₂·H`) + `T.hcop` (`Nat.Coprime.dvd_of_dvd_mul_left`) ⟹ `e₂ ∣ s`; solve `H` by
  omega after the substitution `s = e₂t₀` (`E₂ = e₂*f₂*u₂` by `rfl`).

Acceptance: file compiles, all six public, footprints Lean-core only
(`propext, Classical.choice, Quot.sound`) — NO cite in this stage.

### U-ARITH — file `leanfinal/Uniformity/ChapC/C131ag.lean` (stage 1), 30–40 min ∥ U-SIDE

Imports: `Uniformity.ChapC.C52` (budgetFloor), `Uniformity.ChapC.C131a` (wtCoeff), `Uniformity.ChapC.C50`
(slotOffset; check whether C52's closure already pulls it). Namespace
`Uniformity.Density.Tower.C131ag`.

* **AF-5a `budgetFloor_le_of_succ_le`** (SIG_AF5a, pure ℕ): `0 < d → X + 1 ≤ d*v + w →
  (if X < w then 0 else (X−w+d−1)/d + (if (X−w) % d == 0 then 1 else 0)) ≤ v`.
  Proof: `split_ifs`; trivial branch `Nat.zero_le`. Else `w ≤ X`; set `tgt := X − w`;
  from the hypothesis `tgt + 1 ≤ d*v` (omega). Decompose `tgt = d*q + r`
  (`Nat.div_add_mod`), rewrite `(tgt+d−1)/d` per branch: if `r = 0` (the `== 0` branch:
  `beq_iff_eq`) then `(d*q+d−1)/d = q` (`Nat.add_mul_div_left`-family or
  `Nat.mul_add_div`; prove `d*q + d − 1 = d*q + (d−1)` and use
  `Nat.add_div_right`… simplest: `Nat.div_eq_of_lt_le` with bounds `d*q ≤ d*q+d−1 <
  d*(q+1)`); goal `q + 1 ≤ v` from `d*q + 1 ≤ d*v` (`Nat.lt_of_mul_lt_mul_left` genre +
  omega). If `r ≠ 0`: `(d*q+r+d−1)/d = q+1` (`Nat.div_eq_of_lt_le`, bounds
  `d*(q+1) ≤ tgt+d−1 < d*(q+2)` — omega from `0 < r < d`); goal `q+1 ≤ v` from
  `d*q + r + 1 ≤ d*v` — `d*q < d*v` ⟹ `q < v` (`Nat.mul_lt_mul_left`). NOTE: `omega`
  cannot divide by the VARIABLE `d`; always pass through `Nat.div_eq_of_lt_le`.
  Template precedent: C131ae's private `budgetFloor_wtCoeff_bound` (same genre, reverse
  direction) — read it first.
* **AF-5b `budgetFloor_le_addVal_of_wtCoeff`** (SIG_AF5b, ℕ∞ wrapper):
  `(((μ₂−j)E₂ + 1 : ℕ) : ℕ∞) ≤ wtCoeff T c a b → (budgetFloor T μ₂ j a b : ℕ∞) ≤
  addVal O c`. Proof: `budgetFloor`'s body is DEC2_check BRIDGE 5 (`rfl` with
  `slotOffset`); `wtCoeff`'s body is BRIDGE 4. Case `addVal O c` top/coe
  (`ENat.recTopCoe`): top ⟹ `le_top`; coe `v` ⟹ cast the hypothesis to ℕ
  (`(e₁e₂)•(v:ℕ∞)` is `((e₁e₂*v : ℕ) : ℕ∞)` — `nsmul_eq_mul` + `Nat.cast_inj` genre)
  and finish by AF-5a with `d := F.e₁*T.e₂` (`0 < d` from `F.he₁`, `T.he₂`),
  `X := (μ₂−j)*T.E₂`, `w := slotOffset T a b`.

Acceptance: compiles, Lean-core footprints.

### U-HEART — extends `C131af.lean` (stage 2, after U-SIDE), ~45 min

* **AF-3a `towerLocus_read_eq`** (SIG_AF3a): two members `f, f'` of the same locus have
  equal ϖ-reads at every lattice point:
  `F.twistRead H₀ hpin (μ₂f₂u₂ − t₀u₂) (dev Φ′ f (e₂t₀)) = (same for f')`, `t₀ ≤ μ₂f₂`.
  Proof: for EACH member, build `hne := ⟨0, hpure.1⟩`, the pin `hp` as in AF-1d, then the
  residual pin `hres hne (μ₂f₂u₂) hp : dvResPoly … = towerLabel^μ₂`; extract coefficient
  `t₀` with the two-liner (proved verbatim in DEC2_check.lean §1.6, from
  `Uniformity.Hensel.coeff_sum_range_C_mul_X_pow`; needs `t₀ ≤ dvSideDeg` = AF-1d);
  rewrite `dvSideMin = 0` (AF-1b) and `0 + e₂*t₀ = e₂*t₀`, `ℓ*t = e₂*t₀`, `u*t = t₀*u₂`
  orientation per the check file's example. Both sides equal
  `(towerLabel T ^ μ₂).coeff t₀`; chain the equalities.
* **AF-3 `dvSupp_sub_composedKey_pow`** (SIG_AF3, ★ the heart):
  `((μ₂E₂ + 1 : ℕ) : ℕ∞) ≤ dvSupp F (f − Φ₂^μ₂) T.u₂ T.e₂` for `hμ₂ : 0 < μ₂`,
  `hf : f ∈ towerLocus T μ₂`, `hh`, `[Finite (ResidueField O)]`. Proof script:
  1. `hX := composedKey_pow_mem_towerLocus T hπ hh hμ₂` (CITE enters here, once).
  2. Weak floor: `dvSupp g ≥ min (dvSupp f) (dvSupp Φ₂^μ₂) = μ₂E₂` via
     `C131w.dv2Hgt_add_min` + `C131w.dv2Hgt_neg` on `g = f + (−Φ₂^μ₂)` (both suprema
     `= μ₂E₂` by AF-1a; the `rfl` bridge converts `dv2Hgt ↔ dvSupp` silently).
  3. `rcases lt_or_eq of the weak floor`: if strict, close with
     `exact_mod_cast Order.add_one_le_of_lt` (pinned in DEC2_check §1.7). If
     `dvSupp g = μ₂E₂`:
  4. `hne_g := dvSideSet_nonempty_of_dvSupp_eq_coe` (AF-2a);
     `⟨t₀, ht₀, hsmin, hM⟩ := towerLattice_solve` (AF-2b).
  5. Zero read: `dev Φ′ g s = dev Φ′ f s − dev Φ′ (Φ₂^μ₂) s` (`C131v.dev_sub F.hmonic`),
     so `dev Φ′ f s = dev Φ′ g s + dev Φ′ (Φ₂^μ₂) s` (`sub_add_cancel`). Apply
     `C130rp2.twistRead_add_of_le F hπ H₀ hpin` at `k := μ₂f₂u₂ − t₀u₂` — floors:
     `g`'s digit has EXACT height `k` (AF-2b's `hM`, `rfl`-bridge
     `dvHgt = stageHeight ∘ dev`, `le_of_eq`); `Φ₂^μ₂`'s digit clears `k` from
     AF-1a(`hX`) + `Finset.inf_le` (`s = e₂t₀ ≤ e₂·μ₂f₂ ≤ μ₂·D₂ = natDegree`, omega
     with `TowerDatum.D₂` unfolded; range membership `Finset.mem_range`) + the smul
     cancel helper. Then AF-3a (`f` vs `Φ₂^μ₂`, both in the locus) makes the two reads
     on the right-hand split cancel: `twistRead k (dev Φ′ g s) = 0`.
  6. Contradiction: `(natDegree_dvResPoly F hπ H₀ hpin T.he₂ T.hcop hne_g hM).2` — the
     constant coefficient of `dvResPoly g` is NONZERO — but by the extraction two-liner
     at `t = 0` (`Nat.zero_le`, `+ ℓ*0`/`− u*0` simp) it EQUALS
     `twistRead k (dev Φ′ g s) = 0`. `exact absurd … ` closes the branch.
* **AF-4 `towerLocus_dev_strict_floor`** (SIG_AF4, ★ = C.54(c) strict node floor), in
  root namespace `Uniformity.Density.Tower`: for `j < μ₂`,
  `(((μ₂−j)E₂ + 1 : ℕ) : ℕ∞) ≤ dv2Hgt (T.levelDatum hπ) (dev Φ₂ f j)`. Proof:
  `dev Φ₂ f j = dev Φ₂ g j` (`C131v.dev_sub` + `dev_pow_self (composedKey_monic T)
  hΦpos μ₂ j` with `if_neg (Nat.ne_of_lt hj)`, `sub_zero` — copy C131ae's `hgdig` block,
  lines 538–544; `hΦpos`: derive `0 < (composedKey T).natDegree` locally from
  `composedKey_natDegree T hπ` if `composedKey_natDegree_pos` turns out private —
  C131ae lists it among its private helpers, so re-derive: 3 lines). Then
  `C131w.dv2Hgt_dev_floor T hπ g.natDegree g le_rfl (AF-3) j` (applied shape pinned in
  DEC2_check §1.4) and the numeral `μ₂E₂ + 1 − jE₂ = (μ₂−j)E₂ + 1` (omega via
  `Nat.sub_mul`; `j < μ₂`).

Acceptance: compiles; `#print axioms` — AF-3a is Lean-core; AF-3/AF-4 carry EXACTLY
`fgmn_dv_exact_mul` on top of Lean-core (inherited via `composedKey_pow_mem_towerLocus`;
report it, it is the declared C66b cite, not a new axiom).

### U-ASSEMBLE — extends `C131ag.lean` (stage 2, after U-HEART + U-ARITH), 35–40 min

Add `import Uniformity.ChapC.C131af` (+ `C131t` if not already in closure). ★ nodes in
root namespace `Uniformity.Density.Tower`.

* **AF-6a `budget_of_mem_towerLocus`** (SIG_AF6a, ★ NODE C.131af′): chain, for given
  `j a b` with `hj : j < μ₂`:
  `AF-4` → rewrite through `C131t.dv2Hgt_eq_WT_phiNF T hπ (dev Φ₂ f j)` →
  `le_trans (…) (C131a.WT_le_wtCoeff T _ a b)` → rewrite the scalar via
  `C131k.xNF_coeff` + `C131k.xDigit_eq_dev` (DEC2_check §1.5: the flattened scalar IS
  `(dev F.key (dev (composedKey T) f j) b).coeff a`, the budget clause's own text) →
  `AF-5b`. The range hypotheses `a < e₁f₁`, `b < e₂f₂` are UNUSED (the floor holds for
  all `a b`) — keep the binders anyway (signed shape); silence with
  `set_option linter.unusedVariables false in` per C131w's precedent.
* **AF-6b `towerLocus_iff_budget`** (SIG_AF6b, ★ NODE C.131ag′ / signed C.52):
  `⟨fun hmem => budget_of_mem_towerLocus …, fun hbud => mem_towerLocus_of_budget T hπ hh
  hμ₂ hf hdeg hbud⟩`. Statement byte-mirrors leanspec `ChapC.lean:2030` (modulo
  `axiom → theorem` and any `IsLocalRing.ResidueField` qualification, per the C131w
  precedent). `hf`/`hdeg` binders are consumed by the `←` direction only.
* AxCheck footer for the whole file; expected: AF-5 Lean-core; AF-6a/6b Lean-core +
  `fgmn_dv_exact_mul`.

### U-FEED — file `leanfinal/Uniformity/ChapC/C123r2.lean` (after U-ASSEMBLE), 45–60 min

Imports: `Uniformity.ChapC.C131ag`, `Uniformity.ChapC.C123r` (for the s2/lin
instantiation pattern: `s2Tower h2 hq : TowerDatum (s2Frame h2 hq) 1 (s2Frame_pin h2 hq)`,
C80; read `C123r.lean`'s s2 section header for the exact `h2 hq` binders). Deliverables
(§4 for the mathematics):

* **AF-7a `s2_nondrain_mem`**: `f₀ := composedKey (s2Tower h2 hq) ^ 3 +
  Polynomial.C (π^6) * Polynomial.X * F.key` (i.e. `2^6·x·Φ′` over the s2 frame, where
  `π` is the frame's uniformizer — read it off `s2Frame`) lies in
  `towerLocus (s2Tower h2 hq) 3`, VIA `mem_towerLocus_of_budget`. The `hbud` rows:
  `dev Φ₂ f₀ 0 = C(π^6)·X·Φ′` and `dev Φ₂ f₀ j = 0` for `j = 1, 2`
  (`dev_add_of_monic` + `dev_pow_self` + `(modByMonic_eq_self_iff …).2` on the
  degree-3-below-4 remainder — the C131w:380 pattern); per-slot `addVal` numerals:
  `(a,b) = (1,1) ↦ addVal(π^6) = 6 = budgetFloor 3 0 1 1` (tgt `= 30−7 = 23`, `d = 4`,
  `⌈23/4⌉ = 6`, no pin), all other slots read coefficient `0 ↦ ⊤`. Use the landed s2
  numeral kit from `C123r.lean` (`s2_theta_row` genre) for `decide`/`norm_num`
  discipline; degree/monic side conditions: `natDegree f₀ = 12 = 3 * D₂`.
* **AF-7b `s2_nondrain_digit_height`**: `dv2Hgt … (dev Φ₂ f₀ 0) = (31 : ℕ∞)` — the
  witness digit is FINITE (non-drain) and sits at exactly
  `Θ_0 = 31 = (3−0)·E₂ + margin`. (Computation: flat digit `π^6·X` at abscissa 1;
  `stageHeight = 2·6 + 1 = 13`; `dvSupp = 2·13 + 5·1 = 31`.) This is the first landed
  locus member with a non-drain sub-top digit — C123R's missing witness, with `hbud`
  supplied by construction (disposing verdict_C123R.md's "no such f and no such hbud are
  landed" gap).
* **AF-7c `towerLocus_band_window_empty`** (SIG_AF7c, GENERAL — goes in `C131ag.lean` if
  U-ASSEMBLE prefers, else here): at any margin-1 tower, `f ∈ towerLocus T μ₂`, `j < μ₂`,
  `dv2Hgt (dev Φ₂ f j) = m` ⟹ `¬ m < T.theta μ₂ j`. Proof: AF-4 gives
  `m ≥ (μ₂−j)E₂ + 1 = (μ₂−j)E₂ + margin = Θ_j` (margin `= 1`); `omega`/cast. Then
  instantiate: **`s2_band_window_empty`**, **`lin_band_window_empty`** (both landed
  towers have `margin = 1`: `rfl`/`decide` check it).
* **AF-7d `s2_shadow_floor_live`**: `C131w.shadow_floor` + `C72`'s statement carrier
  fired at `f₀`, `j = 0` — the first instantiation where the honest digit is non-drain
  (finite height 31), so the floor row is live in the strongest sense available.

Acceptance: compiles; footprints Lean-core + `fgmn_dv_exact_mul` (via membership);
verdict must state the §4 finding verbatim (band emptiness is a FINDING, not a failure).

---

## 4. Feeding C123R's band-budget gap — and the honest finding

`verdict_C123R.md` left one gap: "a fully non-vacuous numeric BAND window row" needs a
locus member with non-drain digits below `μ₂`, plus a concrete `hbud`. This plan feeds it
twice over, and settles it:

1. **The witness exists** (AF-7a/b): `f₀ = Φ₂³ + π⁶xΦ′` at `s2Tower`, in the locus via
   `mem_towerLocus_of_budget` with an explicit finite `hbud`, digit height exactly 31.
   `shadow_floor` fires at it non-vacuously (AF-7d).
2. **But the BAND window itself is PROVABLY EMPTY at both landed towers** (AF-7c): the
   band hypothesis `hval : dv2Hgt (dev Φ₂ f j) = m` with `m < Θ_j = (μ₂−j)E₂ + δ` can
   never hold for a locus member when `δ = margin = 1`, because af′'s strict floor is
   `(μ₂−j)E₂ + 1 = Θ_j`. Both `s2Tower` and `linTower` have `margin = 1`
   (`u₂ − e₂·D′·h = 5 − 4 = 1` and `3·? …` — check numerically in-file). So C123R's
   "live `(j,m)` window" was not missing a witness: on the locus it does not exist at
   these towers. This upgrades C123r's kernel-checked drain disclosure to a theorem: at
   margin-1 towers, `shadow_faithful_band` is locus-vacuous. DEC2 checked the landed band
   statement (`C131y.lean:559`): it REQUIRES `hf : f ∈ towerLocus T μ₂`, so there is no
   off-locus escape — the ONLY route to a live band instance is a tower with
   `margin = u₂ − e₂·(e₁f₁)·h ≥ 2` (e.g. `(e₂,f₂,u₂) = (2,1,7)` at the s2 frame: margin
   `7 − 4 = 3`, `Θ_j = (μ₂−j)·14 + 3`, live window of width 2 per digit). Instantiating
   such a tower is a NEW unit (C.80-genre `TowerDatum` construction), booked as follow-on,
   not in this plan's scope. State this finding verbatim in the U-FEED verdict.

---

## 5. Elaboration-check record

`leanfinal/scratch/DEC2_check.lean` (this unit's second deliverable; `lake env lean` exit
0, no sorry, no axiom):

* Part 1 pins 30+ landed inputs at claimed types. Highlights: the five `rfl` BRIDGES
  (`dv2Hgt = dvSupp`, `dvHgt = stageHeight ∘ dev`, `dv2Pin = dv2Hgt ∘ dev`,
  `wtCoeff`-offset `= slotOffset`, `budgetFloor` body); the locus destructure + residual
  clause instantiation; `composedKey_pow_mem_towerLocus`; `C131w.dv2Hgt_dev_floor`
  APPLIED at `w := μ₂E₂+1`; the full flattening chain; `C130rp2.twistRead_add_of_le` /
  `twistRead_eq_zero_of_lt`; C26's `natDegree_dvResPoly` both clauses; **the
  residual-coefficient extraction two-liner PROVED outside C26.lean**; side-set
  attainment (`Finset.exists_mem_eq_inf`); the ℕ∞ `<`-to-`+1` cast; `dev_sub`,
  `dev_add_of_monic`, `dev_pow_self`, `dev_top_eq_one`, `stageHeight_one`; the
  TowerDatum field pins (`hcop`, `he₂`, `hf₂`, `E₂ = e₂f₂u₂` rfl, `one_le_margin`,
  `theta` body, `towerLabel` degree); `mem_towerLocus_of_budget` at its frozen binders.
* Part 2 elaborates all 13 planned signatures (`SIG_AF1a`–`SIG_AF7c`).

## 6. Standing rules for all units

No `sorry`, no new `axiom` (the ONLY non-core footprint permitted is the declared cite
`fgmn_dv_exact_mul`, inherited via `composedKey_pow_mem_towerLocus` — report per file).
Signed statements byte-frozen (AF-6b mirrors leanspec `ChapC.lean` NODE C.52). Do not
edit `leanspec/`, existing `Uniformity/` files, or roll-ups; each unit writes ONLY its
own file + its `runs/wave-b/verdict_*.md`. No `git commit` unless the campaign
orchestrator says so. If a proof step fails twice, trace the s2 numerals
(`Φ′ = x²−2, (e₁,f₁,h) = (2,1,1), (e₂,f₂,u₂) = (2,1,5), E₂ = 10`) before a third
abstract attempt.
