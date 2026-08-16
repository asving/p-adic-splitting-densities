# Chapter-H closing chain after AMENDMENT A-H.6 — H.30b, H.121d LANDED; H.121c, H.122 BLOCKED

**Date.** 2026-08-16. **Unit.** Chapter-H closing chain (H.30b → H.121d → H.121 clause (iii)
→ H.122), all four re-signed the same day by A-H.6.

**Verdict.**

| node | status | commit / reason |
|---|---|---|
| **H.30b** `alpha_geom_partial_le_third` | **LANDED** | `4152ab95`, in `ChapH/H30.lean` |
| **H.121d** `beta_content_census` | **LANDED** | `0c9da12c`, new `ChapH/H121d.lean` |
| **H.121 (iii)** `uCluster_beta_leg` | **BLOCKED** | RESCHEDULE: needs **H.116b** (`betaExtract_fiber_card`) |
| **H.122** `uClusterNorm_rateSpecies` | **BLOCKED** | downstream of (iii); `m = 2` leg already landed (`H122m2.lean`) |

Neither blocked node was weakened; no stand-in, no new axiom, no statement touched. Both
landed nodes are byte-identical to their A-H.6 stubs in `leanspec/Leanspec/ChapH.lean`, are
`sorry`-free and print only `propext, Classical.choice, Quot.sound`. The A-H.6 oracle
`verification/AH6_beta_envelope_check.py` was re-run at landing: **54/54, exit 0**.

---

## 1. H.30b — landed as signed, and its constant is tight

`Σ_{k<n} (Q−1)·Q^(−c(k+1)) ≤ 1/3` for `2 ≤ Q`, `2 ≤ c`. H.30's proof skeleton with the
one-step inequality strengthened from `(Q−1)r ≤ 1 − r` to `(Q−1)r ≤ (1/3)(1 − r)`, i.e. to
`3(Q−1) ≤ Q^c − 1`; under `Q^c ≥ Q²` that is `(Q−1)(Q−2) ≥ 0`, the only place `2 ≤ c` is used.
Equality at `(Q,c) = (2,2)`, so `1/3` cannot be lowered `Q`-uniformly. H.30 stays live (its
`1` is the true value at `c = 1`, the `m = 2` slope). Battery leg `E1`.

## 2. H.121d — landed, but by a DIFFERENT route than A-H.6 §5 sketched

A-H.6 §5's PROOF field prices the census by the exhaustive β polygon classification at
`m = 3` (shapes A/B/C with their digit counts, closed value `Q/(Q²+Q+1) ≤ 2/7`). The landed
proof does **not** use the case list — it needs no polygon API at all. What it uses is the
child event's own divisibility clauses, on the three coefficient digits:

* write `W := π^k·w` for the centre (any lift `w` of `z`; `HasChildAt` is ∀-over-lifts, which
  is what lets ONE `w` serve a whole `(k,z)` cell); the recentring factors as
  `b_j = π^(jk)·t_j` with `t₂ = a₂+3W`, `t₁ = a₁+2a₂W+3W²`, `t₀ = a₀+a₁W+a₂W²+W³`;
* at `m = 3` the child multiplicity is `μ = 2` (H.118 `betaChild_mult_lt` + H.109 `2 ≤ μ`), so
  the event says `v(t₂) = D − 2k` EXACTLY, `π^(D+1−k) ∣ t₁`, `π^(D+1) ∣ t₀`;
* **the structural constraint `D ≥ 2k+1`** comes from the same clause: `a₂ ∈ 𝔪` and `π ∣ W`
  give `v(b₂) ≥ 2k+1`, while `π^(D+1) ∤ b₂` gives `v(b₂) ≤ D`. This single inequality is
  what the polygon case list was needed for;
* the three conditions are TRIANGULAR, so `c ↦ (t₂,t₁,t₀)` is injective into
  `exactSet(D−2k) × dvdSet(D+1−k) × dvdSet(D+1)`, and ChapG **G.14**'s counts
  (`card_dvdSet`, `card_exactSet_add`) give the cell
  `(Q−1)·Q^(3(N−1))·Q^(3k)·Q^(−3D)`;
* summing over the `Q−1` centres and over `1 ≤ k`, `2k+1 ≤ D`, weighted by `Q^D`:
  `Σ (Q−1)²Q^(3k)Q^(−2D) = 1/(Q+1) ≤ 1/3`.

**Certified constant `1/(Q+1)`, sharp constant `Q/(Q²+Q+1)`** — consistent (`sharp ≤ crude`),
and the crude one is TIGHT at `Q = 2`, where it equals the signed `1/3` exactly. Both `Q−1`
factors are load-bearing: relaxing the centre count to `Q`, or the exact-valuation count on
the top digit to mere divisibility, each gives `Q/(Q²−1) = 2/3 > 1/3` at `Q = 2`. Recorded in
the file's §6 gate.

**For the next amendment:** H.121d's blueprint PROOF field can be replaced by the four bullets
above (shorter, and it drops the H.112 (i)-transported uniqueness of `k(c)` from the DEPENDS —
the landed statement quantifies the content existentially, so uniqueness is not consumed).

## 3. H.121 clause (iii) — BLOCKED: needs H.116b, and H.121d does not substitute

Re-signed statement (A-H.6 §2.4, `uCluster_beta_leg`):

```
(Nat.card {c : ClusterState O m N // IsBetaState π c ∧ ClusterUndecided O π m N c} : ℝ)
  ≤ (1/3) * N * Q^(m*(N-1)) * (Q^(N-1))⁻¹
```

`betaExtract_fiber_card` (H.116b) is **still not landed** — `H116bR.lean` carries the peel
(`exists_peel`), the frame-congruence transport (`hasChildAt_iff_of_frame_congr`) and the
planted-factor profiles, but not the fibre COUNT; no declaration of that name exists anywhere
in the corpus (checked at this commit).

**Why the landed pieces do not close it.** The obstruction is sharper than "a step is
missing", and it is worth recording because the census route looks like it should help:

* H.121d prices the β census with **no `N`-decay at all** — summed over every `(k, D)` the β
  cell count is a CONSTANT fraction of `Q^(m(N−1))` (that is exactly what makes the census
  bound `1/3` rather than something shrinking). Clause (iii) needs the factor `Q^(−(N−1))`.
* The whole decay is carried by the CHILD's rate `û₂(M) ≤ M·Q^(−(M−1))` (landed, unconditional:
  `H122m2.uClusterNorm_rateSpecies_two` with the tie `uCluster_two_eq_uTwo`). Transferring it
  to the parent needs the count of β∧undecided states in a cell to be `≤ (cell size) · û₂(M)`
  — i.e. the fibres of `c ↦ (its child state)` must be equicardinal (or at least uniformly
  bounded by the average). That IS `betaExtract_fiber_card`. H.63's `prod_sub_prod_le_sum`
  consumes the fibration's output (`F_g` cancels against `#(genre g)` only once `F_g` exists);
  it cannot produce it.
* The triangular digit parametrization of H.121d does not give the fibre count either: the
  child state is the degree-2 factor obtained by the PEEL, and `H116bR.lean`'s own finding
  (certification D3, refuted with witnesses) records that the naive presentation-stability
  argument for injectivity of the replant is FALSE in same-slope multi-child genres. So the
  fibre count is genuinely the missing theorem, not a bookkeeping step.

**RESCHEDULE: needs H.116b.**

**Residual assembly once H.116b lands** (everything else is now in place, so this should be
one sitting): at `m = 2` the bucket is empty (`H122m2.not_isBetaState_two`, or H.118 inline);
at `m = 3` partition by `(k, z)` and content `D` exactly as `H121d.card_bucket_le` does
(that lemma's `hsub`/`biUnion` skeleton is reusable verbatim), replace its per-cell digit
count by [fibre count] × `û₂(N − D)` via H.63, apply the child rate `û₂(M) ≤ M·Q^(−(M−1))`
with `M = N − D` and `M ≤ N`, then close with **H.121d** — the resulting sum is
`N·Q^(−(N−1))·Σ_β Q^(betaContent) ≤ (1/3)·N·Q^(m(N−1))·Q^(−(N−1))`, which is the re-signed
envelope on the nose (A-H.6 §3 steps 4–6).

## 4. H.122 — BLOCKED downstream, with the route otherwise clear

Statement byte-unchanged: `RateSpecies (residueCard O) 1 1 1 (uClusterNorm O π m)` at
`2 ≤ m ≤ 3`. The `m = 2` leg is LANDED and unconditional (`H122m2.lean`). The `m = 3` leg
needs the three-way split H.121 (i) with **clause (iii)** for the β cell, so it inherits §3's
blocker. Every OTHER input is now landed:

* head: H.113 `card_drainState`, exact;
* α: H.121b `uCluster_alpha_leg` (equality, windowed range) + the induction hypothesis +
  **H.30b** at `clusterC 3 = 3 ≥ 2` (landed today);
* the closing arithmetic `1 + (N−3)⁺/3 + N/3 ≤ N` is battery leg `E2` (`2 ≤ N < 400`), and
  `E4` checks the conclusion on the true recursion.

⚠ **The E3 fence stands** (A-H.6 §4): do NOT attempt one uniform `2 ≤ m ≤ 3` induction through
clause (iii). At `m = 2` the α factor is H.30 at `clusterC 2 = 1`, where `Σ = 1` is TIGHT, and
`1 + (N−2) + N/3 ≤ N` fails from `N = 4`. The `m = 2` leg must go through the EMPTY β bucket.

⚠ `rate_close` (H.71) remains REFUTED as a route to `(1,1,1)` (A-H.6 §4); PA-H17.1 is not a
prerequisite. Nothing in this unit changes either finding.
