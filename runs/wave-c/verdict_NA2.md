# UNIT NA2 — VERDICT: **LANDED, SORRY-FREE** (NA22 finisher, 2026-08-31)

**Charge:** route step (d) at n = 2 — the first diagonal assembly.
**File:** `leanfinal/Uniformity/ChapI/IFCG68.lean` (~810 lines, registered in
`Uniformity/ChapI.lean` after IFCG67).
**Verification:** `lake env lean Uniformity/ChapI/IFCG68.lean` exit 0, zero
errors/warnings; grep sorry = 0; **all 23 AxCheck footer rows PURE Lean core
`[propext, Classical.choice, Quot.sound]`** — no sorryAx, no B.42/C.33/AX_cellRecursion.

## Provenance

The predecessor NA2 hung during a name-check batch, leaving a green-modulo-sorries
skeleton (§0 kit + §1 trichotomy proved; 16 open sorries). NA22 took over, filled all
16 one increment at a time (per-increment LSP verify), and landed the unit. No
statement was changed; two private helper lemmas were added
(`filter_not_irreducible_eq`, `disjoint_split_dbl`, extracted from the inert-count
proof for reuse in the census star) and one private recursion-step lemma
(`primo_two_step`).

## What is now proved (all uniform in q and the window N; no division anywhere)

1. **§2 genre counts** over any finite field K, q := #K: `card_dblVecs` (#double = q),
   `two_mul_card_splitVecs` (2·#split = q²−q, by the exact 2:1 fiber count of
   (a,b) ↦ ![ab, −(a+b)] over the off-diagonal), `two_mul_card_inertVecs`
   (2·#inert = q²−q, by complementation in the trichotomy partition of the q²
   monic quadratics).
2. **§3 per-shape census values** (`primo`-normalized, IFCG65/IFCG63 consumed):
   linear `(δ,e)=(1,1)`, double `(1,2)`, inert `(2,1)` — all instances of
   `card_stratumDepthSet_pow`; split = the binary convolution
   `card_stratumDepthSet_mul` collapsed termwise (`q^{j+1}·q^{v−j+1} = q^{v+2}`) to
   `(v+1)(q−1)²·q^{2(2N−1)}`.
3. **§4 ★★ `two_mul_card_redDepthPairSet_two`** — THE n = 2 DIAGONAL CENSUS, CLOSED:
   `2·#redDepthPairSet(2,N,v)·q^{v+2} = duo(q,v)·q^{2(2N−1)}` for v < N, with
   `duo q v := 2q·primo(q,1,2,v) + (q²−q)·((v+1)(q−1)² + primo(q,2,1,v))`,
   assembled over IFCG63's shape partition + the three §2 counts. Plus
   `primo_two_closed`: `primo(q,1,2,v) = [2∣v](q²−q) + ⌈v/2⌉(q−1)²`.
4. **§5 ★★★ `zcURLim_redDiag_two`** — the reduced diagonal density ZcURLim at n = 2,
   OUTRIGHT: witness `(duoNum v, C 2·X^{v+4})`, eventually constant from window
   M ≥ v+1 by the §4 census. Through IFCG61's transport:
   **`zcURLim_depthDensity_two_two` (the (2,2) depth-density ZcURLim, UNCONDITIONAL)**
   and `zcURLim_depthDensity_two_right` (every (2,n₂), n₂ ≥ 2) — the first diagonal
   firing beyond min = 1.
5. **§6 regression vs IGV**: all five rows v = 0..4 proved as exact ℚ-identities —
   `duo q v = 2q^{v+4}·P_v` with P_v the battery-verified Z₂(t) coefficients
   (1−s), s(1−s)², (1−s)s²(2−s), 2(1−s)²s³, (1−s)s⁴(3−2s) at s = 1/q. The assembly
   and the independently derived generating function agree exactly.

## The named remainder (general n) — §7 docstring, NOT consumed by n = 2

(1) the n-ary coprime convolution (list induction over the landed binary step);
(2) the type grouping over factorization types λ ⊢ n with multiset counts in IFCG19's
necklace values I_δ(q); (3) the per-type primo convolution and the general
`zed_n`-census + ZcURLim, exactly as §5. All finite-field combinatorics at level 1;
IGV's Z_m(t) supplies the per-n regression battery.

## Notes for the record

- Numeric spot-checks at q = 2 (duo = 16, 8, 24, 16, 32 for v = 0..4) matched the
  §6 statements before proving; the file's statements were internally consistent as
  inherited — no skeleton statement needed repair.
- Instance hygiene: the Census section mirrors §2's
  `attribute [local instance] Classical.propDecidable` (instead of the `classical`
  tactic) so filter/union instance TERMS match across sections — this made the
  census-star assembly compile first try.
- omega atomizes nonlinear subterms but cannot relate k·B to (k+1)·B; the
  `primo_two_closed` and census endgames pre-distribute with explicit
  `hdiv`/`add_mul` rewrites before omega/ring.
