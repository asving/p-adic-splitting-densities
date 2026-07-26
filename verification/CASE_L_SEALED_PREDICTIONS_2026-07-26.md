# CASE L SEALED GATE — 3-move joint-history census (§C rev 6 content)

*(2026-07-26. SEALED BEFORE ANY CENSUS AT THIS CONFIGURATION. Charge: §C REV 6
RECORD, MOVES_2026-07-24.md — pin the rev-6 kernel's NEW empirical content:
(β)-strip fresh pins at an s₀ > 0 read, and address displacement of a digit
whose naive label is already pinned. Every number below is DERIVED from the
displayed rules in S1, arithmetic shown (the Case-K v1 lesson). The
configuration reuses the derivation note's instance B (C10B_DERIVATION S6.2):
its LABEL arithmetic is machine-checked and p-independent; the p = 2 DIGIT
data is fresh — no census at p = 2 has ever touched this history.)*

## S0. Config (p, n, the 3-move history)

p = 2 PRIMARY (p = 3 optional leg: S6-OPT), n = 9 (monic degree-9 f), N = 12
(max sealed pin level = 9; deepest probed content v_p 31/3 < 12). Census =
Monte-Carlo conditional on the root stratum: M ≥ 10⁶ members sampled uniformly
(pinned digits per the R₀ pattern, all deeper digits uniform), classified by
GENUINE division (Case-K machinery pattern, case_k_gate_v2_p3.py).

History H = (ν₀, ν₁, ν₂), the S6.2 instance-B shape:
- ν₀ ROOT READ (move 1; landing = increment). Frame 0, Φ₀ = x, D₀ = 1. Side
  [0,8], slope 1: (e₀,h₀,g₀,μ₀) = (1,1,2,4), ψ₀ = z²+z+1 (irreducible /F₂),
  residual R₀ = ψ₀⁴ = z⁸+z⁴+1. Key Φ̂₀ = x²+2x+4 (standard lift; verify the
  division sign against genuine division, per Case-K), D₁ = 2,
  F^(1) = F₄ = F₂[z̄], z̄² = z̄+1.
- ν₁ SECOND READ AT s₀ = 1 (move 2, THE β-PROBE; landing = increment).
  Frame-1 window = slots [0,4]. Side [1,4], slope 7/3:
  (e₁,h₁,g₁,μ₁) = (3,7,1,1); s₀'+w' = 4 = μ₀ — ADJACENT (γ empty; hinge
  inherited). I-aug: 7/3 > w(Φ̂₀) = 2 ✓. Cell label d := dig(B₁) ∈ F₄ˣ, the
  hull digit of the frame-1 slot-1 coefficient at v_p 7 (raw hull digit, not
  the residual coefficient — sidesteps D.8's normalization units; a fixed
  unit relabels cells, leaving masses and uniformity intact). D₂ = 6.
- ν₂ TAIL READ (move 3, recentering-species: e_read = 1, g = 1). Frame-2
  window = slots [0,1], vertex (1, v_p 7/3) inherited. Predicted emission:
  side [0,1] with slot-0 point at v_p 29/3 (stage 29 on the STR₂ = 3 scale),
  (e₂,h₂,g₂) = (1,22,1); cell label u := the slot-0 hull digit ∈ F₄ˣ. The
  D.10 recentering map itself is Case-K's already-gated territory; move 3 is
  probed at its READ (which is what §C's E_fresh(ν₂) consumes).

n = 9 justification: the β-probe needs s₀ ≥ 1 with e ≥ 2 at move 2 plus a
third read below it; instance B is the checked minimal such shape — reusing
it inherits the machine-verified label arithmetic (nothing smaller is on
record, and a new shape would need a fresh unfrozen derivation).

## S1. Displayed rules (the §C clauses + D.8/D.10 landing laws, quoted)

R1 (clause species; §C rev 6, C.1.0(b)(i)): "ν_{i+1}'s clause region is the
FULL current window Win_i ... anchored at 0: a hull-side read asserts (α)
span clauses on [s₀', s₀'+w'], AND (β) strictly-above-extended-line clauses
at slots < s₀', AND (γ) the same at slots in (s₀'+w', μ_i]."
R2 (freshness; §C rev 6, C.1(ii)): "(β)-strips (slots left of the side, the
strip (old line, extended new line]) are ALWAYS fresh"; "(γ)-strips are
fresh iff non-adjacent, up to the crossing slot j×"; "pin COUNTS are
D.11-nominal. NO claim is made about the base ADDRESS of a digit equation
whose naive line-staircase label is already pinned — such an equation
re-solves through the D.8 carries to a fresh ≺-later label, and C.2's
counting consumes only |pins| and freshness, never addresses."
R3 (the product; §C C.2 Theorem C(b)): #{f mod p^N ∈ S(H,Z)} =
p^{nN} · ∏_{i=0}^{k} vol(E_fresh(ν_i)) · vol(Z). Conditional form used
throughout: mass(cell | root stratum) = ∏_{i≥1} vol(E_fresh(ν_i)).
R4 (landing value structure; D.8 via S3.3): Λ(ν_i) places child points
strictly above the old line at slots j < μ (BOX), equality with pinned digit
at μ (VERTEX); within slots [0, μ_i) the old system asserts ZEROS only.
R5 (level/offset conversion; C.1.0(c) + the derivation's S6 recursion): a
clause at v_p height V at base index b pins level ℓ = V − off(b),
off(b) = Σ_r innerslot_r(b)·κ_r, κ_r = h_r/(e_r·STR_r). Here κ₀ = 1/(1·1)
= 1; κ₁ = 7/(3·1) = 7/3.
R6 (mass ⟺ count; PIN-WELLDEF/MOVE-INV, §C C.0.5 + derivation S2.3): pins
are determined by the locus; each fresh base pin contributes the factor
p^{−1} (an F₄-digit = 2 base pins = 2^{−2}); so every count prediction below
IS a mass prediction and conversely.
R7 (nominal counts; D.11): each read's fresh-pin count equals its nominal
count (strips + one residue-field digit per lattice slot read); a candidate
read whose available fresh labels cannot meet the nominal count is not
emitted (realizability — derivation S6.2 MORAL).

## S2. Per-cell predictions: P-count (C.2 product, α/β/γ species)

NODE 0 (the conditioning stratum, not census-measured). Line 8−b at base
index b: pins at (b, ℓ), ℓ = 0..8−b (zeros below the line, the R₀-pattern
digit (1,0,0,0,1,0,0,0,1) at ℓ = 8−b). |pins| = Σ_{b=0}^{8}(9−b) = 45;
vol(E(ν₀)) = 2^{−45}. Floor after ν₀: F₀(b) = 8−b.

NODE 1, species by species (all heights v_p; old(j) = 2(4−j) on frame-1
slots since w(Φ̂₀) = 2; new line L₁(j) = 7(4−j)/3, i.e. L₁ = (28/3, 7, 14/3,
7/3, 0) at j = 0..4; off within frame-1 blocks: off(2j)=0, off(2j+1)=κ₀=1):
- (β), slot 0 (< s₀ = 1): strip (old(0), L₁(0)] = (8, 28/3]. Base 0:
  ℓ ∈ (8, 9⅓] ∩ ℤ = {9}; base 1: ℓ+1 ∈ (8, 9⅓] ⟹ ℓ = {8}. TWO fresh zero
  pins {(0,9),(1,8)} — the rev-6 β content. Factor 2^{−2}.
- (α), slot 1 (lattice slot, left endpoint): strip (6,7) ∩ ℤ = ∅; the line
  digit at v_p 7 = one F₄-digit d ≠ 0 at nominal labels {(2,7),(3,6)}
  (7 − off: 7, 6). Factor 2^{−2}. Slots 2,3 (off-lattice, j−1 ≢ 0 mod 3):
  strips (4, 14/3] and (2, 7/3]: base 4: ℓ ∈ (4,4.67] = ∅; base 5:
  ℓ ∈ (3,3.67] = ∅; base 6: (2,2.33] = ∅; base 7: (1,1.33] = ∅. NO pins
  (this is why the α-strips vanish here). Slot 4 = μ₀ ADJACENT: the hinge is
  ν₀'s VERTEX — inherited, zero pins, one DATA identity (no f-equation).
- (γ): EMPTY (adjacent case, per R2).
E_fresh(ν₁) = 4 base pins ⟹ vol = 2^{−4} = 1/16.

NODE 2 (species): window [0,1]; s₀ = 0 ⟹ NO β; endpoint 1 = μ₁ ADJACENT ⟹
γ empty, hinge inherited. Fresh = the slot-0 digit only: strip empty (v_p
29/3 is the FIRST free rung — arithmetic in S4), one F₄-digit u ≠ 0 = 2 base
pins ⟹ vol(E_fresh(ν₂)) = 2^{−2} = 1/4.

SEALED P-COUNT PREDICTIONS (conditional on the root stratum; R3 product):
P1: each ν₁ cell d ∈ F₄ˣ has mass 1/16; three cells, d-uniform.
P2: total [1,4]-slope-7/3 emission = 3/16.
P3: joint 3-move cells (d, u) ∈ F₄ˣ × F₄ˣ: mass = 2^{−4}·2^{−2} = 1/64
    each; 9 cells, total 9/64; d ⫫ u. THE HEADLINE C.2 PRODUCT.
P4: frame-1 emission PARTITION (with S5's control family):
    P([0,4]-side) + P([1,4]-cells) + P(deeper) = 3/4 + 3/16 + 1/16 = 1.
DISCRIMINANT: the rev-4/5 inventory (no β pins) predicts P1-mass 1/4 —
the census separates 1/16 from 1/4 at 4σ with a few thousand samples.

## S3. P-β: β-strip pins, member-by-member

B1 (the strip, frame form): on EVERY member of every ν₁ cell (and of every
   deeper (d,u) cell): w(B₀) ≥ 10 v_p. [Derivation: β demands w(B₀) > 28/3;
   achievable values min(v(c₀), v(c₁)+1) ∈ ℤ; the least integer > 28/3 that
   node-0's floor admits beyond {9} is 10.] Member-by-member falsifiable.
B2 (the two pins, digit form): the F₄ hull digit of B₀ at v_p 9 (the pair of
   base digits at labels (0,9),(1,8), naive-exact: both labels unpinned in
   Π₀, floors 8 and 7) is ZERO on every cell member — that pair IS the two
   fresh β pins, existence member-by-member.
B3 (fresh-generic beyond the strip; C.2 free coordinates): within each ν₁
   cell, P(w(B₀) = 10 exactly) = 3/4, P(w(B₀) ≥ 11) = 1/4 (the next F₄ pair
   is FREE, uniform). Fractions, not member laws.
B4 (no phantom α content): on every ROOT-stratum member (β dead or alive):
   w(B₂) ≥ 5 and w(B₃) ≥ 3 v_p (BOX strictness + integrality) — the empty
   α-strips of S2 assert nothing new; any member of a ν₁ cell violating
   these would break D.8's landing, not just rev 6.

## S4. P-displacement: existence + nominal count, NO address prediction

RUNG ARITHMETIC (all derived from R5; frame-2 slot-0 block = bases [0,6),
b = 2j₁ + r ⟹ off(b) = j₁·κ₁ + r·κ₀ = j₁·(7/3) + r, i.e. off =
(0, 1, 7/3, 10/3, 14/3, 17/3); cumulative floor F₂(b) after Π₂ =
(9, 8, 7, 6, 4, 3); stages = 3·v_p on the STR₂ = 3 scale):
- THE NAIVE HEIGHT IS DEAD: content at slot-0 v_p 28/3 (stage 28, the naive
  next height) needs level ℓ = 28/3 − off(b) ∈ ℤ: b = 0,1,4,5 give 28/3,
  25/3, 14/3, 11/3 ∉ ℤ; b = 2,3 give ℓ = 7, 6 — EXACTLY the labels (2,7),
  (3,6) already VALUE-pinned by ν₁'s digit d. Zero free labels at stage 28
  vs nominal count 2 ⟹ by R7 the h₂ = 28 read is never emitted.
- FIRST FREE RUNG: v_p(rung at b) = (F₂(b)+1) + off(b) = (10, 10, 31/3,
  31/3, 29/3, 29/3) ⟹ stages (30, 30, 31, 31, 29, 29): minimum 29, via
  b ∈ {4,5} (frame-1 inner slot 2 — matching S6.2's checker verbatim).

SEALED PREDICTIONS:
PD0 (mass zero, the wrong-weight control): NO member of any ν₁ cell has its
  frame-2 slot-0 hull point at v_p 28/3. Corrected theory: mass EXACTLY 0.
  A naive line-staircase reading puts the d-realization there — i.e. would
  predict stage 28 on essentially EVERY cell member. Maximal discrimination.
PD1 (the emitted read): P(slot-0 hull point at v_p 29/3 | ν₁ cell) = 3/4,
  emitted as (e₂,h₂) = (1,22); u-cells u ∈ F₄ˣ mass 1/4 each, u ⫫ d.
PD2 (existence + nominal count of the displaced digit): on the 29-slice the
  fresh-pin count is EXACTLY 2 = one F₄-digit (D.11-nominal), witnessed as
  the mass 2^{−2} in PD1 via R6; and the naive labels (2,7),(3,6) are
  OCCUPIED — on every ν₁-cell member those two base digits are CONSTANT
  (= d's realization; census-checkable) and host no ν₂ content.
PD3 (NO ADDRESS SEALED — the counts-not-addresses discipline, R2): where the
  two displaced fresh coordinates sit is NOT predicted. [Non-binding remark:
  instance B's checker located them at {(4,5),(5,4)}; confirmation is
  welcome but NEITHER outcome falsifies this gate.]
PD4 (deeper slice): P(w ≥ next rung | ν₁ cell) = 1/4 total; the sub-ladder
  masses at stages 30, 31 are NOT sealed (outside the rev-6 obligation).
Absolute record (R3, Z = ∅): each (d,u) cell has absolute density
2^{−45}·2^{−4}·2^{−2} = 2^{−51} among monic degree-9 f — not measured (the
census conditions on the root stratum); N(H,∅) = 1 + 9 = 10 ≤ N = 12.

## S5. P-controls: wrong-weight, wrong-side

C-WS (wrong side, the s₀ = 0 sibling — the no-β family): members whose F₄
  pair at ((0,9),(1,8)) is ALIVE emit the side [0,4] of slope 9/4
  ((e,h,g) = (4,9,1); hull check: 9/4-line at slots 1,2,3 = 6.75, 4.5, 2.25,
  all strictly below the floors 7, 5, 3 — always a hull side when the pair
  is nonzero). Its C.2 product has NO β factor (s₀ = 0) and empty strips:
  ONE F₄ digit ⟹ mass 1/4 per cell u₀ ∈ F₄ˣ, total 3/4.
  THE RATIO EXHIBIT: mass([0,4] cell)/mass([1,4] cell) = (1/4)/(1/16) = 4 =
  2² = exactly the β-strip factor. DISJOINTNESS: no member emits [1,4] with
  w(B₀) = 9 (that would violate B1 — the wrong-weight β).
C-WW (wrong weight): PD0 above — the naive stage-28 emission has mass 0
  (naive theory: mass ≈ 1). One census hit at v_p 28/3 kills the gate.
CONSISTENCY: C-WS + P2 + the both-dead remainder must partition:
  3/4 + 3/16 + 1/16 = 1 (P4).

## S6. FALSIFIERS (any one ⟹ gate FAILS ⟹ §C rev 6's C.1.0(b)/C.1(ii)
inventory is wrong at p = 2)

EXACT-ZERO falsifiers (a SINGLE occurrence falsifies; no noise allowance):
F1: any ν₁-cell member with w(B₀) < 10 v_p (B1/B2 violation).
F2: any member with frame-2 slot-0 hull point at v_p 28/3 (PD0/C-WW).
F3: any ν₁-cell member whose base digits at (2,7),(3,6) differ from d's
    fixed realization (PD2's occupancy premise).
F4: any [1,4] emission with the ((0,9),(1,8)) pair alive (C-WS disjointness).
FRACTION falsifiers (M ≥ 10⁶; reject beyond 4σ binomial bands):
F5: any ν₁ d-cell mass ≠ 1/16 — in particular a value consistent with 1/4
    refutes rev 6 in favor of NO theory on record (revs 4–5 are already
    refuted by the derivation; the gate re-tests on real p = 2 data).
F6: d-cells non-uniform, or u-cells non-uniform, or d ⫫̸ u (P1/PD1/P3).
F7: 29-slice fraction ≠ 3/4 per cell, or joint (d,u) masses ≠ 1/64 (P3).
F8: C-WS masses ≠ 1/4 per u₀-cell / total ≠ 3/4, or the P4 partition fails.
NON-FALSIFIERS (recorded to prevent scope creep): the ADDRESS of the
displaced pair (PD3); the deeper-slice sub-ladder (PD4); B3/B4 are
falsifiers only in their stated fraction/member form.

CENSUS PROTOCOL (for the eventual script — not created here): sample
f = x⁹ + Σ a_b x^b with a_b = (R₀ digit)·2^{8−b} + 2^{9−b}·U_b, U_b uniform
mod 2^{N−(9−b)}, N = 12, M ≥ 10⁶; frame-1 coefficients by genuine division
by Φ̂₀ = x²+2x+4; Φ̂₁ = the D.5 standard lift from ν₁'s emitted data (the
(S6b) realizer; verify the division sign as in Case-K v2); hull points,
valuations and digits read off directly; bucket and compare. Predictions are
independent of the lift/unit choices up to the recorded cell relabelings.

## S6-OPT. The p = 3 leg (optional; same labels, wild e₁ = p)

ψ₀ = z²+1 (irreducible /F₃), R₀ = (z²+1)⁴ ≡ z⁸+z⁶+z²+1 mod 3, Φ̂₀ = x²+9,
F₉ = F₃[z̄]/(z̄²+1). All label/floor/rung arithmetic above is p-independent
(S2, S4 verbatim); alphabets change: F₉-digit = 2 base pins = 3^{−2}.
Masses: ν₁ cells d ∈ F₉ˣ: 3^{−4} = 1/81 each (8 cells, total 8/81); C-WS
[0,4] family: 1/9 per u₀-cell, total 8/9; partition 8/9 + 8/81 + 1/81 = 1;
29-slice 8/9 per cell, u-cells 1/9; joint (d,u): 3^{−6} = 1/729 (64 cells).
B1: w(B₀) ≥ 10 v_p unchanged. B3: 8/9 exact-at-10, 1/9 deeper. PD0/F2
unchanged (exact zero). NOTE: e₁ = 3 = p makes move 2 WILD at p = 3 — a
genuinely new stress (Case-K's char-3 edge was at the digit level only);
label arithmetic is unchanged by design, which is precisely what it tests.
