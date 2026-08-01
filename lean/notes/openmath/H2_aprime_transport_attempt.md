# H2-P2 — (FRESH)(a′) at r ≥ 1: the composed transport write-up (attempt, rev 0)

Prover H2-P2, HDISCHARGE_H2 swarm, wave 1. PAPER unit per
`lean/blueprints/HDISCHARGE_H2.md` §6 (H2-P2): "the §3.1 steps 1–2 write-up
(A1/TRI composition + (P1)–(P3) height transport, floors displayed), with the
(LEAK) clause explicitly assumed and priced to (VTX-DEEP)" — where every
"(VTX-DEEP)" reads as the widened kernel **(TRANS-DEEP)** (BP §5, review pass 1
findings 2/3). Gate: the standard fresh-context hostile pass (§9 below is the
verifier charge). NOT accepted until that pass; no Lean content lands here.

Sources of record: `lean/notes/openmath/O9_phaseB_verifybrief_rev5.md`
(= "O-9" below; §§1, 2, 4, 5.1, 5.2, 5.4, 6.4), the pinned literature loci
(P1)–(P4) (O-9 §1; verbatim quotes in `LITUNIT_2026-08-01.md`), and
`lean/blueprints/HDISCHARGE_H2.md` (= "BP"; §§3.1, 5).

## 0. Executive summary and the honesty ledger

**(FRESH)(a′)** (O-9 §5.4, the ROOT (H2) row's first clause): conditioned on a
parent realization ρ (level-N₀), the parent's conditions, rewritten in the
window coordinates (a_k) via A1, amount to per-slot valuation floors
w(a_k) ≥ g_k together with the clause-(c) pin, with (g_k) a function of the
DISCRETE parent shape only.

This note executes BP §3.1 steps 1–2 at r ≥ 1. Per the blueprint's own review
verdict (finding 3), the full (a′) — the EXACT product-box conclusion — is NOT
derivable from TRI + the per-polynomial (P1)–(P3) formulas alone; it is the
open kernel clause (TRANS-DEEP)(F), and the no-interior-leak clause is
(TRANS-DEEP)(L). Accordingly this note delivers a **proof ROUTE priced to the
kernel**, never a proof of (a′) outright. Claim-status ledger:

| item | status here |
|---|---|
| (COMP) the r-fold composed mixed-radix coordinate system, level-compatible | **PROVED** (§2; iterated A1, unitriangular) |
| (TRI(i)) per-level triangularity, every level 0 ≤ i ≤ r+1 | **PROVED** (§2 scholium; TRI's own induction) |
| (PS) parent-condition normal form: shape-thresholded height conditions ∧ ρ-realized digit conditions | **PROVED by inspection** of O-9 §2's datum format per order (§3) |
| (SCALE) the cross-level valuation scalings E_i, p_i | **PROVED** from (P1) + Lemma 2.2(2) composed (§1) |
| (FLOOR-1) the transported per-coordinate box IMPLIES every parent height condition | **PROVED** (§4; valuation subadditivity — the free-coordinate part; monic/coset tops need the displayed anchor clearance (A-CLR), else the condition couples and is priced to (F)) |
| (g) the floors, DISPLAYED in closed bookkeeping form | **DISPLAYED** (§4); shape-only PROVED at parent order i = r (in particular ALL of r = 1); at i < r (r ≥ 2) shape-onlyness of the display rides the named mechanical obligation (DEV) |
| (FLOOR-2) the displayed g_k is exactly the w-shadow of the transported box | **PROVED** (§4; TRI + witness) |
| (F), (L) — exactness of the product box; no interior digit leak | **ASSUMED**, displayed verbatim = (TRANS-DEEP)(F)/(L) (§5); NOT proved, NOT weakened |
| Theorem A′: (F) + (L) ⟹ (FRESH)(a′) at (D, N, ρ) | **PROVED given the assumed clauses** (§5) |
| A′(ii) floor-consistency tie g*_k ≤ g_k (true floors bounded by the display) | **PROVED only under the displayed witness hypothesis (WIT_k)** (§5; the unconditional version is circular — drafting note kept in the proof) |
| (CHARGE) CEN-J step-2 / Lean H2-U2 `FloorsChargeLaw` counting shape from (F) | **PROVED given (F)** (§6) |
| r = 0 conformance (M08 §2.2 / O-9 §6.4 validation) | **CHECKED** (§6) |

**What this note does NOT claim.** No clause of (TRANS-DEEP) is proved or
evidenced here beyond the existing record; (a′) remains OPEN; the parent DIGIT
conditions' concentration at the junction (BP §3.1 step 3) is consumed only as
the assumed (L); nothing here discharges (H2). One NEW mechanical obligation is
honestly named, not papered: **(DEV)** (§4.2) — the level-i development
min-formula against w for i < r, plus the shape-onlyness of the lower-level
representative valuations v_{i+1}(φ_s), s > i + 1. (DEV) is bookkeeping of
GMN's own recursion (unpinned loci, Prop 2.8/2.15 territory), consumed ONLY by
the closed-form shape-only DISPLAY at r ≥ 2, never by Theorem A′.

## 1. Setting, pins, and the cross-level scalings

Setting verbatim O-9 §1: O a complete DVR with finite residue field F_q
(q = p^δ); t = (φ₁; λ₁, φ₂; …; λ_r, ψ_r) a type of order r ≥ 1 with
representative φ := φ_{r+1}, residue tower F_q = F₀ ⊆ … ⊆ F_{r+1},
d = f₀f₁⋯f_r, e = e₁⋯e_r, m = deg φ = e·d, valuations v₁, …, v_{r+1},
w := v_{r+1} (ℤ-valued; w(c) = e·v_π(c) for c ∈ O), V̂ := w(φ), m_i = deg φ_i.
f monic of degree n, φ-development f = Σ_{k ≤ ℓ} a_k φ^k, ℓ = ⌊n/m⌋. D a
level-N stratum datum over t with box K_D, thresholds β_k per O-9 §2
((STRICT)/(READ)/(TAIL)), on-line slots, junction k_s. Route G/W split as in
O-9 §3; every statement below is at the O-9 generality (any complete DVR,
q a prime power — BP §3.5's discipline).

Pins consumed (O-9 §1's numbering; LITUNIT-verified loci):

* **(P1)** GMN Prop 2.7(1) + Lemma 2.2(2), per-level form (LITUNIT §1): for
  0 < s ≤ r and deg b < m_s: v_{s+1}(b) = e_s·v_s(b). (Constants deg 0 < m₁
  always qualify.)
* **(P2)** GMN Prop 2.7(3): for a type of order s, the φ_s-adic development
  computes v_{s+1} by minima: v_{s+1}(P) = min_j ( v_{s+1}(b_j) +
  j·v_{s+1}(φ_s) ). Applied at t itself (s = r) this is O-9's (P2); applied
  at the order-s TRUNCATION t_s of t (s < r) it is the same printed statement
  at a smaller type — truncations of a type are types (GMN §2.1), so this is
  pin-scope, flagged per use below.
* **(P3)** GMN Prop 2.7(4) + Thm 2.11: the V-recursion values w(φ_i), w(φ) —
  shape (lattice) data of t.
* A1 / ledger / TRI / LED / LED-top: O-9 §4, PROVED there; B_𝐣 =
  φ₀^{j₀}φ₁^{j₁}⋯φ_r^{j_r} (0 ≤ j₀ < f₀, 0 ≤ j_i < e_if_i) the m ledger
  monomials, wt(𝐣) := w(B_𝐣) = Σ j_i·w(φ_i), TRI: w(Σ c_𝐣 B_𝐣) =
  min_𝐣 (e·v_π(c_𝐣) + wt(𝐣)) on deg < m.

**Lemma SCALE.** Set p_i := v_i(π) and E_i := e_i·e_{i+1}⋯e_r (E_{r+1} := 1).
Then for 1 ≤ i ≤ r + 1:

    (SC1)  p_i = e₁⋯e_{i−1}   (p₁ = 1),
    (SC2)  deg b < m_i  ⟹  w(b) = E_i·v_i(b),
    (SC3)  p_i·E_i = e,  hence  w(c) = e·v_π(c)  for constants, consistently.

*Proof.* (SC2): deg b < m_i ≤ m_s for every s ≥ i (the m_s are strictly
increasing), so (P1) applies at each level s = i, …, r:
v_{s+1}(b) = e_s·v_s(b); composing, w(b) = v_{r+1}(b) = (e_i⋯e_r)·v_i(b).
(SC1): apply the same chain to the constant π from level 1
(v₁ = the order-0 valuation with v₁(π) = 1): v_i(π) = e₁⋯e_{i−1}.
(SC3): (e₁⋯e_{i−1})(e_i⋯e_r) = e. ∎

Convention: every threshold appearing below is within LED(i) scope
(≤ p_i·N₀-level bounds via the standing parent-(DET); O-9 §5.2's rev-2 note),
so all conditions are well-defined on the level-N boxes; we do not repeat this
per display.

## 2. Step 1a — the composed coordinate system (the r-fold A1/TRI composition)

This is the "unwritten mechanical composition" BP §3.1 (open point (ii))
assigns to this unit. Two statements; both are elementary consequences of the
O-9 §4 stock, written out.

**Lemma COMP (composed mixed-radix coordinates).** Let the COMPOSED monomials
be M_{k,𝐣} := φ_{r+1}^k·B_𝐣, 0 ≤ k, 𝐣 a ledger index. Then:

* (i) deg M_{k,𝐣} = k·m + deg B_𝐣, and (k, 𝐣) ↦ deg M_{k,𝐣} is a bijection
  onto ℤ_{≥0} in mixed radix (the ledger degrees hit 0..m−1 once each — O-9
  §4 — and the k-digit extends the radix one level: m_{r+2} := ∞).
* (ii) Each M_{k,𝐣} is monic of its degree, so the change of basis between
  {x^t} and {M_{k,𝐣}} (degrees ≤ any fixed bound) is unitriangular over O;
  iterated Euclidean division (A1, applied first in φ = φ_{r+1}, then per
  window coefficient in the ledger basis) realizes it: every f has a unique
  expansion f = Σ_{k,𝐣} c_{k,𝐣}·M_{k,𝐣} with c_{k,𝐣} ∈ O, c_{k,𝐣} = 0 for
  deg M_{k,𝐣} > n; the window coefficients are the groupings
  a_k = Σ_𝐣 c_{k,𝐣}·B_𝐣.
* (iii) Level compatibility: the maps f ↦ (c_{k,𝐣}) and f ↦ (b_j^{(i)}(f))
  (the φ_i-adic development coefficients, any 1 ≤ i ≤ r + 1) are O-linear and
  commute with reduction mod π^{N'} for every N': f ≡ f' (mod π^{N'}) ⟺
  c_{k,𝐣} ≡ c'_{k,𝐣} (mod π^{N'}) for all (k,𝐣), and then
  b_j^{(i)}(f) ≡ b_j^{(i)}(f') (mod π^{N'}) coefficient-wise.
* (iv) Monic tops: for m | n the monic-top box is c-coordinates with the
  slot (ℓ, 𝟎)-group replaced by a_ℓ = 1; for m ∤ n the coset top is A1's
  LED-top coset (O-9 §4, Lemma LED-top): a_ℓ ∈ B_{𝐣*} + W′, both expressed in
  the same composed coordinates with the ANCHOR monomial's coefficient pinned
  to 1. We write f = A + f°, where A ∈ {φ^ℓ, φ^ℓ·B_{𝐣*}, 0} is the pinned
  anchor part (0 in the free box) and f° the free part.

*Proof.* (i) mixed-radix arithmetic; deg B_𝐣 = Σ j_i m_i hits each residue
0..m−1 once (O-9 §4's ledger display). (ii) products of monics are monic;
one monic monomial per degree gives unitriangularity; A1 (division by monic
polynomials, O-linear with O-coefficient formulas) applied at φ and then at
each ledger level realizes the inverse. (iii) O-linearity of Euclidean
division by a monic polynomial (A1's proof, verbatim), applied to each map;
an O-linear map with O-coefficient formulas commutes with mod-π^{N'}
reduction. (iv) is O-9 §2's box bookkeeping restated in c-coordinates
(LED-top's coset identification for m ∤ n). ∎

**Scholium TRI(i) (per-level triangularity — TRI's induction, recorded at
every level).** For 0 ≤ i ≤ r: the order-i sub-radix monomials
B_{𝐣'} (𝐣' = (j₀, …, j_{i−1}), deg < m_i) form the level-i ledger, and

    (TRI(i))   v_i( Σ_{𝐣'} c_{𝐣'} B_{𝐣'} ) = min_{𝐣'} ( p_i·v_π(c_{𝐣'}) + wt_i(𝐣') ),

with wt_i(𝐣') := v_i(B_{𝐣'}) = wt(𝐣')/E_i (SCALE (SC2)). *Proof.* This IS
the inductive hypothesis of TRI's proof (O-9 §4): the induction on r proves
exactly this statement for v_i on its own sub-radix at every level; SCALE
converts weights. ∎

Consequence (grouping): for deg a < m, grouping the ledger by the top index
j_r gives the φ_r-development of a with TRI-computed coefficient valuations;
iterating downward, the composed coordinates of a compute ALL its per-level
development data within degree < m. What does NOT follow from grouping — and
is the genuine content of Step 2 — is the relation between f's φ_i-adic
development ACROSS φ-slots (φ^k is not a φ_i-power; its φ_i-development has
many terms). That is §4's business.

## 3. Step 1b — the parent-condition normal form (PS)

The parent realization ρ is a level-N₀-determined condition family on monic
degree-n f: the order-≤ r OM tower data that produced t, realized (O-9 §2's
C_{D,N} definition: "the fixed concrete φ_i, ψ_i, and the parent stratum data
that produced t"). At each order i ∈ {1, …, r} the order-i stratum datum has
exactly the O-9 §2 format on the φ_i-adic development f = Σ_j b_j^{(i)} φ_i^j
(deg b_j^{(i)} < m_i), with polygon heights u_j^{(i)} = v_i(b_j^{(i)}) +
j·v_i(φ_i):

* (STRICT)/(TAIL)-type slots: v_i(b_j^{(i)}) > or ≥ a threshold;
* (READ)-type on-line slots: v_i(b_j^{(i)}) ≥ β_j^{(i)} together with the
  digit read at β_j^{(i)} equal to ρ's realized value (the zero digit class
  encoding "strictly above" — O-9 §5.1's convention);
* the residual-factor selection at order i (type membership + the marked
  ψ_i-factor): a condition on the JOINT graded read vector of the order-i
  on-line slots, realized by ρ;
* the order-0 block datum (the ψ₀-selection): a Gauss-level graded condition.

**Lemma PS-SPLIT (normal form).** Every parent membership condition family of
the above format is equivalent to a conjunction

    (PS)   HGT≥(shape)  ∧  DIG(ρ)

where HGT≥(shape) is a FINITE family of lower-bound height conditions

    C = (i, j, ▷, θ_C),   ▷ ∈ {≥, >} :      v_i( b_j^{(i)}(f) )  ▷  θ_C,

whose thresholds θ_C are functions of the DISCRETE parent shape only (the
parent data's faces, types, N₀ — never ρ's realized digits), and DIG(ρ) is a
condition on the tuple of order-≤ r graded reads of finitely many b_j^{(i)}(f)
(read values, vertex nonvanishing, joint residual-type/marked-factor
membership), whose defining constants are ρ's realized residues.

*Proof (inspection).* Each format line above is already of one of the two
shapes: (STRICT)/(TAIL) are HGT≥ with shape thresholds (the parent's lines);
a (READ) condition "w = β ∧ read = z*" with z* ≠ 0 equals "w ≥ β ∧ read = z*"
(a nonzero read forces w = β by the read's definition, O-9 §5.1), i.e. one
HGT≥ row plus one DIG row, and with z* = 0 it is "w > β" — HGT≥ alone;
exactness at vertices is carried by the types' nonvanishing (O-9 §5.2), a DIG
row; residual/type selections and the order-0 block are DIG rows by
definition. Thresholds enter only from the parent's lines and N₀: shape-only.
∎

Remark (robustness). Theorem A′ below consumes ONLY the (PS) shape, not the
particular provenance; any level-N₀-determined parent presented in (PS)
normal form is covered. The standing hypothesis "(DET) over the parent's own
reads" (CEN-J's hypothesis, O-9 §2/§6.4 step 1) is what makes the family
level-N₀-determined; we inherit it verbatim.

## 4. Step 2 — the (P1)–(P3) height transport; the floors displayed

Throughout: f = A + f° per COMP(iv) (A the pinned anchor part — 0 in the free
box), f° = Σ_{(k,𝐣) free} c_{k,𝐣} M_{k,𝐣}. Fix the parent family (PS).

### 4.1 The transport data

For a parent height condition C = (i, j, ▷, θ_C) and a free composed slot
(k, 𝐣) define the **transport data**

    (D)    D_{(i,j)}(k,𝐣) := v_i( b_j^{(i)}( M_{k,𝐣} ) )  ∈ ℤ ∪ {∞}
           (∞ iff the φ_i-development of M_{k,𝐣} has zero j-th coefficient),

and the **anchor terms**  ν_{(i,j)} := v_i( b_j^{(i)}(A) ) ∈ ℤ ∪ {∞}.

These are well-defined integers computable by finitely many Euclidean
divisions (COMP(ii)/(iii)); a priori they depend on the CONCRETE φ₁, …, φ_{r+1}
(i.e. on ρ), not only on the shape — see §4.2.

**Lemma D-BND (closed-form lower bound at parent order i = r; PROVED).**

    (D-r)   D_{(r,j)}(k,𝐣)  ≥  ( k·V̂ + wt(𝐣) − j·w(φ_r) ) / e_r ,

and the right side is SHAPE data ((P3) V-recursion values only).
*Proof.* w(M_{k,𝐣}) = k·w(φ) + wt(𝐣) = kV̂ + wt(𝐣) (w a valuation; (P3)).
By (P2) at t itself (order r): w(M) = min_j ( w(b_j^{(r)}(M)) + j·w(φ_r) ),
so w(b_j^{(r)}(M)) ≥ w(M) − j·w(φ_r) for every j. Since
deg b_j^{(r)} < m_r, SCALE (SC2) gives v_r(b_j^{(r)}) = w(b_j^{(r)})/e_r
(E_r = e_r). ∎

The same argument at a truncation t_i (i < r) gives
D_{(i,j)}(k,𝐣) ≥ ( v_{i+1}(M_{k,𝐣}) − j·v_{i+1}(φ_i) ) / e_i via (P2)@t_i +
(P1); here v_{i+1}(φ_i) is (P3)@t_i shape data, but v_{i+1}(M_{k,𝐣}) =
k·v_{i+1}(φ_{r+1}) + Σ_s j_s·v_{i+1}(φ_s) involves the LOWER-LEVEL valuations
of the HIGHER representatives (s > i + 1), which the pins do not put in
closed shape form. We therefore name, honestly:

**(DEV) [named mechanical obligation; NOT assumed by Theorem A′].** For
1 ≤ i < r: (DEV-a) the shape-onlyness (ρ-independence) of v_{i+1}(φ_s),
i + 1 < s ≤ r + 1, with their closed recursion values; equivalently (DEV-b)
the min-formula for w against the φ_i-adic development at levels i < r.
This is GMN's own recursion bookkeeping (Prop 2.8/2.15 territory — loci NOT
pinned; an H2-L1-type lookup or a one-page induction owed separately). It is
consumed ONLY by the closed-form shape-only DISPLAY of the floors at r ≥ 2
(§4.3); FLOOR-1/FLOOR-2 and Theorem A′ consume the transport data (D) as
defined, without (DEV).

### 4.2 The transported per-coordinate box and FLOOR-1

For each free slot (k,𝐣) define the transported per-coordinate floor

    (γ)   γ_{k,𝐣} := max( 0,  max_{C = (i,j,▷,θ_C) ∈ HGT≥}
                     ⌈( θ_C − D_{(i,j)}(k,𝐣) ) / p_i⌉_▷ ),

with ⌈x⌉_≥ := ⌈x⌉, ⌈x⌉_> := ⌊x⌋ + 1, and the convention that a condition with
D_{(i,j)}(k,𝐣) = ∞ contributes nothing. The **transported box** is

    (B_γ)   B_γ := { f = A + f° :  v_π(c_{k,𝐣}) ≥ γ_{k,𝐣}  for all free (k,𝐣) }.

**Anchor clearance.** Say C = (i, j, ▷, θ_C) is *anchor-cleared* if
ν_{(i,j)} ▷ θ_C (automatic in the free box: A = 0, ν = ∞). Display:

    (A-CLR)   every C ∈ HGT≥ is anchor-cleared.

**Proposition FLOOR-1 (the box implies the parent heights; PROVED).** Assume
(A-CLR). Then every f ∈ B_γ satisfies every condition of HGT≥(shape).

*Proof.* Fix C = (i, j, ▷, θ_C). By COMP(iii), b_j^{(i)}(f) = b_j^{(i)}(A) +
Σ_{(k,𝐣) free} c_{k,𝐣}·b_j^{(i)}(M_{k,𝐣}). v_i is a valuation with
v_i(c·P) = p_i·v_π(c) + v_i(P) for c ∈ O (SCALE (SC1) on constants), so

    v_i( b_j^{(i)}(f) ) ≥ min( ν_{(i,j)},  min_{(k,𝐣)} ( p_i·v_π(c_{k,𝐣}) + D_{(i,j)}(k,𝐣) ) ).

On B_γ each free term has p_i·v_π(c) + D ≥ p_i·⌈(θ_C − D)/p_i⌉_▷ + D ▷ θ_C
(integrality of v_i-values), and the anchor term ▷ θ_C by (A-CLR). ∎

**Remark (the coupled branch — priced, not papered).** If (A-CLR) FAILS at
some C — i.e. the pinned anchor part itself violates a parent height
threshold, ν_{(i,j)} = θ' with ¬(θ' ▷ θ_C) — then C forces CANCELLATION
against the anchor: v_i(b_j^{(i)}(f°)) = θ' exactly, with the graded classes
cancelling. That is a coupled, digit-level condition on the free coordinates
— exactly the "triangular change of coordinates can transport congruences
into coupled conditions" shape review finding 3 priced to (TRANS-DEEP)(F),
and exactly the anchor-riding phenomenon of the supplier campaign's Case-J
record (the (z+c)^a anchor-monomial transport) and of LED-top(i)'s anchor
cap. This note asserts NOTHING in that branch beyond its pricing. Note the
r = 0 instance has (A-CLR) automatic (M08's block datum constrains only the
non-anchor slots; §6).

### 4.3 The floors, displayed; FLOOR-2

For each window slot k ∈ K_D define the **displayed floor**

    (g)   g_k := min_{𝐣} ( e·γ_{k,𝐣} + wt(𝐣) )

— "the minimum over the contributing monomials of one slot" (BP §3.1 step 2).

**Proposition FLOOR-2 (the displayed floor is exactly the box's w-shadow;
PROVED).**

* (i) For every f ∈ B_γ and k ∈ K_D: w(a_k) ≥ g_k.
* (ii) g_k is exact: there is f ∈ B_γ with w(a_k) = g_k (choose
  c_{k,𝐣₀} = π^{γ_{k,𝐣₀}} at an argmin 𝐣₀ of (g), all other free
  coordinates of slot k with v_π strictly larger than (g_k − wt)/e, the
  other slots anywhere in B_γ; TRI computes w(a_k) = e·γ_{k,𝐣₀} + wt(𝐣₀)).
* (iii) Hence B_γ ⊆ B_g := { w(a_k) ≥ g_k ∀ k ∈ K_D }, and g is the largest
  slot-floor vector with that property.

*Proof.* (i): on B_γ, TRI gives w(a_k) = min_𝐣 (e·v_π(c_{k,𝐣}) + wt(𝐣)) ≥
min_𝐣 (e·γ_{k,𝐣} + wt(𝐣)) = g_k. (ii): the displayed witness, TRI again.
(iii): (i) is the containment; (ii) forbids any larger floor. ∎

**Shape-onlyness of the display.** θ_C are shape-only (PS-SPLIT). At r = 1
every C has i = 1 = r, and replacing D by its (D-r) closed bound makes (γ),
(g) manifestly shape-only ((P3) values and e, p_i only) — PROVED. At r ≥ 2
the i < r rows' closed shape form rides (DEV); with (D) as defined, γ and g
are per-realization computable integers, and their ρ-INdependence is part of
what the kernel asserts ((F)'s "(g_k) a function of the discrete parent shape
only"). We do NOT claim it here beyond i = r.

**What is NOT proved here (the exactness gap, stated exactly).** The proved
containments are  B_γ ⊆ {HGT≥} (FLOOR-1, under (A-CLR)) and B_γ ⊆ B_g
(FLOOR-2). (a′) needs the ρ-FIBER (= {HGT≥} ∧ DIG(ρ) on the box) to EQUAL
B_g ∧ (pin), i.e. additionally: (α) no cancellation direction — the fiber
admits no f outside B_g's shadow bookkeeping ({HGT≥} ⊆ B_γ-side exactness);
(β) per-slot independence — the fiber's conditions are axis-aligned in the
slots, no cross-slot or lower-digit survival; (γ') no parent digit condition
touches an interior on-line window slot. (α) + (β) = (TRANS-DEEP)(F);
(γ') = (TRANS-DEEP)(L). TRI is an equality per SLOT, but the transported
family is not TRI-shaped per slot (γ_{k,𝐣} need not equal
⌈(g_k − wt(𝐣))/e⌉ for all 𝐣), and v_i-subadditivity is strict under graded
cancellation — both failure channels are real at r ≥ 1, which is exactly why
the kernel is open.

## 5. The assumed clauses and Theorem A′

The two assumed clauses, verbatim the (F)/(L) clauses of BP §5's consumer-side
kernel specification (quoted; (J) is NOT consumed here — it is H2-P1's and
(c)'s):

> **(TRANS-DEEP)(F) [floors/product — ASSUMED].** The ρ-fiber's membership
> conditions, rewritten in the window coordinates (a_k), are EXACTLY the
> per-slot valuation floors w(a_k) ≥ g*_k — independent, axis-aligned (a
> Cartesian product box), with (g*_k) a function of the discrete parent shape
> only — PLUS the clause-(J) pin; no lower-digit or cross-slot condition
> survives.
>
> **(TRANS-DEEP)(L) [leak — ASSUMED; = the (LEAK) clause].** At every
> interior on-line slot k ≠ k_s, the parent's realized conditions impose NO
> constraint on the height-β_k digit of a_k beyond (F)'s floor.

We write g* for (F)'s floors to keep them typographically distinct from the
§4.3 display g.

**Theorem A′ (the composed transport at r ≥ 1; conditional).** Fix t of order
r ≥ 1, φ, a ledger-admissible level-N datum D within (DET) scope, and a
parent realization ρ in (PS) normal form, level-N₀-determined ((DET) over the
parent's own reads), N₀ ≤ N. Assume (GR-B) at order r + 1 (O-9's standing
package) and clauses (TRANS-DEEP)(F) and (L) at (t, φ, N, D, ρ). Then:

* (i) **(FRESH)(a′) holds at (D, N, ρ)** with floors g*: the parent's
  conditions in the window coordinates amount to the per-slot floors
  w(a_k) ≥ g*_k plus the clause-(c) pin, g* shape-only. [(F) restated
  through the (PS) normal form — see the proof for what is actually
  derived vs. assumed.]
* (ii) **(floor-consistency tie — CONDITIONAL on the displayed witness
  hypothesis)** Say (WIT_k) holds if the fiber meets B_γ at a slot-k-minimal
  point: ∃ f ∈ B_γ ∩ (the ρ-fiber) with w(a_k) = g_k. Then g*_k ≤ g_k:
  (F)'s true floor at k is bounded above by the §4.3 DISPLAY. (WIT_k) is a
  mild nonemptiness/genericity statement (the FLOOR-2 witness with digit
  data adjusted to DIG(ρ)'s finitely many read values) but is NOT proved
  here; without it the display is only the w-shadow of the proved inner box
  B_γ ⊆ {HGT≥}. Even so, the kernel supplier owes exactness against a
  concrete, per-instance-computable candidate bookkeeping — not existence
  of an unspecified box.
* (iii) **(rev-0 (a) recovered)** slots with g*_k ≥ β_k charge nothing in
  (E″): the parent's floor already clears the window threshold — the
  max(0, s(β_k) − s(g_k)) truncation (O-9 §6.4 step 2, CEN-J's (E″)).

*Proof.* (i) By PS-SPLIT the parent conditions are HGT≥(shape) ∧ DIG(ρ);
these are level-N₀-determined, hence well-defined on the level-N window box
(COMP(iii), N₀ ≤ N). (F) asserts the fiber equals B_{g*} ∧ pin with g*
shape-only; (L) asserts DIG(ρ)'s only digit-level trace on the window's
on-line slots is at k_s (the pin). Together they are precisely (a′)'s three
claims (floors; product box; shape-onlyness) — the clause is assumed, not
derived; what this note ADDS is that the assumption is consistent with, and
pinned to, the proved transport skeleton: the fiber CONTAINS the concrete
box B_γ (FLOOR-1 for HGT≥; DIG(ρ) is nonempty-compatible on B_γ by O-9's
padding convention — an empty fiber satisfies (a′) vacuously, no
nonemptiness is asserted, matching BP §6's `JunctionPinLaw` design note).
(ii) Immediate from the definitions once (WIT_k) supplies the witness: the
witness lies in the fiber = B_{g*} ∧ pin by (F), hence g*_k ≤ w(a_k) = g_k.
[Rev-0 drafting note, kept for the record: the tempting unconditional
argument — take FLOOR-2(ii)'s B_γ-witness and "adjust its digit data into
the fiber" — is CIRCULAR: keeping the adjusted witness inside B_{g*} at the
other slots already uses g* ≤ g. Hence the displayed hypothesis; a
non-circular discharge of (WIT_k) is welcome future work, likely alongside
the kernel itself.] (iii) is LED(ii) arithmetic:
{w ≥ β_k} ∩ {w ≥ g*_k} = {w ≥ max(β_k, g*_k)}, and s(max(β_k, g*_k)) −
s(β_k) = 0 when g*_k ≤ β_k... — stated for the record in CHARGE below; the
"charges nothing" case is g*_k ≤ β_k, i.e. rev-0 (a)'s automaticity is the
OTHER slots' bookkeeping, exactly O-9 §5.4 (a′)'s parenthetical. ∎

**Corollary CHARGE (the CEN-J step-2 consumption shape; PROVED given (F)).**
Under Theorem A′'s hypotheses, for every slot k ∈ K_D the fiber's height
condition at k is w(a_k) ≥ max(β_k, g*_k) on the slot's LED box, so its
absolute count at alphabet level N is

    (CH)   # = q^{ mN − s( max(β_k, g*_k) ) }        (LED(ii); s′ at an
           m ∤ n coset top per LED-top(i)),

i.e. the relative charge against the parent's baseline is
q^{−max(0, s(β_k) − s(g*_k))} — verbatim the (E″) summand and verbatim the
Lean unit H2-U2 `FloorsChargeLaw` shape (BP §6: ℕ-subtraction implementing
the max(0,·), the `hscope` guard g_k ≤ β_k at on-line slots displayed there
as a hypothesis of the consuming theorems). *Proof.* Intersection of
w-floors is the max-floor ({w ≥ a} ∩ {w ≥ b} = {w ≥ max(a,b)}), then LED(ii)
at max(β_k, g*_k); the monotonicity s(max(β,g)) = max-side count is BP §6's
flagged `Finset.card_le_card` convention. ∎

## 6. Conformance checks (verification scaffolding)

**r = 0 (the proved instance; M08 §2.2 / O-9 §6.4 validation).** Parent = the
x^e-block condition v_π(a_i) ≥ 1 (N₀ = 1): (PS) has HGT≥ = {(i = "order 0
scaled", j, ≥, 1)} rows only — already axis-aligned in the window
coordinates, D-data diagonal, so B_γ = B_g = the fiber with g ≡ 1 EXACTLY,
(A-CLR) automatic (the anchor is the monic top, untouched by the block
condition), and (F)/(L) hold outright — (a′)'s r = 0 face, consistent with
O-9 §6.4's E″ = Σ(N − c_i) validation and BP §6's H2-U6 canonical instance
(floors g ≡ 1, N₀ = 1). This note's machinery degenerates to the known
proof; no circularity (r = 0 is not in this note's scope, it is its floor).

**r = 1 (the first deep case).** All parent height rows have i = 1 = r, so
Lemma D-BND's closed form applies to every row: γ and g are fully displayed,
shape-only, from (P3) values alone — no (DEV). What remains open at r = 1 is
exactly (F)/(L), nothing of the display. This matches the blueprint's
pricing: the kernel, not the bookkeeping, is the open content at the first
deep order.

**Worked micro-display (r = 1, the K6/K7 lattice).** For the O-9 §2 warning
types (f₀ = 1, e₁ = 3, h₁ = 2: ledger weights {0, 2, 4}; or f₀ = 1, e₁ = 1,
f₁ = 2, h₁ = 2: weights {0, 2}), a parent row (1, j, ≥, θ) transports to
γ_{k,𝐣} = ⌈(θ − (kV̂ + wt(𝐣) − j·w(φ₁))/e₁)/1⌉ (p₁ = 1) at contributing
slots, and g_k = min_𝐣(e·γ_{k,𝐣} + wt(𝐣)) is a finite explicit lattice
computation per (k, j, θ) — the H2-N2 harness shape (§8). No numeric claim
is made here; the display is what N2 measures against.

## 7. Pricing and the open ledger (what this note leaves open, exactly)

1. **(TRANS-DEEP)(F), (L)** — ASSUMED (§5), verbatim BP §5; owner: the GD
   order-≥ 2 / MOVES carry-algebra campaign (B2-FINAL, NOT accepted). One
   kernel, three consumption points (BP §3.2): (a′)'s exactness+leak (here),
   (b)'s structural unit-slope face, (c-TR). This note adds NO new kernel
   content and does not evidence the kernel.
2. **(DEV)** (§4.2) — NEW named mechanical obligation, consumed only by the
   closed-form shape-only DISPLAY at r ≥ 2 (parent rows with i < r): the
   level-i development min-formula against w, plus shape-onlyness of
   v_{i+1}(φ_s), s > i + 1. Expected: GMN Prop 2.8/2.15-adjacent, a
   LITUNIT-charge lookup or a one-page induction. NOT load-bearing for
   Theorem A′, CHARGE, or the r = 1 display.
3. **(A-CLR)** — a per-instance side condition (anchor clearance) for
   FLOOR-1 at monic/coset tops; its failure branch is coupled and priced to
   (F) (§4.2 remark). At r = 0 automatic; expected generically automatic
   (the parent stratum is realized BY polynomials of the given monic shape),
   but no such claim is made.
4. **Parent DIGIT conditions** (BP §3.1 step 3) — wholly priced: their
   window trace is (L) + the (c) pin; the graded-level identification of the
   pin's value is H2-P1's (c-GR); the finite-level descent is
   (TRANS-DEEP)(J). Untouched here by charge design.

Consumption of this note once accepted: BP §4's (FRESH-RED) cites it as the
(a′) leg — "(GR-B) + (TRANS-DEEP) ⟹ (FRESH)" with the (a′) conjunct
supplied by Theorem A′(i), the §4.3 display standing as the concrete
candidate floor bookkeeping (tied to (F)'s floors by A′(ii) where (WIT)
holds). Together with H2-P1 ((c-GR)), the two paper units shrink (H2) to
exactly the (TRANS-DEEP) kernel — the unit's stated goal; neither
discharges it.

## 8. Falsifier gates (specs owned elsewhere; what would refute WHAT here)

* **H2-N2** (BP §7): per discrete parent shape, ≥ 2 realizations ρ —
  (i) per-slot minimal attained w(a_k) per fiber vs the §4.3 display:
  measured fiber floors BELOW the display indicate slack in B_γ (D-data
  subadditivity slack or a failed (WIT_k)) — informative, not a refutation;
  a fiber point violating a FLOOR-1-transported HEIGHT condition, or
  measured floors ABOVE the display at an (A-CLR)+(D-r)-verified instance,
  would refute FLOOR-1/FLOOR-2's bookkeeping — stop-the-line, this note is
  then wrong; ρ-DEPENDENT measured floors at fixed shape gate (F)'s
  shape-only clause (kernel evidence); (ii)/(iii) marginal and
  joint leak detectors gate (F)/(L) themselves (evidence, never proof).
* **The standing fence** (BP §1): all residue reads in the COHERENT
  anchored-march normalization; a slot-fresh reading of any digit clause is
  machine-refuted (1,818×). This note's digit content is entirely inside
  DIG(ρ)/(L)/(J) and inherits the fence through O-9 §5.1/(GR-B)(2′).
* Existing record consistent with this note: K2 realization-independence
  (1,128,288 order-2 instances, 0 violations) supports shape-onlyness;
  non-discriminating for exactness (O-9 §10's honest reading).

## 9. Verifier charge (the hostile pass; fresh context)

You are verifying a mathematics note. Quote each offending passage and
classify it: CRITICAL (breaks the logical chain) vs JUSTIFICATION GAP
(assume and continue); fix nothing. Specific audit points: (1) every PROVED
row of §0's ledger — especially FLOOR-1's subadditivity direction (is the
claimed implication really only lower bounds?), FLOOR-2(ii)'s witness, SCALE
and D-BND's pin usage ((P1)/(P2) applied within printed scope? truncation
use of (P2) legitimate?), and Theorem A′(ii)'s (WIT_k) hypothesis (is the
conditional statement now non-circular, and is (WIT_k) consumed nowhere
else silently?); (2) that (F)/(L) are consumed VERBATIM from BP §5 and nowhere
silently strengthened or weakened; (3) that no step silently uses (DEV)
outside the display; (4) quantifier hygiene in (PS) (is the normal form
really exhaustive for O-9 §2's format at every order i ≤ r?); (5) the r = 0
conformance (§6) for circularity. The note is accepted only after the
repo-standard consecutive clean passes.

— H2-P2 attempt rev 0. Statement fence: (FRESH)(a′), (TRANS-DEEP), and all
O-9/BP displays are quoted, never restated-with-drift; any deviation found
is a defect of this note, not a proposal to change the source.
