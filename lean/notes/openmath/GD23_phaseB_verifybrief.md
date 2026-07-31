# GD23 — the GD dictionary unit (GD-2 ⊕ GD-3): frame/valuation tie, development identity, residual dictionary, over an ARBITRARY complete DVR — verification brief (rev 0)

Unit: SYNTH4 (`lean/notes/SYNTHESIS_PASS4_2026-08-01.md`) §1 families **GD-2**
(frame/valuation tie + development identity) and **GD-3** (residual dictionary),
merged into ONE MacLane/GMN unit and stated over an arbitrary complete DVR with
perfect residue field, per the adjudicated plan (§3.2 step 3: "stated over an
arbitrary absolutely-unramified complete DVR from the start — kills most of
D-3"; this brief states everything over an arbitrary complete DVR, which is
wider and costs nothing). Author: Fable prover, 2026-07-31. Status protocol:
PROVED-UNVERIFIED until hostile fresh-context passes accept it.

Composed sources (the ~30% named by SYNTH4's mapping table): O-1thr rev 4
(`O1thr_phaseB_verifybrief_rev4.md` §§1.1, 2.1–2.5 — Lemmas DEV/POS/VAL1/KEY1/
DIV1/WGEO, the (V1)/(V2) statements); O-2a rev 5
(`O2a_phaseB_verifybrief_rev5.md` §§1, 4 — the (L1)–(L9) GMN transcriptions,
the stage interface [F.0]–[F.2], OL-2/OL-2-min/OL-3/OL-3-min, the PROVED (D3));
M08 (`M08-cl6-general_fable.md` §3 — OL-B); `docs/GMN_citations.md` (pinned
loci). Falsifier: `verification/openmath/gd23_check.py` — run BEFORE this brief
was written (§9).

## 0. What is claimed, in one paragraph

Over an arbitrary complete DVR O (fraction field K, normalized valuation v,
residue field F — perfectness of F carried as a standing hypothesis for the
consumers, USED NOWHERE in this brief's proofs, §1.1), the engine/GMN seam's
mathematical middle term is the MacLane augmented-valuation chain w_i (§1.2).
The brief proves, outright and self-contained at the displayed perimeters:
the full order-≤1 layer at EVERY root-key degree d₀ (Lemmas DEV-g/POS-g/
GAUSS-g, Theorems VAL-g/KEY-g/RES-1 — generalizing O-1thr's VAL1/KEY1/DIV1
from d₀ = 1 over ℤ_p to any d₀ over any O, and closing the order-1 residual
dictionary in full, twists absent); the **development identity at EVERY order**
(Theorem DEVID — the (V2b) family member, proved from (V1) + the key-minimality
block by a graded argument that replaces DIV1's slot-chase and is degree- and
ring-free); the uniqueness half of the frame tie (Lemma UNIQ) so that the
MacLane↔GMN identification w_i = v_{i+1} (Theorem TIE) rests on exactly three
GMN transcriptions, two already pinned and one flagged; and the stage-polygon/
record dictionary (Corollary REC-c1) as a corollary shape. GD-3's general-order
residual dictionary is split: the MIN CORE (all the recut cluster consumes, per
V25) gets TWO independent routes — one through a single flagged GMN lemma
(T-2), one through the displayed residue-structure input (GR-B); the FULL form
and the OL-B slot-bijection law are proved FROM (GR-B), whose order-1 instance
is proved here (RES-1) and whose general form is the note's one genuinely open
input, pinned to MacLane §§9–12 / FGMN 2015 (§7, §11). The engine-conformance
half of every carrier statement (that the ENGINE's emitted records are computed
by these formulas) is NOT claimed — it is displayed as the GD-4/GD-6/S-1
residue, and the brief instead proves the interface-instantiation clause: the
stage-interface axioms hold AT the MacLane/GMN valuation (Corollary IFACE).

**Status table.**

| claim | scope | status |
|---|---|---|
| DEV-g, POS-g, GAUSS-g | any O, any d₀ | PROVED (§3) |
| VAL-g: w₁ valuation, gr = K₀[π̄^{±1}][Φ̄₀] UFD | any O, any d₀ | PROVED (§3) |
| KEY-g: standard lift key laws + min core at order 1 | any O, any d₀ | PROVED (§3) |
| RES-1: order-1 residual dictionary, full form, OL-B order-1 | any O, any d₀ | PROVED (§3) |
| DEVID: development identity, every order | any O | PROVED given (V1)+(KPa) at that order (§4) |
| V1-tower: every w_i a valuation | any O | PROVED order ≤ 1; MacLane Thm 4.2 + (KP) beyond (§5; pin + one scope flag) |
| UNIQ (tie uniqueness) | any O | PROVED (§6) |
| TIE: w_i = v_{i+1} (GMN) | GMN's scope (K/ℚ_p finite) | PROVED modulo pins (L2)/(L4-P2.7) [in hand] + T-1 [FLAGGED] (§6) |
| REC-c1: window polygon = N_{i+2}(f), record verbatim (c1) | as TIE | corollary of TIE + DEVID (§6) |
| GD3-MIN (general order) | as TIE | route A: TIE + T-2 [FLAGGED]; route B: (GR-B) (§7) |
| GD3-FULL + OL-B (general order) | any O | PROVED from (GR-B) [displayed open/cited input] (§7) |
| IFACE: [F.0]–[F.2] hold at w | any O | (S-K1)+(u-mult) PROVED; dig laws = (GR-B); order 1 PROVED (§7.4) |
| engine conformance (u = w for the implemented engine) | — | NOT CLAIMED (GD-4/GD-6/S-1 residue; §8) |

## 1. Setting

### 1.1 The base ring, and where each standing hypothesis is used

O: a complete discrete valuation ring, π a uniformizer, v the normalized
valuation (v(π) = 1), K := Frac O, F := O/πO. Standing hypotheses per the unit
spec: O complete, F perfect. **Usage display (attackable):**

* **Completeness is used in NO proof of this brief.** Its consumers are the
  GMN factorization theorems (Thms 1.15/1.19/3.1/3.7 — splitting f into
  factors needs Hensel-type completeness), which this brief cites only inside
  the FLAGGED route-A input T-2 and nowhere else. Every PROVED statement below
  holds over any DVR.
* **Perfectness of F is used in NO proof of this brief.** The residue tower
  K_{i+1} = K_i[z]/(ψ_i) is a tower of fields for any F. Perfectness is
  carried because the project's consumers (separability of residual counts,
  the BB3/L3 finite-field layer) assume it, and because GMN's own scope is
  F finite. It costs nothing to carry.
* Consequently the statements INSTANTIATE at O = ℤ_p, at O = O_δ = W(F_{p^δ})
  (the unramified re-base of D-3/O-8b — **this is the D-3 kill**: T-1-style
  stage laws over O_δ are instances, not a transfer theorem), and at
  equal-characteristic O = F_q[[t]] (exercised by the falsifier, §9).
* GMN's own theorems remain scoped to K/ℚ_p finite (their standing hypothesis,
  `GMN_citations.md` audit-fix); the TIE/T-2 clauses are therefore claimed at
  GMN's scope, and their arbitrary-DVR generalization rides the (GR-B)/FGMN
  pin (FGMN 2015 works over an arbitrary discretely valued field — scope flag
  in §11).

### 1.2 The tower: policy, frames, the MacLane chain, and the three-term seam

Transcribed from O-1thr rev 4 §1.1 with ℤ_p → O throughout (the transcription
is verbatim except v_p → v, p → π, 𝔽_p → F).

* **Policy 𝒫**: (i) to each monic irreducible φ̄ ∈ F[X], a monic lift
  Φ₀ ∈ O[X] with deg Φ₀ = deg φ̄ =: d₀; (ii) to each lawful node ν over a
  frame of order i, a monic key Φ_{i+1} ∈ O[X] with
  deg Φ_{i+1} = e_i·g_i·deg Φ_i. All statements are relative to one fixed 𝒫.
* **Order 0**: w₀(B) := min_j v-content(c_j) over the Φ₀-adic development
  B = Σ_j c_j Φ₀^j (v-content := min of coefficient valuations);
  K₀ := F[z]/(φ̄). (Lemma GAUSS-g: w₀ = the plain Gauss valuation, and a
  valuation.)
* **Order i+1**: given the frame (Φ_i, w_i, K_i) and a read ν_i with data
  (e_i, h_i) coprime ≥ 1 and ψ_i ∈ K_i[z] monic irreducible of degree g_i with
  ψ_i(0) ≠ 0: set γ_{i+1} := e_i·w_i(Φ_i) + h_i and
  w_{i+1}(B) := min_j ( e_i·w_i(c_j) + j·γ_{i+1} ) over the Φ_i-adic
  development; K_{i+1} := K_i[z]/(ψ_i). E_i := w_i(π) = e₀e₁⋯e_{i−1};
  γ̂_i := w_{i+1}(Φ_{i+1}).
* **The MacLane display.** w_{i+1} is EXACTLY MacLane's augmented value
  [e_i·w_i ; w_{i+1}(Φ_i) = γ_{i+1}]: the augmentation of the (rescaled)
  order-i valuation at its own key Φ_i, assigning Φ_i the strictly larger
  value γ_{i+1} > e_i·w_i(Φ_i) (h_i ≥ 1). This display is what closes the
  V24-G6 "owed correspondence" for (V1): the §1.1 chain of O-1thr IS the
  MacLane composite, now said with the augmentation exhibited (§5).
* **The three-term seam.** Three valuation-like objects appear at the
  carriers: **u** (the engine's [F.0] side valuation — an axiom of the stage
  interface, O-2a §4), **w** (the MacLane chain above — a mathematical
  object), **v_r** (GMN's order-r valuation, (L2)). This brief proves
  statements about w and about w = v (TIE); the u = w half is engine
  conformance (the intended proof routes of OL-2/OL-5/OL-6, owned by
  GD-4/GD-6 and the S-1 transcription audit) and is NOT claimed here. What
  IS proved here about u's axioms: they are SATISFIED by w (Corollary IFACE,
  §7.4) — "the engine's axiom holds at the GMN valuation" (SYNTH4 §1, GD-2
  note).
* **Index dictionary (a standing transcription hazard, displayed).** O-1thr's
  0-based reads vs GMN's 1-based orders: Φ_i ↔ φ_{i+1}, w_i ↔ v_{i+1},
  (e_i, h_i) ↔ (e_{i+1}, h_{i+1}), K_i ↔ F_{i+1}, ψ_i ∈ K_i[z] ↔
  ψ_{i+1} ∈ F_{i+1}[y]. Constants check: w_i(π) = E_i = e₀⋯e_{i−1} =
  e₁^{GMN}⋯e_i^{GMN} = v_{i+1}(π) — matching (L2)'s index e₁⋯e_{r−1} at
  r = i+1. O-2a's stage at level i+1 speaks GMN indexing (its constant test
  u_{i+1}(π) = E_i is the same number).

### 1.3 Graded vocabulary

For a function w : K[x]∖{0} → ℤ with w(AB) ≥ w(A) + w(B) and
w(A+B) ≥ min(w(A), w(B)) (a semivaluation): P_γ := {A : w(A) ≥ γ} ∪ {0},
P_γ⁺ := {A : w(A) > γ} ∪ {0}, gr(w) := ⊕_{γ∈ℤ} P_γ/P_γ⁺ (graded pieces over
K[x]; π̄ := in(π) is then invertible, since w(π^{−1}) = −w(π) makes
in(π)·in(π^{−1}) = in(1) = 1). in(A) := the class of A in gr_{w(A)}.
Facts used (displayed, elementary): (g1) if each w(x_j) = γ and
w(Σ x_j) > γ then Σ in(x_j) = 0 in gr_γ; (g2) w is a VALUATION
(w(AB) = w(A)+w(B) always) iff in(A)·in(B) = in(AB) ≠ 0 for all A, B, iff
gr(w) is a domain; (g3) ord_δ(α) := max{k : δ^k | α} is well-defined in a
domain for homogeneous δ of positive weight-or-degree data bounding the chain.

## 2. The merged statements (what GD-2 ⊕ GD-3 assert)

Fix a policy 𝒫 and a lawful chain of reads ν₀, …, ν_i building frames through
order i+1 as in §1.2, and let f ∈ O[x] be monic with the creating read ν_i
satisfying, on f, (R1) at all slots and (R2) at its strides (the standing
WGEO hypothesis of O-1thr §2.5 — side support with equality only at strides,
and exact digit pins at the strides; at a root state, ROOT-M's
ord_{φ̄}(f̄) = m ≥ 2 setting).

**GD-2 (frame/valuation tie + development identity).**
(a) each w_j (j ≤ i+1) is a valuation on K[x], ℕ-valued on O[x]∖{0}
    ((V1)); and w_j = v_{j+1}, GMN's order-(j+1) valuation over the same
    (policy-pinned) representatives — the engine ℤ-normalization being the
    SAME normalization (no rescaling; §1.2 index dictionary);
(b) the state key's development computes the state valuation from below:
    for every nonzero B ∈ K[x], with B = Σ_k C_k Φ_{i+1}^k the
    Φ_{i+1}-development, w_{i+1}(B) = min_k ( w_{i+1}(C_k) + k·γ̂_i ) ((V2b));
(c) hence the state window polygon — the lower hull of the sheared points
    (k, u_k), u_k := w_{i+1}(C_k) + k·γ̂_i, of f's Φ_{i+1}-development — IS
    GMN's N_{i+2}(f), vertex for vertex, and the (c1) side data
    (e, h, ℓ, s, u) of any principal side agree verbatim in the order-(i+2)
    integer frame.

**GD-3 (residual dictionary).** With ψ̂_hom := in(Φ_{i+1})·(unit monomial)^{−1}
the key initial form ((KPa)):
(min core) ord_{ψ̂_hom}(in(f)) = ord_{ψ_i}(R_λ(f)) — the level-i residual
    polynomial computes the ψ-order of the initial form ((V2c); all the recut
    cluster consumes, per V25's split);
(full form) the anchor-normalized stage residual satisfies
    R^{nrm} = c·R_λ(f), c ∈ K_i^× — the z-power twists of GMN Def 2.20 are
    absorbed exactly by the single anchor-unit division of [F.2];
(slot law, = O-9's OL-B) each stride's residual-coefficient read is
    (fixed unit twist)·(residue), a BIJECTION of K_i per slot; no un-cancelled
    z ↦ z^a, a ≥ 2, survives.

**Displayed inputs** (each with owner and proved perimeter):

* **(KP_j), j ≤ i (from GD-1, cumulative).** Φ_{j+1} is monic of degree
  e_j·g_j·deg Φ_j and: **(KPa)** in_{w_{j+1}}(Φ_{j+1}) = u·ψ̂_hom^{(j)} with u
  an invertible homogeneous element of gr(w_{j+1}), and ψ̂_hom^{(j)} ∤ in(B)
  for EVERY nonzero B ∈ K[x] with deg B < deg Φ_{j+1} (the minimality/degree
  block); **(KPb)** R_j(Φ_{j+1}) ∼ ψ_j (the Def-2.12 residual normalization).
  Proved perimeter: at j = 0 for the STANDARD lift at any d₀ — Theorem KEY-g
  (§3), extending O-1thr's KEY1 (d₀ = 1, ℤ_p). At the order-0 key itself the
  analogous block is FREE for any monic lift (Lemma GAUSS-g(iii)). Beyond:
  GD-1's business (GMN Thm 2.11/Def 2.12; MacLane Def 4.1).
* **(ML) MacLane Thm 4.2** (augmented values are valuations) — §5, pinned.
* **(T-1), (T-2)** — two GMN transcriptions, §6/§7, one in hand, one flagged.
* **(GR-B)** — the residue-structure package at orders ≥ 2, §7.2, cited
  (MacLane §§9–12; FGMN 2015) and proved at order 1 here.

## 3. The order-≤1 layer, proved outright over an arbitrary DVR at every d₀

**Lemma DEV-g (development congruence).** Φ ∈ O[x] monic of degree d ≥ 1;
B, B′ ∈ O[x] with B ≡ B′ (mod π^L). Then the Φ-adic developments have
c_j ≡ c′_j (mod π^L) for all j, and all c_j ∈ O[x].

*Proof.* Verbatim O-1thr Lemma DEV with ℤ_p → O: division with remainder by a
monic polynomial keeps O-coefficients, is O-linear in the dividend, and
commutes with reduction mod π^L (uniqueness of monic division over O/π^L);
induct along the development. ∎

**Lemma POS-g.** Each w_i of §1.2 satisfies on O[x]: (i) w_i(B) ≥ 0;
(ii) w_i(πB) = E_i + w_i(B); (iii) w_i(B + B″) ≥ min(w_i(B), w_i(B″)); and
w_i(AB) ≥ w_i(A) + w_i(B) (semivaluation). Consequently B ≡ B′ (mod π^L) ⟹
w_i(B − B′) ≥ L·E_i.

*Proof.* (i)–(iii) verbatim O-1thr Lemma POS (induction on i; DEV-g gives
integral development coefficients; γ_{i+1} > 0). Sub-multiplicativity: at
order 0 it is Gauss's content bound (below); the step is the §5 carry
computation's "≥" half, which uses only the inductive sub-multiplicativity —
displayed inside the proof of Theorem VAL-g, whose "≥" paragraph is stated
for arbitrary order i (it consumes only DEV-g + the induction hypothesis).
The consequence: B − B′ = π^L·C, C integral. ∎

**Lemma GAUSS-g (order-0 layer).** (i) w₀(B) = the plain Gauss valuation
(min coefficient valuation of B itself), independent of Φ₀. (ii) w₀ is a
valuation; gr_K(w₀) = F[X̄][π̄^{±1}] (X̄ := in(X) at weight 0, π̄ := in(π) at
weight 1), a Laurent-polynomial domain, indeed a UFD. (iii) For any monic
lift Φ₀ of an irreducible φ̄ of degree d₀: in(Φ₀) = φ̄(X̄), a prime of
gr_K(w₀), and φ̄(X̄) ∤ in(B) for every nonzero B ∈ K[x] with deg B < d₀.

*Proof.* (i) B ∈ π^L O[x] iff every development coefficient is in π^L O[x]
(⟸ clear; ⟹ DEV-g with B′ = 0), so the two minima agree. (ii) Gauss's
lemma over the domain F[X̄]: the weight-L piece of gr is π̄^L·F[X̄]
(clear denominators by units π̄^{−L}), and in(A)in(B) = in(AB) is the
statement that the product of the content-normalized reductions is the
reduction of the content-normalized product — nonzero since F[X̄] is a
domain. UFD: localization of the UFD F[X̄][π̄]. (iii) Φ₀ monic with
reduction φ̄ has w₀(Φ₀) = 0 and weight-0 class φ̄(X̄); φ̄(X̄) is prime
(irreducible in F[X̄], and π̄ is a unit); a nonzero multiple φ̄·δ has
X̄-degree ≥ d₀ in every graded piece, while in(B) has X̄-degree ≤ deg B < d₀.
∎

Fix now a root read ν₀ over Φ₀ with data (e, h) coprime ≥ 1, and write
w₁(B) = min_t ( e·w₀(b_t) + t·h ) over the Φ₀-development (γ₁ = h since
w₀(Φ₀) = 0). Write K₀ = F[X]/(φ̄) (= F_1^{GMN}, a field, q₀ := |K₀| when F
finite).

**Theorem VAL-g (order-1 valuation, any d₀, any O).** w₁ is a valuation on
K[x]; gr_K(w₁) ≅ K₀[π̄^{±1}][Φ̄₀] with π̄ := in(π) invertible of weight e,
Φ̄₀ := in(Φ₀) of weight h, and K₀ sitting in weight 0 as the classes of
coefficient polynomials (deg < d₀) of w₀-content 0; a UFD. Explicitly, for
A = Σ_t a_t Φ₀^t with S := {t : e·w₀(a_t) + t·h = w₁(A)}:
in(A) = Σ_{t∈S} [a_t]·π̄^{w₀(a_t)}·Φ̄₀^t, where [a_t] ∈ K₀ is the class of
a_t/π^{w₀(a_t)} mod (π, Φ₀) — nonzero for each t ∈ S.

*Proof.* (1) *Sub-multiplicativity with strictly heavier carries.* For
A = Σ a_t Φ₀^t, B = Σ b_s Φ₀^s: AB = Σ_{t,s} a_t b_s Φ₀^{t+s}, and each
a_t b_s (degree ≤ 2d₀ − 2) reduces as a_t b_s = c_{ts} + d_{ts}Φ₀ with
deg c_{ts} < d₀ and deg d_{ts} ≤ d₀ − 2 < d₀. By DEV-g (applied
to the dividend a_t b_s ∈ π^{w₀(a_t)+w₀(b_s)}O[x], using GAUSS-g(ii)'s
multiplicativity of w₀): w₀(c_{ts}), w₀(d_{ts}) ≥ w₀(a_t) + w₀(b_s). The
development of AB therefore has slot-r coefficient
Σ_{t+s=r} c_{ts} + Σ_{t+s=r−1} d_{ts}, every summand of w₁-weight
≥ e(w₀(a_t)+w₀(b_s)) + (t+s)h ≥ w₁(A) + w₁(B), and every CARRY summand
d_{ts} of weight ≥ w₁(A) + w₁(B) + h, strictly heavier. So
w₁(AB) ≥ w₁(A) + w₁(B).
(2) *The graded module.* Weight-γ classes: by slot uniqueness of the
development, a sum Σ_t π^{a_t}u_tΦ₀^t (u_t of content 0, ea_t + th = γ) has
w₁ > γ iff every [u_t] = 0; so gr_γ is the free K₀-module on the monomials
π̄^aΦ̄₀^t with ea + th = γ (a ∈ ℤ after clearing denominators by π-units,
t ≥ 0), and the displayed in(A) formula holds.
(3) *Ring structure.* Products of weight-0 coefficient classes multiply as
in K₀: a_tb_s = c_{ts} + d_{ts}Φ₀ gives, modulo (π, Φ₀),
[c_{ts}] = [a_t][b_s] — the field product — while the carry term d_{ts}Φ̄₀
lands in strictly higher weight by (1) and so vanishes in the graded piece.
Hence gr(w₁) ≅ K₀[π̄^{±1}][Φ̄₀] as a graded ring: a domain, a UFD
(localization of a polynomial ring over a field).
(4) *Multiplicativity.* By (2)/(3), in(A) and in(B) are nonzero elements of
a domain; the weight-(w₁A + w₁B) part of AB's development is, by (1)'s
bookkeeping, exactly the polynomial product in(A)·in(B) ≠ 0. So
w₁(AB) = w₁(A) + w₁(B). ∎

**Theorem KEY-g (standard first key, any d₀, any O).** Let ψ ∈ K₀[z] be
monic irreducible of degree g with ψ(0) ≠ 0, ψ̂_κ ∈ O[x] (deg < d₀) fixed
lifts of its coefficients (ψ̂_g = 1), and
Φ₁ := Σ_κ ψ̂_κ · π^{(g−κ)h} · Φ₀^{eκ} — the standard key lift. Then:
(i) Φ₁ is monic of degree e·g·d₀, every nonzero monomial of w₁-weight
exactly egh, and w₁(Φ₁) = egh with
in(Φ₁) = ψ_hom := Σ_κ [ψ_κ]·π̄^{(g−κ)h}·Φ̄₀^{eκ}, the (e,h)-homogenization
of ψ; (ii) ψ_hom is PRIME in gr_K(w₁), and ψ_hom ∤ in(B) for every nonzero
B ∈ K[x] with deg B < egd₀ — i.e. (KPa) holds at j = 0, u = 1; (iii) for f
satisfying the read's (R1)/(R2) at a side (e, h, s0, d) with residual
R_λ(f) ∈ K₀[z]: ord_{ψ_hom}(in(f)) = ord_ψ(R_λ(f)) — GD-3's min core at
order 1.

*Proof.* (i) Weight of the κ-monomial: e·((g−κ)h + w₀(ψ̂_κ)) + eκ·h = egh
when ψ_κ ≠ 0 (w₀(ψ̂_κ) = 0). Degrees: the κ = g term is Φ₀^{eg}, degree
egd₀, monic; lower terms have degree < egd₀. So in(Φ₁) is the displayed sum
(all monomials at one weight; classes [ψ_κ]).
(ii) The homogenization map hom_{e,h} : c(z) = Σ c_κ z^κ (deg = g′, c ∈
K₀[z]) ↦ Σ_κ c_κ π̄^{(g′−κ)h}Φ̄₀^{eκ} is multiplicative
(hom(c)hom(c′) = hom(cc′): exponents add slot-wise) and injective. Every
homogeneous δ ∈ gr_K(w₁) factors as π̄^a·Φ̄₀^b·hom(c) with c(0) ≠ 0:
collect the least Φ̄₀-exponent b; the remaining exponents lie on one
(e,h)-lattice line (gcd(e,h) = 1: from ea + th = const, t is determined
mod e), giving the hom-shape. Now suppose ψ_hom = δδ′: since Φ̄₀ ∤ ψ_hom
(the κ = 0 term [ψ₀]π̄^{gh} ≠ 0, as ψ(0) ≠ 0) and ψ_hom has a
π̄-unit-free top term Φ̄₀^{eg} (monic), the monomial prefactors of δ, δ′
are units π̄^a, and ψ_hom = π̄^{a+a′}hom(cc′) forces cc′ = ψ up to a
K₀^×-scalar (injectivity), so c or c′ is a scalar: δ or δ′ is a unit.
Irreducible + UFD ⟹ prime. Degree block: deg B < egd₀ ⟹ the
Φ₀-development of B has top slot t ≤ ⌊deg B/d₀⌋ < eg, so in(B) has
Φ̄₀-degree < eg; any nonzero multiple ψ_hom·δ has Φ̄₀-degree ≥ eg (top
Φ̄₀-degrees add in the domain).
(iii) By (R1)/(R2), the w₁-minimizing slots of f's development are exactly
the on-line strides of the side, with digit classes the residual
coefficients c_κ = [b_{s0+eκ}/π^{ℓ(s0+eκ)}] (GMN (L3)'s order-1
coefficients, K₀-valued, 0 above the line): so by VAL-g's in-formula,
in(f) = Φ̄₀^{s0}·π̄^{β}·hom_{e,h}(R_λ(f)), β := the side's right-end
height. π̄ is a unit; Φ̄₀ ∤ ψ_hom and ψ_hom ∤ Φ̄₀; and
ord_{ψ_hom}(hom R) = ord_ψ(R): hom is multiplicative, and if
ψ_hom·δ = hom(R′) with R′(0) ≠ 0 then δ's monomial prefactor is trivial
(match Φ̄₀-floors and top terms as above), so δ = π̄^a·hom(c) and
ψ·c = R′ up to scalar. Hence ord_{ψ_hom}(in f) = ord_ψ(R_λ(f)). ∎

**Theorem RES-1 (order-1 residual dictionary, full form; OL-B at order 1).**
In the setting of KEY-g(iii): (a) the FULL residual identity holds at order
1: reading the stride digits of f through the graded monomials —
c_κ = [b_{s0+eκ}/π^{ℓ(s0+eκ)}] — gives R(z) := Σ_κ c_κ z^κ = R_λ(f)
EXACTLY (GMN's (L3) order-1 residual; no twists: "the z-power normalizations
of Def 2.20 enter at orders ≥ 2 only"), and any anchor-unit normalization
([F.2] with e_b = 1, 𝒟 = K₀) changes it by a c ∈ K₀^× only; (b) per slot,
the digit read b ↦ [b/π^ℓ] is (unit twist = 1)·(residue map), a bijection
from the on-line digit classes onto K₀ ∖ {0} extended by 0 above the line —
OL-B's order-1 instance, with NO z ↦ z^a map anywhere in the chain.

*Proof.* (a) is KEY-g(iii)'s display read off (the identification is
definitional once the in-formula is proved; scalar freedom is GMN's own "∼",
scope remark (4) of O-2a). (b) the slot map is x ↦ x·π^{−ℓ} followed by
reduction mod (π, Φ₀): a composition of a unit scaling and the residue
map onto the field K₀ — bijective on classes; the exponent map on digits is
the identity. ∎

*Remarks.* (1) VAL-g/KEY-g at d₀ = 1 over ℤ_p are verbatim O-1thr's
VAL1/KEY1 (𝔽_p[x̄, p̄] localized); the falsifier (§9) exercises exactly the
NEW perimeter (d₀ = 2; equal characteristic). (2) SYNTH4's GD-5 note
predicted "the weighted-Gauss ring becomes F_{p^g}[x̄, p̄] via the unramified
track extension"; the proof above shows one does not even need the
unramified-extension detour — the coefficient field K₀ emerges inside the
graded ring directly, over any O. (3) KEY-g(iii) + RES-1 discharge the
MATHEMATICAL content of O-2a's OL-5 (b′)+(c′) (the order-1 base of GD-5's
composition note): a base read performed by the displayed formulas emits
verbatim (c1)/(c2) — the remaining OL-5 content is engine conformance, per
§8.

## 4. Theorem DEVID — the development identity at every order

**Theorem DEVID.** Let w be a valuation on K[x] ((V1) at the state order),
Φ ∈ O[x] monic such that in(Φ) = u·ψ̂ with u invertible homogeneous and
ψ̂ ∤ in(B) for every nonzero B ∈ K[x] with deg B < deg Φ ((KPa)). Then for
every nonzero B ∈ K[x], with B = Σ_k C_k Φ^k the Φ-adic development:

    w(B) = min_k ( w(C_k) + k·w(Φ) ),

i.e. (V2b) holds at the state: the state key's development computes the
state valuation from below, with γ̂ = w(Φ).

*Proof.* "≥": ultrametric + multiplicativity: w(B) ≥ min_k w(C_kΦ^k) =
min_k (w(C_k) + k·w(Φ)) =: u₀. Suppose w(B) > u₀ and let
S := {k : w(C_k) + k·w(Φ) = u₀} (nonempty; each C_k ≠ 0 for k ∈ S),
m := min S. By (g1)+(g2) of §1.3, Σ_{k∈S} in(C_k)·in(Φ)^k = 0 in gr_{u₀}.
Substitute in(Φ) = u·ψ̂ and factor (gr is a domain, u invertible):

    0 = ψ̂^m · ( Σ_{k∈S} in(C_k)·u^k·ψ̂^{k−m} ),

so the bracket vanishes; isolating its k = m term,
in(C_m)·u^m = −ψ̂·( Σ_{k∈S, k>m} in(C_k)·u^k·ψ̂^{k−m−1} ), whence
ψ̂ | in(C_m) — contradicting (KPa)'s block at C_m (nonzero, of degree
< deg Φ). ∎

**Corollaries.**

* **(S-K1) instantiated.** The stage interface's axiom
  u(f) = min_j (u(B_j) + j·u(Φ̂)) (O-2a §4 [F.0]) HOLDS at u := w_{i+1},
  Φ̂ := Φ_{i+1}, at every order where (V1)+(KPa) hold — one of the two
  IFACE clauses (§7.4).
* **DIV1 retired; the V24-G4 caveat moot.** O-1thr's DIV1 proved this at
  order 1, d₀ = 1, by a Φ₀-adic slot-chase whose general-lift form was a
  pass-3 repair site (V24 G4: the reduction step is "not weight-graded when
  the policy's root key is Φ₀ = X − a"). The graded proof above never sees
  the shape of any lower key — only (V1) and (KPa) — so it covers every
  order, every d₀, every O at once, and DIV1 survives only as the order-1
  corroboration of a special case.
* **Corollary VTX's deeper leg supplied.** O-1thr's Corollary VTX needed, at
  deeper harvests, exactly "e_i·w_i(C_{μ′}) ≤ w_{i+1}(C_{μ′}), i.e. that
  C_{μ′}'s Φ_i-development computes w_i from below — the development
  identity (V2b) at level i". DEVID at level i (given (V1)_i + (KPa)_{i−1})
  is that statement. (Note the level-i instance consumed there is DEVID at
  the PARENT key: w_i with Φ_i, i.e. (KPa) one level down — the cumulative
  reading of (KP), matching OL-1's joint induction.)
* **WGEO re-founded.** O-1thr's Lemma WGEO consumes (V1), (V2a) = (KPa),
  (V2b) = DEVID, (V2c) = GD3-MIN. With this brief, WGEO's status at every
  order becomes: PROVED given (KP) at the state plus GD3-MIN's route pin —
  the (V1)/(V2) bundle is no longer an undifferentiated citation; its owed
  normalization dictionary (V24-G6, seam S-4) is §§4–7 of this brief.

## 5. (V1) at every order: the MacLane pin

**Proposition V1-tower.** (a) w₀ and w₁ are valuations over any O, any d₀
(GAUSS-g, VAL-g — proved). (b) For i ≥ 1: IF Φ_i is a MacLane key
polynomial for the valuation e_i·w_i (Def 4.1: monic, w_i-minimal,
w_i-irreducible — supplied by GD-1's (KP_{i−1}) package: (KPa)'s block IS
minimality in graded form, and primeness of ψ̂_hom is irreducibility) and
γ_{i+1} > e_i·w_i(Φ_i) (true: h_i ≥ 1), THEN
w_{i+1} = [e_i·w_i ; w(Φ_i) = γ_{i+1}] is a valuation. [MacLane, *A
construction for absolute values in polynomial rings*, Trans. AMS 40 (1936),
363–395: Definition 4.1 (key polynomials), Theorem 4.2 (augmented values are
values) — loci per the V24 literature check, carried from O-1thr rev 4.
Scaling remark: e_i·w_i is a valuation with the same key polynomials and
graded ring (re-graded), so augmenting the rescaled valuation is inside
Thm 4.2's scope.]

**Scope flag (ML-scope), owed to the §3.2-step-4 literature unit.** MacLane's
standing hypotheses are a field with a discrete rank-one valuation — which
covers every K = Frac(O) here, mixed or equal characteristic, with NO
completeness or residue-field hypothesis (this is what makes the
arbitrary-DVR statement free). The exact standing-hypothesis sentence of the
1936 paper must be confirmed verbatim at the literature session; if MacLane's
printed scope is narrower, the fallback pin is Vaquié, *Extension d'une
valuation*, Trans. AMS 359 (2007) (arbitrary valued fields), at the cost of
a normalization audit. FLAGGED, not assumed silently.

Status: (V1) is thus PROVED at orders ≤ 1 (any O, any d₀), and at every
higher order is the composite (KP_{i−1}) [GD-1] + MacLane Thm 4.2 [pinned,
one scope flag]. No other input.

## 6. The tie w = v (GD-2(a) second half) and the record dictionary (GD-2(c))

**Lemma UNIQ (proved).** Let ν, ν′ : K[x]∖{0} → ℤ both satisfy, for a fixed
monic Φ of degree D ≥ 1: (u1) ν = ν′ on {B ≠ 0 : deg B < D} and
ν(Φ) = ν′(Φ); (u2) both are computed by the Φ-development min formula
ν(B) = min_j ( ν(b_j) + j·ν(Φ) ). Then ν = ν′.

*Proof.* Immediate: the development is unique and both sides are the same
min of identical numbers. ∎

**Theorem TIE.** At GMN's scope (K/ℚ_p finite; F finite) and under the
policy pin (the engine/O-1thr keys Φ₀, …, Φ_{i+1} ARE the GMN
representatives φ₁, …, φ_{i+2} of the truncated types — GD-1/OL-1(b)
territory, a displayed hypothesis here): w_j = v_{j+1} on K[x]∖{0} for
every j ≤ i+1, in the SAME ℤ-normalization (no rescaling; constants check
in §1.2). Consumed GMN properties, each displayed:

* (P-base) v₁ = the Gauss valuation on developments — pinned, O-2a (L2)
  [Def 2.5 / Prop 2.6 transcription, verified through O-2a's five rounds];
* (P-key) v_{j+2}(φ_{j+1}) = h + e·v_{j+1}(φ_{j+1}) — pinned, O-2a (L4)
  [Prop 2.7, as used in the proof of Prop 2.15]; equals γ_{j+1} under the
  induction hypothesis;
* **(T-1) [FLAGGED transcription]:** v_{j+2}(b) = e_{j+1}^{GMN}·v_{j+1}(b)
  for deg b < deg φ_{j+1}, and v_{j+2}(P) = min over the φ_{j+1}-development
  of v_{j+2}(b_k φ_{j+1}^k) — i.e., GMN's Def-2.5 valuation is computed by
  the current-key development with the rescaled coefficient values. This is
  the reading of "v_r(P) := e_{r−1}·H_{r−1}(S_{r−1}(P))" as the
  side-intercept of the order-(r−1) polygon in e_{r−1}-cleared units; it
  must be confirmed verbatim at the literature session (§11). Everything
  about the tie EXCEPT this one display is either proved here or already
  pinned.

*Proof (given the pins).* Induction on j. Base: w₀ = Gauss = v₁ (GAUSS-g(i)
+ (P-base)). Step: by §1.2's computation, w_{j+1} satisfies UNIQ's (u2) at
Φ_j with coefficient values e_j·w_j(b) (= w_{j+1}(b) on deg < deg Φ_j: the
slot-0 development) and key value γ_{j+1} = w_{j+1}(Φ_j). By (T-1) and
(P-key), v_{j+2} satisfies (u2) at φ_{j+1} = Φ_j with coefficient values
e·v_{j+1}(b) = e_j·w_j(b) (induction hypothesis + index dictionary) and the
same key value. UNIQ finishes. ∎

**Corollary REC-c1 (GD-2(c)).** In the TIE's setting, at the order-(i+1)
state with key Φ_{i+1}: the sheared window points of f,
(k, u_k) with u_k := w_{i+1}(C_k) + k·γ̂_i over the Φ_{i+1}-development,
are EXACTLY GMN's N_{i+2}(f) points (k, v_{i+2}(C_k φ_{i+2}^k)) — the same
numbers, term by term (v_{i+2} = w_{i+1} by TIE one level up;
v_{i+2}(φ_{i+2}) = γ̂_i). Hence: the window polygon IS N_{i+2}(f) as a
subset of ℝ², vertex for vertex and side for side; every principal side's
(e, h, ℓ) are the lowest-terms slope pair and degree of the corresponding
side of N_{i+2}^−(f); and (s, u) — its initial point — is the pair pinned
by (c1)'s positional clause in the order-(i+2) integer frame. At a root
state the same holds with i+1 = 0 against N₁(f) (w₀ = v₁, γ̂ = 0). By
DEVID, moreover, these points compute w_{i+1}(f) from below — the polygon
is drawn at the honest heights.

*Two displays riding REC-c1.* (1) **The mathematical content of GD-2(c) is
exhausted by TIE + DEVID** — no residual geometry statement remains open on
the math side. What OL-2(b) additionally asserts (the ENGINE's emitted
record equals this data, any internal offset inverted before emission) is
engine conformance: exactly where the corpus's compiled stretch
countermodel lives (HK52: a naive engine-internal vertex transport fails by
a factor-e′ stretch at e′ ≥ 2). The merged GD-2 keeps OL-2(b)'s typing AT
THE EMITTED RECORD for precisely this reason; the HK52 gate remains the
standing GD-2(c) trap for the engine-side units (§8, §9). (2) The
V-recursion clause of SYNTH4's GD-1(c), V_{i+1} = e_i f_i (e_i V_i + h_i),
is the (P-key) pin composed with (KP)'s degree law — recorded here so the
GD-1 unit can consume the tie without re-deriving it.

## 7. GD-3 at general order

### 7.1 The consumption split (per V25)

The recut cluster (K-RUN-C/K-RUN-BOX; O-2a Theorem 2(D); WGEO(b)) consumes
ONLY the min core. The value side (O-9's census → O-11's tables) consumes
the full form and OL-B. The two get different treatment below — min core:
two independent routes, one flagged pin each; full form: one route, through
the displayed (GR-B).

### 7.2 The displayed input (GR-B) — the carry-algebra realization

**(GR-B) [side-residual structure at state order i+1 ≥ 2; OPEN here; cited].**
Given (V1)/(KP) through the state: write w := w_{i+1}, ψ̂ := ψ̂_hom^{(i)}
(the creating read's key initial form, prime by (KPa)), λ := −h_i/e_i.
There exists a residual operator R^{gr} from the nonzero SIDE-SUPPORTED
homogeneous elements of gr_K(w) (sums over one (e_i, h_i)-stride lattice
line of stride monomials times coefficient initial forms) to K_i[z]∖{0}
with:
(1) R^{gr}(α·β) = θ_{α,β}·R^{gr}(α)·R^{gr}(β), θ_{α,β} ∈ K_i^×;
(2) for f with the creating read's (R1)/(R2): R^{gr}(in f) ∼ R_λ(f), GMN's
    Def-2.21 residual (level-i read; index dictionary §1.2), and slot-wise
    the κ-th coefficient of R^{gr}(in f) is
    (fixed invertible twist τ_κ)·(the K_i-residue of the κ-th stride digit)
    — τ_κ from a distinguished system of invertible homogeneous monomial
    elements realizing the digit algebra 𝒟 = K_i-span of u_ρ with
    u_ρu_σ = ζ^{⌊(ρ+σ)/e_b⌋}u_{ρ+σ} ([F.0]'s carry algebra; e_b the birth
    index, ζ the distinguished unit);
(3) R^{gr}(ψ̂) ∼ ψ_i ((KPb) transported);
(4) faithfulness at ψ: ψ̂ | α ⟺ ψ_i | R^{gr}(α).
Citations: MacLane 1936 §§9–12 (residue rings of augmented values — the
structure theorem that the degree-0 localized graded ring is a polynomial
ring over the tower field; exact theorem numbers FLAGGED, §11);
J. Fernández, J. Guàrdia, J. Montes, E. Nart, *Residual ideals of MacLane
valuations*, J. Algebra 427 (2015) 30–75 (the residual polynomial operator
attached to an inductive valuation: multiplicativity, key dictionary;
exact proposition numbers FLAGGED; scope: arbitrary discretely valued
fields — which would carry the arbitrary-DVR claim at orders ≥ 2);
corroborating GMN pin (VERIFIED, `GMN_citations.md`): Thm 2.26 (Theorem of
the product): N_r^−(fg) = N_r^−(f) + N_r^−(g) and
R_λ(fg) ∼ R_λ(f)·R_λ(g) — clause (1)+(2)'s composite at GMN's own
normalization. **Proved at order 1 by RES-1** (there e_b = 1, 𝒟 = K₀,
every τ_κ = 1, R^{gr} = hom_{e,h}^{−1} after clearing the anchor monomial —
all four clauses read off KEY-g/RES-1).

### 7.3 The theorems

**Theorem GD3-MIN (min core, general order).**
ord_{ψ̂}(in f) = ord_{ψ_i}(R_λ(f)), under EITHER of:
* **Route A (no GR-B):** TIE + the flagged pin **(T-2)**: for P of type t
  (order i+1, GMN indexing) with representative φ_{i+2}, the principal part
  of N_{i+2}(P) — including the slope-−∞ side — has length
  ω_{i+2}(P) = ord_{ψ_{i+1}^{GMN}}(R_{i+1}(P)) [candidate locus: the lemma
  displayed with Defs 2.19–2.21 (Lemma 2.17 in the arXiv text); exact
  number owed to the literature unit]. Given (T-2), the first attainment of
  min_k u_k is at k = ω = ord_ψ(R_λ f) (REC-c1: the u_k ARE the N-heights);
  and by DEVID + the WGEO(b) factorization (O-1thr §2.5, verbatim: gr a
  domain + (KPa) block), the first attainment is at ord_{ψ̂}(in f). Equate.
* **Route B (no completeness, any O):** (GR-B). Write in(f) = ψ̂^m·β with
  ψ̂ ∤ β (m := ord, well-defined: gr a domain, §1.3 (g3)). Apply R^{gr}:
  by (1)+(3), R^{gr}(in f) ∼ ψ_i^m·R^{gr}(β), and ψ_i ∤ R^{gr}(β) by (4).
  So ord_{ψ_i}(R^{gr}(in f)) = m; by (2), R^{gr}(in f) ∼ R_λ(f). ∎
Route A inherits GMN's scope and completeness; Route B inherits (GR-B)'s.
Either alone suffices for the cluster.

**Theorem GD3-FULL + OL-B (general order, from (GR-B)).** Given (GR-B):
(full) the anchor-normalized residual R^{nrm} — divide the stride
coefficient vector of in(f) by the anchor unit τ-datum u_{ρ₀} ([F.2]) —
satisfies R^{nrm} = c·R_λ(f), c ∈ K_i^×: clause (2) says each slot κ reads
(τ_κ)·(residue), and the τ-system's carry law makes the single anchor
division absorb ALL slot twists up to one global K_i^×-constant (the
z-power twists of GMN Def 2.20 are exactly the τ_κ-ratios; their
un-absorbed residue would violate (2)'s "fixed invertible twist per slot").
(OL-B) each slot map is (fixed unit twist)·(residue): a bijection of K_i
per slot; in particular no z ↦ z^a (a ≥ 2) survives anywhere in the
evaluation chain — the exponent map on digits is the identity, slot-wise.
*Proof.* Both are re-readings of (2)'s slot form plus the multiplicativity
of the τ-system; at order 1 they are RES-1 (proved). At orders ≥ 2 the
content sits entirely inside (GR-B), which is why the full form is priced
AT (GR-B) and not below it. ∎

### 7.4 Corollary IFACE (the stage-interface instantiation)

The engine's stage-interface axiom package (O-2a §4, [F.0]–[F.2]) is
SATISFIED by the MacLane/GMN valuation: take u := w_{i+1},
Φ̂_{i+1} := Lift_i(c) = Φ_{i+1}, dig := the graded digit read through the
τ-system, 𝒟 := the (GR-B) carry algebra. Then: u is ℤ-valued,
multiplicative, ultrametric ((V1)); (S-K1) holds (DEVID); the stage window
polygon of f is N_{i+2}(f) (REC-c1); [F.1]'s stage residual is R_λ(f) up to
the [F.2] anchor normalization (GD3-FULL; at order 1, RES-1 outright, with
𝒟 = K₀ trivial). So every engine lemma quantified over the interface
(OL-2-min/OL-3-min/OL-5's mathematical halves) is INSTANTIABLE at w — "the
engine's axiom holds at the GMN valuation" (SYNTH4 GD-2 note) — and the
entire remaining gap between the carriers' u and this w is engine
conformance, priced in §8.

## 8. Consumption map (every carrier of the two families, served or re-priced)

| carrier (exact label) | what this brief supplies | residue left at the carrier |
|---|---|---|
| O-1thr (V1) | proved order ≤ 1 (any d₀, any O); MacLane display + pin beyond (§5) | (KP) [GD-1]; ML-scope flag |
| O-1thr (V2)(a) | = (KPa): proved at order 1/standard lift, any d₀ (KEY-g) | GD-1 beyond |
| O-1thr (V2)(b) | **PROVED at every order** given (V1)+(KPa) (DEVID) — the owed dictionary closed | — |
| O-1thr (V2)(c) | order 1 proved (KEY-g(iii)); general: Route A (T-2 flag) or Route B (GR-B) | T-2 or (GR-B) |
| O-1thr Cor VTX deeper leg ("(V2b) at level i") | DEVID at level i | (KP) cumulative |
| O-1thr WGEO/(M6c) beyond the proved slice | its four named inputs now individually priced (§4 corollary) | (KP), GD3-MIN pin |
| O-2a OL-2(a) [u_{i+1} = v_{i+1}] | the w = v half (TIE, mod T-1); u = w re-priced as engine conformance via IFACE | T-1 flag; engine seam (GD-4/6/S-1) |
| O-2a OL-2(b)–(d), OL-2-min | REC-c1 (math half, verbatim (c1)); emitted-record typing kept, HK52 trap displayed | engine seam |
| O-2a OL-3 (full) / OL-3-min | GD3-FULL from (GR-B) / GD3-MIN two routes; order 1 outright (RES-1) | (GR-B) resp. T-2-or-(GR-B); engine seam |
| O-2a OL-5 (b′)+(c′) | mathematical half proved (KEY-g(iii)+RES-1 = the (D3) formulas' semantics, over any O) — GD-5's composition-note input | engine seam (S-1 audit) |
| O5triple (I-1)(a) legs "through OL-2a-2/3" | supplied at the dictionary level by REC-c1 + GD3-MIN | as OL-2/OL-3 above |
| O3design JC-2 / JC-3 | = GD-2 / GD-3 as restated here (the units' targets) | the units consume this brief |
| O-9 OL-B | general form from (GR-B); order-1 instance proved | (GR-B) |
| D-3 / UNRAM-TRANSFER; O-8b (R1)–(R4) scope | KILLED as a separate node: every proved statement holds over O_δ = W(F_{p^δ}) as an instance (§1.1) | O-8b's engine-side clauses only |
| (V1)/(V2) "owed normalization dictionary" (V24-G6, seam S-4) | §§1.2, 4–7 ARE the dictionary (MacLane display, index dictionary, TIE, residual routes) | T-1/T-2/ML-scope flags |

**Not claimed anywhere in this brief:** any statement about the implemented
engine's emitted records (u = w); OL-1/(KP) beyond order 1; OL-4/OL-6
(bookkeeping families GD-4/GD-6); exhaustiveness/drainage; anything about
boxes or runs. The brief is a statement about valuations, keys, polygons,
and residuals only.

## 9. Falsifier record (run before writing; falsifier-first)

`verification/openmath/gd23_check.py` (this unit; exact arithmetic, seed
pinned). Perimeter chosen to be exactly what T-E/T-F did NOT cover: root
keys of degree d₀ = 2, and the equal-characteristic base O = F_p[[t]]
(the arbitrary-DVR claim), with lifts carrying genuine t-noise
(Φ₀ = X² + (φ̄₁ + t)X + φ̄₀). Configurations: (ℤ₂, X²+X+1), (ℤ₃, X²+1),
(F₂[[t]], X²+X+1), (F₃[[t]], X²+1). Per sampled monic f realizing a root
read (ord_{φ̄}(f̄) = m ∈ {2,3,4}, random π-power digits, beyond-window
slots included):

* GAUSS-g: development-min = plain content (asserted on every sample);
* VAL-g: w₁(AB) = w₁(A) + w₁(B) — **2,622 random pairs, 0 violations**;
* A-law (WGEO(a) display): w₁(f) = e·u₀ + s₀·h at every harvested side —
  **1,910 sides, 0 violations**;
* KEY-g: standard lift monic of degree e·g·d₀, every monomial of w₁-weight
  egh, w₁(Φ₁) = egh — **2,115 keys** (every monic irreducible factor ψ of
  every side residual over F_{p²}, complete factorization), **0 violations**;
* DEVID + GD3-MIN: min_k (w₁(C_k) + k·egh) over the Φ₁-development equals
  w₁(f), AND first attainment at k = ord_ψ(R_λ(f)) — **2,115 instances, 0
  violations**.

Standing traps carried from the corpus (not re-run here, cited as gates):
T-E (33,043 depth-1) and T-F (41,720 depth-2, d₀ = 1) already exercise
DEVID/GD3-MIN's consequences at order 2 over ℤ_p — T-F's "7,472 violations
of the UNsheared reading" is the live countermodel showing the §1.2
convention is load-bearing; the HK52 compiled stretch gate
(`HC2/HK52_stretchGate.lean`) is the standing engine-side GD-2(c) trap.
Queued next (the SYNTH4 falsifier plan): the depth-3 harness and a d₀ ≥ 2
DEPTH-2 harness (order-2 states over degree-2 root keys — would exercise
(GR-B)'s order-2 instance and Route B's clauses numerically).

## 10. Honesty ledger (exact conditionality; where to attack)

**Proved outright here (any O; perfectness/completeness unused):** DEV-g,
POS-g, GAUSS-g, VAL-g, KEY-g, RES-1, DEVID, UNIQ, and the reductions
(GD3-MIN Route B given (GR-B); GD3-FULL/OL-B given (GR-B); IFACE's (S-K1)
and u-mult clauses).

**Proved modulo pinned-but-flagged transcriptions:** TIE (T-1), REC-c1
(rides TIE), GD3-MIN Route A (T-2), V1-tower beyond order 1 (ML-scope).
Each flag is a SINGLE displayed sentence to confirm against the printed
source — no mathematical gap is hidden behind them, and each names its
candidate locus.

**Open (the unit's honest residue):** (GR-B) at orders ≥ 2 — ONE package,
cited (MacLane §§9–12; FGMN 2015), proved here at order 1; it carries
GD3-FULL, OL-B, and one of GD3-MIN's two routes. Plus the inputs owned
elsewhere: (KP) = GD-1 beyond order 1; every engine-conformance statement
(GD-4/GD-6/S-1).

**Attack here first:** (1) DEVID's use of (g1)/(g2) — check the graded
bookkeeping does not smuggle multiplicativity where only
sub-multiplicativity is available (the theorem's hypothesis is "(V1) at the
state", so gr IS a domain there; verify no consumer fires DEVID at an order
where (V1) is not yet supplied). (2) VAL-g step (3): the claim that the
carry term ALWAYS lands strictly higher rests on h ≥ 1 — check the h = 0
degenerate is excluded by (N1) everywhere the theorem is consumed. (3)
KEY-g(ii)'s hom-descent at gcd(e,h) = 1 — check the lattice-line argument
at e = 1 and at h multiple of e·(...) corners. (4) TIE's index dictionary
(§1.2) — off-by-one hazards are this seam's known failure mode. (5) The
(GR-B) formulation — is clause (4) (faithfulness) really what FGMN's
operator provides, or does their statement give only (1)–(3)? If only
(1)–(3), Route B needs an extra prime-avoidance argument; Route A is
unaffected. (6) Whether GD3-MIN Route A's (T-2) statement matches the
FIRST-attainment form consumed (WGEO(b)'s "at NO k < μ"), not merely the
length of the principal part.

## 11. Literature pins (single list; status per pin)

* MacLane, *A construction for absolute values in polynomial rings*, Trans.
  AMS 40 (1936) 363–395. Def 4.1 (key polynomials), Thm 4.2 (augmented
  values are values) — loci per the V24 literature check [IN HAND];
  standing-scope sentence [ML-scope FLAG]; §§9–12 residue-ring structure
  for (GR-B) [numbers FLAGGED].
* GMN, Trans. AMS 364 (2012) 361–416 (arXiv:0807.2620v2 numbering;
  printed-TAMS caveat per `GMN_citations.md`). Def 2.5/Prop 2.6 (v_r)
  [transcribed, O-2a (L2)]; Prop 2.7 (key value recursion) [pinned, (L4)];
  Thm 2.11/Def 2.12 (representatives) [pinned; GD-1's input]; Defs
  2.19–2.21 (residuals) [pinned]; **Thm 2.26 (Theorem of the product)
  [VERIFIED verbatim in `GMN_citations.md`]**; T-1 (development computes
  v_r) [FLAG]; T-2 (principal length = ω) [FLAG; candidate Lemma 2.17].
* Fernández–Guàrdia–Montes–Nart, *Residual ideals of MacLane valuations*,
  J. Algebra 427 (2015) 30–75 — the residual polynomial operator and graded
  structure over arbitrary discretely valued fields; the natural home of
  (GR-B) [proposition numbers + scope FLAGGED FOR LOOKUP].
* Vaquié, *Extension d'une valuation*, Trans. AMS 359 (2007) — fallback for
  ML-scope only.

— GD23 rev 0. Verification protocol: hostile fresh-context pass with the §10
attack list + the standard charge (quote-and-classify; check every "proved"
against its displayed perimeter; check no consumer of §8's table is promised
more than the status table of §0 grants).
