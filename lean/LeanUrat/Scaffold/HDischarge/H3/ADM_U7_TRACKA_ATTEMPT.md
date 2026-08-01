# ADM-U7 — track A's kernel (iii): floor clearance vs class-weight clearance at realized reads — Phase-B attempt note (Fable prover ADM-U7, HDISCHARGE_H3 division, 2026-08-01)

**Charge** (`lean/blueprints/HDISCHARGE_H3.md` §1.3(c) track A + §1.4 ADM-U7,
§4 row ADM-U7): phase-B attempt on THE OPEN KERNEL (iii) — "floor clearance
⟹ class-weight clearance at realized reads" — against the (ZC-a)/LED-top
displays, outer quantifiers per §1.3(c). Open math, doc unit; no Lean
statement exists for it in the blueprint (the §1.3(c) math statement IS the
statement of record; no downstream Lean unit is scheduled). Hostile pass
owed on completion — this note is the artifact to hand it.

**Contingency status at dispatch (must be said first).** The unit was
dispatched "CONTINGENT on G-ADM-2 = all-full". G-ADM-2 has NOT run: no
runner, no `gadm2_attainment_*.jsonl`, no `GADM2_DISPOSITION.md` exist
(checked 2026-08-01; ADM-U5 delivered the instrumentation SPEC only, per its
own non-goals). This note proceeds under the charge's own gloss — "no-hit
supports only; the hostile pass is the gate (finding 7)" — and, as it turns
out, PREDICTS G-ADM-2's outcome and shows the router's disposition semantics
need a repair before it runs (§6).

---

## 0. Verdict up front

The statement of record ((ADM-REAL), quantifiers displayed verbatim in §1)
is **REFUTED as displayed and PROVED after one slot is carved out** — and
the carved-out slot is exactly the slot the consumed census never charges.
Specifically:

* **(NON-END, proved here, §3):** for EVERY census datum D over EVERY type t
  of EVERY order r ≥ 0 — abstract, any n, p (wild included), N, no
  realization input beyond β_{k_s} ≥ 0 at the chain's right end — every
  on-line slot k ≠ k_s satisfies β_k ≥ V̂ + 1 > V̂ − w(φ₁) ≥
  max_𝐣 wt(𝐣) ≥ max{wt(𝐣) : wt(𝐣) ≡ β_k (mod e)}. Clearance holds with
  margin ≥ 1 + w(φ₁) ≥ 2. The blueprint's sketch — transport the (ZC-a)
  floor through the frame and compare with the LED-top/V̂ layer — is
  BYPASSED: two elementary lattice lemmas (slot descent + a weight cap from
  the pinned V-recursion) close every non-right-end slot with no engine
  input at all.
* **(REFUTATION at k_s, §4–5):** at the chain's right-end slot k_s the
  clearance inequality genuinely FAILS at realized reads: three explicit
  engine-realizable instances at p = 2 (machine-checked,
  `adm_u7_check.py` alongside, ALL ASSERTIONS PASS), including a
  realization of K7's own shape (0,6)→(1,5) at n = 3. So (ADM-REAL) with
  "every on-line slot" is FALSE — track A as displayed cannot land.
* **(CONSUMPTION AUDIT, §5):** k_s is precisely the slot whose digit read
  the CONSUMED census forms never charge with the onto-F_{r+1} factor: in
  CEN-J the right-end read is ρ-pinned and subtracted from the digit count
  (L′ := L − [k_s ∈ K_D], O-9 rev 5 §2, verbatim quote in §5), and in the
  monic-top CEN-W it is the constant 1 (ε = 0). FULL attainment is consumed
  ONLY at on-line slots counted by L′ — all ≠ k_s — where NON-END proves it
  outright (conversion clearance → FULL consumes (CLASS-d): proved at
  r ≤ 1, (GR-B)-conditional at r ≥ 2, the SAME conditionality every (ADM)
  consumer already carries). One perimeter condition remains, displayed as
  (C-JCT) in §5: no consumed site may use the FREE-box CEN-W (ε = 1) —
  instance A shows that form is unsound at realized partial right ends.

Net: kernel (iii) is CLOSED on the slots that carry the census, REFUTED on
the one slot that doesn't, and (ADM)'s consumption should be re-scoped
accordingly (design in §7; statement changes are sign-off-gated and NOT
landed here).

Verified perimeter used: O-9 rev 5 (`O9_phaseB_verifybrief_rev5.md`),
pass 5 CLEAN (0 crit / 0 gap, confirming; `O9_pass5_verify.md`). All O-9
displays are cited, never re-proved.

---

## 1. The statement of record (outer quantifiers displayed verbatim)

From HDISCHARGE_H3.md §1.3(c) track A:

> **(ADM-REAL)** *for every degree n ≥ 2, every prime p (wild included),
> every monic separable ns-free f of degree n over ℤ_p, every level N, and
> every census datum D read off a realized OM stratum of the engine's run
> on f within its (DET) window (β_k ≤ eN − 1, heights on the read side's
> line): every on-line slot height satisfies
> β_k ≥ max{wt(𝐣) : wt(𝐣) ≡ β_k (mod e)}.*                        (ADM-REAL)

Base-changed (O_δ, δ > 1) instances are NOT quantified here (they ride
(UB-X)(a)'s transport, the (H4b) row) — unchanged.

Fixed notation (O-9 rev 5 §§1–2, 4; F₀ = F_q): type t of order r,
invariants (e_i, f_i, h_i), e := e₁⋯e_r, d := f₀⋯f_r, m := ed = deg φ,
φ := φ_{r+1} a representative, w := v_{r+1} (w(c) = e·v_π(c) on O),
V̂ := w(φ). Ledger monomials B_𝐣 = φ₀^{j₀}⋯φ_r^{j_r} (j₀ < f₀,
j_i < e_if_i), weights wt(𝐣) = Σ j_i·w(φ_i). Datum D: face chain with
vertices (k₀,U₀),…,(k_s,U_s), slopes −h_S/e_S strictly increasing, all
< 0; on-line lattice slots k = k_{S−1} + j·e_S with thresholds
β_k = L_k − kV̂ ((READ) display). G_β := {w ≥ β}/{w > β},
dim G_β = #{𝐣 : wt(𝐣) ≡ β (mod e), wt(𝐣) ≤ β} (LED(iii)). FULL at k ⟺
dim G_{β_k} = d ((ADM), rev-4 form). The deep-stratum reading (ADM) ⟺
"every on-line β_k ≥ max class weight" is available wherever (ADM) is
consumed, via (CLASS-d) (O-9 §2; proved r ≤ 1, from (GR-B) at general
order). K7's countermodel datum: β₁ = 1 < max class weight 2 at N = 7,
(DET)-legal — (ADM-REAL) is exactly the claim that realization excludes
such data.

---

## 2. Lemma W-CAP (the ledger weight cap; proves the sketch's clause (ii) in exact form)

**Lemma W-CAP.** Let t have order r ≥ 1. Then, with E_i := e_{i+1}⋯e_r
(E_r = 1),

    W_max := max_𝐣 wt(𝐣) = Σ_{i=1}^{r} (e_if_i − 1)·w(φ_i)
           = V̂ − w(φ₁) − Σ_{i=2}^{r} E_i·h_i   ≤ V̂ − w(φ₁) ≤ V̂ − 1.  (W-CAP)

At r = 0, W_max = 0. Consequently every class max —
max{wt(𝐣) : wt(𝐣) ≡ c (mod e)} for any c — is ≤ V̂ − w(φ₁) < V̂.

*Proof.* wt is linear in the j_i with nonnegative coefficients w(φ_i), so
the max is at j₀ = f₀ − 1, j_i = e_if_i − 1 (an actual ledger index).
w(φ₀) = 0: for f₀ ≥ 2, deg φ₀ = 1 < m₁, so iterated (P1) gives
w(x) = e·v₁(x) = 0 (v₁ = the Gauss valuation, TRI's base case); for f₀ = 1
the index j₀ ranges over {0} only. For 1 ≤ i ≤ r, iterated (P1) gives
w(φ_i) = E_i·v_{i+1}(φ_i) = E_i(e_iV_i + h_i) with the pinned (P3)
V-recursion V₁ = 0, V_{i+1} = e_if_i(e_iV_i + h_i), and
V̂ = w(φ) = V_{r+1} = e_rf_r·w(φ_r) (E_r = 1). Hence for 1 ≤ i ≤ r−1,
using E_{i+1}e_{i+1} = E_i:

    w(φ_{i+1}) = E_{i+1}(e_{i+1}V_{i+1} + h_{i+1})
               = e_if_i·w(φ_i) + E_{i+1}·h_{i+1},                      (REC)

and at i = r the same computation with no h-term: V̂ = e_rf_r·w(φ_r) (this
IS the blueprint's "V̂ = e_r f_r w(φ_r)" display). Telescoping
Σ_{i=1}^{r}(e_if_i − 1)w(φ_i) = Σ_{i=1}^{r-1}[w(φ_{i+1}) − E_{i+1}h_{i+1}]
+ V̂ − Σ_{i=1}^{r} w(φ_i) = V̂ − w(φ₁) − Σ_{i=2}^{r} E_ih_i. Finally
w(φ₁) = E₁h₁ ≥ 1. ∎

*Instance checks:* r = 1: W_max = (e₁f₁−1)h₁ = V̂ − h₁ ✓. O-9 warning
display 2 (type (e₁,f₁,h₁) = (1,2,2)): W_max = 2 = 4 − 2 ✓; warning
display 1 ((3,1,2)): W_max = 4 = 6 − 2 ✓.

---

## 3. Lemma STEP and Theorem NON-END (kernel (iii) closed off the right end — abstractly)

**Lemma STEP (on-line descent).** On face S, consecutive on-line lattice
slots k, k + e_S have β_{k+e_S} = β_k − (e_SV̂ + h_S). Across the chain, β
is strictly decreasing on the ordered on-line slots (slopes all < 0, faces
concatenated at shared vertices). Hence, with (e_s, h_s) the LAST face's
data: every on-line slot k ≠ k_s satisfies

    β_k ≥ β_{k_s} + (e_sV̂ + h_s) ≥ β_{k_s} + V̂ + 1.                 (STEP)

*Proof.* u drops by h_S per e_S columns along the face's line;
β_k = L_k − kV̂ so Δβ = −h_S − e_SV̂ per on-line step. A face has positive
length, so with ≥ 1 face there are ≥ 2 on-line slots and the second-lowest
sits one step (of the last face) above β_{k_s}. e_s ≥ 1, h_s ≥ 1. ∎

**Theorem NON-END.** Let D be ANY level-N census datum over ANY type t of
order r ≥ 0 (abstract carrier data: no realization, no (DET), no bound on
n, p, N) whose right-end on-line height satisfies β_{k_s} ≥ 0. Then every
on-line slot k ≠ k_s satisfies

    β_k ≥ V̂ + 1 > V̂ − w(φ₁) ≥ W_max ≥ max{wt(𝐣) : wt(𝐣) ≡ β_k (mod e)},

i.e. the clearance inequality of (ADM-REAL), with margin ≥ 1 + w(φ₁) ≥ 2.
Moreover dim G_{β_k} = #{𝐣 : wt(𝐣) ≡ β_k (mod e)} (LED(iii), since every
class weight is ≤ W_max < β_k), which equals d — i.e. the slot is FULL —
under (CLASS-d) (unconditional at r ≤ 1; from (GR-B) at general order:
O-9 §2, the same conditionality every consumer of (ADM) already assumes).
At r = 0 every slot of every datum with nonnegative on-line heights is
FULL (W_max = 0, dim = f₀ = d) — O-9's r = 0 automaticity, recovered.

*Proof.* STEP + β_{k_s} ≥ 0 give β_k ≥ V̂ + 1; W-CAP gives the strict
gap. ∎

**Corollary LOC ((ADM) localizes to one slot).** For any datum with
β_{k_s} ≥ 0, under (CLASS-d): (ADM)-FULL(D) ⟺ FULL at the single slot k_s
⟺ β_{k_s} ≥ max{wt(𝐣) : wt(𝐣) ≡ β_{k_s} (mod e)}. In particular NO
abstract countermodel to (ADM) can ever live off the right end —
corroborated by the record: K6's unattained slot and K7's partial slot are
both at their datum's k_s, and O-9's countermodel search was structurally
forced there.

*Realized reads.* At a realized read, β_{k_s} = w(a_{k_s}) with a_{k_s} ≠ 0
(a hull vertex needs finite height), and w = v_{r+1} ≥ 0 on O[x]∖{0} by
TRI (weights ≥ 0, v_π ≥ 0). So β_{k_s} ≥ 0 is automatic and NON-END applies
to every realized datum — this is ALL the realization input the
non-right-end slots need. The blueprint sketch's clause (i) (the (ZC-a)
staircase anchoring of fresh reads above the accumulated floor F(b)) is NOT
consumed by the positive theorem; it resurfaces only inside the refutation
constructions (§4), where "fresh sits strictly above the floor" is what
makes w(g − φ) ≥ V̂ + 1 for any two lifts of the same order-r data.

---

## 4. The right end k_s: trichotomy, and the realized refutation

At k = k_s the clearance inequality has no lower-bound mechanism — and it
genuinely fails at realized reads. Trichotomy by box role (O-9 §2's two
boxes + LED-top):

* **(a) free vertex (k_s < ℓ; the parent-junction slot).** β_{k_s} =
  w(a_{k_s}) ∈ ℤ_{≥0} unconstrained from above by the frame. REFUTED:
  instance A below realizes β_{k_s} = 0 < 1 = class max.
* **(b) m | n monic top (k_s = ℓ, a_ℓ = 1).** β_{k_s} = 0 always; the
  "read" is the constant 1. FULL-by-letter ⟺ dim G₀ = f₀ = d ⟺
  f₁⋯f_r = 1: fails at EVERY total-length m|n datum of any type with
  d > f₀ (instance C) — but the slot carries no choices and is outside
  K_D, so nothing consumes it.
* **(c) m ∤ n monic-coset top (k_s = ℓ).** LED-top(i): β_{k_s} =
  w(a_ℓ) ≤ w* := wt(𝐣*) ALWAYS (the anchor cap) — so clearance at k_s can
  hold only if β_{k_s} = w* AND the class max of w* is w* itself; below the
  anchor the read's image is LED-top(ii)'s proper subspace V_β. REFUTED as
  a clearance claim: instance B realizes β = 1 < w* = 2.

**The three realized instances (p = 2; machine-checked in
`adm_u7_check.py`, log `adm_u7_check_2026-08-01.log`, ALL ASSERTIONS
PASS).** All use order-1 parent types with f₀ = 1 (φ₁ = x), q = 2,
ψ₁ = y² + y + 1 (irreducible over F₂), d = 2, e = 1, ledger weights
{0, h₁}, V̂ = 2h₁; engine representative φ₂ = a legal lift of ψ₁ (monic,
one-faced slope −h₁, R₁(φ₂) = ψ₁ — GMN Thm 2.11/Def 2.12 scope). The
constructions are parametric in p; verified at p = 2. All three f are
monic, separable (square-free over ℚ, checked), products of a ψ₁-type
quadratic (or two) and unit-/small-valuation linear factors — the engine's
run on f reaches the order-1 frame (φ₁ = x; λ₁ = −h₁; ψ₁) on the displayed
face and reads the order-2 polygon w.r.t. φ₂; (P4) fixes the principal
length ω₂ = ord_{ψ₁}R₁(f); the resulting datum, its (DET) level, and every
β_k are computed and asserted by the script.

* **Instance A (free-vertex right end, case (a)):** type (e₁,f₁,h₁) =
  (1,2,1), V̂ = 2, weights {0,1}, W_max = 1. φ₂ = x² + 2x + 4,
  f = (x² + 6x + 12)(x − 1)(x − 3), n = 4 (m | n; a₂ = 1). Development
  heights u = (3, 2, 4); principal chain (0,3)→(1,2), ω₂ = 1 ✓ (residual
  of f's slope-−1 face = y² + y + 1, checked from f's own coefficients).
  On-line: β₀ = 3 FULL; **β₁ = 0 at k_s = 1 < ℓ = 2: dim G₀ = 1 < 2 —
  PARTIAL at a FREE slot.** (DET) at N = 4 (3 ≤ N − 1). Per-slot window
  census brute-forced at N = 4: slot-1 truth 128 = LED = the §5.1 image
  law (q^{dim}−1)q^{mN−s(0)−dim}; the FULL-shaped display would give 192 —
  refuted numerically at the realized shape; attained nonzero digit
  classes: 1 = q^{dim} − 1 (fiber-uniform), vs 3 = q^d − 1 for FULL.
* **Instance B (monic-coset top, case (c)) — K7's shape realized:** type
  (1,2,2), V̂ = 4, weights {0,2}, W_max = 2, w* = w(x) = 2.
  φ₂ = x² + 4x + 16, f = (x² + 12x + 80)(x − 2), n = 3 (m ∤ n, m′ = 1).
  Chain (0,6)→(1,5) — **literally K7's datum shape** — with β₁ = 1 < 2 =
  class max at the top slot (LED-top(ii) regime, dim G₁ = 1), β₀ = 6 FULL.
  So the answer to the blueprint's explicit question "whether K7's datum
  is realized by an actual engine stratum at some (f, p)" is YES at
  (f as above, p = 2) — with the box refined to the realized monic-coset
  top (K7's abstract FREE box is what realization does NOT produce at
  n = 3).
* **Instance C (m|n monic top, case (b), plus an exactness witness):**
  type (1,2,1), φ₂ = x² + 2x + 4, f = (x² + 6x + 12)(x² + 2x + 20), n = 4.
  Chain (0,7)→(1,5)→(2,4) (two faces, slopes −2 < −1), ω₂ = 2 = ℓ.
  On-line: β = (7, 3, 0); K_D = {0,1} slots FULL (β₁ = 3 hits STEP's bound
  0 + e_sV̂ + h_s = 3 EXACTLY — the descent bound is tight); slot ℓ:
  β = 0, dim G₀ = 1 < 2, partial-BY-LETTER at the pinned constant-1 slot.
  **The CEN-W monic-top display is nevertheless EXACT here:** brute-forced
  window census at N = 8 = 9216 = q^{E′}·M_{(1,1)}(q²)² — a datum OUTSIDE
  (ADM)-as-displayed's fence where the consumed display is still true.
  (ADM) as stated over-fences.

**Consequence.** (ADM-REAL) as displayed is FALSE: the §1 quantifier block
concludes β_k ≥ class-max at EVERY on-line slot, and instances A/B/C are
within its quantifier range (explicit n, p, f, N, realized strata, (DET)
respected) with β_{k_s} < class max. Track A cannot land the displayed
statement. What survives — all of it — is NON-END + LOC: the failure is
CONFINED to k_s, at every order, provably.

---

## 5. Consumption audit: k_s is exactly the un-charged slot

What the census actually consumes at each slot (O-9 rev 5, verbatim
displays):

* **CEN-J (the form Step 14 consumes), §2:** the digit-read charge is
  −d·L′ with "L′ := L − [k_s ∈ K_D] (the chain's right-end read is
  ρ-pinned — (FRESH)(c) — hence charged to the parent, not to the window;
  when the top is monic, k_s = ℓ ∉ K_D and the pin is the monicity
  constant, so nothing is subtracted)." The onto-F_{r+1} ⟺ FULL law
  (§5.1) is consumed exactly at the L′-counted on-line slots — all
  ≠ k_s — where NON-END proves FULL (under (CLASS-d), §3). The
  s(β_k)-terms of E″ at k_s (s′ at an m∤n top) consume only LED(ii)/
  LED-top(i)(ii) counting — unconditional. The k_s read itself consumes
  only NONVANISHING + fixedness of the ρ-pin (§6.4 via Lemma C; LED-top
  (iii) for the m∤n case) — value-attainment-grade, automatic at realized
  (nonempty) reads, priced to (FRESH)(c) as before.
* **CEN-W monic-top (ε = 0), §2:** right-end read = the constant 1; K_D's
  on-line slots are all ≠ k_s: NON-END covers them. Instance C exhibits
  the display exact beyond (ADM)'s fence.
* **CEN-W free box (ε = 1):** the (q^d − 1) unit factor IS a FULL
  consumption at k_s. NOT covered — and instance A shows it is genuinely
  false at realized partial right ends (128 vs 192).

**(C-JCT) — the displayed perimeter condition.** The re-scoped kernel
covers a consumer iff its right-end read is pinned (CEN-J's ρ-pin, or the
monic constant). DUTY, not proved here: confirm no Step-14 consumption
site fires the FREE-box CEN-W (ε = 1) on realized cells. Support on file:
the harness's uniformly measured ε = 0 (O-9 attempt note §1, design
decision 2: the joint form kills the free-end factor); the two-box scoping
of §2 routing every realized monic case through CEN-J/monic-top. This is a
finite audit of O-9 §6.4/§8 + the Step-14 fan-out and belongs to the
consumption seam (§7), not to this kernel.

**The repaired track-A statement (proved, given the displayed
conditionality):**

> **(ADM-REAL′)** Under the SAME outer quantifiers as (ADM-REAL) (§1):
> every on-line slot of D other than the chain's right end k_s satisfies
> β_k ≥ V̂ + 1 > max_𝐣 wt(𝐣) ≥ max{wt(𝐣) : wt(𝐣) ≡ β_k (mod e)} — hence
> is FULL under (CLASS-d) — and β_{k_s} ≥ 0 with the §4 trichotomy at k_s.
> Clearance at k_s itself is NOT asserted (refuted: §4). Proof: NON-END
> (Theorem, §3) — which needs of the quantifier block only that D is a
> datum over a type with β_{k_s} ≥ 0. Conditionality: (CLASS-d) at
> r ≥ 2 = (GR-B), the standing open input; the clearance inequality
> itself is UNCONDITIONAL.

---

## 6. Impact on G-ADM-2 (run it AFTER repairing the router semantics)

Prediction, falsifiable: instrumented per ADM-U5's spec, G-ADM-2 will log
`partial = True` rows — instance-A-shaped ones are reachable within the
declared coverage (n = 4, p = 2, the g = 2 marked-ψ configs, N ≥ 4) — and
EVERY such row will have its slot at the fiber chain's right end (the
harness's chain ends at mu, the junction; `n2_online_slots` includes it).
Under the current spec ("PARTIAL(k) at any config = track A DEAD, fire
ADM-U6a") this would MISROUTE: the hit sits at the one slot CEN-J never
charges, so it refutes only (ADM-REAL)-as-displayed, not (ADM-REAL′), and
firing track B (CEN-W′, the full census generalization program) on it
would buy nothing the junction pin doesn't already give. REPAIR to the
gate spec (one column + one predicate): log `is_right_end := (slot == mu)`
per row; route to track B only on a partial row with `is_right_end =
False`. A right-end-only partial profile CONFIRMS this note's dichotomy
(and any non-right-end partial row REFUTES NON-END — theorem-grade
falsifier, the strongest kind: by §3 that cannot happen unless O-9's
pinned (P1)/(P3) or the datum reader is broken, so it doubles as a harness
integrity gate).

---

## 7. Ripple map (design; every item is someone else's landing, none landed here)

1. **Blueprint §1.3(c) track A display** (blueprints read-only for this
   unit): replace the (ADM-REAL) display with (ADM-REAL′) + the k_s
   trichotomy; retire the "(i) ≥ (ii) floor-transport" sketch in favor of
   STEP/W-CAP; record instances A/B/C as the realized K7 answer. Owner:
   H3 division lead.
2. **O-9 rev 6 (statement change to a verified leaf — SIGN-OFF GATED,
   ADM-U6b-style discipline):** weaken CEN-J's and monic-top CEN-W's
   hypothesis from (ADM) to (ADM′) := FULL at the L′-counted on-line slots
   + value-attainment at vertices. Under LOC this is exactly "drop the
   k_s conjunct". CEN-J's proof should go through verbatim (the k_s charge
   never used FULL — §5); the (C-JCT) audit rides along. Payoff: Step-14
   cells with partial right ends (instances A/C shapes — NOT exotic:
   every m|n total-length datum with d > f₀ is one) re-enter the asserted
   scope instead of being silently fenced out with NO count.
3. **G-ADM-2 / ADM-U5 spec:** §6's slot-role column + routing repair,
   BEFORE the gate runs. Add instance A/B/C's configs to the coverage
   list as positive controls.
4. **Lean carrier seam (ADM-U1/U2/U0 owners, `AdmCarrier.lean`):**
   `ADMFull` quantifies over `D.onLineSlots` with no right-end carve-out;
   the eventual `RootHyps.h3_adm := ∀ D ∈ consumedData, ADMFull D` would
   then be FALSE on realized data by this note's instances. The carrier
   needs either a `rightEnd`-excluding slot set or an (ADM′)-shaped
   predicate; STEP/W-CAP/NON-END are Finset-arithmetic-grade and
   Lean-able against `CensusData` once the k_s field exists. No Lean unit
   scheduled downstream of ADM-U7 (blueprint) — this is design input for
   the next blueprint revision, not a started file.
5. **ROOT (H3) row:** on acceptance of this note + the O-9 rev-6 landing,
   the (ADM) row's operative content becomes: NON-END/W-CAP (proved,
   unconditional inequality) + (CLASS-d)-at-(GR-B) + (FRESH)(c)'s pin +
   (C-JCT). The [M]-row does NOT retire here — (GR-B) and (FRESH) still
   price it — but its OPEN kernel shrinks from "an inequality at every
   slot of every realized datum" to the two already-named opens.

---

## 8. Honesty summary

* **PROVED, unconditional (this note):** W-CAP (exact identity + cap);
  STEP; NON-END's clearance inequality β_k ≥ V̂ + 1 > class max at every
  on-line slot ≠ k_s, for every datum of every order with β_{k_s} ≥ 0
  (realized reads included, all p, wild included); LOC's localization;
  the r = 0 automaticity recovery. Inputs: O-9's PROVED layer only
  (A1/TRI/LED/LED-top, the pinned (P1)/(P3), the §2 datum definitions).
* **PROVED conditional on (CLASS-d) [= (GR-B) at r ≥ 2]:** clearance ⟹
  FULL at those slots, hence (ADM-REAL′).
* **REFUTED:** (ADM-REAL) as displayed (instances A/B/C, machine-checked
  at p = 2, constructions parametric); the free-box CEN-W display at
  realized partial right ends (128 ≠ 192, instance A); "the K7 shape is
  abstract-only" (it is realized, instance B).
* **DISPLAYED OPEN, owned elsewhere / duties:** (C-JCT) (finite audit of
  O-9 §6.4/§8 + Step-14 sites); (GR-B), (FRESH)(c) (standing opens,
  unchanged pricing); the O-9 rev-6 re-scope (sign-off gated); G-ADM-2
  router repair + run; the Lean carrier re-key.
* **NOT CLAIMED:** any change to O-9's verified text; CEN-J's proof
  details beyond its quoted displays; order ≥ 3 or p ≥ 3 numerics
  (constructions are parametric, verified at p = 2, order-2 reads);
  anything about the implemented engine's Step-14 fan-out beyond the
  quoted spec; that the (ADM) [M]-row retires.
* **Unit-gate note:** doc unit — no Lean file created, so the `lake env
  lean` gate is N/A by construction; nothing under `lean/LeanUrat/` is
  imported by any module (a `.py`, a `.log`, and this `.md` only; build
  graph untouched). Zero `sorry` trivially; no statement was weakened —
  the record statement is quoted verbatim (§1) and its refutation is
  reported as a refutation.

## 9. Files + hostile-pass charges

* `lean/LeanUrat/Scaffold/HDischarge/H3/ADM_U7_TRACKA_ATTEMPT.md` — this
  note (the artifact for the hostile pass).
* `lean/LeanUrat/Scaffold/HDischarge/H3/adm_u7_check.py` + 
  `adm_u7_check_2026-08-01.log` — the falsifier (exit 0, ALL ASSERTIONS
  PASS; pure-integer arithmetic, no deps).

Charges for the hostile pass, beyond the standard quote-and-classify:
(1) STEP's "β strictly decreasing across the whole chain" — check the
multi-face concatenation and the e_S-lattice bookkeeping against O-9 §2's
datum definition, including e_S vs e. (2) W-CAP's use of (P1)/(P3) — is
w(φ_i) = E_i(e_iV_i + h_i) a faithful reading of the pins, wild p
included, and w(φ₀) = 0 at f₀ ≥ 2? (3) The realization claims of
instances A/B/C: is "the engine's run on f reads this datum in this
frame" airtight (representative legality, (P4) length, face selection,
(DET) level), and is instance A's slot k_s = 1 really in K_D with a free
box? (4) The §5 audit: re-read O-9 §6.3/§6.4 and confirm FULL is consumed
ONLY at L′-slots — especially whether the LEFT end k₀'s vertex digit is
L′-charged (this note says yes, k₀ ≠ k_s, covered by NON-END — check).
(5) The (C-JCT) framing: is the free-box CEN-W consumed anywhere on the
mandatory path? (6) NON-END's β_{k_s} ≥ 0 hypothesis: any realized or
Step-14-abstract datum shape with a NEGATIVE right-end height? (7) The
G-ADM-2 §6 prediction's harness reading (`n2_online_slots` ends at mu =
junction).
