# GD23 — the GD dictionary unit (GD-2 ⊕ GD-3) — Phase-B attempt (Fable, 2026-07-31)

Charge (dispatch, per the adjudicated plan — SYNTH4 §1 GD-2/GD-3 + §3.2 step
3; O3adj cross-read): state GD-2 (frame/valuation tie + development identity)
and GD-3 (residual dictionary) as ONE MacLane/GMN unit over an ARBITRARY
complete DVR with perfect residue field (the generality that kills
D-3/UNRAM-TRANSFER as a separate node); compose the ~30% already proved
(O-1thr VAL1/KEY1/DIV1, O-2a (D3), the (V1)/(V2) statements); generalize;
prove the rest or pin the sharpest literature statements (MacLane 1936
augmented-valuation multiplicativity; the GMN types dictionary, theorem
numbers pinned). Deliverable: attempt + self-contained verify brief.

The self-contained brief is `GD23_phaseB_verifybrief.md` (hand THAT to the
hostile pass). This attempt records the design decisions, the delta against
the composed sources, and the falsifier run.

## 1. Design decisions (the three that shape the unit)

* **The three-term split u / w / v.** The carriers state GD-2(a) as
  "engine u_{i+1} = GMN v_{i+1}". A math unit cannot prove statements about
  the implemented engine, so the unit introduces the MacLane chain w as the
  mathematical middle term and splits the tie: w = v is proved (Theorem TIE,
  modulo one flagged GMN transcription T-1 + two pins in hand), while u = w
  is re-priced as engine conformance (GD-4/GD-6/S-1 territory) TOGETHER WITH
  the compensating theorem that makes that re-pricing safe: Corollary IFACE —
  the stage-interface axioms ([F.0]–[F.2], incl. (S-K1) and the carry
  algebra) are SATISFIED by w. This executes SYNTH4's GD-2 note verbatim
  ("GD-2 is precisely the tie: the engine's axiom holds AT the GMN
  valuation") and keeps the HK52 emitted-record typing.
* **The development identity is a graded one-liner, not a division chase.**
  The unit's main new proof (Theorem DEVID): (V1)-domain + the key's
  minimality block (KPa) imply w(B) = min_k (w(C_k) + k·γ̂) at EVERY order,
  over every DVR, by the WGEO(b)-style initial-form factorization. This
  retires O-1thr's DIV1 (order-1, d₀ = 1 slot-chase) and moots its V24-G4
  general-lift caveat — the graded proof never sees any lower key's shape.
  It also supplies exactly the "development identity (V2b) at level i" that
  Corollary VTX's deeper-harvest leg was left owing.
* **GD-1 is consumed, not swallowed.** Everything a key must satisfy enters
  as the displayed cumulative input (KP) = GD-1's clauses (proved at order 1
  standard-lift by this unit's KEY-g, any d₀, any O; GMN Thm 2.11/MacLane
  Def 4.1 beyond). The unit stays a transport/dictionary unit, per the
  family cut of SYNTH4 §1.

## 2. What is NEW here vs the composed packages

* **Order-≤1 layer generalized twice** (Theorems GAUSS-g/VAL-g/KEY-g/RES-1):
  from d₀ = 1 to every root-key degree (SYNTH4's GD-5 residue "degree-g > 1
  root keys need the KEY1 generalization" — DELIVERED, and the predicted
  unramified-extension detour turned out unnecessary: the coefficient field
  K₀ = F[X]/(φ̄) emerges inside gr(w₁) directly), and from ℤ_p to an
  arbitrary complete DVR (equal characteristic included — falsifier-tested
  over F_p[[t]]). gr_K(w₁) ≅ K₀[π̄^{±1}][Φ̄₀], weighted UFD, with full
  proof (carry terms strictly heavier — the order-1 shadow of the carry
  algebra).
* **DEVID at every order** (above) — (V2b)'s status changes from
  "citation-grade bundled, dictionary owed" to PROVED given (V1)+(KPa).
* **The order-1 residual dictionary in FULL form** (RES-1): stage residual
  = R_λ(f) on the nose, 𝒟 = K₀, twists absent, per-slot bijections — the
  mathematical half of O-2a's OL-5 (b′)+(c′) over any O, i.e. GD-5's
  composition-note input.
* **UNIQ/TIE architecture**: the w = v tie reduced to exactly three GMN
  properties — (L2) base and Prop 2.7 key-recursion already pinned, ONE new
  flagged transcription (T-1: v_r computed by current-key developments) —
  via a trivial uniqueness lemma. Off-by-one hazards killed by an explicit
  index dictionary (w_i ↔ v_{i+1}, K_i ↔ F_{i+1}).
* **GD-3 split priced per V25**: min core (all the cluster needs) gets TWO
  independent routes — Route A: TIE + one flagged GMN lemma (T-2, candidate
  Lemma 2.17: principal length = ω); Route B: the displayed residue-structure
  package (GR-B). Full form + OL-B proved FROM (GR-B). (GR-B) itself is the
  unit's one honest open input at orders ≥ 2 — formulated as the semantic
  realization of the engine's carry algebra 𝒟 = F[u]/(u^{e_b} − ζ) (the
  MOVES pass-7 object), proved at order 1, cited to MacLane §§9–12 / FGMN
  J. Algebra 427 (2015) with numbers flagged for the literature unit.
* **D-3 killed as promised**: §1.1 of the brief displays that completeness
  and perfectness are used in NO proof; O_δ = W(F_{p^δ}) and F_q[[t]] are
  instances. O-8b's (R1)–(R4) keep only their engine-side clauses.

## 3. Falsifier record (falsifier-first; run BEFORE the brief was written)

`verification/openmath/gd23_check.py` — NEW harness at exactly the
previously-untested perimeter: d₀ = 2 root keys (T-E/T-F ran d₀ = 1 only)
and equal-characteristic O = F_p[[t]] with t-noisy lifts. Four
configurations (ℤ₂, ℤ₃, F₂[[t]], F₃[[t]]); exact arithmetic; complete
residual factorization over F_{p²}. Results (2026-07-31, this machine):

    VAL-g multiplicativity   2,622 pairs      0 violations
    A-law (w₁(f) = γ)        1,910 sides      0 violations
    KEY-g homogeneity/degree 2,115 keys       0 violations
    DEVID + GD3-MIN          2,115 instances  0 violations
    (GAUSS-g asserted on every sample)

Any single violation would have refuted the corresponding claim before it
was written up. Standing traps cited, not re-run: T-E/T-F (the sheared
convention's 7,472-countermodel pin), the HK52 stretch gate (engine-side
GD-2(c) trap). Queued: depth-3 harness; d₀ ≥ 2 depth-2 harness (would
exercise (GR-B)'s order-2 instance numerically).

## 4. Honesty summary (mirror of brief §10)

PROVED outright (any O): DEV-g/POS-g/GAUSS-g/VAL-g/KEY-g/RES-1/DEVID/UNIQ +
the (GR-B)-conditional reductions. PROVED modulo single flagged
transcriptions: TIE (T-1), REC-c1, GD3-MIN Route A (T-2), V1-tower beyond
order 1 (MacLane Thm 4.2 pin + ML-scope flag). OPEN: (GR-B) at orders ≥ 2
(one package, cited, order-1 instance proved). NOT CLAIMED: anything about
the implemented engine's emitted records; (KP)/GD-1 beyond order 1;
GD-4/GD-6 bookkeeping; runs, boxes, exhaustiveness.

## 5. Files

* `lean/notes/openmath/GD23_phaseB_verifybrief.md` — the self-contained
  brief (11 sections; status table in §0; attack list in §10).
* `verification/openmath/gd23_check.py` — the falsifier harness (seed
  pinned; rerun with `python3 gd23_check.py`, exits nonzero on any
  violation).

## 6. Suggested verification charges beyond the standard

(i) The §10 attack list of the brief, items (1)–(6) — especially whether
(GR-B)(4) (faithfulness at ψ) matches what FGMN's operator actually
provides. (ii) Audit the index dictionary at every TIE/REC-c1/GD3-MIN
consumption — the off-by-one seam. (iii) Check DEVID is nowhere consumed at
an order where (V1) is not yet supplied (the cumulative reading of (KP)).
(iv) Confirm the brief's §8 consumption table promises nothing beyond §0's
status table. (v) The three flags (T-1, T-2, ML-scope) are single displayed
sentences — confirm they are flagged at every use site.

## 7. Rev 2 (2026-07-31, post-V26; supersedes §4's honesty summary)

V26 (`V26_gd23.jsonl`, Codex fresh context) returned UNSOUND: 3 criticals,
4 gaps — while CONFIRMING the order-≤1 layer, DEVID, and the arbitrary-DVR
generality audit. `GD23_phaseB_verifybrief_rev2.md` is the repaired brief
(hand THAT to the next hostile pass); confirmed statements/proofs carried
byte-stable (checked by diff). The repairs: (V26-1) the missing MacLane
irreducibility premise is DECLARED as the new (KP) clause (KPirr) — proved
at j = 0 by KEY-g(ii) — and the tower composition recomposed against the
printed Def 4.1 via the new proved Lemma BRIDGE; (V26-2) the false
"one anchor absorbs all slot twists" deduction is DELETED — (GR-B)(2′) now
IS the anchored-march identity (FGMN Thm 4.2's shape), with both
countermodels displayed (V26's τ_κ = a^κ / 1+z ↦ 1+az, and CU-1's
slot-fresh reading refuted 1,818× at depth 3); GD-3(full)/(slot law)/[F.2]
statements now carry the march; (V26-3) IFACE rescoped per clause (the
polygon clause rides REC-c1 = GMN scope; rev 0's "any O" row was a scope
error); (V26-4) POS-g's sub-multiplicativity rescoped to orders ≤ 1
outright, with the general-order division-control step now displayed,
conditional on exactly the tower's own package. The LITUNIT pins
(`LITUNIT_2026-08-01.md`: all five flags MATCH, verbatim quotes) are folded
in: T-1 = GMN Prop 2.7(1)(3)+Lemma 2.2(2); T-2 = ω-def + Lemma 2.17(2)(3)
+ Def 1.8 (first attainment in the printed proof); ML-scope CLEARED;
(GR-B) cited clause-by-clause (MacLane 10.2/10.1/11.1–2/12.1/12.2; FGMN
4.2/4.4/4.8/4.9/5.6(2)/5.13/5.14/5.15). Falsifier-of-record for the march
clause: CU-1's `o1thr_depth3_check.py` production run (470,736 order-2
instances, 0 violations under the coherent convention), run before rev 2
was written.
