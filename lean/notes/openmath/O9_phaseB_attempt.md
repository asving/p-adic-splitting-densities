# O9 — order-r stratum census — Phase-B attempt record (Fable, 2026-08-01)

Charge (tree DELTA 2 §D2.6 step 7, node O-9, dispatched ∥ O-10): the
order-r census statement + proof composing M08 Theorem 2 (level-1 census,
PROVED) with the GD-3 anchored march ((GR-B), GD23 rev 2); OL-A attacked
directly; depth-3 harness extended to order-2 census counts. The
self-contained brief is `O9_phaseB_verifybrief.md` — hand THAT to the
hostile pass. This file records design decisions, deltas, and the
falsifier run.

## 1. Design decisions (the four that shape the unit)

* **OL-A split into four clauses and attacked separately.** (i)
  coordinates and (ii) triangularity/ledger counts are PROVED outright
  (Lemmas A1/TRI/LED — the order-r Lemma A, via the pinned GMN Prop
  2.7(1)(3)(4) + Lemma 2.2(2), with a Route-W any-O variant riding GD23's
  (V1)/DEVID). (iii) the line/digit structure is CONSUMED from GD-3 —
  executing the tree's D2.2 "OL-B is GD-3" re-pointing rather than
  re-proving it. (iv) level determinacy gets a displayed sufficient
  formula (DET), and the joint-with-parent separation is isolated as the
  named clause (FRESH) — priced at the GD-2/CL-13 vertex-law layer (=
  CU-1's step content), NOT re-derived here. Net effect: the census
  reduces to (GR-B) + (FRESH), both pre-existing named opens; O-9 adds
  ZERO new open inputs to the mandatory path.
* **Two-theorem shape (CEN-W / CEN-J).** The window-only census (CEN-W,
  conditional on (GR-B) alone) is separated from the joint-with-parent
  census (CEN-J, adds (FRESH)) because the free-end unit factor
  (q^d − 1)^ε appears exactly in the window form and is killed in the
  joint form by the parent's junction pin — the harness's uniformly
  measured ε = 0 forced this distinction into the statements.
* **TYPE-MARCH displayed as the unit's "why".** The anchored march's
  affine-in-κ exponent law makes per-slot twists a scalar × (y ↦ ρy)
  substitution — type-preserving; a general fixed twist system is NOT
  (displayed F₃ countermodel: (1,1,2) turns type {(1,2)} into {(2,1)}).
  So GD-3's FULL form (march included) is precisely what census
  polynomiality consumes — sharpening SYNTH4's "the value side needs the
  full form" from a pricing note into a theorem-level dependency.
* **Index correction recorded, not silently absorbed.** The tree/M08 §3
  display q^{f̄_r} (f̄_r = f₀⋯f_{r−1}) is off by one: order-(r+1) reads
  live over F_{r+1} of degree d = f₀⋯f_r. The brief uses d throughout and
  flags the tree for a DELTA-3 line.

## 2. What is NEW vs the composed sources

* The order-r slot ledger (mixed-radix φ-monomial basis, TRI, LED) with
  pure-q-power counts and the explicit census exponent E′ — the direct
  OL-A attack the dispatch asked for.
* The fiber-uniformity argument (§5.1): the (GR-B) digit read as a
  surjective F_q-linear map on the graded piece ⟹ every digit value costs
  exactly q^d — the order-r Lemma A second display, obtained from (GR-B)
  by linear algebra instead of slot-by-slot bookkeeping.
* TYPE-MARCH (+ the type-breaking countermodel) and JUNCTION-PIN.
* (DET) as a displayed sufficient level formula, plus the two compiled
  finite-level traps (§5.3 of the brief) discovered BY the falsifier:
  the u-space visibility trap and the cap-split artifact ((q−1)(q³−1)
  census from keying a stratum's deep tail) — both now fence text.
* The census-side execution of D2.2: OL-B formally re-pointed at GD-3.

## 3. Falsifier record (falsifier-first)

`verification/openmath/o9_order2_census_check.py` — M08's proposed T6
executed; reuses the depth-3 harness's coherent anchored-march reader
(`o1thr_depth3_check`: fq arithmetic, res1, the marched pattern) and the
per-site level-1 machinery. Checks K1 (M08 Thm 2 regression, exact),
K2 (parent-realization independence of the refined census), K3 (per-p
type-product law), K4 (cross-p atom fit in {p, p^g−1, p−1}), T2 (pinned
Lemma 2.17(2) length law). Determinacy fence: the key-level (DET)
criterion; strata failing it are dropped WHOLE (`undet` counter), never
box-by-box.

Production run (2026-08-01, this machine, `python3
o9_order2_census_check.py`, ~7 min; log in `verification/openmath/logs/`):

    10 configs: full (2/3,3,5), (2/3,4,4), (2/3/5,4,3);
                restricted (5,3,5)@(3,2,1), (2/3,4,6)@(4,3,2,1) [g=2]
    boxes 8,220,994 · order-2 instances 1,128,288 · K1 rows 100
    cross-p census cells 18 (one at g = 2, i.e. over F_{p²})
    K1: 0 viol · K2: 0 · K3: 0 · K4: 0 · T2: 0  →  GATE SURVIVES
    fitted spectrum: all cells = p^a · ∏M (ε = 0; a ∈ {3,4,5,7,8,9})

Two intermediate FIRES during development were diagnosed as harness key
defects, fixed, and promoted to fence text (brief §5.3): (1) capped slots
compared in β-space instead of u-space let deep slots dip under extended
face lines (first fire: K3/K4 on the (0,4)→(4,0) and (0,3)→(3,0)
designs); (2) keying strata by the working-level vanishing of a tail
coefficient split censuses into non-atom values — measured (q−1)(q³−1)
at the slope −1/2 design. Neither was a mathematics failure; both are
exactly what OL-A(iv)'s determinacy clause exists to fence, and the final
criterion is the brief's (DET) formula verbatim.

Coverage gaps (displayed in brief §10): degree-≥2 child types at p = 5
(config (5,4,4)@(2,2,1,1) behind the `slow` flag, 5^10 boxes); g ≥ 2
with nontrivial child types (needs M = 7-scale); order-3 censuses.

## 4. Honesty summary (mirror of brief §0)

PROVED outright: A1, TRI, LED, (DET)-sufficiency, TYPE-MARCH, the r = 0
recovery of M08 Thm 2. PROVED conditional on (GR-B): the line clause,
fiber uniformity, CEN-W. PROVED conditional on (GR-B) + (FRESH): CEN-J
(the O-9 census), JUNCTION-PIN's use. CONSUMED: GD-3/OL-B (order 1
proved there; ≥ 2 = (GR-B)); M08 Lemmas B/C/D (field-abstract, at
q^d). OPEN, owned elsewhere: (GR-B) [GD-3], (FRESH) deep states [GD-2/
CU-1], OL-D officialization + pack build [table build]. NOT CLAIMED:
anything about the implemented engine; order ≥ 3 numerics; the σ/tree
assembly.

## 5. Files

* `lean/notes/openmath/O9_phaseB_verifybrief.md` — the self-contained
  brief (11 sections; status table §0; attack list §11).
* `verification/openmath/o9_order2_census_check.py` — the census
  falsifier (exit nonzero on any violation; `fast`/`slow` flags).
* `verification/openmath/logs/o9_census_*.log` — the production run.

## 6. Suggested verification charges beyond the standard

(i) Brief §11 items (1)–(7), especially (2) (the LINE clause's degree
step) and (3) (JUNCTION-PIN's attribution). (ii) Recompute E′ for one
harness cell by hand from the ledger and match the fitted exponent.
(iii) Check the (DET) criterion in the harness (`child_data`) against the
brief's displayed formula — they are meant to be verbatim twins.
(iv) Confirm no clause of CEN-J silently consumes GD-3's MIN core where
the FULL form is priced (the V25 consumption-split discipline).
