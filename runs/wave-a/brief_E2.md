# UNIT E2 — the dv-graded engine, version 2 (math + blueprint; HIGH reasoning)

You are a research mathematician repairing a design document after an adversarial review.
Work directory: this repo. NOTHING you write is signed; deliver a DOCUMENT.

READ FIRST, in this order:
1. docs/in-progress/DV_GRADED_ENGINE_2026-08-20.md — v1 with its supersession banner.
2. docs/in-progress/DV_GRADED_ENGINE_REVIEW_2026-08-23.md — the 13 findings (4 CRITICAL). Your v2 must dispose of every finding by number.
3. spec/EFF-GENTOW3.md lines 640–800 (the source ledger, steps .22–.26).
4. leanfinal/Uniformity/ChapC/C72.lean (the shadow statements + theta/margin), C52.lean + C52_BLOCKED_2026-08-18.md (the four legs + obstruction inventory), C06.lean, C11.lean, C43.lean, C46.lean, C47.lean (the landed pins the engine consumes — note which are `private`).
5. verification/dv_ledger_cert.py (the certified floor law and its honest scope).

DELIVER: docs/in-progress/DV_GRADED_ENGINE_V2_<date>.md containing:
(A) THE FLOOR ENGINE, repaired: a well-typed two-index weight on Polynomial (Polynomial O)
    (finding #1); the normal form built by STRUCTURAL RECURSION, not a rewrite system
    (finding #6 — the v1 measure was invariant; give the recursion and prove termination is
    structural); the L4 quotient-side bound stated and proved in the math (finding #5); the
    hpure→all-coefficient bridge lemma stated (finding #3); the private-pin export list
    (finding #4).
(B) THE CONVERSION MODULE (old L6, finding #9): the weight-to-height identification at the
    reduced normal form as a full lemma chain down to dvHgt/dvSupp/dv2Hgt definitions —
    every nested infimum flattening named as its own lemma with a proof sketch.
(C) ★ THE EXACT HALF, adjudicated (finding #11): IsDvPure closure under products/powers and
    normalized dvResPoly multiplicativity/power-exactness. Determine: does a PUBLISHED
    Fernandez–Guardia–Montes–Nart (or Montes/Nart survey, or Guardia–Montes–Nart trilogy)
    theorem state this at citable precision? If yes: give the exact statement, source,
    numbering, and a draft Lean-facing axiom signature in the corpus vocabulary + a
    faithfulness argument (this becomes a gate-(b) cite with owner secondary review). If no:
    give the proof route as blueprint nodes. Recommend ONE of cite/prove with reasons.
(D) the revised node plan (C.131a′–…, ≈30–60 min each) and what each of C.72/C.52/C.53/C.54
    consumes from it.
Every mathematical claim: proved, sketched-with-all-steps-named, or explicitly OPEN. No
"routine" or "clearly". Full rigor; a wrong confident claim is worse than an open one.
