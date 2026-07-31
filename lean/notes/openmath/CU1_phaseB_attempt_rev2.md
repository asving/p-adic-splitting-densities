# CU-1 — no-missing + interior adequacy + state binding — Phase-B attempt REV 2 (Fable, 2026-07-31)

Repair of the V27 hostile verification (`V27_cu1.jsonl`, verdict UNSOUND) of
the rev-1 brief (`CU1_phaseB_verifybrief.md`). V27's own summary: "The two
flagged seams fail as written, and the N\* invocation independently breaks
the induction." All findings are repaired in the rev-2 brief
`CU1_phaseB_verifybrief_rev2.md`; the disposition table (finding → repair →
churn class) is that brief's §0. The rev-1 attempt record and its §1 gate
record (`CU1_phaseB_attempt.md`) stand unchanged — the depth-3 falsifier
T-G ran before rev 1 and SURVIVED; rev 2's falsifier accounting is brief
§7.4 (no new per-site mechanism, so no new gate owed).

## 1. What rev 2 changed (the four structural repairs)

1. **The induction is now N-FREE (V27 findings 3e/5 — the invalid IH use).**
   Theorem CU-1 rev 2 proves realization ON f ITSELF: clauses (i)/(ii)
   mention no working level, so no prefix monotonicity of N\* is needed
   anywhere. The working level lives in the separate Corollary CU-1-LVL:
   ONE D-14 application at the top site (L(M) is a max over all reads, so
   the single top-site ceiling dominates every prefix ceiling by
   definition), then REAL≡ on the displayed decode f_N (monic degree-n by
   the O-1thr §1 box definition; f ≡ f_N mod p^N; "canonical run at working
   level N" is DEFINED as the walk on f_N; REALIZED(f_N, M) is established
   BEFORE REAL≡ fires — findings 3f). (N\*-MAJ) is restated as the single
   inequality N\*(𝐇) ≥ L(M_𝐇).
2. **Construction before recovery + fieldwise record match (findings 2a/6b,
   per the adjudicated directive).** The realized object is an explicitly
   CONSTRUCTED machine history M_𝐇 (each node = THE harvest of one
   identified candidate pair); its 𝔈-projection is matched to 𝐇 FIELD BY
   FIELD, each field with a named source (OL-2(c)/(d), OL-3, [F.2], the
   species/W2 law). Lemma R survives only as a canonicity remark — it
   produces and identifies nothing. Same reorder in Corollary CU-1-ADEQ:
   the node is constructed by displayed formulas (Lemma R's recovery
   formulas used as definitions) and Cons_f + all five W-laws are then
   checked clause by clause (no OL-4).
3. **The width tie (finding 1).** Step 2's chain is now: FULL OL-2(b)
   [stage window polygon = N_{k+1}(f), whole polygon, vertex for vertex] +
   (FR≡) [machine polygon = stage polygon] + WGEO(c) [machine-side: the
   principal part of the FULL polygon coincides with the window hull]. No
   width-indexed dictionary clause is invented. This RESCOPES the unit's
   OL-2/OL-3 consumption from the min cores to the FULL forms — exactly the
   consumption O-2a rev 5 §4 already advertises to "the O-3 design seam",
   which CU-1 is; flagged as sanctioned churn in brief §0.
4. **ADEQ split + honest global read-back (findings 6a/6c).** CU-1 (theorem
   AND corollary) is scoped to INTERIOR chains/children (every μ ≥ 2);
   complete children (μ = 1 — leaves, by O-2a Theorem 2(B)'s biconditional)
   are routed to O5triple Theorem B / Theorem D(b) (= D-7b), whose
   counting-forced coverage consumes NO no-missing clause. The split is
   displayed with its no-gap/no-overlap check (μ ≥ 2 xor μ = 1; terminal
   records are not GMN children — CU-2t). The read-back sentence is
   restated as Corollary CU-1-SURJ, GLOBALLY quantified, with the display
   that its dependencies are exactly ∀-instances of CU-1 + ADEQ.

## 2. Newly DECLARED inputs and consumption drops (churn ledger)

* **Declared pins (P-ROOT)/(P-KEY)/(FR≡)** (brief §0′, residue R-6): the
  cross-artifact identifications between the O-1thr machine and the O-2a
  stage flow (two abstractions of the ONE engine, MOVES §B2-DEF). Rev 1
  consumed this content SILENTLY (V27's finding-2b bracket was one symptom);
  rev 2 declares it. At order 1, (FR≡) = O-2a's PROVED (D3) by inspection;
  at orders ≥ 2 it is OPEN, owner = the MOVES transcription / GD-6 family.
  Its refutable order-2 content is exactly the §7.2 coherent-convention
  finding (slot-fresh reading refuted 1,818×) — already falsifier-shaped.
* **OL-6 DROPPED** (was rev 1's clause-(ii) engine, invoked once at an
  illegal index — V27 finding 2b): clause (ii) is re-founded on
  (R4)/(M4)/(P-KEY). NOTE FOR THE ORCHESTRATOR: this deviates from the
  O3adj §3.1 spec line "Step = IH + OL-6 + …" — the state-level pins
  replace the run-level OL-6, which remains CU-2's consumption inside O-2a
  Theorem 2(D).
* **OL-5 DROPPED**: the order-1 base runs on the PROVED (D3) + the O-1thr
  root kernel; rev 1's "converse-transport" gloss of OL-5 had silently
  strengthened an emission-direction lemma.
* **O-2a Theorem 2(B) dropped from the step** (saturation is now the
  record-only IrrHalts ⟺ μ_last = 1 route); 2(A)/(B) remain at the base
  vocabulary and the §4 split.
* **SPAN row deleted** (V27: listed without a use — correct).
* Consumption map rebuilt exhaustively: 23 rows incl. ROOT-M, (M4), the
  §1.4 definitional bundle + key-degree identity, the decode display, the
  pins (brief §5, with a precise exhaustiveness claim).

## 3. Home-brief pointer updates OWED (not executed here — other units' files)

* O-2a rev 5 §4 says full OL-2 (a)–(d) and full OL-3 are "consumed by NO
  theorem of this note; their consumer is the O-3 design seam (JC-2)" —
  CU-1 rev 2 is now that consumer by name; the O-2a ledger line should gain
  the pointer at its next revision.
* The normative O-2a cite moved rev 4 → rev 5 (V25 repaired; OL-3-min split
  on record); CU-1 rev 2 already cites rev 5.

## 4. Files

* `lean/notes/openmath/CU1_phaseB_verifybrief_rev2.md` — the self-contained
  rev-2 brief (hand THIS to the hostile pass; checklist §8, 11 charges —
  suggested priority: charges 1, 2, 4).
* `lean/notes/openmath/CU1_phaseB_attempt_rev2.md` — this record.
* Rev-1 files and the falsifier suite UNCHANGED (`o1thr_depth3_check.py`,
  results, logs — brief §7 carries the record verbatim).

**Grade: PROVED-UNVERIFIED conditional composition (rev 2).** Open residue =
OL-1 + full OL-2 + full OL-3 (GD-1..3) + O-1thr's interface residue
((M6b)(ii−)/(iii), (V1)/(V2)) + the pending home passes + (N\*-MAJ)'s
cluster discharge + the R-6 pins — every item named with owner in brief §6.
