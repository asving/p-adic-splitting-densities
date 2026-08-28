# UNIT P1U — (P1) IsTestKey ⟹ IsMuKey + (P2) the ¬MuDvd bridge + the (P3) floor adjudication

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities.

## Context

DV2G (runs/wave-c/verdict_DV2G.md — READ FIRST; landed file
leanfinal/Uniformity/ChapC/C134dv2g.lean) reduced the signed F1.3–F1.6 chain to exactly
three named premises:
- **(P1)** `IsTestKey L Ψ → IsMuKey L Ψ` — the Montes "test polynomials are key
  polynomials" content at the level valuation. THE one genuinely new mechanism left in
  the family. `IsTestKey`'s landed definition: rg through leanfinal/Uniformity
  (C53c/C80 territory — the landed witnesses instantiate it); `IsMuKey` is DV2G's new
  generic predicate (C134dv2g.lean, the FGMN Def 1.2/1.4 shapes at the level valuation,
  built on C130kp0's level-1 shapes).
- **(P2)** the complement's `¬ MuDvd L Ψ g` from F1.2's residual clause
  (`C134f12c.block_complement_notdvd`'s conclusion) — the residual↔initial-form
  correspondence at level 2. DV2G expects it to ride P1's apparatus.
- **(P3)** a statement-level fence gap: the SIGNED F1.4–F1.6 floor is
  `ℓ₂ · L.seam < u₂`, an `L.ℓ`-factor WEAKER than the engine-honest
  `ℓ₂ · (L.ℓ · L.seam) < u₂` that DV2G's generic discharge needs.

## Your charge

1. **(P1) cite-vs-prove adjudication, then execution.** The source candidates: FGMN
   (the residual-ideals paper in docs/references/FGMN_residual_ideals_2015_authorpdf.pdf)
   and the GN genetics paper — locate the exact "test polynomial ⟹ key polynomial"
   statement (or its contrapositive apparatus: a test polynomial's minimality forces
   key-hood at μ). Then EITHER (a) prove it in Lean from the landed key-criterion banks
   (C132kp*'s `s2Mu3_key_criterion` pattern generalizes? DV2G's IsMuKey has the criterion
   shape — check whether the C134dv2g bank + Theorem M already carries the proof; this
   repo PREFERS proofs over cites), OR (b) if it is genuinely cite-grade (a real theorem
   of the papers whose proof needs unformalized machinery), draft the declaration +
   faithfulness entry per the axiom policy (docs/AXIOM_FAITHFULNESS.md format) and STOP
   for the orchestrator (declaring a new cite is an orchestrator pass — deliver the
   draft, do not declare). Route (a) strongly preferred; price it honestly first.
2. **(P2)**: state and prove the bridge (the level-2 residual read of g is not divisible
   by the key's residual ⟹ ¬ MuDvd) — the μ₃ bank's initial↔residual iff
   (C132kp6b.s2Mu3_hconv + the forward direction) is the S2 model; DV2G's generic
   predicates are the target vocabulary.
3. **(P3) adjudication** (deliver a recommendation, do NOT edit leanspec): is the signed
   weaker floor provable from the engine floor AT THE SITES F1.4–F1.6 are consumed
   (check the consumers: who instantiates ℓ₂/u₂ and with what margins — at S2 the
   margin is 20 < 21, so the ℓ-factor matters!), or is an A-C amendment forced? If
   forced, write the exact amendment text (the A-C.17..21 style) for the orchestrator.
4. Anything landed goes in a NEW file leanfinal/Uniformity/ChapC/C134p1.lean (header
   [P1U 2026-08-28]; namespace Uniformity.Density.Tower.C134p1; AxCheck footer,
   Lean core + at most the dissection cite). Verify per increment:
   `cd /data/users/asvin/math-and-lean/p-adic-splitting-densities/leanfinal && timeout
   580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134p1.lean`; NEVER bare `lake build`.
   Skeleton first; disk after every fill; bounded repair ~3/error.
5. If P1+P2 land, RE-ATTEMPT the signed F1.4–F1.6 (modulo P3's resolution — if P3 blocks
   them as signed, land the engine-floor twins under blueprint names and record the
   supersession candidates for the P3 amendment).

## Deliverables

- `runs/wave-c/verdict_P1U.md`: P1 route + result; P2 status; P3 recommendation with the
  consumer-margin analysis; per-decl footprints.

## Rules

No git commits. No edits to landed .lean/leanspec files. Statement fence absolute; the
P3 finding is an ADJUDICATION deliverable, not a license to touch signed bytes. Owner's
paper never citable. Honest BLOCKED-BECAUSE beats forcing.
