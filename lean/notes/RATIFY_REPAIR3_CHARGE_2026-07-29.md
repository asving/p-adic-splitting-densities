# RATIFICATION REPAIR ROUND 3 (2026-07-29) — the confirm-2 residues

Repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities. Confirm-2 verdict:
lean/notes/RATIFY_REPAIR2_CONFIRM_CODEX_2026-07-29.md (READ IT — FLAG 2/1). The S5
residue was adjudicated V-side (no MovesS action). Two items remain here. Rules as
before: build green, Lean-core, no git, staged writes ≤4000 tokens/response.

## R3-A — D2's singleton-realizer bypass (OffsetPPin)
Confirm-2: `Realizes ν t := t = pol.liftOf ν` for a policy emitting any nonzero monomial
in the forced congruence class passes support_forced + realizes_unique + total while the
digit values and weight are wrong. Investigate BOTH options and execute the best:
  OPTION 1 (preferred if statable): type the DIGIT-VALUE law from §B2-DEF's (S6b′)
  offset-P paragraph — read MOVES_2026-07-24.md around lines 2000–2080 and 2450–2500
  (the §C C.0 cross-ref cites "§B2-DEF D.5's Bézout pair (s,t) (cf. lines ~2026/2472)")
  plus the §D4-R canonical-policy display (4646–4667). If the prescribed digits t_k are
  expressible as functions of node data reachable in MovesD/MovesC vocabulary (the
  node's (e,h,g,μ), gam, zbar, pat, the Stage carriers), add the law
  `digits_prescribed : Realizes ν t → ∀ k < ν.g, t.coeff (j₀ + k·e) = (the S6b′ value)`.
  Then the monomial policy fails it. Whatever piece genuinely needs the carry-algebra
  (HC-1) stays the named residue — but the residue must then be STRICTLY SMALLER than
  the whole formula (say exactly which piece).
  OPTION 2 (if the digit values are genuinely HC-1-vocabulary): reduce the claim
  surface honestly — rename/re-docstring CD_canonical to state only "CD at a
  W4-5-pinned policy" (no canonicity claim); the OffsetPPin docstring NAMES the
  remaining bypass ("a support-compatible singleton-realizer policy still satisfies
  this pin; excluding it = the W4-5 discharge duty, owner HC-1") so the seam text
  itself carries the residue. No vacuous tags either way.
  Report which option you executed and why.

## R3-B — the note-faithful uniform incidence (additive) + manifest fix
Confirm-2 ratified D11a's hne as the honest minimal repair but noted the note's
empty-shape incidence has RHS = #Box through the unique ∅-prefix fiber. Execute:
  (a) NEW theorem `mult_sum_opt` (D11a's file or a new unit): the uniform incidence
  over ALL shapes with the OPTION-LEVEL right-hand side — Σ_x mult x = (if reads = []
  then Nat.card (Box p m) else Σ_i Nat.card {x // x ∈ fiber i}) — or the PrefOpt-indexed
  sum if cleaner (the none class contributing the emptyFiber = univ card). Prove it
  (reads = [] branch: mult ≡ 1 and card univ; reads ≠ []: rewrite via mult_of_ne and
  cite the existing D11a with hne). Docstring: L5's ∅-inclusion (MOVES ~4788–4800) +
  "the note-faithful uniform form; D11a's hne form is the PrefIdx-indexed face".
  (b) Fix the stale MovesD MANIFEST entry for D11a (hypothesis_fields must record hne).

## Deliverables (≤4000 tokens): decls landed, build status, axiom check, option chosen
for R3-A with the reasoning, deviations.
