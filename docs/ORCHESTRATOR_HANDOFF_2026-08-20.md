# ORCHESTRATOR HANDOFF — read this to resume cold (2026-08-20)

Written by the outgoing orchestrator (an Opus instance) at a CLEAN CHECKPOINT: nothing in
flight, working tree clean, full `lake build` green. This is the tacit operating knowledge
that lives in a session's context rather than in the repo — the part that would otherwise be
lost on restart. Everything factual is in `docs/PROJECT_STATE.md` appends **#102, #103, #104**;
read those first, then this.

## 0. State of play in five lines

* Full build green; roll-up `Uniformity/ChapC.lean` at 87 imports; chapter I wired into the
  library root. Zero `sorry` anywhere, zero axioms outside the SIX signed cites.
* `python3 spec/frontier.py` → 612 nodes, 540 with files, 72 open (B 1, C 51, D 1, E 1, F 0,
  G 1, H 0, I 17).
* `python3 spec/census_driver.py` → the HONEST count: 1236 signed names, **638 PROVED**, 390
  carrier, 195 unlanded, 5 conditional, 5 placeholder-body, 2 cite, 1 unresolved.
* Chapter C holds ~147 of the 195 unlanded signed names: three quarters of all remaining work.
* Nothing is in flight. No agent needs resuming.

## 1. The two numbers, and which to quote

**Never quote the node count as progress.** "LANDED" in `frontier.py` means only that a file
exists; C.72, C.114, H.122, C.27 and C.40 all have green, Lean-core, `sorry`-free files whose
SIGNED statements are not proved. Quote the census (`638/1236` proved) and say what the other
buckets are. Appendix §MECH-2 of the census spells out why the naive 52%-vs-86% comparison is
unfair and why 83% is the fair figure — do not re-derive it wrongly.

## 2. The workhorse counterexample frame — the single most reusable asset here

`(s2Frame, L₀, g₀)` over ℤ_[2]: `Φ′ = x²−2`, `(e₁,f₁,h) = (2,1,1)`, `D′ = 2`, `H₀ = 1`,
`u = 3`, `ℓ = 1`, `r := ρ` (the residual of `g₀` itself), and
**`g₀ = x³ − 2x + 4 = x·Φ′ + 2²`, monic of degree 3.**

It carried FOUR independent results in one day. Two landed lemmas make it an instrument:
`hasLabel_g₀` (`ChapC/C35b.lean`) and `hx_g₀_false` (`ChapC/C61.lean`) — together they witness
that **"LABELLED but NOT x-pure" is inhabited**. All the surrounding arithmetic is landed
(`g₀_monic`, `g₀_natDegree = 3`, `g₀_not_dvd`, `g₀_divmod`, `dev_g₀_*`, `dvhgt_g₀_*`,
`dvside_g₀ = {0,1}`, `hne_g₀`).

**When you suspect a signed statement is false, try this frame FIRST.** Building a fresh frame
costs a unit-lifetime; instantiating this one costs a few lemma applications.

Known gap in it: **`Squarefree g₀` is NOT landed** and is the one blocker for the
`multiplicity_tie` refutation. It is true (`disc = −400 ≠ 0`). Note the `Separable` route is
NOT available: over `O` the resultant is a non-unit, so `IsCoprime g₀ g₀'` fails and
`Separable → Squarefree` cannot be used. It must be proved directly (degree-≤1 case analysis
plus a valuation contradiction, or the two-slope Newton factorization).

## 3. The three defect patterns — use the third check, it is the sharp one

* **A-C.7** — a HYPOTHESIS degeneracy: a guard nothing satisfies / that fails to bind. Four
  registry entries. Checklist at `blueprint/CHAP-C_tower_grammar.md` `### A-C.8.4`.
* **CONTENT-FREE TYPE** — every binder is fine but the TYPE asserts nothing (E.51's frozen
  type proved equivalent to bare ℕ arithmetic; five chapter-I declarations with `True` bodies,
  blueprint defect I-D12). **Any check for this must NOT be satisfiable by exhibiting
  `example : <carrier> := trivial`** — that certifies only that `True` is true.
* ★ **D-CARRY** — a CONCLUSION-vs-BODY mismatch: the body cannot determine the signed
  conclusion. **The standing check is "does this conclusion assert an EXACT DEGREE of a
  labelled object?"** That is mechanical and it is the real fault line: `slot2_exact`
  (refuted), `blockFactor_spec` clause 3 (blocked), C.40 clause (iii) (blocked),
  `multiplicity_tie` (predicted false) all do exactly that, because `IsDvPure`/`mult₂` are
  FLOOR divisions and cannot see `deg mod D′`. Earlier in the day this was mis-framed as "the
  missing `hx` guard"; `hx` was right for C.27 specifically and is NOT the general pattern.
  See `ChapC/HX_SWEEP_2026-08-20.md` §6.

## 4. Fleet operating rules that were learned the hard way

* **Under a ~25-minute expected agent lifetime the optimal strategy INVERTS: build the durable
  artifact FIRST, be careful second.** Carefulness that is not committed does not exist. Every
  unit that committed early kept all its work; one that reasoned first lost FOUR consecutive
  lifetimes. Put "commit a compiling skeleton within 10 minutes, then commit every green leg"
  at the TOP of every brief, and say why.
* **The orchestrator does the ANALYSIS and hands it over.** The best results came from the
  orchestrator working out which candidate was live and why, then briefing a unit to spend its
  short life on Lean rather than rediscovery.
* **The orchestrator wires roll-ups, never the unit.** Landing a node and wiring it are
  separate steps and agents die between them. This defect has recurred THREE times; nine
  modules were once outside `lake build`, including the signed A-C.8 cite pair.
* **Ratchet, never restart a unit from scratch.** Resume from transcript; if it died between
  "verified green" and `git commit`, verify and commit on its behalf. ~35 deaths today, zero
  work lost.
* **A sharpness certificate is worth more than an extra leg.** Proving a statement-minus-a-
  hypothesis FALSE converts "we need this" from a guess into a theorem
  (`tier1_typeOf_without_hx_false`, `slot2_exact_without_hC0_false`).
* Ask every unit to state **LANDED vs SUPPLY vs BLOCKED** explicitly. One had to be asked
  twice before admitting ten green lemmas were supply, not the node.

## 5. Traps that have actually bitten — including the orchestrator

* ★ **Never accept a bare name-grep as evidence about declarations.** `^axiom tier1_typeOf`
  HIT at `C61.lean:38` and nearly triggered a false stop-the-line; the hit was inside a FENCED
  CODE BLOCK in a docstring quoting the leanspec stub. Same trap as
  `package_three_of_drainage` (a unit found that one at `ChapH/H97.lean:26`). **Strip comments
  (`spec/signed_name_census.py`'s parser does) or check `#print axioms`.**
* **`#print axioms` output WRAPS across lines.** Reconstruct the full list before calling a
  footprint core — a naive per-line grep reported 6 false non-core entries.
* **`content_free` in the census instrument returns `(bool, reason)`, not `bool`.** Treating
  the tuple as truthy reported **494** placeholders instead of 5.
* **The leanspec RETIREMENT FORM is evidence of PROVED, not of unresolved.** Where the spec
  deletes a stub and leaves an `example` USING the landed decl, spec elaboration IS a
  type-level check. Mis-filing these produced a spurious 100/148 unresolved bucket and an
  absurd "0 proved" for chapter G.
* **Orchestrator restatements of a record's mechanism are NOT evidence.** A brief asserting
  "unipotence is why the transport is floor-preserving" was false, and the unit was right to
  reject it. The record it came from is wrong too.
* Never a bare `lake build` inside a unit (hangs at final-job commit on this NFS box); per-file
  `lake env lean`. Never pipe a command whose exit code you need. Do not read build logs with
  a file-reader — grep them (one read cost ~73k tokens for an exit code already in hand).

## 6. Owner gates — do not cross these without the owner

Only two: (a) the main capstone Lean statement, (b) importing a new literature cite. The cite
allowlist is exactly SIX: `exists_slope_factorization`, `fgmn_residual_mul`,
`agnprw_termination`, `bBox1_cite`, `exists_dvDissection`, `fgmn_dvDissection_factor_eq`.
Owner-gated content lands as a Prop CARRIER per A-C.8.5 (`ChapC/C72.lean` is the worked
example), never as a temporary axiom.

**Pending owner items:** the FGMN published-number print-read (Thm 6.6 arXiv-v3 vs predicted
published 6.5); the B39a human-review rider; the `WeldObligations.w1` dead-field amendment;
**NEW — the C.27 re-sign question** (`slot2_exact` is REFUTED; the honest repair is to add the
x-purity guard, recorded but not enacted); **NEW — I.10a/I.10b**, the tower-instantiation
sockets on the critical path, are signed as PLACEHOLDERS (`True`, and `… ∧ True`).

## 7. The one status being held at argument-strength — do not upgrade it

C.53's **leg 2 is argued FALSE in prose, NOT machine-checked.** Two consequences rest on that
argument, including a VACUITY finding: that `C53.lean`'s `towerLocus_fibration_of_frontier` is
a true theorem with a FALSE hypothesis. One ingredient of the general argument is C.50's
**transcribed scope note** — corpus prose, not a landed theorem. The machine-check should use
the EXPLICIT NUMERIC WITNESS route instead (given in full in
`ChapC/C53_LEG2_REFUTED_2026-08-20.md`), which avoids the prose dependency. `C53c.lean` is a
beachhead only. **This is the top item in the queue.**

## 8. Restart mechanics

* The 15-minute orchestrator tick is a **session-only** cron job and dies with the session —
  re-create it. Ticks should be cheap no-ops: git log + `ListAgents`, and stop if nothing
  changed.
* Stale untracked scratch in the tree (`leanfinal/scratch*`, `runs/qgen/sweep/brief_*`) is
  leftover exploration from earlier waves, safe to ignore; `docs/references/*.pdf` is an
  untracked reference.
* Reproduce the two measurements with `python3 spec/frontier.py` and
  `python3 spec/census_driver.py`; both are committed and deterministic.
