# Unit CC09 verdict — chain-carrier node CC-9 (legal node points)

## Verdict: LANDED

One new file, `leanfinal/Uniformity/ChapC/C130pt.lean` (imports C130k + C130s2; nothing else
touched). The legal node-point LAYER per design §4.2 / §8 row C.130g / §10 row CC-9:
`Point`/`Pt` exported as the legal P-locus, the exact key values at points, the transported
`ψ`-root, and the ambient letters — all derived from the CC-1 `NodePointSource` source fields,
never stored, never inhabited. Zero `sorry`, no new axiom, no `unsafe`, no `True` body,
**no descent claim anywhere** (grep tooth below). 32 declarations, all Lean-core.

## Declarations (namespace `Uniformity.Density.Tower`)

Transport side (`TerminalReceiver`, receiver-parametric):

* `ambientHom` (+ `_def` rfl pin, `_injective`) — GENTOW5.16's transport `ι`, ambient-valued:
  the named `(algebraMap Kt L).comp (levelHom i)` composite `psi_root` evaluates through
* `psiTransported` (+ `_def` pin) — the transported level-`i` minimal polynomial `ψ_i`
* `psiTransported_monic` / `_natDegree` (= `f_(i+1)`) / `_natDegree_pos` — C.83 `hψ`/`hf`
  transported (gauge-live guarded)
* `psiTransported_coeff_zero_ne_zero`, ★`psiTransported_root_ne_zero` — the **Lˣ-forcing
  theorem** (freeze v2 §4: "`ψ_(a+1)(0) ≠ 0` … admits only an `Lˣ` value" is now a THEOREM:
  every root of the transported `ψ` is nonzero)

Point layer (`NodePointSource`):

* `LegalPt`, `legalPt_nonempty`, `legalPoint`, `legalPoint_mem` — GENTOW5.19's `P_{i+1}` as a
  subtype + the canonical (choice) legal point — the supply for CC-8's `RealizedInput.point`.
  Nonemptiness stays the carried `point_exists` SOURCE field (the row's own conditionality)
* `pointHgt_zero` / `pointHgt_mul` / `pointHgt_pow` — pointwise dv-arithmetic derived from
  `pointHgt_eval` + the `valueOn` source laws (stage-live guarded)
* `key_value_coe` / `key_value_ne_top` — GENTOW5.19's exactness both halves (`= u_(i+1)`
  exactly, `< ∞` derived not assumed)
* ★`key_value_pow` / `key_value_pow_e` — `pointHgt(Φ_i^m) = m·u_(i+1)` exact; at `m = e_(i+1)`
  this is the height-arithmetic half of GENTOW5.16's `Λ_i` dv-value-0 DERIVATION sentence
  (`dv_i(Φ_i^{e_{i+1}}) = e_{i+1}u_{i+1}`). The normalizer half is CC-4/CC-10's, not claimed
* `ambientLetter_ne_zero` (units read-off), `psi_root_ambientHom` (source law at the named
  hom), ★`ambientLetter_isRoot` (the transported ψ-root as an actual `IsRoot`),
  `ambientLetter_ne_zero_forced` (nonzeroness re-derived from root law + `ψ(0) ≠ 0` alone)
* `LegalGentowNodeRead` (+ `Iff.rfl` pin, projections `.pt`/`.key_value`/`.psi_isRoot`) —
  freeze-v2 layer C.130g's legality read: THREE clauses (legality, exact key value, ψ-root),
  nothing Kt-valued. ★`legalGentowNodeRead_of_pt` (the producing theorem: every legal point
  satisfies the full read on gauge-live range), `exists_legalGentowNodeRead`

Teeth (S2 elaboration regressions, instance-parametric — no instance claimed): gauge-live at
depth 2 forces `i = 1`; the frame key `x² − 2` reads exactly `5 = u₂` at any legal point;
transported `ψ` has degree `f₂ = 1`; the legality read specializes and is realized.

## Descent-exclusion audit (the node's explicit fence)

`rg -n "arenaRead|canonicalRead|towerRead|peelUnit|HVarthetaRes|VarthetaRes|Ktˣ"
Uniformity/ChapC/C130pt.lean` → **zero hits** (not even in comments). No Kt-preimage
proposition, no read-agreement equation; unpacking a socket still leaves exactly the OM-8 L3
descent goal, as freeze v2 requires. Threshold/window teeth NOT duplicated (CC-7 owns
`thresholdZ_lt_u_succ` in C130th).

## ⚠ Integration finding for the orchestrator (SUPPLY, not mine to fix)

**C130k (CC-1) and C130tr (CC-3) cannot be co-imported**: both declare
`Uniformity.Density.Tower.instDecidableStageLive` →
`import Uniformity.ChapC.C130tr failed, environment already contains
'Uniformity.Density.Tower.instDecidableStageLive' from Uniformity.ChapC.C130k` (reproduced
2026-08-24). Latent so far (every landed CC file imports only the C130k side) but it BLOCKS
CC-10/CC-11/CC-17, which need the receiver construction AND `NodePointSource` together. Fix is
one-line cross-unit surgery (delete/rename C130tr's duplicate; C130k's is the richer
`decidable_of_iff` form). Consequently the natural CC-3 tie — canonical receiver's
`ambientHom` at a live level `= algebraMap ∘ towerHom`, junk-free — is DEFERRED (it is
`rfl`-adjacent via `terminalReceiver_levelHom_live` once the clash is fixed; noted in the
module docstring). CC03's junk-field finding does not propagate into this layer: `psi_root`
reads `levelHom` only at gauge-live `i`, where the canonical receiver never reads `junk`.

## Verification

```text
cd leanfinal && lake env lean Uniformity/ChapC/C130pt.lean
```

Exit 0 (2026-08-24); output = exactly the 32 `#print axioms` lines, each
`[propext, Classical.choice, Quot.sound]`; no errors, no warnings, no `sorry`.
