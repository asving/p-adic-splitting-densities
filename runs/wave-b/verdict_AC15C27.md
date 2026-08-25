# Unit AC15C27 verdict — A-C.15 enacted (the C.69 bundle repair) + the C.27 chain-blocker attacked

**Charge:** (1) enact amendment A-C.15 — re-sign `ClassSizeSupplyData.read_form` (leanspec
NODE C.69), the bundle clause DEC1 found still quoting the machine-refuted naked C.64 law
after A-C.10 repaired the standalone axiom; (2) attempt the re-signed C.27 (`slot2_exact`
+ `hx`, the 6-row chain root per CCUR) from the landed corpus.
**Deliverables:** the leanspec edit (ChapC.lean, the one authorized clause) +
`leanfinal/Uniformity/ChapC/C27x.lean` + this verdict.  Nothing else touched; no commits
made by this unit.

## Mandate 1 — A-C.15 ENACTED

### The re-sign diff (leanspec/Leanspec/ChapC.lean, NODE C.69, `read_form` only)

```diff
+  -- [RE-SIGNED: A-C.15, 2026-08-25 — DEC1's stop-the-line side finding
+  -- (`runs/wave-b/verdict_DEC1.md`): this clause quoted the NAKED C.64 law, machine-REFUTED
+  -- (`ChapC/C64.lean`: `blockDegEq_false`, 3 = 2 at `(s2Frame, L₀, g₀)` over ℤ_[2]), so
+  -- `classSize_supply` was FALSE at the probe frame. A-C.10 (2026-08-24) re-signed the
+  -- standalone `blockDeg_eq` with the `hlab`/`hdvd` riders but missed this bundle field.
+  -- Repaired to the SAME protected shape (C.48's template): the block's label and
+  -- D′-divisibility are RIDERS, under which the law is C.35's landed
+  -- `hasLabel_natDegree_eq_of_dvd` (already PROVED as `blockDeg_eq_resigned`, `ChapC/C64.lean`).]
   read_form : ∀ (hπ : Irreducible π)
     (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O)
     {f : Polynomial O}, BlockContext L f →
+    HasLabel L (blockFactor L f) →
+    (F.e₁ * F.f₁) ∣ (blockFactor L f).natDegree →
     (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f
```

The two riders mirror the A-C.10 re-signed `blockDeg_eq` (leanspec C.64, `hlab`/`hdvd`)
byte-for-byte in clause form.  `cd leanspec && lake build Leanspec.ChapC` — **green**
(9276 jobs, exit 0) at enactment; two sibling enactments (A-C.14, A-C.16) later rebuilt
green on top of it.  **Provenance note:** this unit made no commits, but sibling commit
`19d1f7ec` (A-C.14, which committed the whole leanspec file state) swept the on-disk
A-C.15 edit into history; it is therefore already committed and twice re-verified.

### Consumer check (`rg classSize_supply|read_form|ClassSizeSupplyData` over leanfinal)

**No landed consumer exists.**  `classSize_supply` does not exist in leanfinal at all;
`read_form` appears only as a FIELD of the definitional twin
`leanfinal/Uniformity/ChapC/C140defs.lean:90–93` (unit DT1's byte-faithful structure twin
of the A-C.1 signed text), which nothing constructs or projects (remaining hits are
doc-comments in `E57p.lean`, `E23.lean`, `C141defs.lean`).  Nothing to repair.

**Named follow-up (outside this unit's fence):** the C140defs twin now quotes the
SUPERSEDED (refuted-shape) clause, so its "byte-faithful twin of the signed text" charter
is stale for this one field.  DEC1 already adjudicated the landed twin harmless (a
`Prop`-former may be uninhabited, and indeed the naked-shape structure is uninhabitable at
the probe frame), and it is DT1's file, so it was left untouched per the unit fence — but a
companion one-clause re-twin (thread the same two riders + an [A-C.15] rider comment) is a
cheap hygiene item for DT1 or the orchestrator.  Until then no unit should try to
inhabit or consume the C140defs `ClassSizeSupplyData` at the `read_form` field.

## Mandate 2 — C.27: TWO OF THREE CONSUMER READS PROVED; the general node stays open with a named obstruction

**Landed:** `leanfinal/Uniformity/ChapC/C27x.lean` — 10 declarations, zero `sorry`, no new
axioms, every `#print axioms` footprint exactly `{propext, Classical.choice, Quot.sound}`
(`lake env lean` exit 0).

| declaration | content |
|---|---|
| `Slot2ExactResignedStatement` | the ∀-closure of the A-C.10 RE-SIGNED `slot2_exact` (with the `hx` rider), byte-frozen Prop carrier — no axiom, signed name stays at the leanspec stub |
| `dv2Hgt_C` | `dv2Hgt L (C a) = ℓ • (e₁ • v(a))`, every frame, every `a` (both sides `⊤` at `a = 0`) |
| `dv2Hgt_C_pi` | the π-pin `dv2Hgt L (C π) = ℓ·e₁` |
| `dv2Hgt_X` | `dv2Hgt L X = ℓ·h`, every frame (the `deg key = 1` branch through the key's own purity value law; the `j = 1` slot dominated via `hκ` with no computation) |
| `dv2Hgt_key` | `dv2Hgt L F.key = u`, every frame — the SLOT half of the third read, isolating its gap to the norm side alone |
| `slot2_exact_resigned_const` | **the signed conclusion at `C := C a`, `a ≠ 0`, PROVED** (norm = `a^deg g` via `Algebra.norm_algebraMap` at the power basis; `hC`/`hC0` are theorems at this instance, so this is the full signed instance, strictly stronger) |
| `slot2_exact_resigned_pi` | the π-read with the value PINNED: `v = ℓ·e₁` — C.59's first read |
| `slot2_exact_resigned_X` | **the signed conclusion at `C := X`, PROVED** — the exact slot `slot2_exact_false` refuted; with `hx` the demanded identity IS the purity value law `e₁·v(g(0)) = h·deg g` (landed `isPure_addVal_coeff_zero`), plus `norm_adjoinRoot_root`.  End-to-end vindication of the A-C.10 re-sign — C.59's second read |
| `self_mem_monicFactors` | a monic irreducible is a member of its own `monicFactors` |
| `ramLeg_dvd_of_ell_one` | **the signed C.59 (`ramLeg_dvd`) PROVED on the extra rider `L.ℓ = 1`** — signed binder row verbatim + rider, via C61's landed `e1_dvd_ramIndexOf_of_mem_monicFactors`; no C.27 input needed at `ℓ = 1` |

### The precise obstruction (why the general re-signed C.27 did not fall)

The remaining consumer read is `C := F.key` (the `u`-read).  Its slot half is now landed
(`dv2Hgt_key`); the norm side `(e₁ℓ)·v(N_{O[x]/(g)}(Φ′ mod g)) = deg g · u` needs TWO
mechanisms absent from the landed corpus:

1. **Norm/resultant symmetry** — `v(N_{O[x]/(g)}(Φ′ mod g)) = v(N_{O[x]/(Φ′)}(g mod Φ′))`
   (both `± Res(g, Φ′)`).  Mathlib has no norm↔resultant bridge; B53c's
   `addVal_norm_key_eval` is the analogue one level down and its B53a/B53b span-transport
   proof is specific to residually-irreducible (order-1, slope-0) keys.
2. **Ramified level-1 exactness at the frame key** —
   `v(N_{AdjoinRoot Φ′}(A₀(β))) = f₁ · stageHeight(A₀)` for `deg A₀ < D′`: the slope-`h/e₁`
   analogue of B53b's `span_mk_eq_span_algebraMap_pow`.  Note C.27 carries NO
   `IsAdicComplete`, so a completion detour is not free — this must be polygon-native.
   Additionally, `HasLabel` alone closes the read only when `D′ ∣ deg g` (the floor endpoint
   `dv(A_{n₂})` is otherwise nonzero — the same D-CARRY fault line as C.64/C.67).

For GENERAL `C` (`deg C < D″`) the node further needs label heredity to `g`'s monic factors
(C.35's `BlockFrontier` frontier; its purity-of-factors half is the declared cite
`fgmn_dv_exact_mul`, C66b) plus per-factor level-2 exactness.  **Correction to CCUR's row:**
"self-contained norm-computation task" is accurate only for the three consumer reads (two
now landed); the general-`C` node sits STRICTLY ABOVE the `BlockFrontier` frontier, not
below it.

### The 6-row chain (CCUR: C.27 → C.59 → C.61 → {C.62, C.63} → {C.49, C.69}) — reachability after this unit

| row | status after this unit |
|---|---|
| C.27 `slot2_exact` | π-/const-/X-reads + all three slot halves PROVED (this file); general node open on obstruction 1–2 above |
| C.59 `ramLeg_dvd` | **PROVED at `L.ℓ = 1`** (`ramLeg_dvd_of_ell_one`, this file); general `ℓ` needs exactly the `F.key`-read's norm side (the two mechanisms) — nothing else |
| C.61 `tier1_typeOf` | already landed at `ℓ = 1` (`tier1_typeOf_of_ell_one`, C61.lean); at general `ℓ` it is one line off C.59 (C61's cash-out rule) — so the ℓ = 1 slice of the chain is now closed through C.61 |
| C.62 `tier1_typeOf_composed` | NOT independently reachable: same e-leg over `ComposedLabel` with its own `ℓ₃`; inherits C.59-general + additionally label heredity to factors (C.34/C.35 frontier) for the per-factor application |
| C.63 `classSize_separable` | NOT independently reachable: needs C.61 per separable-residual factor + the C.34 dissection frontier (`C34_BLOCKED_2026-08-18.md`) — blocked on BOTH chains |
| C.49 `composed_dictionary` / C.69 `classSize_supply` | C.49 consumes C.62 (blocked).  C.69 is DOUBLE-blocked and C.27 is not its binding constraint: clause 1 (C.63) is this chain, but clause 2 (C.64, now A-C.15-consistent) is READY (wrap `blockDeg_eq_resigned`) while clause 3 (C.67 repaired) sits on the independent `BlockFrontier` chain — so landing C.27 in full would STILL not land C.69 |

**Highest-leverage next node, named:** the ramified level-1 exactness lemma (obstruction
mechanism 2) — it is one level DOWN from C.27 (a `KeyFrame`-only statement, no
`LevelDatum`), unlocks the `F.key`-read via mechanism 1, hence C.59-general, hence C.61
general, and is the natural B53-family extension (B53b's Eisenstein-free analogue).

## Verification

* `cd leanspec && lake build Leanspec.ChapC` — green at enactment (9276 jobs) and re-run
  green at current HEAD (post A-C.14/A-C.16 sibling edits).
* `cd leanfinal && lake env lean Uniformity/ChapC/C27x.lean` — exit 0, zero warnings;
  all 10 `#print axioms` Lean-core only.
* Fence audit: `git status` shows this unit's writes = the leanspec clause + C27x.lean +
  this verdict; sibling files in flight (`C131af.lean`, `E57c.lean`, `C107ac14.lean`, …)
  untouched; no roll-up touched; no commits made.
