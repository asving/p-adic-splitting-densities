# UNIT A22E verdict — A-C.22 ENACTED: the engine-honest floor in the signed F1.3–F1.6 rows (2026-08-28)

## Outcome

**ENACTED, exactly per P1U's draft.**  The four signed floor binders (F1.3 = C.37
`dv2Supp_translation`, F1.4 = C.39 `dv2ResPoly_scalar`, F1.5 = C.38
`dv2ResPoly_radical_eq`, F1.6 = C.64 `mult₂_readable`; F-row names per verdict_CFS's
table, C-node names per verdict_P1U §P3 — same four declarations) were re-signed from the
seam floor to the engine-honest floor.  Conclusions byte-unchanged (diff empty — verified
below).  leanspec `ChapC.lean` re-elaborates exit 0.  One comment-only leanfinal ripple
(the now-closed (P3) record in `C134dv2g.lean`), per-file exit 0 + direct-importer roll-up
exit 0, axiom footprints unchanged.

## The before/after hypothesis diff (each of the 4 rows, identical hunk)

```diff
-    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * L.seam < u₂)
+    {u₂ ℓ₂ : ℕ} (hℓ₂ : 0 < ℓ₂) (hseam : ℓ₂ * (L.ℓ * L.seam) < u₂)
```

Sites (post-edit `leanspec/Leanspec/ChapC.lean`): C.37 at the binder line following the
new 17-line A-C.22 record (pre-edit line 1639); C.38 (pre-edit 1693); C.39 (pre-edit
1718); C.64 (pre-edit 2311).  **Conclusion diff: EMPTY at all four rows** — `git diff`
shows exactly 4 changed binder lines + 4 inserted comment records (29 insertions,
4 deletions; no other line touched).

## The amendment record (as placed)

Full dated record above C.37 (style per the A-C.17..A-C.21 precedents: `-- [RE-SIGNED:
A-C.22, 2026-08-28 — P1U/verdict_P1U §P3] ...`), quoting the machine forcing:

* **Engine consumption**: the landed generic discharge
  (`leanfinal/Uniformity/ChapC/C134dv2g.lean`, Part 7 (P3)) consumes the OUTER floor
  `ℓ₂ * KΨ < u₂` at the test key's own level grade
  `KΨ = (L.ℓ · d_r) · L.u = L.ℓ * L.seam` (`C131aa.dvSupp_testKey`); its slot-1 sharp
  carry bound is TIGHT (`C132nv3b`), so no rearrangement recovers the engine premise from
  the seam floor.
* **S2/μ₃ margin arithmetic**: `C130np4.seam_s2Tower` (`L.seam = 5`),
  `C130np4.ell_mul_seam_s2Tower` (`L.ℓ * L.seam = 10`, `L.ℓ = 2`), outer pair
  `(u₂, ℓ₂) = (21, 2)` per `C132nv4`/`C132rp*`: the engine needs `2·(2·5) = 20 < 21`; the
  pre-A-C.22 floor exposed only `10 < 21`.
* **The generic implication is FALSE**: same `L`, `(ℓ₂, u₂) = (2, 11)` — old premise
  holds (`10 < 11`), engine premise fails (`20 ≮ 11`); and no consumer supplies a
  strengthening (verdict_P1U §P3's repo-wide exact-name search: the four names have zero
  callers outside their declarations — re-verified this unit, same result).

Pointer records (2 lines each) above C.38, C.39, C.64.

## Scope fence (floor occurrences deliberately NOT amended)

`rg 'ℓ₂ \* L\.seam'` over leanspec `ChapC.lean` post-edit leaves exactly two seam-form
sites, both out of A-C.22's scope (the draft names only the four rows; recorded in the
C.64 pointer comment):

* **C.65 `dv2_length_sum`** (∀-clause floor, pre-edit line 2326) — its landed proof
  `C134f12c.dv2_length_sum` (F1.7) PROVES the statement with the weak floor as a premise
  inside the ∀ (about `blockFactor L f` alone; weaker premise = stronger proved theorem).
  Amending it would DISCARD a landed proof for no engine need.
* **C.68 `dv2Pin_translation_interior`** (pre-edit line 2358) — same family, but no
  landed engine forces its floor yet; if a future generic discharge of C.68 hits the same
  wall, that is a follow-up amendment with its own forcing record.
* (Also `dv2_read_congr_res_guarded`, C.118 family, pre-edit line 3385 — different
  mechanism (visibility congruence), PROVED as-is at the seam form in
  `leanfinal/Uniformity/ChapC/C118b.lean:453`; its weak floor is machine-validated, not
  an engine gap.)

`blueprint/CHAP-C_tower_grammar.md` still quotes the four pre-amendment statements
(prose blueprint, not compiled surface) — flagged for the next blueprint refresh, not
edited here.

## leanfinal ripple (one file, comment-only)

`rg` for the four names and for both floor shapes across `leanfinal/` found **no landed
declaration consuming the signed floor shape** — the only landed hits are prose.  One
prose record was made STALE by the enactment: `C134dv2g.lean` Part 7's (P3) bullet
("either the signed statements gain the stronger fence, or …" — A-C.22 is that first
horn).  Appended a dated 4-line `[A-C.22 ENACTED …]` note inside that comment; (P1)
(test-key ⟹ μ-key, the GN Lemma 3.1(3) wall) and (P2) (complement `¬ MuDvd`) remain the
open premises, as the note states.  No proof line touched.

## Verification

| check | command | result |
|---|---|---|
| leanspec ChapC | `cd leanspec && timeout 580 ~/.elan/bin/lake env lean Leanspec/ChapC.lean` | **exit 0, 40.4s** (only diagnostic: the pre-existing `sideCensus` overlapping-instances lint at line 2774, untouched region) |
| rippled file | `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134dv2g.lean` | **exit 0, 5.3s**; `#print axioms` unchanged (Lean core; `dv2Supp_translation_of_muKey` carries only the allowlisted `Uniformity.Density.Tower.exists_dvDissection`) |
| scoped roll-up | `cd leanfinal && timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapC/C134p1.lean` (the sole direct importer besides the `Uniformity/ChapC.lean` aggregate) | **exit 0, 4.8s**; footprints exactly as verdict_P1U recorded |
| diff minimality | `git diff --stat leanspec/Leanspec/ChapC.lean` | 29 insertions / 4 deletions, all 8 hunks = the 4 binders + 4 records; conclusions and every other signed byte unchanged |

Review row appended to `docs/REVIEW_QUEUE_2026-08-26.md` Tier 2 (newest-first, top row).
No git operations performed.
