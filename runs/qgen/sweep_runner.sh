#!/bin/bash
# PHASE-0a sweep queue: sequential codex runs over sweep_manifest.txt with budget throttle.
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
PROG=runs/qgen/sweep_progress.txt
echo "[$(date -u +%H:%M:%S)] sweep queue start ($(wc -l < runs/qgen/sweep_manifest.txt) runs)" >> $PROG
while IFS='|' read -r NAME PATHF A B TAG; do
  OUT=runs/qgen/sweep/EFF_${NAME}_${TAG}.log
  [ -s "$OUT" ] && grep -q "COMPILED:" "$OUT" && continue   # resume-safe: skip done
  PCT=$(codex-limits 2>/dev/null | grep -oP '7-day, \K[0-9]+')
  if [ -n "$PCT" ] && [ "$PCT" -ge 88 ]; then
    echo "[$(date -u +%H:%M:%S)] PAUSED at ${PCT}% before ${NAME}_${TAG} (resume after reset: rerun this script)" >> $PROG
    exit 0
  fi
  BRIEF=runs/qgen/sweep/brief_${NAME}_${TAG}.txt
  cat > $BRIEF << CHARGE
PHASE-0a EFFECTIVE-SPEC COMPILATION — ${NAME} shard ${TAG} (you are gpt-5.6-sol high; COMPILER, not author: resolve, never invent). Repo readable with shell at /data/users/asvin/math-and-lean/p-adic-splitting-densities. GOVERNING FORMAT: spec/EFF_TEMPLATE_v2.md — READ IT FIRST and obey every rule (DERIVATION field mandatory; XREF designations grep-verified with counts recorded, unverifiable = OPEN-CALL never invention; NON-IMPORTS; teeth inverse table; protocol-vs-absorption scope split; tables as [TABLE]; verbatim-or-[ASSEMBLED] fidelity). Exemplar of the format at full quality: spec/EFF-T3.md + its cross-read repair charge runs/qgen/EFFT3_crossread.md (skim for the failure modes to avoid).
TARGET NOTE: ${PATHF} — read it IN FULL (base + all r-rounds + riders + acceptance/status records; the highest governing section defines the effective text; supersessions living OUTSIDE your shard range still govern INSIDE it).
YOUR SHARD: emit statement-inventory units ONLY for material whose HOME section lies in lines ${A}-${B} of the note (resolution may draw on the whole file). Use temporary IDs EFF.${NAME}.${TAG}.<nn>; the merge run renumbers. If ${TAG} = full, also emit the header (blob hash, governing quotes, resolution rules), the consumption table, NON-IMPORTS, the teeth inverse table, and the self-audit; if a shard (sNofM), emit header/tables ONLY for material homed in your range plus a SHARD NOTES section (cross-shard supersessions you applied; boundary units split across the range edge — flag, do not truncate silently). Tag-sparse prose sections: add a BOUNDARY SELF-AUDIT (why each unit boundary was drawn where it was).
End with: EFF-${NAME}-${TAG} COMPILED: <n> statements / <n> xrefs verified / <n> open calls
CHARGE
  echo "[$(date -u +%H:%M:%S)] ${NAME}_${TAG} start (window ${PCT}%)" >> $PROG
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - < $BRIEF > $OUT 2> runs/qgen/sweep/err_${NAME}_${TAG}.log
  echo "[$(date -u +%H:%M:%S)] ${NAME}_${TAG} exit $? ($(wc -c < $OUT) B; $(grep -E 'COMPILED:' $OUT | tail -1 | cut -c1-70))" >> $PROG
done < runs/qgen/sweep_manifest.txt
echo "[$(date -u +%H:%M:%S)] sweep queue DONE" >> $PROG
