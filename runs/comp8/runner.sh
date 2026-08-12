#!/bin/bash
# SOL comp8 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T1R6 T2P3 T4R2 T5R2"
echo "[$(date -u +%H:%M:%S)] comp8 queue start" > runs/comp8/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp8/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp8/${name}_brief.txt > runs/comp8/${name}_output.log 2> runs/comp8/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp8/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp8/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp8/progress.txt
  git add -f runs/comp8/${name}_output.log runs/comp8/${name}_brief.txt runs/comp8/progress.txt 2>/dev/null
  git commit -q -m "SOL comp8: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp8 queue done" >> runs/comp8/progress.txt
