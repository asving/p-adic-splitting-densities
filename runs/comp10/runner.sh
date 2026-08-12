#!/bin/bash
# SOL comp10 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T4R3 T5R3 T1P9 T2P1v2"
echo "[$(date -u +%H:%M:%S)] comp10 queue start" > runs/comp10/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp10/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp10/${name}_brief.txt > runs/comp10/${name}_output.log 2> runs/comp10/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp10/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp10/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp10/progress.txt
  git add -f runs/comp10/${name}_output.log runs/comp10/${name}_brief.txt runs/comp10/progress.txt 2>/dev/null
  git commit -q -m "SOL comp10: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp10 queue done" >> runs/comp10/progress.txt
