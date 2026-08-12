#!/bin/bash
# SOL comp7 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T1P7 T2R2 T4P2 T5P2"
echo "[$(date -u +%H:%M:%S)] comp7 queue start" > runs/comp7/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp7/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp7/${name}_brief.txt > runs/comp7/${name}_output.log 2> runs/comp7/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp7/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp7/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp7/progress.txt
  git add -f runs/comp7/${name}_output.log runs/comp7/${name}_brief.txt runs/comp7/progress.txt 2>/dev/null
  git commit -q -m "SOL comp7: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp7 queue done" >> runs/comp7/progress.txt
