#!/bin/bash
# SOL comp9 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T2C2 T1P8 T4P3 T5P3"
echo "[$(date -u +%H:%M:%S)] comp9 queue start" > runs/comp9/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp9/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp9/${name}_brief.txt > runs/comp9/${name}_output.log 2> runs/comp9/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp9/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp9/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp9/progress.txt
  git add -f runs/comp9/${name}_output.log runs/comp9/${name}_brief.txt runs/comp9/progress.txt 2>/dev/null
  git commit -q -m "SOL comp9: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp9 queue done" >> runs/comp9/progress.txt
