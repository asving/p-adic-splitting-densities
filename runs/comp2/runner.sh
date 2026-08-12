#!/bin/bash
# SOL comp2 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T1P2 T1CC3 T3P1 S6"
echo "[$(date -u +%H:%M:%S)] comp2 queue start" > runs/comp2/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp2/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp2/${name}_brief.txt > runs/comp2/${name}_output.log 2> runs/comp2/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp2/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp2/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp2/progress.txt
  git add -f runs/comp2/${name}_output.log runs/comp2/${name}_brief.txt runs/comp2/progress.txt 2>/dev/null
  git commit -q -m "SOL comp2: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp2 queue done" >> runs/comp2/progress.txt
