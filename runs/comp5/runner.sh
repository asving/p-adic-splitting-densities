#!/bin/bash
# SOL comp5 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T1P5 T2R1 T3CC T4P1 T5P1"
echo "[$(date -u +%H:%M:%S)] comp5 queue start" > runs/comp5/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp5/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp5/${name}_brief.txt > runs/comp5/${name}_output.log 2> runs/comp5/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp5/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp5/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp5/progress.txt
  git add -f runs/comp5/${name}_output.log runs/comp5/${name}_brief.txt runs/comp5/progress.txt 2>/dev/null
  git commit -q -m "SOL comp5: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp5 queue done" >> runs/comp5/progress.txt
