#!/bin/bash
# SOL comp4 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T1R4 T3P3 T2P1 T4C T5C"
echo "[$(date -u +%H:%M:%S)] comp4 queue start" > runs/comp4/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp4/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp4/${name}_brief.txt > runs/comp4/${name}_output.log 2> runs/comp4/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp4/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp4/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp4/progress.txt
  git add -f runs/comp4/${name}_output.log runs/comp4/${name}_brief.txt runs/comp4/progress.txt 2>/dev/null
  git commit -q -m "SOL comp4: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp4 queue done" >> runs/comp4/progress.txt
