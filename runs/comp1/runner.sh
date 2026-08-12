#!/bin/bash
# SOL comp1 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="T1CC T1B T1P T3R S5 S7"
echo "[$(date -u +%H:%M:%S)] comp1 queue start" > runs/comp1/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp1/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp1/${name}_brief.txt > runs/comp1/${name}_output.log 2> runs/comp1/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp1/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp1/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp1/progress.txt
  git add -f runs/comp1/${name}_output.log runs/comp1/${name}_brief.txt runs/comp1/progress.txt 2>/dev/null
  git commit -q -m "SOL comp1: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp1 queue done" >> runs/comp1/progress.txt
