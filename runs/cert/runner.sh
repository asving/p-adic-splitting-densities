#!/bin/bash
# SOL end-to-end certification runner (goal: Asvin 2026-08-12)
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
echo "[$(date -u +%H:%M:%S)] cert queue start" > runs/cert/progress.txt
for name in A0_hex3 A1_w12 A2_genhn A3_he6 A4_he6r1 A5_he3 R9_drain_repair R10_wi_pass3 D1a_gentow5 D1b_gentow3 C1_liftcorner C2_grtja C3_grtjb C4_grtjc C5_grtw2 C6_weldmaster C7_w11 C8_hmenu3 C9_sigmalaw C10_jd0 C11_boxes; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/cert/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/cert/${name}_brief.txt > runs/cert/${name}_output.log 2> runs/cert/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/cert/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE)' runs/cert/${name}_output.log | tail -1 | cut -c1-90))" >> runs/cert/progress.txt
  git add -f runs/cert/${name}_output.log runs/cert/${name}_brief.txt runs/cert/progress.txt 2>/dev/null
  git commit -q -m "SOL cert: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] cert queue done" >> runs/cert/progress.txt
