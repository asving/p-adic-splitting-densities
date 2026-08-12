#!/bin/bash
# SOL certification runner 2: discharge confirmations + C-run adjudications
# (goal: Asvin 2026-08-12). LAUNCH ONLY AFTER runs/cert/runner.sh drains
# (progress.txt shows "cert queue done") — never two codex queues at once.
# Extend NAMES with C-adjudication briefs (Cx_*_adj) before launching.
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="D2a_w12 D2b_genhn D2c_he6 D2d_he6r1 D2e_he3 D2f_genind E9_w11_annex E10_sigmalaw_annex E11_boxes_annex E1_liftcorner E2_grtja E3_grtjb E4_grtjc E5_grtw2 E6_weldmaster E7_hmenu3 E8_jd0 E12_gentow5 E13_gentow3"
echo "[$(date -u +%H:%M:%S)] cert2 queue start" > runs/cert2/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/cert2/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/cert2/${name}_brief.txt > runs/cert2/${name}_output.log 2> runs/cert2/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/cert2/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|STACK-VERDICT)' runs/cert2/${name}_output.log | tail -1 | cut -c1-90))" >> runs/cert2/progress.txt
  git add -f runs/cert2/${name}_output.log runs/cert2/${name}_brief.txt runs/cert2/progress.txt 2>/dev/null
  git commit -q -m "SOL cert2: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] cert2 queue done" >> runs/cert2/progress.txt
