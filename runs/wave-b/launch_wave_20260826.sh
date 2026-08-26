#!/bin/bash
# Wave launcher, 2026-08-26 evening: AMND (HIGH) + BW1 + HW1 (default effort).
# Written while the codex 5h window sat at 96%; run AFTER the 22:26 reset.
# Idempotence guard: refuses to relaunch a unit whose out log is non-empty.
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities || exit 1
launch () {
  local U=$1 EFFORT_FLAG=$2
  if [ -s "runs/wave-b/out_${U}.log" ] || [ -f "runs/wave-b/verdict_${U}.md" ]; then
    echo "SKIP $U (out log or verdict already exists)"; return
  fi
  nohup codex exec $EFFORT_FLAG --sandbox workspace-write \
    "$(cat runs/wave-b/brief_${U}_codex.md)" < /dev/null \
    > "runs/wave-b/out_${U}.log" 2> "runs/wave-b/err_${U}.log" &
  disown
  echo "LAUNCHED $U (pid $!)"
}
launch AMND "-c model_reasoning_effort=high"
launch BW1 ""
launch HW1 ""
sleep 15
for U in AMND BW1 HW1; do echo "== $U err head =="; head -6 "runs/wave-b/err_${U}.log" 2>/dev/null; done
