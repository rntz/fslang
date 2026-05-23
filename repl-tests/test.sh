#!/usr/bin/env bash
# Run every repl-tests/*.fsl through the repl and diff its combined
# stdout+stderr against the matching .expect file in unified-diff format.
# Exit status is the number of failing tests (0 == all pass).

set -e
cd "$(dirname "$0")"
passed=()
failed=()
second=false

for fsl in *.fsl; do
  $second && echo
  name="${fsl%.fsl}"
  expect="$name.expect"
  if [ ! -f "$expect" ]; then
    echo "SKIP $name (no .expect file)"
    continue
  fi
  if racket ../fslang-repl.rkt < "$fsl" 2>&1 | \
      diff --color --unified "$expect" -; then
      # reset colors; diff can leave colors on if file is missing trailing newline.
      echo -en "\033[0m"
      echo "PASS $name"
      passed+=("$name")
  else
      echo -en "\033[0m"        # reset colors
      failed+=("$name")
  fi
  second=true
done

echo
echo "PASSED: ${passed[@]}"
echo "FAILED: ${failed[@]}"
exit "${#failed[@]}"
