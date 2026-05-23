#!/usr/bin/env bash
# Run every repl-tests/*.fsl through the repl and diff its combined
# stdout+stderr against the matching .expect file in unified-diff format.
# Exit status is the number of failing tests (0 == all pass).

set -e
cd "$(dirname "$0")"
tmpdir="${TMPDIR:-/tmp}"
passed=()
failed=()

for fsl in *.fsl; do
  name="${fsl%.fsl}"
  expect="$name.expect"
  if [ ! -f "$expect" ]; then
    echo "SKIP $name (no .expect file)"
    continue
  fi
  actual="$tmpdir/repl-test.$$.$name.out"
  racket ../fslang-repl.rkt < "$fsl" > "$actual" 2>&1
  if diff -s "$expect" "$actual" >/dev/null; then
      echo "PASS $name"
      passed+=("$name")
      rm "$actual"
  else
      echo "FAIL $name"
      failed+=("$name")
  fi
done

nfailed="${#failed[@]}"
if (( $nfailed > 0 )); then
    echo
    for name in "${failed[@]}"; do
        expect="$name.expect"
        actual="$tmpdir/repl-test.$$.$name.out"
        diff --color=auto -U 2 "$expect" "$actual" || true
        # reset colors; diff can leave colors on if file is missing trailing newline.
        rm "$actual"
        #echo -e "\033[0m"
        echo
    done
fi

echo "PASSED: ${passed[@]}"
echo "FAILED: ${failed[@]}"
exit "${#failed[@]}"
