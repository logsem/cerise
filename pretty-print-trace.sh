#!/usr/bin/env bash
#
# pretty-print-trace.sh
#
# Usage: ./pretty-print-trace.sh <trace‑json-file>
#
# The script extracts every `coqc` record, keeps only the generated
# *.vo files, sorts them by duration (longest first) and prints a table
# like:
#
#   Time        | File Name
#   ------------+----------------------------------------
#   0m58.65s    | theories/logrel/ftlr/Jalr.vo
#   12m03.27s   | some/very/long/path/file.vo
#   …
#   0m02.19s    | Total
#
# The first column is padded to a constant width (12 characters) so the
# vertical bar stays aligned even when the minutes part grows to two or
# three digits.
#
# Requires: jq, awk
# -------------------------------------------------------------------------

set -euo pipefail

usage() {
    cat <<EOF >&2
Usage: $0 <trace-json-file>

Pretty-print a table of .vo files with:
  - compilation time per file
  - heap usage (if available)
  - total build time (Alias builder)

Requires: jq, awk
EOF
    exit 1
}

# ---------- args ----------
if [[ $# -ne 1 ]]; then
    usage
fi

TRACE_FILE="$1"

if [[ ! -f "$TRACE_FILE" ]]; then
    echo "Error: file not found – $TRACE_FILE" >&2
    exit 1
fi

# ---------- total time (from Alias builder) ----------
TOTAL_SEC=$(
  jq -r '
    .[]
    | select(.name=="Alias builder: .")
    | (.dur / 1000000)
  ' "$TRACE_FILE"
)

# fallback if missing
TOTAL_SEC=${TOTAL_SEC:-0}

# ---------- main data ----------
jq -r '
  .[]
  | select(.name == "rocq")
  | .dur as $dur_us
  | ($dur_us / 1000000) as $sec

  | (
      (.args.stdout // "")
      | match("total heap size = ([0-9]+) kbytes")?
      | .captures[0].string
    ) as $heap

  | (.args.target_files // [])[]
  | select(endswith(".vo"))
  | sub("^_build/default/"; "") as $file

  | "\($sec)\t\($heap // 0)\t\($file)"
' "$TRACE_FILE" |
sort -nr -k1,1 |
awk -F'\t' -v total_sec="$TOTAL_SEC" '
BEGIN {
    col1 = 12
    col2 = 10
    col3 = 50

    max_heap = 0
    max_file = "-"

    printf "%-*s | %-*s | %-*s\n",
        col1, "Time",
        col2, "Heap",
        col3, "File"

    for (i=0;i<col1;i++) printf "-"
    printf "-+-"
    for (i=0;i<col2;i++) printf "-"
    printf "-+-"
    for (i=0;i<col3;i++) printf "-"
    printf "\n"
}

{
    sec  = $1 + 0
    heap = ($2 ~ /^[0-9]+$/ ? $2 : 0) + 0
    file = $3

    if (heap > max_heap) {
       max_heap = heap
       max_file = file
       }

    min = int(sec / 60)
    rem = sec - min * 60
    time = sprintf("%dm%05.2fs", min, rem)

    heap_gib = heap / (1024 * 1024)
    heap_str = (heap > 0 ? sprintf("%.2f GiB", heap_gib) : "-")

    printf "%-*s | %-*s | %s\n",
        col1, time,
        col2, heap_str,
        file
}

END {
    # ----- total time row -----
    min = int(total_sec / 60)
    rem = total_sec - min * 60
    total = sprintf("%dm%05.2fs", min, rem)

    printf "%-*s | %-*s | %s\n",
        col1, total,
        col2, "-",
        "Total time"

        # ----- max heap row -----
        max_gib = max_heap / (1024 * 1024)
        max_str = (max_heap > 0 ? sprintf("%.2f GiB", max_gib) : "-")

        printf "%-*s | %-*s | %s\n",
        col1, "-",
        col2, max_str,
        "Max memory usage (" max_file ")"
}
'
