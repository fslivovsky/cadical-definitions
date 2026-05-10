#!/usr/bin/env bash
# Run get_definitions on a QDIMACS file, restricting the definability search
# to the variables listed in <same-dir>/<stem>.defined (single line,
# whitespace-separated, 0-terminated).  Pass extra options (e.g. --basic,
# --write-definitions <path>) as additional arguments.
#
# Usage: find_defined_restricted.sh <file.qdimacs> [get_definitions-opts...]
set -euo pipefail

GET_DEFINITIONS="$HOME/tools/cadical-definitions/build/get_definitions"

if [ ! -x "$GET_DEFINITIONS" ]; then
    echo "Error: get_definitions not found or not executable at $GET_DEFINITIONS" >&2
    exit 1
fi

if [ "$#" -lt 1 ]; then
    echo "Usage: $0 <file.qdimacs> [get_definitions-opts...]" >&2
    exit 1
fi

input="$1"
shift
extra_args=( "$@" )

if [ ! -f "$input" ]; then
    echo "Error: input file not found: $input" >&2
    exit 1
fi

dir="$(dirname -- "$input")"
base="$(basename -- "$input")"
stem="${base%.*}"
restrict="$dir/$stem.defined"

if [ ! -f "$restrict" ]; then
    echo "Error: restriction file not found: $restrict" >&2
    exit 1
fi

"$GET_DEFINITIONS" "${extra_args[@]}" --defined-variables "$restrict" "$input"
