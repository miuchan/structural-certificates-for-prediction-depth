#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
    printf 'Usage: %s <Noto Serif CJK font directory>\n' "$0" >&2
    exit 2
fi

font_dir=$1
for font in NotoSerifCJK{sc,jp}-{Regular,Bold}.otf; do
    if [[ ! -f "$font_dir/$font" ]]; then
        printf 'Missing font: %s/%s\n' "$font_dir" "$font" >&2
        exit 2
    fi
done

paper_dir=$(cd "$(dirname "$0")/../paper" && pwd)
build() {
    local stem=$1
    shift
    typst compile --ignore-system-fonts --creation-timestamp 1794268800 "$@" \
        "$paper_dir/$stem.typ" "$paper_dir/$stem.pdf"
}

build structural-certificates
build structural-certificates.zh-CN --font-path "$font_dir"
build structural-certificates.ja --font-path "$font_dir"
build structural-certificates.eo
