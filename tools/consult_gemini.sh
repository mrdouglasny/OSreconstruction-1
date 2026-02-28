#!/usr/bin/env bash
set -euo pipefail

if ! command -v gemini >/dev/null 2>&1; then
  echo "error: gemini CLI not found on PATH" >&2
  exit 127
fi

if [ $# -ne 1 ]; then
  cat >&2 <<'USAGE'
Usage:
  tools/consult_gemini.sh <prompt-file>
  tools/consult_gemini.sh -

Notes:
  - Pass '-' to read prompt text from stdin.
  - Do not include secrets in prompts.
USAGE
  exit 2
fi

if [ "$1" = "-" ]; then
  prompt="$(cat)"
else
  if [ ! -f "$1" ]; then
    echo "error: prompt file not found: $1" >&2
    exit 2
  fi
  prompt="$(cat "$1")"
fi

MODEL="${GEMINI_MODEL-gemini-3.1-pro-preview}"

if [ -n "$MODEL" ]; then
  gemini -m "$MODEL" -p "$prompt"
else
  gemini -p "$prompt"
fi
