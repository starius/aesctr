#!/usr/bin/env bash
# Create vendor/LNSym from the dev shell's LNSym (the pinned flake input).
# Lake builds inside the dependency's directory, so it must be a writable copy.
# vendor/LNSym.source records the store path the copy was made from; an
# existing copy is kept only if it came from the same store path.
# Run inside the dev shell: `nix develop -c bash scripts/setup-vendor.sh`.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
vendor="$(cd "$here/.." && pwd)/vendor"
dest="$vendor/LNSym"
stamp="$vendor/LNSym.source"
[ -n "${LNSYM_SRC:-}" ] || { echo "LNSYM_SRC is not set: run inside the dev shell" >&2; exit 1; }
if [ -e "$dest" ]; then
  if [ "$(cat "$stamp" 2>/dev/null)" = "$LNSYM_SRC" ]; then
    echo "$dest is up to date ($LNSYM_SRC)"
    exit 0
  fi
  echo "$dest was not copied from the dev shell's LNSym ($LNSYM_SRC); to recreate: rm -rf '$dest' '$stamp'" >&2
  exit 1
fi
mkdir -p "$vendor"
cp -r "$LNSYM_SRC" "$dest"
chmod -R u+w "$dest"
echo "$LNSYM_SRC" > "$stamp"
echo "created $dest from $LNSYM_SRC"
