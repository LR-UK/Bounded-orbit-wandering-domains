#!/usr/bin/env bash
set -euo pipefail

# Adapted from PalomarRegistry/PalomarTemplate, commit
# cb5c79b69a740d2dc299071fc35994627050d77a (Apache-2.0).
# Judge Solution against Challenge the way Palomar does: with the `lake
# comparator` that ships in this project's own toolchain, replaying the proof
# through Lean's kernel and the toolchain's bundled independent kernels
# (NanoDa and con-ron). Nothing is built from a pin; everything that judges
# comes from `lean-toolchain`, which Palomar requires to be v4.35.0-rc2 or
# later.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

# Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted
# comparator.json: it registers the toolchain's bundled kernels itself. This
# generated copy does the same, so the local check judges as the registry does.
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels is not a submitter field; Palomar rejects it", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

python3 scripts/fetch_cache.py
# Comparator in Lean 4.35.0-rc2 permits writes only below the root .lake.
# Put local path dependencies' generated Lake state there too, retaining their
# usual paths through relative symlinks. Sources, manifests and the sandbox
# policy are unchanged. Existing build results are preserved.
python3 - <<'PATH_STATE_PY'
import json
import os
from pathlib import Path

root = Path.cwd().resolve()
manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
state = root / ".lake"
storage = state / "comparator-path-state"


def ordinary_directory(path):
    for ancestor in [path, *path.parents]:
        if ancestor == root:
            break
        if ancestor.is_symlink():
            raise SystemExit(f"error: unexpected symlink in build-state path: {ancestor}")
        if ancestor.exists() and not ancestor.is_dir():
            raise SystemExit(f"error: expected a directory: {ancestor}")


ordinary_directory(storage)
relocations = []
for package in manifest["packages"]:
    if package.get("type") != "path":
        continue
    relative = Path(package["dir"])
    if relative.is_absolute() or ".." in relative.parts or not relative.parts:
        raise SystemExit(f"error: dependency must be inside this repository: {relative}")
    directory = root / relative
    ordinary_directory(directory)
    if not directory.is_dir():
        raise SystemExit(f"error: missing path dependency: {relative}")
    source = directory / ".lake"
    destination = storage / relative / ".lake"
    ordinary_directory(destination)
    if source.is_symlink():
        if source.resolve() != destination or not destination.is_dir():
            raise SystemExit(f"error: unexpected dependency build-state link: {source}")
        continue
    if source.exists():
        if not source.is_dir() or destination.exists():
            raise SystemExit(f"error: conflicting dependency build state: {source}")
    relocations.append((source, destination))

for source, destination in relocations:
    destination.parent.mkdir(parents=True, exist_ok=True)
    if source.exists():
        source.rename(destination)
    else:
        destination.mkdir(exist_ok=True)
    source.symlink_to(os.path.relpath(destination, source.parent), target_is_directory=True)
    print(f"Prepared Comparator build directory: {source.relative_to(root)}", flush=True)
PATH_STATE_PY

lake comparator --config "$config"
