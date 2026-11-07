#!/usr/bin/env bash
# Run every comparator pair under RandomSandpileAudit/. A missing pair or a failed check is fatal.
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
case "${1:-}" in
  '') ;;
  --help) cat <<'USAGE'
Usage: scripts/run_comparators.sh

Runs leanprover/comparator, with its Lean kernel replay and the NanoDa kernel, on every pair
RandomSandpileAudit/<Pair>/comparator.json. Set COMPARATOR_BIN, COMPARATOR_LANDRUN, COMPARATOR_LEAN4EXPORT
and COMPARATOR_NANODA to the executable paths of separately built verification tools (the defaults
are the paths of .github/workflows/comparator.yml, under ~/tools). The script builds the library,
then every audit module in a fresh copy of the source tree that reuses only the production build.
Logs are written under .lake/comparator-logs/.
USAGE
    exit 0 ;;
  *) echo "Unknown option: $1" >&2; exit 2 ;;
esac
[ "$#" -le 1 ] || { echo 'Too many arguments' >&2; exit 2; }
for command_name in lake lean python3; do
  command -v "$command_name" >/dev/null || { echo "Missing command: $command_name" >&2; exit 1; }
done
log_dir="$repository_root/.lake/comparator-logs"
mkdir -p "$log_dir"
config_dir=$(mktemp -d "${TMPDIR:-/tmp}/sandpile-comparators.XXXXXXXX")
trap 'rm -rf "$config_dir"' EXIT

# Validate every configuration and write protected copies; the submitted files are not changed.
python3 - "$repository_root" "$config_dir" <<'PY'
import json
import pathlib
import re
import sys

root, destination = map(pathlib.Path, sys.argv[1:])
audit = root / 'RandomSandpileAudit'
# The two required pairs: MainTheorem and SingleSource.
required = {'MainTheorem', 'SingleSource'}
paths = sorted(audit.glob('*/comparator.json'))
missing = required - {p.parent.name for p in paths}
if missing:
    raise SystemExit('Missing required comparator pairs: ' + ', '.join(sorted(missing)))
allowed_keys = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms',
                'definition_names', 'enable_nanoda'}
standard_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
def unique_keys(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError('Duplicate configuration key: ' + key)
        result[key] = value
    return result
manifest = []
for index, path in enumerate(paths):
    config = json.loads(path.read_text(), object_pairs_hook=unique_keys)
    if not isinstance(config, dict) or set(config) - allowed_keys:
        raise SystemExit(f'{path}: unsupported configuration fields')
    # The literature inputs are hypotheses of the theorems, so no pair may permit another axiom.
    axioms = config.get('permitted_axioms')
    if not isinstance(axioms, list) or len(set(axioms)) != len(axioms) or set(axioms) != standard_axioms:
        raise SystemExit(f'{path}: permitted_axioms must be exactly propext, Classical.choice, Quot.sound')
    names = config.get('theorem_names')
    if (not isinstance(names, list) or not names
            or any(not isinstance(n, str) or not n.strip() or any(ord(c) < 32 for c in n) for n in names)):
        raise SystemExit(f'{path}: theorem_names must be a nonempty list of declaration names')
    for key in ['challenge_module', 'solution_module']:
        module = config.get(key)
        if not isinstance(module, str) or not re.fullmatch(r'RandomSandpileAudit(?:\.[A-Za-z_][A-Za-z_0-9]*)+', module):
            raise SystemExit(f'{path}: invalid {key}')
        file = root.joinpath(*module.split('.')).with_suffix('.lean')
        if not file.is_file():
            raise SystemExit(f'{path}: missing {key} source {file}')
    # The NanoDa replay is never disabled.
    config['enable_nanoda'] = True
    output = destination / f'{index:03d}.json'
    output.write_text(json.dumps(config, indent=2) + '\n')
    manifest.append(f'{index:03d}\t{path.relative_to(root)}\t{output}')
(destination / 'pairs.tsv').write_text('\n'.join(manifest) + '\n')
print(f'Validated {len(paths)} comparator pairs, including the two required pairs.')
PY

: "${COMPARATOR_BIN:=$HOME/tools/comparator/.lake/build/bin/comparator}"
: "${COMPARATOR_LANDRUN:=$HOME/tools/bin/landrun}"
: "${COMPARATOR_LEAN4EXPORT:=$HOME/tools/lean4export/.lake/build/bin/lean4export}"
: "${COMPARATOR_NANODA:=$HOME/tools/nanoda_lib/target/release/nanoda_bin}"
export COMPARATOR_LANDRUN COMPARATOR_LEAN4EXPORT COMPARATOR_NANODA
for tool_path in "$COMPARATOR_BIN" "$COMPARATOR_LANDRUN" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_NANODA"; do
  [ -x "$tool_path" ] || { echo "Missing executable: $tool_path" >&2; exit 1; }
done
# A denied write alone is insufficient: also prove that the sandbox can execute.
probe_dir=$(mktemp -d "${TMPDIR:-/tmp}/sandpile-landrun.XXXXXXXX")
probe="$probe_dir/escape"
if ! "$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev -ldd -add-exec -- /bin/true; then
  rm -rf "$probe_dir"
  echo 'landrun could not execute the permitted sandbox probe' >&2
  exit 1
fi
"$COMPARATOR_LANDRUN" --best-effort --ro / --rw /dev -ldd -add-exec \
  -- /bin/sh -c 'printf escaped > "$1"' sh "$probe" || true
if [ -e "$probe" ]; then
  rm -rf "$probe_dir"
  echo 'landrun allowed an out-of-sandbox write' >&2
  exit 1
fi
rm -rf "$probe_dir"

lake build 2>&1 | tee "$log_dir/library-build.log"
# A fresh copy of the source tree gives the audit modules empty build paths while reusing the
# production and dependency artifacts. It is retained; no olean is removed by this script.
run_parent="$repository_root/.lake/comparator-runs"
mkdir -p "$run_parent"
run_root=$(mktemp -d "$run_parent/run.XXXXXXXX")
python3 - "$repository_root" "$run_root" <<'PY'
import errno
import fcntl
import pathlib
import shutil
import sys

def copy_cached_file(source, destination):
    # Reflinks save space without sharing writable cache files.
    with open(source, 'rb') as original, open(destination, 'wb') as copied:
        try:
            fcntl.ioctl(copied.fileno(), 0x40049409, original.fileno())
        except OSError as error:
            if error.errno not in (errno.EXDEV, errno.EOPNOTSUPP, errno.ENOTTY, errno.EINVAL):
                raise
            shutil.copyfileobj(original, copied, length=1024 * 1024)
    shutil.copystat(source, destination)
    return destination

source, destination = map(pathlib.Path, sys.argv[1:])
# Copy the source tree; never copy its existing build tree recursively.
shutil.copytree(source, destination, dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('.lake', '.git'))
local_lake = destination / '.lake'
local_lake.mkdir()
packages = source / '.lake/packages'
if packages.is_dir():
    # Keep the symbolic links of the package checkouts: copying their targets would change the
    # type of tracked files, and Lake would report the dependency repositories as modified.
    shutil.copytree(packages, local_lake / 'packages', copy_function=copy_cached_file,
                    symlinks=True, ignore=shutil.ignore_patterns('*.setup.json'))
build = source / '.lake/build'
if build.is_dir():
    # Copy the production artifacts only; the audit modules start with empty paths.
    for path in build.rglob('*'):
        relative = path.relative_to(build)
        if any(part == 'RandomSandpileAudit' or part.startswith('RandomSandpileAudit.') for part in relative.parts):
            continue
        output = local_lake / 'build' / relative
        if path.is_dir():
            output.mkdir(parents=True, exist_ok=True)
        elif path.is_file():
            # Compiler setup JSON is a consumed input, not a cached output.
            if path.name.endswith('.setup.json'):
                continue
            output.parent.mkdir(parents=True, exist_ok=True)
            copy_cached_file(path, output)
print('Fresh audit checkout (retained): ' + str(destination))
PY
printf '%s\n' "$run_root" | tee "$log_dir/audit-checkout.txt"
cd "$run_root"
# Do not inherit the Lean search path of another checkout; Lake supplies this tree's paths.
unset LEAN_PATH
lake build RandomSandpileAudit 2>&1 | tee "$log_dir/audit-build.log"

failed=0
checked=0
while IFS=$'\t' read -r index source_config protected_config; do
  printf '\nChecking %s\n' "$source_config"
  log="$log_dir/$index.log"
  if lake env "$COMPARATOR_BIN" "$protected_config" < /dev/null 2>&1 | tee "$log"; then
    result=0
  else
    result=1
  fi
  if [ "$result" -eq 0 ] && grep -Fxq 'Your solution is okay!' "$log"; then
    printf '%s: OK\n' "$source_config"
  else
    printf '%s: FAILED\n' "$source_config" >&2
    failed=1
  fi
  checked=$((checked + 1))
done < "$config_dir/pairs.tsv"
[ "$checked" -ge 2 ] || { echo 'Fewer than two comparator pairs ran' >&2; exit 1; }
[ "$failed" -eq 0 ] || exit 1
printf '\nAll %s comparator pairs passed. Logs: %s\n' "$checked" "$log_dir"
