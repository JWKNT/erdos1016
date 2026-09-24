#!/usr/bin/env bash
# Bootstrap the pinned Linux CI toolchain without updating dependency revisions.
set -euo pipefail

ci_repository="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ci_repository"

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  printf '%s\n' 'This bootstrap requires Linux x86_64.' >&2
  exit 1
fi

: "${RUNNER_TEMP:?GitHub Actions RUNNER_TEMP is required}"
: "${GITHUB_ENV:?GitHub Actions GITHUB_ENV is required}"
: "${GITHUB_PATH:?GitHub Actions GITHUB_PATH is required}"

ci_download="$(mktemp -d "$RUNNER_TEMP/erdos1016-elan-download.XXXXXX")"
trap 'rm -rf -- "$ci_download"' EXIT

ci_elan_url='https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz'
ci_elan_sha256='42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63'
curl --fail --location --proto '=https' --tlsv1.2 --retry 3 \
  --connect-timeout 15 --max-time 180 "$ci_elan_url" -o "$ci_download/elan.tar.gz"
printf '%s  %s\n' "$ci_elan_sha256" "$ci_download/elan.tar.gz" | sha256sum --check --status
tar -xzf "$ci_download/elan.tar.gz" -C "$ci_download"

export ELAN_HOME="$RUNNER_TEMP/erdos1016-elan"
"$ci_download/elan-init" -y --no-modify-path --default-toolchain none
export PATH="$ELAN_HOME/bin:$PATH"

IFS= read -r ci_toolchain < lean-toolchain
if [[ "$ci_toolchain" != 'leanprover/lean4:v4.19.0' ]]; then
  printf 'Unexpected Lean toolchain pin: %s\n' "$ci_toolchain" >&2
  exit 1
fi
export ELAN_TOOLCHAIN="$ci_toolchain"
elan toolchain install "$ci_toolchain"
printf 'ELAN_HOME=%s\nELAN_TOOLCHAIN=%s\n' "$ELAN_HOME" "$ELAN_TOOLCHAIN" >> "$GITHUB_ENV"
printf '%s\n' "$ELAN_HOME/bin" >> "$GITHUB_PATH"
elan --version
lean --version
lake --version

cp lake-manifest.json "$ci_download/lake-manifest.json"
ci_cache_result=0
lake exe cache get || ci_cache_result=$?
if ! cmp --silent lake-manifest.json "$ci_download/lake-manifest.json"; then
  printf '%s\n' 'Dependency setup changed lake-manifest.json; refusing to verify changed pins.' >&2
  exit 1
fi
exit "$ci_cache_result"
