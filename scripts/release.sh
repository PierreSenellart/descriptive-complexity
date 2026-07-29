#!/usr/bin/env bash
# Release helper for DescriptiveComplexity. The version scheme is stated in the
# README, under "Use as a dependency": versions are the library's own, a patch
# release keeps the Mathlib pin it was cut against, and a new pin always takes
# at least a minor bump, so that `~x.y.z` means "stay on my Mathlib".
#
#   release.sh check              verify every version/pin location agrees
#   release.sh prepare <version>  bump the library version everywhere, then check
#   release.sh publish            tag the current commit and cut the GitHub release
#
# `check` is safe to run any time (and in CI); `prepare` only edits tracked files
# and leaves the commit to you; `publish` is the only step that touches origin.

set -euo pipefail

cd "$(dirname "$0")/.."

readonly REPO="PierreSenellart/descriptive-complexity"

die() { printf 'error: %s\n' "$*" >&2; exit 1; }

# --- readers -----------------------------------------------------------------
# Each returns the version string recorded in one place, or the empty string.

lib_lakefile()   { grep -oP '(?<=version := v!")[^"]+' lakefile.lean; }
lib_citation()   { grep -oP '(?<=^version: ")[^"]+' CITATION.cff; }
lib_cff_date()   { grep -oP '(?<=^date-released: ")[^"]+' CITATION.cff; }
lib_readme_git() { grep -oP '(?<=descriptive-complexity" @ ")v[^"]+' README.md; }
lib_readme_rev() { grep -oP '(?<=^rev = ")v[^"]+' README.md; }
lib_readme_row() { sed -n '/^| --- | --- | --- |$/{n;s/^| `v\([^`]*\)`.*/\1/p;q;}' README.md; }

pin_toolchain()  { grep -oP '(?<=leanprover/lean4:)\S+' lean-toolchain; }
pin_docbuild()   { grep -oP '(?<=leanprover/lean4:)\S+' docbuild/lean-toolchain; }
pin_mathlib()    { grep -oP '(?<=/ "mathlib" @ git ")[^"]+' lakefile.lean; }
pin_docgen()     { grep -oP '(?<=^rev = ")[^"]+' docbuild/lakefile.toml; }
pin_readme_row() { sed -n '/^| --- | --- | --- |$/{n;s/^| `[^`]*` | `\([^`]*\)`.*/\1/p;q;}' README.md; }
# The concept DOI: minted once, then the same for every later version.
doi_citation()   { grep -oP '(?<=value: ")10\.5281/zenodo\.[0-9]+' CITATION.cff | head -1; }
doi_readme()     { grep -oP '(?<=zenodo\.org/badge/DOI/)10\.5281/zenodo\.[0-9]+' README.md | head -1; }
# shields.io escapes a literal hyphen as `--`, so undo that before comparing.
pin_readme_badge() { grep -oP '(?<=/badge/Mathlib-)[^-][^)]*?(?=-blue\))' README.md | sed 's/--/-/g'; }

# --- check -------------------------------------------------------------------

report() { # name expected actual
  if [[ "$2" == "$3" ]]; then
    printf '  ok    %-34s %s\n' "$1" "$3"
  else
    printf '  FAIL  %-34s %s (expected %s)\n' "$1" "${3:-<missing>}" "$2"
    failed=1
  fi
}

cmd_check() {
  local version pin failed=0
  version="$(lib_lakefile)" || die "no version in lakefile.lean"
  pin="$(pin_toolchain)"    || die "no toolchain in lean-toolchain"

  printf 'Library version (from lakefile.lean): %s\n' "$version"
  report "CITATION.cff version"        "$version"     "$(lib_citation)"
  report "README require (lakefile.lean)" "v$version" "$(lib_readme_git)"
  report "README require (lakefile.toml)" "v$version" "$(lib_readme_rev)"
  report "README table, newest row"     "$version"    "$(lib_readme_row)"

  printf 'Mathlib/toolchain pin (from lean-toolchain): %s\n' "$pin"
  report "docbuild/lean-toolchain"      "$pin" "$(pin_docbuild)"
  report "lakefile.lean mathlib require" "$pin" "$(pin_mathlib)"
  report "docbuild doc-gen4 rev"        "$pin" "$(pin_docgen)"
  report "README table, toolchain col"  "$pin" "$(pin_readme_row)"
  report "README Mathlib badge"         "$pin" "$(pin_readme_badge)"

  printf 'Other:\n'
  report "README DOI badge" "$(doi_citation)" "$(doi_readme)"
  local today; today="$(date -u +%Y-%m-%d)"
  if [[ "$(lib_cff_date)" > "$today" ]]; then
    printf '  FAIL  %-34s %s is in the future\n' "CITATION.cff date-released" "$(lib_cff_date)"
    failed=1
  else
    printf '  ok    %-34s %s\n' "CITATION.cff date-released" "$(lib_cff_date)"
  fi
  if command -v cffconvert >/dev/null 2>&1; then
    if cffconvert --validate -i CITATION.cff >/dev/null 2>&1; then
      printf '  ok    %-34s valid CFF 1.2.0\n' "CITATION.cff schema"
    else
      printf '  FAIL  %-34s does not validate\n' "CITATION.cff schema"; failed=1
    fi
  else
    printf '  skip  %-34s cffconvert not installed\n' "CITATION.cff schema"
  fi

  [[ $failed -eq 0 ]] || die "some locations disagree; fix them (or run: $0 prepare <version>)"
  printf '\nAll release metadata agrees.\n'
}

# --- prepare -----------------------------------------------------------------

cmd_prepare() {
  local version="${1:-}" old pin today
  [[ -n "$version" ]] || die "usage: $0 prepare <version>   (e.g. 1.0.1)"
  [[ "$version" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] \
    || die "version must be major.minor.patch with no suffix: a '-suffix' is matched by no Lake range"

  old="$(lib_lakefile)"
  pin="$(pin_toolchain)"
  today="$(date -u +%Y-%m-%d)"
  [[ "$version" != "$old" ]] || die "lakefile.lean is already at $version"

  # Reminder of the scheme, since the caller picked the number by hand.
  if [[ "$pin" != "$(pin_readme_row)" && "${version%.*}" == "${old%.*}" ]]; then
    die "the Mathlib pin changed ($(pin_readme_row) -> $pin) but $version is only a patch bump;
       a new pin takes at least a minor bump, so that ~$old keeps users on their Mathlib"
  fi

  sed -i "s|version := v!\"$old\"|version := v!\"$version\"|" lakefile.lean
  sed -i "s|^version: \"$old\"|version: \"$version\"|"        CITATION.cff
  sed -i "s|^date-released: \".*\"|date-released: \"$today\"|" CITATION.cff
  sed -i "s|descriptive-complexity\" @ \"v$old\"|descriptive-complexity\" @ \"v$version\"|" README.md
  sed -i "s|^rev = \"v$old\"|rev = \"v$version\"|" README.md
  # Newest release first, directly under the table header.
  sed -i "/^| --- | --- | --- |$/a | \`v$version\` | \`$pin\` | \`leanprover/lean4:$pin\` |" README.md
  # Badge tracks the pin; shields.io wants a literal hyphen doubled.
  sed -i "s|/badge/Mathlib-[^)]*-blue|/badge/Mathlib-${pin//-/--}-blue|" README.md
  sed -i "s|mathlib4/releases/tag/[^)]*|mathlib4/releases/tag/$pin|" README.md

  printf 'Bumped %s -> %s (Mathlib pin %s).\n\n' "$old" "$version" "$pin"
  cmd_check
  printf '\nReview the diff, then commit and run: %s publish\n' "$0"
}

# --- publish -----------------------------------------------------------------

cmd_publish() {
  local version pin tag
  version="$(lib_lakefile)"; pin="$(pin_toolchain)"; tag="v$version"

  cmd_check
  # -uno: this repo deliberately keeps untracked working notes at the root.
  [[ -z "$(git status --porcelain -uno)" ]] || die "tracked files have uncommitted changes"
  [[ "$(git rev-parse --abbrev-ref HEAD)" == "master" ]] || die "not on master"
  git fetch -q origin master
  [[ "$(git rev-parse HEAD)" == "$(git rev-parse origin/master)" ]] \
    || die "HEAD and origin/master differ; push first, and let CI go green"
  ! git rev-parse -q --verify "refs/tags/$tag" >/dev/null || die "tag $tag already exists"

  printf '\nAbout to publish %s (Mathlib %s) from %s.\n' "$tag" "$pin" "$(git rev-parse --short HEAD)"
  read -r -p 'This mints a permanent Zenodo DOI. Continue? [y/N] ' reply
  [[ "$reply" == "y" || "$reply" == "Y" ]] || die "aborted"

  git tag -a "$tag" -m "$tag – for Mathlib $pin"
  git push origin "$tag"
  gh release create "$tag" --repo "$REPO" \
    --title "$tag – for Mathlib $pin" \
    --notes "Requires Mathlib \`$pin\` and toolchain \`leanprover/lean4:$pin\`.

Add to a \`lakefile.lean\` with

\`\`\`lean
require \"descriptive-complexity\" from git
  \"https://github.com/$REPO\" @ \"$tag\"
\`\`\`

See the [compatibility table](https://github.com/$REPO#use-as-a-dependency) for
which version to use with which Mathlib."

  printf '\nReleased %s (Mathlib %s). Zenodo archives it on the release event, under the\n' "$tag" "$pin"
  printf 'concept DOI already recorded in CITATION.cff, which covers every version.\n'
}

case "${1:-}" in
  check)   cmd_check ;;
  prepare) shift; cmd_prepare "$@" ;;
  publish) cmd_publish ;;
  *) die "usage: $0 {check | prepare <version> | publish}" ;;
esac
