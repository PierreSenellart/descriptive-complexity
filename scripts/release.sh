#!/usr/bin/env bash
# Release helper for DescriptiveComplexity. The version scheme is stated in the
# README, under "Use as a dependency": versions are the library's own, a patch
# release keeps the Mathlib pin it was cut against, and a new pin always takes
# at least a minor bump, so that `~x.y.z` means "stay on my Mathlib".
#
# One Mathlib version is pinned in four *declared* places, which move together
# and are what `pins` rewrites:
#
#   /lean-toolchain            /lakefile.lean          (the Mathlib `require`)
#   /docbuild/lean-toolchain   /docbuild/lakefile.toml (the doc-gen4 `rev`)
#
# Two manifests then *record* what those declarations resolved to, and a fresh
# clone builds against them, so `check` compares all six:
#
#   /lake-manifest.json        (mathlib)
#   /docbuild/lake-manifest.json (mathlib, and doc-gen4)
#
# `pins` cannot write them – only `lake update` can, in each workspace – so
# `check` stays red between the two steps, by design.
#
#   release.sh check              verify every version/pin location agrees
#   release.sh next-pin           print the Mathlib tag to move to, if any
#   release.sh pins <tag>         move the four Mathlib/toolchain pins to <tag>
#   release.sh next-minor         print the next minor library version
#   release.sh prepare <version>  bump the library version everywhere, then check
#   release.sh notes              print draft release notes for the current version
#   release.sh publish            tag the current commit and cut the GitHub release
#
# `check`, `next-minor` and `next-pin` are safe to run any time (`next-pin` asks
# GitHub what exists, the others are offline); `pins` and `prepare` only edit
# tracked files and leave the commit to you; `publish` is the only step that
# touches origin. `update.yml` drives `next-pin` -> `pins` -> `prepare` monthly.

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
# The manifests are what a fresh clone resolves against, so a stale one ships a
# pin nobody declared. Read the `inputRev` recorded for a dependency by matching
# its repository url, which is unique in the file and, unlike the package name,
# is not wrapped in guillemets.
manifest_rev()   { # manifest url
  grep -A11 -F "$2" "$1" | grep -oP '(?<="inputRev": ")[^"]+' | head -1 || true
}
pin_manifest()          { manifest_rev lake-manifest.json          github.com/leanprover-community/mathlib4; }
pin_docbuild_mathlib()  { manifest_rev docbuild/lake-manifest.json github.com/leanprover-community/mathlib4; }
pin_docbuild_docgen()   { manifest_rev docbuild/lake-manifest.json github.com/leanprover/doc-gen4; }
pin_readme_row() { sed -n '/^| --- | --- | --- |$/{n;s/^| `[^`]*` | `\([^`]*\)`.*/\1/p;q;}' README.md; }
# The concept DOI: minted once, then the same for every later version.
doi_citation()   { grep -oP '(?<=value: ")10\.5281/zenodo\.[0-9]+' CITATION.cff | head -1; }
# Read the badge's *link target*, not its image URL: the image is a styling
# choice (zenodo.org/badge vs shields.io), the doi.org link is what must be right.
doi_readme()     { grep -oP '(?<=doi\.org/)10\.5281/zenodo\.[0-9]+' README.md | head -1; }
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
  report "lake-manifest mathlib"        "$pin" "$(pin_manifest)"
  report "docbuild manifest mathlib"    "$pin" "$(pin_docbuild_mathlib)"
  report "docbuild manifest doc-gen4"   "$pin" "$(pin_docbuild_docgen)"
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

# --- pins --------------------------------------------------------------------
# Moving the Mathlib pin is the other half of a release; `next-pin` decides
# whether there is anything to move to, and `pins` performs the move. The
# library version is `prepare`'s business, below: a new pin always takes at
# least a minor bump, which is what `next-minor` computes.

# Lake's own order on version strings (`Lake/Util/Version.lean`): the numeric
# `major.minor.patch` first, then the *empty* suffix ranks highest, and two
# non-empty suffixes compare as plain strings. A leading `v` is ignored, so
# `v4.33.0-rc1 < v4.33.0 < v4.33.1`.
ver_lt() { # ver_lt A B -- true when A is strictly older than B
  local a="${1#v}" b="${2#v}" an as bn bs first
  an="${a%%-*}"; as="${a#"$an"}"; as="${as#-}"
  bn="${b%%-*}"; bs="${b#"$bn"}"; bs="${bs#-}"
  if [[ "$an" != "$bn" ]]; then
    [[ "$(printf '%s\n%s\n' "$an" "$bn" | sort -V | head -1)" == "$an" ]]
    return
  fi
  # Same numbers: a suffixed version is older than the unsuffixed one.
  [[ -n "$as" && -z "$bs" ]] && return 0
  if [[ -n "$as" && -n "$bs" ]]; then
    first="$(LC_ALL=C printf '%s\n%s\n' "$as" "$bs" | LC_ALL=C sort | head -1)"
    [[ "$first" == "$as" && "$as" != "$bs" ]]
    return
  fi
  return 1
}

cmd_next_minor() {
  local version major minor
  version="$(lib_lakefile)" || die "no version in lakefile.lean"
  IFS=. read -r major minor _ <<< "$version"
  printf '%d.%d.0\n' "$major" $((minor + 1))
}

# Prints the tag to move to on stdout, or nothing at all when the answer is
# "stay where you are"; everything else goes to stderr, so the caller can just
# test whether stdout is empty.
cmd_next_pin() {
  local pin latest mathlib_toolchain
  pin="$(pin_toolchain)" || die "no toolchain in lean-toolchain"
  command -v gh >/dev/null || die "next-pin needs the gh CLI"

  # Tags, not releases: Mathlib only started publishing GitHub releases in 2026,
  # and the tag is what the `require` names anyway. Stable lines only, since
  # master tracks a stable Mathlib.
  latest="$(gh api --paginate repos/leanprover-community/mathlib4/git/matching-refs/tags/v4. \
              -q '.[].ref' | sed 's|^refs/tags/||' \
              | grep -E '^v[0-9]+\.[0-9]+\.[0-9]+$' | sort -V | tail -1)" \
    || die "could not list the Mathlib tags"
  [[ -n "$latest" ]] || die "no stable Mathlib tag found"
  printf 'Pinned: %s. Newest stable Mathlib tag: %s.\n' "$pin" "$latest" >&2

  if ! ver_lt "$pin" "$latest"; then
    printf 'Nothing to move to: the pin is not older than that.\n' >&2
    return 0
  fi
  # A patch release *inside* the pinned line is deliberately not chased: Mathlib
  # cuts those often (7 over the last 10 minor lines), and each would spend a
  # minor bump here on no new content. Take such a pin by hand when it fixes
  # something the library needs. An rc pin, on the other hand, is exactly what
  # its own stable release supersedes, so that move is offered.
  if [[ "$pin" != *-* && "${pin%.*}" == "${latest%.*}" ]]; then
    printf 'Nothing to do: %s is only a patch release of the pinned line.\n' "$latest" >&2
    return 0
  fi
  # All four pins move together, so refuse unless the whole set exists and
  # agrees: Mathlib's own toolchain at that tag, and a doc-gen4 tag to match.
  mathlib_toolchain="$(curl -fsSL \
    "https://raw.githubusercontent.com/leanprover-community/mathlib4/$latest/lean-toolchain" \
    | tr -d '[:space:]')" || die "could not read Mathlib's lean-toolchain at $latest"
  [[ "$mathlib_toolchain" == "leanprover/lean4:$latest" ]] \
    || die "Mathlib $latest is built with $mathlib_toolchain, so the pins do not
       share one version any more; move them by hand"
  if ! gh api "repos/leanprover/doc-gen4/git/ref/tags/$latest" >/dev/null 2>&1; then
    printf 'Waiting: doc-gen4 has no %s tag yet, so docbuild cannot follow.\n' "$latest" >&2
    return 0
  fi

  printf '%s\n' "$latest"
}

cmd_pins() {
  local ver="${1:-}" old
  [[ -n "$ver" ]] || die "usage: $0 pins <mathlib tag>   (e.g. v4.33.0)"
  [[ "$ver" =~ ^v[0-9]+\.[0-9]+\.[0-9]+(-[0-9A-Za-z.]+)?$ ]] || die "not a Mathlib tag: $ver"
  old="$(pin_toolchain)" || die "no toolchain in lean-toolchain"
  [[ "$ver" != "$old" ]] || die "already pinned to $ver"

  printf 'leanprover/lean4:%s\n' "$ver" > lean-toolchain
  printf 'leanprover/lean4:%s\n' "$ver" > docbuild/lean-toolchain
  sed -i "s|\"mathlib\" @ git \"[^\"]*\"|\"mathlib\" @ git \"$ver\"|" lakefile.lean
  # The only `rev` in that file is doc-gen4's; the local package uses `path`.
  sed -i "s|^rev = \"[^\"]*\"|rev = \"$ver\"|" docbuild/lakefile.toml

  printf 'Moved the pin %s -> %s in the four pinned places.\n\n' "$old" "$ver"
  printf 'Next: `lake update` here and `lake update doc-gen4` in `docbuild/` (both\n'
  printf 'manifests still record the old Mathlib, and `check` reads them), let the\n'
  printf 'build go green, then `%s prepare %s`. The README badge and table\n' "$0" "$(cmd_next_minor)"
  printf 'follow the pin from there, so `check` stays red until that runs.\n'
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
  # The Reservoir form carries a `~` range rather than a tag, in both syntaxes.
  sed -i "s|^version = \"~$old\"|version = \"~$version\"|" README.md
  sed -i "s|descriptive-complexity\" @ \"~$old\"|descriptive-complexity\" @ \"~$version\"|" README.md
  # Newest release first, directly under the table header.
  sed -i "/^| --- | --- | --- |$/a | \`v$version\` | \`$pin\` | \`leanprover/lean4:$pin\` |" README.md
  # Badge tracks the pin; shields.io wants a literal hyphen doubled.
  sed -i "s|/badge/Mathlib-[^)]*-blue|/badge/Mathlib-${pin//-/--}-blue|" README.md
  sed -i "s|mathlib4/releases/tag/[^)]*|mathlib4/releases/tag/$pin|" README.md

  printf 'Bumped %s -> %s (Mathlib pin %s).\n\n' "$old" "$version" "$pin"
  cmd_check
  printf '\nReview the diff, then commit and run: %s publish\n' "$0"
}

# --- notes -------------------------------------------------------------------
# A draft, not the final word: the commit subjects are one line each and read
# well as a changelog, but they are written for the log, not for a reader
# arriving at the release page. Curate before publishing.

cmd_notes() {
  local version pin tag prev
  version="$(lib_lakefile)"; pin="$(pin_toolchain)"; tag="v$version"
  # No previous tag (or none but this one) is not an error: the first release
  # simply has nothing to list. `|| true` keeps `pipefail` from treating the
  # empty grep as a failure.
  prev="$(git tag --sort=-creatordate | grep -v "^$tag\$" | head -1 || true)"

  printf 'Requires Mathlib `%s` and toolchain `leanprover/lean4:%s`.\n\n' "$pin" "$pin"
  if [[ -n "$prev" ]]; then
    printf '## Changes since %s\n\n' "$prev"
    git log --no-merges --reverse --pretty='- %s' "$prev..HEAD"
    printf '\n'
  fi
  printf '## Use\n\n```lean\nrequire "descriptive-complexity" from git\n  "https://github.com/%s" @ "%s"\n```\n\n' \
    "$REPO" "$tag"
  printf 'See the [compatibility table](https://github.com/%s#use-as-a-dependency)\n' "$REPO"
  printf 'for which version to use with which Mathlib.\n'
  [[ -z "$prev" ]] || printf '\n**Full changelog**: https://github.com/%s/compare/%s...%s\n' "$REPO" "$prev" "$tag"
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

  # Kept in .git/, so a draft is never mistaken for a tracked file.
  local notes_file=".git/RELEASE_NOTES-$tag.md"
  cmd_notes > "$notes_file"
  if [[ -t 0 ]]; then
    # The editor git itself would use for a commit message: `core.editor`, then
    # `GIT_EDITOR`/`VISUAL`/`EDITOR`, then the platform default. Asking git
    # rather than reading `$EDITOR` directly means the release notes open where
    # every other message in this repository does.
    local editor edit_reply
    editor="$(git var GIT_EDITOR)"
    printf '\nDrafted release notes from the log into %s.\n' "$notes_file"
    read -r -p "Edit them in $editor before publishing? [Y/n] " edit_reply || true
    # `git var` may return a command with arguments (`code --wait`, `emacsclient
    # -c`), so it has to go through a shell; the file is passed as `$0` rather
    # than interpolated, so a path with spaces survives.
    [[ "$edit_reply" == "n" || "$edit_reply" == "N" ]] \
      || sh -c "$editor \"\$0\"" "$notes_file"
  fi
  printf '\n--- release notes ---\n'; cat "$notes_file"; printf -- '--- end notes -------\n'

  printf '\nAbout to publish %s (Mathlib %s) from %s.\n' "$tag" "$pin" "$(git rev-parse --short HEAD)"
  read -r -p 'This mints a permanent Zenodo DOI. Continue? [y/N] ' reply
  [[ "$reply" == "y" || "$reply" == "Y" ]] || die "aborted"

  git tag -a "$tag" -m "$tag – for Mathlib $pin"
  git push origin "$tag"
  gh release create "$tag" --repo "$REPO" \
    --title "$tag – for Mathlib $pin" \
    --notes-file "$notes_file"

  printf '\nReleased %s (Mathlib %s). Zenodo archives it on the release event, under the\n' "$tag" "$pin"
  printf 'concept DOI already recorded in CITATION.cff, which covers every version.\n'
}

case "${1:-}" in
  check)      cmd_check ;;
  next-pin)   cmd_next_pin ;;
  pins)       shift; cmd_pins "$@" ;;
  next-minor) cmd_next_minor ;;
  prepare)    shift; cmd_prepare "$@" ;;
  notes)      cmd_notes ;;
  publish)    cmd_publish ;;
  *) die "usage: $0 {check | next-pin | pins <tag> | next-minor | prepare <version> | notes | publish}" ;;
esac
