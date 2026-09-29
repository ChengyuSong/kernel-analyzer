# Shared fetch helpers for the eval scripts (source'd). Everything that
# can be cloned or downloaded is fetched from a pinned source and
# verified: git commits by SHA, files by sha256. Nothing depends on
# paths of the machine the scripts were written on.

# clone_at URL DIR SHA: fetch exactly one commit and check it out
clone_at() {
  local url=$1 dir=$2 sha=$3
  if [[ ! -d "$dir/.git" ]]; then
    git init -q "$dir"; git -C "$dir" remote add origin "$url"
  fi
  if [[ "$(git -C "$dir" rev-parse -q --verify HEAD 2>/dev/null)" != "$sha" ]]; then
    git -C "$dir" fetch -q --depth 1 origin "$sha" \
      && git -C "$dir" checkout -q --detach "$sha"
  fi
  [[ "$(git -C "$dir" rev-parse HEAD)" == "$sha" ]] \
    || { echo "!! $dir is not at $sha" >&2; return 1; }
}

# sha_ok FILE SHA256
sha_ok() { echo "$2  $1" | sha256sum -c --quiet >/dev/null 2>&1; }

# fetch_url URL FILE SHA256: download unless already present and correct
fetch_url() {
  local url=$1 f=$2 sha=$3
  sha_ok "$f" "$sha" && return 0
  mkdir -p "$(dirname "$f")"
  curl -fsSL -o "$f" "$url" || { echo "!! download failed: $url" >&2; return 1; }
  sha_ok "$f" "$sha" || { echo "!! checksum mismatch: $f ($url)" >&2; return 1; }
}

# fetch_gdrive FILE_ID FILE SHA256: a Google Drive file, via a pinned
# gdown in a digest-pinned python image (Drive needs more than curl:
# HTML interstitial + large-file confirmation). Needs docker.
GDOWN_IMAGE=python@sha256:f77ac9e44ae96ef2c90b8053ea08c31f8be030f824196b0ae4db6d462c84e51f
GDOWN_VERSION=6.4.0
fetch_gdrive() {
  local id=$1 f=$2 sha=$3
  sha_ok "$f" "$sha" && return 0
  mkdir -p "$(dirname "$f")"
  docker run --rm -u "$(id -u):$(id -g)" -e HOME=/tmp \
    -v "$(cd "$(dirname "$f")" && pwd)":/out "$GDOWN_IMAGE" \
    sh -c "pip install -q --user gdown==$GDOWN_VERSION >/dev/null 2>&1 \
           && python -m gdown -q -O '/out/$(basename "$f")' '$id'" \
    || { echo "!! Drive download failed ($id); retry later (quota) or place $f by hand" >&2; return 1; }
  sha_ok "$f" "$sha" || { echo "!! checksum mismatch: $f (Drive $id)" >&2; return 1; }
}
