#!/usr/bin/env bash
set -euo pipefail

usage() {
    cat <<'EOF'
Usage: scripts/expose_trust_tcargo_toolchain.sh [options]

Materialize the repo-local Trust-owned dist artifacts, link them as a rustup
toolchain, and expose a tcargo-compatible frontend for Trust Codegen S5 probes.

Options:
  --trust-root PATH   Trust checkout root (default: ${TRUST_ROOT:-$HOME/tRust})
  --dist-dir PATH     Trust dist artifact directory. Overrides --dist-date.
  --dist-date DATE    Dated dist directory under bootstrap/trust-stage0/dist.
  --prefix PATH       Install prefix (default: ~/.tRust/toolchains/trust-stage0-DATE)
  --link-name NAME    rustup toolchain link name (default: trust)
  --tcargo-bin PATH   tcargo shim path (default: ${CARGO_HOME:-~/.cargo}/bin/tcargo)
  --require-rustc-dev Require and install the matching rustc-dev dist artifact.
                      This is needed to rebuild rustc_codegen_trust_cg against
                      the linked Trust rustc ABI.
  --no-link           Install artifacts but do not run rustup toolchain link.
  --no-tcargo         Do not create the tcargo shim.
  -h, --help          Show this help text.

The script refuses to replace an existing non-generated tcargo file and refuses
to relink an existing rustup toolchain name that points at a different prefix.
The S5 rustc_codegen_trust_cg lane also needs a matching rustc-dev artifact in the
selected dist directory when --require-rustc-dev is used.
EOF
}

die() {
    printf 'error: %s\n' "$*" >&2
    exit 1
}

info() {
    printf '%s\n' "$*" >&2
}

canonical_dir() {
    (
        cd "$1"
        pwd -P
    )
}

require_command() {
    command -v "$1" >/dev/null 2>&1 || die "$1 is required on PATH"
}

archive_prefix() {
    local archive_name="$1"

    case "$archive_name" in
        *.tar.xz)
            printf '%s\n' "${archive_name%.tar.xz}"
            ;;
        *.tar.gz)
            printf '%s\n' "${archive_name%.tar.gz}"
            ;;
        *.tar)
            printf '%s\n' "${archive_name%.tar}"
            ;;
        *)
            die "unsupported Trust dist artifact extension: $archive_name"
            ;;
    esac
}

legacy_component_name() {
    local component="$1"

    case "$component" in
        trustc)
            printf 'rustc\n'
            ;;
        trust-std)
            printf 'rust-std\n'
            ;;
        tcargo)
            printf 'cargo\n'
            ;;
        tcargo-trust)
            printf 'cargo-trust\n'
            ;;
        trust-src)
            printf 'rust-src\n'
            ;;
    esac
}

component_pattern() {
    local component="$1"

    case "$component" in
        trustc)
            printf '%s/trustc-[0-9]*.tar.xz\n' "$DIST_DIR"
            ;;
        trust-std)
            printf '%s/trust-std-[0-9]*.tar.xz\n' "$DIST_DIR"
            ;;
        tcargo)
            printf '%s/tcargo-[0-9]*.tar.xz\n' "$DIST_DIR"
            ;;
        tcargo-trust)
            printf '%s/tcargo-trust-[0-9]*.tar.xz\n' "$DIST_DIR"
            ;;
        trust-src)
            printf '%s/trust-src-[0-9]*.tar.xz\n' "$DIST_DIR"
            ;;
        rustc-dev)
            printf '%s/rustc-dev-[0-9]*.tar.xz\n' "$DIST_DIR"
            ;;
        *)
            die "unknown Trust component: $component"
            ;;
    esac
}

find_single_archive() {
    local component="$1"
    local pattern

    pattern="$(component_pattern "$component")"

    local matches=()
    local match
    for match in $pattern; do
        if [ -f "$match" ]; then
            matches+=("$match")
        fi
    done

    if [ "${#matches[@]}" -eq 0 ]; then
        if [ "$component" = "rustc-dev" ]; then
            cat >&2 <<EOF
error: missing Trust rustc-dev dist artifact in $DIST_DIR

rustc-dev is required to rebuild rustc_codegen_trust_cg against the linked Trust
rustc ABI. Add a matching artifact such as:
  $DIST_DIR/rustc-dev-<trust-version>-<host>.tar.xz

One external production route is:
  cd $TRUST_ROOT
  ./x.py dist rustc-dev
  python3 src/tools/trust-stage0-dist/prepare.py \\
    --input-dist build/dist \\
    --source-channel trust \\
    --owned-channel trust \\
    --archive-format xz \\
    --stage0-seed-only \\
    --git-commit-hash <trust-commit> \\
    --output-root bootstrap/trust-stage0 \\
    --stage0-output src/stage0

Then rerun:
  scripts/expose_trust_tcargo_toolchain.sh --require-rustc-dev
EOF
            exit 1
        fi
        local legacy_component legacy_pattern
        legacy_component="$(legacy_component_name "$component")"
        if [ -n "$legacy_component" ]; then
            legacy_pattern="$DIST_DIR/$legacy_component-[0-9]*.tar.xz"
            local legacy_matches=()
            for match in $legacy_pattern; do
                if [ -f "$match" ]; then
                    legacy_matches+=("$match")
                fi
            done
            if [ "${#legacy_matches[@]}" -gt 0 ]; then
                printf 'error: missing Trust dist artifact for component %s in %s\n\n' \
                    "$component" "$DIST_DIR" >&2
                printf 'Legacy-named archive(s) were found but are not accepted for this Trust-owned component:\n' >&2
                printf '  %s\n' "${legacy_matches[@]}" >&2
                printf '\nExpected a Trust-owned archive such as:\n  %s\n' "$pattern" >&2
                exit 1
            fi
        fi
        die "missing Trust dist artifact for component $component in $DIST_DIR"
    fi
    if [ "${#matches[@]}" -ne 1 ]; then
        printf 'ambiguous Trust dist artifacts for %s:\n' "$component" >&2
        printf '  %s\n' "${matches[@]}" >&2
        exit 1
    fi
    printf '%s\n' "${matches[0]}"
}

install_archive() {
    local archive="$1"
    local expected_top tmp_dir top_dir top_name

    expected_top="$(archive_prefix "$(basename "$archive")")"

    tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/trust-cg-trust-install.XXXXXX")"
    if ! tar -xJf "$archive" -C "$tmp_dir"; then
        rm -rf "$tmp_dir"
        die "failed to extract Trust dist artifact: $archive"
    fi
    top_dir="$(find "$tmp_dir" -mindepth 1 -maxdepth 1 -type d -print | head -1)"
    if [ -z "$top_dir" ] || [ ! -x "$top_dir/install.sh" ]; then
        rm -rf "$tmp_dir"
        die "artifact does not contain an executable install.sh: $archive"
    fi
    top_name="$(basename "$top_dir")"
    if [ "$top_name" != "$expected_top" ]; then
        rm -rf "$tmp_dir"
        die "artifact top-level directory '$top_name' does not match expected Trust-owned prefix '$expected_top'"
    fi
    info "installing $(basename "$archive") into $PREFIX"
    if ! "$top_dir/install.sh" --prefix="$PREFIX" --disable-ldconfig >/dev/null; then
        rm -rf "$tmp_dir"
        die "failed to install Trust dist artifact: $archive"
    fi
    rm -rf "$tmp_dir"
}

linked_toolchain_path() {
    local name="$1"
    rustup toolchain list -v | awk -v name="$name" '
        $1 == name && found == "" { found = $NF }
        END { if (found != "") print found }
    '
}

trust_rustc_dev_available() {
    local host="$1"

    find "$PREFIX/lib/rustlib/$host/lib" "$PREFIX/lib" \
        -maxdepth 1 \
        -type f \
        \( -name 'librustc_driver-*.rlib' -o -name 'librustc_abi-*.rlib' \) \
        -print -quit 2>/dev/null | grep -q .
}

write_tcargo_shim() {
    local shim="$1"
    local dir

    dir="$(dirname "$shim")"
    mkdir -p "$dir"

    if [ -e "$shim" ] && ! grep -q 'TRUST_CG_TRUST_TCARGO_SHIM=1' "$shim" 2>/dev/null; then
        die "$shim already exists and was not generated by this script"
    fi

    cat > "$shim" <<EOF
#!/usr/bin/env bash
# Generated by scripts/expose_trust_tcargo_toolchain.sh.
# TRUST_CG_TRUST_TCARGO_SHIM=1
set -euo pipefail
exec rustup run "$LINK_NAME" tcargo "\$@"
EOF
    chmod +x "$shim"
}

TRUST_ROOT="${TRUST_ROOT:-$HOME/tRust}"
DIST_DIR=""
DIST_DATE="2026-04-24"
PREFIX=""
LINK_NAME="trust"
TCARGO_BIN="${CARGO_HOME:-$HOME/.cargo}/bin/tcargo"
REQUIRE_RUSTC_DEV=0
DO_LINK=1
DO_TCARGO=1

while [ "$#" -gt 0 ]; do
    case "$1" in
        --trust-root)
            [ "$#" -ge 2 ] || die "--trust-root requires a path"
            TRUST_ROOT="$2"
            shift 2
            ;;
        --dist-dir)
            [ "$#" -ge 2 ] || die "--dist-dir requires a path"
            DIST_DIR="$2"
            shift 2
            ;;
        --dist-date)
            [ "$#" -ge 2 ] || die "--dist-date requires a date"
            DIST_DATE="$2"
            shift 2
            ;;
        --prefix)
            [ "$#" -ge 2 ] || die "--prefix requires a path"
            PREFIX="$2"
            shift 2
            ;;
        --link-name)
            [ "$#" -ge 2 ] || die "--link-name requires a name"
            LINK_NAME="$2"
            shift 2
            ;;
        --tcargo-bin)
            [ "$#" -ge 2 ] || die "--tcargo-bin requires a path"
            TCARGO_BIN="$2"
            shift 2
            ;;
        --require-rustc-dev)
            REQUIRE_RUSTC_DEV=1
            shift
            ;;
        --no-link)
            DO_LINK=0
            shift
            ;;
        --no-tcargo)
            DO_TCARGO=0
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            die "unknown argument: $1"
            ;;
    esac
done

case "$LINK_NAME" in
    *[!A-Za-z0-9._-]*|"")
        die "--link-name must contain only letters, digits, '.', '_', or '-'"
        ;;
esac

if [ -z "$DIST_DIR" ]; then
    DIST_DIR="$TRUST_ROOT/bootstrap/trust-stage0/dist/$DIST_DATE"
fi
if [ -z "$PREFIX" ]; then
    PREFIX="$HOME/.tRust/toolchains/trust-stage0-$DIST_DATE"
fi

require_command awk
require_command find
require_command rustup
require_command tar

[ -d "$TRUST_ROOT" ] || die "Trust root is missing: $TRUST_ROOT"
[ -d "$DIST_DIR" ] || die "Trust dist directory is missing: $DIST_DIR"

mkdir -p "$PREFIX"
PREFIX="$(canonical_dir "$PREFIX")"
DIST_DIR="$(canonical_dir "$DIST_DIR")"

archives=()
for component in trustc trust-std tcargo tcargo-trust trust-src; do
    archives+=("$(find_single_archive "$component")")
done
if [ "$REQUIRE_RUSTC_DEV" -eq 1 ]; then
    archives+=("$(find_single_archive rustc-dev)")
fi

for archive in "${archives[@]}"; do
    install_archive "$archive"
done

[ -x "$PREFIX/bin/trustc" ] || die "installed Trust compiler is missing: $PREFIX/bin/trustc"
[ -x "$PREFIX/bin/tcargo" ] || die "installed Trust cargo frontend is missing: $PREFIX/bin/tcargo"
TRUST_HOST="$("$PREFIX/bin/trustc" -vV | awk -F': ' '/^host:/ { host = $2 } END { print host }')"
if [ -z "$TRUST_HOST" ]; then
    die "installed Trust trustc did not report a host triple"
fi
if [ "$REQUIRE_RUSTC_DEV" -eq 1 ] && ! trust_rustc_dev_available "$TRUST_HOST"; then
    die "installed Trust rustc-dev private crates were not found under $PREFIX/lib/rustlib/$TRUST_HOST/lib"
fi

if [ "$DO_LINK" -eq 1 ]; then
    existing_path="$(linked_toolchain_path "$LINK_NAME" || true)"
    if [ -n "$existing_path" ]; then
        existing_path="$(canonical_dir "$existing_path")"
        if [ "$existing_path" != "$PREFIX" ]; then
            die "rustup toolchain '$LINK_NAME' already points at $existing_path, not $PREFIX"
        fi
    else
        info "linking rustup toolchain '$LINK_NAME' -> $PREFIX"
        rustup toolchain link "$LINK_NAME" "$PREFIX"
    fi
fi

if [ "$DO_TCARGO" -eq 1 ]; then
    info "writing tcargo shim $TCARGO_BIN"
    write_tcargo_shim "$TCARGO_BIN"
fi

if [ "$DO_LINK" -eq 1 ]; then
    info "Trust tcargo: $(rustup run "$LINK_NAME" tcargo --version 2>&1 | head -1)"
    info "Trust trustc: $(rustup run "$LINK_NAME" trustc --version 2>&1 | head -1)"
    if [ "$DO_TCARGO" -eq 1 ]; then
        info "tcargo: $("$TCARGO_BIN" --version 2>&1 | head -1)"
    fi
else
    info "Trust install prefix: $PREFIX"
    if [ "$DO_TCARGO" -eq 1 ]; then
        info "tcargo shim written, but --no-link leaves it unusable until '$LINK_NAME' exists"
    fi
fi
