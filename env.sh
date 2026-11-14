meat_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
meat_native="$(cd "$meat_root" && { pwd -W 2>/dev/null || pwd; })"
export ELAN_HOME="$meat_native/.elan"
export MATHLIB_CACHE_DIR="$meat_native/.cache/mathlib"
case ":$PATH:" in
  *":$meat_root/.elan/bin:"*) ;;
  *) export PATH="$meat_root/.elan/bin:$PATH" ;;
esac

book() {
  (cd "$meat_root" && lake exe manifest && typst compile --root . book/main.typ .lake/build/meat.pdf "$@")
}
