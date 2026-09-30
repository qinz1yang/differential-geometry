# Geometrization integration handoff

Work only in this checkout on `codex/geometrization-435rc3-integration`, origin `qinz1yang/differential-geometry-dev`. Accepted upstream baseline: differential-geometry main `777299070a5529e96345e0033979706fd00c7e62`, Lean 4.35.0-rc3, mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.

The skeleton and independent theorem forest are integrated. The current 832-module joint gate passes the complete root (27,692 jobs) and fresh audit (8,286 declarations); exactly 22 historical skeleton admissions remain and all independent closures exclude admissions. Upstream mathematical sources and frozen Blueprint207 A/B remain unchanged. The original 802-module migration receipt and all prior evidence retain their original scope.

Current verification: `docs/geometrization/integration/evidence/verification.json`. Fresh checks of the 31 newly installed Chapter 13 files, five linters, axiom prints, generated audits and 21 actual applications: `docs/geometrization/integration/evidence/installed_ch13/verification.json`. Migration translations: `docs/geometrization/integration/api_translations.md`.

Continue the user's Chapter 13 independent formalization, then Chapter 14, until the finite contract review and independent producers are complete or a verified hard stop. The current frontier is `docs/geometrization/chapter13/frontier.md`. A separate LPA03 metric residual batch has passed scratch checks (3 modules, 5 declarations, 3 actual examples) and awaits installation/next full gate. No whole-chapter or admission-free endpoint completion is claimed.

Run `python3 tools/gc/check_skeleton.py --prepare` after registered source changes, the five negative fixtures in `tools/gc/test_integration_gate.py`, then `python3 tools/gc/check_skeleton.py --full-root --fresh-audit`. Preserve exact endpoints and quantifier order, actual original maps and inherited foundation bindings. Do not edit the frozen Blueprint. The outer historical blueprint auditor was rerun with a bounded timeout; read `blueprint_audit_result.json` for its actual status rather than claiming document verification.
