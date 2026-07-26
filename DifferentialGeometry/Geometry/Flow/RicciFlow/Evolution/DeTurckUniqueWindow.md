# DeTurckUniqueWindow

## 2026-07-19 source-only state

This file now contains both the local and the continuation layers for smooth
Ricci--DeTurck uniqueness.  Given two metric paths on `[a,b)` with the
existing joint chart-Gram smoothness/continuity package, the same fixed
DeTurck background, the geometric Ricci--DeTurck equation on `(a,b)`, and
equality at one interior time `c`, `chartRD_local`:

1. invokes the canonical `metricFamilySmoothOn_of_chartGram` producer for
   each path;
2. translates the open regular interval around `c` to an open set containing
   zero;
3. transports each geometric PDE by `HasDerivAt.comp_add_const`;
4. invokes `metricRD_local`, which internally chooses the Sobolev ball,
   fibre-smallness, forcing-ball, and mixed-contraction horizon; and
5. concludes equality of the original metrics on one positive translated
   closed window.

The new continuation facts are:

- `metric_eq_chartGram`: equality of all centred chart-Gram entries determines
  the smooth metric, by extending equality from the chart basis to both
  bilinear slots;
- `metric_eq_leftLim`: equality on `[c,d)` passes to `d` using only the given
  joint chart-Gram `C0` regularity and the cluster filter from the left; and
- `chartRD_forward`: equality propagates to every `t` in `[c,b)`.  Its reached
  set is closed at its supremum by `metric_eq_leftLim`, and if the supremum is
  below a fixed target, `chartRD_local` gives a strictly longer reached time.
  No uniform positive lower bound for successive local lifetimes is used.

Verification status: **source-only / not yet Lean-checked** because the shared
named Lean build was still active.  No `sorry`, `admit`, axiom, opaque
placeholder, or replacement hypothesis was added.

Honest accounting: the local-to-whole-interval source body is **100%**;
Lean-verified continuation completion is **0%** until a focused check passes;
the public `ricci_flow_forward_unique` endpoint remains **0%**.  There is no
known mathematical obstruction in the continuation argument.  The remaining
risks are elaboration-level: centred chart-basis extensionality in
`metric_eq_chartGram`, the `nhdsWithin` congruence used for the left limit, and
the final translated-time simplification `d + (r - d) = r`.

Scope is intentionally exact: this closes continuation from an interior time
at which the two Ricci--DeTurck metrics are already equal.  It does not obtain
that equality from a merely `C0` original edge, construct harmonic-map heat
flow, or prove the gauge PDE identity.  Those remain explicit producers
before `ricci_flow_forward_unique`, whose exact endpoint remains **0%**.
