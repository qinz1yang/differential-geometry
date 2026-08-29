# ActionLower

## Status

Focused verification passed without warnings or placeholders.

## Role

`lKinetic_liminf` is the fixed-chart direct-method consumer for the regularized
kinetic action. Its canonical interface accepts the shifted local
`timeH1 E (b-a)` representatives produced by a finite chart decomposition; it
combines `chartKin_liminf` with `lKinetic_local` on each approximating manifold
curve.

`lRegAction_liminf` adds the scalar-curvature term. Scalar integrals converge
under uniform manifold convergence, while the kinetic liminf is combined with
them using the real-valued liminf addition API. The only sequence bound exposed
is the eventual upper bound for the original full actions, which is already
available for a minimizing sequence. Kinetic nonnegativity, scalar bounds, and
all integrability facts are produced internally.

The limiting kinetic object remains only a chart-valued `timeH1` path. In
particular, neither lower-semicontinuity theorem identifies its weak derivative
with `lVelocity` of a manifold curve. The geometric kinetic integrals on the
right belong only to the almost-everywhere differentiable approximants.

The metric coefficient uses forward time `T - (a + r)^2`, with the kinetic
factor `1 / 2`. Compact-chart hypotheses produce all measurability and operator
bounds internally; the theorem exposes no such consumer assumptions.

The private finite-assembly lemma `sum_liminf_le` proves the correct
superadditivity inequality for a finite sum of real-valued sequences. It uses
eventual lower and upper bounds for each local action. In the intended
application those bounds are derived from kinetic nonnegativity, a common
scalar lower bound, total-action boundedness, and `lRegAction_sum`; they are not
new hypotheses for the eventual minimizer theorem.

`lRegAction_lim_cpt` is the noncompact one-chart interface: it uses a supplied
compact target for the scalar dominated-convergence bound. The compatibility
theorem `lRegAction_liminf` recovers the previous compact-manifold statement by
taking that target to be the whole manifold.

`lRegAction_fin_lsc` is the finite-subdivision assembly theorem. It sums the
generalized chart kinetic terms of the local `timeH1` limits and the scalar
terms along the uniform manifold limit. It derives each local Lagrangian
integrability fact, each local lower and eventual upper action bound, and the
limit's compact chart-value condition internally. It therefore exposes neither
a global Lagrangian-integrability premise nor local action bounds.

`lRegAction_chart` is the complementary realization theorem. Given a finite
chart-valued `timeH1` representation of one manifold curve, it derives its
almost-everywhere manifold differentiability with `curve_mdiff_local`, proves
the kinetic and scalar integrability on every piece, and identifies the finite
generalized chart sum with the actual `lRegAction`. It uses the existing
finite-adjacent-interval identity internally and exposes no extra
integrability or differentiability assumptions.

`lRegAction_fin_cpt` is the corresponding noncompact finite-subdivision
producer. Its supplied compact target gives both the scalar lower bound needed
to control the chart-piece actions and the scalar dominated-convergence bound.
The new compact-target forms pass focused verification without warnings.

## Progress boundary

- `lKinetic_liminf`: 100% proved and focused-check green.
- The fixed-chart kinetic lower-semicontinuity bridge: 100%.
- `lRegAction_liminf`: 100% proved and focused-check green.
- The fixed-chart generalized regularized-action lower-semicontinuity stage:
  100%.
- The finite-sum liminf algebra needed for chart assembly: 100%.
- `lRegAction_fin_lsc`: 100% proved and focused-check green.
- The finite chart lower-semicontinuity assembly stage: 100%.
- `lRegAction_chart`: 100% proved and focused-check green.
- `exists_lMinimizer`: 0%; this theorem supplies only one dedicated analytic
  input and does not yet perform the finite chart extraction or regularity
  upgrade of the limiting manifold curve.
- `redVolume_anti`: 0%; no reduced-volume endpoint is stated or proved here.
