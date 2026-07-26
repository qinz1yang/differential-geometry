# SmoothScalarGerm

## Current state

- `DifferentialGeometry.exists_smooth_germ` gives a globally smooth scalar
  representative of any scalar function smooth on an open neighborhood, with
  eventual equality at the chosen point.
- The proof uses the existing smooth bump basis, support-controlled gluing, and
  no geometry-specific assumptions.
- This extracts a proof pattern that previously existed only as duplicated
  private curvature helpers.

## Verification and role

Focused verification passed without warnings or placeholders.  The Hessian
chart bridge can use this theorem together with germ congruence instead of
strengthening local HCG cage smoothness to a false global hypothesis.
