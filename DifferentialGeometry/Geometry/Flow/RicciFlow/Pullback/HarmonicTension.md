# HarmonicTension

## Source status

This file supplies the first coordinate-free geometric producer for the
harmonic-map gauge.  It was written while another named Lean export owned the
single build slot, so focused elaboration is still pending.  There is no
`sorry`, `admit`, axiom, opaque replacement, new class, instance, or notation.

## Implemented facts

- `connDiff_neg` proves that reversing the two Levi-Civita endpoints negates
  the connection-difference tensor.
- `idTension` is the actual `g`-orthonormal-frame trace of
  `nabla(h) - nabla(g)`, rather than a renamed DeTurck vector field.
- `idTension_eq` proves
  `idTension g h = -deTurckVF g h` pointwise from
  `deTurckVF_eq_orthoFrame_trace` and `connDiff_neg`.
- `idTensionVF` packages the resulting smooth vector field.
- `diffeoTension g h Phi` pushes the identity tension for
  `(M,g) -> (M,Phi*h)` through `Phi`.  `tension_image` proves its evaluation at
  `Phi x` is

  ```text
  - dPhi_x (deTurckVF g (Phi*h) x).
  ```

- `tension_eq_push` packages the same formula as equality with the negative
  pushed-forward DeTurck vector field on the target.  This is the exact shape
  consumed when `symm_gauge_vel` differentiates the inverse family.
- `tension_eq_DT` applies DeTurck naturality and identifies the same tension
  directly with the negative DeTurck field of the inverse-pulled source
  metric.
- `hmf_neg_gauge` rewrites a time-dependent HMF equation into that
  inverse-family-ready negative-gauge equation without adding an existence
  hypothesis or changing the time window.
- `hmf_target_gauge` exports the target-metric version used by the complete
  inverse-gauge composition.
- `tension_refl` gives the exact harmonic-map sign at the identity gauge.

This is the correct diffeomorphism-level tension formula and directly matches
the negative-gauge convention consumed by `symm_gauge_vel` after inversion.

## Remaining analytic frontier

The file does not claim harmonic-map heat-flow existence.  Before the map has
been proved to be a diffeomorphism, the local-addition unknown is a tangent
section `V` and `x |-> exp_x(V x)` is only a smooth self-map.  A solver still
needs the component-local realization of that map's tension as a strongly
parabolic equation for `V`, including:

1. the second-derivative principal term, equal at the zero section to the
   vector connection Laplacian;
2. time-dependent tame bounds for the remaining local-addition terms;
3. initial-edge coefficient bounds derived from the endpoint's joint
   smoothness and continuity hypotheses;
4. the finite-cover `C1` argument making the solved maps diffeomorphisms on a
   common short window.

Thus the geometric sign/trace layer is source-complete here, while exact HMF
existence and `ricci_flow_forward_unique` remain 0% until those producers are
proved and focused-verified.
