# HeatEarlyFlux

## Verified producer

`HeatEarlyFlux.lean` proves the near-cylinder part of the early
`Y¹ -> L∞` heat-potential estimate for a divergence source.

- `lintegral_enorm_le_sqrt` is the finite-measure `L² -> L¹`
  Cauchy--Schwarz inequality in the ENNReal form used by rough cylinder
  masses.
- `earlyFluxCyl_volume_le` bounds an early half-cylinder by its exact
  parabolic volume scale `(sqrt t)^(n+2)`.
- `earlyFlux_l1` and `earlyFlux_l1_scale` turn `GradCarl` control into local
  `L¹` mass and prove that its scale is exactly `(sqrt t)^(n+1)`.
- `halfScale_cancel_succ` cancels that scale against the first spatial
  derivative of the heat kernel.
- `heatD1_early_near` is the concrete fixed-scale Gaussian bound on the
  near cylinder.
- `heatEarly1Near_norm` bounds the actual Bochner potential by
  `ofReal ||w|| * earlyFluxC(V) * C^(1/2)`, uniformly in the observation
  time.
- `earlyFlux_cover_l1` bounds the early-slab `L¹` source mass on any set
  covered by finitely many heat-scale balls by the cover cardinality times
  the scale-cancelled local gradient-Carleson mass.  It is independent of the
  particular quantitative covering theorem.
- `heatD1_early_shell` retains the exact `(k+1) exp(-k²/4)` radial-Gaussian
  factor of the first heat derivative on shell `k`; `fluxShellCyl_meas`
  supplies the measurable shell cylinder needed by the integral comparison.
- `fluxShellMass_raw` combines that pointwise kernel bound with
  `earlyFlux_cover_l1`, giving the complete pre-cancellation bound for one
  shell and an arbitrary finite heat-scale cover.
- `fluxShellMass_le` inserts the quantitative cardinality bound and cancels
  every power of `sqrt t`; the remaining factor is exactly polynomial cover
  growth times `(k+1) exp(-k/4)`.
- `heatEarly1_norm` sums the shell masses over the full early slab.  It is
  parameterized by the quantitative covers and a weight-series majorant, so
  the canonical cover and summability files need only supply a short bridge.

The focused Lean check passes with no warnings. The source contains no
`sorry`, `admit`, axiom, opaque replacement, new class, instance, or notation.

## Honest frontier

This file now contains the full analytic early divergence-potential estimate,
parameterized by quantitative covers and the shell-series majorant. The next
producer must instantiate the existing canonical finite-ball cover and the
checked `fluxShellWeight_sum`. After that, `KLSource1.local_l2` converts
the squared radius to its stated `A₂` bound.

The exact theorem `ricci_flow_forward_unique` remains 0% until the complete
heat map, harmonic-map heat-flow gauge, Ricci--DeTurck uniqueness continuation,
and gauge removal are proved. `ricci_flow_unif_existence` also remains 0%.
