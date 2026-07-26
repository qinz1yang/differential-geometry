# KochLammHmf

## Status

Source complete. The focused Lean check passes with no local warnings.

## Proved source assembly

`klHmf_split` packages the two nonlinear arms of one local-addition
harmonic-map heat iterate into the exact `KLSplit` carrier:

- a uniformly `ε`-bounded linear coefficient applied to the path gradient is
  a divergence source with radii `ε A₂` and `ε Aₚ`;
- a uniformly `K`-bounded bilinear coefficient applied twice to that gradient
  is an ordinary source with radii `K A₂²` and `K Aₚ²`.

Thus the critical principal arm keeps the genuine small coefficient `ε`,
while the lower-order arm is small on a small Koch--Lamm gradient ball. No
pointwise weighted-gradient surrogate and no false horizon gain is used.
The principal coefficient now has an independent output type, so this theorem
applies to the genuine operator-valued divergence flux rather than only to a
single directional component.  The updated theorem passes a warning-free
focused check against the exported two-codomain `KLSplit` interface.

## Remaining producer

The direct missing analytic map is now sharply isolated: the heat potential
of an arbitrary `KLSplit T A₁ A_q A₂ Aₚ f₀ f₁` must produce one `KLPath`
on the same horizon. Of this map, the current checked source proves only the
early-time part of the `f₀` value estimate (`kl0_early_norm`). It must still
prove:

1. the late-time `f₀` value estimate and both early/late value estimates for
   the differentiated `f₁` potential;
2. the full-cylinder, scale-invariant local spacetime `L²` gradient estimate
   for both source arms;
3. the late-half-cylinder, scale-invariant `L^(n+4)` gradient estimate for
   both source arms.

The kernel library already supplies pointwise Gaussian derivative bounds,
finite-`p` spatial convolution bounds, the heat-kernel PDE, and the early
ordinary-source value estimate. It does not yet define and verify the full
time-dependent split potential, identify its realized spatial gradient, or
prove the local parabolic energy / late Calderón--Zygmund estimates above.

The endpoint `ricci_flow_forward_unique` remains 0% until the heat map,
fixed point, finite-chart realization, and gauge removal are all proved.
