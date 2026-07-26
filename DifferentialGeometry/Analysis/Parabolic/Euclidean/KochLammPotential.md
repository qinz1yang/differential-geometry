# KochLammPotential

## Status

Source complete. The focused Lean check passes with no local warnings.

## Exact boundary

This file supplies the previously absent full time-dependent potential
definitions for one component of a split source:

- `heatPot0` is the ordinary-source Duhamel potential;
- `heatPot1` is one directional divergence-source potential;
- `heatSplit` is their sum;
- `heatGrad0`, `heatGrad1`, and `heatSplitGrad` are the corresponding
  CLM-valued spatial-gradient candidates.

The full divergence potential is the finite sum of `heatPot1` over a fixed
orthonormal basis. Keeping the component direction explicit matches the
scalar heat-kernel derivative API and avoids hiding a tensor contraction.

`heatTerm0_fderiv` and `heatTerm1_fderiv` prove that the two spatial
integrands have exactly the CLM derivatives used in the gradient candidates.
They use the checked Gaussian derivative identities, not an assumed heat
solver.

## Remaining analytic passage

The next realization theorem must use concrete Koch--Lamm source bounds to
justify differentiation under both the spatial and time integrals. Its
dominating functions are respectively the first- and second-derivative
Gaussian majorants. The second-derivative flux arm requires the genuine
local parabolic energy / singular-integral argument; an absolute
`(t-s)^(-1)` time majorant is not integrable and must not be substituted.

This file does not prove any `Y_T → X_T` norm bound. The endpoint
`ricci_flow_forward_unique` remains 0%.
