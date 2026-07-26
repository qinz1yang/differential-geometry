# PullbackCross

## Status

`PullbackCross.lean` is green and contains no placeholders.

The checked pointwise producer `covAlong_mapCrossAt` proves cross-model
naturality of `covDerivAlong` for the restriction of a globally smooth tangent
section, assuming only `ContMDiffAt` for the curve at the evaluation time.  Its
local covariant chain rule uses the public Christoffel correction/contraction
bridge and `metricCov_pullbackCross`.  `covAlong_mapCross` remains the global
smoothness wrapper.

The canonical pointwise producer `covAlong_natCrossAt` removes the
ambient-section restriction.  At a fixed time it extends the value of an arbitrary
differentiable along-curve section to a globally smooth tangent section, then
subtracts that extension.  The residual vanishes at the foot.  In fixed source
and target charts, the derivative of `dPhi` applied to this residual has no
base-derivative term because the residual value is zero, so the residual
covariant derivatives transform by `dPhi`.  Additivity then recombines the
ambient and residual parts.

`covAlong_natCross` is now only the globally smooth wrapper around this
pointwise theorem.  No global extension of the curve is used.

This is genuine connection/parallel-transport infrastructure; it does not by
itself prove the HCG moving inverse or compactness endpoint.  Those target
theorems remain unstated and therefore 0% complete.

## Scope

`covAlong_natCrossAt` handles an arbitrary dependent family
`V : (s : ℝ) → T_(gamma s) M` whose pinned chart representation is
differentiable at the evaluation time.  The curve hypothesis is pointwise
`ContMDiffAt ... ∞`; open-set consumers obtain it directly from
`ContMDiffOn` and openness.  The connection-naturality localization gap is
closed.

## Verification

Focused verification passed without warnings, and the exported module refresh
completed successfully.  Replayed warnings were confined to pre-existing
upstream modules.
