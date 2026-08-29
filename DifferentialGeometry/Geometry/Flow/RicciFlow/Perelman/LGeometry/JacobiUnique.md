# Regularized L-Jacobi uniqueness

## Verified coefficient brick

The private theorem `lRegJacCLM_cont` is verified without warnings.  It
reconstructs the geometric velocity from its chart coordinate, evaluates the
continuous curvature, Hessian, Ricci, and covariant-Ricci families on continuous
tangent sections, and raises the resulting covector through the inverse Gram
matrix.  The final operator-norm continuity step uses finite-basis evaluation
rather than unfolding tensor or Hom representations.

The only verification interruption was a stale `Jacobi` artifact that did not
yet export the newly checked force and coefficient declarations.  A targeted
refresh resolved it; there is no remaining proof or API blocker in this brick.

## Verified global uniqueness

The public theorem `lRegJacobi_unique` is verified without warnings.  It first
packages a field and its moving-metric covariant velocity as a paired tangent
state.  Around each time it reconstructs the geometric curve velocity from one
fixed chart, applies `lRegJacCLM_cont`, and invokes the native linear-ODE
uniqueness theorem.  Equality then propagates across the connected open time
set because the equal-state set is open and relatively closed.

The theorem assumes only the regular-time condition, differentiability of the
curve velocity coordinates, the two existing `IsLRegJacobi` predicates, and
equality of the field and moving covariant velocity at one time.  No regularized
L-curve equation or acceleration hypothesis is added.

`lRegJacobi_unique` is complete (100%), and its dedicated fixed-chart
uniqueness machinery is complete for this endpoint (100%).  The broader
dedicated L-geometry machinery remains about 50%; `redVolume_anti` remains
unproved at 0%.
