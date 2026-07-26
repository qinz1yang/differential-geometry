# GPT Pro consultation: H6 off-zero exponential branch

Post-audit status: the off-zero intrinsic Jacobi and endpoint-differential
questions are resolved. The remaining issue is the canonical radius/API design,
including the shrinkable `NormalCoordMetricBoundInput.radius`; use
`H6_RADIUS_CONSULT.md` for the current consultation prompt.

We are working on the short-time-existence alignment branch
`codex/short-time-existence-align`, current checked baseline commit
`4039d5eec17c891898b3463120840e2c161c1834`. The files below are repository
relative. Some declarations described as new are local uncommitted work, so
please reason from the supplied signatures when they are not visible remotely.

## Goal

Choose the smallest mathematically honest Lean route to a canonical framed
exponential partial diffeomorphism on a source ball whose radius is a fixed
positive fraction of the CGT injectivity profile. This is the missing
zero-order producer for
`C4.MetricCompactnessInputs.NormalRadiusProfile`; do not add a wrapper or an
assumption equivalent to that endpoint.

## Checked state

1. `Geometry/Comparison/InjectivityRadius.lean` defines `injRadius` as the
   supremum of framed model-ball radii on which
   `framedExpMap g p : E -> M` is injective.
2. The new checked lemmas are semantically:

   ```lean
   theorem exp_dom_of_inj
       (hinj : Set.InjOn (framedExpMap g p) (Metric.ball 0 r))
       (hz : z in Metric.ball 0 r) :
       normalFrame g p z in expDomain g p

   theorem exp_dom_of_inj_rad
       (hr : ENNReal.ofReal r < injRadius g p)
       (hz : z in Metric.ball 0 r) :
       normalFrame g p z in expDomain g p
   ```

   The proof uses the fact that the totalized exponential equals `p` outside
   `expDomain`, while zero is in the ball and maps to `p`.
3. `C4/H6NormalCoord.lean` has exact-green zero-order Jacobi/Rm04 estimates on
   `ball 0 (min (expRadiusGp / 26) r0)`, with one sequence-independent
   curvature scale `r0 > 0`. The remaining clamp is `expRadiusGp`, whose
   `expMapC2Radius` factor is a qualitative local choice.
4. `Geometry/Exponential/Smoothness/OffZero.lean` proves `C^infty` smoothness
   of `expMap` on one qualitative ball around zero, but despite its old header
   it has no theorem for arbitrary `v in expDomain`.
5. `Geometry/Exponential/IntrinsicExpContinuity.lean` proves joint continuity
   of the complete intrinsic geodesic in `(initialVelocity, time)` by a finite
   cross-chart continuation.
6. `Analysis/ODE/Flow/GlobalSliceSmoothness.lean` proves smooth dependence of
   exact ODE families while they remain in one smooth field domain.
7. `Geometry/Exponential/ExpVariationSmooth.lean` proves smoothness of special
   scalar two-parameter intrinsic exponential variations and smoothness of
   `diagExp` at the zero section, not Frechet smoothness in every launch
   vector.
8. `Geometry/Geodesic/CrossVFReduction.lean` now proves the focused- and
   exact-green theorem

   ```lean
   theorem Geodesic.geodesicVF_smooth
       (g : SmoothRiemannianMetric I M) :
       ContMDiff I.tangent I.tangent.tangent infinity
         (fun p : TangentBundle I M =>
           (p, geodesicVectorField g p))
   ```

   Thus global smoothness of the basepoint-free geodesic spray is no longer a
   missing premise. `local_flow_chartIsLocalFlow_and_realisation` can provide
   local smooth flow realizations for this autonomous field.
9. The finite-time question has now been resolved natively.
   `Analysis/ODE/TimeDependentFlow/SmoothDependence/CompactTrajectory.lean`
   proves the exact-green compact-restart theorem `ODE.flow_slice_smooth`.
   `Geometry/Exponential/IntrinsicVelocity.lean` identifies the complete
   intrinsic velocity lift as an exact spray trajectory and proves the
   focused-green theorems `velocityLift_one` and `intrinsicExp_smooth`.

## Precise obstruction

Injectivity supplies natural-domain membership, and the complete intrinsic
time-one endpoint is globally smooth. The global intrinsic Jacobi equation and
time-one differential identity are now proved. To replace the arbitrarily
selected `framedExpDiffeo.source` canonically, the remaining mathematical
frontier is agreement between the ordinary exponential used by `injRadius` and
the complete intrinsic exponential on the sub-injectivity ball.

The existing Jacobi variation API is itself clamped by `expMapC2Radius`, so it
cannot be used to prove the desired lower bound without circularity.

## Resolved route

Route 2 was implemented: compactness of each reference orbit supplies one
uniform restart width, local smooth spray flows are patched by uniqueness, and
the selected global trajectory is the intrinsic velocity lift. No new radius
assumption was introduced.

The old routes 1, 3, and 4 are no longer needed for endpoint smoothness.
`intrinsic_jacobi` and `intrinsic_jacobi_one` close the natural-domain Jacobi
and endpoint-differential question. The next audit should focus only on
ordinary/intrinsic agreement on the sub-injectivity ball.

## Questions

1. How should the ordinary `expMap` and complete `expMapIntrinsic` be related on
   a sub-injectivity ball without reintroducing a single-home-chart
   confinement assumption?
2. Resolved: `intrinsic_jacobi_one` derives the endpoint differential identity
   from the exact spray trajectory and fixed-fibre smoothness.
3. API located: `IsLocalDiffeomorphOn.exists_diffeo_of_injOn` constructs the
   partial diffeomorphism once injectivity and pointwise invertible derivative
   are available.

Constraints: preserve the current framed B/C consumer API, introduce no new
endpoint-equivalent assumption, do not use the qualitative
`framedExpDiffeo.source` to prove its own lower bound, and keep at most one real
mathematical frontier visible.
