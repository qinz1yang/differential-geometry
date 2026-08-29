# WeakBarrier

## Target

`exists_redWeak_sup` is the canonical all-point, noncompact weak upper-barrier
theorem for reduced length.  It returns an open product neighborhood in space
and backward time, a smooth spatial support at the base time, its time
derivative, and Perelman's backward differential inequality up to an arbitrary
positive error.  The support statement is genuinely product-local; separate
slice and time-line bounds are not used as a substitute.

## Source route

- Obtain the minimizing initial vector with `exists_lMinVec_rm`, using a global
  smooth competitor from the complete connected background metric.  This is the
  noncompact replacement for the compact minimizer route.
- Choose a positive cutoff by `lKTail_tendsto`, then construct the local tail
  family.  Use `exists_lRayAdapt` on the canonical ray and transport its frame
  locally to the tail-family center through germ equality.
- Define one joint inverse branch in endpoint and terminal parameter.  For every
  nearby space-time point, splice the canonical head to that moving tail and use
  `lRegCosts_bdd_rm` with `lCost_le_join_bdd`; this proves the full product upper
  support without a compactness instance.
- Differentiate the joint branch in time.  For the spatial Laplacian, use the
  fixed terminal-time branch and reconcile it with the joint slice using
  `lTailInv_slice` and `laplacian_congr_of_eventuallyEq`.
- Combine `lTail_lap_K` with the Hamilton energy identity.  The remaining scalar
  error is selected to be below `eps` by the cutoff limit.

The public statement does not expose the minimizer, the adapted frame, or a new
support class.  It does not use the forward-sign `ParabolicUpperSupportAt` API.

## Verification state

`WeakBarrier.lean` is warning-free focused GREEN.  The public theorem
`exists_redWeak_sup` is fully proved, with no `sorry`, `admit`, or new `axiom`.
Its exact producer chain is:

1. a complete-metric smooth competitor followed by `exists_lMinVec_rm`;
2. `lKTail_tendsto` and `exists_lTail_inj` for the positive cutoff and joint
   tail family;
3. `exists_lRayAdapt` for the canonical-ray frame;
4. `lRegCosts_bdd_rm` and `lCost_le_join_bdd` for the noncompact product
   upper-support inequality;
5. `lTailJoint_mfd` for the joint endpoint-time derivative;
6. `lTailInv_slice` and `laplacian_congr_of_eventuallyEq` for fixed/joint slice
   compatibility;
7. `lTail_lap_K` and the Hamilton energy identity for the pre-limit bound.

The theorem's own module has received warning-free focused verification and an
explicit named artifact refresh.  The umbrella import also checks warning-free.

## Lean lessons

- The temporary complete background metric must live inside the existential
  competitor construction, and the theorem uses the same scoped removal of the
  canonical tangent-space norm instances as the checked noncompact minimizer
  proofs.  Otherwise the temporary Riemannian-bundle instance leaks into the
  tail APIs and creates an instance diamond.
- `lTailInv_slice` identifies only the first coordinate of the joint inverse.
  The terminal coordinate comes separately from the joint right-inverse, and
  the resulting germ must be transported from `alpha (A0,b)` to `y` explicitly.
- Adapted fields over the canonical ray transfer to the family center through
  their common model-space values and germ equality; dependent tangent fibers
  should not be rewritten as if they were definitionally identical.
- For the joint time derivative, typed continuous-linear maps `Lj` and `Lq`
  keep the composition stable.  Projection evaluation across the tangent-model
  alias is most robustly closed by congruence of the whole summands rather than
  subterm rewriting.
- The center-tail and canonical-ray `lKTail` terms require an explicit
  interval-integral congruence using point and velocity germs.  The Laplacian
  bound is first proved for the center tail and only then transported.

## Progress accounting

- `exists_redWeak_sup`: **100% theorem endpoint** and **100% dedicated
  assembly**; warning-free focused verification, named refresh, and umbrella
  verification are complete.
- The subsequent endpoints `exists_redLen_le`, `redVolume_late_low`,
  `smooth_nlc`, the P2 endpoint, and the final Poincare endpoint remain 0%.
- `ReducedVolume.redVolume_anti` is already declared and checked: 100%.
- This lane belongs to the late L-geometry barrier/semiconcavity phase.  The
  dedicated complete-flow L8--L9 lane is now about **66--68%**, while the
  entire fixed-manifold P0--P9 infrastructure remains roughly **15--25%** of
  the full Poincare formalization program.  The exact next downstream theorem
  is `exists_redLen_le`.
