# LipschitzGradient

## 2026-07-16 sharp differentiability-point bound

`grad_norm_le_lip` is proved and focused verification passes without warnings.
It states that an explicitly Riemannian-distance `L`-Lipschitz real function
has Riemannian gradient norm at most `L` at every manifold differentiability
point.

The successful normal form is one-dimensional.  Set
`v = gradFun g u x`, test `u` on the radial curve
`t ↦ expMap g x (t • v)`, use `edist_exp_le_radius`, and apply
`HasDerivAt.le_of_lip'` at `t = 0`.  This needs only a center-to-radial-point
distance estimate, so it avoids proving that an exponential chart is
Lipschitz between arbitrary pairs of tangent vectors and introduces no chart
comparison constant.  Scalarizing the curve also avoids the tangent/model
norm topology diamond in the derivative estimate.

`CompleteSpace E`, `T2Space (TangentBundle I M)`, and positive model dimension
are internalized: finite dimensionality supplies completeness, the existing
fiber-bundle theorem supplies Hausdorffness of the tangent bundle, and the
zero-dimensional case is split before installing `NeZero`.  The live theorem
still honestly requires `InnerProductSpace ℝ E` and `I.Boundaryless`, because
the current local exponential-map API has those assumptions.  They were not
added to any Noncollapsing consumer.

Failed proof shapes:

- Bounding the full Frechet derivative of `u ∘ expMap` used the fixed model
  norm and therefore could not recover the exact Riemannian constant.
- Installing the Riemannian tangent norm before forming the small model-space
  ball exposed the tangent/model norm instance diamond.  The final proof forms
  the model-norm neighborhood first and only then installs the metric bundle.
- A whole exponential-chart Lipschitz theorem is unnecessary; Mathlib's
  center-point `HasDerivAt.le_of_lip'` is the cheaper interface.

Honest accounting: `grad_norm_le_lip` and its everywhere representative form
`grad_norm_le_lip_all` are **100%**.  The downstream `weak_grad_of_lip`,
gradient-norm measurability, and `memW1p_of_lip` are now also checked.  The
dedicated cutoff machinery is approximately **80%**; the remaining producer is
a quantitative chart-W¹ to intrinsic-gradient estimate for a Lipschitz input
minus a smooth approximant.  `exists_cutoff_energy` and the Noncollapsing
endpoint theorems remain theorem-level **0%**.

## 2026-07-17 regularity cleanup

The file no longer inherits the accidentally stronger `IsManifold I ⊤ M`
context. Its section now uses the standard analytic smooth regularity with an
explicit `WithTop ℕ∞` annotation, avoiding the scoped-notation ambiguity
that made a bare infinity elaborate as the wrong type. Focused verification
and the targeted module refresh passed; no consumer assumption changed.
