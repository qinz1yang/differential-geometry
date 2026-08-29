# RiemannianDistContinuity

## Compact metric comparison

The live API already contained `continuous_riemannianEDist`, but that theorem is
pointwise in a fixed base point and does not provide the uniform modulus needed
for equicontinuity.  No existing theorem directly converted uniformly small
Riemannian extended distance into an arbitrary compatible `dist` on a compact
manifold.

`dist_lt_of_riedist` fills this canonical gap.  Given `ε > 0`, it supplies
`δ > 0` such that

```text
riemannianEDist I x y < ENNReal.ofReal δ  →  dist x y < ε
```

uniformly in `x` and `y`.  Compatibility is encoded structurally: the
`PseudoMetricSpace` instance is present before the manifold `ChartedSpace`, so
the chart topology is the metric topology.

The proof reuses `compactSpace_uniformity`, `Metric.dist_mem_uniformity`,
`uniformity_basis_edist_nnreal`, and
`PseudoEMetricSpace.ofRiemannianMetric`.  It requires neither completeness nor
an `IsMetricNorm` consumer assumption.  A consumer phrased with
`riemannianEDistOf g` can expose its local Riemannian-bundle instance and use
this theorem by simplification of `riemannianEDistOf`.

`dist_lt_riedist_cpt` is the proper-subset form needed on complete noncompact
manifolds.  It assumes only that the relevant target set is compact, restricts
both compatible uniform structures to that subtype, and uses uniqueness of the
uniformity on a compact Hausdorff space.  Thus it supplies the same uniform
modulus for points in the compact set without a `CompactSpace` instance on the
ambient manifold.

A direct import of `DistanceScaling` was rejected because it perturbed the
tangent inner-product instance environment of this established comparison
file.  Keeping the canonical let-bound `riemannianEDist` statement avoids that
import and remains definitionally compatible with `riemannianEDistOf` consumers.

## Verification and frontier

Focused verification and the targeted module refresh of the new compact-subset
form passed without warnings. The compact
Riemannian-distance-to-compatible-distance bridge is complete.  It converts an
existing square-root extended-distance modulus into ordinary metric
equicontinuity; it does not itself supply the separate Arzelà–Ascoli subsequence
or lower-semicontinuity steps of the direct method.
