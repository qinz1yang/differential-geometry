import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs

/-!
# The rank-`r` order-`2` rough-Laplacian / covariant-gradient commutator defect

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`, this thin upstream file
holds the single contravariant-rank-`r` commutator-defect definition

```
pointwiseTensorCurvRS g r s S := Δ_∇(∇S) − ∇(Δ_∇ S)
```

a smooth compactly-supported `(r, s + 1)`-tensor field (`∇S = covGrad g r s S`,
`Δ_∇ = rawTensorConnLapSmooth`). It is the contravariant-rank-`r` lift of `pointwiseTensorCurv`
(`PointwiseTensorBochner`); at `r = 0` it is definitionally `pointwiseTensorCurv g s`.

The definition lives here, upstream of both its moving-frame field apparatus
(`MovingFrameGenuineFieldPairingRS`) and its Hom-field curvature jet decomposition
(`HomFieldCurvatureJetDecomposition`), so the two consume the shared defect without a file-level
import cycle.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **The rank-`r` order-`2` commutator defect.** The difference of the rough Laplacian of the
`(r, s + 1)`-tensor gradient field `∇S` and the covariant gradient of the rough Laplacian of `S`, as a
smooth compactly-supported `(r, s + 1)`-tensor field:
```
pointwiseTensorCurvRS g r s S := Δ_∇(∇S) − ∇(Δ_∇ S).
```
This is the contravariant-rank-`r` lift of `pointwiseTensorCurv` (`PointwiseTensorBochner`); at `r = 0`
it is definitionally `pointwiseTensorCurv g s`. Its body matches the inline defect form the rank-`r`
leaf-`C` consumers (`LocalWeylReproducingKernel`) state. -/
noncomputable def pointwiseTensorCurvRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    SmoothCcTensor g r (s + 1) :=
  rawTensorConnLapSmooth (I := I) g r (s + 1) (covGrad (I := I) (M := M) g r s S) -
    covGrad (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s S)

end Connection
end Integral
end DifferentialGeometry
