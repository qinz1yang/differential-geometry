import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorSmoothChartComponent

/-!
# The smooth representative *is* the connection-Laplacian resolvent eigenvector

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)` and an eigenbasis
index `i`, the smooth representative `eigenvectorSmooth g r s i` is
a genuine smooth compactly-supported `(r, s)`-tensor section. The chart-component
analysis has shown that, at every chart centre `β` and component multi-index
`P₀`, its canonical Euclidean chart component agrees — as an element of the chart
`L²` space — with the chart component of the abstract connection-Laplacian
resolvent eigenvector `tensorResolventEigenbasisVec`.

This file is the thin assembly that converts that chart-by-chart agreement into
the headline identifications, re-keyed onto the intrinsic compact-operator
eigenbasis at the unconditional compactness witness
`tensorResolventL2_isCompactOperator`.

## Main results

* `eigenvectorSmooth_toL2` — the image of
  `eigenvectorSmooth` in the metric `L²` Hilbert space
  `TensorL2 r s g` equals the eigenvector
  `tensorResolventEigenbasisVec`. The chart-component separation
  theorem `tensorL2_eq_of_chartComponent_eq` reduces the equality to the
  chart-component agreement
  `eigenvectorSmooth_tensorL2ChartComponent_eq`, which supplies
  exactly the `∀ β P₀` family of chart-component equalities the separation
  theorem demands.

* `tensorEigenvector_exists_smooth` — the abstract eigenvector
  `tensorResolventEigenbasisVec` is the `L²`-coercion of a smooth
  compactly-supported tensor section. The witness is
  `eigenvectorSmooth`, whose `SmoothCcTensor` type is exactly the
  type of smooth compactly-supported `(r, s)`-tensor sections.

* `eigenvectorSmooth_contMDiff` — the underlying section of
  `eigenvectorSmooth` is `C^∞`. This is the smoothness datum
  carried by the `SmoothCcTensor` structure, made explicit.

* `eigenvectorSmooth_weak_eigen` — the smooth weak eigen-equation:
  testing the eigenvector resolvent `eigenvectorResolvent g r s i`
  against a smooth compactly-supported `H¹` section `S`, its `H¹` pairing with
  the completion embedding of `S` equals the `L²` pairing of the underlying
  smooth `L²` section of `S` with the smooth representative
  `eigenvectorSmooth g r s i`. This is the eigenvector weak
  equation `eigenWeakEquation`, transported across
  `eigenvectorSmooth_toL2`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `eigenvectorSmooth_toL2`. -/
theorem eigenvectorSmooth_toL2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g) =
      tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i :=
  tensorL2_eq_of_chartComponent_eq (I := I) (M := M) g r s
    (eigenvectorSmooth (I := I) (M := M) g r s i : TensorL2 r s g)
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    (fun β P₀ => eigenvectorSmooth_tensorL2ChartComponent_eq
      (I := I) (M := M) g r s i β P₀)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `tensorEigenvector_exists_smooth`. -/
theorem tensorEigenvector_exists_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ∃ T : SmoothCcTensor g r s,
      (T : TensorL2 r s g) =
        tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i :=
  ⟨eigenvectorSmooth (I := I) (M := M) g r s i,
    eigenvectorSmooth_toL2 (I := I) (M := M) g r s i⟩

/-- Chart-locality-free twin of `eigenvectorSmooth_contMDiff`. -/
theorem eigenvectorSmooth_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        TotalSpace.mk' (TensorRSModel r s ℝ E) x
          ((eigenvectorSmooth (I := I) (M := M) g r s i).toSection x)) :=
  (eigenvectorSmooth (I := I) (M := M) g r s i).toSection.contMDiff

/-- Chart-locality-free twin of `eigenvectorSmooth_weak_eigen`. -/
theorem eigenvectorSmooth_weak_eigen
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (S : SmoothCcTensorH1 g r s) :
    ⟪eigenvectorResolvent (I := I) (M := M) g r s i,
        (smoothToTensorH1Compl (I := I) (M := M) g r s S)⟫_ℝ =
      ⟪(S.toCcTensor : TensorL2 r s g),
        (eigenvectorSmooth (I := I) (M := M) g r s i :
          TensorL2 r s g)⟫_ℝ := by
  rw [eigenvectorSmooth_toL2 (I := I) (M := M) g r s i]
  exact eigenWeakEquation (I := I) (M := M) g r s i S

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
