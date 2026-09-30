import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseCometricMultiplier
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.CometricSlotPairing
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner
import DifferentialGeometry.Geometry.Connection.ParsevalFrameField
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Bounds.CovariantTwoTensor.FrameExpansion

open DifferentialGeometry.TensorMetric
  (fiberNormSqComponent tensorInnerPointwise tensorInnerPointwise_eq_sum_componentS_mul)
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry.Analysis.Laplacian

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem tensorL2Inner_slotΛ_le
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {κ : ℝ}
    (Wfield Sfield : M → TensorRSModel 0 (s + 1) ℝ E)
    (hptwise : ∀ x : M,
      tensorInnerPointwise g₀ 0 (s+1) x (Wfield x) (Sfield x)
        ≤ κ * tensorInnerPointwise g₀ 0 (s+1) x (Wfield x) (Wfield x))
    (hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s+1) x (Wfield x) (Sfield x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀))
    (hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s+1) x (Wfield x) (Wfield x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀)) :
    tensorL2Inner g₀ 0 (s+1) Wfield Sfield
      ≤ κ * tensorL2Inner g₀ 0 (s+1) Wfield Wfield := by
  unfold tensorL2Inner
  rw [← MeasureTheory.integral_const_mul]
  refine integral_mono hWS_int (hWW_int.const_mul κ) ?_
  intro x; exact hptwise x

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem tensorL2Inner_gInvDiffSlot_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (s : ℕ) (W : ∀ x, TensorRSSpace 0 (s+1) I x)
    (hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s+1) x
        (TensorRSSpace.toModel (W x))
        (TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x))))
      (riemannianVolumeMeasure (I := I) (M := M) g₀))
    (hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s+1) x
        (TensorRSSpace.toModel (W x)) (TensorRSSpace.toModel (W x)))
      (riemannianVolumeMeasure (I := I) (M := M) g₀)) :
    tensorL2Inner g₀ 0 (s+1)
        (fun x => TensorRSSpace.toModel (W x))
        (fun x => TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x)))
      ≤ (δ / (1 - δ)) * tensorL2Inner g₀ 0 (s+1)
          (fun x => TensorRSSpace.toModel (W x)) (fun x => TensorRSSpace.toModel (W x)) := by
  refine tensorL2Inner_slotΛ_le g₀ s
    (fun x => TensorRSSpace.toModel (W x))
    (fun x => TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x)))
    (fun x => ?_) hWS_int hWW_int
  exact tensorInnerPointwise_gInvDiffSlot_le g₀ g₁ h htie hδ_lt hδ_nn hδ s x (W x)


omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem neg_gInvDiffSlot_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (s : ℕ) (W : ∀ x, TensorRSSpace 0 (s + 1) I x)
    (hWS_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
        (TensorRSSpace.toModel (W x))
        (-TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x))))
      (riemannianVolumeMeasure (I := I) (M := M) g₀))
    (hWW_int : Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + 1) x
        (TensorRSSpace.toModel (W x)) (TensorRSSpace.toModel (W x)))
      (riemannianVolumeMeasure (I := I) (M := M) g₀)) :
    tensorL2Inner g₀ 0 (s + 1)
        (fun x => TensorRSSpace.toModel (W x))
        (fun x => -TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x))) ≤
      (δ / (1 - δ)) * tensorL2Inner g₀ 0 (s + 1)
        (fun x => TensorRSSpace.toModel (W x)) (fun x => TensorRSSpace.toModel (W x)) := by
  refine tensorL2Inner_slotΛ_le g₀ s
    (fun x => TensorRSSpace.toModel (W x))
    (fun x => -TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x (W x)))
    (fun x => ?_) hWS_int hWW_int
  exact negDiffSlot_point_le g₀ g₁ h htie hδ_lt hδ_nn hδ s x (W x)


omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] in
theorem negSlotAtL2_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (r : ℕ) (j : Fin r) (W : ∀ x, TensorRSSpace 0 r I x)
    (hWS_int : Integrable
      (fun x ↦ tensorInnerPointwise (I := I) (M := M) g₀ 0 r x
        (TensorRSSpace.toModel (W x))
        (-TensorRSSpace.toModel (gInvDiffSlotAt (I := I) g₀ g₁ r j x (W x))))
      (riemannianVolumeMeasure (I := I) (M := M) g₀))
    (hWW_int : Integrable
      (fun x ↦ tensorInnerPointwise (I := I) (M := M) g₀ 0 r x
        (TensorRSSpace.toModel (W x)) (TensorRSSpace.toModel (W x)))
      (riemannianVolumeMeasure (I := I) (M := M) g₀)) :
    tensorL2Inner g₀ 0 r
        (fun x ↦ TensorRSSpace.toModel (W x))
        (fun x ↦ -TensorRSSpace.toModel (gInvDiffSlotAt (I := I) g₀ g₁ r j x (W x))) ≤
      (δ / (1 - δ)) * tensorL2Inner g₀ 0 r
        (fun x ↦ TensorRSSpace.toModel (W x))
        (fun x ↦ TensorRSSpace.toModel (W x)) := by
  unfold tensorL2Inner
  rw [← MeasureTheory.integral_const_mul]
  refine integral_mono hWS_int (hWW_int.const_mul (δ / (1 - δ))) ?_
  intro x
  exact negDiffSlotAt_le g₀ g₁ h htie hδ_lt hδ_nn hδ r j x (W x)

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
