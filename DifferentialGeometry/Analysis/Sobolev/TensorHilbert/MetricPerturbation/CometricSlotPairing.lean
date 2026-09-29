import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ComparisonEndomorphismPairing
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


def gInvDiffSlotApplied (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) : TensorRSSpace 0 (s+1) I x :=
  TensorRSSpace.ofCLM ((slotInsertEndoFib (s+1) 0 x
    (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x)).comp
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s+1) I x from W))

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorInnerPointwise_gInvDiffSlot_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (s : ℕ) (x : M) (W : TensorRSSpace 0 (s+1) I x) :
    tensorInnerPointwise g₀ 0 (s+1) x
        (TensorRSSpace.toModel W)
        (TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x W))
      ≤ (δ / (1 - δ)) * tensorInnerPointwise g₀ 0 (s+1) x
          (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis_E (I := I) (M := M) g₀ x
  exact tensorInnerPointwise_slotΛ_le g₀ s x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x)
    (metricComparisonDifferenceEndomorphism_g0_self_adjoint (I := I) g₀ g₁ x)
    (fun v => metricComparisonDifferenceEndomorphism_inner_self_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v)
    W e bse hbse horth

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

def gInvDiffSlotAt (g₀ g₁ : SmoothRiemannianMetric I M) (r : ℕ) (j : Fin r) (x : M)
    (W : TensorRSSpace 0 r I x) : TensorRSSpace 0 r I x :=
  TensorRSSpace.ofCLM
    ((slotInsertEndoFib r j x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x)).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))

private noncomputable def negDiffSlotApplied
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) : TensorRSSpace 0 (s + 1) I x :=
  TensorRSSpace.ofCLM
    ((slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (-metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x)).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem negDiffSlot_eq_neg
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    negDiffSlotApplied (I := I) g₀ g₁ s x W =
      -gInvDiffSlotApplied (I := I) g₀ g₁ s x W := by
  rw [negDiffSlotApplied, gInvDiffSlotApplied,
    show (-metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x) =
        (-1 : ℝ) • metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x from
      (neg_one_smul ℝ _).symm,
    slotInsertEndoFib_smul_left (I := I) (M := M) (s + 1) 0 x,
    neg_one_smul, ContinuousLinearMap.neg_comp]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem negDiffSlot_model
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (W : TensorRSSpace 0 (s + 1) I x) :
    TensorRSSpace.toModel
        (negDiffSlotApplied (I := I) g₀ g₁ s x W) =
      -TensorRSSpace.toModel
        (gInvDiffSlotApplied (I := I) g₀ g₁ s x W) := by
  rw [negDiffSlot_eq_neg (I := I) g₀ g₁ s x W, TensorRSSpace.toModel_neg]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem negDiffEndo_adjoint
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a b : TangentSpace I x) :
    g₀.inner x ((-metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x) a) b =
      g₀.inner x a ((-metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x) b) := by
  simp only [neg_apply, map_neg]
  rw [metricComparisonDifferenceEndomorphism_g0_self_adjoint (I := I) g₀ g₁ x a b]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem negDiffEndo_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (x : M) (v : TangentSpace I x) :
    g₀.inner x ((-metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x) v) v ≤
      (δ / (1 - δ)) * g₀.inner x v v := by
  rw [neg_apply (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x) v,
    map_neg (g₀.inner x)]
  have hbnd := abs_inner_metricComparisonDifferenceEndomorphism_le
    (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v v
  have hv_nn : 0 ≤ g₀.inner x v v :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) =
      g₀.inner x v v := by
    rw [← Real.sqrt_mul hv_nn, Real.sqrt_mul_self hv_nn]
  calc
    -g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) v
        ≤ |g₀.inner x (metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x v) v| := neg_le_abs _
    _ ≤ (δ / (1 - δ)) *
        (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := hbnd
    _ = (δ / (1 - δ)) * g₀.inner x v v := by rw [hsq]

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem negDiffSlot_point_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (s : ℕ) (x : M) (W : TensorRSSpace 0 (s + 1) I x) :
    tensorInnerPointwise g₀ 0 (s + 1) x
        (TensorRSSpace.toModel W)
        (-TensorRSSpace.toModel (gInvDiffSlotApplied (I := I) g₀ g₁ s x W)) ≤
      (δ / (1 - δ)) * tensorInnerPointwise g₀ 0 (s + 1) x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis_E (I := I) (M := M) g₀ x
  have hslot := tensorInnerPointwise_slotΛ_le g₀ s x
    (-metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x)
    (negDiffEndo_adjoint (I := I) g₀ g₁ x)
    (fun v => negDiffEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v)
    W e bse hbse horth
  rw [← negDiffSlot_model (I := I) g₀ g₁ s x W]
  exact hslot

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

private noncomputable def negDiffSlotAt
    (g₀ g₁ : SmoothRiemannianMetric I M) (r : ℕ) (j : Fin r) (x : M)
    (W : TensorRSSpace 0 r I x) : TensorRSSpace 0 r I x :=
  TensorRSSpace.ofCLM
    ((slotInsertEndoFib (I := I) (M := M) r j x
        (-metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x)).comp
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from W))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
private theorem negSlotAt_model
    (g₀ g₁ : SmoothRiemannianMetric I M) (r : ℕ) (j : Fin r) (x : M)
    (W : TensorRSSpace 0 r I x) :
    TensorRSSpace.toModel (negDiffSlotAt (I := I) g₀ g₁ r j x W) =
      -TensorRSSpace.toModel (gInvDiffSlotAt (I := I) g₀ g₁ r j x W) := by
  rw [negDiffSlotAt, gInvDiffSlotAt,
    show (-metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x) =
        (-1 : ℝ) • metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x from
      (neg_one_smul ℝ _).symm,
    slotInsertEndoFib_smul_left (I := I) (M := M) r j x,
    neg_one_smul, ContinuousLinearMap.neg_comp]
  rfl

omit [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem negDiffSlotAt_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ) (hδ : metricCauchySchwarzBound (I := I) g₀ h δ)
    (r : ℕ) (j : Fin r) (x : M) (W : TensorRSSpace 0 r I x) :
    tensorInnerPointwise g₀ 0 r x
        (TensorRSSpace.toModel W)
        (-TensorRSSpace.toModel (gInvDiffSlotAt (I := I) g₀ g₁ r j x W)) ≤
      (δ / (1 - δ)) * tensorInnerPointwise g₀ 0 r x
        (TensorRSSpace.toModel W) (TensorRSSpace.toModel W) := by
  have hslot := TensorMetric.tensorInnerPointwise_slot_insert_le (I := I) (M := M) g₀ r j x
    (-metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x)
    (negDiffEndo_adjoint (I := I) g₀ g₁ x)
    (fun v ↦ negDiffEndo_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x v)
    W
  rw [← negSlotAt_model (I := I) g₀ g₁ r j x W]
  exact hslot

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
