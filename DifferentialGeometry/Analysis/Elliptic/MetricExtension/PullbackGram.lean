import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients

noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [T2Space M] in
private theorem chartBasisVecFiber_eq_chartInverse_mfderiv
    (α : M) {y : EuclN}
    (hy : y ∈ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) α i
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      mfderiv 𝓘(ℝ, EuclN) I
        (fun z => (extChartAt I α).symm ((toEuclidean (E := E)).symm z)) y
        (EuclideanSpace.single i 1) := by
  let z := (toEuclidean (E := E)).symm y
  have hz : z ∈ interior (extChartAt I α).target := by
    rcases hy with ⟨z', hz', rfl⟩
    simpa only [z, ContinuousLinearEquiv.symm_apply_apply] using hz'
  have htarget : (extChartAt I α).target ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hz
  have hrange : Set.range I ∈ 𝓝 z :=
    mem_of_superset htarget (extChartAt_target_subset_range α)
  have hinv : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm z :=
    (mdifferentiableWithinAt_extChartAt_symm (interior_subset hz)).mdifferentiableAt hrange
  have hlin : MDifferentiableAt 𝓘(ℝ, EuclN) 𝓘(ℝ, E)
      (toEuclidean (E := E)).symm y :=
    (mdifferentiableAt_iff_differentiableAt.mpr (toEuclidean (E := E)).symm.differentiableAt)
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, EuclN)) (I' := 𝓘(ℝ, E))
    (I'' := I) y hinv hlin
  have hsource : (extChartAt I α).symm z ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target (interior_subset hz)
  rw [chartBasisVecFiber, TangentBundle.symmL_trivializationAt hsource,
    (extChartAt I α).right_inv (interior_subset hz), mfderivWithin_of_mem_nhds hrange,
    chartModelBasis_apply]
  have hlinD : mfderiv 𝓘(ℝ, EuclN) 𝓘(ℝ, E)
      (toEuclidean (E := E)).symm y =
      (toEuclidean (E := E)).symm.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    exact (toEuclidean (E := E)).symm.fderiv
  have heval := congrArg
    (fun L : EuclN →L[ℝ] TangentSpace I ((extChartAt I α).symm z) =>
      L (EuclideanSpace.single i 1)) hcomp
  have hlinear := congrArg (fun L : EuclN →L[ℝ] E => L (EuclideanSpace.single i 1)) hlinD
  exact (congrArg (fun v : E => mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm z v)
    hlinear).symm.trans heval.symm

theorem gramOnEuclid_pullback
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : ContMDiff I J ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv I J f x))
    (α : M) {y : EuclN}
    (hy : y ∈ toEuclidean (E := E) '' interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    gramOnEuclid (I := I) (g.pullback f hf himm) α i j y =
      pullbackMetricCoefficients g
        (fun z => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  let c : EuclN → M := fun z =>
    (extChartAt I α).symm ((toEuclidean (E := E)).symm z)
  have hz : (toEuclidean (E := E)).symm y ∈ interior (extChartAt I α).target := by
    rcases hy with ⟨z, hz, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hz
  have ht : (extChartAt I α).target ∈ 𝓝 ((toEuclidean (E := E)).symm y) :=
    mem_interior_iff_mem_nhds.mp hz
  have hrange : Set.range I ∈ 𝓝 ((toEuclidean (E := E)).symm y) :=
    mem_of_superset ht (extChartAt_target_subset_range α)
  have hc : MDifferentiableAt 𝓘(ℝ, EuclN) I c y :=
    ((mdifferentiableWithinAt_extChartAt_symm (interior_subset hz)).mdifferentiableAt hrange).comp y
      ((mdifferentiableAt_iff_differentiableAt.mpr (toEuclidean (E := E)).symm.differentiableAt))
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, EuclN)) (I' := I) (I'' := J) y
    (hf.mdifferentiableAt (by simp)) hc
  rw [gramOnEuclid, chartGramMatrix_apply, SmoothRiemannianMetric.pullback_inner,
    chartBasisVecFiber_eq_chartInverse_mfderiv α hy i,
    chartBasisVecFiber_eq_chartInverse_mfderiv α hy j,
    pullbackMetricCoefficients_apply]
  have heval (k : Fin (Module.finrank ℝ E)) := congrArg
    (fun L : EuclN →L[ℝ] TangentSpace J (f (c y)) => L (EuclideanSpace.single k 1)) hcomp
  exact congrArg₂ (fun v w => g.inner (f (c y)) v w) (heval i).symm (heval j).symm

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
