import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Geodesic.Minimizing.Line.Regularity
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.NormDiamond
import DifferentialGeometry.Geometry.Comparison.Distance.EndpointRate
import Mathlib.Topology.Separation.Connected

open Bundle Filter Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem IsMinimizingLine.inner_mfderiv_self_eq_one
    [I.Boundaryless] [T2Space M]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (t : ℝ) :
    g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 1 := by
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    hEnorm.isContinuousRiemannianBundle
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    intro hdim
    let _ : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).mp hdim
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    have heq := TotallyDisconnectedSpace.eq_of_continuous γ hγ.continuous 0 1
    have hd := hγ.edist_eq (s := 0) (t := 1) zero_le_one
    rw [heq, riemannianEDist_self] at hd
    norm_num at hd⟩
  have hspeed := riemannianEDistOf_div_tendsto_speed g γ t
    (hγ.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hlimit : Tendsto
      (fun h : ℝ => (riemannianEDistOf (I := I) g (γ (t + h)) (γ t)).toReal / h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hhpos : 0 < h := hh
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm,
      riemannianEDist_comm, hγ.edist_eq (by linarith),
      add_sub_cancel_left, ENNReal.toReal_ofReal hhpos.le, div_self (ne_of_gt hhpos)]
  have hsqrt := tendsto_nhds_unique hspeed hlimit
  rw [← Real.sq_sqrt (metric_inner_self_nonneg (I := I) g _ _), hsqrt, one_pow]

end DifferentialGeometry.Geometry.Riemannian
