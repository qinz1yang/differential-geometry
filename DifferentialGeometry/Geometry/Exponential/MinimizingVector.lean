import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

open Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

theorem tendsto_minimizingVec_of_unique
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {p q : M} {u : TangentSpace I p}
    (huniq : ∀ v : TangentSpace I p,
      expMapIntrinsic g hEnorm p v = q →
      Real.sqrt (g.inner p v v) = (riemannianEDist I p q).toReal → v = u) :
    Tendsto (minimizingVec g hEnorm p) (𝓝 q) (𝓝 u) := by
  let d : M → ℝ := fun z => (riemannianEDist I p z).toReal
  have hd : Continuous d := by
    have hed : Continuous (fun z : M => riemannianEDist I p z) :=
      (continuous_riemannianEDist_to (I := I) p).congr
        (fun _ => Manifold.riemannianEDist_comm)
    exact continuousOn_univ.mp (ENNReal.continuousOn_toReal.comp'
      hed.continuousOn (fun z _ => riemannianEDist_ne_top (I := I) p z))
  have hbound : ∀ᶠ z in 𝓝 q, d z < d q + 1 :=
    hd.continuousAt (Iio_mem_nhds (lt_add_one _))
  apply (gLenBall_isCompact g p (d q + 1)).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [hbound] with z hz
    change Real.sqrt (g.inner p (minimizingVec g hEnorm p z)
      (minimizingVec g hEnorm p z)) ≤ d q + 1
    rw [minimizingVec_len]
    exact hz.le
  · intro v _ hv
    apply huniq v
    · have hc := hv.continuousAt_comp
        (expMapIntrinsic_continuous g hEnorm p).continuousAt
      have heq : (expMapIntrinsic g hEnorm p) ∘ (minimizingVec g hEnorm p) = id :=
        funext (minimizingVec_exp g hEnorm p)
      rw [heq] at hc
      exact eq_of_nhds_neBot hc
    · have hc := hv.continuousAt_comp (continuous_sqrt_gInner_self g p).continuousAt
      have heq : (fun v : TangentSpace I p => Real.sqrt (g.inner p v v)) ∘
          (minimizingVec g hEnorm p) = d :=
        funext (minimizingVec_len g hEnorm p)
      rw [heq] at hc
      exact eq_of_nhds_neBot (hc.clusterPt.mono hd.continuousAt)

end DifferentialGeometry.Geometry.Riemannian
