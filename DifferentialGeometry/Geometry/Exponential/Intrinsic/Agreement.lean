import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic
import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import DifferentialGeometry.Geometry.Geodesic.Maximal.Uniqueness

noncomputable section

open Bundle Set Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

open Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem intrinsicGeodesic_initial
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) :
    IsGeodesicOnWithInitial (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm p v) univ p v := by
  let γ := intrinsicGeodesic (I := I) g hEnorm p v
  refine ⟨DifferentialGeometry.velocityLift (I := I) γ,
    DifferentialGeometry.velocityLift_proj (I := I) γ, ?_, ?_⟩
  · apply TotalSpace.ext (intrinsicGeodesic_zero (I := I) g hEnorm p v)
    exact heq_of_eq (intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v)
  · exact isMIntegralCurveOn_velocityLift (I := I) g isOpen_univ
      ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v).isGeodesicOn univ)
      (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn

theorem expDomain_eq_univ_of_completeSpace
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    expDomain (I := I) g p = univ := by
  classical
  apply eq_univ_of_forall
  intro v
  by_cases hdim : Module.finrank ℝ E = 0
  · have hsub : Subsingleton E := (Module.finrank_zero_iff (R := ℝ)).mp hdim
    have hv : v = 0 := @Subsingleton.elim E hsub v 0
    rw [hv]
    exact zero_mem_expDomain (I := I) g p
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact ⟨intrinsicGeodesic (I := I) g hEnorm p v, univ,
      isOpen_univ, isPreconnected_univ, mem_univ _, mem_univ _,
      intrinsicGeodesic_initial (I := I) g hEnorm p v⟩

theorem maximalGeodesic_eq_intrinsicGeodesic
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) :
    maximalGeodesic (I := I) g p v = intrinsicGeodesic (I := I) g hEnorm p v := by
  funext t
  exact maximalGeodesic_eqOn g isOpen_univ isPreconnected_univ (mem_univ _)
    (intrinsicGeodesic_initial (I := I) g hEnorm p v) (mem_univ t)

theorem expMap_eq_expMapIntrinsic
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (p : M) :
    expMap (I := I) g p = expMapIntrinsic (I := I) g hEnorm p := by
  funext v
  exact congrFun (maximalGeodesic_eq_intrinsicGeodesic (I := I) g hEnorm p v) 1

theorem radialCurve_eq_intrinsicGeodesic
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) :
    VolumeComparison.radialCurve (I := I) g p v =
      intrinsicGeodesic (I := I) g hEnorm p v := by
  funext t
  exact (expMap_smul (I := I) g p v t).trans
    (congrFun (maximalGeodesic_eq_intrinsicGeodesic (I := I) g hEnorm p v) t)

end DifferentialGeometry.Geometry.Riemannian.Exponential
