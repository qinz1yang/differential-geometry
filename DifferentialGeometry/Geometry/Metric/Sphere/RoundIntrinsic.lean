import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond
import DifferentialGeometry.Geometry.Metric.Sphere.GreatCircle
import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set Metric Module
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Geometry

open Riemannian.Exponential
open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

private instance sphereModel_neZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

omit [FiniteDimensional ℝ E] [NeZero n] in
theorem dIncl_orth (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    ⟪(p : E), dIncl (n := n) p v⟫ = 0 := by
  rw [real_inner_comm]
  apply Submodule.inner_left_of_mem_orthogonal
    (Submodule.mem_span_singleton_self (p : E))
  rw [← range_mfderiv_coe_sphere (n := n) p]
  exact ⟨v, rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable
  [RiemannianBundle
    (fun p : sphere (0 : E) 1 => TangentSpace (𝓡 n) p)]
  [PseudoEMetricSpace (sphere (0 : E) 1)]
  [@CompleteSpace (sphere (0 : E) 1)
    (@PseudoEMetricSpace.toUniformSpace _ ‹PseudoEMetricSpace (sphere (0 : E) 1)›)]
  [IsRiemannianManifold (𝓡 n) (sphere (0 : E) 1)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
    (fun p : sphere (0 : E) 1 => TangentSpace (𝓡 n) p)]

theorem intrinsic_eq_gc
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p)
    (hv : ‖dIncl (n := n) p v‖ = 1) (t : ℝ) :
    intrinsicGeodesic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p v t =
      greatCircle p (dIncl (n := n) p v) hv (dIncl_orth p v) t := by
  let γi :=
    intrinsicGeodesic (I := 𝓡 n) (roundMetric (E := E) (n := n))
      hEnorm p v
  let γc := greatCircle p (dIncl (n := n) p v) hv (dIncl_orth p v)
  have hgc :
      IsGeodesic (I := 𝓡 n) (roundMetric (E := E) (n := n)) γc := by
    intro s
    exact greatCircle_geodesic (n := n) p (dIncl (n := n) p v)
      hv (dIncl_orth p v) s
  have heq : Set.EqOn γi γc Set.univ := by
    apply geo_eqOn_of_init (I := 𝓡 n) (roundMetric (E := E) (n := n))
      isOpen_univ isPreconnected_univ (Set.mem_univ 0)
    · exact
        (intrinsicGeodesic_isGeodesic (I := 𝓡 n)
          (roundMetric (E := E) (n := n)) hEnorm p v).isGeodesicOn Set.univ
    · exact hgc.isGeodesicOn Set.univ
    · exact
        (intrinsicGeodesic_continuous (I := 𝓡 n)
          (roundMetric (E := E) (n := n)) hEnorm p v).continuousOn
    · exact
        (greatCircle_smooth (n := n) p (dIncl (n := n) p v)
          hv (dIncl_orth p v)).continuous.continuousOn
    · simp [γi, γc]
    · dsimp only [γi, γc]
      rw [intrinsicGeodesic_mfderiv_zero]
      apply mfderiv_coe_sphere_injective p
      have hvel :=
        greatCircle_vel (n := n) p (dIncl (n := n) p v)
          hv (dIncl_orth p v) 0
      rw [greatCircle_zero] at hvel
      simpa only [Real.sin_zero, neg_zero, zero_smul, Real.cos_zero, one_smul,
        zero_add] using hvel.symm
  exact heq (Set.mem_univ t)

theorem round_exp_radial
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p)
    (hv : ‖dIncl (n := n) p v‖ = 1) (r : ℝ) :
    expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (r • v) =
      greatCircle p (dIncl (n := n) p v) hv (dIncl_orth p v) r := by
  rw [expMapIntrinsic_def, intrinsicGeodesic_smul]
  exact intrinsic_eq_gc hEnorm p v hv r

theorem round_exp_val
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm (I := 𝓡 n) (M := sphere
      (0 : E) 1) (roundMetric (E := E) (n := n)))
    (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p)
    (hv : ‖dIncl (n := n) p v‖ = 1) (r : ℝ) :
    ((expMapIntrinsic (I := 𝓡 n) (roundMetric (E := E) (n := n))
        hEnorm p (r • v) : sphere (0 : E) 1) : E) =
      Real.cos r • (p : E) + Real.sin r • dIncl (n := n) p v := by
  rw [round_exp_radial hEnorm p v hv r, greatCircle_val]

end Geometry
end DifferentialGeometry
