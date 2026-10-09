import DifferentialGeometry.Geometry.Collapse.SmallFields
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections
import DifferentialGeometry.Geometry.Geodesic.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothAgreement
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

/-!
The same small model preserves edge-set distances and complete geodesics.
Minimizing directions use the actual finite exponential map and its smooth agreement.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Manifold Set Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓡 3

variable {M : Type u} [mM : MetricSpace M] [cM : ChartedSpace E3 M]
  [sM : IsManifold I3 ∞ M] (S : SmallManifoldModel (I := I3) M)

omit sM in
theorem smallModel_infDist_preimage (E : Set M) (x : S.Carrier) :
    letI _smallMetric := S.metricSpace
    Metric.infDist x (S.diffeo ⁻¹' E) = Metric.infDist (S.diffeo x) E := by
  let smallMetric := S.metricSpace
  have hset : S.diffeo '' (S.diffeo ⁻¹' E) = E :=
    image_preimage_eq E S.diffeo.surjective
  calc
    Metric.infDist x (S.diffeo ⁻¹' E) =
        Metric.infDist (S.diffeo x) (S.diffeo '' (S.diffeo ⁻¹' E)) :=
      (Metric.infDist_image S.isometryEquiv.isometry).symm
    _ = Metric.infDist (S.diffeo x) E := congrArg (Metric.infDist (S.diffeo x)) hset

theorem smallModel_gradient_add_inner (g : SmoothRiemannianMetric I3 M)
    (F : M → ℝ) (x : S.Carrier) (u : TangentSpace I3 x)
    (hF : MDifferentiableAt I3 𝓘(ℝ, ℝ) F (S.diffeo x)) :
    (S.metric g).inner x
      (Operator.gradFun (S.metric g) (F ∘ S.diffeo) x + u)
      (Operator.gradFun (S.metric g) (F ∘ S.diffeo) x + u) =
      g.inner (S.diffeo x)
        (Operator.gradFun g F (S.diffeo x) + mfderiv I3 I3 S.diffeo x u)
        (Operator.gradFun g F (S.diffeo x) + mfderiv I3 I3 S.diffeo x u) := by
  let d := S.diffeo.mfderivToContinuousLinearEquiv (by simp) x
  have hd : d (Operator.gradFun (S.metric g) (F ∘ S.diffeo) x) =
      Operator.gradFun g F (S.diffeo x) := by
    have hgrad : Operator.gradFun (S.metric g) (F ∘ S.diffeo) x =
        d.symm (Operator.gradFun g F (S.diffeo x)) :=
      Operator.gradientFun_pullbackCross g S.diffeo F x hF
    rw [hgrad]
    exact d.apply_symm_apply _
  rw [S.metric_inner]
  rw [← S.diffeo.mfderivToContinuousLinearEquiv_coe (by simp)]
  change g.inner (S.diffeo x) (d (_ + u)) (d (_ + u)) = _
  rw [map_add, hd]
  rfl

omit sM in
theorem smallModel_scalar_derivative (F : M → ℝ) (x : S.Carrier)
    (u : TangentSpace I3 x)
    (hF : MDifferentiableAt I3 𝓘(ℝ, ℝ) F (S.diffeo x)) :
    mvfderiv I3 (F ∘ S.diffeo) x u =
      mvfderiv I3 F (S.diffeo x) (mfderiv I3 I3 S.diffeo x u) :=
  mvfderiv_comp_apply x hF (S.diffeo.contMDiff.mdifferentiableAt (by simp)) u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [scM : SigmaCompactSpace M] [completeM : CompleteSpace M]
  [bundleM : RiemannianBundle (fun x : M => TangentSpace I3 x)]
  [riemM : IsRiemannianManifold I3 M]
  [continuousM : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace I3 x)]

local instance smallMetricEdge : MetricSpace S.Carrier := S.metricSpace

variable [bundleS : RiemannianBundle (fun x : S.Carrier => TangentSpace I3 x)]
  [riemS : IsRiemannianManifold I3 S.Carrier]
  [completeS : CompleteSpace S.Carrier]
  [continuousS : IsContinuousRiemannianBundle E3 (fun x : S.Carrier => TangentSpace I3 x)]

theorem smallModel_intrinsicGeodesic (g : SmoothRiemannianMetric I3 M)
    (hM : IsMetricNorm g) (hS : IsMetricNorm (S.metric g))
    (p : S.Carrier) (v : TangentSpace I3 p) (t : ℝ) :
    S.diffeo (intrinsicGeodesic (S.metric g) hS p v t) =
      intrinsicGeodesic g hM (S.diffeo p) (mfderiv I3 I3 S.diffeo p v) t := by
  let Γ := intrinsicGeodesic (S.metric g) hS p v
  have hsm : ContMDiff 𝓘(ℝ, ℝ) I3 ∞ Γ :=
    intrinsicGeodesic_contMDiff (S.metric g) hS p v
  have hgeo : IsGeodesic g (fun s => S.diffeo (Γ s)) :=
    geodesic_mapCross g S.diffeo Γ hsm
      (intrinsicGeodesic_isGeodesic (S.metric g) hS p v)
  have heq : (fun s => S.diffeo (Γ s)) =
      intrinsicGeodesic g hM (S.diffeo p) (mfderiv I3 I3 S.diffeo p v) := by
    apply isGeodesic_eq_of_initial g hgeo
      (intrinsicGeodesic_isGeodesic g hM _ _)
      (S.diffeo.continuous.comp (intrinsicGeodesic_continuous (S.metric g) hS p v))
      (intrinsicGeodesic_continuous g hM _ _)
    · simp only [Γ, intrinsicGeodesic_zero]
    · rw [intrinsicGeodesic_mfderiv_zero]
      have hc := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I3) (I'' := I3) (g := S.diffeo) (f := Γ) 0
        (S.diffeo.contMDiff.mdifferentiableAt (by simp))
        (hsm.mdifferentiableAt (by simp)) (1 : ℝ)
      change (mfderiv 𝓘(ℝ, ℝ) I3 (S.diffeo ∘ Γ) 0 1 : E3) =
        (mfderiv I3 I3 S.diffeo (Γ 0) (mfderiv 𝓘(ℝ, ℝ) I3 Γ 0 1) : E3) at hc
      have hzero : Γ 0 = p := intrinsicGeodesic_zero (S.metric g) hS p v
      have hvzero : (mfderiv 𝓘(ℝ, ℝ) I3 Γ 0 1 : E3) = v :=
        intrinsicGeodesic_mfderiv_zero (S.metric g) hS p v
      have hvmap := congrArg
        (fun w : E3 => (mfderiv I3 I3 S.diffeo (Γ 0) w : E3)) hvzero
      have hcfinal := hc.trans hvmap
      let D : S.Carrier → E3 → E3 := fun x w => mfderiv I3 I3 S.diffeo x w
      have hbase : D (Γ 0) = D p := congrArg D hzero
      exact hcfinal.trans (congrFun hbase v)
  exact congrFun heq t

theorem smallModel_minimizingDirection (g : SmoothRiemannianMetric I3 M)
    (hM : IsMetricNorm g) (hS : IsMetricNorm (S.metric g))
    (E : Set M) (p : S.Carrier) (v : TangentSpace I3 p)
    (hv : v ∈ (S.metric g).finiteMinimizingDirectionsTo (S.diffeo ⁻¹' E) p) :
    mfderiv I3 I3 S.diffeo p v ∈ g.finiteMinimizingDirectionsTo E (S.diffeo p) := by
  rcases hv with ⟨hunit, hend⟩
  refine ⟨?_, ?_⟩
  · rw [← S.metric_inner g]
    exact hunit
  · rw [ContMDiffRiemannianMetric.expMap_smul_eq_intrinsicGeodesic g hM]
    rw [← smallModel_infDist_preimage S E p]
    rw [← smallModel_intrinsicGeodesic S g hM hS p v]
    rw [ContMDiffRiemannianMetric.expMap_smul_eq_intrinsicGeodesic (S.metric g) hS] at hend
    exact hend

end DifferentialGeometry.Geometry.Collapse
