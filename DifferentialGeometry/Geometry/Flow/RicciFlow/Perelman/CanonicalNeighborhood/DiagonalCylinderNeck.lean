import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderCoverPositiveEnd
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderCoverScalarNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonReflexive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance sphereTwoDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem localPullMetric_shrinkingCylinderCover_projection_translate
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (C : ShrinkingCylinderCover P) (hbase : PointedFlowScalarAtBase P 1)
    (R t : ℝ) (ht : t ≤ 0) :
    localPullMetric (P.S.base.metric t) (C.projection ∘ cylinderLineTranslation R)
      (isLocalDiffeomorph_comp C.projection_local
        (cylinderLineTranslation R).isLocalDiffeomorph) = cylinderReferenceMetric t := by
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  rcases y with ⟨x, s⟩
  rcases v with ⟨v, a⟩
  rcases w with ⟨w, b⟩
  apply (localPullMetric_inner (P.S.base.metric t)
    (C.projection ∘ cylinderLineTranslation R) _ (x, s) (v, a) (w, b)).trans
  apply (C.projection_translate_metric R t ht x s v w a b).trans
  rw [C.extinctionTime_eq_one_of_scalar_at_base_one hbase]
  change 2 * (1 - t) * inner ℝ
    (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) x v)
    (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) x w) + a * b = _
  exact (cylinderReferenceMetric_inner t ht (x, s) (v, a) (w, b)).symm

private def spatialNeckOfNormalizedCylinderProjection
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (C : ShrinkingCylinderCover P) (hT : C.extinctionTime = 1)
    (p : Sphere 2) (R : ℝ)
    (Phi : PartialDiffeomorph IC I3 Cylinder P.M ∞)
    (hPhi : (Phi : Cylinder → P.M) = C.projection ∘ cylinderLineTranslation R)
    (hsource : Phi.source = Set.univ ×ˢ Set.Ioi (-R))
    (hscalar : metricScalarAt (P.S.base.metric 0) (C.projection (p, R)) = 1)
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hR : eps⁻¹ ≤ R) :
    SpatialNeck (P.S.base.metric 0) eps (C.projection (p, R)) := by
  have hcenter : Phi (p, 0) = C.projection (p, R) := by
    rw [hPhi]
    change C.projection (p, 0 + R) = C.projection (p, R)
    rw [zero_add]
  have hderiv (x : Sphere 2) (s : ℝ) (v : TangentSpace I2 x) (a : ℝ) :
      mfderiv IC I3 Phi (x, s) (v, a) =
        mfderiv IC I3 C.projection (x, s + R) (v, a) := by
    rw [hPhi]
    have h := mfderiv_comp_apply (x, s)
      (C.projection_local.mdifferentiable (by decide) (cylinderLineTranslation R (x, s)))
      ((cylinderLineTranslation R).mdifferentiable (by decide) (x, s)) (v, a)
    rw [mfderiv_cylinderLineTranslation, cylinderLineTranslation_apply] at h
    exact h
  have hmetric (y : Cylinder) (v w : TangentSpace IC y) :
      (P.S.base.metric 0).inner (Phi y)
        (mfderiv IC I3 Phi y v) (mfderiv IC I3 Phi y w) =
          (cylinderReferenceMetric 0).inner y v w := by
    rcases y with ⟨x, s⟩
    rcases v with ⟨v, a⟩
    rcases w with ⟨w, b⟩
    rw [hderiv x s v a, hderiv x s w b, hPhi]
    change (P.S.base.metric 0).inner (C.projection (x, s + R))
      (mfderiv IC I3 C.projection (x, s + R) (v, a))
      (mfderiv IC I3 C.projection (x, s + R) (w, b)) = _
    apply (C.projection_metric 0 le_rfl x (s + R) v w a b).trans
    rw [hT]
    change 2 * (1 - 0) * inner ℝ
      (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) x v)
      (show ThreeSpace from mfderiv I2 I3 (fun z : Sphere 2 => (z : ThreeSpace)) x w) + a * b = _
    simpa only [sub_zero, mul_one] using
      (cylinderReferenceMetric_zero_inner (x, s) (v, a) (w, b)).symm
  have hQ : 0 < metricScalarAt (P.S.base.metric 0) (C.projection (p, R)) := by
    rw [hscalar]
    norm_num
  have hg : scaleMetric (metricScalarAt (P.S.base.metric 0) (C.projection (p, R)))
      hQ (P.S.base.metric 0) = P.S.base.metric 0 := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [scaleMetric_inner, hscalar, one_mul]
  refine {
    eps_pos := heps
    eps_small := hsmall
    Q_pos := hQ
    cylinder := cylinderReference
    map := Phi
    center := p
    center_eq := hcenter
    domain := ?_
    comparison := {
      pullback := fun _ => metricTensorField (cylinderReferenceMetric 0)
      pullback_eq := ?_
      jet := fun _ _ => 0
      jet_zero := ?_
      jet_succ := ?_
      equivalence := ?_
      close := ?_ } }
  · intro y hy
    rw [hsource]
    exact ⟨Set.mem_univ _, lt_of_le_of_lt (neg_le_neg hR) hy.2.1⟩
  · intro s y hy v
    rw [metricTensorField_apply, hg]
    exact (hmetric y (v 0) (v 1)).symm
  · intro s y v
    simp [metricTensorField_apply, cylinderReference]
  · intro b s hs y hy v
    simp
  · intro s hs y hy v
    have hnn := inner_self_nonneg (cylinderReferenceMetric 0) y v
    simp only [metricTensorField_apply, cylinderReference]
    constructor <;> nlinarith
  · intro a b hab s hs y hy
    have hz : tensor02CovDerivNormWith (I := IC) a 0
        (cylinderReferenceMetric 0) (cylinderReferenceMetric 0) y = 0 := by
      rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
        covDerivOfField_zero_tensor]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
        MetricFiberData.inner, map_zero, Real.sqrt_zero]
    exact hz.le.trans heps.le

theorem exists_spatialNeck_of_shrinkingCylinderCover_diagonalModel_at
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (C : ShrinkingCylinderCover P) (hmodel : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1)
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (p : Sphere 2) (R : ℝ) (hR : eps⁻¹ ≤ R) :
    ∃ N : SpatialNeck (P.S.base.metric 0) eps (C.projection (p, R)),
      N.center = p ∧ N.map.source = Set.univ ×ˢ Set.Ioi (-R) ∧
      (N.map : Cylinder → P.M) = C.projection ∘ cylinderLineTranslation R := by
  obtain ⟨Phi, hsource, _, hPhi⟩ :=
    C.exists_partialDiffeomorph_projection_translate_of_diagonalModel hmodel R
  exact ⟨spatialNeckOfNormalizedCylinderProjection P C
    (C.extinctionTime_eq_one_of_scalar_at_base_one hbase) p R Phi hPhi hsource
    (C.metricScalarAt_zero_eq_one_of_scalar_at_base_one hbase _) heps hsmall hR,
    rfl, hsource, hPhi⟩

theorem exists_spatialNeck_of_shrinkingCylinderCover_diagonalModel
    (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (C : ShrinkingCylinderCover P) (hmodel : C.DiagonalModel)
    (hbase : PointedFlowScalarAtBase P 1)
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ p : P.M, Nonempty (SpatialNeck (P.S.base.metric 0) eps p) := by
  obtain ⟨N, _⟩ := exists_spatialNeck_of_shrinkingCylinderCover_diagonalModel_at
    P C hmodel hbase heps hsmall (sphereEquator 0) (eps⁻¹ + 1) (by linarith)
  exact ⟨_, ⟨N⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
