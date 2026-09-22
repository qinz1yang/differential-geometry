import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderLine
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.OrientedCylinderExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderScalarNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckDetection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderMetric

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel)}
  {F : PointedFlowData.{u, 0, 0} (I := ThreeModel) ancientTimeInterval}
  {subseq : ℕ → ℕ}

private local instance lineNeckSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem pointedAncientKappaLimit_normalized_cylinder_of_intrinsic_line
    (Phi : PointedRiemannianConvergenceMaps X (F.atTime 0) subseq)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (horient : ∀ k, TangentOrientationSection (X.obj k).M)
    (hscalar : ∀ k, metricScalarAt (X.obj k).metric (X.obj k).basepoint = 1)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {t₀ : ℝ} (ht₀ : t₀ ≤ 0) (γ : ℝ → F.M)
    (hline : ∀ s t : ℝ, riemannianEDistOf (F.S.family.metric t₀) (γ s) (γ t) =
      ENNReal.ofReal |s - t|)
    : ∃ (yStar : SpatialNeckSphere)
      (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, ThreeModel⟯ F.M),
      e (yStar, 0) = F.basepoint ∧
      ∀ t : ℝ, ∀ ht : t ≤ 0,
        Diffeomorph.pullbackMetricCross (F.S.family.metric t) e =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)) := by
  obtain ⟨A, htrivial | hantipodal⟩ :=
    ancientKappa_cylinder_branch_of_intrinsic_line F hF (by simp [ThreeSpace]) ht₀ γ hline
  · obtain ⟨d, hd⟩ := htrivial.1
    have hmetric : ∀ t : ℝ, t ≤ 0 → ∀ (y : SpatialNeckSphere) (s : ℝ)
        (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
        (F.S.family.metric t).inner (d (y, s))
          (mfderiv SpatialNeckCylinderModel ThreeModel d (y, s) (v, a))
          (mfderiv SpatialNeckCylinderModel ThreeModel d (y, s) (w, b)) =
          (2 * (A.extinctionTime - t)) *
            (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w + a * b := by
      have heq : (d : SpatialNeckCylinder → F.M) = A.projection := funext hd
      rw [heq]
      exact A.projection_metric
    have hbase : metricScalarAt (F.S.family.metric 0) F.basepoint = 1 :=
      pointedScalar_base_eq_of_metricCG_canonical_domains C hcanonical
        (fun k => hscalar (subseq k))
    obtain ⟨yStar, e, hmarked, _, hinner⟩ :=
      exists_marked_normalized_cylinder F.S.family.metric A.extinctionTime
        A.extinctionTime_pos d hmetric F.basepoint hbase
    refine ⟨yStar, e, hmarked, ?_⟩
    intro t ht
    apply SmoothRiemannianMetric.ext_inner
    rintro ⟨y, s⟩ v w
    change TangentSpace (𝓡 2) y × ℝ at v w
    rcases v with ⟨v, a⟩
    rcases w with ⟨w, b⟩
    exact (Diffeomorph.pullbackMetricCross_inner (F.S.family.metric t) e
      (y, s) (v, a) (w, b)).trans ((hinner t ht y s v w a b).trans
        (scalarOneShrinkingCylinderMetric_inner t (ht.trans_lt (by norm_num)) y s v w a b).symm)
  · obtain ⟨d, _⟩ := hantipodal.1
    exact (pointedLimit_not_antipodalProduct_diffeomorph Phi horient ⟨d⟩).elim

theorem pointedAncientKappaLimit_eventually_spatialNeckWitness_of_intrinsic_line
    (Phi : PointedRiemannianConvergenceMaps X (F.atTime 0) subseq)
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcomplete : ∀ k, MetricComplete (X.obj k))
    (horient : ∀ k, TangentOrientationSection (X.obj k).M)
    (hscalar : ∀ k, metricScalarAt (X.obj k).metric (X.obj k).basepoint = 1)
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {t₀ : ℝ} (ht₀ : t₀ ≤ 0) (γ : ℝ → F.M)
    (hline : ∀ s t : ℝ, riemannianEDistOf (F.S.family.metric t₀) (γ s) (γ t) =
      ENNReal.ofReal |s - t|)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (yStar : SpatialNeckSphere)
      (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, ThreeModel⟯ F.M),
      e (yStar, 0) = F.basepoint ∧
      Diffeomorph.pullbackMetricCross (F.S.family.metric 0) e = doubleSphereCylinderMetric ∧
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        ∃ W : SpatialNeckWitness (X.obj (subseq k)).metric yStar
            (X.obj (subseq k)).basepoint epsilon,
          ∀ x : spatialNeckBuffer epsilon,
            W.embedding x = Phi.map k
              (e (cylinderAxialScale (Real.sqrt 2) (by positivity)
                (x : SpatialNeckCylinder))) := by
  obtain ⟨yStar, e, hmarked, hmetric⟩ :=
    pointedAncientKappaLimit_normalized_cylinder_of_intrinsic_line Phi C hcanonical
      horient hscalar hF ht₀ γ hline
  have hpull := (hmetric 0 le_rfl).trans scalarOneShrinkingCylinderMetric_zero
  exact ⟨yStar, e, hmarked, hpull,
    pointedCylinderLimit_eventually_spatialNeckWitness Phi C hcanonical
      (by simp [ThreeSpace]) hcomplete hscalar yStar e hmarked hpull epsilon hepsilon⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
end
