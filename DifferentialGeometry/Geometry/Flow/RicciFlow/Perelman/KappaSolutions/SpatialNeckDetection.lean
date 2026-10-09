import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAxialNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricJetScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedDomainMetricConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalMetricCompactness
open scoped ContDiff Manifold _root_.Topology

universe u uE uH

private local instance neckDetectionSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

private local instance neckDetectionLimitTopology : TopologicalSpace L.M := L.topology
private local instance neckDetectionLimitCharted : ChartedSpace H L.M := L.charted
private local instance neckDetectionLimitSmooth : IsManifold I ∞ L.M := L.smooth
private local instance neckDetectionLimitT2 : T2Space L.M := L.t2
private local instance neckDetectionLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

private local instance neckDetectionApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
private local instance neckDetectionApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
private local instance neckDetectionApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
private local instance neckDetectionApproxC1 (k : ℕ) :
    IsManifold I 1 (X.obj k).M := IsManifold.of_le (n := ∞) (by decide)
private local instance neckDetectionApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
private local instance neckDetectionApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem neckDetection_normalized_reference
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I⟯ L.M)
    (hmetric : Diffeomorph.pullbackMetricCross L.metric e = doubleSphereCylinderMetric) :
    scaleMetric (1 / 2) (by norm_num)
        (Diffeomorph.pullbackMetricCross L.metric
          ((cylinderAxialScale (Real.sqrt 2) (by positivity)).trans e)) =
      unitCylinderMetric := by
  let Psi := cylinderAxialScale (Real.sqrt 2) (by positivity)
  have hcomp : Diffeomorph.pullbackMetric
        (Diffeomorph.pullbackMetricCross L.metric e) Psi =
      Diffeomorph.pullbackMetricCross L.metric (Psi.trans e) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetric_inner, Diffeomorph.pullbackMetricCross_inner,
      Diffeomorph.pullbackMetricCross_inner]
    have hd (a : TangentSpace SpatialNeckCylinderModel x) :
        mfderiv SpatialNeckCylinderModel I (Psi.trans e) x a =
          mfderiv SpatialNeckCylinderModel I e (Psi x)
            (mfderiv SpatialNeckCylinderModel SpatialNeckCylinderModel Psi x a) :=
      mfderiv_comp_apply x (e.mdifferentiable (by decide) (Psi x))
        (Psi.mdifferentiable (by decide) x) a
    rw [hd, hd]
    rfl
  rw [← hcomp, hmetric]
  exact cylinderAxialScale_normalized_doubleSphereCylinderMetric

theorem pointedCylinderLimit_eventually_spatialNeckWitness
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k : ℕ, C.domain k = canonicalSourceData Phi k)
    (hdimension : Module.finrank ℝ E = 3)
    (hcomplete : ∀ k : ℕ, MetricComplete (X.obj k))
    (hscalar : ∀ k : ℕ, metricScalarAt (I := I) (X.obj k).metric (X.obj k).basepoint = 1)
    (yStar : SpatialNeckSphere)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I⟯ L.M)
    (hmarked : e (yStar, 0) = L.basepoint)
    (hmetric : Diffeomorph.pullbackMetricCross L.metric e = doubleSphereCylinderMetric)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ W : SpatialNeckWitness (X.obj (subseq k)).metric yStar
          (X.obj (subseq k)).basepoint epsilon,
        ∀ x : spatialNeckBuffer epsilon,
          W.embedding x = Phi.map k
            (e (cylinderAxialScale (Real.sqrt 2) (by positivity) (x : SpatialNeckCylinder))) := by
  let Psi := cylinderAxialScale (Real.sqrt 2) (by positivity)
  let e' := Psi.trans e
  let U := spatialNeckBuffer epsilon
  let Kbuffer : Set SpatialNeckCylinder :=
    (univ : Set SpatialNeckSphere) ×ˢ Icc (-epsilon⁻¹ - 1) (epsilon⁻¹ + 1)
  have hbuffer : IsCompact Kbuffer := isCompact_univ.prod isCompact_Icc
  have hUbuffer : (U : Set SpatialNeckCylinder) ⊆ Kbuffer := by
    intro x hx
    exact ⟨mem_univ _, hx.1.le, hx.2.le⟩
  let p := Nat.ceil epsilon⁻¹
  let A := metricJetScaleLoss (1 / 2) p
  have hA : 0 < A := metricJetScaleLoss_pos (1 / 2) p
  let gRef := (Diffeomorph.pullbackMetricCross L.metric e').restrictOpen
    (I := SpatialNeckCylinderModel) U
  have hreference : scaleMetric (1 / 2) (by norm_num) gRef =
      unitCylinderMetric.restrictOpen (I := SpatialNeckCylinderModel) U := by
    have hglobal := neckDetection_normalized_reference e hmetric
    have hrestrict : scaleMetric (1 / 2) (by norm_num) gRef =
        (scaleMetric (1 / 2) (by norm_num)
          (Diffeomorph.pullbackMetricCross L.metric e')).restrictOpen
            (I := SpatialNeckCylinderModel) U := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rfl
    rw [hrestrict, hglobal]
  obtain ⟨k0, hk0⟩ := pointedMaps_eventually_fixedDomain_metric_close Phi C hcanonical e' U
    Kbuffer hbuffer hUbuffer (spatialNeckClosedCore epsilon)
    (spatialNeckClosedCore_isCompact epsilon) p (epsilon / A) (div_pos hepsilon hA)
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨f, hf, hfmap, hclose⟩ := hk0 k hk
  have hR : 0 < metricScalarAt (I := I) (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint := by rw [hscalar]; norm_num
  have hfmarked : f (spatialNeckCentralPoint epsilon hepsilon yStar) =
      (X.obj (subseq k)).basepoint := by
    rw [hfmap]
    change Phi.map k (e (Psi (yStar, 0))) = _
    rw [cylinderAxialScale_central, hmarked]
    exact Phi.basepoint_map k
  let gk := immersionInducedMetric (X.obj (subseq k)).metric hf.isImmersion
  have hnormalized : spatialNeckNormalizedMetric (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint hR hf = scaleMetric (1 / 2) (by norm_num) gk := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [spatialNeckNormalizedMetric_inner, spatialNeckScale_inv_sq _ _ hR, hscalar,
      scaleMetric_inner, immersionInducedMetric_inner]
  have hscaled : metricDerivNormSupOn (I := SpatialNeckCylinderModel)
      (spatialNeckClosedCore epsilon) p
      (scaleMetric (1 / 2) (by norm_num) gk)
      (scaleMetric (1 / 2) (by norm_num) gRef)
      (scaleMetric (1 / 2) (by norm_num) gRef) < epsilon := by
    calc
      _ ≤ A * metricDerivNormSupOn (I := SpatialNeckCylinderModel)
          (spatialNeckClosedCore epsilon) p gk gRef gRef :=
        metricDerivNormSupOn_scale_all_le (1 / 2) (by norm_num)
          (spatialNeckClosedCore_isCompact epsilon) p gk gRef gRef
      _ < A * (epsilon / A) := mul_lt_mul_of_pos_left hclose hA
      _ = epsilon := by field_simp [hA.ne']
  have hneckclose : metricDerivNormSupOn (I := SpatialNeckCylinderModel)
      (spatialNeckClosedCore epsilon) (Nat.ceil epsilon⁻¹)
      (spatialNeckNormalizedMetric (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint hR hf)
      (unitCylinderMetric.restrictOpen U) (unitCylinderMetric.restrictOpen U) < epsilon := by
    simpa only [hnormalized, hreference] using hscaled
  let W := SpatialNeckWitness.ofEmbedding (X.obj (subseq k)).metric yStar
    (X.obj (subseq k)).basepoint epsilon hdimension ⟨hcomplete (subseq k)⟩
    hepsilon hR f hf hfmarked hneckclose
  exact ⟨W, hfmap⟩

theorem pointedCylinderLimit_eventually_isSpatialNeckCenter
    (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k : ℕ, C.domain k = canonicalSourceData Phi k)
    (hdimension : Module.finrank ℝ E = 3)
    (hcomplete : ∀ k : ℕ, MetricComplete (X.obj k))
    (hscalar : ∀ k : ℕ, metricScalarAt (I := I) (X.obj k).metric (X.obj k).basepoint = 1)
    (yStar : SpatialNeckSphere)
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I⟯ L.M)
    (hmarked : e (yStar, 0) = L.basepoint)
    (hmetric : Diffeomorph.pullbackMetricCross L.metric e = doubleSphereCylinderMetric)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      IsSpatialNeckCenter (X.obj (subseq k)).metric yStar
        (X.obj (subseq k)).basepoint epsilon := by
  obtain ⟨k0, hk0⟩ := pointedCylinderLimit_eventually_spatialNeckWitness
    Phi C hcanonical hdimension hcomplete hscalar yStar e hmarked hmetric epsilon hepsilon
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨W, _⟩ := hk0 k hk
  exact ⟨W⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
