import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylindricalComparisonRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderScalarFromConnection


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.DifferentialGeometry.Manifold Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

private local instance asymptoticCylinderSourceC1
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) : IsManifold I3 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance asymptoticCylinderLimitC1
    (L : PointedRiemannianManifold.{u, 0, 0} (I := I3)) : IsManifold I3 1 L.M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance asymptoticCylinderBufferSigma (epsilon : ℝ) :
    SigmaCompactSpace (spatialNeckBuffer epsilon) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen SpatialNeckCylinderModel (spatialNeckBuffer epsilon).isOpen)


theorem backwardCylinderLimit_eventually_strongNeckWitness
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I3) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I3) Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (hscalar : metricScalarAt L.metric L.basepoint = 1)
    (h : ℝ → SmoothRiemannianMetric I3 L.M)
    (hconvergence : ∀ K : Set L.M, IsCompact K → ∀ order : ℕ, ∀ eta : ℝ, 0 < eta →
      ∀ᶠ i in atTop, Nonempty (MetricComparisonOn h
        (backwardScaledMetric F.S (tau (phi i)) (htau (phi i))) (Phi.map i) K
        (Icc (1 : ℝ) 3) order eta))
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (yStar : SpatialNeckSphere) (hmarked : e (yStar, 0) = L.basepoint)
    (hmetric : ∀ theta : ℝ, ∀ htheta : theta ∈ Icc (1 : ℝ) 3,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross (h theta) e =
        scalarOneShrinkingCylinderMetric (1 - theta)
          (sub_lt_self 1 (lt_of_lt_of_le zero_lt_one htheta.1)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    ∀ᶠ i in atTop,
      ∃ W : StrongNeckWitness F.S yStar (q (phi i)) (-tau (phi i)) epsilon,
        ∀ x : spatialNeckBuffer epsilon, W.embedding x = Phi.map i (e (x : SpatialNeckCylinder)) := by
  let U := spatialNeckBuffer epsilon
  let Kbuffer : Set SpatialNeckCylinder :=
    (univ : Set SpatialNeckSphere) ×ˢ Icc (-epsilon⁻¹ - 1) (epsilon⁻¹ + 1)
  have hbuffer : IsCompact Kbuffer := isCompact_univ.prod isCompact_Icc
  have hUbuffer : (U : Set SpatialNeckCylinder) ⊆ Kbuffer := by
    intro x hx
    exact ⟨mem_univ _, hx.1.le, hx.2.le⟩
  have hcompact : IsCompact (e '' Kbuffer) := hbuffer.image e.continuous
  obtain ⟨i0, hi0⟩ := Phi.source_subset hcompact
  have hsource : ∀ᶠ i in atTop, e '' Kbuffer ⊆ Phi.source i :=
    eventually_atTop.2 ⟨i0, hi0⟩
  have hlocalMetric (theta : ℝ) (htheta : theta ∈ Icc (1 : ℝ) 3) :
      strongNeckBackgroundMetric epsilon (1 - theta) =
        (DifferentialGeometry.Diffeomorph.pullbackMetricCross (h theta) e).restrictOpen U := by
    rw [strongNeckBackgroundMetric_of_nonpos epsilon (1 - theta) (sub_nonpos.mpr htheta.1),
      hmetric theta htheta]
  apply canonicalBackwardMetricComparisons_eventually_strongNeckWitness F tau htau q Phi C
    hcanonical hscalar e yStar hmarked epsilon hepsilon hepsilon_one
  intro eta heta
  filter_upwards [hsource, hconvergence (e '' Kbuffer) hcompact (Nat.ceil epsilon⁻¹) eta heta]
    with i hsource_i hcomparison_i
  obtain ⟨B⟩ := hcomparison_i
  exact ⟨backwardMetricComparisonCylindricalRestriction F tau htau q Phi e epsilon i B
    ((image_mono hUbuffer).trans hsource_i)
    (fun x => ⟨x, hUbuffer x.property, rfl⟩) hlocalMetric⟩


theorem asymptoticCylinder_eventually_isStrongNeckCenter
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I3) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I3) Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (h : ℝ → SmoothRiemannianMetric I3 L.M) (htimeOne : h 1 = L.metric)
    (hconvergence : ∀ K : Set L.M, IsCompact K → ∀ order : ℕ, ∀ eta : ℝ, 0 < eta →
      ∀ᶠ i in atTop, Nonempty (MetricComparisonOn h
        (backwardScaledMetric F.S (tau (phi i)) (htau (phi i))) (Phi.map i) K
        (Icc (1 : ℝ) 3) order eta))
    (e : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (yStar : SpatialNeckSphere) (hmarked : e (yStar, 0) = L.basepoint)
    (hmetric : ∀ theta : ℝ, ∀ htheta : theta ∈ Icc (1 : ℝ) 3,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross (h theta) e =
        scalarOneShrinkingCylinderMetric (1 - theta)
          (sub_lt_self 1 (lt_of_lt_of_le zero_lt_one htheta.1)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_one : epsilon < 1) :
    ∀ᶠ i in atTop, IsStrongNeckCenter F.S yStar (q (phi i)) (-tau (phi i)) epsilon := by
  have hzero : DifferentialGeometry.Diffeomorph.pullbackMetricCross L.metric e =
      doubleSphereCylinderMetric := by
    simpa only [htimeOne, sub_self, scalarOneShrinkingCylinderMetric_zero] using
      hmetric 1 (by norm_num)
  have hscalar : metricScalarAt L.metric L.basepoint = 1 := by
    have hcross := metricScalar_cross L.metric e (yStar, 0)
    rw [hzero, hmarked, doubleSphereCylinderMetric_scalar_native] at hcross
    exact hcross.symm
  filter_upwards [backwardCylinderLimit_eventually_strongNeckWitness F tau htau q Phi C
    hcanonical hscalar h hconvergence e yStar hmarked hmetric epsilon hepsilon hepsilon_one]
    with i hi
  exact ⟨hi.choose⟩


theorem cylindricalAsymptoticLimit_eventually_strongNecks
    (F : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    {L : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedRiemannianConvergenceMaps (I := I3) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I3) Phi)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Phi i)
    (h : ℝ → SmoothRiemannianMetric I3 L.M) (htimeOne : h 1 = L.metric)
    (hconvergence : ∀ K : Set L.M, IsCompact K → ∀ order : ℕ, ∀ eta : ℝ, 0 < eta →
      ∀ᶠ i in atTop, Nonempty (MetricComparisonOn h
        (backwardScaledMetric F.S (tau (phi i)) (htau (phi i))) (Phi.map i) K
        (Icc (1 : ℝ) 3) order eta))
    (d : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, I3⟯ L.M)
    (hmetric : ∀ theta : ℝ, ∀ htheta : theta ∈ Icc (1 : ℝ) 3,
      DifferentialGeometry.Diffeomorph.pullbackMetricCross (h theta) d =
        scalarOneShrinkingCylinderMetric (1 - theta)
          (sub_lt_self 1 (lt_of_lt_of_le zero_lt_one htheta.1))) :
    ∃ yStar : SpatialNeckSphere, ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∀ᶠ i in atTop, IsStrongNeckCenter F.S yStar (q (phi i)) (-tau (phi i)) epsilon := by
  let pStar := d.symm L.basepoint
  let e := (cylinderLineTranslation pStar.2).trans d
  have hmarked : e (pStar.1, 0) = L.basepoint := by
    change d (pStar.1, (0 : ℝ) + pStar.2) = L.basepoint
    rw [zero_add]
    exact d.apply_symm_apply L.basepoint
  have hd (y : SpatialNeckSphere) (z : ℝ) (v : TangentSpace (𝓡 2) y) (a : ℝ) :
      mfderiv SpatialNeckCylinderModel I3 e (y, z) (v, a) =
        mfderiv SpatialNeckCylinderModel I3 d (y, z + pStar.2) (v, a) := by
    change mfderiv SpatialNeckCylinderModel I3
      ((d : SpatialNeckCylinder → L.M) ∘ cylinderLineTranslation pStar.2) (y, z) (v, a) = _
    have hcomp := mfderiv_comp_apply (y, z)
      (d.mdifferentiable (by decide) (cylinderLineTranslation pStar.2 (y, z)))
      ((cylinderLineTranslation pStar.2).mdifferentiable (by decide) (y, z)) (v, a)
    rw [mfderiv_cylinderLineTranslation, cylinderLineTranslation_apply] at hcomp
    exact hcomp
  have hmetric_e (theta : ℝ) (htheta : theta ∈ Icc (1 : ℝ) 3) :
      DifferentialGeometry.Diffeomorph.pullbackMetricCross (h theta) e =
        scalarOneShrinkingCylinderMetric (1 - theta)
          (sub_lt_self 1 (lt_of_lt_of_le zero_lt_one htheta.1)) := by
    apply SmoothRiemannianMetric.ext_inner
    rintro ⟨y, z⟩ ⟨v, a⟩ ⟨w, b⟩
    have hh := congrArg (fun g : SmoothRiemannianMetric SpatialNeckCylinderModel
        SpatialNeckCylinder => g.inner (y, z + pStar.2) (v, a) (w, b)) (hmetric theta htheta)
    have htime : 1 - theta < 1 :=
      sub_lt_self 1 (lt_of_lt_of_le zero_lt_one htheta.1)
    have hpull_d := DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner
      (h theta) d (y, z + pStar.2) (v, a) (w, b)
    have hmodel_d := scalarOneShrinkingCylinderMetric_inner
      (1 - theta) htime y (z + pStar.2) v w a b
    have hform := hpull_d.symm.trans (hh.trans hmodel_d)
    have hpull_e := DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner
      (h theta) e (y, z) (v, a) (w, b)
    have hmodel_e := scalarOneShrinkingCylinderMetric_inner
      (1 - theta) htime y z v w a b
    have hderivs := congrArg₂
      (fun V W : TangentSpace I3 (d (y, z + pStar.2)) =>
        (h theta).inner (d (y, z + pStar.2)) V W)
      (hd y z v a) (hd y z w b)
    exact hpull_e.trans (hderivs.trans (hform.trans hmodel_e.symm))
  refine ⟨pStar.1, ?_⟩
  intro epsilon hepsilon hepsilon_one
  exact asymptoticCylinder_eventually_isStrongNeckCenter F tau htau q Phi C hcanonical
    h htimeOne hconvergence e pStar.1 hmarked hmetric_e epsilon hepsilon hepsilon_one

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
