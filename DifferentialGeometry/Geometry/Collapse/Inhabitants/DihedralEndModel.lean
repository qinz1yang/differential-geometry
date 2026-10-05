import DifferentialGeometry.Geometry.Collapse.ZeroModel.ZeroModelRowLFR52
import DifferentialGeometry.Geometry.Collapse.RiemannianConeAtInfinity
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralCurvature
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralAxis
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientTautological

/-!
The actual diagonal sphere-line quotient, transported to a three-dimensional atlas, carries
the thin endpoint metric with the same spherical scale. Its source pullback, completeness,
nonnegative sectional curvature, full cone package and genuine one-end topology are
supplied internally.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse GC.Geometry.SphericalProduct
open scoped Manifold ContDiff
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
namespace DifferentialGeometry.Geometry.Collapse

private theorem dihedralEndRawMetric_invariant (ε : ℝ) (hε : 0 < ε) (γ : cylinderDiagonalGroup) :
    Diffeomorph.pullbackMetric (dihedralThinCylinderMetric ε (1 / 2) hε (by norm_num))
      (MulAction.smulDiffeomorph (n := ∞) ((𝓡 2).prod 𝓘(ℝ, ℝ)) γ) =
      dihedralThinCylinderMetric ε (1 / 2) hε (by norm_num) := by
  rcases cylinderDiagonalGroup_eq_one_or_generator γ with h | h
  · have heq : MulAction.smulDiffeomorph (n := ∞) ((𝓡 2).prod 𝓘(ℝ, ℝ)) γ =
        Diffeomorph.refl ((𝓡 2).prod 𝓘(ℝ, ℝ)) sphereCylinder ∞ := by
      apply Diffeomorph.ext
      intro x
      change γ.1 x = x
      rw [h]
      rfl
    rw [heq, Diffeomorph.pullbackMetric_refl]
  · have heq : MulAction.smulDiffeomorph (n := ∞) ((𝓡 2).prod 𝓘(ℝ, ℝ)) γ =
        cylinderActDiffeo dihedralReflectionZero := by
      apply Diffeomorph.ext
      intro x
      change γ.1 x = cylinderAct dihedralReflectionZero x
      rw [h, cylinderAct_dihedralReflectionZero]
      exact cylinderDiagonalDiffeomorph_apply x
    rw [heq]
    exact dihedralThinCylinderMetric_invariant ε (1 / 2) hε (by norm_num) _
private theorem dihedralEndRawMetric_compatible (ε : ℝ) (hε : 0 < ε) :
    metricFiberCompatible (dihedralThinCylinderMetric ε (1 / 2) hε (by norm_num))
      cylinderDiagonalQuotientMap cylinderDiagonalQuotientMap_isLocalDiffeomorph :=
  metricFiberCompatible_quotientMk_of_invariant _ (dihedralEndRawMetric_invariant ε hε)

def dihedralEndRawMetric (ε : ℝ) (hε : 0 < ε) :
    SmoothRiemannianMetric ((𝓡 2).prod 𝓘(ℝ, ℝ)) CylinderDiagonalQuotient :=
  descendedMetric (dihedralThinCylinderMetric ε (1 / 2) hε (by norm_num))
    cylinderDiagonalQuotientMap cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_surjective (dihedralEndRawMetric_compatible ε hε)
theorem dihedralEndRawMetric_pullback (ε : ℝ) (hε : 0 < ε) :
    localPullMetric (dihedralEndRawMetric ε hε) cylinderDiagonalQuotientMap
      cylinderDiagonalQuotientMap_isLocalDiffeomorph =
      dihedralThinCylinderMetric ε (1 / 2) hε (by norm_num) :=
  localPullMetric_descendedMetric _ _ _ _ _
theorem dihedralEndRawMetric_complete (ε : ℝ) (hε : 0 < ε) :
    DifferentialGeometry.RiemannianMetricComplete (dihedralEndRawMetric ε hε) := by
  have hraw : DifferentialGeometry.RiemannianMetricComplete
      (dihedralThinCylinderMetric ε (1 / 2) hε (by norm_num)) := by
    have hc := DifferentialGeometry.RiemannianMetricComplete.pullbackCross
      (dihedralRechartedMetric ε (1 / 2) hε (by norm_num))
      sphereCylinderRechartDiffeomorph
      (dihedralRechartedMetric_complete ε (1 / 2) hε (by norm_num))
    rw [dihedralRechartedMetric, Diffeomorph.pullbackMetricCross_trans,
      Diffeomorph.self_trans_symm, Diffeomorph.pullbackMetricCross_refl] at hc
    exact hc
  exact DifferentialGeometry.RiemannianMetricComplete.of_coveringMap_localPullMetric
    _ _ cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_isCoveringMap cylinderDiagonalQuotientMap_surjective
    (dihedralEndRawMetric_pullback ε hε) hraw

open private localPullMetric_eq_pullbackMetricCross localPullMetric_symm_pullbackMetricCross
from DifferentialGeometry.Geometry.Metric.DistancePullback
abbrev dihedralEndCarrier :=
  CarrierRechart (Homeomorph.refl CylinderDiagonalQuotient) (productModelEquiv 2)
local instance dihedralEndSigma : SigmaCompactSpace dihedralEndCarrier :=
  (CarrierRechart.homeomorphPoint (Homeomorph.refl CylinderDiagonalQuotient)
    (productModelEquiv 2)).isClosedEmbedding.sigmaCompactSpace
def dihedralEndRechart : CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
    dihedralEndCarrier :=
  CarrierRechart.diffeomorph (Homeomorph.refl CylinderDiagonalQuotient) (productModelEquiv 2)
def dihedralEndMetric (ε : ℝ) (hε : 0 < ε) : SmoothRiemannianMetric (𝓡 3) dihedralEndCarrier :=
  Diffeomorph.pullbackMetricCross (dihedralEndRawMetric ε hε) dihedralEndRechart.symm
def dihedralEndProjection : sphereCylinderRechart → dihedralEndCarrier :=
  dihedralEndRechart ∘ cylinderDiagonalQuotientMap ∘ sphereCylinderRechartDiffeomorph.symm
theorem dihedralEndProjection_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ dihedralEndProjection :=
  isLocalDiffeomorph_comp dihedralEndRechart.isLocalDiffeomorph
    (isLocalDiffeomorph_comp cylinderDiagonalQuotientMap_isLocalDiffeomorph
      sphereCylinderRechartDiffeomorph.symm.isLocalDiffeomorph)
theorem dihedralEndMetric_complete (ε : ℝ) (hε : 0 < ε) :
    DifferentialGeometry.RiemannianMetricComplete (dihedralEndMetric ε hε) :=
  DifferentialGeometry.RiemannianMetricComplete.pullbackCross _ _
    (dihedralEndRawMetric_complete ε hε)
theorem dihedralEndMetric_pullback (ε : ℝ) (hε : 0 < ε) :
    localPullMetric (dihedralEndMetric ε hε) dihedralEndProjection
      dihedralEndProjection_localDiffeomorph =
      dihedralRechartedMetric ε (1 / 2) hε (by norm_num) := by
  have he : localPullMetric (dihedralEndMetric ε hε) dihedralEndRechart
      dihedralEndRechart.isLocalDiffeomorph = dihedralEndRawMetric ε hε := by
    have heq : dihedralEndRechart.symm.symm = dihedralEndRechart := by
      apply Diffeomorph.ext
      intro x
      rfl
    change localPullMetric
      (Diffeomorph.pullbackMetricCross (dihedralEndRawMetric ε hε) dihedralEndRechart.symm)
      dihedralEndRechart dihedralEndRechart.isLocalDiffeomorph = _
    simpa only [heq] using
      localPullMetric_symm_pullbackMetricCross (dihedralEndRawMetric ε hε) dihedralEndRechart.symm
  let f := cylinderDiagonalQuotientMap ∘ sphereCylinderRechartDiffeomorph.symm
  have hf : IsLocalDiffeomorph (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f :=
    isLocalDiffeomorph_comp cylinderDiagonalQuotientMap_isLocalDiffeomorph
      sphereCylinderRechartDiffeomorph.symm.isLocalDiffeomorph
  calc
    _ = localPullMetric
        (localPullMetric (dihedralEndMetric ε hε) dihedralEndRechart
          dihedralEndRechart.isLocalDiffeomorph)
        f hf :=
      (localPullMetric_comp _ dihedralEndRechart f dihedralEndRechart.isLocalDiffeomorph hf
        (isLocalDiffeomorph_comp dihedralEndRechart.isLocalDiffeomorph hf)).symm
    _ = localPullMetric (dihedralEndRawMetric ε hε) f hf := by rw [he]
    _ = localPullMetric
        (localPullMetric (dihedralEndRawMetric ε hε) cylinderDiagonalQuotientMap
          cylinderDiagonalQuotientMap_isLocalDiffeomorph)
        sphereCylinderRechartDiffeomorph.symm
        sphereCylinderRechartDiffeomorph.symm.isLocalDiffeomorph :=
      (localPullMetric_comp _ cylinderDiagonalQuotientMap sphereCylinderRechartDiffeomorph.symm
        cylinderDiagonalQuotientMap_isLocalDiffeomorph
        sphereCylinderRechartDiffeomorph.symm.isLocalDiffeomorph hf).symm
    _ = _ := by
      rw [dihedralEndRawMetric_pullback, localPullMetric_eq_pullbackMetricCross]
      rfl

open DifferentialGeometry.Geometry.Riemannian
open private dihedralThinCylinderMetric_sectional_nonneg
from DifferentialGeometry.Geometry.Collapse.Inhabitants.DihedralCurvature
theorem dihedralEndRawMetric_sectional_nonneg (ε : ℝ) (hε : 0 < ε)
    (x : CylinderDiagonalQuotient) :
    SectionalBoundedBelowAt (dihedralEndRawMetric ε hε) x 0 := by
  obtain ⟨y, rfl⟩ := cylinderDiagonalQuotientMap_surjective x
  let e := cylinderDiagonalQuotientMap_isLocalDiffeomorph.mfderivToContinuousLinearEquiv
    (by decide) y
  change ∀ v w, 0 * _ ≤ _
  simp only [zero_mul]
  refine (e.surjective.forall₂ (p := fun v w =>
    0 ≤ Curvature.metricRm04StandardAt (dihedralEndRawMetric ε hε)
      (cylinderDiagonalQuotientMap y) v w w v)).mpr ?_
  intro v w
  have h := dihedralThinCylinderMetric_sectional_nonneg ε (1 / 2) hε (by norm_num) y v w
  rw [← dihedralEndRawMetric_pullback] at h
  have he (a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) y) :
      e a = mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        cylinderDiagonalQuotientMap y a := rfl
  rw [he v, he w]
  simpa only [zero_mul, Curvature.metricRm04StandardAt_localPullMetric] using h
theorem dihedralEndMetric_sectional_nonneg (ε : ℝ) (hε : 0 < ε) (x : dihedralEndCarrier) :
    SectionalBoundedBelowAt (dihedralEndMetric ε hε) x 0 :=
  Geometry.Riemannian.sectionalBoundedBelowAt_pullbackMetricCross _ _ x
    (dihedralEndRawMetric_sectional_nonneg ε hε _)

local instance dihedralEndRawConnected : ConnectedSpace CylinderDiagonalQuotient :=
  cylinderDiagonalQuotientMap_surjective.connectedSpace
    cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff.continuous
local instance dihedralEndMetrizable : TopologicalSpace.MetrizableSpace dihedralEndCarrier :=
  Manifold.metrizableSpace (𝓡 3) dihedralEndCarrier
open Set GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped ENNReal
theorem exists_dihedralEndCone (ε : ℝ) (hε : 0 < ε) (p : dihedralEndCarrier) :
    let modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace (dihedralEndMetric ε hε)
    ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
      ProperSpace C ∧ CompleteSpace C ∧
      (∀ a b : C, ∃ f : Set.Icc (0 : ℝ) 1 → C, Continuous f ∧
        f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      fourPointComparison 0 (Set.univ : Set C) ∧
      dimH (Set.univ : Set C) ≤ dimH (Set.univ : Set dihedralEndCarrier) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox dihedralEndCarrier C (modelMetric.rescale R⁻¹ (inv_pos.mpr hR))
          mC p o δ) := by
  let modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace (dihedralEndMetric ε hε)
  let modelComplete : CompleteSpace dihedralEndCarrier :=
    riemannianMetricComplete_iff_inducedMetricSpace.mp (dihedralEndMetric_complete ε hε)
  exact exists_cone_at_infinity_package_of_sectional_nonneg (dihedralEndMetric ε hε)
    (inducedMetricSpace_hmetric _) (dihedralEndMetric_sectional_nonneg ε hε) p

open Bundle DifferentialGeometry.Topology.VectorBundle

private abbrev EndFiber := RealProjectiveTautologicalFiber (A := EuclideanSpace ℝ (Fin 3))
open private projectiveQuotient_isLocalHomeomorph
  tautologicalLocalTrivialization tautologicalSectionTrivializationInv
  tautologicalSectionTrivializationInv_apply
from DifferentialGeometry.Bundle.ProjectiveSpace.Tautological
local instance dihedralEndTautologicalContinuous : IsContinuousRiemannianBundle ℝ EndFiber := by
  refine ⟨fun p => innerSL ℝ, ?_, fun p v w => rfl⟩
  rw [continuous_iff_continuousAt]
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  have hp := (trivializationAt ℝ EndFiber p).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt ℝ EndFiber p)
  apply (continuousAt_const (y := innerSL ℝ)).congr_of_eventuallyEq
  filter_upwards [hp] with q hq
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [hom_trivializationAt_apply]
  have htriv : q ∈ (trivializationAt ℝ (Bundle.Trivial
      (RealProjectiveSpace (EuclideanSpace ℝ (Fin 3))) ℝ) p).baseSet := Set.mem_univ q
  have hhom : q ∈ (trivializationAt (ℝ →L[ℝ] ℝ) (fun x => EndFiber x →L[ℝ] ℝ) p).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hq, htriv⟩
  rw [ContinuousLinearMap.inCoordinates_eq hq hhom]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Trivialization.coe_continuousLinearEquivAt_eq]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hhom,
    hom_trivializationAt_apply,
    ContinuousLinearMap.inCoordinates_eq hq htriv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ htriv,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ htriv]
  have hreal (r : ℝ) :
      (trivializationAt ℝ (Bundle.Trivial
        (RealProjectiveSpace (EuclideanSpace ℝ (Fin 3))) ℝ) p ⟨q, r⟩).2 = r := rfl
  rw [hreal]
  rw [innerSL_apply_apply, innerSL_apply_apply, Submodule.coe_inner]
  let s := projectiveQuotient_isLocalHomeomorph.localInverseAt (Quotient.out p)
  have hlift (r : ℝ) :
      (((trivializationAt ℝ EndFiber p).continuousLinearEquivAt ℝ q hq).symm r :
        EuclideanSpace ℝ (Fin 3)) = r • (s q : EuclideanSpace ℝ (Fin 3)) := by
    have ht := (trivializationAt ℝ EndFiber p).symm_apply_eq_mk_continuousLinearEquivAt_symm
      (R := ℝ) q hq r
    have htvec := congrArg (fun z : Bundle.TotalSpace ℝ EndFiber =>
      (z.2 : EuclideanSpace ℝ (Fin 3))) ht
    have hi := congrArg Prod.snd (tautologicalSectionTrivializationInv_apply
      (projectiveQuotient_isLocalHomeomorph.localInverseAt (Quotient.out p)).source s
      (fun t ht => projectiveQuotient_isLocalHomeomorph.apply_localInverseAt_of_mem ht)
      (q, r) hq)
    exact htvec.symm.trans hi
  rw [hlift, hlift, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow, mul_one]
  rw [Real.inner_apply]

private def dihedralEndUnitCover (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Bundle.TotalSpace ℝ EndFiber :=
  cylinderDiagonalQuotientTautologicalTotalSpaceHomeomorph
    (cylinderDiagonalQuotientMap (y, 1))
private theorem dihedralEndUnitCover_continuous : Continuous dihedralEndUnitCover :=
  cylinderDiagonalQuotientTautologicalTotalSpaceHomeomorph.continuous.comp
    (cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff.continuous.comp
      (continuous_id.prodMk continuous_const))
private theorem dihedralEndUnitCover_norm (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ‖(dihedralEndUnitCover y).2‖ = 1 := by
  change ‖(1 : ℝ) • (y : EuclideanSpace ℝ (Fin 3))‖ = 1
  rw [one_smul, norm_eq_of_mem_sphere]
private theorem dihedralEndUnitCover_surjective (z : Bundle.TotalSpace ℝ EndFiber)
    (hz : ‖z.2‖ = 1) :
    ∃ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, dihedralEndUnitCover y = z := by
  obtain ⟨⟨y, t⟩, he⟩ := cylinderDiagonalQuotientMap_surjective
    (cylinderDiagonalQuotientTautologicalTotalSpaceHomeomorph.symm z)
  have heq : cylinderDiagonalQuotientTautologicalTotalSpaceHomeomorph
      (cylinderDiagonalQuotientMap (y, t)) = z := by
    rw [he, Homeomorph.apply_symm_apply]
  have ht : |t| = 1 := by
    rw [← heq] at hz
    change ‖t • (y : EuclideanSpace ℝ (Fin 3))‖ = 1 at hz
    simpa only [norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one] using hz
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ht with h | h
  · subst t
    exact ⟨y, heq⟩
  · subst t
    refine ⟨-y, ?_⟩
    have hquot : cylinderDiagonalQuotientMap (-y, 1) = cylinderDiagonalQuotientMap (y, -1) := by
      apply cylinderDiagonalQuotientMap_eq_iff.mpr
      right
      rw [cylinderDiagonalDiffeomorph_apply]
      simp only [cylinderDiagonal, neg_neg]
    exact (congrArg cylinderDiagonalQuotientTautologicalTotalSpaceHomeomorph hquot).trans heq


theorem dihedralEndMetric_one_end (ε : ℝ) (hε : 0 < ε) :
    let _modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace (dihedralEndMetric ε hε)
    ∀ K : Set dihedralEndCarrier, IsCompact K →
      (∃ a : dihedralEndCarrier, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a)) ∧
      ∀ a b : dihedralEndCarrier, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
        ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
        connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b := by
  let _modelMetric : MetricSpace dihedralEndCarrier := inducedMetricSpace (dihedralEndMetric ε hε)
  let modelProper : ProperSpace dihedralEndCarrier :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete (dihedralEndMetric_complete ε hε)
  exact ZeroModel.exactly_one_end_of_connected_unit_cover dihedralEndUnitCover
    dihedralEndUnitCover_continuous
    dihedralEndUnitCover_norm dihedralEndUnitCover_surjective
    (cylinderDiagonalQuotientTautologicalTotalSpaceHomeomorph.symm.trans
      dihedralEndRechart.toHomeomorph)

end DifferentialGeometry.Geometry.Collapse
