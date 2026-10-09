import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalCapChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticCollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticProfile
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapWitnessProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import DifferentialGeometry.Geometry.Metric.Pullback.Composition
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Geometry.Metric.DistancePullback

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace ThreeSpace (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold ThreeModel ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k}
  {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}

namespace CanonicalStaticInsertionWitness

variable (w : CanonicalStaticInsertionWitness d fixed.collarLength fixed.collar_pos D m ε)

def toStaticCapWitness (hD : 0 < D) :
    StaticCapWitness d.oriented.toNormalizedNeck fixed D m ε := by
  letI := neckRetainedCollarChartedSpace d.precision_pos
  letI := neckRetainedCollar_isManifold d.precision_pos
  letI := threeBallChartedSpace
  letI := threeBall_isManifold
  letI := standardCapCoreChartedSpace
  letI := standardCapCore_isManifold
  letI := w.properties.secondCountable
  letI := uliftChartedSpace ThreeSpace (InsertionQuotient (inv_pos.mpr d.precision_pos))
  letI := isManifold_ulift ThreeModel (InsertionQuotient (inv_pos.mpr d.precision_pos))
  letI := staticCapInsertionQuotientChartedSpace d.precision_pos
  let e : InsertionQuotient (inv_pos.mpr d.precision_pos) ≃ₘ⟮ThreeModel, ThreeModel⟯
      ULift.{u} (InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
    uliftDiffeomorph ThreeModel _
  let up : C(InsertionQuotient (inv_pos.mpr d.precision_pos),
      ULift.{u} (InsertionQuotient (inv_pos.mpr d.precision_pos))) := ⟨e, e.continuous⟩
  let liftedMetric := Diffeomorph.pullbackMetricCross w.data.outMetric e.symm
  refine
    { radius_pos := hD
      accuracy_pos := w.accuracy_pos
      Output := ULift.{u} (InsertionQuotient (inv_pos.mpr d.precision_pos))
      outputTopology := inferInstance
      outputCharts := inferInstance
      outputSmooth := inferInstance
      outputHausdorff := inferInstance
      outputCountable := e.toHomeomorph.symm.secondCountableTopology
      attaching := Diffeomorph.refl (𝓡 2) (Sphere 2) ∞
      quotientCharts := staticCapInsertionQuotientChartedSpace d.precision_pos
      quotientSmooth := staticCapInsertionQuotient_isManifold d.precision_pos
      quotientPresentation :=
        (staticCapQuotientDiffeomorphInsertionQuotient d.precision_pos).trans e
      retainedCharts := inferInstance
      retainedSmooth := inferInstance
      retained_induced := neckRetainedCollar_inclusion_isSmoothEmbedding d.precision_pos
      ballCharts := inferInstance
      ballSmooth := inferInstance
      ball_induced := isSmoothEmbedding_threeBall_inclusion
      retained := up.comp w.retainedMap
      cap := up.comp w.cap
      retained_smooth := isSmoothEmbedding_diffeomorph_comp _ _ _ w.retainedMap_isSmoothEmbedding e
      cap_smooth := isSmoothEmbedding_diffeomorph_comp _ _ _ w.cap_smooth e
      retained_quotient := ?_
      cap_quotient := ?_
      cover := ?_
      overlap := ?_
      boundary_eq := fun y => congrArg e (w.cap_boundary y)
      tip := e w.data.tip
      tip_interior := ?_
      metric := liftedMetric
      retainedMetric := w.retainedMetric
      retained_metric_output := ?_
      retained_metric_input := w.retained_metric_input_neck
      window := up.comp w.window
      window_smooth := isSmoothEmbedding_diffeomorph_comp _ _ _ w.window_smooth e
      window_tip := fun hx => congrArg e (w.window_tip hx)
      windowMetric := w.windowMetric
      window_inner := ?_
      window_closeness := w.window_closeness
      modelCoreCharts := inferInstance
      modelCoreSmooth := inferInstance
      modelCore_induced := standardCapCore_induced
      capChart := up.comp w.capChart
      capChart_smooth := isSmoothEmbedding_diffeomorph_comp _ _ _ w.capChart_smooth e
      capChart_range := ?_
      capChart_boundary := fun y hx => congrArg e (w.capChart_boundary y hx)
      capChart_tip := fun hx => congrArg e (w.capChart_tip hx)
      window_deep := fun x _ hx hc => congrArg e (w.windowMap_eq_capChart x hx hc)
      tipCoordinate := w.data.profileTip
      tipCoordinate_lower := w.properties.profileTip_location.1
      tipCoordinate_upper := w.properties.profileTip_location.2
      radial := w.data.profile
      radial_continuous := w.properties.profile_smooth.continuous.continuousOn
      radial_monotone := w.properties.profile_monotone.monotoneOn _
      radial_range := w.properties.profile_mapsTo
      radial_smooth := w.properties.profile_smooth.contDiffOn
      radial_tip := w.properties.profile_tip
      radial_boundary := w.properties.profile_zero
      radial_derivative := fun z hz => w.profile_derivWithin_mem_Icc ⟨hz.1.le, hz.2⟩
      radial_tip_germ := w.profile_tip_germ
      radial_collar := fun z hz => w.profile_collar_eq_standardCapRadiusOfZ hz
      collapse := up.comp w.collapse
      collapse_locallyLipschitz := ?_
      collapse_retained := fun x hz => congrArg e (w.collapse_retained x hz)
      collapse_tip := fun x hz => congrArg e (w.collapse_tip x hz)
      collapse_radial := fun x hlo hhi hx => congrArg e (w.collapse_radial x hlo hhi hx)
      collapse_length := ?_ }
  · intro x
    apply congrArg e
    change w.data.retainedInclusion _ = _
    erw [staticCapQuotientDiffeomorphInsertionQuotient_retained, w.properties.retainedInclusion_eq]
  · intro x
    apply congrArg e
    change w.data.capInclusion _ = _
    erw [staticCapQuotientDiffeomorphInsertionQuotient_cap, w.properties.capInclusion_eq]
    rfl
  · change range (e ∘ w.retainedMap) ∪ range (e ∘ w.cap) = univ
    rw [range_comp, range_comp, ← image_union, w.retainedMap_range, w.cap_range,
      union_comm, w.properties.inclusions_cover, image_univ]
    exact e.surjective.range_eq
  · change range (e ∘ w.retainedMap) ∩ range (e ∘ w.cap) =
      range (e ∘ (w.cap ∘ sphereToThreeBall))
    rw [range_comp e w.retainedMap, range_comp e w.cap,
      range_comp e (w.cap ∘ sphereToThreeBall)]
    have hi : Injective (e : InsertionQuotient (inv_pos.mpr d.precision_pos) →
        ULift.{u} (InsertionQuotient (inv_pos.mpr d.precision_pos))) := e.injective
    rw [← image_inter hi, w.retainedMap_range, w.cap_range, inter_comm,
      w.properties.inclusions_inter]
    rfl
  · obtain ⟨x, hx, he⟩ := w.cap_tip_interior
    exact ⟨x, hx, congrArg e he⟩
  · intro x V W
    change w.retainedMetric.inner x V W =
      liftedMetric.inner (e (w.retainedMap x))
        (mfderiv (𝓡∂ 3) ThreeModel (e ∘ w.retainedMap) x V)
        (mfderiv (𝓡∂ 3) ThreeModel (e ∘ w.retainedMap) x W)
    rw [DifferentialGeometry.Geometry.Metric.pullbackMetricCross_symm_comp_inner
      w.data.outMetric e w.retainedMap w.retainedMap_contMDiff]
    exact w.retained_metric_output x V W
  · intro x V W
    change w.windowMetric.inner x V W = metricScalarAt g x₀ *
      liftedMetric.inner (e (w.window x))
        (mfderiv ThreeModel ThreeModel (e ∘ w.window) x V)
        (mfderiv ThreeModel ThreeModel (e ∘ w.window) x W)
    rw [DifferentialGeometry.Geometry.Metric.pullbackMetricCross_symm_comp_inner
      w.data.outMetric e w.window w.window_smooth.contMDiff]
    exact w.window_inner x V W
  · change range (e ∘ w.capChart) = range (e ∘ w.cap)
    rw [range_comp, range_comp, w.capChart_range_cap]
  · intro x
    obtain ⟨U, hU, L, hL⟩ := w.collapse_locallyLipschitz x
    refine ⟨U, hU, L, ?_⟩
    intro y hy z hz
    change riemannianEDistOf liftedMetric (e (w.collapse y)) (e (w.collapse z)) ≤ _
    rw [DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross]
    simp only [Diffeomorph.symm_apply_apply]
    exact hL y hy z hz
  · intro γ a b _ hγ _
    have h := w.collapse_length γ a b hγ
    change DifferentialGeometry.Geometry.riemannianCurveVariation liftedMetric
      (e ∘ w.collapse ∘ γ) a b ≤
        riemannianCurveLength g (fun t => d.oriented.map (γ t).1) a b
    unfold DifferentialGeometry.Geometry.riemannianCurveVariation
    simp only [liftedMetric, Function.comp_apply,
      DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross,
      Diffeomorph.symm_apply_apply]
    exact h

end CanonicalStaticInsertionWitness
end DifferentialGeometry.PDE.RicciFlow.StandardCap
