import DifferentialGeometry.Geometry.Neck.Normalized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.Cylinder
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Metric.StandardCap.Distance
import Mathlib.Topology.Constructions

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology InnerProductSpace NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩


variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]


structure StaticCapScaffold where
  collarLength : ℝ
  collar_pos : 0 < collarLength
  positiveRadius : ℝ
  deepRadius : ℝ
  positiveRadius_pos : 0 < positiveRadius
  positive_lt_deep : positiveRadius < deepRadius
  deep_lt_one : deepRadius < 1
  deep_lt_cap : deepRadius < standardCapL


  deep_tip_side : deepRadius < standardCapRadiusOfZ (-2 * collarLength)

def standardCapClosedCore : Set ThreeSpace := Metric.closedBall 0 standardCapL

private theorem standardCapRho_eq_expNegInvGlue (r : ℝ) : standardCapRho r = expNegInvGlue r := by
  by_cases hr : r ≤ 0
  · simp [standardCapRho, expNegInvGlue, hr]
  · simp only [standardCapRho, expNegInvGlue, ite_eq_right hr]
    congr 1
    ring

private theorem standardCapEta_eq_smoothTransition (x : ℝ) :
    standardCapEta x = Real.smoothTransition (1 - x) := by
  simp only [standardCapEta, Real.smoothTransition, standardCapRho_eq_expNegInvGlue,
    sub_sub_cancel]
  rw [add_comm]

private theorem standardCapAngle_eq (r : ℝ) :
    standardCapAngle r = DifferentialGeometry.PDE.RicciFlow.StandardCap.angle r := by
  have h1 : (∫ u in (0 : ℝ)..r, standardCapEta (u - standardCapA0)) =
      (∫ u in (0 : ℝ)..r,
        Real.smoothTransition
          (DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd - u)) := by
    apply intervalIntegral.integral_congr
    intro u _
    change standardCapEta (u - standardCapA0) =
      Real.smoothTransition
        (DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd - u)
    rw [standardCapEta_eq_smoothTransition]
    congr 1
    simp only [standardCapA0,
      DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionStart,
      DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd]
    ring
  simp only [standardCapAngle, DifferentialGeometry.PDE.RicciFlow.StandardCap.angle, one_div]
  rw [h1]

private theorem standardCapWarp_eq_warpingFunction (r : ℝ) :
    standardCapWarp r = DifferentialGeometry.PDE.RicciFlow.StandardCap.warpingFunction r := by
  simp only [standardCapWarp, DifferentialGeometry.PDE.RicciFlow.StandardCap.warpingFunction,
    standardCapAngle_eq]

theorem standardCapMetric_eq_metric :
    standardCapMetric = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric := by
  have hstd : ∀ (x v w : ThreeSpace),
      (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric).inner x v w =
        standardCapInner x v w := by
    intro x v w
    by_cases hx : x = 0
    · subst x
      rw [DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_inner_zero, standardCapInner,
        ite_eq_left rfl]
    · rw [DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_inner_of_ne_zero hx,
        standardCapInner, ite_eq_right hx]
      rw [DifferentialGeometry.Geometry.Riemannian.radialBilinearField_apply]
      simp only [standardCapWarp_eq_warpingFunction]
      field_simp
  refine SmoothRiemannianMetric.ext_inner fun x v w => ?_
  exact (standardCapMetric_inner x v w).trans (hstd x v w).symm

theorem standardCap_edist_zero (x : ThreeSpace) :
    riemannianEDistOf standardCapMetric 0 x = ENNReal.ofReal ‖x‖ := by
  rw [standardCapMetric_eq_metric]
  exact DifferentialGeometry.PDE.RicciFlow.StandardCap.edist_zero x

def standardCapWindow (D : ℝ) : TopologicalSpace.Opens ThreeSpace :=
  ⟨{x | ‖x‖ < D + 1}, isOpen_lt continuous_norm continuous_const⟩

def staticCapGluingRel (δ : ℝ) (ζ : Sphere 2 ≃ₜ Sphere 2)
    (x y : neckRetainedCollar δ ⊕ ThreeBall) : Prop :=
  ∃ z : Sphere 2, ∃ hz : 0 < δ⁻¹,
    x = Sum.inr (sphereToThreeBall z) ∧
      y = Sum.inl ⟨(ζ z, 0), le_rfl, hz⟩

abbrev StaticCapQuotient (δ : ℝ) (ζ : Sphere 2 ≃ₜ Sphere 2) :=
  Quotient (Relation.EqvGen.setoid (staticCapGluingRel δ ζ))

structure StaticCapWitness {h : SmoothRiemannianMetric ThreeModel M}
    {δ : ℝ} {k : ℕ} (neck : NormalizedNeck h δ k)
    (fixed : StaticCapScaffold) (D : ℝ) (m : ℕ) (ε : ℝ) where
  radius_pos : 0 < D
  accuracy_pos : 0 < ε
  Output : Type u
  [outputTopology : TopologicalSpace Output]
  [outputCharts : ChartedSpace ThreeSpace Output]
  [outputSmooth : IsManifold ThreeModel ∞ Output]
  [outputHausdorff : T2Space Output]
  [outputCountable : SecondCountableTopology Output]
  attaching : Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2
  [quotientCharts : ChartedSpace ThreeSpace (StaticCapQuotient δ attaching.toHomeomorph)]
  [quotientSmooth : IsManifold ThreeModel ∞ (StaticCapQuotient δ attaching.toHomeomorph)]
  quotientPresentation : StaticCapQuotient δ attaching.toHomeomorph ≃ₘ⟮ThreeModel, ThreeModel⟯ Output
  [retainedCharts : ChartedSpace (EuclideanHalfSpace 3) (neckRetainedCollar δ)]
  [retainedSmooth : IsManifold (𝓡∂ 3) ∞ (neckRetainedCollar δ)]
  retained_induced : IsSmoothEmbedding (𝓡∂ 3) NeckCylinderModel ∞
    (Subtype.val : neckRetainedCollar δ → NeckCylinder)
  [ballCharts : ChartedSpace (EuclideanHalfSpace 3) ThreeBall]
  [ballSmooth : IsManifold (𝓡∂ 3) ∞ ThreeBall]
  ball_induced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : ThreeBall → ThreeSpace)
  retained : C(neckRetainedCollar δ, Output)
  cap : C(ThreeBall, Output)
  retained_smooth : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ retained
  cap_smooth : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ cap
  retained_quotient : ∀ x, retained x = quotientPresentation (Quotient.mk _ (Sum.inl x))
  cap_quotient : ∀ x, cap x = quotientPresentation (Quotient.mk _ (Sum.inr x))
  cover : Set.range retained ∪ Set.range cap = univ
  overlap : Set.range retained ∩ Set.range cap = Set.range (cap.comp sphereToThreeBall)
  boundary_eq : ∀ y, cap (sphereToThreeBall y) =
    retained ⟨(attaching y, 0), le_rfl, inv_pos.mpr neck.delta_pos⟩
  tip : Output
  tip_interior : ∃ x : ThreeBall, ‖x.1‖ < 1 ∧ cap x = tip
  metric : SmoothRiemannianMetric ThreeModel Output
  retainedMetric : SmoothRiemannianMetric (𝓡∂ 3) (neckRetainedCollar δ)
  retained_metric_output : ∀ x V W, retainedMetric.inner x V W =
    metric.inner (retained x) (mfderiv (𝓡∂ 3) ThreeModel retained x V)
      (mfderiv (𝓡∂ 3) ThreeModel retained x W)
  retained_metric_input : ∀ x V W,
    let inclusion : neckRetainedCollar δ → neckBuffer δ := fun y =>
      ⟨y.1, by
        have := inv_pos.mpr neck.delta_pos
        constructor <;> linarith [y.2.1, y.2.2]⟩
    retainedMetric.inner x V W = h.inner (neck.chart (inclusion x))
      (mfderiv (𝓡∂ 3) ThreeModel (neck.chart ∘ inclusion) x V)
      (mfderiv (𝓡∂ 3) ThreeModel (neck.chart ∘ inclusion) x W)
  window : C(standardCapWindow D, Output)
  window_smooth : IsSmoothEmbedding ThreeModel ThreeModel ∞ window
  window_tip : ∀ hx : (0 : ThreeSpace) ∈ standardCapWindow D, window ⟨0, hx⟩ = tip
  windowMetric : SmoothRiemannianMetric ThreeModel (standardCapWindow D)
  window_inner : ∀ x V W, windowMetric.inner x V W = neck.scale *
    metric.inner (window x) (mfderiv ThreeModel ThreeModel window x V)
      (mfderiv ThreeModel ThreeModel window x W)
  window_closeness : metricDerivNormSupOn {x : standardCapWindow D | ‖x.1‖ < D}
    m windowMetric (standardCapMetric.restrictOpen (standardCapWindow D))
      (standardCapMetric.restrictOpen (standardCapWindow D)) < ε
  [modelCoreCharts : ChartedSpace (EuclideanHalfSpace 3) standardCapClosedCore]
  [modelCoreSmooth : IsManifold (𝓡∂ 3) ∞ standardCapClosedCore]
  modelCore_induced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
    (Subtype.val : standardCapClosedCore → ThreeSpace)
  capChart : C(standardCapClosedCore, Output)
  capChart_smooth : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ capChart
  capChart_range : Set.range capChart = Set.range cap
  capChart_boundary : ∀ y : Sphere 2, ∀ hx : standardCapL • y.1 ∈ standardCapClosedCore,
    capChart ⟨standardCapL • y.1, hx⟩ =
      retained ⟨(y, 0), le_rfl, inv_pos.mpr neck.delta_pos⟩
  capChart_tip : ∀ hx : (0 : ThreeSpace) ∈ standardCapClosedCore, capChart ⟨0, hx⟩ = tip
  window_deep : ∀ x : ThreeSpace, ‖x‖ ≤ fixed.deepRadius →
    ∀ hx : x ∈ standardCapWindow D, ∀ hc : x ∈ standardCapClosedCore,
      window ⟨x, hx⟩ = capChart ⟨x, hc⟩
  tipCoordinate : ℝ
  tipCoordinate_lower : -δ⁻¹ < tipCoordinate
  tipCoordinate_upper : tipCoordinate < -2 * fixed.collarLength - standardCapL
  radial : ℝ → ℝ
  radial_continuous : ContinuousOn radial (Icc tipCoordinate 0)
  radial_monotone : MonotoneOn radial (Icc tipCoordinate 0)
  radial_range : MapsTo radial (Icc tipCoordinate 0) (Icc 0 standardCapL)
  radial_smooth : ContDiffOn ℝ ∞ radial (Ioc tipCoordinate 0)
  radial_tip : radial tipCoordinate = 0
  radial_boundary : radial 0 = standardCapL
  radial_derivative : ∀ z ∈ Ioc tipCoordinate 0,
    0 ≤ derivWithin radial (Icc tipCoordinate 0) z ∧
      derivWithin radial (Icc tipCoordinate 0) z ≤ 1
  radial_tip_germ : ∃ e : ℝ, 0 < e ∧ ∀ z ∈ Icc tipCoordinate (min 0 (tipCoordinate + e)),
    radial z = z - tipCoordinate
  radial_collar : ∀ z ∈ Icc (-2 * fixed.collarLength) 0,
    radial z = standardCapRadiusOfZ z
  collapse : C(neckCentralDomain δ, Output)
  collapse_locallyLipschitz : ∀ x : neckCentralDomain δ, ∃ U ∈ 𝓝 x, ∃ L : ℝ≥0,
    ∀ y ∈ U, ∀ z ∈ U, riemannianEDistOf metric (collapse y) (collapse z) ≤
      L * riemannianEDistOf h (neck.chart y.1) (neck.chart z.1)
  collapse_retained : ∀ x : neckCentralDomain δ, ∀ hz : 0 ≤ x.1.1.2,
    collapse x = retained ⟨x.1.1, hz, x.2.2⟩
  collapse_tip : ∀ x : neckCentralDomain δ, x.1.1.2 ≤ tipCoordinate → collapse x = tip
  collapse_radial : ∀ x : neckCentralDomain δ,
    tipCoordinate < x.1.1.2 → x.1.1.2 ≤ 0 →
    ∀ hx : radial x.1.1.2 • x.1.1.1.1 ∈ standardCapClosedCore,
      collapse x = capChart ⟨radial x.1.1.2 • x.1.1.1.1, hx⟩
  collapse_length : ∀ (γ : ℝ → neckCentralDomain δ) (a b : ℝ),
    a ≤ b → ContinuousOn γ (Icc a b) →
    DifferentialGeometry.Geometry.riemannianCurveVariation h (fun t => neck.chart (γ t).1) a b ≠ ⊤ →
    DifferentialGeometry.Geometry.riemannianCurveVariation metric (fun t => collapse (γ t)) a b ≤
      DifferentialGeometry.Geometry.riemannianCurveVariation h (fun t => neck.chart (γ t).1) a b

attribute [instance] StaticCapWitness.outputTopology StaticCapWitness.outputCharts
  StaticCapWitness.outputSmooth StaticCapWitness.outputHausdorff StaticCapWitness.outputCountable

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace StaticCapScaffold

def ofCollarLength (A : ℝ) (hA : 0 < A) : StaticCapScaffold := by
  have hL : 0 < standardCapL := by
    rw [standardCapL_eq_transitionEnd]
    exact DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd_pos
  let r := min (min (standardCapL / 2) (standardCapRadiusOfZ (-2 * A) / 2)) (1 / 2)
  have hr : 0 < r :=
    lt_min (lt_min (half_pos hL)
      (half_pos (Function.invFun standardCapConformalCoordinate (-2 * A)).2)) (by norm_num)
  exact {
    collarLength := A
    collar_pos := hA
    positiveRadius := r / 2
    deepRadius := r
    positiveRadius_pos := half_pos hr
    positive_lt_deep := half_lt_self hr
    deep_lt_one := (min_le_right _ _).trans_lt (by norm_num)
    deep_lt_cap := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt
      (half_lt_self hL)
    deep_tip_side := ((min_le_left _ _).trans (min_le_right _ _)).trans_lt
      (half_lt_self (Function.invFun standardCapConformalCoordinate (-2 * A)).2) }

@[simp] theorem ofCollarLength_collarLength (A : ℝ) (hA : 0 < A) :
    (ofCollarLength A hA).collarLength = A := rfl

end StaticCapScaffold
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
