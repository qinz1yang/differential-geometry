import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Mathlib.Topology.Constructions

noncomputable section

open Bundle Manifold Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology InnerProductSpace NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

abbrev NeckCylinder := Sphere 2 × ℝ
abbrev NeckCylinderModel := (𝓡 2).prod 𝓘(ℝ, ℝ)

def shrinkingCylinderInner (v : Iio (1 : ℝ)) (x : NeckCylinder)
    (V W : TangentSpace NeckCylinderModel x) : ℝ :=
  2 * (1 - v.1) *
      ⟪mfderiv NeckCylinderModel ThreeModel (fun p : NeckCylinder => p.1.1) x V,
        mfderiv NeckCylinderModel ThreeModel (fun p : NeckCylinder => p.1.1) x W⟫_ℝ +
    ((fun (r s : ℝ) => r * s) : ℝ → ℝ → ℝ)
      (mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd x V)
      (mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd x W)

theorem exists_unique_shrinkingCylinderMetric (v : Iio (1 : ℝ)) :
    ∃! g : SmoothRiemannianMetric NeckCylinderModel NeckCylinder,
      ∀ x V W, g.inner x V W = shrinkingCylinderInner v x V W := by
  sorry

def shrinkingCylinderMetric (v : Iio (1 : ℝ)) :
    SmoothRiemannianMetric NeckCylinderModel NeckCylinder :=
  Classical.choose (exists_unique_shrinkingCylinderMetric v)

def roundCylinderMetric : SmoothRiemannianMetric NeckCylinderModel NeckCylinder :=
  shrinkingCylinderMetric ⟨0, by norm_num⟩


def neckBuffer (δ : ℝ) : TopologicalSpace.Opens NeckCylinder :=
  ⟨{x | -δ⁻¹ - 1 < x.2 ∧ x.2 < δ⁻¹ + 1},
    (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)⟩

def neckClosedTest (δ : ℝ) : Set (neckBuffer δ) :=
  {x | -δ⁻¹ ≤ x.1.2 ∧ x.1.2 ≤ δ⁻¹}

def neckCentralDomain (δ : ℝ) : Set (neckBuffer δ) :=
  {x | -δ⁻¹ < x.1.2 ∧ x.1.2 < δ⁻¹}

abbrev neckRetainedCollar (δ : ℝ) := {x : NeckCylinder // 0 ≤ x.2 ∧ x.2 < δ⁻¹}

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]

structure NormalizedNeck (h : SmoothRiemannianMetric ThreeModel M) (δ : ℝ) (k : ℕ) where
  delta_pos : 0 < δ
  delta_lt_one : δ < 1
  sphereMark : Sphere 2
  center : M
  chart : C(neckBuffer δ, M)
  chart_smooth : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ chart
  marked : chart ⟨(sphereMark, 0), by
    have := inv_pos.mpr delta_pos
    constructor <;> linarith⟩ = center
  scale : ℝ
  scale_pos : 0 < scale
  scale_scalar : scale = metricScalarAt h center
  normalizedMetric : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ)
  normalized_inner : ∀ x V W,
    normalizedMetric.inner x V W = scale * h.inner (chart x)
      (mfderiv NeckCylinderModel ThreeModel chart x V)
      (mfderiv NeckCylinderModel ThreeModel chart x W)
  closeness : metricDerivNormSupOn (neckClosedTest δ) k normalizedMetric
    (roundCylinderMetric.restrictOpen (neckBuffer δ))
    (roundCylinderMetric.restrictOpen (neckBuffer δ)) < δ

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

theorem standardCap_edist_zero (x : ThreeSpace) :
    riemannianEDistOf standardCapMetric 0 x = ENNReal.ofReal ‖x‖ := by
  sorry

def standardCapWindow (D : ℝ) : TopologicalSpace.Opens ThreeSpace :=
  ⟨Metric.ball 0 (D + 1), Metric.isOpen_ball⟩

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
    riemannianCurveLength h (fun t => neck.chart (γ t).1) a b ≠ ⊤ →
    riemannianCurveLength metric (fun t => collapse (γ t)) a b ≤
      riemannianCurveLength h (fun t => neck.chart (γ t).1) a b

attribute [instance] StaticCapWitness.outputTopology StaticCapWitness.outputCharts
  StaticCapWitness.outputSmooth StaticCapWitness.outputHausdorff StaticCapWitness.outputCountable

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
