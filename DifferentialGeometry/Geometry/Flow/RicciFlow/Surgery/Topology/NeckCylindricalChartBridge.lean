import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

noncomputable section

open Set Bundle Manifold Function
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

section

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.exists_cylindricalChart (N : NormalizedNeck h δ k) :
    ∃ (V : TopologicalSpace.Opens M)
      (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V),
      (V : Set M) = Set.range (N.chart : neckBuffer δ → M) ∧
      (∀ x, (Φ x : M) = N.chart x) ∧
      (∀ y : V, N.chart (Φ.symm y) = (y : M)) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp [ThreeSpace]
  have hinj : ∀ y : neckBuffer δ,
      Injective (mfderiv NeckCylinderModel ThreeModel (N.chart : neckBuffer δ → M) y) :=
    fun y => injective_mfderiv_of_isImmersionAt NeckCylinderModel ThreeModel
      (N.chart : neckBuffer δ → M) y (N.chart_smooth.isImmersion.isImmersionAt y)
  exact exists_diffeomorph_onto_range_of_injective_immersion (I := NeckCylinderModel)
    (J := ThreeModel) (N.chart : neckBuffer δ → M) N.chart_smooth.contMDiff
    N.chart_smooth.isEmbedding.injective hinj hdim

noncomputable def NormalizedNeck.cylindricalChart (N : NormalizedNeck h δ k) :
    DifferentialGeometry.Geometry.Neck.cylindricalChart ThreeModel (M := M) :=
  let V : TopologicalSpace.Opens M := Classical.choose N.exists_cylindricalChart
  let Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V :=
    Classical.choose (Classical.choose_spec N.exists_cylindricalChart)
  { domain := neckBuffer δ
    target := V
    chart := Φ
    scale := N.scale
    scale_pos := N.scale_pos }

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem NormalizedNeck.cylindricalChart_domain (N : NormalizedNeck h δ k) :
    N.cylindricalChart.domain = neckBuffer δ := rfl

omit [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem NormalizedNeck.cylindricalChart_scale (N : NormalizedNeck h δ k) :
    N.cylindricalChart.scale = N.scale := rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_target (N : NormalizedNeck h δ k) :
    (N.cylindricalChart.target : Set M) = Set.range (N.chart : neckBuffer δ → M) := by
  simp only [NormalizedNeck.cylindricalChart]
  exact (Classical.choose_spec (Classical.choose_spec N.exists_cylindricalChart)).1

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_chart_apply (N : NormalizedNeck h δ k)
    (x : neckBuffer δ) :
    ((N.cylindricalChart.chart x : N.cylindricalChart.target) : M) = N.chart x := by
  simp only [NormalizedNeck.cylindricalChart]
  exact (Classical.choose_spec (Classical.choose_spec N.exists_cylindricalChart)).2.1 x

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_center (N : NormalizedNeck h δ k) :
    ((N.cylindricalChart.chart ⟨(N.sphereMark, 0), by
        have := inv_pos.mpr N.delta_pos
        constructor <;> linarith⟩ : N.cylindricalChart.target) : M) = N.center :=
  (N.cylindricalChart_chart_apply _).trans N.marked

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_chart_symm_apply (N : NormalizedNeck h δ k)
    (y : N.cylindricalChart.target) :
    N.chart (N.cylindricalChart.chart.symm y) = (y : M) := by
  simp only [NormalizedNeck.cylindricalChart]
  exact (Classical.choose_spec (Classical.choose_spec N.exists_cylindricalChart)).2.2 y

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_pullbackMetricCross (N : NormalizedNeck h δ k) :
    Diffeomorph.pullbackMetricCross
        (scaleMetric N.cylindricalChart.scale N.cylindricalChart.scale_pos
          (h.restrictOpen N.cylindricalChart.target))
        N.cylindricalChart.chart = N.normalizedMetric := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp [ThreeSpace]
  have hinj : ∀ y : neckBuffer δ,
      Injective (mfderiv NeckCylinderModel ThreeModel (N.chart : neckBuffer δ → M) y) :=
    fun y => injective_mfderiv_of_isImmersionAt NeckCylinderModel ThreeModel
      (N.chart : neckBuffer δ → M) y (N.chart_smooth.isImmersion.isImmersionAt y)
  have hlocal : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞
      (N.chart : neckBuffer δ → M) :=
    isLocalDiffeomorph_of_injective_mfderiv (N.chart : neckBuffer δ → M)
      N.chart_smooth.contMDiff hinj hdim
  have hEq : N.normalizedMetric =
      pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric N.scale N.scale_pos h)
        (N.chart : neckBuffer δ → M) hlocal N.chart_smooth.isEmbedding.injective := by
    apply SmoothRiemannianMetric.ext_inner
    intro y V W
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner, N.normalized_inner]
  rw [hEq]
  exact (pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart h (N.chart : neckBuffer δ → M)
    hlocal N.chart_smooth.isEmbedding.injective N.scale N.scale_pos
    N.cylindricalChart.target N.cylindricalChart.chart
    (fun x => N.cylindricalChart_chart_apply x)).symm

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_metricCloseOn (N : NormalizedNeck h δ k)
    (hk : 2 ≤ k) : N.cylindricalChart.metricCloseOn h δ (neckClosedTest δ) := by
  intro x hx j hj
  have hcl := N.closeness
  rw [roundCylinderMetric_eq_geometry] at hcl
  rw [N.cylindricalChart_pullbackMetricCross]
  exact (metricDerivNorm_lt_of_sup_lt (isCompact_neckClosedTest δ) (hj.trans hk)
    N.normalizedMetric _ _ hcl hx).le

omit [T2Space M] [SigmaCompactSpace M] in
theorem isOpen_neckCentralDomain (δ : ℝ) : IsOpen (neckCentralDomain δ) := by
  change IsOpen {x : neckBuffer δ | -δ⁻¹ < x.1.2 ∧ x.1.2 < δ⁻¹}
  have hc : Continuous fun x : neckBuffer δ => x.1.2 := continuous_subtype_val.snd
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

omit [T2Space M] [SigmaCompactSpace M] in
theorem neckCentralDomain_subset_neckClosedTest (δ : ℝ) :
    neckCentralDomain δ ⊆ neckClosedTest δ :=
  fun _ hx => ⟨hx.1.le, hx.2.le⟩

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.cylindricalChart_metricCloseOn_neckCentralDomain
    (N : NormalizedNeck h δ k) (hk : 2 ≤ k) :
    N.cylindricalChart.metricCloseOn h δ (neckCentralDomain δ) :=
  fun x hx j hj =>
    N.cylindricalChart_metricCloseOn hk x (neckCentralDomain_subset_neckClosedTest δ hx) j hj

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.exists_least_ricci_field (N : NormalizedNeck h δ k) (hk : 2 ≤ k)
    (hδ : δ < 1 / 200000) :
    ∃ (ν : M → ℝ) (Y : ∀ y : M, TangentSpace ThreeModel y),
      ContMDiffOn ThreeModel 𝓘(ℝ) ∞ N.cylindricalChart.axial N.cylindricalChart.target ∧
      ContMDiffOn ThreeModel 𝓘(ℝ) ∞ ν
        (N.cylindricalChart.region (neckCentralDomain δ)) ∧
      ContMDiffOn ThreeModel ThreeModel.tangent ∞
        (fun y ↦ (⟨y, Y y⟩ : TangentBundle ThreeModel M))
        (N.cylindricalChart.region (neckCentralDomain δ)) ∧
      ∀ y ∈ N.cylindricalChart.region (neckCentralDomain δ),
        h.inner y (Y y) (Y y) = 1 ∧
        ricciSharp h y (Y y) = ν y • Y y ∧
        (∀ z : TangentSpace ThreeModel y, h.inner y z z = 1 → ν y ≤ ricciTensor h y z z) ∧
        |ν y| ≤ 5772 * N.cylindricalChart.scale * δ ∧
        Module.End.eigenspace (ricciSharp h y).toLinearMap (ν y) = Submodule.span ℝ {Y y} ∧
        0 < mvfderiv ThreeModel N.cylindricalChart.axial y (Y y) ∧
        |mvfderiv ThreeModel N.cylindricalChart.axial y (Y y) - 1| ≤ 92354 * δ :=
  N.cylindricalChart.exists_least_ricci_field h (isOpen_neckCentralDomain δ) δ hδ
    (N.cylindricalChart_metricCloseOn_neckCentralDomain hk)

end

theorem endNeckNormalizedNeck_cylindricalChart_target
    (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    ((endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart.target : Set ThreeSpace) =
      Set.range fun z : neckBuffer δ => endNeckMap r δ z := by
  rw [NormalizedNeck.cylindricalChart_target, endNeckNormalizedNeck_chart]

theorem endNeckNormalizedNeck_cylindricalChart_metricCloseOn
    (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) (hk : 2 ≤ k) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart.metricCloseOn metric δ
      (neckClosedTest δ) :=
  (endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart_metricCloseOn hk

theorem endNeckNormalizedNeck_cylindricalChart_metricCloseOn_zero
    (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart.metricCloseOn metric 0
      (neckClosedTest δ) := by
  intro x hx j hj
  rw [NormalizedNeck.cylindricalChart_pullbackMetricCross]
  have hK : (endNeckNormalizedNeck r δ hδ hδ1 hr k y).normalizedMetric =
      (Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen
        (endNeckNormalizedNeck r δ hδ hδ1 hr k y).cylindricalChart.domain := by
    rw [endNeckNormalizedNeck_normalizedMetric, referenceMetric_eq_roundCylinderMetric_neckBuffer,
      roundCylinderMetric_eq_geometry]
    rfl
  rw [hK, metricDerivNorm_self]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
