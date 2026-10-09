import DifferentialGeometry.Geometry.Exponential.FiniteMetric
import DifferentialGeometry.Geometry.Geodesic.Maximal.Uniqueness
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Koszul
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import DifferentialGeometry.Analysis.FiniteDimensional.BilinearPositivity

/-!
# The ported finite-order flow of a smooth metric is the smooth geodesic flow

For a smooth metric `g : SmoothRiemannianMetric I M` (that is, `ContMDiffRiemannianMetric I ∞`,
and `((⊤ : ℕ∞) : ℕ∞ω) + 1 = ∞` holds by `rfl`, so every lemma of the finite-order flow applies with
`r := ⊤`):

* `geodesicSpray_eq_geodesicVectorField`: the finite-order spray `g.geodesicSpray` (chart
  pull-back + `metricSpray`) is the smooth API's `geodesicVectorField g` (chart Christoffel symbols);
* `mem_geodesicFlowDomain_iff_mem_maximalGeodesicInterval`: the flow domain at `⟨p, v⟩` is the
  smooth API's `maximalGeodesicInterval g p v`;
* `proj_geodesicFlow_eq_maximalGeodesic`: on it, the projection of the flow is `maximalGeodesic`.

Lane CM-H (package CM, row 3), 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

open DifferentialGeometry.MetricKoszul (metricSpray koszulCov raisedKoszulOp_eq apply_koszul_vec)
open DifferentialGeometry.Geometry.Riemannian.Geodesic
  (geodesicVectorField maximalGeodesicInterval maximalGeodesic IsGeodesicOnWithInitial
    maximalGeodesic_eqOn)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- On the chart target, the chart Gram form of a smooth metric is the pull-back of the metric by
the inverse chart. -/
theorem chartGramBilin_extChartAt_symm_eq (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    DifferentialGeometry.Tensor.Coordinates.chartGramBilin g α ((extChartAt I α).symm y) =
      DifferentialGeometry.Geometry.pullbackMetricCoefficients g (extChartAt I α).symm y := by
  have hx : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  have ht : (trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) =
      mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y := by
    rw [TangentBundle.symmL_trivializationAt hx]
    rw [(extChartAt I α).right_inv hy, I.range_eq_univ, mfderivWithin_univ]
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun w => ?_
  rw [DifferentialGeometry.Tensor.Coordinates.chartGramBilin_eq_innerJinv]
  change (g.inner ((extChartAt I α).symm y) : E →L[ℝ] E →L[ℝ] ℝ)
      ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) u)
      ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) w) = _
  rw [ht]
  rfl

local instance : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance smoothSprayBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  inferInstance
local instance smoothSprayBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  inferInstance

/-- **Agreement of the sprays at `n = ∞`.** For a smooth metric the finite-order geodesic spray of
the ported flow is the smooth API's geodesic vector field. -/
theorem geodesicSpray_eq_geodesicVectorField
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (p : TangentBundle I M) :
    g.geodesicSpray p = geodesicVectorField g p := by
  let α : M := p.proj
  let y : E := extChartAt I α α
  let b := DifferentialGeometry.Geometry.pullbackMetricCoefficients g (extChartAt I α).symm
  let v : E := p.snd
  have hy : y ∈ (extChartAt I α).target := mem_extChartAt_target α
  have hnhds : (extChartAt I α).target ∈ 𝓝 y := (isOpen_extChartAt_target α).mem_nhds hy
  have heq : (fun u => DifferentialGeometry.Tensor.Coordinates.chartGramBilin g α
      ((extChartAt I α).symm u)) =ᶠ[𝓝 y] b := by
    filter_upwards [hnhds] with u hu
    exact chartGramBilin_extChartAt_symm_eq g α hu
  have hint : y ∈ interior (extChartAt I α).target := mem_interior_iff_mem_nhds.mpr hnhds
  have hK :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.chartChristoffelContraction_flat_eq_koszul
      g α hint v v
  rw [heq.fderiv_eq, chartGramBilin_extChartAt_symm_eq g α hy] at hK
  have hid (a : E) : (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y : E →L[ℝ] E) a = a := by
    have h := mfderivWithin_range_extChartAt_symm (I := I) (x := α)
    rw [I.range_eq_univ, mfderivWithin_univ] at h
    exact congrArg (fun L => L a) h
  have hco : IsCoercive (b y) := by
    refine DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal (b y) fun a ha => ?_
    have hpos := g.pos ((extChartAt I α).symm y) a ha
    change 0 < (g.inner ((extChartAt I α).symm y) : E →L[ℝ] E →L[ℝ] ℝ)
      ((mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y : E →L[ℝ] E) a)
      ((mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y : E →L[ℝ] E) a)
    rw [hid a]
    exact hpos
  have hR : b y (DifferentialGeometry.MetricKoszul.raisedKoszulOp (b y) (fderiv ℝ b y) v v) =
      koszulCov (fderiv ℝ b y) v v := by
    rw [raisedKoszulOp_eq hco, apply_koszul_vec]
  have hΓ := hco.bilin_injective (hR.trans hK.symm)
  change metricSpray b (y, v) = (v, -_)
  rw [metricSpray]
  exact Prod.ext rfl (congrArg Neg.neg hΓ)

/-- Function form of `geodesicSpray_eq_geodesicVectorField`. -/
theorem geodesicSpray_eq_geodesicVectorField_fun
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) :
    g.geodesicSpray = geodesicVectorField g :=
  funext (geodesicSpray_eq_geodesicVectorField g)

/-- An open preconnected set of times containing `0` and `t` contains an open interval around
both. -/
theorem exists_Ioo_subset_of_isOpen_isPreconnected {J : Set ℝ} (hJ : IsOpen J)
    (hJc : IsPreconnected J) {t : ℝ} (h0 : (0 : ℝ) ∈ J) (ht : t ∈ J) :
    ∃ a b : ℝ, Ioo a b ⊆ J ∧ (0 : ℝ) ∈ Ioo a b ∧ t ∈ Ioo a b := by
  have hmin : min 0 t ∈ J := by
    rcases le_total 0 t with h | h
    · rwa [min_eq_left h]
    · rwa [min_eq_right h]
  have hmax : max 0 t ∈ J := by
    rcases le_total 0 t with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ.mem_nhds hmin)
  obtain ⟨l', u', ⟨hl', hu'⟩, hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ.mem_nhds hmax)
  have ha : (l + min 0 t) / 2 ∈ J :=
    hsub ⟨by linarith, by linarith [min_le_max (a := (0 : ℝ)) (b := t)]⟩
  have hb : (max 0 t + u') / 2 ∈ J :=
    hsub' ⟨by linarith [min_le_max (a := (0 : ℝ)) (b := t)], by linarith⟩
  refine ⟨(l + min 0 t) / 2, (max 0 t + u') / 2, fun s hs => ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact hJc.ordConnected.out ha hb ⟨hs.1.le, hs.2.le⟩
  · linarith [min_le_left (0 : ℝ) t]
  · linarith [le_max_left (0 : ℝ) t]
  · linarith [min_le_right (0 : ℝ) t]
  · linarith [le_max_right (0 : ℝ) t]

variable [T2Space M]

/-- The orbit of the ported flow of a smooth metric is a smooth-API geodesic with the right
initial data on the whole maximal interval of the flow. -/
theorem isGeodesicOnWithInitial_geodesicFlow
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    IsGeodesicOnWithInitial g (fun s => (g.geodesicFlow (⟨p, v⟩ : TangentBundle I M) s).proj)
      (maximalIntegralCurveInterval g.geodesicSpray (⟨p, v⟩ : TangentBundle I M)) p v := by
  refine ⟨g.geodesicFlow (⟨p, v⟩ : TangentBundle I M), fun _ => rfl,
    g.geodesicFlow_zero (r := ⊤) le_top _, ?_⟩
  rw [← geodesicSpray_eq_geodesicVectorField_fun g]
  exact g.isMIntegralCurveOn_geodesicFlow (r := ⊤) le_top _

/-- The flow domain of the ported flow of a smooth metric is the smooth API's maximal interval. -/
theorem mem_geodesicFlowDomain_iff_mem_maximalGeodesicInterval
    {g : DifferentialGeometry.SmoothRiemannianMetric I M} {p : M} {v : TangentSpace I p}
    {t : ℝ} :
    ((⟨p, v⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain ↔
      t ∈ maximalGeodesicInterval g p v := by
  constructor
  · intro ht
    exact ⟨fun s => (g.geodesicFlow (⟨p, v⟩ : TangentBundle I M) s).proj,
      maximalIntegralCurveInterval g.geodesicSpray (⟨p, v⟩ : TangentBundle I M),
      isOpen_maximalIntegralCurveInterval, isPreconnected_maximalIntegralCurveInterval,
      g.mem_geodesicFlowDomain_zero (r := ⊤) le_top _, ht,
      isGeodesicOnWithInitial_geodesicFlow g p v⟩
  · rintro ⟨γ, J, hJ, hJc, h0, ht, f, -, hf0, hf⟩
    obtain ⟨a, b, hsub, h0ab, htab⟩ := exists_Ioo_subset_of_isOpen_isPreconnected hJ hJc h0 ht
    rw [← geodesicSpray_eq_geodesicVectorField_fun g] at hf
    exact (hf.mono hsub).subset_maximalIntegralCurveInterval h0ab hf0 htab

/-- Along its maximal interval, the projection of the ported flow of a smooth metric is the smooth
API's maximal geodesic. -/
theorem proj_geodesicFlow_eq_maximalGeodesic
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) (p : M) (v : TangentSpace I p)
    {t : ℝ} (ht : ((⟨p, v⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain) :
    (g.geodesicFlow (⟨p, v⟩ : TangentBundle I M) t).proj = maximalGeodesic g p v t :=
  (maximalGeodesic_eqOn g isOpen_maximalIntegralCurveInterval
    isPreconnected_maximalIntegralCurveInterval
    (g.mem_geodesicFlowDomain_zero (r := ⊤) le_top _)
    (isGeodesicOnWithInitial_geodesicFlow g p v) ht).symm

end Bundle.ContMDiffRiemannianMetric
