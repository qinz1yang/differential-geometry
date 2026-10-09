import DifferentialGeometry.Geometry.Geodesic.Equation.FiniteMetric
import DifferentialGeometry.External.TauCeti.Geometry.Manifold.IntegralCurve.Flow

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def geodesicFlow {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (p : TangentBundle I M) (t : ℝ) : TangentBundle I M :=
  maximalIntegralCurve g.geodesicSpray p t

def geodesicFlowDomain {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    Set (TangentBundle I M × ℝ) :=
  TauCeti.maximalIntegralCurveFlowDomain g.geodesicSpray

omit [I.Boundaryless] in
theorem mem_geodesicFlowDomain_zeroSection {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (x : M) (t : ℝ) :
    ((⟨x, 0⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain := by
  have hγ := (isMIntegralCurve_const (g.geodesicSpray_zero x)).isMIntegralCurveOn
    (Ioo (-(|t| + 1)) (|t| + 1))
  exact hγ.subset_maximalIntegralCurveInterval
    ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩ rfl
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

variable [T2Space M] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

theorem isOpen_geodesicFlowDomain (hr : 1 ≤ r) : IsOpen g.geodesicFlowDomain := by
  exact TauCeti.isOpen_maximalIntegralCurveFlowDomain
    (g.contMDiff_geodesicSpray.of_le (by exact_mod_cast hr))

theorem contMDiffOn_geodesicFlow (hr : 1 ≤ r) :
    ContMDiffOn (I.tangent.prod 𝓘(ℝ, ℝ)) I.tangent r
      (fun p : TangentBundle I M × ℝ => g.geodesicFlow p.1 p.2)
      g.geodesicFlowDomain := by
  exact TauCeti.contMDiffOn_maximalIntegralCurve hr g.contMDiff_geodesicSpray

omit [T2Space M] in
theorem mem_geodesicFlowDomain_zero (hr : 1 ≤ r) (p : TangentBundle I M) :
    (p, 0) ∈ g.geodesicFlowDomain := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact zero_mem_maximalIntegralCurveInterval
    (g.contMDiff_geodesicSpray.of_le (by exact_mod_cast hr)).contMDiffAt

omit [T2Space M] in
@[simp]
theorem geodesicFlow_zero (hr : 1 ≤ r) (p : TangentBundle I M) :
    g.geodesicFlow p 0 = p :=
  maximalIntegralCurve_zero (g.mem_geodesicFlowDomain_zero hr p)

theorem geodesicFlow_add (hr : 1 ≤ r) {p : TangentBundle I M} {s t : ℝ}
    (ht : (p, t) ∈ g.geodesicFlowDomain)
    (hts : (p, t + s) ∈ g.geodesicFlowDomain) :
    g.geodesicFlow p (t + s) = g.geodesicFlow (g.geodesicFlow p t) s :=
  TauCeti.maximalIntegralCurve_add
    (g.contMDiff_geodesicSpray.of_le (by exact_mod_cast hr)) ht hts

@[simp]
theorem geodesicFlow_zeroSection (hr : 1 ≤ r) (x : M) (t : ℝ) :
    g.geodesicFlow (⟨x, 0⟩ : TangentBundle I M) t = ⟨x, 0⟩ := by
  have hγ := (isMIntegralCurve_const (g.geodesicSpray_zero x)).isMIntegralCurveOn
    (Ioo (-(|t| + 1)) (|t| + 1))
  exact hγ.eqOn_maximalIntegralCurve
    (g.contMDiff_geodesicSpray.of_le (by exact_mod_cast hr))
    ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩ rfl
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

theorem isMIntegralCurveOn_geodesicFlow (hr : 1 ≤ r) (p : TangentBundle I M) :
    IsMIntegralCurveOn (g.geodesicFlow p) g.geodesicSpray
      (maximalIntegralCurveInterval g.geodesicSpray p) :=
  isMIntegralCurveOn_maximalIntegralCurve
    (g.contMDiff_geodesicSpray.of_le (by exact_mod_cast hr))

theorem hasMFDerivAt_geodesicFlow_proj (hr : 1 ≤ r) {p : TangentBundle I M} {t : ℝ}
    (ht : (p, t) ∈ g.geodesicFlowDomain) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (g.geodesicFlow p s).proj) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p t).snd) := by
  have hcurve := (g.isMIntegralCurveOn_geodesicFlow hr p t ht).hasMFDerivAt
    (isOpen_maximalIntegralCurveInterval.mem_nhds ht)
  have hproj := (Bundle.mdifferentiable_proj (TangentSpace I) (g.geodesicFlow p t)).hasMFDerivAt.comp t hcurve
  have hder :
      (mfderiv I.tangent I (TotalSpace.proj : TangentBundle I M → M)
        (g.geodesicFlow p t)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicSpray (g.geodesicFlow p t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p t).snd := by
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
      ContinuousLinearMap.comp_toSpanSingleton, g.mfderiv_proj_geodesicSpray]
  exact hproj.congr_mfderiv hder

local instance : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

theorem hasDerivAt_geodesicFlow_chart
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) {p : TangentBundle I M} {t : ℝ}
    (ht : (p, t) ∈ g.geodesicFlowDomain) (q : TangentBundle I M)
    (hq : (g.geodesicFlow p t).proj ∈ (chartAt H q.proj).source) :
    HasDerivAt (fun s => extChartAt I.tangent q (g.geodesicFlow p s))
      (DifferentialGeometry.MetricKoszul.metricSpray
        (fun x => (g.inner ((extChartAt I q.proj).symm x) :
          E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (E := E) (F := E) (E' := E) (F' := E)
          (mfderiv 𝓘(ℝ, E) I (extChartAt I q.proj).symm x : E →L[ℝ] E)
            (mfderiv 𝓘(ℝ, E) I (extChartAt I q.proj).symm x : E →L[ℝ] E))
        (extChartAt I.tangent q (g.geodesicFlow p t))) t := by
  have hqT : g.geodesicFlow p t ∈ (chartAt (ModelProd H E) q).source := by
    simpa only [TangentBundle.mem_chart_source_iff] using hq
  have hcurve := (g.isMIntegralCurveOn_geodesicFlow hr p t ht).hasMFDerivAt
    (isOpen_maximalIntegralCurveInterval.mem_nhds ht)
  have hchart := TauCeti.Manifold.hasDerivAt_comp_curve
    (mdifferentiableAt_extChartAt (I := I.tangent) hqT) hcurve
  change HasDerivAt (fun s => extChartAt I.tangent q (g.geodesicFlow p s))
    (mfderiv I.tangent 𝓘(ℝ, E × E) (extChartAt I.tangent q) (g.geodesicFlow p t)
      (g.geodesicSpray (g.geodesicFlow p t))) t at hchart
  rwa [g.mfderiv_geodesicSpray_chart
    (le_add_of_nonneg_left (show (0 : ℕ∞ω) ≤ r from zero_le)) q (g.geodesicFlow p t) hq] at hchart


end Bundle.ContMDiffRiemannianMetric

end
