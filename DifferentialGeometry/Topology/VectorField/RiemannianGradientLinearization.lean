import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Topology.VectorField.VerticalLinearization
import DifferentialGeometry.Topology.Manifold.InteriorChart

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
  DifferentialGeometry.Tensor.Coordinates
namespace Poincare.VectorField
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]


def gradientInChart (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) (y : E) : E :=
  (trivializationAt E (TangentSpace I) x
    ⟨(extChartAt I x).symm y, gradientFun g f ((extChartAt I x).symm y)⟩).2


theorem metricFlat_gradientInChart (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : M} {y : E} (hy : y ∈ interior (extChartAt I x).target)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I x).symm y)) :
    metricFlatModelInChart g x y (gradientInChart g f x y) =
      fderiv ℝ (fun z => f ((extChartAt I x).symm z)) y := by
  let c := Poincare.Manifold.interiorChart I ∞ x
  have hc : y ∈ c.symm.source := hy
  have hy' : (extChartAt I x).symm y ∈ (chartAt H x).source :=
    (c.map_target hy).1
  have hty : extChartAt I x ((extChartAt I x).symm y) = y :=
    (extChartAt I x).right_inv (interior_subset hy)
  have hrange : range I ∈ 𝓝 y := mem_of_superset
    (isOpen_interior.mem_nhds hy) (interior_subset.trans (extChartAt_target_subset_range x))
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm y :=
    (c.symm.contMDiffOn_toFun.contMDiffAt (c.symm.open_source.mem_nhds hc)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp y hf hsymm
  ext w
  rw [← hty, flatChart_apply g x (show (extChartAt I x).symm y ∈ coordinateFrameSet x by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hy')]
  rw [hty]
  have hcancel : (trivializationAt E (TangentSpace I) x).symmL ℝ ((extChartAt I x).symm y)
      (gradientInChart g f x y) = gradientFun g f ((extChartAt I x).symm y) := by
    have hb : (extChartAt I x).symm y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hy'
    have hh := Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (trivializationAt E (TangentSpace I) x) hb (gradientFun g f ((extChartAt I x).symm y))
    simpa only [Trivialization.continuousLinearMapAt_apply,
      (trivializationAt E (TangentSpace I) x).coe_linearMapAt_of_mem (R := ℝ) hb,
      gradientInChart] using hh
  rw [hcancel, inner_gradientFun, TangentBundle.symmL_trivializationAt hy', hty,
    mfderivWithin_of_mem_nhds hrange]
  have hh := congrArg (fun L => L w) hcomp
  simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, mvfderiv] using! hh.symm


theorem contDiffAt_gradientInChart (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : M} (hx : I.IsInteriorPoint x)
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x) :
    ContDiffAt ℝ ∞ (gradientInChart g f x) (extChartAt I x x) := by
  have hc := gradientFun_contMDiffAt g hf
  rw [contMDiffAt_section] at hc
  have hs := (contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x).contMDiffAt
    (range_mem_nhds_isInteriorPoint hx)
  have hc' : ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun y => (trivializationAt E (TangentSpace I) x ⟨y, gradientFun g f y⟩).2)
      ((extChartAt I x).symm (extChartAt I x x)) := by
    simpa only [extChartAt_to_inv] using hc
  exact (hc'.comp (extChartAt I x x) hs).contDiffAt


theorem gradientInChart_center_zero (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : M} (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    gradientInChart g f x (extChartAt I x x) = 0 := by
  rw [gradientInChart, (extChartAt I x).left_inv (mem_extChartAt_source x)]
  rw [gradientFun_eq_zero_of_mfderiv_eq_zero g f hcrit]
  change tangentCoordChange I x x x 0 = 0
  exact map_zero _


theorem linearizationAtZero_gradientFun_eq_fderivInChart
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    linearizationAtZero ((gradientFun_contMDiffAt g hf).mdifferentiableAt (by simp))
        (gradientFun_eq_zero_of_mfderiv_eq_zero g f hcrit) =
      fderiv ℝ (gradientInChart g f x) (extChartAt I x x) := by
  rw [linearizationAtZero_eq_fderivWithin]
  exact fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hx)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem contDiffAt_scalarInChart {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x) :
    ContDiffAt ℝ ∞ (fun z => f ((extChartAt I x).symm z)) (extChartAt I x x) := by
  have hs := (contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x).contMDiffAt
    (range_mem_nhds_isInteriorPoint hx)
  have hf' : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f ((extChartAt I x).symm (extChartAt I x x)) := by
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact hf
  exact (hf'.comp (extChartAt I x x) hs).contDiffAt


theorem metricFlat_comp_fderiv_gradientInChart
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    (metricFlatContinuousEquiv g x).toContinuousLinearMap ∘L
        fderiv ℝ (gradientInChart g f x) (extChartAt I x x) =
      fderiv ℝ (fderiv ℝ (fun z => f ((extChartAt I x).symm z))) (extChartAt I x x) := by
  have hrange := range_mem_nhds_isInteriorPoint hx
  have hB := ((metricFlatModelInChart_contDiffWithinAt g x).contDiffAt hrange).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hZ := (contDiffAt_gradientInChart g hx hf).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hprod := (hB.hasFDerivAt.clm_apply hZ.hasFDerivAt).fderiv
  rw [gradientInChart_center_zero g hcrit, map_zero, add_zero,
    metricFlatModelInChart_center_eq] at hprod
  have heq : (fun y => metricFlatModelInChart g x y (gradientInChart g f x y)) =ᶠ[𝓝 (extChartAt I x x)]
      fderiv ℝ (fun z => f ((extChartAt I x).symm z)) := by
    obtain ⟨u, hu, hfu⟩ := (contMDiffAt_iff_contMDiffOn_nhds
      (show (1 : ℕ∞ω) ≠ ∞ by norm_num)).mp (hf.of_le (by simp))
    obtain ⟨v, hvu, hv, hxv⟩ := mem_nhds_iff.mp hu
    have hfd : ∀ᶠ z in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f z := by
      filter_upwards [hv.mem_nhds hxv] with z hz
      exact (hfu.contMDiffAt (mem_of_superset (hv.mem_nhds hz) hvu)).mdifferentiableAt one_ne_zero
    have hs := (contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x).contMDiffAt hrange
    have hs' : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
      simpa only [ContinuousAt, (extChartAt I x).left_inv (mem_extChartAt_source x)] using hs.continuousAt
    filter_upwards [isOpen_interior.mem_nhds (I.isInteriorPoint_iff.mp hx), hs'.eventually hfd]
      with y hy hfy
    exact metricFlat_gradientInChart g hy hfy
  exact hprod.symm.trans heq.fderiv_eq


theorem metricFlatContinuousEquiv_apply_self
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    metricFlatContinuousEquiv g x v w = g.inner x v w := by
  erw [metricFlatContinuousEquiv_apply,
    TangentBundle.symmL_trivializationAt (mem_chart_source H x),
    mfderivWithin_range_extChartAt_symm]
  rfl


theorem metric_inner_linearizationAtZero_gradientFun
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0) (v w : TangentSpace I x) :
    g.inner x (linearizationAtZero
      ((gradientFun_contMDiffAt g hf).mdifferentiableAt (by simp))
      (gradientFun_eq_zero_of_mfderiv_eq_zero g f hcrit) v) w =
      fderiv ℝ (fderiv ℝ (fun z => f ((extChartAt I x).symm z))) (extChartAt I x x) v w := by
  erw [linearizationAtZero_gradientFun_eq_fderivInChart g hx hf hcrit]
  rw [← metricFlatContinuousEquiv_apply_self]
  exact congrArg (fun L => L v w) (metricFlat_comp_fderiv_gradientInChart g hx hf hcrit)


theorem linearizationAtZero_gradientFun_eq_metricSharp_hessian
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    linearizationAtZero ((gradientFun_contMDiffAt g hf).mdifferentiableAt (by simp))
        (gradientFun_eq_zero_of_mfderiv_eq_zero g f hcrit) =
      (metricFlatContinuousEquiv g x).symm.toContinuousLinearMap ∘L
        fderiv ℝ (fderiv ℝ (fun z => f ((extChartAt I x).symm z))) (extChartAt I x x) := by
  erw [linearizationAtZero_gradientFun_eq_fderivInChart g hx hf hcrit]
  ext v
  apply (metricFlatContinuousEquiv g x).injective
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (fun L => L v) (metricFlat_comp_fderiv_gradientInChart g hx hf hcrit)

theorem linearizationAtZero_gradientFun_apply_metricSharp
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hx : I.IsInteriorPoint x) (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0) (v : TangentSpace I x) :
    linearizationAtZero ((gradientFun_contMDiffAt g hf).mdifferentiableAt (by simp))
        (gradientFun_eq_zero_of_mfderiv_eq_zero g f hcrit) v =
      metricSharp g x
        (fderiv ℝ (fderiv ℝ (fun z => f ((extChartAt I x).symm z)))
          (extChartAt I x x) v).toLinearMap := by
  apply (metricFlatEquiv g x).injective
  ext w
  erw [metricFlatEquiv_apply, metricFlatEquiv_apply, inner_metricSharp,
    metric_inner_linearizationAtZero_gradientFun g hx hf hcrit]
  rfl

end Poincare.VectorField
