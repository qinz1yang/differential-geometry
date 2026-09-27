import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Predicates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.FlowBall.Functional

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle Set
open scoped Manifold ContDiff ENNReal

open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

namespace FlowMetricBall

variable {S : SolutionOn (I := I) (M := M) D}
variable {time : RealTimeInterval.FlowTime D}

omit [SigmaCompactSpace M] [T2Space M] in
theorem scalarControlled_of_radius_le
    (B B' : FlowMetricBall S time) (hc : B'.center = B.center)
    (hr : B'.radius ≤ B.radius) (hB : B.IsScalarControlled) :
    B'.IsScalarControlled := by
  intro x hx
  have hxB : x ∈ B.set := by
    change DifferentialGeometry.riemannianEDistOf (I := I)
      (S.base.metric (time : ℝ)) B'.center x < ENNReal.ofReal B'.radius at hx
    change DifferentialGeometry.riemannianEDistOf (I := I)
      (S.base.metric (time : ℝ)) B.center x < ENNReal.ofReal B.radius
    rw [hc] at hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal hr)
  have hs := hB x hxB
  by_cases hR : 0 ≤ S.scalar (time : ℝ) x
  · exact (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ B'.radius_pos.le B.radius_pos.le).2 hr) hR).trans hs
  · exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg B'.radius)
      (le_of_not_ge hR)).trans zero_le_one

theorem exists_scalar_coll_scale
    [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless]
    [T2Space (TangentBundle I M)] [T3Space M] [ConnectedSpace M]
    [CompactSpace M]
    (B : FlowMetricBall S time) (hB : B.IsScalarControlled) :
    ∃ B' : FlowMetricBall S time,
      B'.Nested B ∧ B'.radius ≤ B.radius ∧ B'.IsScalarControlled ∧
      B'.volume.toReal / B'.radius ^ Module.finrank ℝ E ≤
        B.volume.toReal / B.radius ^ Module.finrank ℝ E ∧
      B'.volume.toReal < (2 : ℝ) ^ (Module.finrank ℝ E + 1) *
        (volumeMeasureOn (I := I) (M := M) S.family time
          {x : M | DifferentialGeometry.riemannianEDistOf
            (I := I) (S.base.metric (time : ℝ)) B'.center x <
              ENNReal.ofReal (B'.radius / 2)}).toReal := by
  let n : ℕ := Module.finrank ℝ E
  let V : ℕ → ℝ := fun j => (B.dyadic j).volume.toReal
  let W : ℕ → ℝ := fun j => V j / (B.dyadic j).radius ^ n
  obtain ⟨ε, ρ, hε, hρ, hvol⟩ :=
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.exists_edist_vol
      (I := I) (g := S.base.metric (time : ℝ)) B.center
  have hr_tend : Filter.Tendsto (fun j : ℕ => (B.dyadic j).radius)
      Filter.atTop (nhds 0) := by
    simpa only [dyadic_radius, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
          B.radius
  have hr_small : ∀ᶠ j : ℕ in Filter.atTop, (B.dyadic j).radius ≤ ρ := by
    filter_upwards [hr_tend.eventually_lt_const hρ] with j hj
    exact hj.le
  have hW : ∀ j : ℕ, 0 ≤ W j := by
    intro j
    exact div_nonneg ENNReal.toReal_nonneg (pow_nonneg (B.dyadic j).radius_pos.le _)
  have hlow : ∀ᶠ j : ℕ in Filter.atTop, ε ≤ W j := by
    filter_upwards [hr_small] with j hj
    have hjvol := hvol (B.dyadic j).radius (B.dyadic j).radius_pos hj
    have hjvol' : ε * (B.dyadic j).radius ^ n ≤ V j := by
      simpa only [n, V, FlowMetricBall.volume, FlowMetricBall.set,
        FlowMetricBall.setAt, volumeMeasureOn_eq_metric, SolutionOn.family_metric,
        dyadic, shrink] using hjvol
    exact (le_div_iff₀ (pow_pos (B.dyadic j).radius_pos n)).2 hjvol'
  obtain ⟨j, hjdrop, hjbase⟩ :=
    DifferentialGeometry.Analysis.Calculus.exists_drop_lower W
      (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hW hε hlow
  refine ⟨B.dyadic j, ?_, ?_, ?_, ?_, ?_⟩
  · apply shrink_nested B (by positivity)
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · rw [dyadic_radius]
    exact mul_le_of_le_one_left B.radius_pos.le
      (pow_le_one₀ (by norm_num) (by norm_num))
  · apply scalarControlled_of_radius_le B (B.dyadic j) rfl _ hB
    rw [dyadic_radius]
    exact mul_le_of_le_one_left B.radius_pos.le
      (pow_le_one₀ (by norm_num) (by norm_num))
  · simpa only [W, V, n, dyadic, shrink, pow_zero, one_mul] using hjbase
  · have hrj : 0 < (B.dyadic j).radius := (B.dyadic j).radius_pos
    have hrn : 0 < (B.dyadic j).radius ^ n := pow_pos hrj n
    have hsuc : (B.dyadic (j + 1)).radius ^ n =
        (B.dyadic j).radius ^ n / (2 : ℝ) ^ n := by
      rw [dyadic_succ_radius, div_pow]
    have hdrop : (1 / 2 : ℝ) *
        (V j / (B.dyadic j).radius ^ n) <
          V (j + 1) / ((B.dyadic j).radius ^ n / (2 : ℝ) ^ n) := by
      simpa only [W, hsuc] using hjdrop
    have htwo : 0 < (2 : ℝ) ^ n := by positivity
    have hscaled := mul_lt_mul_of_pos_right hdrop hrn
    have hV : V j < (2 : ℝ) ^ (n + 1) * V (j + 1) := by
      field_simp at hscaled
      rw [pow_succ]
      nlinarith
    rw [← dyadic_succ_radius]
    change V j < (2 : ℝ) ^ (n + 1) * V (j + 1)
    exact hV

end FlowMetricBall

end

end DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.PDE.RicciFlow.Entropy

open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [T2Space M] [CompactSpace M] [I.Boundaryless]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem cutoff_grad_le
    {r C : ℝ} {V H : ℝ≥0∞} (hr : 0 < r)
    (hHr : 0 < H.toReal)
    (hVH : V.toReal < C * H.toReal) :
    4 * r ^ 2 *
        ((ENNReal.ofReal (5 / r) * V ^ (1 / 2 : ℝ)).toReal /
          ((H ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2 ≤ 400 * C := by
  have hrootV : (V ^ (1 / 2 : ℝ)).toReal = Real.sqrt V.toReal := by
    rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  have hrootH : (H ^ (1 / 2 : ℝ)).toReal = Real.sqrt H.toReal := by
    rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  have hsqrtH : 0 < Real.sqrt H.toReal := Real.sqrt_pos.2 hHr
  have hnum : (ENNReal.ofReal (5 / r) * V ^ (1 / 2 : ℝ)).toReal =
      (5 / r) * Real.sqrt V.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hrootV]
  have hden : (H ^ (1 / 2 : ℝ) / 2).toReal =
      Real.sqrt H.toReal / 2 := by
    rw [ENNReal.toReal_div, hrootH]
    norm_num
  have heq :
      4 * r ^ 2 * (((5 / r) * Real.sqrt V.toReal) /
          (Real.sqrt H.toReal / 2)) ^ 2 = 400 * (V.toReal / H.toReal) := by
    field_simp [hr.ne', hsqrtH.ne']
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt hHr.le]
    ring
  rw [hnum, hden, heq]
  exact mul_le_mul_of_nonneg_left
    ((div_le_iff₀ hHr).2 hVH.le) (by norm_num)

private theorem scale_scalar_eq {r : ℝ} (hr : 0 < r) :
    r ^ 2 * (1 / r ^ 2) = 1 := by
  field_simp [hr.ne']

private theorem log_scale_eq (n : ℕ) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    Real.log v +
        (Real.log (perelmanDensityPrefactor n (r ^ 2)) - (n : ℝ)) =
      Real.log (v / r ^ n) +
        (-(n : ℝ) / 2) * Real.log (4 * Real.pi) - (n : ℝ) := by
  rw [log_prefactor n (sq_pos_of_pos hr)]
  rw [Real.log_div hv.ne' (pow_ne_zero n hr.ne')]
  rw [Real.log_mul (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (pow_ne_zero 2 hr.ne')]
  rw [Real.log_pow, Real.log_pow]
  push_cast
  ring


theorem flowball_wform_of_scalar_controlled
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsScalarControlled) (C : ℝ) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧ support v ⊆ B.set ∧
      (∫ x, v x ^ 2
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          I M (S.base.metric time))) = 1 ∧
      Integrable (fun x => (S.base.metric time).inner x
        (DifferentialGeometry.Geometry.Operator.gradFun
          (I := I) (S.base.metric time) v x)
        (DifferentialGeometry.Geometry.Operator.gradFun
          (I := I) (S.base.metric time) v x))
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          I M (S.base.metric time)) ∧
      (∫ x, 4 * B.radius ^ 2 *
            (S.base.metric time).inner x
              (DifferentialGeometry.Geometry.Operator.gradFun
                (I := I) (S.base.metric time) v x)
              (DifferentialGeometry.Geometry.Operator.gradFun
                (I := I) (S.base.metric time) v x) +
          B.radius ^ 2 *
            DifferentialGeometry.Geometry.Curvature.metricScalarAt
              (I := I) (M := M) (S.base.metric time) x * v x ^ 2 -
          v x ^ 2 * Real.log (v x ^ 2) + C * v x ^ 2
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          I M (S.base.metric time))) ≤
        4 * B.radius ^ 2 *
            ((ENNReal.ofReal (5 / B.radius) * B.volume ^ (1 / 2 : ℝ)).toReal /
              (((DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                  I M (S.base.metric time)
                  {x | DifferentialGeometry.riemannianEDistOf
                    (I := I) (S.base.metric time) B.center x <
                      ENNReal.ofReal (B.radius / 2)}) ^
                    (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
          B.radius ^ 2 *
            (1 / B.radius ^ 2) +
          Real.log B.volume.toReal + C := by
  let R : M → ℝ := fun x =>
    DifferentialGeometry.Geometry.Curvature.metricScalarAt
      (I := I) (M := M) (S.base.metric time) x
  have hRcont : Continuous R := by
    simpa only [R] using
      (DifferentialGeometry.Geometry.Curvature.metricScalar_smooth
        (I := I) (M := M) (S.base.metric time)).continuous
  have hR : ∀ x, x ∈ B.set →
      R x ≤ 1 / B.radius ^ 2 := by
    intro x hx
    have hs := hB x hx
    change B.radius ^ 2 * R x ≤ 1 at hs
    exact (le_div_iff₀ (sq_pos_of_pos B.radius_pos)).2 (by nlinarith)
  have hw := DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.exists_cutoff_wform
    (I := I) (M := M) (S.base.metric time) B.center B.radius_pos
    (R := R) hRcont (tau := B.radius ^ 2)
    (K := 1 / B.radius ^ 2)
    (C := C) (sq_nonneg B.radius)
    (fun x hx => hR x hx)
  simpa only [R, FlowMetricBall.set, FlowMetricBall.setAt,
    FlowMetricBall.volume,
    DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric,
    SolutionOn.family_metric] using hw


theorem flowball_w_upper_of_scalar_controlled
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsScalarControlled)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ w ∧ (∀ x : M, 0 < w x) ∧
      (∫ x, w x ^ 2
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          I M (S.base.metric time))) = 1 ∧
      wFunctional
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
            I M (S.base.metric time))
          (Module.finrank ℝ E) (B.radius ^ 2)
          (fun x => DifferentialGeometry.Geometry.Curvature.metricScalarAt
            (I := I) (M := M) (S.base.metric time) x)
          (fun x => (S.base.metric time).inner x
            (gradientFun (I := I) (S.base.metric time)
              (perelmanPotential (Module.finrank ℝ E) (B.radius ^ 2)
                (fun y => w y * w y)) x)
            (gradientFun (I := I) (S.base.metric time)
              (perelmanPotential (Module.finrank ℝ E) (B.radius ^ 2)
                (fun y => w y * w y)) x))
          (perelmanPotential (Module.finrank ℝ E) (B.radius ^ 2)
            (fun y => w y * w y)) ≤
        4 * B.radius ^ 2 *
            ((ENNReal.ofReal (5 / B.radius) * B.volume ^ (1 / 2 : ℝ)).toReal /
              (((DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                  I M (S.base.metric time)
                  {x | DifferentialGeometry.riemannianEDistOf
                    (I := I) (S.base.metric time) B.center x <
                      ENNReal.ofReal (B.radius / 2)}) ^
                    (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
          B.radius ^ 2 *
            (1 / B.radius ^ 2) +
          Real.log B.volume.toReal +
          (Real.log (perelmanDensityPrefactor
            (Module.finrank ℝ E) (B.radius ^ 2)) - (Module.finrank ℝ E : ℝ)) + δ := by
  let : Nonempty M := ⟨B.center⟩
  let g : SmoothRiemannianMetric I M := S.base.metric time
  let μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g
  let n : ℕ := Module.finrank ℝ E
  let tau : ℝ := B.radius ^ 2
  let R : M → ℝ := fun x =>
    DifferentialGeometry.Geometry.Curvature.metricScalarAt
      (I := I) (M := M) g x
  let C₀ : ℝ := Real.log (perelmanDensityPrefactor n tau) - (n : ℝ)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact sq_pos_of_pos B.radius_pos
  have hRcont : Continuous R := by
    simpa only [R] using
      (DifferentialGeometry.Geometry.Curvature.metricScalar_smooth
        (I := I) (M := M) g).continuous
  obtain ⟨v, hv, _hvsupp, hvmass, hvgradi, hvupper⟩ :=
    flowball_wform_of_scalar_controlled (I := I) (M := M) B hB C₀
  have hvgradi' : Integrable (fun x => g.inner x
      (gradientFun (I := I) g v x) (gradientFun (I := I) g v x)) μ := by
    simpa only [g, μ, gradient_eq_gradFun] using hvgradi
  have hvmass' : (∫ x, v x ^ 2 ∂μ) = 1 := by
    simpa only [g, μ] using hvmass
  obtain ⟨w, hw, hwpos, hwmass, hwapprox⟩ :=
    exists_pos_wform (I := I) (M := M) g hv hvmass' hvgradi'
      hRcont (tau := tau) (C := C₀) (δ := δ) htau.le hδ
  refine ⟨w, hw, hwpos, ?_, ?_⟩
  · simpa only [g, μ] using hwmass
  · have hvsquare :
        (∫ x, 4 * tau * g.inner x
              (gradientFun (I := I) g v x) (gradientFun (I := I) g v x) +
            tau * R x * v x ^ 2 - v x ^ 2 * Real.log (v x ^ 2) + C₀ * v x ^ 2
          ∂μ) ≤
          4 * B.radius ^ 2 *
              ((ENNReal.ofReal (5 / B.radius) * B.volume ^ (1 / 2 : ℝ)).toReal /
                (((DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                    I M (S.base.metric time)
                    {x | DifferentialGeometry.riemannianEDistOf
                      (I := I) (S.base.metric time) B.center x <
                        ENNReal.ofReal (B.radius / 2)}) ^
                      (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
            B.radius ^ 2 *
              (1 / B.radius ^ 2) +
            Real.log B.volume.toReal + C₀ := by
      simpa only [g, μ, tau, R, gradient_eq_gradFun] using hvupper
    rw [w_square_form μ g n htau R hw hwpos]
    calc
      (∫ x, 4 * tau * g.inner x
            (gradientFun (I := I) g w x) (gradientFun (I := I) g w x) +
          tau * R x * (w x * w x) - (w x * w x) * Real.log (w x * w x) +
          (Real.log (perelmanDensityPrefactor n tau) - (n : ℝ)) * (w x * w x) ∂μ) ≤
          (∫ x, 4 * tau * g.inner x
                (gradientFun (I := I) g v x) (gradientFun (I := I) g v x) +
              tau * R x * v x ^ 2 - v x ^ 2 * Real.log (v x ^ 2) + C₀ * v x ^ 2
            ∂μ) + δ := by
        simpa only [pow_two, C₀] using hwapprox
      _ ≤ (4 * B.radius ^ 2 *
              ((ENNReal.ofReal (5 / B.radius) * B.volume ^ (1 / 2 : ℝ)).toReal /
                (((DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                    I M (S.base.metric time)
                    {x | DifferentialGeometry.riemannianEDistOf
                      (I := I) (S.base.metric time) B.center x <
                        ENNReal.ofReal (B.radius / 2)}) ^
                      (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
            B.radius ^ 2 *
              (1 / B.radius ^ 2) +
            Real.log B.volume.toReal + C₀) + δ :=
        by linarith
      _ = _ := by rfl


def scalarCollapseWConst (n : ℕ) : ℝ :=
  400 * (2 : ℝ) ^ (n + 1) + (1 : ℝ) +
    (-(n : ℝ) / 2) * Real.log (4 * Real.pi) - (n : ℝ)

theorem exists_scalar_controlled_w_bound
    [CompleteSpace E] [T2Space (TangentBundle I M)] [T3Space M]
    [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsScalarControlled)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (B' : FlowMetricBall S time) (w : M → ℝ),
      B'.Nested B ∧ B'.radius ≤ B.radius ∧ B'.IsScalarControlled ∧
      B'.volume.toReal / B'.radius ^ Module.finrank ℝ E ≤
        B.volume.toReal / B.radius ^ Module.finrank ℝ E ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ w ∧ (∀ x : M, 0 < w x) ∧
      (∫ x, w x ^ 2
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          I M (S.base.metric time))) = 1 ∧
      wFunctional
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
            I M (S.base.metric time))
          (Module.finrank ℝ E) (B'.radius ^ 2)
          (fun x => DifferentialGeometry.Geometry.Curvature.metricScalarAt
            (I := I) (M := M) (S.base.metric time) x)
          (fun x => (S.base.metric time).inner x
            (gradientFun (I := I) (S.base.metric time)
              (perelmanPotential (Module.finrank ℝ E) (B'.radius ^ 2)
                (fun y => w y * w y)) x)
            (gradientFun (I := I) (S.base.metric time)
              (perelmanPotential (Module.finrank ℝ E) (B'.radius ^ 2)
                (fun y => w y * w y)) x))
          (perelmanPotential (Module.finrank ℝ E) (B'.radius ^ 2)
            (fun y => w y * w y)) ≤
        scalarCollapseWConst (Module.finrank ℝ E) +
          Real.log (B.volume.toReal / B.radius ^ Module.finrank ℝ E) + δ := by
  let n : ℕ := Module.finrank ℝ E
  obtain ⟨B', hnest, hrle, hB', hnorm, hdouble⟩ :=
    FlowMetricBall.exists_scalar_coll_scale (I := I) (M := M) (S := S) (time := time) B hB
  obtain ⟨w, hw, hwpos, hwmass, hwupper⟩ :=
    flowball_w_upper_of_scalar_controlled (I := I) (M := M) B' hB' hδ
  let H : ℝ≥0∞ :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
      I M (S.base.metric time)
      {x : M | DifferentialGeometry.riemannianEDistOf
        (I := I) (S.base.metric time) B'.center x < ENNReal.ofReal (B'.radius / 2)}
  have hHr : 0 < H.toReal := by
    simpa only [H] using edist_vol_pos (I := I) (M := M)
      (S.base.metric time) B'.center (half_pos B'.radius_pos)
  have hgrad :
      4 * B'.radius ^ 2 *
          ((ENNReal.ofReal (5 / B'.radius) * B'.volume ^ (1 / 2 : ℝ)).toReal /
            ((H ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2 ≤
        400 * (2 : ℝ) ^ (n + 1) := by
    exact cutoff_grad_le B'.radius_pos hHr (by
      simpa only [n, H,
        DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric,
        SolutionOn.family_metric] using hdouble)
  have hcurv := scale_scalar_eq B'.radius_pos
  have hB'vol : 0 < B'.volume.toReal := by
    simpa only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
      DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric,
      SolutionOn.family_metric] using
        edist_vol_pos (I := I) (M := M) (S.base.metric time) B'.center B'.radius_pos
  have hBvol : 0 < B.volume.toReal := by
    simpa only [FlowMetricBall.volume, FlowMetricBall.set, FlowMetricBall.setAt,
      DifferentialGeometry.Integral.Measure.volumeMeasureOn_eq_metric,
      SolutionOn.family_metric] using
        edist_vol_pos (I := I) (M := M) (S.base.metric time) B.center B.radius_pos
  have hnorm' : 0 < B'.volume.toReal / B'.radius ^ n :=
    div_pos hB'vol (pow_pos B'.radius_pos n)
  have hlog : Real.log (B'.volume.toReal / B'.radius ^ n) ≤
      Real.log (B.volume.toReal / B.radius ^ n) := by
    exact Real.log_le_log hnorm' (by simpa only [n] using hnorm)
  have hscale := log_scale_eq n B'.radius_pos hB'vol
  refine ⟨B', w, hnest, hrle, hB', hnorm, hw, hwpos, hwmass, ?_⟩
  calc
    wFunctional
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
            I M (S.base.metric time)) n (B'.radius ^ 2)
          (fun x => DifferentialGeometry.Geometry.Curvature.metricScalarAt
            (I := I) (M := M) (S.base.metric time) x)
          (fun x => (S.base.metric time).inner x
            (gradientFun (I := I) (S.base.metric time)
              (perelmanPotential n (B'.radius ^ 2) (fun y => w y * w y)) x)
            (gradientFun (I := I) (S.base.metric time)
              (perelmanPotential n (B'.radius ^ 2) (fun y => w y * w y)) x))
          (perelmanPotential n (B'.radius ^ 2) (fun y => w y * w y))
        ≤ 4 * B'.radius ^ 2 *
              ((ENNReal.ofReal (5 / B'.radius) * B'.volume ^ (1 / 2 : ℝ)).toReal /
                ((H ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
            B'.radius ^ 2 * (1 / B'.radius ^ 2) +
            Real.log B'.volume.toReal +
            (Real.log (perelmanDensityPrefactor n (B'.radius ^ 2)) - (n : ℝ)) + δ := by
          simpa only [n, H] using hwupper
    _ ≤ 400 * (2 : ℝ) ^ (n + 1) + (1 : ℝ) +
          Real.log (B'.volume.toReal / B'.radius ^ n) +
          (-(n : ℝ) / 2) * Real.log (4 * Real.pi) - (n : ℝ) + δ := by
        rw [hcurv]
        calc
          4 * B'.radius ^ 2 *
                ((ENNReal.ofReal (5 / B'.radius) * B'.volume ^ (1 / 2 : ℝ)).toReal /
                  ((H ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
              (1 : ℝ) + Real.log B'.volume.toReal +
              (Real.log (perelmanDensityPrefactor n (B'.radius ^ 2)) - (n : ℝ)) + δ =
            4 * B'.radius ^ 2 *
                ((ENNReal.ofReal (5 / B'.radius) * B'.volume ^ (1 / 2 : ℝ)).toReal /
                  ((H ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
              (1 : ℝ) +
              (Real.log (B'.volume.toReal / B'.radius ^ n) +
                (-(n : ℝ) / 2) * Real.log (4 * Real.pi) - (n : ℝ)) + δ := by
                  linarith
          _ ≤ 400 * (2 : ℝ) ^ (n + 1) + (1 : ℝ) +
                Real.log (B'.volume.toReal / B'.radius ^ n) +
                (-(n : ℝ) / 2) * Real.log (4 * Real.pi) - (n : ℝ) + δ := by
                  linarith
    _ ≤ scalarCollapseWConst n +
          Real.log (B.volume.toReal / B.radius ^ n) + δ := by
        unfold scalarCollapseWConst
        linarith
    _ = scalarCollapseWConst (Module.finrank ℝ E) +
          Real.log (B.volume.toReal / B.radius ^ Module.finrank ℝ E) + δ := rfl

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
