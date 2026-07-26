import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CutoffW
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CurvatureBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.PositiveApprox
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CollapseScale
import DifferentialGeometry.Geometry.Comparison.Volume.SmallBall

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Cutoff W-form on curvature-controlled flow balls

This file assembles the intrinsic cutoff and curvature trace bounds at the
distinguished time of a genuine `FlowMetricBall`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section

open Bundle Tensor0SBundle MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.PDE.RicciFlow.Entropy
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M]
  [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
  [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The cutoff gradient term is controlled by a real outer/half-volume ratio. -/
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

private theorem scale_curv_eq (n : ℕ) {r : ℝ} (hr : 0 < r) :
    r ^ 2 * ((n : ℝ) ^ 2 * Real.sqrt (1 / r ^ 4)) = (n : ℝ) ^ 2 := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  rw [show r ^ 4 = (r ^ 2) ^ 2 by ring]
  rw [show 1 / (r ^ 2) ^ 2 = (1 / r ^ 2) ^ 2 by field_simp]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hr2)]
  field_simp

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

/-- A curvature-controlled flow ball admits the normalized cutoff square-form
estimate at its distinguished time, with the scalar term controlled directly
by the invariant Riemann norm hypothesis. -/
theorem flowball_wform
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled) (C : ℝ) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧ support v ⊆ B.set ∧
      (∫ x, v x ^ 2
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          I M (S.base.metric time))) = 1 ∧
      Integrable (fun x => (S.base.metric time).inner x
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) (S.base.metric time) v x)
        (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
          (I := I) (S.base.metric time) v x))
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          I M (S.base.metric time)) ∧
      (∫ x, 4 * B.radius ^ 2 *
            (S.base.metric time).inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) (S.base.metric time) v x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun
                (I := I) (S.base.metric time) v x) +
          B.radius ^ 2 *
            DifferentialGeometry.Integral.Connection.metricScalarAt
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
            ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (1 / B.radius ^ 4)) +
          Real.log B.volume.toReal + C := by
  have htime : (time : ℝ) ∈
      Set.Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) := by
    constructor
    · linarith [sq_nonneg B.radius]
    · exact le_rfl
  let R : M → ℝ := fun x =>
    DifferentialGeometry.Integral.Connection.metricScalarAt
      (I := I) (M := M) (S.base.metric time) x
  have hRcont : Continuous R := by
    simpa only [R] using
      (DifferentialGeometry.Integral.Connection.metricScalar_smooth
        (I := I) (M := M) (S.base.metric time)).continuous
  have hR : ∀ x, x ∈ B.set →
      R x ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (1 / B.radius ^ 4) := by
    intro x hx
    have hs := scalar_le_of_rm (I := I) (M := M) B hB htime hx
    simpa only [R, show Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ E from rfl] using hs
  have hw := DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.exists_cutoff_wform
    (I := I) (M := M) (S.base.metric time) B.center B.radius_pos
    (R := R) hRcont (tau := B.radius ^ 2)
    (K := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (1 / B.radius ^ 4))
    (C := C) (sq_nonneg B.radius)
    (fun x hx => hR x hx)
  simpa only [R, FlowMetricBall.set, FlowMetricBall.setAt,
    FlowMetricBall.volume,
    DifferentialGeometry.Integral.Measure.volumeMeasureOn] using hw

/-- A curvature-controlled flow ball admits a strictly positive unit-mass
amplitude whose actual Perelman W-functional is bounded by the cutoff estimate,
up to an arbitrarily small error. -/
theorem flowball_w_upper
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ w ∧ (∀ x : M, 0 < w x) ∧
      (∫ x, w x ^ 2
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          I M (S.base.metric time))) = 1 ∧
      wFunctional
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
            I M (S.base.metric time))
          (Module.finrank ℝ E) (B.radius ^ 2)
          (fun x => DifferentialGeometry.Integral.Connection.metricScalarAt
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
            ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (1 / B.radius ^ 4)) +
          Real.log B.volume.toReal +
          (Real.log (perelmanDensityPrefactor
            (Module.finrank ℝ E) (B.radius ^ 2)) - (Module.finrank ℝ E : ℝ)) + δ := by
  letI : Nonempty M := ⟨B.center⟩
  let g : SmoothRiemannianMetric I M := S.base.metric time
  let μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g
  let n : ℕ := Module.finrank ℝ E
  let tau : ℝ := B.radius ^ 2
  let R : M → ℝ := fun x =>
    DifferentialGeometry.Integral.Connection.metricScalarAt
      (I := I) (M := M) g x
  let C₀ : ℝ := Real.log (perelmanDensityPrefactor n tau) - (n : ℝ)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact sq_pos_of_pos B.radius_pos
  have hRcont : Continuous R := by
    simpa only [R] using
      (DifferentialGeometry.Integral.Connection.metricScalar_smooth
        (I := I) (M := M) g).continuous
  obtain ⟨v, hv, _hvsupp, hvmass, hvgradi, hvupper⟩ :=
    flowball_wform (I := I) (M := M) B hB C₀
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
              ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (1 / B.radius ^ 4)) +
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
              ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (1 / B.radius ^ 4)) +
            Real.log B.volume.toReal + C₀) + δ :=
        by linarith
      _ = _ := by rfl

/-- The dimension-only constant left after the dyadic cutoff and parabolic
scale cancellations. -/
def collapseWConst (n : ℕ) : ℝ :=
  400 * (2 : ℝ) ^ (n + 1) + (n : ℝ) ^ 2 +
    (-(n : ℝ) / 2) * Real.log (4 * Real.pi) - (n : ℝ)

/-- A curvature-controlled ball admits a selected dyadic subball and a
positive unit-mass test amplitude whose W value is bounded only by the original
normalized volume, a dimension constant, and the chosen approximation error. -/
theorem exists_sel_w_bound
    [CompleteSpace E] [T2Space (TangentBundle I M)] [T3Space M]
    [ConnectedSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    {time : DifferentialGeometry.Integral.Connection.RealTimeInterval.FlowTime D}
    (B : FlowMetricBall S time) (hB : B.IsRmControlled)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (B' : FlowMetricBall S time) (w : M → ℝ),
      B'.Nested B ∧ B'.radius ≤ B.radius ∧ B'.IsRmControlled ∧
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
          (fun x => DifferentialGeometry.Integral.Connection.metricScalarAt
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
        collapseWConst (Module.finrank ℝ E) +
          Real.log (B.volume.toReal / B.radius ^ Module.finrank ℝ E) + δ := by
  let n : ℕ := Module.finrank ℝ E
  obtain ⟨B', hnest, hrle, hB', hnorm, hdouble⟩ :=
    FlowMetricBall.exists_coll_scale (I := I) (M := M) (S := S) (time := time) B hB
  obtain ⟨w, hw, hwpos, hwmass, hwupper⟩ :=
    flowball_w_upper (I := I) (M := M) B' hB' hδ
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
    exact cutoff_grad_le B'.radius_pos hHr (by simpa only [n, H] using hdouble)
  have hcurv := scale_curv_eq n B'.radius_pos
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
          (fun x => DifferentialGeometry.Integral.Connection.metricScalarAt
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
            B'.radius ^ 2 * ((n : ℝ) ^ 2 * Real.sqrt (1 / B'.radius ^ 4)) +
            Real.log B'.volume.toReal +
            (Real.log (perelmanDensityPrefactor n (B'.radius ^ 2)) - (n : ℝ)) + δ := by
          simpa only [n, H] using hwupper
    _ ≤ 400 * (2 : ℝ) ^ (n + 1) + (n : ℝ) ^ 2 +
          Real.log (B'.volume.toReal / B'.radius ^ n) +
          (-(n : ℝ) / 2) * Real.log (4 * Real.pi) - (n : ℝ) + δ := by
        rw [hcurv]
        calc
          4 * B'.radius ^ 2 *
                ((ENNReal.ofReal (5 / B'.radius) * B'.volume ^ (1 / 2 : ℝ)).toReal /
                  ((H ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
              (n : ℝ) ^ 2 + Real.log B'.volume.toReal +
              (Real.log (perelmanDensityPrefactor n (B'.radius ^ 2)) - (n : ℝ)) + δ =
            4 * B'.radius ^ 2 *
                ((ENNReal.ofReal (5 / B'.radius) * B'.volume ^ (1 / 2 : ℝ)).toReal /
                  ((H ^ (1 / 2 : ℝ) / 2).toReal)) ^ 2 +
              (n : ℝ) ^ 2 +
              (Real.log (B'.volume.toReal / B'.radius ^ n) +
                (-(n : ℝ) / 2) * Real.log (4 * Real.pi) - (n : ℝ)) + δ := by
                  linarith
          _ ≤ 400 * (2 : ℝ) ^ (n + 1) + (n : ℝ) ^ 2 +
                Real.log (B'.volume.toReal / B'.radius ^ n) +
                (-(n : ℝ) / 2) * Real.log (4 * Real.pi) - (n : ℝ) + δ := by
                  linarith
    _ ≤ collapseWConst n +
          Real.log (B.volume.toReal / B.radius ^ n) + δ := by
        unfold collapseWConst
        linarith
    _ = collapseWConst (Module.finrank ℝ E) +
          Real.log (B.volume.toReal / B.radius ^ Module.finrank ℝ E) + δ := rfl

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
