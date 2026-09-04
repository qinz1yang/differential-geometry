import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Slice
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Operator.MetricFamilyGram
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Tensor.Tensor0SRiemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

private theorem lKinetic_ae
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (p : M) {L : Real} (us : timeH1 E L)
    (a b : Real) (hab : a ≤ b)
    (hsrc : MapsTo alpha (Icc a b) (chartAt H p).source)
    (hslice : EqOn us.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (Icc (0 : Real) L))
    (hL : L = b - a)
    (hdiff : ∀ᵐ r ∂timeMeasure L,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha (a + r)) :
    (fun r ↦ (1 / 2 : Real) *
      (S.base.metric (T - (r + a) ^ 2)).inner (alpha (r + a))
        (lVelocity (I := I) alpha (r + a))
        (lVelocity (I := I) alpha (r + a))) =ᵐ[timeMeasure L]
      fun r ↦ inner Real
        (((1 / 2 : Real) • chartGramOp (I := I) S.family p
          (T - (a + r) ^ 2, us.toFun r)) (us.deriv r)) (us.deriv r) := by
  have hL0 : 0 ≤ L := by rw [hL]; exact sub_nonneg.mpr hab
  have hmem : ∀ᵐ r ∂timeMeasure L, r ∈ Ioo (0 : Real) L := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [us.ae_hasDerivWithinAt_toFun, hdiff, hmem] with r hu hmdiff hr
  have hrcc : r ∈ Icc (0 : Real) L := ⟨hr.1.le, hr.2.le⟩
  have hnhds : Icc (0 : Real) L ∈ nhds r := Icc_mem_nhds hr.1 hr.2
  have hcoord : HasDerivAt
      (fun q ↦ extChartAt I p (alpha (a + q))) (us.deriv r) r := by
    apply hu.hasDerivAt hnhds |>.congr_of_eventuallyEq
    filter_upwards [hnhds] with q hq
    exact (hslice hq).symm
  have hderiv :
      (fderiv Real ((extChartAt I p) ∘ alpha) (a + r) : Real →L[Real] E) 1 =
        us.deriv r := by
    change deriv ((extChartAt I p) ∘ alpha) (a + r) = us.deriv r
    rw [← deriv_comp_const_add]
    simpa only [Function.comp_apply] using hcoord.deriv
  have hrab : a + r ∈ Icc a b := by
    rw [hL] at hrcc
    exact ⟨le_add_of_nonneg_right hrcc.1, by linarith [hrcc.2]⟩
  have hars : alpha (a + r) ∈ (chartAt H p).source := hsrc hrab
  have hraw :=
    raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
      (I := I) (M := M) hmdiff p hars
  rw [hderiv] at hraw
  have hinv : (extChartAt I p).symm (us.toFun r) = alpha (a + r) := by
    rw [hslice hrcc]
    exact (extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hars)
  rw [smul_apply, real_inner_smul_left,
    chartGramOp_inner, hinv]
  rw [add_comm r a]
  change (1 / 2 : Real) *
      (S.base.metric (T - (a + r) ^ 2)).inner (alpha (a + r))
        ((mfderiv (modelWithCornersSelf Real Real) I alpha (a + r) :
          Real →L[Real] _) (1 : Real))
        ((mfderiv (modelWithCornersSelf Real Real) I alpha (a + r) :
          Real →L[Real] _) (1 : Real)) = _
  rw [hraw]
  rfl

theorem lKinetic_eq_chart_integral
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (p : M) (a b : Real) (hab : a ≤ b)
    (us : timeH1 E (b - a))
    (hsrc : MapsTo alpha (Icc a b) (chartAt H p).source)
    (hslice : EqOn us.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (Icc (0 : Real) (b - a)))
    (hdiff : ∀ᵐ r ∂timeMeasure (b - a),
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha (a + r)) :
    (∫ s in a..b, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) =
      ∫ r in (0 : Real)..b - a,
        inner Real
          (((1 / 2 : Real) •
            chartGramOp (I := I) S.family p
              (T - (a + r) ^ 2, us.toFun r)) (us.deriv r))
          (us.deriv r) := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hpoint := lKinetic_ae S T alpha p us a b hab hsrc hslice rfl hdiff
  have hshift :
      (∫ r in (0 : Real)..b - a, (1 / 2 : Real) *
        (S.base.metric (T - (r + a) ^ 2)).inner (alpha (r + a))
          (lVelocity (I := I) alpha (r + a))
          (lVelocity (I := I) alpha (r + a))) =
        ∫ s in a..b, (1 / 2 : Real) *
          (S.base.metric (T - s ^ 2)).inner (alpha s)
            (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) := by
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right
        (fun s ↦ (1 / 2 : Real) *
          (S.base.metric (T - s ^ 2)).inner (alpha s)
            (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
        (a := 0) (b := b - a) a)
  rw [← hshift]
  apply intervalIntegral.integral_congr_ae_restrict
  simpa only [timeMeasure, uIoc_of_le hba,
    restrict_Ioc_eq_restrict_Icc] using hpoint

theorem lKinetic_eq_chart_slice_integral
    (S : SolutionOn (I := I) (M := M) D) (T R : Real)
    (alpha : Real → M) (p : M) (u : timeH1 E R)
    (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) (hbR : b ≤ R)
    (hsrc : MapsTo alpha (Icc a b) (chartAt H p).source)
    (hrep : EqOn u.toFun ((extChartAt I p) ∘ alpha) (Icc a b))
    (hdiff : ∀ᵐ r ∂timeMeasure (b - a),
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha (a + r)) :
    (∫ s in a..b, (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) =
      ∫ r in (0 : Real)..b - a,
        inner Real
          (((1 / 2 : Real) • chartGramOp (I := I) S.family p
            (T - (a + r) ^ 2, (timeH1.slice u a b ha hbR).toFun r))
            ((timeH1.slice u a b ha hbR).deriv r))
          ((timeH1.slice u a b ha hbR).deriv r) := by
  let us : timeH1 E (b - a) := timeH1.slice u a b ha hbR
  have hslice : EqOn us.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (Icc (0 : Real) (b - a)) := by
    intro r hr
    rw [show us.toFun r = u.toFun (a + r) from
      timeH1.slice_toFun u a b ha hbR hr]
    exact hrep ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  simpa only [us] using
    lKinetic_eq_chart_integral S T alpha p a b hab us hsrc hslice hdiff

theorem intervalIntegrable_lKinetic_of_chartH1
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (T : Real) (alpha : Real → M) (p : M)
    (a b : Real) (hab : a ≤ b) (us : timeH1 E (b - a))
    (hsrc : MapsTo alpha (Icc a b) (chartAt H p).source)
    (hslice : EqOn us.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (Icc (0 : Real) (b - a)))
    (hdiff : ∀ᵐ r ∂timeMeasure (b - a),
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha (a + r))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (fun s ↦ (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume a b := by
  let L : Real := b - a
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  have hL : 0 ≤ L := sub_nonneg.mpr hab
  have hτc : ContinuousOn τ (Icc (0 : Real) L) := by
    exact continuousOn_const.sub ((continuousOn_const.add continuousOn_id).pow 2)
  let J : Set Real := τ '' Icc (0 : Real) L
  let K : Set E := us.toFun '' Icc (0 : Real) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn us.continuousOn_toFun
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    apply hreg (a + r)
    exact ⟨le_add_of_nonneg_right hr.1, by dsimp only [L] at hr; linarith [hr.2]⟩
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro z ⟨r, hr, rfl⟩
    rw [hslice hr, (isOpen_extChartAt_target (I := I) p).interior_eq]
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc ⟨le_add_of_nonneg_right hr.1,
        by dsimp only [L] at hr; linarith [hr.2]⟩)
  let A : Real → E →L[Real] E := fun r ↦
    (1 / 2 : Real) • chartGramOp (I := I) S.family p (τ r, us.toFun r)
  have hpair : ContinuousOn (fun r ↦ (τ r, us.toFun r)) (Icc (0 : Real) L) :=
    hτc.prodMk us.continuousOn_toFun
  have hAcont : ContinuousOn A (Icc (0 : Real) L) := by
    dsimp only [A]
    exact ((chartGramOp_cont (I := I) hS hJreg p hKchart).comp hpair
      fun r hr ↦ ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩).const_smul (1 / 2 : Real)
  have hA : AEStronglyMeasurable A (timeMeasure L) := by
    simpa only [timeMeasure] using
      hAcont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hCraw⟩ := chartGramOp_bound (I := I) hS hJreg hJc p hKchart hKc
  have hC : ∀ᵐ r ∂timeMeasure L, ‖A r‖ ≤ (C : Real) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp only [A]
    rw [norm_smul]
    have hb := hCraw (τ r, us.toFun r) ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (by
      have hC0 := NNReal.coe_nonneg C
      linarith)
  have hquad := timeQuad_int A hA C hC hL us.deriv
  have hpoint := lKinetic_ae S T alpha p us a b hab hsrc hslice rfl hdiff
  have hpoint' :
      (fun r ↦ (1 / 2 : Real) *
        (S.base.metric (T - (r + a) ^ 2)).inner (alpha (r + a))
          (lVelocity (I := I) alpha (r + a))
          (lVelocity (I := I) alpha (r + a))) =ᵐ[volume.restrict (Ι (0 : Real) L)]
        fun r ↦ inner Real (A r (us.deriv r)) (us.deriv r) := by
    simpa only [timeMeasure, uIoc_of_le hL, restrict_Ioc_eq_restrict_Icc,
      A, τ] using hpoint
  have hshift : IntervalIntegrable (fun r ↦ (1 / 2 : Real) *
      (S.base.metric (T - (r + a) ^ 2)).inner (alpha (r + a))
        (lVelocity (I := I) alpha (r + a))
        (lVelocity (I := I) alpha (r + a))) volume 0 L :=
    hquad.congr_ae hpoint'.symm
  have horig := (IntervalIntegrable.comp_add_right_iff
    (f := fun s ↦ (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
    (a := 0) (b := L) (c := a)).mp hshift
  simpa only [zero_add, L, sub_add_cancel] using horig

theorem intervalIntegrable_lKinetic_of_timeH1
    [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (T R : Real) (alpha : Real → M) (p : M) (u : timeH1 E R)
    (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) (hbR : b ≤ R)
    (hsrc : MapsTo alpha (Icc a b) (chartAt H p).source)
    (hrep : EqOn u.toFun ((extChartAt I p) ∘ alpha) (Icc a b))
    (hdiff : ∀ᵐ r ∂timeMeasure (b - a),
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha (a + r))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (fun s ↦ (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
      volume a b := by
  let us : timeH1 E (b - a) := timeH1.slice u a b ha hbR
  have hslice : EqOn us.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (Icc (0 : Real) (b - a)) := by
    intro r hr
    rw [show us.toFun r = u.toFun (a + r) from
      timeH1.slice_toFun u a b ha hbR hr]
    exact hrep ⟨le_add_of_nonneg_right hr.1, by linarith [hr.2]⟩
  exact intervalIntegrable_lKinetic_of_chartH1 S hS T alpha p a b hab us hsrc hslice hdiff hreg

end DifferentialGeometry.PDE.RicciFlow.Perelman
