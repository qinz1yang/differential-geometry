import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1Convergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierGramContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.KineticEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Scalar
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Chart.H1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.StrongConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false

noncomputable section

open Bundle Filter Function MeasureTheory Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open scoped ContDiff Manifold Topology Interval NNReal

namespace DifferentialGeometry.PDE.RicciFlow

section Kinetic

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem kinetic_eq_chart_ae
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ)
    (alpha : ℝ → M) (p : M) (a b : ℝ) (hab : a ≤ b)
    (u : timeH1 E (b - a))
    (hsrc : MapsTo alpha (Icc a b) (chartAt H p).source)
    (hrep : EqOn u.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (Icc (0 : ℝ) (b - a))) :
    (fun r ↦ (1 / 2 : ℝ) *
      (S.base.metric (T - (r + a) ^ 2)).inner (alpha (r + a))
        (lVelocity (I := I) alpha (r + a))
        (lVelocity (I := I) alpha (r + a))) =ᵐ[timeMeasure (b - a)]
      fun r ↦ inner ℝ
        (((1 / 2 : ℝ) • chartGramOp (I := I) S.family p
          (T - (a + r) ^ 2, u.toFun r)) (u.deriv r)) (u.deriv r) := by
  have hdiff := curve_mdiff_local I p alpha u hab hsrc hrep
  have hmem : ∀ᵐ r ∂timeMeasure (b - a), r ∈ Ioo (0 : ℝ) (b - a) := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [u.ae_hasDerivWithinAt_toFun, hdiff, hmem] with r hu hmdiff hr
  have hrcc : r ∈ Icc (0 : ℝ) (b - a) := ⟨hr.1.le, hr.2.le⟩
  have hnhds : Icc (0 : ℝ) (b - a) ∈ 𝓝 r := Icc_mem_nhds hr.1 hr.2
  have hcoord : HasDerivAt
      (fun q ↦ extChartAt I p (alpha (a + q))) (u.deriv r) r := by
    apply hu.hasDerivAt hnhds |>.congr_of_eventuallyEq
    filter_upwards [hnhds] with q hq
    exact (hrep hq).symm
  have hderiv :
      (fderiv ℝ ((extChartAt I p) ∘ alpha) (a + r) : ℝ →L[ℝ] E) 1 =
        u.deriv r := by
    change deriv ((extChartAt I p) ∘ alpha) (a + r) = u.deriv r
    rw [← deriv_comp_const_add]
    simpa only [Function.comp_apply] using hcoord.deriv
  have hrab : a + r ∈ Icc a b :=
    ⟨le_add_of_nonneg_right hrcc.1, by linarith [hrcc.2]⟩
  have hars := hsrc hrab
  have hraw := raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt
    (I := I) (M := M) hmdiff p hars
  rw [hderiv] at hraw
  have hinv : (extChartAt I p).symm (u.toFun r) = alpha (a + r) := by
    rw [hrep hrcc]
    exact (extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hars)
  rw [smul_apply, real_inner_smul_left, chartGramOp_inner, hinv, add_comm r a]
  change (1 / 2 : ℝ) *
      (S.base.metric (T - (a + r) ^ 2)).inner (alpha (a + r))
        ((mfderiv (modelWithCornersSelf ℝ ℝ) I alpha (a + r) : ℝ →L[ℝ] _) 1)
        ((mfderiv (modelWithCornersSelf ℝ ℝ) I alpha (a + r) : ℝ →L[ℝ] _) 1) =
      (1 / 2 : ℝ) * (S.base.metric (T - (a + r) ^ 2)).inner (alpha (a + r))
        ((trivializationAt E (TangentSpace I) p).symmL ℝ (alpha (a + r)) (u.deriv r))
        ((trivializationAt E (TangentSpace I) p).symmL ℝ (alpha (a + r)) (u.deriv r))
  exact congrArg
    (fun v : TangentSpace I (alpha (a + r)) ↦
      (1 / 2 : ℝ) * (S.base.metric (T - (a + r) ^ 2)).inner (alpha (a + r)) v v)
    hraw

private theorem kinetic_integrable_chart_on_carrier [I.Boundaryless]
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (T a b : ℝ) (hab : a ≤ b) (p : M) (alpha : ℝ → M)
    (u : timeH1 E (b - a))
    (hsrc : MapsTo alpha (Icc a b) (chartAt H p).source)
    (hrep : EqOn u.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (Icc (0 : ℝ) (b - a)))
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (fun s ↦ (1 / 2 : ℝ) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) volume a b := by
  let L : ℝ := b - a
  let tau : ℝ → ℝ := fun r ↦ T - (a + r) ^ 2
  let J : Set ℝ := tau '' Icc (0 : ℝ) L
  let K : Set E := u.toFun '' Icc (0 : ℝ) L
  have hL : 0 ≤ L := sub_nonneg.mpr hab
  have hJ : J ⊆ D.carrier := by
    rintro t ⟨r, hr, rfl⟩
    exact hback (a + r) ⟨le_add_of_nonneg_right hr.1, by
      dsimp only [L] at hr
      linarith [hr.2]⟩
  have hK : K ⊆ interior (extChartAt I p).target := by
    rintro z ⟨r, hr, rfl⟩
    rw [hrep hr, (isOpen_extChartAt_target (I := I) p).interior_eq]
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc ⟨le_add_of_nonneg_right hr.1, by
        dsimp only [L] at hr
        linarith [hr.2]⟩)
  let A : ℝ → E →L[ℝ] E := fun r ↦
    (1 / 2 : ℝ) • chartGramOp (I := I) S.family p (tau r, u.toFun r)
  have hpair : ContinuousOn (fun r ↦ (tau r, u.toFun r)) (Icc (0 : ℝ) L) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn.prodMk
      u.continuousOn_toFun
  have hAcont : ContinuousOn A (Icc (0 : ℝ) L) :=
    ((chartGramOp_continuousOn_carrier hMet hJ p hK).comp hpair
      (fun r hr ↦ ⟨⟨r, hr, rfl⟩, ⟨r, hr, rfl⟩⟩)).const_smul (1 / 2 : ℝ)
  have hA : AEStronglyMeasurable A (timeMeasure L) := by
    simpa only [timeMeasure] using hAcont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hAcont
  let C : ℝ≥0 := ⟨max C₀ 0, le_max_right _ _⟩
  have hC : ∀ᵐ r ∂timeMeasure L, ‖A r‖ ≤ (C : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (hC₀ r hr).trans (le_max_left _ _)
  have hquad := timeQuad_int A hA C hC hL u.deriv
  have hpoint := kinetic_eq_chart_ae S T alpha p a b hab u hsrc hrep
  have hpoint' :
      (fun r ↦ (1 / 2 : ℝ) *
        (S.base.metric (T - (r + a) ^ 2)).inner (alpha (r + a))
          (lVelocity (I := I) alpha (r + a))
          (lVelocity (I := I) alpha (r + a))) =ᵐ[volume.restrict (Ι (0 : ℝ) L)]
        fun r ↦ inner ℝ (A r (u.deriv r)) (u.deriv r) := by
    simpa only [timeMeasure, uIoc_of_le hL, restrict_Ioc_eq_restrict_Icc,
      A, tau, L] using hpoint
  have hshift := hquad.congr_ae hpoint'.symm
  have horig := (IntervalIntegrable.comp_add_right_iff
    (f := fun s ↦ (1 / 2 : ℝ) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
    (a := 0) (b := L) (c := a)).mp hshift
  simpa only [zero_add, L, sub_add_cancel] using horig

theorem chartKin_tendsto_on_carrier
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (p : M) {L : ℝ} (hL : 0 ≤ L) (tau : ℝ → ℝ)
    (htau : ContinuousOn tau (Icc (0 : ℝ) L))
    (hback : MapsTo tau (Icc (0 : ℝ) L) D.carrier)
    {K : Set E} (hKc : IsCompact K)
    (hK : K ⊆ interior (extChartAt I p).target)
    (u : ℕ → timeH1 E L) (uLim : timeH1 E L)
    (huK : ∀ n (r : Icc (0 : ℝ) L), (u n).toFun r.1 ∈ K)
    (hLimK : ∀ r : Icc (0 : ℝ) L, uLim.toFun r.1 ∈ K)
    (hu : Tendsto u atTop (𝓝 uLim)) :
    Tendsto (fun n ↦ ∫ r in (0 : ℝ)..L,
      (1 / 2 : ℝ) * inner ℝ
        (chartGramOp (I := I) G p (tau r, (u n).toFun r) ((u n).deriv r))
        ((u n).deriv r)) atTop
      (𝓝 (∫ r in (0 : ℝ)..L,
        (1 / 2 : ℝ) * inner ℝ
          (chartGramOp (I := I) G p (tau r, uLim.toFun r) (uLim.deriv r))
          (uLim.deriv r))) := by
  let J : Set ℝ := tau '' Icc (0 : ℝ) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn htau
  have hJ : J ⊆ D.carrier := by
    rintro t ⟨r, hr, rfl⟩
    exact hback hr
  let F : ℝ × E → E →L[ℝ] E := fun q ↦ (1 / 2 : ℝ) • chartGramOp G p q
  have hF : ContinuousOn F (J ×ˢ K) :=
    (chartGramOp_continuousOn_carrier hG hJ p hK).const_smul (1 / 2 : ℝ)
  let A : ℕ → ℝ → E →L[ℝ] E := fun n r ↦ F (tau r, (u n).toFun r)
  let ALim : ℝ → E →L[ℝ] E := fun r ↦ F (tau r, uLim.toFun r)
  have hAcont (n : ℕ) : ContinuousOn (A n) (Icc (0 : ℝ) L) :=
    hF.comp (htau.prodMk (u n).continuousOn_toFun)
      (fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩)
  have hALimCont : ContinuousOn ALim (Icc (0 : ℝ) L) :=
    hF.comp (htau.prodMk uLim.continuousOn_toFun)
      (fun r hr ↦ ⟨⟨r, hr, rfl⟩, hLimK ⟨r, hr⟩⟩)
  have hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure L) := fun n ↦ by
    simpa only [timeMeasure] using (hAcont n).aestronglyMeasurable measurableSet_Icc
  have hALim : AEStronglyMeasurable ALim (timeMeasure L) := by
    simpa only [timeMeasure] using hALimCont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C₀, hC₀⟩ := (hJc.prod hKc).exists_bound_of_continuousOn hF
  let C : ℝ≥0 := ⟨max C₀ 0, le_max_right _ _⟩
  have hC : ∀ n, ∀ᵐ r ∂timeMeasure L, ‖A n r‖ ≤ (C : ℝ) := fun n ↦ by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (hC₀ (tau r, (u n).toFun r) ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩).trans
      (le_max_left _ _)
  have hCLim : ∀ᵐ r ∂timeMeasure L, ‖ALim r‖ ≤ (C : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (hC₀ (tau r, uLim.toFun r) ⟨⟨r, hr, rfl⟩, hLimK ⟨r, hr⟩⟩).trans
      (le_max_left _ _)
  have hposUnif := DifferentialGeometry.Analysis.timeH1_tendstoUniformly u uLim hu
  have hpairUnif : TendstoUniformly
      (fun n (r : Icc (0 : ℝ) L) ↦ (tau r.1, (u n).toFun r.1))
      (fun r ↦ (tau r.1, uLim.toFun r.1)) atTop := by
    rw [Metric.tendstoUniformly_iff] at hposUnif ⊢
    intro epsilon hepsilon
    filter_upwards [hposUnif epsilon hepsilon] with n hn
    intro r
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hn r
  have hFUnif : TendstoUniformly
      (fun n (r : Icc (0 : ℝ) L) ↦ A n r.1)
      (fun r ↦ ALim r.1) atTop := by
    apply ((hJc.prod hKc).uniformContinuousOn_of_continuous hF).comp_tendstoUniformly_eventually
    · exact Eventually.of_forall fun n r ↦ ⟨⟨r.1, r.2, rfl⟩, huK n r⟩
    · exact fun r ↦ ⟨⟨r.1, r.2, rfl⟩, hLimK r⟩
    · exact hpairUnif
  have hconv : ∀ delta : ℝ, 0 < delta → ∀ᶠ n in atTop,
      ∀ᵐ r ∂timeMeasure L, ‖A n r - ALim r‖ ≤ delta := by
    intro delta hdelta
    filter_upwards [(Metric.tendstoUniformly_iff.mp hFUnif) delta hdelta] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have h := (hn ⟨r, hr⟩).le
    simpa only [dist_eq_norm, norm_sub_rev] using h
  have hdu : Tendsto (fun n ↦ (u n).deriv) atTop (𝓝 uLim.deriv) :=
    ((timeH1.timeDeriv E L).continuous.tendsto uLim).comp hu
  have hquad := timeQuad_strong A ALim hA hALim (fun _ ↦ C) C hC hCLim hconv
    (fun n ↦ (u n).deriv) uLim.deriv hdu
  have hlimEq := timeQuad_eq_integral ALim hALim C hCLim hL uLim.deriv
  have hseqEq :
      (fun n ↦ timeQuad (A n) (hA n) C (hC n) (u n).deriv) =
      (fun n ↦ ∫ r in (0 : ℝ)..L, inner ℝ (A n r ((u n).deriv r)) ((u n).deriv r)) := by
    funext n
    exact timeQuad_eq_integral (A n) (hA n) C (hC n) hL (u n).deriv
  rw [hlimEq, hseqEq] at hquad
  simpa only [A, ALim, F, smul_apply, real_inner_smul_left] using hquad

end Kinetic

section Lagrangian

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem lRegLag_integrable_chart_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : ℝ) (hab : a ≤ b) (p : M) (alpha : ℝ → M)
    (u : timeH1 E (b - a))
    (hsrc : MapsTo alpha (Icc a b) (chartAt H p).source)
    (hrep : EqOn u.toFun
      (fun r ↦ extChartAt I p (alpha (a + r))) (Icc (0 : ℝ) (b - a)))
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.carrier) :
    IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b := by
  have hkin := kinetic_integrable_chart_on_carrier S hMet T a b hab p alpha u hsrc hrep hback
  have hcont := curve_cont_local I p alpha u hab hsrc hrep
  have hpot := lScalar_int (I := I) S hSc T a b alpha
    (by simpa only [uIcc_of_le hab] using hback)
    (by simpa only [uIcc_of_le hab] using hcont)
  unfold lRegularizedLagrangian
  exact hkin.add hpot

end Lagrangian

end DifferentialGeometry.PDE.RicciFlow

end
