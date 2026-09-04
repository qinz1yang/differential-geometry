import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.StrongConvergence
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open scoped Manifold Topology ContDiff Interval

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem chartKin_tendsto {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 ≤ L) (τ : Real → Real)
    (hτc : ContinuousOn τ (Icc (0 : Real) L))
    (hτreg : MapsTo τ (Icc (0 : Real) L) D.regular)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : ℕ → timeH1 E L) (uLim : timeH1 E L)
    (huK : ∀ n (r : Icc (0 : Real) L), (u n).toFun r.1 ∈ K)
    (huLimK : ∀ r : Icc (0 : Real) L, uLim.toFun r.1 ∈ K)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : Tendsto (fun n ↦ (u n).deriv) atTop (nhds uLim.deriv)) :
    Tendsto (fun n ↦ ∫ r in (0 : Real)..L,
      (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) G alpha (τ r, (u n).toFun r) ((u n).deriv r))
        ((u n).deriv r)) atTop
      (nhds (∫ r in (0 : Real)..L,
        (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) G alpha (τ r, uLim.toFun r) (uLim.deriv r))
          (uLim.deriv r))) := by
  let J : Set Real := τ '' Icc (0 : Real) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hτreg hr
  let A : ℕ → Real → E →L[Real] E := fun n r ↦
    (1 / 2 : Real) • chartGramOp (I := I) G alpha (τ r, (u n).toFun r)
  let ALim : Real → E →L[Real] E := fun r ↦
    (1 / 2 : Real) • chartGramOp (I := I) G alpha (τ r, uLim.toFun r)
  have hpair (n : ℕ) : ContinuousOn
      (fun r ↦ (τ r, (u n).toFun r)) (Icc (0 : Real) L) :=
    hτc.prodMk (u n).continuousOn_toFun
  have hpairLim : ContinuousOn
      (fun r ↦ (τ r, uLim.toFun r)) (Icc (0 : Real) L) :=
    hτc.prodMk uLim.continuousOn_toFun
  have hAcont (n : ℕ) : ContinuousOn (A n) (Icc (0 : Real) L) := by
    dsimp only [A]
    exact ((chartGramOp_cont (I := I) hG hJreg alpha hKchart).comp
      (hpair n) fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩).const_smul (1 / 2 : Real)
  have hALimCont : ContinuousOn ALim (Icc (0 : Real) L) := by
    dsimp only [ALim]
    exact ((chartGramOp_cont (I := I) hG hJreg alpha hKchart).comp
      hpairLim fun r hr ↦ ⟨⟨r, hr, rfl⟩, huLimK ⟨r, hr⟩⟩).const_smul (1 / 2 : Real)
  have hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure L) := fun n ↦ by
    simpa only [timeMeasure] using
      (hAcont n).aestronglyMeasurable measurableSet_Icc
  have hALim : AEStronglyMeasurable ALim (timeMeasure L) := by
    simpa only [timeMeasure] using
      hALimCont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hCraw⟩ := chartGramOp_bound (I := I) hG hJreg hJc alpha hKchart hKc
  have hC : ∀ n, ∀ᵐ r ∂timeMeasure L, ‖A n r‖ ≤ (C : Real) := fun n ↦ by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp only [A]
    rw [norm_smul]
    have hb := hCraw (τ r, (u n).toFun r) ⟨⟨r, hr, rfl⟩, huK n ⟨r, hr⟩⟩
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (by
      have hC0 := NNReal.coe_nonneg C
      linarith)
  have hCLim : ∀ᵐ r ∂timeMeasure L, ‖ALim r‖ ≤ (C : Real) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    dsimp only [ALim]
    rw [norm_smul]
    have hb := hCraw (τ r, uLim.toFun r) ⟨⟨r, hr, rfl⟩, huLimK ⟨r, hr⟩⟩
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (by
      have hC0 := NNReal.coe_nonneg C
      linarith)
  have hGramUnif : TendstoUniformly
      (fun n (r : Icc (0 : Real) L) ↦
        chartGramOp (I := I) G alpha (τ r.1, (u n).toFun r.1))
      (fun r ↦ chartGramOp (I := I) G alpha (τ r.1, uLim.toFun r.1)) atTop :=
    chartGramOp_unif (I := I) hG hJreg hJc alpha hKchart hKc
      (fun r ↦ ⟨r.1, r.2, rfl⟩) (Eventually.of_forall huK) huLimK hu
  have hconv : ∀ δ : Real, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ r ∂timeMeasure L, ‖A n r - ALim r‖ ≤ δ := by
    intro δ hδ
    have hev := (Metric.tendstoUniformly_iff.1 hGramUnif) (2 * δ) (by positivity)
    filter_upwards [hev] with n hn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hraw := hn ⟨r, hr⟩
    have hraw' :
        ‖chartGramOp (I := I) G alpha (τ r, (u n).toFun r) -
          chartGramOp (I := I) G alpha (τ r, uLim.toFun r)‖ < 2 * δ := by
      simpa only [dist_eq_norm, norm_sub_rev] using hraw
    have hscaled : (1 / 2 : Real) *
        ‖chartGramOp (I := I) G alpha (τ r, (u n).toFun r) -
          chartGramOp (I := I) G alpha (τ r, uLim.toFun r)‖ < δ := by
      linarith
    dsimp only [A, ALim]
    rw [← smul_sub, norm_smul]
    have hhalf : ‖(1 / 2 : Real)‖ = (1 / 2 : Real) := by norm_num
    rw [hhalf]
    exact hscaled.le
  have hq := timeQuad_strong A ALim hA hALim (fun _ ↦ C) C hC hCLim hconv
    (fun n ↦ (u n).deriv) uLim.deriv hdu
  have hlimEq := timeQuad_eq_integral ALim hALim C hCLim hL uLim.deriv
  have hseqEq :
      (fun n ↦ timeQuad (A n) (hA n) C (hC n) (u n).deriv) =
        (fun n ↦ ∫ r in (0 : Real)..L,
          inner Real (A n r ((u n).deriv r)) ((u n).deriv r)) := by
    funext n
    exact timeQuad_eq_integral (A n) (hA n) C (hC n) hL (u n).deriv
  rw [hlimEq, hseqEq] at hq
  dsimp only [A, ALim] at hq
  simpa only [smul_apply, real_inner_smul_left] using hq

end DifferentialGeometry.Geometry.Curvature

end
