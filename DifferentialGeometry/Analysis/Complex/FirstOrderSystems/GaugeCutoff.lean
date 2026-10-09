import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Function
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The cutoff used for the original gauge is one on three quarters of its disk
and supported in the original disk. -/
def bufferedGaugeCutoff (a : ℂ) (R : ℝ) (hR : 0 < R) : ContDiffBump a where
  rIn := 3 * R / 4
  rOut := R
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Cut off the same continuous gauge and its same bounded measurable right hand
side. Both fields are globally integrable and unchanged on the buffered disk. -/
theorem buffered_gauge_cutoff_data
    (a : ℂ) (R : ℝ) (hR : 0 < R) (P A : ℂ → V →L[ℂ] V)
    (hP : ContinuousOn P (closedBall a R)) (hA : AEStronglyMeasurable A volume)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hnear : ∀ z ∈ closedBall a R, ‖P z - 1‖ ≤ δ)
    (hbound : ∀ z, ‖A z‖ ≤ C) :
    let χ := bufferedGaugeCutoff a R hR
    let F : ℂ → V →L[ℂ] V := fun z => χ z • P z
    let G : ℂ → V →L[ℂ] V := fun z => χ z • (A z * P z)
    Continuous F ∧ Integrable F ∧ Integrable G ∧
      (∀ z, ‖F z‖ ≤ 1 + δ) ∧ (∀ z, ‖G z‖ ≤ C * (1 + δ)) ∧
      (∀ z ∈ closedBall a (3 * R / 4), F z = P z ∧ G z = A z * P z) := by
  intro χ F G
  classical
  have hFzero (z : ℂ) (hz : R ≤ dist z a) : F z = 0 := by
    have hχ : χ z = 0 := χ.zero_of_le_dist hz
    simp only [F, hχ, zero_smul]
  have hFc : Continuous F := by
    have hpiece : Continuous ((closedBall a R).piecewise F (fun _ => 0)) := by
      apply continuous_piecewise
      · intro z hz
        exact hFzero z (frontier_closedBall_subset_sphere hz).ge
      · rw [isClosed_closedBall.closure_eq]
        exact χ.continuous.continuousOn.smul hP
      · exact continuousOn_const
    convert hpiece using 1
    funext z
    by_cases hz : z ∈ closedBall a R
    · simp only [Set.piecewise, hz, ite_true]
    · simp only [Set.piecewise, hz, ite_false]
      exact hFzero z (lt_of_not_ge hz).le
  have hFi : Integrable F := hFc.integrable_of_hasCompactSupport χ.hasCompactSupport.smul_right
  have hFm (z : ℂ) : ‖F z‖ ≤ 1 + δ := by
    by_cases hz : χ z = 0
    · simp only [F, hz, zero_smul, norm_zero]
      positivity
    · have hzR : z ∈ closedBall a R := by
        have hz' : z ∈ support χ := hz
        rw [χ.support_eq] at hz'
        exact ball_subset_closedBall hz'
      have hPn : ‖P z‖ ≤ 1 + δ := by
        calc
          _ = ‖(P z - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖P z - 1‖ + ‖(1 : V →L[ℂ] V)‖ := norm_add_le _ _
          _ ≤ δ + 1 := add_le_add (hnear z hzR) ContinuousLinearMap.norm_id_le
          _ = _ := add_comm _ _
      calc
        _ = χ z * ‖P z‖ := by
          dsimp only [F]
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (χ.nonneg' z)]
        _ ≤ 1 * (1 + δ) := mul_le_mul χ.le_one hPn (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
  have hGm (z : ℂ) : ‖G z‖ ≤ C * ‖F z‖ := by
    calc
      _ = χ z * ‖A z * P z‖ := by
        dsimp only [G]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (χ.nonneg' z)]
      _ ≤ χ z * (C * ‖P z‖) := mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _)))
        (χ.nonneg' z)
      _ = C * ‖F z‖ := by
        dsimp only [F]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (χ.nonneg' z)]
        ring
  have hG_eq : G = fun z => A z * F z := by
    funext z
    simp only [G, F, mul_smul_comm]
  have hGa : AEStronglyMeasurable G volume := by
    rw [hG_eq]
    exact hA.mul hFc.aestronglyMeasurable
  have hGi : Integrable G := (hFi.norm.const_mul C).mono' hGa (Eventually.of_forall hGm)
  refine ⟨hFc, hFi, hGi, hFm,
    fun z => (hGm z).trans (mul_le_mul_of_nonneg_left (hFm z) hC), ?_⟩
  intro z hz
  have hχ : χ z = 1 := χ.one_of_mem_closedBall hz
  exact ⟨by simp only [F, hχ, one_smul], by simp only [G, hχ, one_smul]⟩

/-- The original disk weak equation becomes the weak equation of the literal
cutoff fields on the buffered disk. The bundled gauge and its ambient
representative are identified at every original disk point. -/
theorem buffered_gauge_cutoff_weak_equation
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (P : C(closedBall a R, V →L[ℂ] V)) (P₀ A : ℂ → V →L[ℂ] V)
    (hrep : ∀ z : closedBall a R, P₀ z = P z)
    (hweak : ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball a R →
      (∫ z : ℂ, (((fderiv ℝ φ z 1 : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) =
      -(∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • (A w * P w)
        ∂(volume.comap ((↑) : closedBall a R → ℂ)))) :
    let χ := bufferedGaugeCutoff a R hR
    let F : ℂ → V →L[ℂ] V := fun z => χ z • P₀ z
    let G : ℂ → V →L[ℂ] V := fun z => χ z • (A z * P₀ z)
    ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball a (3 * R / 4) →
      (∫ z : ℂ, (((fderiv ℝ φ z 1 : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • F z) =
      -(∫ z : ℂ, (φ z : ℂ) • G z) := by
  intro χ F G φ hφ hc hs
  have hsR : tsupport φ ⊆ ball a R :=
    hs.trans (ball_subset_ball (by linarith))
  have hleft : (fun z : ℂ => (((fderiv ℝ φ z 1 : ℂ) +
      Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • F z) =
      (fun z : ℂ => (((fderiv ℝ φ z 1 : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · have hχ : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall (hs hz))
      simp only [F, hχ, one_smul]
    · simp only [fderiv_of_notMem_tsupport ℝ hz, zero_apply,
        Complex.ofReal_zero, mul_zero, add_zero, zero_div, zero_smul]
  have hright : (fun z : ℂ => (φ z : ℂ) • G z) =
      (fun z : ℂ => (φ z : ℂ) • (A z * P₀ z)) := by
    funext z
    by_cases hz : z ∈ tsupport φ
    · have hχ : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall (hs hz))
      simp only [G, hχ, one_smul]
    · simp only [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, zero_smul]
  have hdisk : (∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • (A w * P w)
      ∂(volume.comap ((↑) : closedBall a R → ℂ))) =
      ∫ z : ℂ, (φ z : ℂ) • (A z * P₀ z) := by
    calc
      _ = ∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • (A w * P₀ w)
          ∂(volume.comap ((↑) : closedBall a R → ℂ)) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun w => by
          change (φ (w : ℂ) : ℂ) • (A w * P w) =
            (φ (w : ℂ) : ℂ) • (A w * P₀ w)
          rw [hrep w]
      _ = ∫ z in closedBall a R, (φ z : ℂ) • (A z * P₀ z) :=
        integral_subtype_comap (μ := volume) (s := closedBall a R)
          isClosed_closedBall.measurableSet (fun z : ℂ => (φ z : ℂ) • (A z * P₀ z))
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport fun hz' =>
          hz (ball_subset_closedBall (hsR hz'))
        simp only [hφz, Complex.ofReal_zero, zero_smul]
  rw [hleft, hright, hweak φ hφ hc hsR, hdisk]

end DifferentialGeometry.Analysis
