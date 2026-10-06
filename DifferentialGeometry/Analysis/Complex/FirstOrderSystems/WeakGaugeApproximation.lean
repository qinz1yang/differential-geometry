import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.WeakGaugeCalculus
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.GaugeMollifierBounds
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.GaugeCutoff
import DifferentialGeometry.Analysis.Complex.WeakHolomorphic.BoundedMollification
import DifferentialGeometry.Analysis.Complex.WeakHolomorphic.Mollification
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Function
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- A fixed positive mollifier sequence whose support fits in a quarter of the
original disk, with no dependence on values or zeros of the section. -/
def bufferedGaugeBump (R : ℝ) (hR : 0 < R) (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := ((R / 4) * (1 / ((n : ℝ) + 1))) / 2
  rOut := (R / 4) * (1 / ((n : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < (R / 4) * (1 / ((n : ℝ) + 1)) := by positivity
    linarith

/-- The chosen mollifiers shrink to the original point. -/
theorem bufferedGaugeBump_rOut_tendsto (R : ℝ) (hR : 0 < R) :
    Tendsto (fun n => (bufferedGaugeBump R hR n).rOut) atTop (𝓝 0) := by
  simpa only [bufferedGaugeBump, mul_zero] using
    (tendsto_const_nhds (x := R / 4)).mul tendsto_one_div_add_atTop_nhds_zero_nat

omit [CompleteSpace V] in
/-- The coefficient residual separates into the error of the original gauge
approximation and the error in its weak derivative. -/
theorem norm_gauge_residual_le (A P Q D : V →L[ℂ] V) {C : ℝ} (hA : ‖A‖ ≤ C) :
    ‖A * Q - D‖ ≤ C * ‖Q - P‖ + ‖A * P - D‖ := by
  have heq : A * Q - D = A * (Q - P) + (A * P - D) := by
    rw [mul_sub]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) le_rfl)

omit [CompleteSpace V] in
/-- The inverse-section error is controlled by the original gauge error and
uniform bounds on the two inverses, including at zeros of the section. -/
theorem norm_inverse_gauge_sub_le (P Q : V →L[ℂ] V) (ξ : V)
    (hP : IsUnit P) (hQ : IsUnit Q) {L M : ℝ} (hL : 0 ≤ L)
    (hPi : ‖Ring.inverse P‖ ≤ L) (hQi : ‖Ring.inverse Q‖ ≤ L)
    (hξ : ‖ξ‖ ≤ M) :
    ‖Ring.inverse Q ξ - Ring.inverse P ξ‖ ≤ L ^ 2 * M * ‖Q - P‖ := by
  have heq : Ring.inverse Q - Ring.inverse P =
      Ring.inverse Q * (P - Q) * Ring.inverse P := by
    rw [mul_sub, sub_mul, mul_assoc, Ring.mul_inverse_cancel _ hP,
      Ring.inverse_mul_cancel _ hQ, mul_one, one_mul]
  have heqξ : Ring.inverse Q ξ - Ring.inverse P ξ =
      Ring.inverse Q ((P - Q) (Ring.inverse P ξ)) := by
    change (Ring.inverse Q - Ring.inverse P) ξ =
      (Ring.inverse Q * (P - Q) * Ring.inverse P) ξ
    rw [heq]
  rw [heqξ]
  calc
    _ ≤ ‖Ring.inverse Q‖ * ‖(P - Q) (Ring.inverse P ξ)‖ :=
      (Ring.inverse Q).le_opNorm _
    _ ≤ L * (‖P - Q‖ * (L * M)) := by
      apply mul_le_mul hQi _ (norm_nonneg _) hL
      exact ((P - Q).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (((Ring.inverse P).le_opNorm _).trans
          (mul_le_mul hPi hξ (norm_nonneg _) hL)) (norm_nonneg _))
    _ = L ^ 2 * M * ‖Q - P‖ := by rw [norm_sub_rev]; ring

omit [CompleteSpace V] in
/-- Bounded coefficients convert the two genuine approximation errors into the
weighted local `L¹` residual required by the weak inverse-gauge theorem. -/
theorem weighted_gauge_residual_tendsto_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A P : X → V →L[ℂ] V) (Q D : ℕ → X → V →L[ℂ] V) (ψ : X → ℝ)
    {C : ℝ} (hA : ∀ᵐ z ∂μ, ‖A z‖ ≤ C) (hψ : ∀ᵐ z ∂μ, 0 ≤ ψ z)
    (hPQ : ∀ n, Integrable (fun z => ψ z * ‖Q n z - P z‖) μ)
    (hPD : ∀ n, Integrable (fun z => ψ z * ‖A z * P z - D n z‖) μ)
    (hresMeas : ∀ n, AEStronglyMeasurable
      (fun z => ψ z * ‖A z * Q n z - D n z‖) μ)
    (hPQlim : Tendsto (fun n => ∫ z, ψ z * ‖Q n z - P z‖ ∂μ) atTop (𝓝 0))
    (hPDlim : Tendsto (fun n => ∫ z, ψ z * ‖A z * P z - D n z‖ ∂μ)
      atTop (𝓝 0)) :
    (∀ n, Integrable (fun z => ψ z * ‖A z * Q n z - D n z‖) μ) ∧
      Tendsto (fun n => ∫ z, ψ z * ‖A z * Q n z - D n z‖ ∂μ) atTop (𝓝 0) := by
  have hb (n : ℕ) : ∀ᵐ z ∂μ,
      ψ z * ‖A z * Q n z - D n z‖ ≤
        C * (ψ z * ‖Q n z - P z‖) + ψ z * ‖A z * P z - D n z‖ := by
    filter_upwards [hA, hψ] with z hz hψz
    calc
      _ ≤ ψ z * (C * ‖Q n z - P z‖ + ‖A z * P z - D n z‖) :=
        mul_le_mul_of_nonneg_left (norm_gauge_residual_le _ _ _ _ hz) hψz
      _ = _ := by ring
  have hi (n : ℕ) : Integrable (fun z => ψ z * ‖A z * Q n z - D n z‖) μ := by
    apply (((hPQ n).const_mul C).add (hPD n)).mono' (hresMeas n)
    filter_upwards [hb n, hψ] with z hz hψz
    simpa only [Pi.add_apply, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hψz (norm_nonneg _))] using hz
  refine ⟨hi, ?_⟩
  apply squeeze_zero
  · intro n
    exact integral_nonneg_of_ae (hψ.mono fun z hz => mul_nonneg hz (norm_nonneg _))
  · intro n
    calc
      _ ≤ ∫ z, C * (ψ z * ‖Q n z - P z‖) + ψ z * ‖A z * P z - D n z‖ ∂μ :=
        integral_mono_ae (hi n) (((hPQ n).const_mul C).add (hPD n)) (hb n)
      _ = C * (∫ z, ψ z * ‖Q n z - P z‖ ∂μ) +
          (∫ z, ψ z * ‖A z * P z - D n z‖ ∂μ) := by
        rw [integral_add ((hPQ n).const_mul C) (hPD n), integral_const_mul]
  · simpa only [mul_zero, add_zero] using (tendsto_const_nhds.mul hPQlim).add hPDlim

omit [CompleteSpace V] in
/-- A weighted local `L¹` approximation of the original gauges also approximates
the literal inverse-gauged section under the already constructed inverse bounds. -/
theorem weighted_inverse_gauge_tendsto_zero
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (P : X → V →L[ℂ] V) (Q : ℕ → X → V →L[ℂ] V) (ξ : X → V) (ψ : X → ℝ)
    {L M : ℝ} (hL : 0 ≤ L)
    (hP : ∀ᵐ z ∂μ, ψ z ≠ 0 →
      IsUnit (P z) ∧ ‖Ring.inverse (P z)‖ ≤ L ∧ ‖ξ z‖ ≤ M)
    (hQ : ∀ n, ∀ᵐ z ∂μ, ψ z ≠ 0 →
      IsUnit (Q n z) ∧ ‖Ring.inverse (Q n z)‖ ≤ L)
    (hψ : ∀ᵐ z ∂μ, 0 ≤ ψ z)
    (hPQ : ∀ n, Integrable (fun z => ψ z * ‖Q n z - P z‖) μ)
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun z => ψ z * ‖Ring.inverse (Q n z) (ξ z) - Ring.inverse (P z) (ξ z)‖) μ)
    (hPQlim : Tendsto (fun n => ∫ z, ψ z * ‖Q n z - P z‖ ∂μ) atTop (𝓝 0)) :
    (∀ n, Integrable
      (fun z => ψ z * ‖Ring.inverse (Q n z) (ξ z) - Ring.inverse (P z) (ξ z)‖) μ) ∧
      Tendsto (fun n => ∫ z, ψ z *
        ‖Ring.inverse (Q n z) (ξ z) - Ring.inverse (P z) (ξ z)‖ ∂μ) atTop (𝓝 0) := by
  have hb (n : ℕ) : ∀ᵐ z ∂μ,
      ψ z * ‖Ring.inverse (Q n z) (ξ z) - Ring.inverse (P z) (ξ z)‖ ≤
        (L ^ 2 * M) * (ψ z * ‖Q n z - P z‖) := by
    filter_upwards [hP, hQ n, hψ] with z hPz hQz hψz
    by_cases hz : ψ z = 0
    · simp only [hz, zero_mul, mul_zero, le_refl]
    obtain ⟨huP, hiP, hξz⟩ := hPz hz
    obtain ⟨huQ, hiQ⟩ := hQz hz
    calc
      _ ≤ ψ z * (L ^ 2 * M * ‖Q n z - P z‖) :=
        mul_le_mul_of_nonneg_left (norm_inverse_gauge_sub_le _ _ _ huP huQ hL hiP hiQ hξz) hψz
      _ = _ := by ring
  have hi (n : ℕ) : Integrable
      (fun z => ψ z * ‖Ring.inverse (Q n z) (ξ z) - Ring.inverse (P z) (ξ z)‖) μ := by
    apply ((hPQ n).const_mul (L ^ 2 * M)).mono' (hMeas n)
    filter_upwards [hb n, hψ] with z hz hψz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hψz (norm_nonneg _))] using hz
  refine ⟨hi, ?_⟩
  apply squeeze_zero
  · intro n
    exact integral_nonneg_of_ae (hψ.mono fun z hz => mul_nonneg hz (norm_nonneg _))
  · intro n
    exact (integral_mono_ae (hi n) ((hPQ n).const_mul (L ^ 2 * M)) (hb n)).trans_eq
      (integral_const_mul _ _)
  · simpa only [mul_zero] using tendsto_const_nhds.mul hPQlim

/-- The same disk gauge supplies literal smooth mollifications with every-point
inverse control and vanishing weighted coefficient residuals. The weak equation
is that of the original bundled disk gauge, with its original comap measure. -/
theorem disk_gauge_has_controlled_mollifications
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (P : C(closedBall a R, V →L[ℂ] V)) (P₀ A : ℂ → V →L[ℂ] V)
    (hrep : ∀ z : closedBall a R, P₀ z = P z)
    (hA : AEStronglyMeasurable A volume)
    {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1) (hC : 0 ≤ C)
    (hnear : ∀ z ∈ closedBall a R, ‖P₀ z - 1‖ ≤ δ)
    (hbound : ∀ z, ‖A z‖ ≤ C)
    (hweak : ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball a R →
      (∫ z : ℂ, (((fderiv ℝ φ z 1 : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) =
      -(∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • (A w * P w)
        ∂(volume.comap ((↑) : closedBall a R → ℂ)))) :
    let χ := bufferedGaugeCutoff a R hR
    let F : ℂ → V →L[ℂ] V := fun z => χ z • P₀ z
    let Q : ℕ → ℂ → V →L[ℂ] V := fun n =>
      (bufferedGaugeBump R hR n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
    (∀ n, ContDiff ℝ ∞ (Q n)) ∧
      (∀ n z, z ∈ closedBall a (R / 2) →
        IsUnit (Q n z) ∧ ‖Ring.inverse (Q n z)‖ ≤ 1 / (1 - δ)) ∧
      (∀ z ∈ closedBall a R, IsUnit (P₀ z) ∧
        ‖Ring.inverse (P₀ z)‖ ≤ 1 / (1 - δ)) ∧
      (∀ ψ : ℂ → ℝ, Integrable ψ volume → (∀ z, 0 ≤ ψ z) →
        support ψ ⊆ ball a (R / 2) →
        (∀ n, Integrable (fun z => ψ z * ‖Q n z - P₀ z‖)) ∧
        Tendsto (fun n => ∫ z, ψ z * ‖Q n z - P₀ z‖) atTop (𝓝 0) ∧
        (∀ n, Integrable (fun z => ψ z * ‖A z * Q n z - complexDbar (Q n) z‖)) ∧
        Tendsto (fun n => ∫ z, ψ z * ‖A z * Q n z - complexDbar (Q n) z‖)
          atTop (𝓝 0)) := by
  intro χ F Q
  let G : ℂ → V →L[ℂ] V := fun z => χ z • (A z * P₀ z)
  let D : ℕ → ℂ → V →L[ℂ] V := fun n =>
    (bufferedGaugeBump R hR n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G
  have hP₀ : ContinuousOn P₀ (closedBall a R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact P.continuous.congr fun z => (hrep z).symm
  obtain ⟨hFc, hFi, hGi, hFb, hGb, hagree⟩ :=
    buffered_gauge_cutoff_data a R hR P₀ A hP₀ hA hδ0 hC hnear hbound
  change (∀ z ∈ closedBall a (3 * R / 4),
    F z = P₀ z ∧ G z = A z * P₀ z) at hagree
  have hsmall (n : ℕ) : (bufferedGaugeBump R hR n).rOut ≤ R / 4 := by
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr (by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)
    change (R / 4) * (1 / ((n : ℝ) + 1)) ≤ R / 4
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ R / 4)
  have hratio (n : ℕ) : (bufferedGaugeBump R hR n).rOut ≤
      2 * (bufferedGaugeBump R hR n).rIn := by
    change (R / 4) * (1 / ((n : ℝ) + 1)) ≤
      2 * (((R / 4) * (1 / ((n : ℝ) + 1))) / 2)
    linarith
  have hQc (n : ℕ) : ContDiff ℝ ∞ (Q n) :=
    (bufferedGaugeBump R hR n).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (bufferedGaugeBump R hR n).contDiff_normed
      hFi.locallyIntegrable
  have hweakFG : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball a (3 * R / 4) →
      (∫ z : ℂ, (((fderiv ℝ φ z 1 : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • F z) =
      -(∫ z : ℂ, φ z • G z) := by
    intro φ hφ hc hs
    have hh := buffered_gauge_cutoff_weak_equation a R hR P P₀ A hrep hweak
      φ (hφ.of_le (by simp)) hc hs
    change (∫ z : ℂ, (((fderiv ℝ φ z 1 : ℂ) +
      Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • F z) =
      -(∫ z : ℂ, (φ z : ℂ) • G z) at hh
    have hcast (z : ℂ) : (φ z : ℂ) • G z = φ z • G z :=
      IsScalarTower.algebraMap_smul ℂ (φ z) (G z)
    simpa only [hcast] using hh
  have hQdbar (n : ℕ) : ∀ z ∈ ball a (R / 2), complexDbar (Q n) z = D n z := by
    simpa only [complexDbar] using normed_bump_convolution_dbar_eq_on_ball
      hFi.locallyIntegrable hGi.locallyIntegrable hweakFG
      (bufferedGaugeBump R hR n) (by linarith [hsmall n])
  refine ⟨hQc, ?_, ?_, ?_⟩
  · intro n z hz
    apply isUnit_and_norm_inverse_le_of_norm_sub_one_le (Q n z) hδ
    apply normed_bump_gauge_near_identity hFc.aestronglyMeasurable hδ0
      (R := 3 * R / 4) (r := R / 2) ?_ (bufferedGaugeBump R hR n)
      (by linarith [hsmall n]) hz
    intro w hw
    change ‖F w - 1‖ ≤ δ
    rw [(hagree w hw).1]
    exact hnear w (closedBall_subset_closedBall (by linarith) hw)
  · intro z hz
    exact isUnit_and_norm_inverse_le_of_norm_sub_one_le (P₀ z) hδ (hnear z hz)
  · intro ψ hψ hψ0 hs
    obtain ⟨hPQi, hPQlim⟩ := weighted_normed_bump_convolution_sub_tendsto_zero
      F hFi.locallyIntegrable (by positivity : 0 ≤ 1 + δ) hFb
      (bufferedGaugeBump R hR) (bufferedGaugeBump_rOut_tendsto R hR) hratio ψ hψ hψ0
    obtain ⟨hGDi, hGDlim⟩ := weighted_normed_bump_convolution_sub_tendsto_zero
      G hGi.locallyIntegrable (mul_nonneg hC (by positivity : 0 ≤ 1 + δ)) hGb
      (bufferedGaugeBump R hR) (bufferedGaugeBump_rOut_tendsto R hR) hratio ψ hψ hψ0
    have hbuffer {z : ℂ} (hz : ψ z ≠ 0) : z ∈ closedBall a (3 * R / 4) := by
      have hz' := hs hz
      exact closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz')
    have hPQeq (n : ℕ) : (fun z => ψ z * ‖Q n z - F z‖) =
        (fun z => ψ z * ‖Q n z - P₀ z‖) := by
      funext z
      by_cases hz : ψ z = 0
      · simp only [hz, zero_mul]
      · rw [(hagree z (hbuffer hz)).1]
    have hPDeq (n : ℕ) : (fun z => ψ z * ‖D n z - G z‖) =
        (fun z => ψ z * ‖A z * P₀ z - complexDbar (Q n) z‖) := by
      funext z
      by_cases hz : ψ z = 0
      · simp only [hz, zero_mul]
      · rw [(hagree z (hbuffer hz)).2, hQdbar n z (hs hz), norm_sub_rev]
    change (∀ n, Integrable (fun z => ψ z * ‖Q n z - F z‖)) at hPQi
    change Tendsto (fun n => ∫ z, ψ z * ‖Q n z - F z‖) atTop (𝓝 0) at hPQlim
    change (∀ n, Integrable (fun z => ψ z * ‖D n z - G z‖)) at hGDi
    change Tendsto (fun n => ∫ z, ψ z * ‖D n z - G z‖) atTop (𝓝 0) at hGDlim
    simp_rw [hPQeq] at hPQi hPQlim
    simp_rw [hPDeq] at hGDi hGDlim
    have hresMeas (n : ℕ) : AEStronglyMeasurable
        (fun z => ψ z * ‖A z * Q n z - complexDbar (Q n) z‖) volume := by
      have hdc : Continuous (complexDbar (Q n)) := by
        unfold complexDbar
        have hd := (hQc n).continuous_fderiv (by simp)
        exact ((hd.clm_apply continuous_const).add
          ((hd.clm_apply continuous_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)
      exact hψ.aestronglyMeasurable.mul
        ((hA.mul (hQc n).continuous.aestronglyMeasurable).sub hdc.aestronglyMeasurable).norm
    obtain ⟨hresi, hreslim⟩ := weighted_gauge_residual_tendsto_zero volume A P₀ Q
      (fun n => complexDbar (Q n)) ψ (Eventually.of_forall hbound)
      (Eventually.of_forall hψ0) hPQi hGDi hresMeas hPQlim hGDlim
    exact ⟨hPQi, hPQlim, hresi, hreslim⟩

private theorem continuousOn_inverse_apply_of_isUnit
    {Ω : Set ℂ} {P : ℂ → V →L[ℂ] V} {ξ : ℂ → V}
    (hP : ContinuousOn P Ω) (hξ : ContinuousOn ξ Ω)
    (hunit : ∀ z ∈ Ω, IsUnit (P z)) :
    ContinuousOn (fun z => Ring.inverse (P z) (ξ z)) Ω := by
  have hi : ContinuousOn (fun z => Ring.inverse (P z)) Ω := by
    intro z hz
    obtain ⟨u, hu⟩ := hunit z hz
    have hinv : ContinuousAt Ring.inverse (P z) := by
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    exact hinv.comp_continuousWithinAt (hP z hz)
  exact hi.clm_apply hξ

/-- The original bounded integral gauge cancels the full same-coefficient system
in the weak sense. Only the bundled disk gauge is continuous; the proof obtains
smooth inverses by mollification and never differentiates the limiting gauge. -/
theorem disk_gauge_inverse_section_weak_equation
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (P : C(closedBall a R, V →L[ℂ] V)) (P₀ A : ℂ → V →L[ℂ] V)
    (hrep : ∀ z : closedBall a R, P₀ z = P z)
    (hA : AEStronglyMeasurable A volume)
    {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1) (hC : 0 ≤ C)
    (hnear : ∀ z ∈ closedBall a R, ‖P₀ z - 1‖ ≤ δ)
    (hbound : ∀ z, ‖A z‖ ≤ C)
    (hweak : ∀ (φ : ℂ → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball a R →
      (∫ z : ℂ, (((fderiv ℝ φ z 1 : ℂ) +
        Complex.I * (fderiv ℝ φ z Complex.I : ℂ)) / 2) • P₀ z) =
      -(∫ w : closedBall a R, (φ (w : ℂ) : ℂ) • (A w * P w)
        ∂(volume.comap ((↑) : closedBall a R → ℂ))))
    (ξ : ℂ → V) (hξ : ContDiffOn ℝ 1 ξ (ball a R))
    (hξeq : ∀ z ∈ ball a R, complexDbar ξ z = A z (ξ z)) :
    ContinuousOn (fun z => Ring.inverse (P₀ z) (ξ z)) (ball a (R / 2)) ∧
      ∀ (φ : ℂ → ℂ), ContDiff ℝ 1 φ → HasCompactSupport φ →
        tsupport φ ⊆ ball a (R / 2) →
        (∫ z, complexDbar φ z • Ring.inverse (P₀ z) (ξ z)) = 0 := by
  let χ := bufferedGaugeCutoff a R hR
  let Q : ℕ → ℂ → V →L[ℂ] V := fun n =>
    (bufferedGaugeBump R hR n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (fun z => χ z • P₀ z)
  obtain ⟨hQc, hQi, hPi, hweights⟩ := disk_gauge_has_controlled_mollifications
    a R hR P P₀ A hrep hA hδ0 hδ hC hnear hbound hweak
  have hsub : closedBall a (R / 2) ⊆ ball a R := by
    intro z hz
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have hξsmall : ContDiffOn ℝ 1 ξ (ball a (R / 2)) :=
    hξ.mono (ball_subset_closedBall.trans hsub)
  have hP₀ : ContinuousOn P₀ (closedBall a R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact P.continuous.congr fun z => (hrep z).symm
  have hsmallR : ball a (R / 2) ⊆ closedBall a R :=
    (ball_subset_closedBall.trans hsub).trans ball_subset_closedBall
  have hPc := hP₀.mono hsmallR
  have hFc : ContinuousOn (fun z => Ring.inverse (P₀ z) (ξ z)) (ball a (R / 2)) :=
    continuousOn_inverse_apply_of_isUnit hPc hξsmall.continuousOn
      (fun z hz => (hPi z (hsmallR hz)).1)
  obtain ⟨M, hM⟩ := (isCompact_closedBall a (R / 2)).exists_bound_of_continuousOn
    (hξ.continuousOn.mono hsub)
  let L := 1 / (1 - δ)
  have hL : 0 ≤ L := div_nonneg zero_le_one (sub_nonneg.mpr hδ.le)
  refine ⟨hFc, ?_⟩
  intro φ hφ hc hs
  have hd : Continuous (complexDbar φ) := by
    unfold complexDbar
    have hdf := hφ.continuous_fderiv one_ne_zero
    exact ((hdf.clm_apply continuous_const).add
      ((hdf.clm_apply continuous_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)
  have hdsub : tsupport (complexDbar φ) ⊆ tsupport φ := by
    apply closure_minimal _ isClosed_closure
    intro z hz
    by_contra hzφ
    have heq : complexDbar φ z = 0 := by
      simp only [complexDbar, fderiv_of_notMem_tsupport ℝ hzφ,
        zero_apply, smul_zero, add_zero]
    exact hz heq
  have hdc : HasCompactSupport (complexDbar φ) :=
    hc.of_isClosed_subset isClosed_closure hdsub
  have hψi : Integrable (fun z => ‖complexDbar φ z‖) :=
    (hd.integrable_of_hasCompactSupport hdc).norm
  have hψsupport : support (fun z => ‖complexDbar φ z‖) ⊆ ball a (R / 2) := by
    intro z hz
    exact hs (hdsub (subset_closure (norm_ne_zero_iff.mp hz)))
  obtain ⟨hPQi, hPQlim, _, _⟩ := hweights (fun z => ‖complexDbar φ z‖)
    hψi (fun _ => norm_nonneg _) hψsupport
  obtain ⟨_, _, hresi, hreslim⟩ := hweights (fun z => ‖φ z‖)
    (hφ.continuous.integrable_of_hasCompactSupport hc).norm
    (fun _ => norm_nonneg _) (by
      intro z hz
      exact hs (subset_closure (norm_ne_zero_iff.mp hz)))
  have hFi : Integrable (fun z => complexDbar φ z • Ring.inverse (P₀ z) (ξ z)) :=
    (hFc.locallyIntegrableOn isOpen_ball.measurableSet).integrable_smul_left_of_hasCompactSupport
      hd hdc (hdsub.trans hs)
  have hFni (n : ℕ) : Integrable
      (fun z => complexDbar φ z • Ring.inverse (Q n z) (ξ z)) := by
    have hFn := continuousOn_inverse_apply_of_isUnit (hQc n).continuous.continuousOn
      hξsmall.continuousOn (fun z hz => (hQi n z (ball_subset_closedBall hz)).1)
    have hlocal : LocallyIntegrableOn
        (fun z => Ring.inverse (Q n z) (ξ z)) (ball a (R / 2)) volume :=
      hFn.locallyIntegrableOn isOpen_ball.measurableSet
    exact hlocal.integrable_smul_left_of_hasCompactSupport hd hdc (hdsub.trans hs)
  have hdiffi (n : ℕ) : Integrable (fun z => ‖complexDbar φ z‖ *
      ‖Ring.inverse (Q n z) (ξ z) - Ring.inverse (P₀ z) (ξ z)‖) := by
    simpa only [Pi.sub_apply, ← smul_sub, norm_smul] using ((hFni n).sub hFi).norm
  obtain ⟨_, hdiffLim⟩ := weighted_inverse_gauge_tendsto_zero volume P₀ Q ξ
    (fun z => ‖complexDbar φ z‖) hL
    (Eventually.of_forall fun z hz => by
      have hz' := hψsupport hz
      exact ⟨(hPi z (hsmallR hz')).1, (hPi z (hsmallR hz')).2,
        hM z (ball_subset_closedBall hz')⟩)
    (fun n => Eventually.of_forall fun z hz => hQi n z
      (ball_subset_closedBall (hψsupport hz)))
    (Eventually.of_forall fun _ => norm_nonneg _) hPQi
    (fun n => (hdiffi n).aestronglyMeasurable) hPQlim
  apply integral_complexDbar_smul_inverse_gauge_eq_zero_of_approximation
    isOpen_ball P₀ A ξ Q hξsmall
    (fun n => ((hQc n).of_le (by simp)).contDiffOn)
    (fun n z hz => (hQi n z (ball_subset_closedBall hz)).1)
    (fun z hz => hξeq z (hsub (ball_subset_closedBall hz))) hL
    (fun n z hz => (hQi n z (ball_subset_closedBall hz)).2)
    (fun z hz => hM z (ball_subset_closedBall hz)) hφ hc hs hFi
    (by simpa only [norm_smul] using hdiffLim) hresi hreslim

end DifferentialGeometry.Analysis
