import DifferentialGeometry.Analysis.Parabolic.Energy.Caccioppoli
import DifferentialGeometry.Bundle.PartialMfderiv

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Energy

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem localized_energy_differential_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (cutoff : SmoothScalar g)
    (u dissipation error : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hdissipation : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => dissipation p.1 p.2))
    (herror : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => error p.1 p.2))
    (t : ℝ)
    (hpde : ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x +
          dissipation t x ≤
        deriv (fun s => u s x) t)
    (hcross : ∀ x : M,
      2 * cutoff.toFun x *
          g.inner x
            (gradientFun (I := I) g cutoff.toFun x)
            (gradientFun (I := I) g
              (smoothScalarSlice (I := I) g u hu t).toFun x) ≤
        (1 / 2 : ℝ) * cutoff.toFun x ^ 2 * dissipation t x + error t x) :
    (1 / 2 : ℝ) *
        ∫ x, cutoff.toFun x ^ 2 * dissipation t x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
      deriv
          (fun s => localizedIntegral (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu s)) t +
        ∫ x, error t x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let ut := smoothScalarSlice (I := I) g u hu t
  let test : SmoothScalar g :=
    ⟨fun x => cutoff.toFun x ^ 2, cutoff.smooth.pow 2⟩
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hdissipation_cont : Continuous (fun x : M => dissipation t x) :=
    hdissipation.continuous.comp (continuous_const.prodMk continuous_id)
  have herror_cont : Continuous (fun x : M => error t x) :=
    herror.continuous.comp (continuous_const.prodMk continuous_id)
  have hcross_cont : Continuous (fun x : M =>
      cutoff.toFun x *
        g.inner x
          (gradientFun (I := I) g cutoff.toFun x)
          (gradientFun (I := I) g ut.toFun x)) := by
    have hinner := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g cutoff.toContMDiffMap) (grad_g (I := I) g ut.toContMDiffMap)
    exact cutoff.smooth.continuous.mul
      (by simpa only [grad_g_apply] using hinner.continuous)
  have hlap_cont : Continuous (fun x : M => Δ_g (I := I) g ut.toContMDiffMap x) :=
    (Δ_g_contMDiff (I := I) g ut.toContMDiffMap).continuous
  let F : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; ℝ⟯ := ⟨fun p => u p.1 p.2, hu⟩
  have htime_cont : Continuous (fun x : M => deriv (fun s => u s x) t) := by
    have hpartial := DifferentialGeometry.contMDiff_partial_deriv_fst I F
    exact (hpartial.comp (contMDiff_const.prodMk contMDiff_id)).continuous
  have hdissipation_int : Integrable (fun x : M =>
      cutoff.toFun x ^ 2 * dissipation t x) μ :=
    ((cutoff.smooth.continuous.pow 2).mul hdissipation_cont)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have herror_int : Integrable (fun x : M => error t x) μ :=
    herror_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcross_int : Integrable (fun x : M =>
      cutoff.toFun x *
        g.inner x
          (gradientFun (I := I) g cutoff.toFun x)
          (gradientFun (I := I) g ut.toFun x)) μ :=
    hcross_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlap_int : Integrable (fun x : M =>
      cutoff.toFun x ^ 2 * Δ_g (I := I) g ut.toContMDiffMap x) μ :=
    ((cutoff.smooth.continuous.pow 2).mul hlap_cont)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have htime_int : Integrable (fun x : M =>
      cutoff.toFun x ^ 2 * deriv (fun s => u s x) t) μ :=
    ((cutoff.smooth.continuous.pow 2).mul htime_cont)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpointwise : ∀ x : M,
      cutoff.toFun x ^ 2 * Δ_g (I := I) g ut.toContMDiffMap x +
          cutoff.toFun x ^ 2 * dissipation t x ≤
        cutoff.toFun x ^ 2 * deriv (fun s => u s x) t := by
    intro x
    have hmul := mul_le_mul_of_nonneg_left (hpde x) (sq_nonneg (cutoff.toFun x))
    simpa only [mul_add] using hmul
  have htime_le :
      (∫ x, cutoff.toFun x ^ 2 * Δ_g (I := I) g ut.toContMDiffMap x ∂μ) +
          ∫ x, cutoff.toFun x ^ 2 * dissipation t x ∂μ ≤
        ∫ x, cutoff.toFun x ^ 2 * deriv (fun s => u s x) t ∂μ := by
    rw [← integral_add hlap_int hdissipation_int]
    exact integral_mono (hlap_int.add hdissipation_int) htime_int hpointwise
  have hgreen :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      (I := I) g test.smooth ut.smooth (HasCompactSupport.of_compactSpace _)
  have htest_pointwise : ∀ x : M,
      g.inner x
          (gradientFun (I := I) g test.toFun x)
          (gradientFun (I := I) g ut.toFun x) =
        2 * cutoff.toFun x *
          g.inner x
            (gradientFun (I := I) g cutoff.toFun x)
            (gradientFun (I := I) g ut.toFun x) := by
    intro x
    dsimp only [test]
    rw [gradientFun_pow (I := I) g 1
      (cutoff.smooth.mdifferentiable (by simp) x)]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hlap_identity :
      (∫ x, cutoff.toFun x ^ 2 * Δ_g (I := I) g ut.toContMDiffMap x ∂μ) =
        -2 * ∫ x, cutoff.toFun x *
          g.inner x
            (gradientFun (I := I) g cutoff.toFun x)
            (gradientFun (I := I) g ut.toFun x) ∂μ := by
    have hgreen' :
        2 * ∫ x, cutoff.toFun x *
            g.inner x
              (gradientFun (I := I) g cutoff.toFun x)
              (gradientFun (I := I) g ut.toFun x) ∂μ =
          -∫ x, cutoff.toFun x ^ 2 * Δ_g (I := I) g ut.toContMDiffMap x ∂μ := by
      calc
        2 * ∫ x, cutoff.toFun x *
              g.inner x
                (gradientFun (I := I) g cutoff.toFun x)
                (gradientFun (I := I) g ut.toFun x) ∂μ =
            ∫ x, 2 * (cutoff.toFun x *
              g.inner x
                (gradientFun (I := I) g cutoff.toFun x)
                (gradientFun (I := I) g ut.toFun x)) ∂μ := by
              rw [integral_const_mul]
        _ = ∫ x, g.inner x
              (gradientFun (I := I) g test.toFun x)
              (gradientFun (I := I) g ut.toFun x) ∂μ := by
              exact integral_congr_ae (ae_of_all μ fun x => by
                simpa only [mul_assoc] using (htest_pointwise x).symm)
        _ = -∫ x, cutoff.toFun x ^ 2 * Δ_g (I := I) g ut.toContMDiffMap x ∂μ := by
              simpa only [μ, test, ut, smoothScalarSlice_toFun,
                grad_g_apply] using hgreen
    linarith
  have hcross_integral :
      2 * ∫ x, cutoff.toFun x *
          g.inner x
            (gradientFun (I := I) g cutoff.toFun x)
            (gradientFun (I := I) g ut.toFun x) ∂μ ≤
        (1 / 2 : ℝ) *
            ∫ x, cutoff.toFun x ^ 2 * dissipation t x ∂μ +
          ∫ x, error t x ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul]
    rw [← integral_add (hdissipation_int.const_mul (1 / 2)) herror_int]
    exact integral_mono (hcross_int.const_mul 2)
      ((hdissipation_int.const_mul (1 / 2)).add herror_int)
      (fun x => by simpa only [mul_assoc] using hcross x)
  have hmass := hasDerivAt_localizedIntegral
    (I := I) (M := M) cutoff u hu t
  rw [hmass.deriv]
  rw [hlap_identity] at htime_le
  linarith

end DifferentialGeometry.Analysis.Parabolic.Energy

end
