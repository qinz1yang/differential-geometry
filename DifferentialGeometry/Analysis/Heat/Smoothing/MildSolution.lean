import DifferentialGeometry.Analysis.Heat.Semigroup.ClassicalSolution
import DifferentialGeometry.Analysis.Heat.Smoothing.SmoothingOfClosed
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeEndpoint

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge
open DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def mildForcingCoeff
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (i : EigenIdx (I := I) (M := M) g) (t : ℝ) : ℝ :=
  ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, f t⟫_ℝ

def forcingSpectralMass
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (t : ℝ) (k : ℕ) (i : EigenIdx (I := I) (M := M) g) : ℝ :=
  (1 + EigenIdx.lambda (I := I) (M := M) i) ^ k *
    ∫ s in (0 : ℝ)..t, (mildForcingCoeff (I := I) (M := M) g f i s) ^ 2

theorem mildForcingCoeff_continuous
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) (i : EigenIdx (I := I) (M := M) g) :
    Continuous (mildForcingCoeff (I := I) (M := M) g f i) := by
  exact (innerSL (𝕜 := ℝ)
    (E := Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (resolventHilbertEigenbasisSigma (I := I) (M := M) g i)).continuous.comp hf

theorem summable_one_add_lambda_pow_succ_mildForcingConv
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g f t k))
    (k : ℕ) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
        (perModeConv (EigenIdx.lambda (I := I) (M := M) i)
          (mildForcingCoeff (I := I) (M := M) g f i) t) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    ((hmass k).mul_left (t + 1 / 2))
  · exact mul_nonneg (pow_nonneg (by
        linarith [lambda_nonneg (I := I) (M := M) i]) _)
      (sq_nonneg _)
  · have hgain :=
      DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.one_add_lambda_mul_perModeConv_endpoint_sq_le
        (f := mildForcingCoeff (I := I) (M := M) g f i)
        (EigenIdx.lambda (I := I) (M := M) i)
        (lambda_nonneg (I := I) (M := M) i)
        (mildForcingCoeff_continuous (I := I) (M := M) g hf i) ht.le
    have hpow_nn : 0 ≤
        (1 + EigenIdx.lambda (I := I) (M := M) i) ^ k :=
      pow_nonneg (by linarith [lambda_nonneg (I := I) (M := M) i]) _
    calc
      (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (k + 1) *
          (perModeConv (EigenIdx.lambda (I := I) (M := M) i)
            (mildForcingCoeff (I := I) (M := M) g f i) t) ^ 2 =
          (1 + EigenIdx.lambda (I := I) (M := M) i) ^ k *
            ((1 + EigenIdx.lambda (I := I) (M := M) i) *
              (perModeConv (EigenIdx.lambda (I := I) (M := M) i)
                (mildForcingCoeff (I := I) (M := M) g f i) t) ^ 2) := by
            rw [pow_succ]
            ring
      _ ≤ (1 + EigenIdx.lambda (I := I) (M := M) i) ^ k *
          ((t + 1 / 2) * ∫ s in (0 : ℝ)..t,
            (mildForcingCoeff (I := I) (M := M) g f i s) ^ 2) :=
        mul_le_mul_of_nonneg_left hgain hpow_nn
      _ = (t + 1 / 2) *
          forcingSpectralMass (I := I) (M := M) g f t k i := by
        simp only [forcingSpectralMass]
        ring

theorem mildSolution_zero_initial_inner_basis
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t)
    (i : EigenIdx (I := I) (M := M) g) :
    ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
      mildSolution (I := I) (M := M) g 0 f t⟫_ℝ =
      perModeConv (EigenIdx.lambda (I := I) (M := M) i)
        (mildForcingCoeff (I := I) (M := M) g f i) t := by
  rw [mildSolution_inner_basis (I := I) (M := M) g 0 hf ht i]
  simp only [inner_zero_right, mul_zero, zero_add, mildForcingCoeff, perModeConv]
  ring_nf

theorem mildSolution_zero_initial_weighted_coeff_summable
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g f t k))
    (k : ℕ) :
    Summable (fun i : EigenIdx (I := I) (M := M) g =>
      (1 + EigenIdx.lambda (I := I) (M := M) i) ^ (2 * k) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          mildSolution (I := I) (M := M) g 0 f t⟫_ℝ ^ 2) := by
  have htop := summable_one_add_lambda_pow_succ_mildForcingConv
    (I := I) (M := M) g hf ht hmass (2 * k)
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) htop
  · exact mul_nonneg (pow_nonneg (by
        linarith [lambda_nonneg (I := I) (M := M) i]) _)
      (sq_nonneg _)
  · rw [mildSolution_zero_initial_inner_basis (I := I) (M := M) g hf ht.le i]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀
        (by linarith [lambda_nonneg (I := I) (M := M) i]) (by omega))
      (sq_nonneg _)

theorem mildSolution_zero_initial_mem_laplacianDomainPow_all
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g f t k)) :
    ∀ k : ℕ, ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          mildSolution (I := I) (M := M) g 0 f t := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨u_h, hu_h, hu_eq⟩ :=
      exists_laplacianDomainPow_succ_lift_of_weighted_coeff_summable
        (I := I) (M := M) g (mildSolution (I := I) (M := M) g 0 f t) 0
        (mildSolution_zero_initial_weighted_coeff_summable
          (I := I) (M := M) g hf ht hmass 1)
    exact ⟨u_h, by rw [laplacianDomainPow_zero]; exact Submodule.mem_top, hu_eq⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact exists_laplacianDomainPow_succ_lift_of_weighted_coeff_summable
      (I := I) (M := M) g (mildSolution (I := I) (M := M) g 0 f t) k
      (mildSolution_zero_initial_weighted_coeff_summable
        (I := I) (M := M) g hf ht hmass (k + 1))

theorem mildSolution_zero_initial_smooth_representative
    (g : SmoothRiemannianMetric I M)
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g f t k)) :
    ∃ u_smooth : SmoothScalar g,
      ((mildSolution (I := I) (M := M) g 0 f t :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] u_smooth.toFun := by
  obtain ⟨u_smooth, hu_smooth, hu_ae⟩ :=
    smooth_representative_of_memWkpChart_forall
      (I := I) (M := M) g (mildSolution (I := I) (M := M) g 0 f t) (by
        intro k
        obtain ⟨u_h, hu_h, hu_eq⟩ :=
          mildSolution_zero_initial_mem_laplacianDomainPow_all
            (I := I) (M := M) g hf ht hmass k
        have hreg := memWkpChart_two_k_of_laplacianDomainPow_unconditional
          (I := I) (M := M) g k hu_h
        have hcoe : ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =
            ((mildSolution (I := I) (M := M) g 0 f t :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
          rw [hu_eq]
        rw [hcoe] at hreg
        exact hreg)
  exact ⟨⟨u_smooth, hu_smooth⟩, hu_ae⟩

theorem mildSolution_smooth_representative_of_forcingSpectralMass
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g f t k)) :
    ∃ u_smooth : SmoothScalar g,
      smoothToLp (I := I) (M := M) g u_smooth =
        mildSolution (I := I) (M := M) g u_0 f t := by
  obtain ⟨u_heat_fun, hu_heat_smooth, hu_heat_ae⟩ :=
    heatSemigroup_smooth_representative_of_closed
    (I := I) (M := M) g ht u_0
  let u_heat : SmoothScalar g := ⟨u_heat_fun, hu_heat_smooth⟩
  obtain ⟨u_force, hu_force_ae⟩ := mildSolution_zero_initial_smooth_representative
    (I := I) (M := M) g hf ht hmass
  have hu_heat : smoothToLp (I := I) (M := M) g u_heat =
      heatSemigroup (I := I) (M := M) g t u_0 := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp u_heat.memLp_two).trans hu_heat_ae.symm
  have hu_force : smoothToLp (I := I) (M := M) g u_force =
      mildSolution (I := I) (M := M) g 0 f t := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp u_force.memLp_two).trans hu_force_ae.symm
  refine ⟨u_heat + u_force, ?_⟩
  rw [map_add, hu_heat, hu_force]
  unfold mildSolution
  rw [(heatSemigroup (I := I) (M := M) g t).map_zero, zero_add]

theorem mildSolution_has_classical_representatives_of_forcingSpectralMass
    (g : SmoothRiemannianMetric I M)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ 1 f) {t : ℝ} (ht : 0 < t)
    (hmass : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g f t k))
    (hmass_deriv : ∀ k : ℕ,
      Summable (forcingSpectralMass (I := I) (M := M) g (deriv f) t k))
    (f_smooth : SmoothScalar g)
    (hf_smooth : smoothToLp (I := I) (M := M) g f_smooth = f t) :
    ∃ u_smooth du_smooth : SmoothScalar g,
      smoothToLp (I := I) (M := M) g u_smooth =
          mildSolution (I := I) (M := M) g u_0 f t ∧
        smoothToLp (I := I) (M := M) g du_smooth =
          -(heatPower (I := I) (M := M) g 1 t u_0) +
            mildSolution (I := I) (M := M) g (f 0) (deriv f) t ∧
        du_smooth = u_smooth.laplacian + f_smooth := by
  obtain ⟨u_smooth, hu_smooth⟩ :=
    mildSolution_smooth_representative_of_forcingSpectralMass
      (I := I) (M := M) g u_0 hf.continuous ht hmass
  obtain ⟨du_heat, hdu_heat_ae⟩ := heatPower_smooth_representative_of_closed
    (I := I) (M := M) g 1 ht u_0
  have hdu_heat : smoothToLp (I := I) (M := M) g du_heat =
      heatPower (I := I) (M := M) g 1 t u_0 := by
    apply Lp.ext
    exact (MemLp.coeFn_toLp du_heat.memLp_two).trans hdu_heat_ae.symm
  obtain ⟨du_force, hdu_force⟩ :=
    mildSolution_smooth_representative_of_forcingSpectralMass
      (I := I) (M := M) g (f 0) hf.continuous_deriv_one ht hmass_deriv
  let du_smooth : SmoothScalar g := -du_heat + du_force
  have hdu_smooth : smoothToLp (I := I) (M := M) g du_smooth =
      -(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) (deriv f) t := by
    simp only [du_smooth, map_add, map_neg, hdu_heat, hdu_force]
  refine ⟨u_smooth, du_smooth, hu_smooth, hdu_smooth, ?_⟩
  exact mildSolution_smooth_representatives_satisfy_heat_equation
    (I := I) (M := M) g u_0 hf ht u_smooth du_smooth f_smooth
    hu_smooth hdu_smooth hf_smooth

end HeatEquation
end Analysis
end DifferentialGeometry

end
