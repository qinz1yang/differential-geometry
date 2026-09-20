import DifferentialGeometry.Analysis.Parabolic.WeakEquation.ProductTest
import DifferentialGeometry.Analysis.Integration.Integral.WeightedCutoffMass


noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open Filter MeasureTheory
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M]
variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

theorem integrable_and_tendsto_integral_integral_parabolic_test_residual_prod_zero_of_const_mass
    (μ : Measure ℝ) (ν : ℝ → Measure M)
    (g : ℝ → SmoothRiemannianMetric I M) (w : ℝ × M → ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    (η : ℝ → ℝ) (χ : ι → M → ℝ)
    (hχmeas : ∀ᶠ i in l, Measurable (χ i))
    (hχbound : ∀ᶠ i in l, ∀ x, ‖χ i x‖ ≤ 1)
    (hχone : ∀ x, Tendsto (fun i => χ i x) l (𝓝 1))
    (hw : ∀ᵐ t ∂μ, Integrable (fun x => w (t, x)) (ν t))
    (hwnonneg : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, 0 ≤ w (t, x))
    (m : ℝ) (hmass : ∀ᵐ t ∂μ, (∫ x, w (t, x) ∂ν t) = m)
    (hηderiv : Integrable (deriv η) μ)
    (hηzero : (∫ t, deriv η t ∂μ) = 0)
    (hmassOuter : ∀ᶠ i in l,
      AEStronglyMeasurable (fun t => ∫ x, χ i x * w (t, x) ∂ν t) μ)
    (hfluxSpatial : ∀ᶠ i in l, ∀ᵐ t ∂μ,
      Integrable (fun x => η t *
        (w (t, x) * (g t).inner x (X t x) (gradientFun (g t) (χ i) x))) (ν t))
    (hfluxTime : ∀ᶠ i in l, Integrable (fun t => η t *
      (∫ x, w (t, x) * (g t).inner x (X t x) (gradientFun (g t) (χ i) x) ∂ν t)) μ)
    (hfluxZero : Tendsto (fun i => ∫ t, η t *
      (∫ x, w (t, x) * (g t).inner x (X t x) (gradientFun (g t) (χ i) x) ∂ν t) ∂μ)
      l (𝓝 0)) :
    let R := fun (i : ι) (t : ℝ) (x : M) => w (t, x) *
      (deriv (fun s => η s * χ i x) t +
        (g t).inner x (X t x) (gradientFun (g t) (fun y => η t * χ i y) x))
    (∀ᶠ i in l, (∀ᵐ t ∂μ, Integrable (R i t) (ν t)) ∧
      Integrable (fun t => ∫ x, R i t x ∂ν t) μ) ∧
      Tendsto (fun i => ∫ t, ∫ x, R i t x ∂ν t ∂μ) l (𝓝 0) := by
  intro R
  have hnormmass : ∀ᵐ t ∂μ, (∫ x, ‖w (t, x)‖ ∂ν t) = m := by
    filter_upwards [hwnonneg, hmass] with t ht hmt
    rw [← hmt]
    apply integral_congr_ae
    filter_upwards [ht] with x hx
    exact Real.norm_of_nonneg hx
  have hmassSpatial : ∀ᶠ i in l, ∀ᵐ t ∂μ,
      Integrable (fun x => deriv η t * (χ i x * w (t, x))) (ν t) := by
    filter_upwards [hχmeas, hχbound] with i hiMeas hiBound
    filter_upwards [hw] with t ht
    apply Integrable.const_mul
    apply ht.mono (hiMeas.aestronglyMeasurable.mul ht.aestronglyMeasurable)
    exact ae_of_all (ν t) fun x => by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hiBound x)
  have hmassTime : ∀ᶠ i in l,
      Integrable (fun t => deriv η t * (∫ x, χ i x * w (t, x) ∂ν t)) μ := by
    filter_upwards [hχbound, hmassOuter] with i hiBound hiOuter
    apply (hηderiv.norm.mul_const m).mono' (hηderiv.aestronglyMeasurable.mul hiOuter)
    filter_upwards [hw, hnormmass] with t ht hmt
    simp only [Pi.mul_apply, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      ‖∫ x, χ i x * w (t, x) ∂ν t‖ ≤ ∫ x, ‖w (t, x)‖ ∂ν t := by
        apply norm_integral_le_of_norm_le ht.norm
        exact ae_of_all (ν t) fun x => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hiBound x)
      _ = m := hmt
  have hsplit : ∀ᶠ i in l,
      (∀ᵐ t ∂μ, Integrable (R i t) (ν t)) ∧
        Integrable (fun t => ∫ x, R i t x ∂ν t) μ ∧
        (∫ t, ∫ x, R i t x ∂ν t ∂μ) =
          (∫ t, deriv η t * (∫ x, χ i x * w (t, x) ∂ν t) ∂μ) +
            ∫ t, η t *
              (∫ x, w (t, x) * (g t).inner x (X t x)
                (gradientFun (g t) (χ i) x) ∂ν t) ∂μ := by
    filter_upwards [hmassSpatial, hfluxSpatial, hmassTime, hfluxTime]
      with i hiMassSpatial hiFluxSpatial hiMassTime hiFluxTime
    exact integrable_and_integral_integral_parabolic_test_residual_prod μ ν g w X η (χ i)
      hiMassSpatial hiFluxSpatial hiMassTime hiFluxTime
  refine ⟨hsplit.mono fun _ hi => ⟨hi.1, hi.2.1⟩, ?_⟩
  have hmassZero := tendsto_integral_weighted_cutoff_mass_zero_of_const_mass μ ν
    (deriv η) (fun t x => w (t, x)) χ hχmeas hχbound hχone hw hwnonneg m hmass
    hηderiv hηzero hmassOuter
  have hsum := hmassZero.add hfluxZero
  have heq : (fun i =>
      (∫ t, deriv η t * (∫ x, χ i x * w (t, x) ∂ν t) ∂μ) +
        ∫ t, η t *
          (∫ x, w (t, x) * (g t).inner x (X t x) (gradientFun (g t) (χ i) x) ∂ν t) ∂μ)
      =ᶠ[l] (fun i => ∫ t, ∫ x, R i t x ∂ν t ∂μ) :=
    hsplit.mono fun _ hi => hi.2.2.symm
  simpa only [zero_add] using Filter.Tendsto.congr' heq hsum

end DifferentialGeometry.Geometry.Operator
