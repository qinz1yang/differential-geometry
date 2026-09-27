import DifferentialGeometry.Geometry.Metric.CurveEnergy

noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Riemannian

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

theorem ofReal_mul_curveEnergy_le_lintegral_of_inner_le
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {a b mu : ℝ} (hab : a ≤ b)
    (hmu : 0 ≤ mu) (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b))
    (f : ℝ → ℝ) (hf : ∀ t ∈ Ioc a b,
      mu * g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) ≤ f t) :
    ENNReal.ofReal (mu * curveEnergy g gamma a b) ≤ ∫⁻ t in Ioc a b, ENNReal.ofReal (f t) := by
  let e : ℝ → ℝ := fun t => g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
    (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
  have hint : IntegrableOn e (Ioc a b) :=
    (integrableOn_inner_mfderiv_self_of_contMDiffOn g hgamma).mono_set Ioc_subset_Icc_self
  have heq : ENNReal.ofReal (mu * curveEnergy g gamma a b) =
      ∫⁻ t in Ioc a b, ENNReal.ofReal (mu * e t) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul mu)
      (Filter.Eventually.of_forall (fun t => mul_nonneg hmu
        (DifferentialGeometry.metric_inner_self_nonneg _ _ _)))]
    congr 1
    rw [integral_const_mul, curveEnergy, intervalIntegral.integral_of_le hab]
    rfl
  rw [heq]
  exact setLIntegral_mono' measurableSet_Ioc (fun t ht => ENNReal.ofReal_le_ofReal (hf t ht))

theorem ofReal_mul_sq_div_le_lintegral_of_inner_le_of_endpoint_separation
    (g : SmoothRiemannianMetric I M) {gamma : ℝ → M} {a b mu r : ℝ} (hab : a < b)
    (hmu : 0 ≤ mu) (hr : 0 ≤ r)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b))
    (f : ℝ → ℝ) (hf : ∀ t ∈ Ioc a b,
      mu * g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) ≤ f t)
    (hsep : ENNReal.ofReal r ≤ riemannianEDistOf g (gamma a) (gamma b)) :
    ENNReal.ofReal (mu * r ^ 2 / (b - a)) ≤ ∫⁻ t in Ioc a b, ENNReal.ofReal (f t) := by
  have hint := integrableOn_inner_mfderiv_self_of_contMDiffOn g hgamma
  have hd := edistOf_le_energy g hab.le hgamma hint
  have hfinite : riemannianEDistOf g (gamma a) (gamma b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd
  have hdist : r ≤ (riemannianEDistOf g (gamma a) (gamma b)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hsep
  have henergy := riemannianEDistOf_toReal_sq_le_curveEnergy g hab.le hgamma hint
  have hsq := (pow_le_pow_left₀ hr hdist 2).trans henergy
  have hmul := mul_le_mul_of_nonneg_left hsq hmu
  have hbound : mu * r ^ 2 / (b - a) ≤ mu * curveEnergy g gamma a b := by
    apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
    nlinarith
  exact (ENNReal.ofReal_le_ofReal hbound).trans
    (ofReal_mul_curveEnergy_le_lintegral_of_inner_le g hab.le hmu hgamma f hf)

end DifferentialGeometry.Geometry.Riemannian

end
