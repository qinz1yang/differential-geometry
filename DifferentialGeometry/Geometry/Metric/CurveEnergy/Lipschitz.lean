import DifferentialGeometry.Geometry.Metric.ScalarCurveComparison
import DifferentialGeometry.Geometry.Metric.LipschitzCurves
import DifferentialGeometry.Topology.EMetricSpace.FiniteDistanceLipschitz
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

section

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

private theorem norm_sub_sq_le_length_mul_integral_deriv_sq
    {ν : ℝ → ℝ} {C : ℝ≥0} (hν : LipschitzWith C ν) {a b : ℝ} (hab : a ≤ b) :
    ‖ν b - ν a‖ ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖deriv ν t‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hd : MemLp (deriv ν) 2 μ := MemLp.of_bound (aestronglyMeasurable_deriv ν _) C
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hν)
  have hac := hν.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have hnorm : ‖ν b - ν a‖ ≤ ∫ t, ‖deriv ν t‖ ∂μ := by
    rw [← hac.integral_deriv_eq_sub]
    calc
      _ ≤ ∫ t in uIoc a b, ‖deriv ν t‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ = ∫ t, ‖deriv ν t‖ ∂μ := by
        rw [uIoc_of_le hab]
        exact integral_Icc_eq_integral_Ioc.symm
  have hholder : (∫ t, ‖deriv ν t‖ ∂μ) ≤
      Real.sqrt (b - a) * Real.sqrt (∫ t, ‖deriv ν t‖ ^ 2 ∂μ) := by
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun t => ‖deriv ν t‖)
      (by simpa using (memLp_const (p := 2) (μ := μ) (1 : ℝ)))
      (by simpa using hd.norm)
    simpa only [norm_one, norm_norm, one_mul, one_pow, integral_const, Measure.real, μ,
      Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul, mul_one,
      Real.one_rpow, Real.rpow_two, ← Real.sqrt_eq_rpow] using h
  have hnonneg : 0 ≤ ∫ t, ‖deriv ν t‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  calc
    ‖ν b - ν a‖ ^ 2 ≤
        (Real.sqrt (b - a) * Real.sqrt (∫ t, ‖deriv ν t‖ ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hholder) 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hab), Real.sq_sqrt hnonneg]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_toReal_sq_le_interval_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    {a b : ℝ} (hab : a ≤ b)
    (henergy : IntegrableOn (fun t => (riemannianCurveSpeed g γ t) ^ 2) (Icc a b)) :
    (riemannianEDistOf g (γ a) (γ b)).toReal ^ 2 ≤
      (b - a) * ∫ t in Icc a b, (riemannianCurveSpeed g γ t) ^ 2 := by
  let : IsManifold 𝓘(ℝ, E) 1 M :=
    IsManifold.of_le (I := 𝓘(ℝ, E)) (M := M) (n := ∞) (by decide)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  have hγLip : LipschitzWith C γ := hγ
  have hfin (t : ℝ) : edist (γ t) (γ a) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top t a)) (hγLip t a)
  let ν : ℝ → ℝ := fun t => (edist (γ t) (γ a)).toReal
  have hν : LipschitzWith C ν := EMetric.lipschitzWith_toReal_edist_comp hγLip (γ a) hfin
  have hνa : ν a = 0 := by simp only [ν, edist_self, ENNReal.toReal_zero]
  have hder : ∀ᵐ t ∂volume, ‖deriv ν t‖ ^ 2 ≤ (riemannianCurveSpeed g γ t) ^ 2 := by
    filter_upwards [ae_mdifferentiableAt_riemannian_curve g hγ, hν.ae_differentiableAt_real]
      with t ht hνt
    have hb := abs_deriv_le_of_riemannian_distance_bound g ht hνt (fun y => by
      change |(edist (γ y) (γ a)).toReal - (edist (γ t) (γ a)).toReal| ≤
        (edist (γ t) (γ y)).toReal
      simpa only [edist_comm (γ y) (γ t)] using
        EMetric.abs_toReal_edist_sub_le_of_edist_ne_top (hfin y) (hfin t))
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hb) 2
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hd : MemLp (deriv ν) 2 μ := MemLp.of_bound (aestronglyMeasurable_deriv ν _) C
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hν)
  have hcompare : (∫ t in Icc a b, ‖deriv ν t‖ ^ 2) ≤
      ∫ t in Icc a b, (riemannianCurveSpeed g γ t) ^ 2 :=
    integral_mono_ae hd.norm.integrable_sq henergy (ae_restrict_of_ae hder)
  have hscalar := norm_sub_sq_le_length_mul_integral_deriv_sq hν hab
  rw [hνa, sub_zero, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hscalar
  have hdist : ν b = (riemannianEDistOf g (γ a) (γ b)).toReal := by
    change (edist (γ b) (γ a)).toReal = (edist (γ a) (γ b)).toReal
    rw [edist_comm]
  change ν b ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖deriv ν t‖ ^ 2 at hscalar
  rw [hdist] at hscalar
  exact hscalar.trans (mul_le_mul_of_nonneg_left hcompare (sub_nonneg.mpr hab))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_le_ofReal_sqrt_interval_energy
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * edist x y)
    {a b : ℝ} (hab : a ≤ b)
    (henergy : IntegrableOn (fun t => (riemannianCurveSpeed g γ t) ^ 2) (Icc a b)) :
    riemannianEDistOf g (γ a) (γ b) ≤ ENNReal.ofReal
      (Real.sqrt ((b - a) * ∫ t in Icc a b, (riemannianCurveSpeed g γ t) ^ 2)) := by
  have hfin : riemannianEDistOf g (γ a) (γ b) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top a b)) (hγ a b)
  apply (ENNReal.le_ofReal_iff_toReal_le hfin (Real.sqrt_nonneg _)).mpr
  have hs := Real.sqrt_le_sqrt (riemannianEDistOf_toReal_sq_le_interval_energy g hγ hab henergy)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hs

end DifferentialGeometry.Geometry

end

end
