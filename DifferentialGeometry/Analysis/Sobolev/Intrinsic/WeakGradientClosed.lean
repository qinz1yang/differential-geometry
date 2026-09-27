import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakGradientLimit
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakProduct
import DifferentialGeometry.Analysis.Integration.L2Convergence

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma abs_sqrt_inner_sub_le (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    |Real.sqrt (g.inner x v v) - Real.sqrt (g.inner x w w)| ≤
      Real.sqrt (g.inner x (v - w) (v - w)) := by
  have hsym : Real.sqrt (g.inner x (w - v) (w - v)) =
      Real.sqrt (g.inner x (v - w) (v - w)) := by
    have heq : w - v = (-1 : ℝ) • (v - w) := by simp
    rw [heq, Geometry.Riemannian.sqrt_inner_smul]
    norm_num
  have hv := Geometry.Riemannian.sqrt_inner_add_le g x (v - w) w
  have hw := Geometry.Riemannian.sqrt_inner_add_le g x (w - v) v
  rw [sub_add_cancel] at hv hw
  rw [hsym] at hw
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [Module.Finite ℝ E] in
private lemma continuous_fiber_metric_norm (g : SmoothRiemannianMetric I M) (x : M) :
    Continuous (fun v : TangentSpace I x => Real.sqrt (g.inner x v v)) :=
  Real.continuous_sqrt.comp ((g.inner x).continuous.clm_apply continuous_id)

variable [CompactSpace M] [T2Space M]


theorem tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto
    (g : SmoothRiemannianMetric I M) {V : ℕ → ∀ x : M, TangentSpace I x}
    {G : ∀ x : M, TangentSpace I x}
    (hmetric : Tendsto (fun n => eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2
      (riemannianVolumeMeasure I M g)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Real.sqrt (g.inner x (V n x) (V n x)) -
      Real.sqrt (g.inner x (G x) (G x))) 2 (riemannianVolumeMeasure I M g)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmetric (fun _ => bot_le)
  intro n
  apply eLpNorm_mono_ae
  filter_upwards with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
    abs_sqrt_inner_sub_le g x (V n x) (G x)


theorem memLp_metric_norm_of_smooth_limit (g : SmoothRiemannianMetric I M)
    (V : ℕ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {G : ∀ x : M, TangentSpace I x}
    (hpoint : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      Tendsto (fun n => V n x) atTop (𝓝 (G x)))
    (hmetric : Tendsto (fun n => eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2
      (riemannianVolumeMeasure I M g)) atTop (𝓝 0)) :
    MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 2
      (riemannianVolumeMeasure I M g) := by
  let μ := riemannianVolumeMeasure I M g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hV (n : ℕ) : Continuous (fun x => Real.sqrt (g.inner x (V n x) (V n x))) :=
    Real.continuous_sqrt.comp (TangentBundle.continuous_g_inner_of_smooth_sections g (V n) (V n))
  have hmeas : AEStronglyMeasurable (fun x => Real.sqrt (g.inner x (G x) (G x))) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hV n).aestronglyMeasurable)
    filter_upwards [hpoint] with x hx
    exact ((continuous_fiber_metric_norm g x).tendsto _).comp hx
  apply Lp.memLp_of_cauchy_tendsto (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (fun n => (hV n).memLp_of_hasCompactSupport (isClosed_tsupport _).isCompact) _ hmeas
  exact tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto g hmetric


theorem HasWeakRiemannianGradLp.of_metricL2_limit [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {f : ℕ → M → ℝ} {u : M → ℝ}
    (V : ℕ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {G : ∀ x : M, TangentSpace I x}
    (hf : ∀ n, MemLp (f n) 2 (riemannianVolumeMeasure I M g))
    (hu : MemLp u 2 (riemannianVolumeMeasure I M g))
    (hweak : ∀ n, HasWeakRiemannianGradLp g (f n) (fun x => V n x))
    (hpoint : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      Tendsto (fun n => V n x) atTop (𝓝 (G x)))
    (hscalar : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2
      (riemannianVolumeMeasure I M g)) atTop (𝓝 0))
    (hmetric : Tendsto (fun n => eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2
      (riemannianVolumeMeasure I M g)) atTop (𝓝 0)) :
    HasWeakRiemannianGradLp g u G := by
  let μ := riemannianVolumeMeasure I M g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hpair (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
      AEStronglyMeasurable (fun x => g.inner x (G x) (X x)) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hweak n).1 X)
    filter_upwards [hpoint] with x hx
    exact (((g.inner x).continuous.clm_apply continuous_const).tendsto (G x)).comp hx
  refine ⟨hpair, fun X hX => ?_⟩
  have hXcont : Continuous (fun x => Real.sqrt (g.inner x (X x) (X x))) :=
    Real.continuous_sqrt.comp (TangentBundle.continuous_g_inner_of_smooth_sections g X X)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hXcont.continuousOn
  have hpair2 : Tendsto (fun n => eLpNorm
      (fun x => g.inner x (V n x) (X x) - g.inner x (G x) (X x)) 2 μ) atTop (𝓝 0) := by
    have hboundlim : Tendsto (fun n => ENNReal.ofReal C * eLpNorm (fun x => Real.sqrt
        (g.inner x (V n x - G x) (V n x - G x))) 2 μ) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hmetric (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundlim
      (fun _ => bot_le)
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have heq : g.inner x (V n x) (X x) - g.inner x (G x) (X x) =
        g.inner x (V n x - G x) (X x) := by rw [map_sub, sub_apply]
    rw [heq]
    calc
      |g.inner x (V n x - G x) (X x)| ≤
          Real.sqrt (g.inner x (V n x - G x) (V n x - G x)) *
            Real.sqrt (g.inner x (X x) (X x)) :=
        EquivalenceReverse.abs_g_inner_le_sqrt_mul_sqrt g x (V n x - G x) (X x)
      _ ≤ Real.sqrt (g.inner x (V n x - G x) (V n x - G x)) * C := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hC x (mem_univ x)
      _ = C * Real.sqrt (g.inner x (V n x - G x) (V n x - G x)) := mul_comm _ _
  have hpair1 := Integration.tendsto_eLpNorm_one_of_two
    (fun n => ((hweak n).1 X).sub (hpair X)) hpair2
  have hleft : Tendsto (fun n => ∫ x, g.inner x (V n x) (X x) ∂μ) atTop
      (𝓝 (∫ x, g.inner x (G x) (X x) ∂μ)) :=
    tendsto_integral_of_L1' _ (hpair X) (Eventually.of_forall fun n =>
      (TangentBundle.continuous_g_inner_of_smooth_sections g (V n) X).integrable_of_hasCompactSupport
        (isClosed_tsupport _).isCompact) hpair1
  have hdiv : MemLp (divergenceG g X) 2 μ :=
    (divergence_g_contMDiff g X).continuous.memLp_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have hright := (Integration.tendsto_integral_mul_of_eLpNorm_two hf hu hdiv hscalar).neg
  have heq : (fun n => ∫ x, g.inner x (V n x) (X x) ∂μ) =
      (fun n => -(∫ x, f n x * divergenceG g X x ∂μ)) :=
    funext fun n => (hweak n).pairing_eq X hX
  rw [← heq] at hright
  exact tendsto_nhds_unique hleft hright


theorem tendsto_integral_metric_energy_of_smooth_limit (g : SmoothRiemannianMetric I M)
    (V : ℕ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {G : ∀ x : M, TangentSpace I x}
    (hpoint : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      Tendsto (fun n => V n x) atTop (𝓝 (G x)))
    (hmetric : Tendsto (fun n => eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2
      (riemannianVolumeMeasure I M g)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, g.inner x (V n x) (V n x) ∂riemannianVolumeMeasure I M g)
      atTop (𝓝 (∫ x, g.inner x (G x) (G x) ∂riemannianVolumeMeasure I M g)) := by
  let μ := riemannianVolumeMeasure I M g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hV (n : ℕ) : MemLp (fun x => Real.sqrt (g.inner x (V n x) (V n x))) 2 μ :=
    (Real.continuous_sqrt.comp (TangentBundle.continuous_g_inner_of_smooth_sections g (V n) (V n))).memLp_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have hG := memLp_metric_norm_of_smooth_limit g V hpoint hmetric
  have hnorm := tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto g hmetric
  have hnonneg (x : M) (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  simpa only [Real.sq_sqrt (hnonneg _ _)] using
    Integration.tendsto_integral_sq_of_eLpNorm_two hV hG hnorm

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
