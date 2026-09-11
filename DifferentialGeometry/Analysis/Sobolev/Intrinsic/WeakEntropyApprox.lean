import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakSmoothDensity
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.SmoothSobolevBound
import DifferentialGeometry.Analysis.Integration.EntropyUniform
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [T2Space M] [I.Boundaryless]


theorem HasWeakRiemannianGradLp.exists_smooth_entropy_integrals_approx
    {g : SmoothRiemannianMetric I M} (hdim : 2 ≤ Module.finrank ℝ E)
    {u : M → ℝ} {G : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G)
    (hu : MemLp u 2 (riemannianVolumeMeasure I M g))
    (hGn : MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 2
      (riemannianVolumeMeasure I M g))
    {R : M → ℝ} (hR : Continuous R) :
    ∃ f : ℕ → M → ℝ, (∀ n, ContMDiff I 𝓘(ℝ) ∞ (f n)) ∧
      Tendsto (fun n => ∫ x, f n x ^ 2 ∂riemannianVolumeMeasure I M g) atTop
        (𝓝 (∫ x, u x ^ 2 ∂riemannianVolumeMeasure I M g)) ∧
      Tendsto (fun n => ∫ x, g.inner x (gradFun g (f n) x) (gradFun g (f n) x)
        ∂riemannianVolumeMeasure I M g) atTop
        (𝓝 (∫ x, g.inner x (G x) (G x) ∂riemannianVolumeMeasure I M g)) ∧
      Tendsto (fun n => ∫ x, R x * f n x ^ 2 ∂riemannianVolumeMeasure I M g) atTop
        (𝓝 (∫ x, R x * u x ^ 2 ∂riemannianVolumeMeasure I M g)) ∧
      Tendsto (fun n => ∫ x, f n x ^ 2 * Real.log (f n x ^ 2)
        ∂riemannianVolumeMeasure I M g) atTop
        (𝓝 (∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂riemannianVolumeMeasure I M g)) := by
  let μ := riemannianVolumeMeasure I M g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  obtain ⟨f, hf, hscalar, hpointG, hmetric⟩ := hG.exists_smooth_metricL2_approx hu hGn
  have hfn (n : ℕ) : MemLp (f n) 2 μ := (MemW1pIntrinsicLp_of_contMDiff g 2 (hf n)).1
  have hgrad (n : ℕ) : MemLp (fun x => Real.sqrt
      (g.inner x (gradFun g (f n) x) (gradFun g (f n) x))) 2 μ :=
    Equivalence.memLp_g_norm_gradFun_smooth g 2 (hf n)
  obtain ⟨Cv, hCv, hvbound⟩ := Integration.exists_eLpNorm_bound_of_tendsto_two hfn hu hscalar
  have hnorm := tendsto_eLpNorm_metric_norm_sub_of_metricL2_tendsto g hmetric
  obtain ⟨Cg, hCg, hgbound⟩ := Integration.exists_eLpNorm_bound_of_tendsto_two hgrad hGn hnorm
  obtain ⟨q, hq, C, hC, hSobolev⟩ := exists_eLpNorm_gt_two_bound_smooth g hdim
  let B : ℝ≥0∞ := C * (Cv + Cg)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top hC (ENNReal.add_ne_top.mpr ⟨hCv, hCg⟩)
  have hqbound (n : ℕ) : eLpNorm (f n) (ENNReal.ofReal q) μ ≤ B :=
    (hSobolev (hf n)).trans (mul_le_mul_right (add_le_add (hvbound n) (hgbound n)) C)
  have hInMeasure := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun n => (hf n).continuous.aestronglyMeasurable) hu.aestronglyMeasurable hscalar
  obtain ⟨s, hs, hpoint⟩ := hInMeasure.exists_seq_tendsto_ae
  have huq : MemLp u (ENNReal.ofReal q) μ := by
    refine ⟨hu.aestronglyMeasurable, ?_⟩
    exact (Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall fun n => hqbound (s n))
      (fun n => (hf (s n)).continuous.aestronglyMeasurable) hpoint).trans_lt hB.lt_top
  have hentropy := Integration.tendsto_integral_sq_mul_log_sq_of_eLpNorm_bdd hq
    (fun n => (hf (s n)).continuous.aestronglyMeasurable) huq hB
    (fun n => hqbound (s n)) hpoint
  have hmass := Integration.tendsto_integral_sq_of_eLpNorm_two hfn hu hscalar
  have hRtop : MemLp R ⊤ μ := hR.memLp_top_of_hasCompactSupport (isClosed_tsupport _).isCompact μ
  have hweighted := Integration.tendsto_integral_weighted_sq_of_eLpNorm_two hfn hu hRtop hscalar
  let V (n : ℕ) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG g ⟨f n, hf n⟩
  have hV (n : ℕ) (x : M) : V n x = gradFun g (f n) x := grad_g_apply g ⟨f n, hf n⟩ x
  have hpointV : ∀ᵐ x ∂μ, Tendsto (fun n => V n x) atTop (𝓝 (G x)) := by
    simpa only [hV] using hpointG
  have hmetricV : Tendsto (fun n => eLpNorm (fun x => Real.sqrt
      (g.inner x (V n x - G x) (V n x - G x))) 2 μ) atTop (𝓝 0) := by
    simpa only [hV] using hmetric
  have henergy : Tendsto (fun n => ∫ x, g.inner x (gradFun g (f n) x) (gradFun g (f n) x) ∂μ)
      atTop (𝓝 (∫ x, g.inner x (G x) (G x) ∂μ)) := by
    simpa only [hV] using tendsto_integral_metric_energy_of_smooth_limit g V hpointV hmetricV
  exact ⟨fun n => f (s n), fun n => hf (s n), hmass.comp hs.tendsto_atTop,
    henergy.comp hs.tendsto_atTop, hweighted.comp hs.tendsto_atTop, hentropy⟩

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
