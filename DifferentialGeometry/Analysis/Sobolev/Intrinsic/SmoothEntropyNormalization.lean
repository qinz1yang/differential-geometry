import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakEntropyApprox
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.WeakEmbedding
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


theorem integrable_metric_energy_of_memLp [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {G : ∀ x : M, TangentSpace I x}
    (hG : MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 2
      (riemannianVolumeMeasure I M g)) :
    Integrable (fun x => g.inner x (G x) (G x)) (riemannianVolumeMeasure I M g) := by
  exact hG.integrable_sq.congr (Eventually.of_forall fun x =>
    Real.sq_sqrt (metric_inner_self_nonneg g x (G x)))

private lemma sq_mul_log_sq_const_mul (c x : ℝ) :
    (c * x) ^ 2 * Real.log ((c * x) ^ 2) =
      c ^ 2 * (x ^ 2 * Real.log (x ^ 2)) + c ^ 2 * Real.log (c ^ 2) * x ^ 2 := by
  have h := Real.negMulLog_mul (c ^ 2) (x ^ 2)
  simp only [Real.negMulLog] at h
  rw [mul_pow]
  nlinarith only [h]

private lemma integral_wform_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u e R : α → ℝ} (he : Integrable e μ)
    (hR : Integrable (fun x => R x * u x ^ 2) μ)
    (hH : Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) μ) (tau : ℝ) :
    (∫ x, 4 * tau * e x + tau * R x * u x ^ 2 - u x ^ 2 * Real.log (u x ^ 2) ∂μ) =
      4 * tau * (∫ x, e x ∂μ) + tau * (∫ x, R x * u x ^ 2 ∂μ) -
        (∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂μ) := by
  simp_rw [mul_assoc tau]
  have hsum : Integrable (fun x => 4 * tau * e x + tau * (R x * u x ^ 2)) μ :=
    (he.const_mul (4 * tau)).add (hR.const_mul tau)
  rw [integral_sub hsum hH,
    integral_add (he.const_mul (4 * tau)) (hR.const_mul tau),
    integral_const_mul, integral_const_mul]

variable [CompactSpace M] [T2Space M] [I.Boundaryless]

private lemma integrable_smooth_wform (g : SmoothRiemannianMetric I M)
    {f R : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hR : Continuous R) (tau : ℝ) :
    Integrable (fun x => 4 * tau * g.inner x (gradFun g f x) (gradFun g f x) +
      tau * R x * f x ^ 2 - f x ^ 2 * Real.log (f x ^ 2)) (riemannianVolumeMeasure I M g) := by
  have he := integrable_metric_energy_of_memLp g
    (Equivalence.memLp_g_norm_gradFun_smooth g 2 hf)
  have hRs : Integrable (fun x => R x * f x ^ 2) (riemannianVolumeMeasure I M g) :=
    integrable_of_continuous_compactSpace g (hR.mul (hf.continuous.pow 2))
  have hH : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2))
      (riemannianVolumeMeasure I M g) :=
    integrable_of_continuous_compactSpace g (Real.continuous_mul_log.comp (hf.continuous.pow 2))
  have hInt : Integrable (fun x => 4 * tau * g.inner x (gradFun g f x) (gradFun g f x) +
      tau * (R x * f x ^ 2) - f x ^ 2 * Real.log (f x ^ 2)) (riemannianVolumeMeasure I M g) :=
    ((he.const_mul (4 * tau)).add (hRs.const_mul tau)).sub hH
  simpa only [mul_assoc tau] using hInt


theorem integral_wform_const_smul (g : SmoothRiemannianMetric I M)
    {f R : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hR : Continuous R) (tau c : ℝ) :
    (∫ x, 4 * tau * g.inner x (gradFun g (c • f) x) (gradFun g (c • f) x) +
      tau * R x * (c * f x) ^ 2 - (c * f x) ^ 2 * Real.log ((c * f x) ^ 2)
      ∂riemannianVolumeMeasure I M g) =
    c ^ 2 * (∫ x, 4 * tau * g.inner x (gradFun g f x) (gradFun g f x) +
      tau * R x * f x ^ 2 - f x ^ 2 * Real.log (f x ^ 2) ∂riemannianVolumeMeasure I M g) -
        c ^ 2 * Real.log (c ^ 2) * (∫ x, f x ^ 2 ∂riemannianVolumeMeasure I M g) := by
  let μ := riemannianVolumeMeasure I M g
  have hmass : Integrable (fun x => f x ^ 2) μ :=
    (MemW1pIntrinsicLp_of_contMDiff g 2 hf).1.integrable_sq
  calc
    _ = ∫ x, c ^ 2 * (4 * tau * g.inner x (gradFun g f x) (gradFun g f x) +
        tau * R x * f x ^ 2 - f x ^ 2 * Real.log (f x ^ 2)) -
          (c ^ 2 * Real.log (c ^ 2)) * f x ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Geometry.Connection.gradFun_const_smul g c (hf.mdifferentiableAt (by norm_num)),
        metric_inner_smul_self, sq_mul_log_sq_const_mul, mul_pow]
      ring
    _ = _ := by
      rw [integral_sub ((integrable_smooth_wform g hf hR tau).const_mul (c ^ 2))
          (hmass.const_mul (c ^ 2 * Real.log (c ^ 2))),
        integral_const_mul, integral_const_mul]


theorem HasWeakRiemannianGradLp.exists_smooth_normalized_wform_le
    {g : SmoothRiemannianMetric I M} (hdim : 2 ≤ Module.finrank ℝ E)
    {u : M → ℝ} {G : ∀ x : M, TangentSpace I x}
    (hG : HasWeakRiemannianGradLp g u G)
    (hu : MemLp u 2 (riemannianVolumeMeasure I M g))
    (hGn : MemLp (fun x => Real.sqrt (g.inner x (G x) (G x))) 2
      (riemannianVolumeMeasure I M g))
    (hmass : (∫ x, u x ^ 2 ∂riemannianVolumeMeasure I M g) = 1)
    {R : M → ℝ} (hR : Continuous R) (tau : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v ∧
      (∫ x, v x ^ 2 ∂riemannianVolumeMeasure I M g) = 1 ∧
      (∫ x, 4 * tau * g.inner x (gradFun g v x) (gradFun g v x) +
        tau * R x * v x ^ 2 - v x ^ 2 * Real.log (v x ^ 2)
        ∂riemannianVolumeMeasure I M g) ≤
      (∫ x, 4 * tau * g.inner x (G x) (G x) +
        tau * R x * u x ^ 2 - u x ^ 2 * Real.log (u x ^ 2)
        ∂riemannianVolumeMeasure I M g) + ε := by
  let μ := riemannianVolumeMeasure I M g
  obtain ⟨f, hf, hmasslim, henergy, hweighted, hentropy⟩ :=
    hG.exists_smooth_entropy_integrals_approx hdim hu hGn hR
  let m : ℕ → ℝ := fun n => ∫ x, f n x ^ 2 ∂μ
  have hm : Tendsto m atTop (𝓝 1) := by simpa only [hmass] using hmasslim
  let c : ℕ → ℝ := fun n => (Real.sqrt (m n))⁻¹
  have hc : Tendsto c atTop (𝓝 1) := by
    simpa only [c, Function.comp_apply, Real.sqrt_one, inv_one] using ((Real.continuous_sqrt.tendsto 1).comp hm).inv₀
      (by norm_num : Real.sqrt (1 : ℝ) ≠ 0)
  let v : ℕ → M → ℝ := fun n => c n • f n
  have hv (n : ℕ) : ContMDiff I 𝓘(ℝ) ∞ (v n) := contMDiff_const.mul (hf n)
  let W : ℝ := ∫ x, 4 * tau * g.inner x (G x) (G x) +
    tau * R x * u x ^ 2 - u x ^ 2 * Real.log (u x ^ 2) ∂μ
  let F : ℕ → ℝ := fun n => ∫ x, 4 * tau * g.inner x (gradFun g (f n) x) (gradFun g (f n) x) +
    tau * R x * f n x ^ 2 - f n x ^ 2 * Real.log (f n x ^ 2) ∂μ
  have hRtop : MemLp R ⊤ μ := hR.memLp_top_of_hasCompactSupport (isClosed_tsupport _).isCompact μ
  have hRu : Integrable (fun x => R x * u x ^ 2) μ := by
    have hRu₂ : MemLp (fun x => R x * u x) 2 μ := hu.mul' hRtop
    convert hRu₂.integrable_mul hu using 1
    funext x
    simp only [Pi.mul_apply, pow_two, mul_assoc]
  have hHu := (show MemW1pIntrinsicLp g 2 u from ⟨hu, G, hG, hGn⟩).integrable_sq_mul_log_sq hdim
  have hW : W = 4 * tau * (∫ x, g.inner x (G x) (G x) ∂μ) +
      tau * (∫ x, R x * u x ^ 2 ∂μ) - (∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂μ) :=
    integral_wform_eq (integrable_metric_energy_of_memLp g hGn) hRu hHu tau
  have hF (n : ℕ) : F n =
      4 * tau * (∫ x, g.inner x (gradFun g (f n) x) (gradFun g (f n) x) ∂μ) +
        tau * (∫ x, R x * f n x ^ 2 ∂μ) - (∫ x, f n x ^ 2 * Real.log (f n x ^ 2) ∂μ) :=
    integral_wform_eq (integrable_metric_energy_of_memLp g
      (Equivalence.memLp_g_norm_gradFun_smooth g 2 (hf n)))
      (integrable_of_continuous_compactSpace g (hR.mul ((hf n).continuous.pow 2)))
      (integrable_of_continuous_compactSpace g
        (Real.continuous_mul_log.comp ((hf n).continuous.pow 2))) tau
  have hFlim : Tendsto F atTop (𝓝 W) := by
    rw [hW]
    exact (((henergy.const_mul (4 * tau)).add (hweighted.const_mul tau)).sub hentropy).congr'
      (Eventually.of_forall fun n => (hF n).symm)
  have hclog : Tendsto (fun n => c n ^ 2 * Real.log (c n ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_pow, Real.log_one, mul_zero] using
      Real.continuous_mul_log.continuousAt.tendsto.comp (hc.pow 2)
  have hlim : Tendsto (fun n => c n ^ 2 * F n - (c n ^ 2 * Real.log (c n ^ 2)) * m n)
      atTop (𝓝 W) := by
    simpa only [one_pow, one_mul, zero_mul, sub_zero] using
      ((hc.pow 2).mul hFlim).sub (hclog.mul hm)
  obtain ⟨n, hn, hnW⟩ := ((hm.eventually (Ioi_mem_nhds zero_lt_one)).and
    (hlim.eventually (Iio_mem_nhds (show W < W + ε by linarith)))).exists
  have hnormalized : (∫ x, v n x ^ 2 ∂μ) = 1 := by
    have hc2 : c n ^ 2 = (m n)⁻¹ := by
      dsimp only [c]
      rw [inv_pow, Real.sq_sqrt hn.le]
    calc
      _ = c n ^ 2 * (∫ x, f n x ^ 2 ∂μ) := by
        simp only [v, Pi.smul_apply, smul_eq_mul, mul_pow, integral_const_mul]
      _ = 1 := by rw [hc2]; exact inv_mul_cancel₀ hn.ne'
  refine ⟨v n, hv n, hnormalized, ?_⟩
  change (∫ x, 4 * tau * g.inner x (gradFun g (c n • f n) x) (gradFun g (c n • f n) x) +
    tau * R x * (c n * f n x) ^ 2 - (c n * f n x) ^ 2 * Real.log ((c n * f n x) ^ 2) ∂μ) ≤ W + ε
  rw [integral_wform_const_smul g (hf n) hR tau (c n)]
  exact hnW.le

end DifferentialGeometry.Analysis.Sobolev.IntrinsicLp
