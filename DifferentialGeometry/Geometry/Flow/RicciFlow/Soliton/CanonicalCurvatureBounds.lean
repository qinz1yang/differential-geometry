import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

theorem canonicalMetric_riemannNormSq
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ℝ) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : ℝ} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    Tensor0SBundle.normSq0S
        (canonicalMetric g f sigma hcomplete hsol ht) x 4
        (metricRm04At (canonicalMetric g f sigma hcomplete hsol ht) x) =
      ((1 - sigma * t)⁻¹) ^ 2 * Tensor0SBundle.normSq0S g
        (canonicalFlowDiffeomorph g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x) 4
        (metricRm04At g (canonicalFlowDiffeomorph g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x)) := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Phi := canonicalFlowDiffeomorph g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  let gt := scaleMetric (I := I) (1 - sigma * t)
    (mem_canonicalTimeDomain_iff.mp ht) g
  have hpull : Tensor0SBundle.normSq0S (Diffeomorph.pullbackMetric gt Phi) x 4
      (metricRm04At (Diffeomorph.pullbackMetric gt Phi) x) =
        Tensor0SBundle.normSq0S gt (Phi x) 4 (metricRm04At gt (Phi x)) := by
    obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis
      (Diffeomorph.pullbackMetric gt Phi) x
    apply DifferentialGeometry.CheegerGromovCompactness.normSq0S_pullback_eval_of_orthonormal
      gt Phi x 4 basis hON
    intro slots
    simpa only [metricRm04_apply] using metricRm04_pullback_eval gt Phi x slots
  change Tensor0SBundle.normSq0S (Diffeomorph.pullbackMetric gt Phi) x 4
      (metricRm04At (Diffeomorph.pullbackMetric gt Phi) x) = _
  rw [hpull]
  change Tensor0SBundle.normSq0S
      (scaleMetric (I := I) (1 - sigma * t) (mem_canonicalTimeDomain_iff.mp ht) g)
      (Phi x) 4
      (metricRm04 (scaleMetric (I := I) (1 - sigma * t)
        (mem_canonicalTimeDomain_iff.mp ht) g) (Phi x)) = _
  rw [metricRm_scale, Tensor0SBundle.normSq0S_scale, Tensor0SBundle.normSq0S_smul]
  field_simp [(mem_canonicalTimeDomain_iff.mp ht).ne']
  rfl

theorem canonicalMetricFamily_riemannNormSq_le
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ℝ) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {c K : ℝ} (hc : 0 < 1 - sigma * c) (hK : 0 ≤ K)
    (hbound : ∀ x : M, Tensor0SBundle.normSq0S g x 4 (metricRm04At g x) ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 c) (x : M) :
    Tensor0SBundle.normSq0S
        (canonicalMetricFamily g f sigma hcomplete hsol t) x 4
        (metricRm04At (canonicalMetricFamily g f sigma hcomplete hsol t) x) ≤
      K / (min 1 (1 - sigma * c)) ^ 2 := by
  have hd : 0 < min 1 (1 - sigma * c) := lt_min (by norm_num) hc
  have hscale : min 1 (1 - sigma * c) ≤ 1 - sigma * t := by
    by_cases hsigma : 0 ≤ sigma
    · exact (min_le_right _ _).trans
        (sub_le_sub_left (mul_le_mul_of_nonneg_left ht.2 hsigma) 1)
    · have hst : sigma * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsigma) ht.1
      exact (min_le_left _ _).trans (by linarith)
  have htpos : 0 < 1 - sigma * t := hd.trans_le hscale
  have htdomain : t ∈ canonicalTimeDomain sigma :=
    mem_canonicalTimeDomain_iff.mpr htpos
  rw [canonicalMetricFamily_eq g f sigma hcomplete hsol htdomain,
    canonicalMetric_riemannNormSq]
  have hinv : (1 - sigma * t)⁻¹ ≤ (min 1 (1 - sigma * c))⁻¹ :=
    (inv_le_inv₀ htpos hd).mpr hscale
  have hsq : ((1 - sigma * t)⁻¹) ^ 2 ≤ ((min 1 (1 - sigma * c))⁻¹) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr htpos.le) hinv 2
  calc
    _ ≤ ((1 - sigma * t)⁻¹) ^ 2 * K :=
      mul_le_mul_of_nonneg_left (hbound _) (sq_nonneg _)
    _ ≤ ((min 1 (1 - sigma * c))⁻¹) ^ 2 * K := mul_le_mul_of_nonneg_right hsq hK
    _ = _ := by rw [inv_pow, div_eq_mul_inv, mul_comm]

theorem canonicalMetricFamily_curvature_bound_on_Icc
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ℝ) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {K c : ℝ} (hK : 0 ≤ K) (hscale : 0 < 1 - sigma * c)
    (hbound : ∀ x : M, Tensor0SBundle.normSq0S g x 4 (metricRm04At g x) ≤ K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc 0 c, ∀ x : M,
      Tensor0SBundle.normSq0S
          (canonicalMetricFamily g f sigma hcomplete hsol t) x 4
          (metricRm04At (canonicalMetricFamily g f sigma hcomplete hsol t) x) ≤ R := by
  refine ⟨K / (min 1 (1 - sigma * c)) ^ 2, div_nonneg hK (sq_nonneg _), ?_⟩
  intro t ht x
  exact canonicalMetricFamily_riemannNormSq_le g f sigma hcomplete hsol
    hscale hK hbound ht x

theorem canonicalSolutionOn_riemannNormSq_le
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ℝ) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (D : RealTimeInterval) {c K : ℝ} (hc : 0 < 1 - sigma * c) (hK : 0 ≤ K)
    (hbound : ∀ x : M, Tensor0SBundle.normSq0S g x 4 (metricRm04At g x) ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 c) (x : M) :
    Tensor0SBundle.normSq0S
        ((canonicalSolutionOn g f sigma hcomplete hsol D).base.metric t) x 4
        (metricRm04At
          ((canonicalSolutionOn g f sigma hcomplete hsol D).base.metric t) x) ≤
      K / (min 1 (1 - sigma * c)) ^ 2 :=
  canonicalMetricFamily_riemannNormSq_le g f sigma hcomplete hsol hc hK hbound ht x

end DifferentialGeometry.PDE.RicciFlow.Soliton
