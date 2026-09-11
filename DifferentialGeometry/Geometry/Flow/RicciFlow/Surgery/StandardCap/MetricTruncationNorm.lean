import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.MetricTruncation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndTranslations
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Metric.InterpolationNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance (U : Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

private def fixedAnnulus : Opens E3 :=
  ⟨{x | transitionEnd + 1 < ‖x‖ ∧ ‖x‖ < transitionEnd + 4},
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)⟩

private def fixedBand : Set fixedAnnulus :=
  {q | transitionEnd + 2 ≤ ‖(q : E3)‖ ∧ ‖(q : E3)‖ ≤ transitionEnd + 3}

private theorem fixedBand_compact : IsCompact fixedBand := by
  rw [Subtype.isCompact_iff]
  have himage : Subtype.val '' fixedBand =
      {x : E3 | transitionEnd + 2 ≤ ‖x‖ ∧ ‖x‖ ≤ transitionEnd + 3} := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hx
      have hu : x ∈ fixedAnnulus := by
        change transitionEnd + 1 < ‖x‖ ∧ ‖x‖ < transitionEnd + 4
        constructor <;> linarith [hx.1, hx.2]
      exact ⟨⟨x, hu⟩, hx, rfl⟩
  rw [himage]
  exact (isCompact_closedBall (0 : E3) (transitionEnd + 3)).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2)

private def fixedReference : SmoothRiemannianMetric (𝓡 3) fixedAnnulus :=
  metric.restrictOpen fixedAnnulus

private def fixedCutoff (q : fixedAnnulus) : ℝ := truncationCutoff (transitionEnd + 4) q.val

private theorem fixedCutoff_smooth : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ fixedCutoff :=
  (truncationCutoff_contMDiff (transitionEnd + 4) (by linarith [transitionEnd_pos])).comp
    (contMDiff_subtype_val (U := fixedAnnulus))

private theorem fixedCutoff_mem (q : fixedAnnulus) : fixedCutoff q ∈ Icc (0 : ℝ) 1 :=
  truncationCutoff_mem _ _

private def translatedShift (R : ℝ) : ℝ := R - transitionEnd - 4

private theorem shift_nonneg (R : ℝ) (hR : transitionEnd + 4 ≤ R) :
    0 ≤ translatedShift R := by unfold translatedShift; linarith

private theorem annulus_in_end (R : ℝ) (hR : transitionEnd + 4 ≤ R) :
    (fixedAnnulus : Set E3) ⊆ endTranslationDomain (translatedShift R) := by
  intro x hx
  change transitionEnd < ‖x‖ ∧ transitionEnd < ‖x‖ + translatedShift R
  have hl : transitionEnd + 1 < ‖x‖ := hx.1
  constructor <;> linarith [shift_nonneg R hR]

private theorem annulus_in_source (R : ℝ) (hR : transitionEnd + 4 ≤ R) :
    (fixedAnnulus : Set E3) ⊆ (radialTranslationDiffeomorph (translatedShift R)).source :=
  (annulus_in_end R hR).trans (endTranslationDomain_subset_source _)

private def translatedAnnulus (R : ℝ) (hR : transitionEnd + 4 ≤ R) : Opens E3 :=
  ⟨(radialTranslationDiffeomorph (translatedShift R) : E3 → E3) '' (fixedAnnulus : Set E3),
    DifferentialGeometry.image_opens_isOpen _ (annulus_in_source R hR)⟩

private def annulusTranslation (R : ℝ) (hR : transitionEnd + 4 ≤ R) :
    fixedAnnulus ≃ₘ⟮𝓡 3, 𝓡 3⟯ translatedAnnulus R hR :=
  PartialDiffeomorph.toOpensDiffeo
    (radialTranslationDiffeomorph (translatedShift R)) (annulus_in_source R hR)

private theorem translation_norm (R : ℝ) (hR : transitionEnd + 4 ≤ R) (q : fixedAnnulus) :
    ‖(annulusTranslation R hR q : E3)‖ = ‖(q : E3)‖ + translatedShift R :=
  endTranslationDiffeomorph_norm _ _ (annulus_in_end R hR q.property)

private theorem translation_mfderiv (R : ℝ) (hR : transitionEnd + 4 ≤ R)
    (q : fixedAnnulus) (v : TangentSpace (𝓡 3) q) :
    mfderiv (𝓡 3) (𝓡 3) (annulusTranslation R hR) q v =
      mfderiv (𝓡 3) (𝓡 3) (radialTranslationDiffeomorph (translatedShift R)) (q : E3) v :=
  PartialDiffeomorph.mfderiv_toOpensDiffeo _ (annulus_in_source R hR) q v

private theorem pullback_reference (R : ℝ) (hR : transitionEnd + 4 ≤ R) :
    Diffeomorph.pullbackMetric (metric.restrictOpen (translatedAnnulus R hR))
      (annulusTranslation R hR) = fixedReference := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
    fixedReference, SmoothRiemannianMetric.restrictOpen_inner,
    translation_mfderiv, translation_mfderiv]
  exact (endTranslationDiffeomorph_metric_inner _ _ (annulus_in_end R hR q.property) v w).symm

private theorem translation_cutoff (R : ℝ) (hR : transitionEnd + 4 ≤ R) (q : fixedAnnulus) :
    truncationCutoff R (annulusTranslation R hR q : E3) = fixedCutoff q := by
  unfold fixedCutoff truncationCutoff
  rw [translation_norm]
  have he : (‖(q : E3)‖ + translatedShift R) - (R - 2) =
      ‖(q : E3)‖ - (transitionEnd + 4 - 2) := by unfold translatedShift; ring
  rw [he]

private def transportedMetric (g : SmoothRiemannianMetric (𝓡 3) E3)
    (R : ℝ) (hR : transitionEnd + 4 ≤ R) : SmoothRiemannianMetric (𝓡 3) fixedAnnulus :=
  Diffeomorph.pullbackMetric (g.restrictOpen (translatedAnnulus R hR)) (annulusTranslation R hR)

private theorem transported_norm (g : SmoothRiemannianMetric (𝓡 3) E3)
    (R : ℝ) (hR : transitionEnd + 4 ≤ R) (j : ℕ) (q : fixedAnnulus) :
    metricDerivNorm j (transportedMetric g R hR) fixedReference fixedReference q =
      metricDerivNorm j g metric metric (annulusTranslation R hR q : E3) := by
  have hp := metricDerivNorm_pullback (g.restrictOpen (translatedAnnulus R hR))
    (metric.restrictOpen (translatedAnnulus R hR)) (metric.restrictOpen (translatedAnnulus R hR))
    (annulusTranslation R hR) j q
  rw [pullback_reference] at hp
  exact hp.trans (metricDerivNorm_restrictOpen g metric metric _ j _)

private theorem transported_truncation (g : SmoothRiemannianMetric (𝓡 3) E3)
    (R : ℝ) (hR : 2 < R) (hlarge : transitionEnd + 4 ≤ R) :
    transportedMetric (metricTruncation g R hR) R hlarge =
      (transportedMetric g R hlarge).convexComb fixedReference fixedCutoff
        fixedCutoff_smooth fixedCutoff_mem := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  have hcap := congrArg
    (fun h : SmoothRiemannianMetric (𝓡 3) fixedAnnulus => h.inner q v w)
    (pullback_reference R hlarge)
  simp only [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner] at hcap
  simp only [transportedMetric, Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner, convexComb_inner, smul_eq_mul]
  have ht := metricTruncation_inner g R hR (annulusTranslation R hlarge q : E3)
    (mfderiv (𝓡 3) (𝓡 3) (annulusTranslation R hlarge) q v)
    (mfderiv (𝓡 3) (𝓡 3) (annulusTranslation R hlarge) q w)
  rw [translation_cutoff] at ht
  exact ht.trans (congrArg (fun z : ℝ => fixedCutoff q *
    g.inner (annulusTranslation R hlarge q : E3)
      (mfderiv (𝓡 3) (𝓡 3) (annulusTranslation R hlarge) q v)
      (mfderiv (𝓡 3) (𝓡 3) (annulusTranslation R hlarge) q w) +
      (1 - fixedCutoff q) * z) hcap)

private theorem band_preimage (R : ℝ) (hR : transitionEnd + 4 ≤ R) (x : E3)
    (hx : R - 2 ≤ ‖x‖ ∧ ‖x‖ ≤ R - 1) :
    ∃ q ∈ fixedBand, (annulusTranslation R hR q : E3) = x := by
  let s := translatedShift R
  have hxsrc : max 0 (-(-s)) < ‖x‖ := by
    rw [neg_neg]
    apply max_lt
    · linarith [transitionEnd_pos, hx.1]
    · dsimp [s, translatedShift]
      linarith [transitionEnd_pos, hx.1]
  let y := radialTranslation (-s) x
  have hn : ‖y‖ = ‖x‖ - s := by
    simpa only [sub_eq_add_neg] using norm_radialTranslation (-s) hxsrc
  have hyband : transitionEnd + 2 ≤ ‖y‖ ∧ ‖y‖ ≤ transitionEnd + 3 := by
    rw [hn]
    dsimp [s, translatedShift]
    constructor <;> linarith [hx.1, hx.2]
  have hy : y ∈ fixedAnnulus := by
    change transitionEnd + 1 < ‖y‖ ∧ ‖y‖ < transitionEnd + 4
    constructor <;> linarith [hyband.1, hyband.2]
  refine ⟨⟨y, hy⟩, hyband, ?_⟩
  change radialTranslation s (radialTranslation (-s) x) = x
  simpa only [neg_neg] using radialTranslation_neg_cancel (-s) hxsrc

private theorem fixed_interpolation_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : SmoothRiemannianMetric (𝓡 3) fixedAnnulus)
      (B : ℝ), 0 ≤ B →
      (∀ j ≤ k, ∀ q ∈ fixedBand, metricDerivNorm j g fixedReference fixedReference q ≤ B) →
      ∀ j ≤ k, ∀ q ∈ fixedBand,
        metricDerivNorm j
          (g.convexComb fixedReference fixedCutoff fixedCutoff_smooth fixedCutoff_mem)
          fixedReference fixedReference q ≤ C * B := by
  obtain ⟨C, hC, hbound⟩ := exists_metricDerivENormSupOn_conformal_convexComb_bound
    fixedReference fixedReference (fun _ => 0) contMDiff_const fixedCutoff
    fixedCutoff_smooth fixedCutoff_mem fixedBand_compact k
  refine ⟨C, hC, ?_⟩
  intro g B hB hg j hj q hq
  have hscale : scaleMetric 1 zero_lt_one fixedReference = fixedReference := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    simp only [scaleMetric_inner, one_mul]
  have hb := hbound g 1 zero_lt_one
  rw [hscale, conformalMetricOfContDiff_zero, conformalMetricOfContDiff_zero, sub_self, abs_zero,
    ENNReal.ofReal_zero, add_zero] at hb
  have hsup : metricDerivENormSupOn fixedBand k g fixedReference fixedReference ≤ ENNReal.ofReal B :=
    (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
      (fun j hj q hq => ENNReal.ofReal_le_ofReal (hg j hj q hq))
  have hp := (ofReal_metricDerivNorm_le_sup fixedBand k
    (g.convexComb fixedReference fixedCutoff fixedCutoff_smooth fixedCutoff_mem)
    fixedReference fixedReference hj hq).trans (hb.trans (mul_le_mul' le_rfl hsup))
  rw [← ENNReal.ofReal_mul hC.le] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le hB)).mp hp

private theorem norm_eq_on_open (g h ref : SmoothRiemannianMetric (𝓡 3) E3)
    (U : Opens E3)
    (he : ∀ (y : E3), y ∈ U → ∀ (v w : TangentSpace (𝓡 3) y), g.inner y v w = h.inner y v w)
    (j : ℕ) (x : U) :
    metricDerivNorm j g ref ref (x : E3) = metricDerivNorm j h ref ref (x : E3) := by
  have hh : g.restrictOpen U = h.restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact he y y.property v w
  have hp := metricDerivNorm_restrictOpen g ref ref U j x
  rw [hh] at hp
  exact hp.symm.trans (metricDerivNorm_restrictOpen h ref ref U j x)

theorem exists_uniform_metricTruncation_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : SmoothRiemannianMetric (𝓡 3) E3)
      (R : ℝ) (hR : 2 < R), transitionEnd + 4 ≤ R →
      ∀ B : ℝ, 0 ≤ B →
      (∀ j ≤ k, ∀ x : E3, metricDerivNorm j g metric metric x ≤ B) →
      ∀ j ≤ k, ∀ x : E3,
        metricDerivNorm j (metricTruncation g R hR) metric metric x ≤ C * B := by
  obtain ⟨C, hC, hb⟩ := fixed_interpolation_bound k
  refine ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro g R hR hlarge B hB hg j hj x
  by_cases hcore : ‖x‖ < R - 2
  · let U : Opens E3 := ⟨{y | ‖y‖ < R - 2}, isOpen_lt continuous_norm continuous_const⟩
    have he := norm_eq_on_open (metricTruncation g R hR) g metric U
      (fun y hy v w => metricTruncation_inner_core g R hR hy.le v w) j ⟨x, hcore⟩
    exact he.le.trans ((hg j hj x).trans (le_mul_of_one_le_left hB (le_max_left _ _)))
  · by_cases hend : R - 1 < ‖x‖
    · let U : Opens E3 := ⟨{y | R - 1 < ‖y‖}, isOpen_lt continuous_const continuous_norm⟩
      have he := norm_eq_on_open (metricTruncation g R hR) metric metric U
        (fun y hy v w => metricTruncation_inner_end g R hR hy.le v w) j ⟨x, hend⟩
      rw [metricDerivNorm_self] at he
      exact he.le.trans (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hB)
    · obtain ⟨q, hq, hqx⟩ := band_preimage R hlarge x ⟨not_lt.mp hcore, not_lt.mp hend⟩
      have hh := hb (transportedMetric g R hlarge) B hB
        (fun i hi p _ => (transported_norm g R hlarge i p).le.trans (hg i hi _)) j hj q hq
      rw [← transported_truncation g R hR hlarge, transported_norm, hqx] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)

end DifferentialGeometry.PDE.RicciFlow.StandardCap
