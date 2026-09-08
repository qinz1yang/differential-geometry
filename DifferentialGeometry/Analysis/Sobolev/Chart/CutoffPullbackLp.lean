import DifferentialGeometry.Analysis.Sobolev.Chart.ChartPullbackLp
import Mathlib.Analysis.Normed.Operator.Basic

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ENNReal ContDiff Manifold

namespace DifferentialGeometry.Analysis.Sobolev.Chart

open DifferentialGeometry.Integral.Measure

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ E)) → ℝ)

omit [FiniteDimensional ℝ E] in
private theorem cutoff_ae_eq_of_restrict
    {Ω : Set EuStd} (hΩ : MeasurableSet Ω) {η f g : EuStd → ℝ}
    (hηs : tsupport η ⊆ Ω) (hfg : f =ᵐ[volume.restrict Ω] g) :
    (fun z => η z * f z) =ᵐ[volume] fun z => η z * g z := by
  have hae := (ae_restrict_iff' hΩ).mp hfg
  filter_upwards [hae] with z hz
  by_cases hzs : z ∈ tsupport η
  · rw [hz (hηs hzs)]
  · rw [image_eq_zero_of_notMem_tsupport hzs, zero_mul, zero_mul]

theorem exists_continuousLinearMap_chartPullback_mul
    (q : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuStd}
    (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ chartTargetEuclid (I := I) α)
    {η : EuStd → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) :
    ∃ L : Lp ℝ 2 (volume.restrict Ω) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) q),
      ∀ f, (L f : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I) (M := M) q]
        chartPullback I α (fun z => η z * f z) := by
  obtain ⟨C, hC⟩ := hηc.exists_bound_of_continuous hη
  obtain ⟨D, hD, hbound⟩ := exists_eLpNorm_chartPullback_le q α hΩc hΩs
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num)
  have hηf (f : Lp ℝ 2 (volume.restrict Ω)) : MemLp (fun z => η z * f z) 2 volume := by
    refine ⟨(hη.measurable.mul (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable, ?_⟩
    rw [← eLpNorm_restrict_eq_of_support_subset
      ((subset_tsupport _).trans ((tsupport_mul_subset_left (f := η) (g := f)).trans hηs))]
    exact ((Lp.memLp f).of_le_mul (c := C)
      (hη.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right (hC z) (norm_nonneg (f z)))).2
  have hpb (f : Lp ℝ 2 (volume.restrict Ω)) :
      MemLp (chartPullback I α (fun z => η z * f z)) 2
        (riemannianVolumeMeasure (I := I) (M := M) q) := by
    refine ⟨(measurable_chartPullback α
      (hη.measurable.mul (Lp.stronglyMeasurable f).measurable)).aestronglyMeasurable, ?_⟩
    exact (hbound _ (hη.measurable.mul (Lp.stronglyMeasurable f).measurable)
      ((tsupport_mul_subset_left (f := η) (g := f)).trans (hηs.trans subset_closure))).trans_lt
      (ENNReal.mul_lt_top (by simp) (hηf f).2)
  let F : Lp ℝ 2 (volume.restrict Ω) →
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) q) :=
    fun f => (hpb f).toLp _
  have hF (f : Lp ℝ 2 (volume.restrict Ω)) : (F f : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) q]
      chartPullback I α (fun z => η z * f z) := (hpb f).coeFn_toLp
  let L : Lp ℝ 2 (volume.restrict Ω) →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) q) :=
    { toFun := F
      map_add' := by
        intro f g
        apply Lp.ext
        have hadd := chartPullback_ae_eq_of_ae_eq q α
          (cutoff_ae_eq_of_restrict hΩ hηs (Lp.coeFn_add f g))
        filter_upwards [hF (f+g), hF f, hF g, Lp.coeFn_add (F f) (F g), hadd]
          with x hfg hf hg hcoe hsum
        rw [hfg, hcoe, Pi.add_apply, hf, hg, hsum]
        simp only [Pi.add_apply]
        rw [show (fun z => η z * (f z + g z)) =
          (fun z => η z * f z + η z * g z) by funext z; ring, chartPullback_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        have hsmul := chartPullback_ae_eq_of_ae_eq q α
          (cutoff_ae_eq_of_restrict hΩ hηs (Lp.coeFn_smul c f))
        filter_upwards [hF (c • f), hF f, Lp.coeFn_smul c (F f), hsmul]
          with x hcf hf hcoe hmul
        change (F (c • f) : M → ℝ) x = (c • F f : Lp ℝ 2 _) x
        rw [hcf, hcoe, Pi.smul_apply, hf, hmul]
        change chartPullback I α (fun z => η z * (c * f z)) x =
          c * chartPullback I α (fun z => η z * f z) x
        rw [show (fun z => η z * (c * f z)) =
          (fun z => c * (η z * f z)) by funext z; ring, chartPullback_const_smul] }
  have hn (f : Lp ℝ 2 (volume.restrict Ω)) : ‖L f‖ ≤ D * max C 0 * ‖f‖ := by
    have hb := hbound _ (hη.measurable.mul (Lp.stronglyMeasurable f).measurable)
      ((tsupport_mul_subset_left (f := η) (g := f)).trans (hηs.trans subset_closure))
    have hcut : eLpNorm (fun z => η z * f z) 2 volume ≤
        ENNReal.ofReal (max C 0) * eLpNorm f 2 (volume.restrict Ω) := by
      rw [← eLpNorm_restrict_eq_of_support_subset
        ((subset_tsupport _).trans ((tsupport_mul_subset_left (f := η) (g := f)).trans hηs))]
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul _ 2
      filter_upwards [] with z
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hC z).trans (le_max_left _ _)) (norm_nonneg _)
    have hb' := hb.trans (mul_le_mul' le_rfl hcut)
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by simp) (Lp.memLp f).2.ne)) hb'
    change ‖(hpb f).toLp _‖ ≤ _
    rw [Lp.norm_toLp]
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.le,
      ENNReal.toReal_ofReal (le_max_right C 0), Lp.norm_def, mul_assoc, Pi.mul_def] using hreal
  exact ⟨L.mkContinuous (D * max C 0) hn, hF⟩

end DifferentialGeometry.Analysis.Sobolev.Chart
