import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.ChartPullbackSmooth


noncomputable section

open MeasureTheory Set Manifold
open scoped ENNReal ContDiff Manifold

namespace DifferentialGeometry.Analysis.Sobolev.Chart

open DifferentialGeometry.Integral.Measure

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel _
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ E)) → ℝ)

theorem measurable_chartPullback (α : M) {f : EuStd → ℝ} (hf : Measurable f) :
    Measurable (chartPullback I α f) := by
  classical
  let s := (chartAt H α).source
  let coord := s.piecewise (fun x => toEuclidean (E := E) (extChartAt I α x)) (fun _ => 0)
  have hs : MeasurableSet s := (chartAt H α).open_source.measurableSet
  have hc : ContinuousOn (fun x : M => toEuclidean (E := E) (extChartAt I α x)) s := by
    apply (toEuclidean (E := E)).continuous.comp_continuousOn
    simpa only [s, extChartAt_source] using continuousOn_extChartAt (I := I) α
  have hm : Measurable coord := hc.measurable_piecewise continuousOn_const hs
  have heq : chartPullback I α f = s.indicator (f ∘ coord) := by
    funext x
    by_cases hx : x ∈ s
    · simp [chartPullback, s, coord, hx]
    · simp [chartPullback, s, coord, hx]
  rw [heq]
  exact (hf.comp hm).indicator hs

theorem chartPushedRaw_chartPullback (α : M) {f : EuStd → ℝ}
    (hfs : tsupport f ⊆ chartTargetEuclid (I := I) α) :
    chartPushedRaw I α (chartPullback I α f) = f := by
  funext z
  by_cases hz : z ∈ chartTargetEuclid (I := I) α
  · rw [chartPushedRaw_apply_of_mem α _ hz]
    have hy : (toEuclidean (E := E)).symm z ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M) α] at hz
      exact hz
    have hx := (extChartAt I α).map_target hy
    rw [extChartAt_source] at hx
    rw [chartPullback_apply_of_mem α f hx, (extChartAt I α).right_inv hy]
    exact congrArg f ((toEuclidean (E := E)).apply_symm_apply z)
  · rw [chartPushedRaw_apply_of_notMem α _ hz]
    exact (image_eq_zero_of_notMem_tsupport fun hs => hz (hfs hs)).symm

theorem exists_eLpNorm_chartPullback_le
    [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    (q : SmoothRiemannianMetric I M) (α : M) {K : Set EuStd}
    (hK : IsCompact K) (hKs : K ⊆ chartTargetEuclid (I := I) α)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : EuStd → ℝ), Measurable f → tsupport f ⊆ K →
      eLpNorm (chartPullback I α f) p (riemannianVolumeMeasure (I := I) (M := M) q) ≤
        ENNReal.ofReal C * eLpNorm f p volume := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKe
  · refine ⟨1, zero_lt_one, ?_⟩
    intro f _ hfs
    have hf : f = 0 := by
      funext z
      exact image_eq_zero_of_notMem_tsupport fun hz => by simpa [hKe] using hfs hz
    rw [hf, show (0 : EuStd → ℝ) = (fun _ => 0) from rfl, chartPullback_zero_fun]
    simp
  let e := toEuclidean (E := E)
  let L := e.symm '' K
  have hL : IsCompact L := hK.image e.symm.continuous
  have hLs : L ⊆ (extChartAt I α).target := by
    rintro _ ⟨z, hz, rfl⟩
    have h := hKs hz
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M) α] at h
    exact h
  obtain ⟨C, hC, hbound⟩ := eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform
    q α hL (hKe.image e.symm) hLs hp hpt
  refine ⟨C, hC, ?_⟩
  intro f hfm hfK
  have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport _) hfK
  have hfs := hfK.trans hKs
  have hs : tsupport (chartPullback I α f) ⊆ (chartAt H α).source := by
    intro x hx
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := tsupport_chartPullback_subset α hfc hfs hx
    have hy : e.symm z ∈ (extChartAt I α).target := hLs ⟨z, hfK hz, rfl⟩
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  have himage : extChartAt I α '' tsupport (chartPullback I α f) ⊆ L := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := tsupport_chartPullback_subset α hfc hfs hx
    have hy : e.symm z ∈ (extChartAt I α).target := hLs ⟨z, hfK hz, rfl⟩
    rw [(extChartAt I α).right_inv hy]
    exact ⟨z, hfK hz, rfl⟩
  have hb := hbound (measurable_chartPullback α hfm) hs himage
  rw [chartPushedRaw_chartPullback α hfs] at hb
  exact hb.trans (mul_le_mul' le_rfl (eLpNorm_mono_measure f Measure.restrict_le_self))

theorem chartPullback_ae_eq_of_ae_eq
    [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    (q : SmoothRiemannianMetric I M) (α : M)
    {f g : EuStd → ℝ} (hfg : f =ᵐ[volume] g) :
    chartPullback I α f =ᵐ[riemannianVolumeMeasure (I := I) (M := M) q] chartPullback I α g := by
  obtain ⟨S, hSae, hS, hSfg⟩ := hfg.exists_measurable_mem
  have hchart := ae_chart_of_volume q α hS hSae
  have hs : MeasurableSet (chartAt H α).source := (chartAt H α).open_source.measurableSet
  have hres : chartPullback I α f =ᵐ[
      (riemannianVolumeMeasure (I := I) (M := M) q).restrict (chartAt H α).source]
      chartPullback I α g := by
    rw [volume_restrict_eq q α]
    filter_upwards [ae_restrict_of_ae hchart, ae_restrict_mem hs] with x hx hxs
    rw [chartPullback_apply_of_mem α f hxs, chartPullback_apply_of_mem α g hxs]
    exact hSfg _ (hx hxs)
  have h := (ae_restrict_iff' hs).mp hres
  filter_upwards [h] with x hx
  by_cases hxs : x ∈ (chartAt H α).source
  · exact hx hxs
  · rw [chartPullback_apply_of_notMem α f hxs, chartPullback_apply_of_notMem α g hxs]

theorem integral_mul_chartPullback_eq_integral_euclidean
    [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    (q : SmoothRiemannianMetric I M) (α : M) {u : M → ℝ} (hu : Measurable u)
    {f : EuStd → ℝ} (hf : Measurable f)
    (hfs : Function.support f ⊆ chartTargetEuclid (I := I) α) :
    (∫ x, u x * chartPullback I α f x ∂(riemannianVolumeMeasure (I := I) (M := M) q)) =
      ∫ z, chartDensity (I := I) q α ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) *
        u ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) * f z := by
  let e := toEuclidean (E := E)
  have he : MeasurePreserving e (modelHaar (E := E)) volume :=
    ⟨e.continuous.measurable, map_toEuclidean_modelHaar_eq_volume (E := E)⟩
  rw [integral_eq_integral_chartDensity_of_support_in_chart (I := I) q α
    (f := fun x => u x * chartPullback I α f x)
    (hu.mul (measurable_chartPullback α hf)) (fun x hx => by
      rw [chartPullback_apply_of_notMem α f hx, mul_zero])]
  have hpoint {y : E} (hy : y ∈ (extChartAt I α).target) :
      chartPullback I α f ((extChartAt I α).symm y) = f (e y) := by
    have hs := (extChartAt I α).map_target hy
    rw [extChartAt_source] at hs
    rw [chartPullback_apply_of_mem α f hs, (extChartAt I α).right_inv hy]
  calc
    _ = ∫ y in (extChartAt I α).target,
        chartDensity (I := I) q α ((extChartAt I α).symm y) * u ((extChartAt I α).symm y) * f (e y)
        ∂(modelHaar (E := E)) := by
      apply setIntegral_congr_fun (measurableSet_extChartAt_target (I := I) α)
      intro y hy
      dsimp only
      rw [hpoint hy, mul_assoc]
    _ = ∫ z in e '' (extChartAt I α).target,
        chartDensity (I := I) q α ((extChartAt I α).symm (e.symm z)) *
          u ((extChartAt I α).symm (e.symm z)) * f z := by
      rw [he.setIntegral_image_emb e.toHomeomorph.measurableEmbedding]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [Function.notMem_support.mp (fun hs => hz (hfs hs)), mul_zero])

end DifferentialGeometry.Analysis.Sobolev.Chart
