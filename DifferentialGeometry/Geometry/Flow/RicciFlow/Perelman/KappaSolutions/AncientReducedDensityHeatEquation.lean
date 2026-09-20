import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityFlux
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityHeatDistribution
import DifferentialGeometry.Analysis.Integration.Integral.CutoffProfile
import DifferentialGeometry.Analysis.Parabolic.WeakEquationExhaustion
import DifferentialGeometry.Analysis.Calculus.ContDiff.Lipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set _root_.MeasureTheory Bundle
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure Entropy
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff ENNReal NNReal _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

private theorem tendsto_ancient_cutoff_tensor_mass
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p o : F.M)
    {a b : ℝ} (ha : 0 < a) {c : ℝ≥0∞}
    (hmass : ∀ t ∈ Icc a b, intrinsicReducedVolume F.S 0 p t = c)
    (μ : Measure (Icc a b)) [IsFiniteMeasure μ] (ψ : C(Icc a b, ℝ))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (r : ι → ℝ≥0) (hr : Tendsto r l (𝓝 0)) :
    Tendsto (fun i => ∫ t : Icc a b, ψ t *
      ∫ x : F.M, perelmanDensity (Module.finrank ℝ E) t (fun y => redLength F.S 0 p y t) x *
        Analysis.CutoffProfile.evalue
          ((r i : ℝ≥0∞) * riemannianEDistOf (F.S.base.metric (-a)) o x)
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-t)) ∂μ)
      l (𝓝 ((∫ t, ψ t ∂μ) * c.toReal)) := by
  let _ : ConnectedSpace F.M := hF.connected
  let R := F.S.base.metric (-a)
  let g : Icc a b → SmoothRiemannianMetric I F.M := fun t => F.S.base.metric (-t)
  let u : Icc a b → F.M → ℝ := fun t =>
    perelmanDensity (Module.finrank ℝ E) t (fun y => redLength F.S 0 p y t)
  let χ : ι → F.M → ℝ := fun i x => Analysis.CutoffProfile.evalue
    ((r i : ℝ≥0∞) * riemannianEDistOf R o x)
  let w : ι → Icc a b × F.M → ℝ := fun i z =>
    χ i z.2 * (ψ z.1 * (riemannianVolumeDensity R (g z.1) z.2 * u z.1 z.2))
  have hm : Integrable (fun z : Icc a b × F.M =>
      riemannianVolumeDensity R (g z.1) z.2 * u z.1 z.2)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R)) :=
    integrable_ancient_perelmanDensity F hF p ha μ R
  have hp := hm.bdd_mul (c := ‖ψ‖) (ψ.continuous.comp continuous_fst).aestronglyMeasurable
    (Eventually.of_forall fun z => ψ.norm_coe_le_norm z.1)
  have hi (i : ι) : Integrable (w i)
      (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R)) := by
    have hc : Continuous (fun z : Icc a b × F.M => χ i z.2) :=
      Analysis.CutoffProfile.continuous_evalue.comp
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
          ((continuous_riemannianEDist R o).comp continuous_snd))
    exact hp.bdd_mul (c := 1) hc.aestronglyMeasurable (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Analysis.CutoffProfile.evalue_mem_Icc _).1]
      exact (Analysis.CutoffProfile.evalue_mem_Icc _).2)
  have hu (t : Icc a b) : Continuous (u t) := by
    have hl : Continuous (fun x : F.M => redLength F.S 0 p x t) :=
      (continuousOn_redLength_space_time_of_ancient F hF p).comp_continuous
        (continuous_const.prodMk continuous_id) (fun x => ⟨ha.trans_le t.property.1, mem_univ x⟩)
    exact continuous_const.mul (Real.continuous_exp.comp hl.neg)
  have hM (t : Icc a b) : (∫ x, u t x
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t)) = c.toReal := by
    have ht : 0 < (t : ℝ) := ha.trans_le t.property.1
    have hnonneg (x : F.M) : 0 ≤ u t x :=
      (mul_pos (prefactor_pos _ ht) (Real.exp_pos _)).le
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnonneg) (hu t).aestronglyMeasurable]
    apply congrArg ENNReal.toReal
    have h := intrinsicReducedVolume_eq_normalizedShrinkerMass F.S 0 p ht
    rw [normalizedShrinkerMass_scaleMetric_inv_eq_lintegral_perelmanDensity _ ht, zero_sub] at h
    exact h.symm.trans (hmass t t.property)
  have htotal : (∫ z : Icc a b × F.M,
      ψ z.1 * (riemannianVolumeDensity R (g z.1) z.2 * u z.1 z.2)
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R)) = (∫ t, ψ t ∂μ) * c.toReal := by
    have hh : Integrable (fun z : Icc a b × F.M =>
        riemannianVolumeDensity R (g z.1) z.2 • (ψ z.1 * u z.1 z.2))
        (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R)) := by
      apply hp.congr
      filter_upwards [] with z
      simp only [smul_eq_mul, Function.comp_apply]
      ring
    calc
      _ = ∫ z : Icc a b × F.M, riemannianVolumeDensity R (g z.1) z.2 • (ψ z.1 * u z.1 z.2)
          ∂μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [smul_eq_mul]
        ring
      _ = ∫ t, ∫ x, ψ t * u t x ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t) ∂μ :=
        integral_prod_volumeDensity_smul μ R g (fun z => ψ z.1 * u z.1 z.2) hh
      _ = _ := by simp only [integral_const_mul, hM, integral_mul_const]
  have hlimit := Analysis.CutoffProfile.tendsto_integral_evalue_smul
    ((continuous_riemannianEDist R o).comp continuous_snd).aemeasurable
    (Eventually.of_forall fun z => riemannianEDistOf_ne_top R o z.2) hp r hr
  simp only [Function.comp_apply] at hlimit
  rw [htotal] at hlimit
  have heq (i : ι) : (∫ z, w i z
      ∂μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R)) =
      ∫ t, ψ t * ∫ x, u t x * χ i x
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t) ∂μ := by
    have hf : Integrable (fun z : Icc a b × F.M =>
        riemannianVolumeDensity R (g z.1) z.2 • (ψ z.1 * (u z.1 z.2 * χ i z.2)))
        (μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R)) := by
      apply (hi i).congr
      filter_upwards [] with z
      dsimp only [w]
      rw [smul_eq_mul]
      ring
    calc
      _ = ∫ z, riemannianVolumeDensity R (g z.1) z.2 • (ψ z.1 * (u z.1 z.2 * χ i z.2))
          ∂μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R) := by
        apply integral_congr_ae
        filter_upwards [] with z
        dsimp only [w]
        rw [smul_eq_mul]
        ring
      _ = ∫ t, ∫ x, ψ t * (u t x * χ i x)
          ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t) ∂μ :=
        integral_prod_volumeDensity_smul μ R g (fun z => ψ z.1 * (u z.1 z.2 * χ i z.2)) hf
      _ = _ := by simp only [integral_const_mul]
  change Tendsto (fun i => ∫ z, w i z
    ∂μ.prod (riemannianVolumeMeasure (I := I) (M := F.M) R)) l (𝓝 _) at hlimit
  simp_rw [heq] at hlimit
  exact hlimit

private theorem integral_subtype_comap_smul_eq_of_tsupport_subset
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a b : ℝ} (ψ : ℝ → ℝ) (f : ℝ → F) (hs : tsupport ψ ⊆ Icc a b) :
    (∫ t : Icc a b, ψ t • f t ∂volume.comap Subtype.val) =
      ∫ t, ψ t • f t := by
  rw [integral_subtype_comap (f := fun t => ψ t • f t) measurableSet_Icc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hs h)), zero_smul]

private theorem tendsto_ancient_cutoff_defect
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p o : F.M)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {c : ℝ≥0∞}
    (hmass : ∀ t ∈ Icc a b, intrinsicReducedVolume F.S 0 p t = c)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψs : tsupport ψ ⊆ Ioo a b)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (r : ι → ℝ≥0) (hr : Tendsto r l (𝓝 0)) :
    let u := fun t => perelmanDensity (Module.finrank ℝ E) t
      (fun x => redLength F.S 0 p x t)
    let g := fun t => F.S.base.metric (-t)
    let χ := fun i x => Analysis.CutoffProfile.evalue
      ((r i : ℝ≥0∞) * riemannianEDistOf (F.S.base.metric (-a)) o x)
    Tendsto (fun i =>
      (∫ t, deriv ψ t * ∫ x, u t x * χ i x
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t)) -
      ∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) (χ i) x)
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t)) l (𝓝 0) := by
  let μ : MeasureTheory.Measure (Icc a b) := volume.comap Subtype.val
  let _ : IsFiniteMeasure μ := by
    let _ : MeasureSpace (Icc a b) := Measure.Subtype.measureSpace
    constructor
    change (volume.comap (Subtype.val : Icc a b → ℝ)) univ < ⊤
    rw [← Measure.Subtype.volume_def, Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top
  let ψ₀ : C(Icc a b, ℝ) := ⟨fun t => ψ t, hψ.continuous.comp continuous_subtype_val⟩
  let ψ₁ : C(Icc a b, ℝ) := ⟨fun t => deriv ψ t,
    (hψ.continuous_deriv le_rfl).comp continuous_subtype_val⟩
  have hm := tendsto_ancient_cutoff_tensor_mass F hF p o ha hmass μ ψ₁ r hr
  have hz : (∫ t : Icc a b, ψ₁ t ∂μ) = 0 := by
    change (∫ t : Icc a b, deriv ψ t ∂volume.comap Subtype.val) = 0
    rw [integral_subtype_comap measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab.le]
    rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => hψ.differentiable (by norm_num) t)
      ((hψ.continuous_deriv le_rfl).intervalIntegrable a b)]
    have ha0 : ψ a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hψs h).1.false)
    have hb0 : ψ b = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hψs h).2.false)
    rw [ha0, hb0, sub_self]
  rw [hz, zero_mul] at hm
  have hf := tendsto_integral_ancient_perelmanDensity_cutoff_flux F hF p o ha μ ψ₀ r hr
  have hresult := hm.sub hf
  simp only [sub_zero] at hresult
  have hψcc : tsupport ψ ⊆ Icc a b := hψs.trans Ioo_subset_Icc_self
  have hdcc : tsupport (deriv ψ) ⊆ Icc a b := tsupport_deriv_subset.trans hψcc
  have heq (φ : ℝ → ℝ) (f : ℝ → ℝ) (hs : tsupport φ ⊆ Icc a b) :
      (∫ t : Icc a b, φ t * f t ∂μ) = ∫ t, φ t * f t := by
    exact integral_subtype_comap_smul_eq_of_tsupport_subset φ f hs
  convert hresult using 1
  funext i
  congr 1
  · rw [← heq (deriv ψ) _ hdcc]
    apply integral_congr_ae
    filter_upwards [] with theta
    simp only [ψ₁, ContinuousMap.coe_mk]
  · rw [← heq ψ _ hψcc]
    apply integral_congr_ae
    filter_upwards [] with theta
    simp only [ψ₀, ContinuousMap.coe_mk]

private theorem integrable_ancient_cutoff_flux_slice
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p o : F.M)
    {a b : ℝ} (ha : 0 < a) (r : ℝ≥0) (t : Icc a b) :
    Integrable (fun x : F.M => (F.S.base.metric (-t)).inner x
      (gradFun (F.S.base.metric (-t))
        (perelmanDensity (Module.finrank ℝ E) t (fun y => redLength F.S 0 p y t)) x)
      (gradFun (F.S.base.metric (-t)) (fun y => Analysis.CutoffProfile.evalue
        ((r : ℝ≥0∞) * riemannianEDistOf (F.S.base.metric (-a)) o y)) x))
      (riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric (-t))) := by
  let _ := riemannianVolumeMeasure_sigmaFinite (F.S.base.metric (-a))
  let ψ : C(Icc a b, ℝ) := ⟨fun _ => 1, continuous_const⟩
  have hi := integrable_ancient_perelmanDensity_cutoff_flux F hF p o ha (Measure.dirac t) ψ r
  simp only [ψ, ContinuousMap.coe_mk, mul_one] at hi
  have hi' := hi.prod_right_ae
  rw [ae_dirac_eq] at hi'
  exact (integrable_riemannianVolumeMeasure_iff (F.S.base.metric (-a))
    (F.S.base.metric (-t)) _).mpr hi'

private theorem continuous_ancient_density_slice
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) (t : ℝ) :
    Continuous (perelmanDensity (Module.finrank ℝ E) t (fun x => redLength F.S 0 p x t)) := by
  have hl : Continuous (fun x => redLength F.S 0 p x t) := by
    by_cases ht : 0 < t
    · exact continuous_redLength_of_ancient F hF p ht
    · simp only [redLength, Real.sqrt_eq_zero_of_nonpos (le_of_not_gt ht), mul_zero, div_zero]
      exact continuous_const
  exact continuous_const.mul (Real.continuous_exp.comp hl.neg)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set _root_.MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure Entropy
open scoped _root_.Manifold ContDiff _root_.Topology NNReal ENNReal
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
private local instance : MeasurableSpace F.M := borel F.M
private local instance : BorelSpace F.M := ⟨rfl⟩

theorem ancient_perelmanDensity_tensor_weak_eq_in_chart_of_constant_reducedVolume
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {c : ℝ≥0∞}
    (hmass : ∀ t ∈ Icc a b, intrinsicReducedVolume F.S 0 p t = c)
    (α : F.M) (χ : C(F.M, ℝ)) (hχc : HasCompactSupport (χ : F.M → ℝ)) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχsm : ContMDiff I 𝓘(ℝ) ∞ (χ : F.M → ℝ))
    (hχs : tsupport (χ : F.M → ℝ) ⊆ (chartAt H α).source)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ioo a b) (hψ0 : ∀ t, 0 ≤ ψ t) :
    let u := fun t => perelmanDensity (Module.finrank ℝ E) t
      (fun x => redLength F.S 0 p x t)
    let g := fun t => F.S.base.metric (-t)
    Integrable (fun t => ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t)) volume ∧
    Integrable (fun t => deriv ψ t * ∫ x, u t x * χ x
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t)) volume ∧
    (∫ t, ψ t * ∫ x, (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x)
      ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t)) =
      ∫ t, deriv ψ t * ∫ x, u t x * χ x
        ∂riemannianVolumeMeasure (I := I) (M := F.M) (g t) := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace F.M := ChartedSpace.locallyCompactSpace H F.M
  let _ : ConnectedSpace F.M := hF.connected
  let u : ℝ → C(F.M, ℝ) := fun t =>
    ⟨perelmanDensity (Module.finrank ℝ E) t (fun x => redLength F.S 0 p x t),
      continuous_ancient_density_slice F hF p t⟩
  let g : ℝ → SmoothRiemannianMetric I F.M := fun t => F.S.base.metric (-t)
  have hR : RiemannianMetricComplete (F.S.base.metric (-a)) :=
    ⟨MetricComplete.complete (F.atTime (-a)) (hF.complete (-a) (neg_nonpos.mpr ha.le))⟩
  obtain ⟨Cχ, hCχ⟩ := Geometry.Riemannian.exists_lipschitz_constant_of_smooth_compact_support
    (F.S.base.metric (-a)) hR hχsm hχc
  have hψpos : tsupport ψ ⊆ Ioi 0 := fun t ht => ha.trans (hψs ht).1
  have hwχ := ancient_perelmanDensity_tensor_weak_le F hF p (F.S.base.metric (-a))
    χ hχc hχ0 hCχ hψ hψc hψpos hψ0
  refine ⟨hwχ.1, hwχ.2.1, ?_⟩
  let r : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  have hr : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hr0 (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  let ζ : ℕ → C(F.M, ℝ) := fun n =>
    ⟨fun x => Analysis.CutoffProfile.evalue
      ((r n : ℝ≥0∞) * riemannianEDistOf (F.S.base.metric (-a)) F.basepoint x),
      Analysis.CutoffProfile.continuous_evalue.comp
        ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
          (Geometry.Riemannian.continuous_riemannianEDist (F.S.base.metric (-a)) F.basepoint))⟩
  have hu : LocallyLipschitzOn (Ioo a b ×ˢ (extChartAt I α).target)
      (fun z : ℝ × E => u z.1 ((extChartAt I α).symm z.2)) :=
    (ancient_perelmanDensity_locallyLipschitzOn_in_chart F hF p α).mono
      (fun _ hw => ⟨ha.trans hw.1.1, hw.2⟩)
  have hχi (t : ℝ) (ht : t ∈ Ioo a b) :
      Integrable (fun x => (g t).inner x (gradFun (g t) (u t) x) (gradFun (g t) χ x))
        (riemannianVolumeMeasure (I := I) (M := F.M) (g t)) := by
    have hus : LocallyLipschitzOn (extChartAt I α).target (scalarOnE (I := I) α (u t)) := by
      apply locallyLipschitzOn_iff_restrict.mpr
      have hmap : LipschitzWith 1 (fun x : (extChartAt I α).target =>
          (⟨(t, x.1), ht, x.2⟩ : Ioo a b ×ˢ (extChartAt I α).target)) := by
        simpa only [one_mul, Function.comp_apply] using
          ((LipschitzWith.prodMk_left t).comp (LipschitzWith.subtype_val (extChartAt I α).target)).subtype_mk
            (fun x => ⟨ht, x.2⟩)
      have hh : LocallyLipschitz
          (((Ioo a b ×ˢ (extChartAt I α).target).domRestrict
            (fun z : ℝ × E => u z.1 ((extChartAt I α).symm z.2))) ∘
            (fun x : (extChartAt I α).target =>
              (⟨(t, x.1), ht, x.2⟩ : Ioo a b ×ˢ (extChartAt I α).target))) :=
        hu.restrict.comp hmap.locallyLipschitz
      exact hh
    have hχchart : ContDiffOn ℝ 1 (scalarOnE (I := I) α χ) (extChartAt I α).target :=
      (scalarOnE_contDiffOn α hχsm).of_le (by simp)
    exact Analysis.integrable_inner_gradFun_of_locallyLipschitzOn_chart (g t) α (u t) χ hus
      (hχchart.locallyLipschitzOn_of_isOpen (isOpen_extChartAt_target (I := I) α)) hχc hχs
  apply Analysis.Parabolic.integral_tensor_test_eq_of_exhaustion (F.S.base.metric (-a)) g u hψs
    (fun η hηc hη0 hηL => by
      obtain ⟨Cη, hCη⟩ := hηL
      exact ancient_perelmanDensity_tensor_weak_le F hF p (F.S.base.metric (-a))
        η hηc hη0 hCη hψ hψc hψpos hψ0)
    χ hχc hχ0 ⟨Cχ, hCχ⟩ hχi ζ
    (fun n => Geometry.Riemannian.hasCompactSupport_distance_cutoff
      (F.S.base.metric (-a)) hR F.basepoint (hr0 n))
    (fun n x => (Analysis.CutoffProfile.evalue_mem_Icc _).1)
    (fun n => ⟨⟨Analysis.CutoffProfile.derivBound, Analysis.CutoffProfile.derivBound_nonneg⟩ * r n,
      Geometry.Riemannian.edist_distance_cutoff_le (F.S.base.metric (-a)) F.basepoint (r n)⟩)
    (fun n t ht => ?_)
    (Geometry.Riemannian.eventually_distance_cutoff_eq_one_on_isCompact
      (F.S.base.metric (-a)) F.basepoint hχc r hr)
    (tendsto_ancient_cutoff_defect F hF p F.basepoint ha hab hmass hψ hψs r hr)
  have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hi := integrable_ancient_cutoff_flux_slice F hF p F.basepoint ha (r n) ⟨t, ht'⟩
  simpa only [g, u, ζ, ContinuousMap.coe_mk] using hi

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem ancient_perelmanDensity_weak_eq_in_chart_of_constant_reducedVolume
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {c : ℝ≥0∞}
    (hmass : ∀ t ∈ Icc a b, intrinsicReducedVolume F.S 0 p t = c)
    (α : F.M) {φ : ℝ × E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo a b ×ˢ (extChartAt I α).target) :
    let u := fun w : ℝ × E => perelmanDensity (Module.finrank ℝ E) w.1
      (fun x => redLength F.S 0 p x w.1) ((extChartAt I α).symm w.2)
    let ρ := fun w : ℝ × E => chartDensityOnE (F.S.base.metric (-w.1)) α w.2
    let A := fun w : ℝ × E => fun i j : Fin (Module.finrank ℝ E) =>
      chartInvGramOnE (F.S.base.metric (-w.1)) α i j w.2;
    (∑ i, ∑ j, ∫ w, (A w i j * ρ w) * lineDeriv ℝ u w (0, chartModelBasis E j) *
      fderiv ℝ φ w (0, chartModelBasis E i) ∂volume.prod (modelHaar (E := E))) =
        ∫ w, ρ w * u w * fderiv ℝ φ w (1, 0) ∂volume.prod (modelHaar (E := E)) := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _ht, z, hz⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) z (by norm_num : 0 < 4) _ hz⟩
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace F.M := ChartedSpace.locallyCompactSpace H F.M
  let u : ℝ → C(F.M, ℝ) := fun t =>
    ⟨perelmanDensity (Module.finrank ℝ E) t (fun x => redLength F.S 0 p x t),
      continuous_ancient_density_slice F hF p t⟩
  apply Analysis.Parabolic.integral_chart_test_eq_of_tensor_test
    (I := I) (M := F.M) (J := Ioo a b) isOpen_Ioo
    (fun t => F.S.base.metric (-t)) α u
    ((ancient_perelmanDensity_locallyLipschitzOn_in_chart F hF p α).mono
      (fun _ hw => ⟨ha.trans hw.1.1, hw.2⟩))
    (fun i j => ?_)
    (fun ψ hψ hψc hψs hψ0 => ancient_perelmanDensity_weak_le_in_chart F hF p α
      (volume.prod (modelHaar (E := E)))
      ((hψ.of_le (by simp) : ContDiff ℝ 1 ψ).locallyLipschitz.locallyLipschitzOn)
      hψc (hψs.trans (prod_mono (fun _ ht => ha.trans ht.1) Subset.rfl)) hψ0)
    (fun χ hχsm hχc hχs hχ0 ψ hψ hψc hψs hψ0 =>
      (ancient_perelmanDensity_tensor_weak_eq_in_chart_of_constant_reducedVolume
        F hF p ha hab hmass α χ hχc hχ0 hχsm hχs (hψ.of_le (by simp)) hψc hψs hψ0).2.2)
    hφ hφc hφs
  have hmap : ContinuousOn (fun z : ℝ × F.M => (-z.1, z.2))
      (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    (continuous_fst.neg.prodMk continuous_snd).continuousOn
  have hmaps : MapsTo (fun z : ℝ × F.M => (-z.1, z.2))
      (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
      (ancientTimeInterval.carrier ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    fun z hz => ⟨show -z.1 ≤ 0 from neg_nonpos.mpr (ha.trans hz.1.1).le, hz.2⟩
  have hc : ContinuousOn
      ((fun z : ℝ × F.M => chartGramMatrix (F.S.base.metric z.1) α z.2 i j) ∘
        (fun z : ℝ × F.M => (-z.1, z.2)))
      (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    (F.isSolution.smoothMetric.chartGramMatrix_continuousOn_carrier α i j).comp hmap hmaps
  exact hc

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
