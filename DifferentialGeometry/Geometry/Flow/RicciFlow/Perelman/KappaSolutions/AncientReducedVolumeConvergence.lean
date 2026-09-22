import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientVolumeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedDensityMeasurability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientGaussianIntegrability
import DifferentialGeometry.Analysis.Integration.Measure.SandwichConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set MeasureTheory
open CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped ContDiff _root_.Manifold _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance terminalVolumeLimitTopology : TopologicalSpace F.M := F.topology
private local instance terminalVolumeLimitCharted : ChartedSpace H F.M := F.charted
private local instance terminalVolumeLimitSmooth : IsManifold I ∞ F.M := F.smooth
private local instance terminalVolumeLimitT2 : T2Space F.M := F.t2
private local instance terminalVolumeLimitSigma : SigmaCompactSpace F.M := F.sigmaCompact
private local instance terminalVolumeLimitMeasurable : MeasurableSpace F.M := borel F.M
private local instance terminalVolumeLimitBorel : BorelSpace F.M := ⟨rfl⟩

theorem ancient_reducedVolume_tendsto_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p : F.M) :
    Tendsto (fun T : ℝ => intrinsicReducedVolume F.S T p tau) (𝓝[<] (0 : ℝ))
      (𝓝 (intrinsicReducedVolume F.S 0 p tau)) := by
  let mu : Measure F.M := riemannianVolumeMeasure (I := I) (M := F.M)
    (F.S.base.metric (0 - tau))
  let nu : ℝ → Measure F.M := fun T => riemannianVolumeMeasure (I := I) (M := F.M)
    (F.S.base.metric (T - tau))
  let density : ℝ → F.M → ℝ≥0∞ := fun T q => ENNReal.ofReal (redDensity F.S T p q tau)
  let A : ℝ := Real.exp (-((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  let bound : F.M → ℝ≥0∞ := fun q => ENNReal.ofReal (A * Real.exp
    (-(1 / (4 * tau)) * (riemannianEDistOf (I := I) (F.S.base.metric 0) p q).toReal ^ 2))
  obtain ⟨K, hK, hvol⟩ := exists_ancientKappa_volumeMeasure_le_exp F hF
  let c : ℝ → ℝ≥0∞ := fun T =>
    ENNReal.ofReal (Real.sqrt (Real.exp (2 * K * (0 - T)) ^ Module.finrank ℝ E))
  have hmeas : ∀ᶠ T in 𝓝[<] (0 : ℝ), Measurable (density T) := by
    filter_upwards [self_mem_nhdsWithin] with T hT
    exact ENNReal.measurable_ofReal.comp
      (ancient_measurable_redDensity F hF hT.le htau p)
  have hbound : ∀ᶠ T in 𝓝[<] (0 : ℝ), ∀ᵐ q ∂mu, density T q ≤ bound q := by
    filter_upwards [self_mem_nhdsWithin] with T hT
    exact ae_of_all _ (fun q => ENNReal.ofReal_le_ofReal
      (ancient_redDensity_le_terminal_gaussian F hF hT.le p q htau))
  have hfin : ∫⁻ q, bound q ∂mu ≠ (⊤ : ℝ≥0∞) :=
    ancient_lintegral_terminal_gaussian_ne_top F hF p (by linarith : 0 - tau ≤ 0)
      (by positivity : 0 < 1 / (4 * tau)) (Real.exp_pos _).le
  have hpoint : ∀ᵐ q ∂mu,
      Tendsto (fun T => density T q) (𝓝[<] (0 : ℝ)) (𝓝 (density 0 q)) := by
    exact ae_of_all _ (fun q => ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((ancient_redDensity_continuousWithinAt_terminal F hF htau p q).mono
        Iio_subset_Iic_self))
  have hc : Tendsto c (𝓝[<] (0 : ℝ)) (𝓝 1) := by
    have hcont : Continuous c := by
      exact ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp
        ((Real.continuous_exp.comp (continuous_const.mul
          (continuous_const.sub continuous_id))).pow _))
    have hzero : c 0 = 1 := by simp only [c, sub_self, mul_zero, Real.exp_zero,
      one_pow, Real.sqrt_one, ENNReal.ofReal_one]
    rw [← hzero]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlower : ∀ᶠ T in 𝓝[<] (0 : ℝ), mu ≤ nu T := by
    filter_upwards [self_mem_nhdsWithin] with T hT
    exact ancient_volumeMeasure_le_of_time_le F hF (sub_le_sub_right hT.le tau)
      (by linarith : 0 - tau ≤ 0)
  have hupper : ∀ᶠ T in 𝓝[<] (0 : ℝ), nu T ≤ c T • mu := by
    filter_upwards [self_mem_nhdsWithin] with T hT
    have h := hvol (T - tau) (0 - tau) (sub_le_sub_right hT.le tau)
      (by linarith : 0 - tau ≤ 0)
    have hdiff : 0 - tau - (T - tau) = 0 - T := by ring
    simpa only [hdiff] using h
  exact tendsto_lintegral_of_dominated_convergence_of_measure_sandwich bound
    hmeas hbound hfin hpoint hc hlower hupper

theorem ancient_reducedVolume_upperSemicontinuousWithinAt_terminal
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {tau : ℝ} (htau : 0 < tau) (p : F.M) :
    UpperSemicontinuousWithinAt (fun T => intrinsicReducedVolume F.S T p tau) (Iio 0) 0 := by
  have hcont : ContinuousWithinAt (fun T => intrinsicReducedVolume F.S T p tau) (Iio 0) 0 :=
    ancient_reducedVolume_tendsto_terminal F hF htau p
  exact hcont.upperSemicontinuousWithinAt


theorem ancient_reducedVolume_antitone
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) := by
  have hdim : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    have hb := ancientKappa_rmNormLeScalar_finrank F hF t ht x
    rw [hzero, Nat.cast_zero] at hb
    norm_num at hb
    have hn : 0 ≤ F.rmNormSq (I := I) t x := by
      simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
        DifferentialGeometry.Tensor0SBundle.normSq0S_nonneg
          (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
    have hz : Real.sqrt (F.rmNormSq (I := I) t x) = 0 :=
      le_antisymm hb (Real.sqrt_nonneg _)
    exact hx ((Real.sqrt_eq_zero hn).mp hz)
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  intro tau₁ h₁ tau₂ h₂ h₁₂
  apply le_of_tendsto_of_tendsto
    (ancient_reducedVolume_tendsto_terminal F hF h₂ p)
    (ancient_reducedVolume_tendsto_terminal F hF h₁ p)
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (ancient_reducedVolume_antitone_of_regular_base F hF p
    (T := T) hT) h₁ h₂ h₁₂


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
