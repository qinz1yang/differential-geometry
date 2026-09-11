import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Integral.Measure

theorem integral_contOn_compact
    {P X W : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [SecondCountableTopologyEither X W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : P → X → W) {K : Set P} (hK : IsCompact K)
    (hF : ContinuousOn (fun p : P × X => F p.1 p.2)
      (K ×ˢ (Set.univ : Set X))) :
    ContinuousOn (fun p : P => ∫ x, F p x ∂μ) K := by
  have hKX : IsCompact (K ×ˢ (Set.univ : Set X)) :=
    hK.prod isCompact_univ
  have hnorm : ContinuousOn (fun p : P × X => ‖F p.1 p.2‖)
      (K ×ˢ (Set.univ : Set X)) := hF.norm
  obtain ⟨C, hC⟩ := hKX.exists_bound_of_continuousOn hnorm
  let C₀ : ℝ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right C 0
  have hCint : Integrable (fun _ : X => C₀) μ := integrable_const C₀
  intro p hp
  have hmeas : ∀ᶠ q in 𝓝[K] p, AEStronglyMeasurable (F q) μ := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hslice : Continuous (F q) := by
      rw [← continuousOn_univ]
      exact hF.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x _ => ⟨hq, Set.mem_univ x⟩)
    exact hslice.aestronglyMeasurable
  have hbound : ∀ᶠ q in 𝓝[K] p,
      ∀ᵐ x ∂μ, ‖F q x‖ ≤ (fun _ : X => C₀) x := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), C₀] using
      (hC (q, x) ⟨hq, Set.mem_univ x⟩).trans (le_max_left C 0)
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun q => F q x) (𝓝[K] p) (𝓝 (F p x)) := by
    filter_upwards with x
    have hx : ContinuousOn (fun q : P => F q x) K :=
      hF.comp (continuousOn_id.prodMk continuousOn_const)
        (fun q hq => ⟨hq, Set.mem_univ x⟩)
    exact hx p hp
  exact tendsto_integral_filter_of_dominated_convergence
    (fun _ : X => C₀) hmeas hbound hCint hlim

attribute [local instance] Measure.Subtype.measureSpace in
theorem continuousOn_intervalIntegral_of_continuousOn_compact
    {P W : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {K : Set P} (hK : IsCompact K) {a b : ℝ} (hab : a ≤ b)
    {f : P → ℝ → W}
    (hf : ContinuousOn (fun p : P × ℝ => f p.1 p.2) (K ×ˢ Icc a b)) :
    ContinuousOn (fun p => ∫ q in a..b, f p q) K := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
      exact isCompact_Icc.measure_lt_top⟩
  have hcont : ContinuousOn (fun p : P × Icc a b => f p.1 p.2.val)
      (K ×ˢ (Set.univ : Set (Icc a b))) := by
    exact hf.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, p.2.property⟩)
  have h := integral_contOn_compact (volume : Measure (Icc a b))
    (fun p q => f p q) hK hcont
  refine h.congr (fun p _hp => ?_)
  change (∫ q in a..b, f p q) = ∫ q : Icc a b, f p q
  rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc]
  exact intervalIntegral.integral_of_le hab

end DifferentialGeometry.Integral.Measure

end
