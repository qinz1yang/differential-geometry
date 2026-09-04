import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.MetricSpace.ProperSpace

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Integral.Measure

theorem hasFDerivAt_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (u : V) :
    HasFDerivAt (fun v : V => ∫ x, F v x ∂μ) (∫ x, F' u x ∂μ) u := by
  let K : Set (V × X) := Metric.closedBall u 1 ×ˢ (Set.univ : Set X)
  have hK : IsCompact K :=
    (isCompact_closedBall u 1).prod isCompact_univ
  have hnorm : ContinuousOn (fun p : V × X => ‖F' p.1 p.2‖) K :=
    hF'.norm.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hnorm
  have hs : Metric.closedBall u 1 ∈ 𝓝 u :=
    Metric.closedBall_mem_nhds u zero_lt_one
  have hmeas : ∀ᶠ v in 𝓝 u, AEStronglyMeasurable (F v) μ := by
    filter_upwards [] with v
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hint : Integrable (F u) μ := by
    have hc : Continuous (F u) :=
      hF.comp (continuous_const.prodMk continuous_id)
    exact integrableOn_univ.mp
      (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hmeas' : AEStronglyMeasurable (F' u) μ :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ∀ v ∈ Metric.closedBall u 1,
      ‖F' v x‖ ≤ C := by
    filter_upwards [] with x
    intro v hv
    simpa using hC (v, x) ⟨hv, Set.mem_univ x⟩
  have hCint : Integrable (fun _ : X => C) μ := integrable_const C
  have hdiff' : ∀ᵐ x ∂μ, ∀ v ∈ Metric.closedBall u 1,
      HasFDerivAt (fun w : V => F w x) (F' v x) v := by
    filter_upwards [] with x
    intro v _
    exact hdiff v x
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    hs hmeas hint hmeas' hbound hCint hdiff'

theorem hasFDerivAt_integral_compactOn
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasure μ]
    {U : Set V} (hU : IsOpen U)
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (hF : ContinuousOn (fun p : V × X => F p.1 p.2) (U ×ˢ (Set.univ : Set X)))
    (hF' : ContinuousOn (fun p : V × X => F' p.1 p.2) (U ×ˢ (Set.univ : Set X)))
    (hdiff : ∀ u : V, u ∈ U → ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (u : V) (hu : u ∈ U) :
    HasFDerivAt (fun v : V => ∫ x, F v x ∂μ) (∫ x, F' u x ∂μ) u := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU u hu
  have hδ2 : 0 < δ / 2 := by positivity
  have hδ2lt : δ / 2 < δ := by linarith
  have hcl : Metric.closedBall u (δ / 2) ⊆ U := by
    exact fun y hy => hball ((Metric.closedBall_subset_ball hδ2lt) hy)
  let K : Set (V × X) := Metric.closedBall u (δ / 2) ×ˢ (Set.univ : Set X)
  have hK : IsCompact K :=
    (isCompact_closedBall u (δ / 2)).prod isCompact_univ
  have hKU : K ⊆ U ×ˢ (Set.univ : Set X) := by
    intro p hp
    exact ⟨hcl hp.1, Set.mem_univ p.2⟩
  have hnorm : ContinuousOn (fun p : V × X => ‖F' p.1 p.2‖) K :=
    (hF'.mono hKU).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hnorm
  have hs : Metric.closedBall u (δ / 2) ∈ 𝓝 u :=
    Metric.closedBall_mem_nhds u hδ2
  have hmeas : ∀ᶠ v in 𝓝 u, AEStronglyMeasurable (F v) μ := by
    filter_upwards [hs] with v hv
    have hvU : v ∈ U := hcl hv
    have hc : Continuous (F v) := by
      rw [← continuousOn_univ]
      exact (hF.comp (continuousOn_const.prodMk continuousOn_id)
        (by intro x hx; exact ⟨hvU, Set.mem_univ x⟩))
    exact hc.aestronglyMeasurable
  have hint : Integrable (F u) μ := by
    have hc : Continuous (F u) := by
      rw [← continuousOn_univ]
      exact (hF.comp (continuousOn_const.prodMk continuousOn_id)
        (by intro x hx; exact ⟨hu, Set.mem_univ x⟩))
    exact integrableOn_univ.mp
      (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hmeas' : AEStronglyMeasurable (F' u) μ := by
    have hc : Continuous (F' u) := by
      rw [← continuousOn_univ]
      exact (hF'.comp (continuousOn_const.prodMk continuousOn_id)
        (by intro x hx; exact ⟨hu, Set.mem_univ x⟩))
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ∀ v ∈ Metric.closedBall u (δ / 2),
      ‖F' v x‖ ≤ C := by
    filter_upwards [] with x
    intro v hv
    simpa using hC (v, x) ⟨hv, Set.mem_univ x⟩
  have hCint : Integrable (fun _ : X => C) μ := integrable_const C
  have hdiff' : ∀ᵐ x ∂μ, ∀ v ∈ Metric.closedBall u (δ / 2),
      HasFDerivAt (fun w : V => F w x) (F' v x) v := by
    filter_upwards [] with x
    intro v hv
    exact hdiff v (hcl hv) x
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    hs hmeas hint hmeas' hbound hCint hdiff'

theorem fderiv_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (u : V) :
    fderiv ℝ (fun v : V => ∫ x, F v x ∂μ) u = ∫ x, F' u x ∂μ :=
  (hasFDerivAt_integral_compact μ F F' hF hF' hdiff u).fderiv

theorem continuous_fderiv_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (F'' : V → X → (V →L[ℝ] (V →L[ℝ] W)))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hF'' : Continuous (fun p : V × X => F'' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (hdiff' : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F' v x) (F'' u x) u) :
    Continuous (fun u : V => fderiv ℝ (fun v : V => ∫ x, F v x ∂μ) u) := by
  let D : V → (V →L[ℝ] W) := fun u => ∫ x, F' u x ∂μ
  have hDdiff : Differentiable ℝ D := by
    intro u
    exact (hasFDerivAt_integral_compact μ F' F'' hF' hF'' hdiff' u).differentiableAt
  have hEq : (fun u : V => fderiv ℝ (fun v : V => ∫ x, F v x ∂μ) u) = D := by
    funext u
    exact fderiv_integral_compact μ F F' hF hF' hdiff u
  rw [hEq]
  exact hDdiff.continuous

end DifferentialGeometry.Integral.Measure

end
