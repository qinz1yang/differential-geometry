import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Integral.Measure

theorem hasFDerivAt_integral_compactOn
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
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
  have hslice (v : V) (hv : v ∈ U) : Continuous (F v) := by
    rw [← continuousOn_univ]
    exact hF.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ => ⟨hv, mem_univ x⟩)
  have hslice' : Continuous (F' u) := by
    rw [← continuousOn_univ]
    exact hF'.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ => ⟨hu, mem_univ x⟩)
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (univ : Set X)).exists_bound_of_continuousOn
    hslice'.continuousOn
  let A := (U ×ˢ (univ : Set X)) ∩
    (fun p : V × X => ‖F' p.1 p.2‖) ⁻¹' Iio (C + 1)
  have hA : IsOpen A :=
    hF'.norm.isOpen_inter_preimage (hU.prod isOpen_univ) isOpen_Iio
  have hsub : ({u} : Set V) ×ˢ (univ : Set X) ⊆ A := by
    rintro ⟨v, x⟩ ⟨rfl, hx⟩
    exact ⟨⟨hu, hx⟩, (hC x hx).trans_lt (lt_add_one C)⟩
  obtain ⟨S, T, hS, _, huS, hT, hST⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hA hsub
  have hnear : S ∩ U ∈ 𝓝 u :=
    (hS.inter hU).mem_nhds ⟨singleton_subset_iff.mp huS, hu⟩
  have hmeas : ∀ᶠ v in 𝓝 u, AEStronglyMeasurable (F v) μ := by
    filter_upwards [hnear] with v hv
    exact (hslice v hv.2).aestronglyMeasurable
  have hint : Integrable (F u) μ :=
    integrableOn_univ.mp ((hslice u hu).continuousOn.integrableOn_compact isCompact_univ)
  have hbound : ∀ᵐ x ∂μ, ∀ v ∈ S ∩ U, ‖F' v x‖ ≤ C + 1 := by
    filter_upwards [] with x
    intro v hv
    exact le_of_lt (hST (show (v, x) ∈ S ×ˢ T from ⟨hv.1, hT (mem_univ x)⟩)).2
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hnear hmeas hint
    hslice'.aestronglyMeasurable hbound (integrable_const (C + 1))
    (Filter.Eventually.of_forall fun x v hv => hdiff v hv.2 x)

theorem hasFDerivAt_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (u : V) :
    HasFDerivAt (fun v : V => ∫ x, F v x ∂μ) (∫ x, F' u x ∂μ) u := by
  exact hasFDerivAt_integral_compactOn μ isOpen_univ F F' hF.continuousOn hF'.continuousOn
    (fun v _ x => hdiff v x) u (mem_univ u)

theorem fderiv_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SecondCountableTopology X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
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
    [NormedAddCommGroup V] [NormedSpace ℝ V]
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
