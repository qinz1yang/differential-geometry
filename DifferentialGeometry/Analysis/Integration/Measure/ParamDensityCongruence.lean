import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem paramGramMatrix_eq_of_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    {Ψ Φ : E → M} {x : E}
    (h : Ψ =ᶠ[𝓝 x] Φ) :
    paramGramMatrix g Ψ x = paramGramMatrix g Φ x := by
  have hm := h.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := I)
  have hx := h.eq_of_nhds
  ext i j
  simp only [paramGramMatrix_apply]
  rw [hm, hx]

theorem paramDensity_eq_of_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    {Ψ Φ : E → M} {x : E}
    (h : Ψ =ᶠ[𝓝 x] Φ) :
    paramDensity g Ψ x = paramDensity g Φ x := by
  rw [paramDensity_apply, paramDensity_apply, paramGramMatrix_eq_of_eventuallyEq g h]

theorem paramGramMatrix_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    {Ψ Φ : E → M} {x : E}
    (h : Ψ =ᶠ[𝓝 x] Φ) :
    paramGramMatrix g Ψ =ᶠ[𝓝 x] paramGramMatrix g Φ :=
  h.eventuallyEq_nhds.mono fun _ hy => paramGramMatrix_eq_of_eventuallyEq g hy

theorem paramDensity_eventuallyEq
    (g : SmoothRiemannianMetric I M)
    {Ψ Φ : E → M} {x : E}
    (h : Ψ =ᶠ[𝓝 x] Φ) :
    paramDensity g Ψ =ᶠ[𝓝 x] paramDensity g Φ :=
  h.eventuallyEq_nhds.mono fun _ hy => paramDensity_eq_of_eventuallyEq g hy

end DifferentialGeometry.Integral.Measure
