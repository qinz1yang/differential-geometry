import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def paramGramMatrix (g : SmoothRiemannianMetric I M)
    (Ψ : E → M) :
    E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun w => Matrix.of fun i j =>
    g.inner (Ψ w)
      (mfderiv 𝓘(ℝ, E) I Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
      (mfderiv 𝓘(ℝ, E) I Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))

@[simp] lemma paramGramMatrix_apply
    (g : SmoothRiemannianMetric I M)
    (Ψ : E → M)
    (w : E) (i j : Fin (Module.finrank ℝ E)) :
    paramGramMatrix (I := I) g Ψ w i j =
      g.inner (Ψ w)
        (mfderiv 𝓘(ℝ, E) I Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
        (mfderiv 𝓘(ℝ, E) I Ψ w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := rfl

def paramDensity (g : SmoothRiemannianMetric I M)
    (Ψ : E → M) : E → ℝ :=
  fun w => Real.sqrt (paramGramMatrix (I := I) g Ψ w).det

@[simp] lemma paramDensity_apply
    (g : SmoothRiemannianMetric I M)
    (Ψ : E → M)
    (w : E) :
    paramDensity (I := I) g Ψ w =
      Real.sqrt (paramGramMatrix (I := I) g Ψ w).det := rfl

end DifferentialGeometry.Integral.Measure
