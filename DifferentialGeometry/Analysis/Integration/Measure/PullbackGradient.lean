import DifferentialGeometry.Analysis.Integration.Measure.Pullback
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Bundle.VectorField.Pushforward

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open Bundle MeasureTheory
open Geometry.Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_inner_gradientFun_pullbackMetric
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (f : M → ℝ) (hf : MDifferentiable I 𝓘(ℝ, ℝ) f)
    (X : ∀ x : M, TangentSpace I x) :
    (∫ x, (Diffeomorph.pullbackMetric g Φ).inner x
      (gradientFun (Diffeomorph.pullbackMetric g Φ) (f ∘ Φ) x) (X x)
      ∂riemannianVolumeMeasure (I := I) (M := M) (Diffeomorph.pullbackMetric g Φ)) =
      ∫ y, g.inner y (gradientFun g f y) (Diffeomorph.pushforward Φ X y)
        ∂riemannianVolumeMeasure (I := I) (M := M) g := by
  have hpoint (x : M) : (Diffeomorph.pullbackMetric g Φ).inner x
      (gradientFun (Diffeomorph.pullbackMetric g Φ) (f ∘ Φ) x) (X x) =
      g.inner (Φ x) (gradientFun g f (Φ x)) (Diffeomorph.pushforward Φ X (Φ x)) := by
    rw [inner_gradientFun, inner_gradientFun, Diffeomorph.pushforward_image]
    exact mvfderiv_comp_apply x (hf (Φ x))
      (Φ.contMDiff.mdifferentiableAt (by simp)) (X x)
  rw [riemannianVolumeMeasure_pullback]
  have he : MeasurableEmbedding (Φ.symm : M → M) :=
    Φ.symm.toHomeomorph.isClosedEmbedding.measurableEmbedding
  rw [he.integral_map]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    have h := hpoint (Φ.symm y)
    rw [Φ.apply_symm_apply] at h
    exact h

end DifferentialGeometry.Integral.Measure
