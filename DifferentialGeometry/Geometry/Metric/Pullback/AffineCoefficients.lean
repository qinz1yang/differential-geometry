import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Ring

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem pullbackMetricCoefficients_comp_add_smul
    (g : SmoothRiemannianMetric I M) {f : V → M} (b : V) (r : ℝ) {y : V}
    (hf : MDifferentiableAt 𝓘(ℝ, V) I f (b + r • y)) (v w : V) :
    pullbackMetricCoefficients g (fun z => f (b + r • z)) y v w =
      r ^ 2 * pullbackMetricCoefficients g f (b + r • y) v w := by
  let S : V → V := fun z => b + r • z
  have hS : HasFDerivAt S (r • ContinuousLinearMap.id ℝ V) y :=
    ((hasFDerivAt_id y).const_smul r).const_add b
  have hchain :
      (mfderiv 𝓘(ℝ, V) I (fun z => f (b + r • z)) y : V →L[ℝ] E) =
        (mfderiv 𝓘(ℝ, V) I f (b + r • y) : V →L[ℝ] E).comp
          (r • ContinuousLinearMap.id ℝ V) := by
    have hc := mfderiv_comp (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, V)) (I'' := I)
      y hf hS.differentiableAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv, hS.fderiv] at hc
    exact hc
  have hderiv (u : V) :
      (mfderiv 𝓘(ℝ, V) I (fun z => f (b + r • z)) y : V →L[ℝ] E) u =
        r • (mfderiv 𝓘(ℝ, V) I f (b + r • y) : V →L[ℝ] E) u := by
    calc
      (mfderiv 𝓘(ℝ, V) I (fun z => f (b + r • z)) y : V →L[ℝ] E) u =
          (mfderiv 𝓘(ℝ, V) I f (b + r • y) : V →L[ℝ] E) (r • u) :=
        congrArg (fun L : V →L[ℝ] E => L u) hchain
      _ = r • (mfderiv 𝓘(ℝ, V) I f (b + r • y) : V →L[ℝ] E) u :=
        map_smul _ _ _
  simp only [pullbackMetricCoefficients_apply]
  change (g.inner (f (b + r • y)) : E →L[ℝ] E →L[ℝ] ℝ)
      ((mfderiv 𝓘(ℝ, V) I (fun z => f (b + r • z)) y : V →L[ℝ] E) v)
      ((mfderiv 𝓘(ℝ, V) I (fun z => f (b + r • z)) y : V →L[ℝ] E) w) =
    r ^ 2 * (g.inner (f (b + r • y)) : E →L[ℝ] E →L[ℝ] ℝ)
      ((mfderiv 𝓘(ℝ, V) I f (b + r • y) : V →L[ℝ] E) v)
      ((mfderiv 𝓘(ℝ, V) I f (b + r • y) : V →L[ℝ] E) w)
  rw [hderiv v, hderiv w]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end DifferentialGeometry.Geometry
