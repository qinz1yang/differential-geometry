import DifferentialGeometry.Geometry.MinimalSurface.Plateau.AngleTrace
import DifferentialGeometry.Geometry.Metric.CurveUnitReparametrization
import Mathlib.Analysis.Calculus.MeanValue



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




theorem IsConformalMinimizingDisk.nonconstant
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (hu : IsConformalMinimizingDisk g γ u σ U) (hγ : IsSmoothEmbeddedLoop (E := E) γ) :
    ¬ ∃ c : M, ∀ z : closedDisk, u z = c := by
  rintro ⟨c, hc⟩
  obtain ⟨φ, hφ, _, hp, hl⟩ := hu.positiveTrace.exists_angle_parameter
  have ht := hu.extension.angle_trace hu.trace hl
  have hconst : U ∘ circleMap 0 1 = (fun _ : ℝ => c) := by
    funext θ
    have hz : circleMap 0 1 θ ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp [Metric.mem_closedBall, dist_zero_right]
    exact (hu.extension.1 ⟨_, hz⟩).trans (hc _)
  have hder (θ : ℝ) : deriv φ θ = 0 := by
    have he := riemannianCurveSpeed_reparam g
      ((hγ.smooth (φ θ)).mdifferentiableAt (by simp))
      ((hφ.differentiable (by simp)) θ)
    have hz : riemannianCurveSpeed g ((fun t : ℝ => γ (t : loopCircle)) ∘ φ) θ = 0 := by
      rw [← ht, hconst]
      simp only [riemannianCurveSpeed, mfderiv_const]
      change Real.sqrt (g.inner c (0 : TangentSpace 𝓘(ℝ, E) c) 0) = 0
      simp
    rw [hz] at he
    exact abs_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right
      (ne_of_gt (riemannianCurveSpeed_pos g (hγ.immersed (φ θ)))))
  have he := is_const_of_deriv_eq_zero (hφ.differentiable (by simp)) hder (2 * Real.pi) 0
  have hh := hp 0
  rw [zero_add, he] at hh
  linarith

end DifferentialGeometry.Geometry
