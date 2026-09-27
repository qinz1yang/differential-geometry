import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension








noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry



def IsSmoothPositiveCircleMap (σ : C(loopCircle, loopCircle)) : Prop :=
  ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
    (∀ t, ψ (t + 1) = ψ t + 1) ∧ (∀ t : ℝ, (ψ t : loopCircle) = σ (t : loopCircle))



theorem IsSmoothPositiveCircleMap.weaklyMonotoneOnce {σ : C(loopCircle, loopCircle)}
    (h : IsSmoothPositiveCircleMap σ) : IsWeaklyMonotoneOnce σ := by
  obtain ⟨ψ, hψ, hm, hp, hl⟩ := h
  exact ⟨ψ, hψ.continuous, hl, Or.inl ⟨hm, hp⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]




structure IsConformalMinimizingDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : freeLoop M) (u : C(closedDisk, M)) (σ : C(loopCircle, loopCircle))
    (U : ℂ → M) : Prop where
  extension : SmoothDiskExtension (E := E) u U
  positiveTrace : IsSmoothPositiveCircleMap σ
  trace : diskTrace u = γ.comp σ
  conformal : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U z
  harmonic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, diskMapTension g U z = 0
  minimizesSmooth : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
    diskTrace v = γ → riemannianDiskArea g u ≤ riemannianDiskArea g v



theorem IsConformalMinimizingDisk.weakJordanTrace
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} {σ : C(loopCircle, loopCircle)} {U : ℂ → M}
    (h : IsConformalMinimizingDisk g γ u σ U) : DiskWeakJordanTrace γ u :=
  ⟨σ, h.positiveTrace.weaklyMonotoneOnce, h.trace⟩

end DifferentialGeometry.Geometry
