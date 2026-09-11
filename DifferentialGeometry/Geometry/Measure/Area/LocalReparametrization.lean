import DifferentialGeometry.Geometry.Measure.Area.RegionCongruence
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization
import Mathlib.Analysis.Normed.Module.FiniteDimension








noncomputable section

open Manifold Set DifferentialGeometry
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]




theorem riemannianArea_precomp_on (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : ℂ → M} {φ : ℂ → ℂ} {s : Set ℂ} {C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * edist x y)
    (hs : IsOpen s) (hφ : LipschitzOnWith K φ s)
    (hL : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ (L : ℝ≥0∞) * edist (φ x) (φ y)) :
    riemannianArea g (u ∘ φ) s = riemannianArea g u (φ '' s) := by
  have hinj : InjOn φ s := by
    intro x hx y hy heq
    apply edist_eq_zero.mp
    apply le_antisymm _ bot_le
    simpa only [heq, edist_self, mul_zero] using! hL x hx y hy
  let ψ := Function.invFunOn φ s
  have hi : ∀ x ∈ s, ψ (φ x) = x := hinj.leftInvOn_invFunOn
  have hψ : LipschitzOnWith L ψ (φ '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hi x hx, hi y hy]
    exact hL x hx y hy
  obtain ⟨Φ, hΦ, heΦ⟩ := hφ.extend_finite_dimension
  obtain ⟨Ψ, hΨ, heΨ⟩ := hψ.extend_finite_dimension
  have hi' (x : ℂ) (hx : x ∈ s) : Ψ (Φ x) = x := by
    rw [← heΦ hx, ← heΨ (mem_image_of_mem φ hx), hi x hx]
  calc
    _ = riemannianArea g (u ∘ Φ) s := riemannianArea_congr_on_open g hs
      (fun x hx => congrArg u (heΦ hx))
    _ = riemannianArea g u (Φ '' s) := riemannianArea_precomp g hu hΦ hΨ hs.measurableSet hi'
    _ = _ := by rw [heΦ.image_eq]

end DifferentialGeometry.Geometry
