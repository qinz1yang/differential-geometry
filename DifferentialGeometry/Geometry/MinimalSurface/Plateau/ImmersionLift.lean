/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Measure.Area.ImmersionPullback
import DifferentialGeometry.Geometry.Metric.Pullback.ImmersionDistance
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- A lift of the original minimizing disk retains its full weak-Jordan-trace
Lipschitz comparison law for the metric pulled back by the given immersion.
Both the lifted disk and lifted boundary loop are tied to the original ones by
their projection equations. -/
theorem IsMorreyDisk.minimizesLipschitz_of_immersion_lift
    {g : SmoothRiemannianMetric 𝓘(ℝ, F) N}
    {γ : freeLoop N} {u : C(closedDisk, N)} (hu : IsMorreyDisk g γ u)
    (p : M → N) (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (uLift : C(closedDisk, M)) (γLift : freeLoop M)
    (hmap : ∀ z, p (uLift z) = u z) (hloop : ∀ θ, p (γLift θ) = γ θ)
    {C : ℝ≥0}
    (hLift : ∀ z w, riemannianEDistOf (g.pullback p hp himm) (uLift z) (uLift w) ≤
      (C : ℝ≥0∞) * edist z w)
    (v : C(closedDisk, M)) (hvtrace : DiskWeakJordanTrace γLift v)
    (hvLip : ∃ L : ℝ≥0, ∀ z w : closedDisk,
      riemannianEDistOf (g.pullback p hp himm) (v z) (v w) ≤
        (L : ℝ≥0∞) * edist z w) :
    riemannianDiskArea (g.pullback p hp himm) uLift ≤
      riemannianDiskArea (g.pullback p hp himm) v := by
  let pc : C(M, N) := ⟨p, hp.continuous⟩
  have hproj : pc.comp uLift = u := by
    ext z
    exact hmap z
  have htrace : DiskWeakJordanTrace γ (pc.comp v) := by
    obtain ⟨σ, hσ, hboundary⟩ := hvtrace
    refine ⟨σ, hσ, ?_⟩
    ext θ
    change p (v (diskBoundary θ)) = γ (σ θ)
    have hb := congrArg (fun δ : freeLoop M => δ θ) hboundary
    change v (diskBoundary θ) = γLift (σ θ) at hb
    rw [hb, hloop]
  obtain ⟨L, hL⟩ := hvLip
  have hprojectedLip : ∀ z w : closedDisk,
      riemannianEDistOf g ((pc.comp v) z) ((pc.comp v) w) ≤
        (L : ℝ≥0∞) * edist z w := by
    intro z w
    exact (riemannianEDistOf_le_pullback g p hp himm (v z) (v w)).trans (hL z w)
  have huArea : riemannianDiskArea (g.pullback p hp himm) uLift =
      riemannianDiskArea g u := by
    rw [riemannianDiskArea_pullback_immersion g p hp himm hLift]
    change riemannianDiskArea g (pc.comp uLift) = _
    rw [hproj]
  rw [huArea, riemannianDiskArea_pullback_immersion g p hp himm hL]
  exact hu.minimizesLipschitz (pc.comp v) htrace ⟨L, hprojectedLip⟩

end DifferentialGeometry.Geometry
