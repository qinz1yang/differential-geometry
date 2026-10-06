/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacher
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- An immersion preserves two-dimensional area density when its source carries
the pullback metric. Differentiability of the parametrization is required at
the point where the chain rule is used. -/
theorem riemannianAreaDensity_pullback_immersion
    [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))
    {u : ℂ → M} {z : ℂ} (hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z) :
    riemannianAreaDensity (g.pullback f hf himm) u z =
      riemannianAreaDensity g (f ∘ u) z := by
  have hd := mfderiv_comp z (hf.mdifferentiableAt (by simp)) hu
  simp only [riemannianAreaDensity, tangentTwoJacobian,
    SmoothRiemannianMetric.pullback_inner, hd]
  rfl

variable [T3Space M]

/-- Pullback area is preserved for a metric-Lipschitz parametrization, including
its nondifferentiable null set. -/
theorem riemannianArea_pullback_immersion
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))
    {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf (g.pullback f hf himm) (u x) (u y) ≤
      (C : ℝ≥0∞) * edist x y) (s : Set ℂ) :
    riemannianArea (g.pullback f hf himm) u s = riemannianArea g (f ∘ u) s := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (ae_mdifferentiableAt_of_riemannian_lipschitz (g.pullback f hf himm) hu)] with z hz
  exact riemannianAreaDensity_pullback_immersion g f hf himm hz

/-- Postcomposition with an immersion preserves the area of every disk that is
Lipschitz for its pullback metric. -/
theorem riemannianDiskArea_pullback_immersion
    (g : SmoothRiemannianMetric 𝓘(ℝ, F) N) (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))
    {u : closedDisk → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf (g.pullback f hf himm) (u x) (u y) ≤
      (C : ℝ≥0∞) * edist x y) :
    riemannianDiskArea (g.pullback f hf himm) u = riemannianDiskArea g (f ∘ u) :=
  riemannianArea_pullback_immersion g f hf himm
    (diskExtension_riemannian_lipschitz (g.pullback f hf himm) hu) _

end DifferentialGeometry.Geometry
