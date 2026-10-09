import DifferentialGeometry.Geometry.Curvature.Surface.PositiveCurvatureSphere
import DifferentialGeometry.Geometry.Exponential.Flat.FlatTorusSmooth
import DifferentialGeometry.Geometry.Metric.Approximation.NonnegativeSectionalSurface
import DifferentialGeometry.Geometry.Curvature.Surface.PeriodicGaussBonnetBinding

/-!
# LFR17: closed nonnegative finite surfaces have smooth type

Chapter 13, row LFR17 (`lem:collapse-finite-surface-classification`). Let `Z` be a compact
connected oriented surface without boundary, modelled on `𝓡 2`, with a `C^n` Riemannian metric
`k` (`2 ≤ n`) of nonnegative finite-order Gaussian curvature. Then `Z` is diffeomorphic to the
round `S²` or to `ℝ²/ℤ²`, and in the torus case the finite-order curvature of `k` vanishes
identically (`finiteSurface_sphere_or_flat_torus`).

Route (no Gauss–Bonnet on the original metric, no area measure, no classification of surfaces;
the statement is the row's):
* SF1 + SF2 (`MetricSmoothing.exists_smooth_flat_or_scalar_pos_of_finite_metric_dim_two`): a
  smooth flat metric or a smooth metric of positive scalar curvature on the same surface;
* flat branch: SF4(c) for a plain smooth metric
  (`ClosedSurface.nonempty_diffeomorph_torus_of_rm04_eq_zero`), then SF5
  (`Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_zero_of_diffeomorph_addCircle_prod`)
  for the ORIGINAL metric `k`;
* positive branch: SF3, orientable case (`ClosedSurface.nonempty_diffeomorph_sphere_of_scalar_pos`:
  Synge, surface Ricci flow to a round metric, simply connected space form).
No smooth nonnegative approximation of `k` is part of the conclusion.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]

/-- **LFR17 (the row).** A compact connected oriented surface modelled on `𝓡 2` with a `C^n`
metric `k`, `2 ≤ n`, of nonnegative finite-order Gaussian curvature is diffeomorphic to the round
`S²`, or it is diffeomorphic to `ℝ²/ℤ²` and the curvature of `k` vanishes identically. -/
theorem finiteSurface_sphere_or_flat_torus (o : ManifoldOrientation (𝓡 2) Z 2) {n : ℕ∞ω}
    (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    Nonempty (Z ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
      (Nonempty (Z ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) ∧
        ∀ x (v w : TangentSpace (𝓡 2) x), k.sectionalCurvature x v w = 0) := by
  rcases MetricSmoothing.exists_smooth_flat_or_scalar_pos_of_finite_metric_dim_two (I := 𝓡 2)
      (by simp) hn k hK with ⟨h, hflat⟩ | ⟨h, hpos⟩
  · obtain ⟨Φ⟩ := ClosedSurface.nonempty_diffeomorph_torus_of_rm04_eq_zero o h hflat
    exact Or.inr ⟨⟨Φ⟩,
      Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_zero_of_diffeomorph_addCircle_prod
        (by simp) k hn Φ.symm hK⟩
  · exact Or.inl (ClosedSurface.nonempty_diffeomorph_sphere_of_scalar_pos o h hpos)

/-- **LFR17, smooth type only.** -/
theorem finiteSurface_sphere_or_torus (o : ManifoldOrientation (𝓡 2) Z 2) {n : ℕ∞ω}
    (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    Nonempty (Z ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
      Nonempty (Z ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) :=
  (finiteSurface_sphere_or_flat_torus o hn k hK).imp id And.left

/-- **LFR17, the torus case with a curvature point.** If the finite-order curvature of `k` is
positive somewhere, the surface is the sphere. -/
theorem finiteSurface_sphere_of_sectionalCurvature_pos (o : ManifoldOrientation (𝓡 2) Z 2)
    {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (k : Bundle.ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {x₀ : Z} {v₀ w₀ : TangentSpace (𝓡 2) x₀} (hpos : 0 < k.sectionalCurvature x₀ v₀ w₀) :
    Nonempty (Z ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) := by
  rcases finiteSurface_sphere_or_flat_torus o hn k hK with hS | ⟨-, hflat⟩
  · exact hS
  · exact absurd (hflat x₀ v₀ w₀) hpos.ne'

end DifferentialGeometry.Geometry.Collapse
