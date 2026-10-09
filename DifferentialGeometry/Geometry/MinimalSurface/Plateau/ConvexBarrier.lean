import DifferentialGeometry.Geometry.HarmonicMap.ConvexBarrier
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem IsMorreyDisk.confinement_of_hessian_nonneg
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {C : ℝ}
    (hH : ∀ p : M, C < f p → ∀ v : TangentSpace 𝓘(ℝ, E) p,
      0 ≤ hessFun g f p v v)
    (hγ : ∀ θ : loopCircle, f (γ θ) ≤ C) :
    ∀ z : closedDisk, f (u z) ≤ C := by
  have hb : ∀ z ∈ frontier (Metric.ball (0 : ℂ) 1), f (diskExtension u z) ≤ C := by
    intro z hz
    have hz' : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp (Metric.frontier_ball_subset_sphere hz)
    let c : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz'⟩
    obtain ⟨θ, hθ⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
    have hbd : (diskBoundary θ : ℂ) = z := by
      have hc := congrArg (fun x : Circle => (x : ℂ)) hθ
      simpa only [AddCircle.homeomorphCircle_apply] using! hc
    obtain ⟨σ, _, hσ⟩ := hu.trace
    have hv := congrArg (fun η : freeLoop M => η θ) hσ
    change u (diskBoundary θ) = γ (σ θ) at hv
    rw [← hbd, diskExtension_coe, hv]
    exact hγ (σ θ)
  have hs : IsCompact (closure (Metric.ball (0 : ℂ) 1)) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact isCompact_closedBall _ _
  have hbound := le_boundary_of_planarTension_eq_zero_of_hessian_nonneg
    (U := diskExtension u) (s := Metric.ball (0 : ℂ) 1) g hf hs
    (show ContinuousOn (diskExtension u) (closure (Metric.ball (0 : ℂ) 1)) from
      (u.continuous.comp diskRetraction_lipschitz.continuous).continuousOn)
    (by
      intro z hz
      have hz' : z ∈ Metric.ball (0 : ℂ) 1 := by
        simpa only [Metric.isOpen_ball.interior_eq] using hz
      exact ((hu.smoothInterior z hz').contMDiffAt
        (Metric.isOpen_ball.mem_nhds hz')).of_le (by simp))
    (by
      intro z hz
      change diskMapTension g (diskExtension u) z = 0
      exact hu.harmonic z (by simpa only [Metric.isOpen_ball.interior_eq] using hz))
    (fun z _ hz => hH (diskExtension u z) hz) hb
  intro z
  have hz : (z : ℂ) ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact z.property
  simpa only [diskExtension_coe] using hbound z hz

end DifferentialGeometry.Geometry
