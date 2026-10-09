import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDeepMinimizers
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeConvergence

set_option autoImplicit false
noncomputable section
open Filter Set Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_finiteHorn_end_geometry_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (W : Type u) [MetricSpace W] [ChartedSpace ThreeSpace W]
      [IsManifold I3 ∞ W] [SigmaCompactSpace W], ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collarDepth →
      (∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
        ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) →
        hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
        Nonempty (RayApproximation H a b lo hi)) ∧
      Nonempty (EndAngles H) ∧
      ∀ angles : EndAngles H, ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
        ∀ s t : ℝ, s ∈ Ioc 0 (min a.length d) → t ∈ Ioc 0 (min b.length d) →
          endComparisonAngle a b s t ≤ angles.angle a b := by
  obtain ⟨H₀, hH₀, hsave⟩ := exists_no_endpoint_shortcut_depth_uniform_in_manifold.{u}
  refine ⟨H₀, hH₀, ?_⟩
  intro W _ _ _ _ g H hdepth
  have hno := hsave W g H hdepth
  obtain ⟨d, hd, hm⟩ := finiteHorn_end_angle_monotone_of_endRay_dist_lt_sum g H hno
  refine ⟨?_, finite_horn_end_angle_of_monotone H d hd hm, ?_⟩
  · obtain ⟨r, hr, happ⟩ := finiteHorn_ray_approximation_in_subend_of_endRay_dist_lt_sum g H hno 0
    refine ⟨r, hr, ?_⟩
    intro a b lo hi hlo hia hib hir
    obtain ⟨A, _⟩ := happ a b lo hi hlo hia hib hir
    exact ⟨A⟩
  · intro angles
    exact exists_d_endComparisonAngle_le_angle H hd hm angles

def hornEndGeometryDepth : ℝ :=
  Classical.choose exists_finiteHorn_end_geometry_depth.{u}

theorem hornEndGeometryDepth_pos : 0 < hornEndGeometryDepth.{u} :=
  (Classical.choose_spec exists_finiteHorn_end_geometry_depth.{u}).1

theorem hornEndGeometryDepth_spec
    (W : Type u) [MetricSpace W] [ChartedSpace ThreeSpace W]
    [IsManifold I3 ∞ W] [SigmaCompactSpace W]
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (hdepth : hornEndGeometryDepth.{u} ≤ H.collarDepth) :
    (∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
      ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) →
      hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      Nonempty (RayApproximation H a b lo hi)) ∧
    Nonempty (EndAngles H) ∧
    ∀ angles : EndAngles H, ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
      ∀ s t : ℝ, s ∈ Ioc 0 (min a.length d) → t ∈ Ioc 0 (min b.length d) →
        endComparisonAngle a b s t ≤ angles.angle a b :=
  (Classical.choose_spec exists_finiteHorn_end_geometry_depth.{u}).2 W g H hdepth

noncomputable def hornDepthThreshold : ℝ := max hornEndGeometryDepth.{u} 1

theorem hornEndGeometryDepth_le_hornDepthThreshold :
    hornEndGeometryDepth.{u} ≤ hornDepthThreshold.{u} := le_max_left _ _

theorem one_le_hornDepthThreshold : (1 : ℝ) ≤ hornDepthThreshold.{u} := le_max_right _ _

theorem hornDepthThreshold_pos : 0 < hornDepthThreshold.{u} :=
  zero_lt_one.trans_le one_le_hornDepthThreshold.{u}

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
