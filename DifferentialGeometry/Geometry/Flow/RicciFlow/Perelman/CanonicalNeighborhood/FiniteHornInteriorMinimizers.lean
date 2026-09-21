import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornAnnulusCompactness
import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_isCompact_subradial_closedBall (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : W,
      dist (x : UniformSpace.Completion W) H.endpoint < d →
      ∀ R : ℝ, R < dist (x : UniformSpace.Completion W) H.endpoint →
        IsCompact (Metric.closedBall x R) := by
  obtain ⟨delta, hdelta, htail⟩ := finiteHorn_ball_subset_subend g H 0
  refine ⟨delta / 4, by positivity, ?_⟩
  intro x hx R hR
  have ha : 0 < dist (x : UniformSpace.Completion W) H.endpoint - R := sub_pos.mpr hR
  apply (finiteHorn_isCompact_radial_annulus g H 0 ha).of_isClosed_subset
    Metric.isClosed_closedBall
  intro y hy
  have hyx : dist y x ≤ R := hy
  have hxy : dist x y ≤ R := by simpa only [dist_comm] using hyx
  have hupper : dist (y : UniformSpace.Completion W) H.endpoint < delta := by
    have htri := dist_triangle (y : UniformSpace.Completion W)
      (x : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq] at htri
    linarith
  refine ⟨subset_closure ⟨y, htail y hupper, rfl⟩, ?_⟩
  have htri := dist_triangle (x : UniformSpace.Completion W)
    (y : UniformSpace.Completion W) H.endpoint
  rw [UniformSpace.Completion.dist_eq] at htri
  linarith

variable [SigmaCompactSpace W]

theorem finiteHorn_exists_subradial_minimizer (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ x : W,
      dist (x : UniformSpace.Completion W) H.endpoint < d →
      ∀ y : W, dist x y < dist (x : UniformSpace.Completion W) H.endpoint →
      ∃ R : ℝ, dist x y < R ∧ R < dist (x : UniformSpace.Completion W) H.endpoint ∧
        IsCompact (Metric.closedBall x R) ∧
        ∃ gamma : ℝ → W, gamma 0 = x ∧ gamma 1 = y ∧
          ContMDiff 𝓘(ℝ, ℝ) I3 ∞ gamma ∧
          (∀ s ∈ Icc (0 : ℝ) 1, gamma s ∈ Metric.closedBall x R) ∧
          metricPathELength g gamma 0 1 = ENNReal.ofReal (dist x y) ∧
          ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
            metricPathELength g gamma a b =
              ENNReal.ofReal (b - a) * ENNReal.ofReal (dist x y) := by
  obtain ⟨d, hd, hcpt⟩ := finiteHorn_isCompact_subradial_closedBall g H
  refine ⟨d, hd, ?_⟩
  intro x hx y hxy
  let R : ℝ := (dist x y + dist (x : UniformSpace.Completion W) H.endpoint) / 2
  have hxyR : dist x y < R := by dsimp [R]; linarith
  have hR : R < dist (x : UniformSpace.Completion W) H.endpoint := by dsimp [R]; linarith
  have hK := hcpt x hx R hR
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hlength, hsub, _, _⟩ :=
    Geometry.exists_smooth_geodesic_minimizer_of_isCompact_closedBall g
      (fun x y => (edist_dist x y).trans (edist_eq_ofReal_dist g H x y).symm) hK hxyR
  exact ⟨R, hxyR, hR, hK, gamma, hstart, hend, hsmooth, hmem, hlength, hsub⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
