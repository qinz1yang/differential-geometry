import DifferentialGeometry.Topology.SphereSeparation.Schoenflies
import DifferentialGeometry.Topology.SphereSeparation.StandardSphere
import DifferentialGeometry.Topology.SphereSeparation.Transport
import DifferentialGeometry.Topology.Manifold.BallDiffeomorphExtension

noncomputable section
open Set Metric Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_global_diffeomorph_of_smoothSchoenflies
    (hSch : smoothSchoenfliesThree) (e : sphere (0 : EuclideanThree) 1 → EuclideanThree)
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ D : Diffeomorph (𝓡 3) (𝓡 3) EuclideanThree EuclideanThree ∞,
      D '' sphere 0 1 = range e := by
  obtain ⟨φ, hφ, hφS⟩ := hSch e he
  obtain ⟨D, hD⟩ := DifferentialGeometry.Topology.Manifold.exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall
    φ zero_lt_one hφ
  exact ⟨D, ((hD.mono sphere_subset_closedBall).image_eq).trans hφS⟩

theorem exists_ball_sphereSides_of_smoothSchoenflies
    (hSch : smoothSchoenfliesThree) (e : sphere (0 : EuclideanThree) 1 → EuclideanThree)
    (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ (D : Diffeomorph (𝓡 3) (𝓡 3) EuclideanThree EuclideanThree ∞)
      (d : SphereSides (range e)),
      D '' sphere 0 1 = range e ∧ d.compactSide = D '' ball 0 1 ∧
      closure d.compactSide = D '' closedBall 0 1 := by
  obtain ⟨D, hDS⟩ := exists_global_diffeomorph_of_smoothSchoenflies hSch e he
  have hDB : closure (D '' ball 0 1) = D '' closedBall 0 1 := by
    change closure (D.toHomeomorph '' ball 0 1) = D.toHomeomorph '' closedBall 0 1
    rw [← D.toHomeomorph.image_closure, closure_ball 0 one_ne_zero]
  have hside : ∃ d : SphereSides (D '' sphere 0 1),
      d.compactSide = D '' ball 0 1 ∧ closure d.compactSide = D '' closedBall 0 1 :=
    ⟨standardUnitSphereSides.image D.toHomeomorph, rfl, hDB⟩
  rw [hDS] at hside
  obtain ⟨d, hd, hdc⟩ := hside
  exact ⟨D, d, hDS, hd, hdc⟩

end DifferentialGeometry.Topology.SphereSeparation
