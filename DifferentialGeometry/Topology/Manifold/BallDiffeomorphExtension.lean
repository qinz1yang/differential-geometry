import DifferentialGeometry.Topology.Manifold.EmbeddedBallStraightening

noncomputable section
open Set Metric Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_diffeomorph_eqOn_of_partialDiffeomorph_closedBall
    (φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r : ℝ} (hr : 0 < r) (hrs : closedBall (0 : E) r ⊆ φ.source) :
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, EqOn D φ (closedBall 0 r) := by
  obtain ⟨A, ε, F, _, hε, _, hformula, _⟩ :=
    exists_diffeomorph_straightening_embedded_closedBall φ hr hrs isOpen_univ (subset_univ _)
  let B : E ≃L[ℝ] E := (Units.mk0 ε hε.ne') • A
  let T := DifferentialGeometry.Topology.translateDiffeomorph (φ 0)
  let D := (B.toDiffeomorph.trans T).trans F.symm
  refine ⟨D, ?_⟩
  intro x hx
  change F.symm (ε • A x + φ 0) = φ x
  rw [← hformula x hx, F.symm_apply_apply]

end DifferentialGeometry.Topology.Manifold
