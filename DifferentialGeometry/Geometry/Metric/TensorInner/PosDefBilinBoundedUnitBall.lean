import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity

namespace DifferentialGeometry.Tensor.Tensor0SRiemannian

lemma posDef_bilin_unit_ball_isBounded
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hPD : ∀ v : F, v ≠ 0 → 0 < B v v) :
    Bornology.IsBounded {v : F | B v v < 1} :=
  ((B.isCoercive_of_posDef hPD).isBounded_le 1).subset (by
    intro v hv
    exact show B v v ≤ 1 from le_of_lt hv)

end DifferentialGeometry.Tensor.Tensor0SRiemannian
