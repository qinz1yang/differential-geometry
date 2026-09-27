import DifferentialGeometry.Geometry.Connection.Trivial
import DifferentialGeometry.Geometry.Connection.AlongCurve

noncomputable section

open scoped Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem connectionForm_trivial (x : M) :
    (trivial I M F).connectionForm (trivializationAt F (Bundle.Trivial M F) x) x = 0 := by
  ext X v
  rw [connectionForm_apply _ _ (mem_baseSet_trivializationAt F (Bundle.Trivial M F) x)]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.symmL_trivialization,
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply,
    trivial_apply, mvfderiv_const, zero_apply]

theorem derivAlongWithin_trivial (γ : ℝ → M) (Z : ℝ → F) (J : Set ℝ) (t : ℝ) :
    (trivial I M F).derivAlongWithin γ Z J t = derivWithin Z J t := by
  dsimp only [derivAlongWithin]
  rw [connectionForm_trivial]
  simp only [zero_apply, add_zero,
    Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.symmL_trivialization,
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]

end CovariantDerivative
