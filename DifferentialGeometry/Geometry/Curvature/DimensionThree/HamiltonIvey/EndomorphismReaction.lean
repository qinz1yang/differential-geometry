import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionAlgebra

noncomputable section
open scoped BigOperators InnerProductSpace
namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem hamilton_ivey_reaction_inner_ge_at_logarithmic_boundary
    (hdim : Module.finrank ℝ V = 3) (A : V →L[ℝ] V)
    (hA : A.toLinearMap.IsSymmetric) {v : V} {c : ℝ}
    (hunit : ‖v‖ = 1)
    (heigen : A v = (hA.eigenvalues hdim 2) • v)
    (hneg : (hA.eigenvalues hdim 2) < 0)
    (hboundary : LinearMap.trace ℝ V A.toLinearMap =
      (-(hA.eigenvalues hdim 2)) * (c - 1)) :
    (hA.eigenvalues hdim 2) ^ 2 ≤
      LinearMap.trace ℝ V (curvatureOperatorReactionEndomorphism3 A.toLinearMap) +
        c * inner ℝ (curvatureOperatorReactionEndomorphism3 A.toLinearMap v) v := by
  have h21 : hA.eigenvalues hdim 1 ≤ hA.eigenvalues hdim 0 :=
    hA.eigenvalues_antitone hdim (by decide : (0 : Fin 3) ≤ 1)
  have h32 : hA.eigenvalues hdim 2 ≤ hA.eigenvalues hdim 1 :=
    hA.eigenvalues_antitone hdim (by decide : (1 : Fin 3) ≤ 2)
  have hb : sectionalSum3 (hA.eigenvalues hdim 0) (hA.eigenvalues hdim 1)
      (hA.eigenvalues hdim 2) = (-hA.eigenvalues hdim 2) * (c - 1) := by
    rw [hA.trace_eq_sum_eigenvalues hdim] at hboundary
    simpa only [Fin.sum_univ_three, sectionalSum3, RCLike.ofReal_real_eq_id, id_eq] using hboundary
  have hcore := hamilton_ivey_reaction_ge_at_logarithmic_boundary h21 h32 hneg hb
  rw [trace_curvatureOperatorReactionEndomorphism3_eq_eigenvalues hdim A.toLinearMap hA,
    curvatureOperatorReactionEndomorphism3_apply_of_eigenvalues_last hdim A.toLinearMap hA heigen]
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hunit, one_pow, mul_one]
  dsimp only [reactionSectionalSum3, reactionPinchHeight3,
    DifferentialGeometry.Dim3Reaction.sectionalReaction12,
    DifferentialGeometry.Dim3Reaction.sectionalReaction13,
    DifferentialGeometry.Dim3Reaction.sectionalReaction23] at hcore
  nlinarith only [hcore]

end DifferentialGeometry.Geometry.Curvature.DimensionThree
