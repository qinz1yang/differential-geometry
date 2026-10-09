import DifferentialGeometry.Analysis.InnerProductSpace.ProjectedGraphRank

set_option autoImplicit false

namespace ContinuousLinearMap

variable {E F H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem pruned_graph_range_surjective_of_approximation
    (K : H →L[ℝ] H) (Q : H →L[ℝ] F) (T : F →L[ℝ] H)
    (L : E →L[ℝ] F) (D : E →L[ℝ] H)
    (hK : ‖K‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hQT : Q.comp (K.comp T) = ContinuousLinearMap.id ℝ F)
    (hKD : K.comp D = D) {a e b l : ℝ}
    (ha : 0 < a) (he : e < a) (hl : ∀ z, a * ‖z‖ ≤ ‖L.adjoint z‖)
    (hT : ‖T‖ ≤ b) (hL : ‖L‖ ≤ l) (herror : ‖D - T.comp L‖ ≤ e) :
    let P := (K.comp T).range.orthogonalProjectionOnto.comp D
    Function.Surjective P ∧ ‖D - (K.comp T).range.subtypeL.comp P‖ ≤ e ∧
      ∀ v ∈ P.kerᗮ, (a - e) * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ (b * l + e) * ‖v‖ := by
  have hlower (z : F) : ‖z‖ ≤ ‖K (T z)‖ := by
    have hz : Q (K (T z)) = z := congrArg (fun A : F →L[ℝ] F => A z) hQT
    calc
      ‖z‖ = ‖Q (K (T z))‖ := congrArg norm hz.symm
      _ ≤ ‖Q‖ * ‖K (T z)‖ := Q.le_opNorm _
      _ ≤ ‖K (T z)‖ := mul_le_of_le_one_left (norm_nonneg _) hQ
  have hbound : ‖K.comp T‖ ≤ b :=
    ((opNorm_comp_le K T).trans (mul_le_of_le_one_left (norm_nonneg T) hK)).trans hT
  have herr : ‖D - (K.comp T).comp L‖ ≤ e := by
    have hid : D - (K.comp T).comp L = K.comp (D - T.comp L) := by
      rw [comp_sub, hKD, comp_assoc]
    rw [hid]
    exact ((opNorm_comp_le K _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hK)).trans herror
  exact projected_range_surjective_of_approximation (K.comp T) L D ha he hl hlower hbound hL herr

end ContinuousLinearMap
