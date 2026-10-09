import DifferentialGeometry.Topology.MetricSpace.FiniteDimensionalBallPacking
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false
noncomputable section

namespace Submodule

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι]

theorem card_le_of_near_subspace_separated_family
    (P : Submodule ℝ H) [FiniteDimensional ℝ P] (c : ι → H) (o : H)
    {R ε δ : ℝ} (hR : 0 ≤ R) (hgap : 2 * δ < ε)
    (hc : ∀ i, ‖c i - o‖ ≤ R)
    (hnormal : ∀ i, ‖c i - o - P.starProjection (c i - o)‖ ≤ δ)
    (hsep : ∀ i j, i ≠ j → ε ≤ dist (c i) (c j)) :
    (Fintype.card ι : ℝ) ≤ (1 + 2 * R / (ε - 2 * δ)) ^ Module.finrank ℝ P := by
  let f : ι → P := fun i => P.orthogonalProjectionOnto (c i - o)
  have hf (i : ι) : dist (f i) 0 ≤ R := by
    rw [dist_zero_right]
    exact (P.norm_orthogonalProjectionOnto_apply_le (c i - o)).trans (hc i)
  have hsepf (i j : ι) (hij : i ≠ j) : ε - 2 * δ ≤ dist (f i) (f j) := by
    have hsplit : c i - c j =
        (P.starProjection (c i - o) - P.starProjection (c j - o)) +
        ((c i - o - P.starProjection (c i - o)) -
          (c j - o - P.starProjection (c j - o))) := by abel
    have hn : ‖c i - c j‖ ≤
        ‖P.starProjection (c i - o) - P.starProjection (c j - o)‖ + 2 * δ := by
      calc
        _ = ‖(P.starProjection (c i - o) - P.starProjection (c j - o)) +
            ((c i - o - P.starProjection (c i - o)) -
              (c j - o - P.starProjection (c j - o)))‖ := congrArg norm hsplit
        _ ≤ ‖P.starProjection (c i - o) - P.starProjection (c j - o)‖ +
            ‖(c i - o - P.starProjection (c i - o)) -
              (c j - o - P.starProjection (c j - o))‖ := norm_add_le _ _
        _ ≤ ‖P.starProjection (c i - o) - P.starProjection (c j - o)‖ +
            (‖c i - o - P.starProjection (c i - o)‖ +
              ‖c j - o - P.starProjection (c j - o)‖) :=
          add_le_add le_rfl (norm_sub_le _ _)
        _ ≤ ‖P.starProjection (c i - o) - P.starProjection (c j - o)‖ + 2 * δ := by
          linarith [hnormal i, hnormal j]
    have hs := hsep i j hij
    rw [dist_eq_norm] at hs
    rw [dist_eq_norm]
    change ε - 2 * δ ≤ ‖P.starProjection (c i - o) - P.starProjection (c j - o)‖
    linarith
  exact Metric.card_le_of_separated_family_closedBall f 0 hR (sub_pos.mpr hgap) hf hsepf

end Submodule
