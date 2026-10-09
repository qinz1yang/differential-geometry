import DifferentialGeometry.Topology.SphereSeparation.HeightNormalForm

open Set Manifold Metric
open scoped Manifold ContDiff
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_global_height_preserving_extremum_normal_form {e : SphereTwo → EuclideanThree}
    (he : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanThree) ∞ e)
    {p : SphereTwo}
    (hnd : IsNondegenerateCriticalPointAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (fun x => e x 2) p)
    (hindex : sigNeg (chartHessianAt
      (fun y => e ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p).symm y) 2)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p p)) ∈ ({0, 2} : Set ℕ)) :
    ∃ α : ℝ, (α = 1 ∨ α = -1) ∧ ∃ R : ℝ, 0 < R ∧
      ∃ χ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞,
        ∃ Φ : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
          χ.source = ball 0 R ∧ χ 0 = p ∧ (∀ z, Φ z 2 = z 2) ∧
          ∀ y ∈ χ.source,
            e (χ y) 2 = e p 2 + α / 2 * ‖y‖ ^ 2 ∧
            Φ ((EuclideanSpace.equivProdLast 2).symm (y, e p 2 + α / 2 * ‖y‖ ^ 2)) = e (χ y) := by
  have hmodel : ∃ k : ℕ, ∃ hk : k ≤ 2, ∃ α : ℝ, (α = 1 ∨ α = -1) ∧
      sigNeg (chartHessianAt
        (fun y => e ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p).symm y) 2)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) p p)) = k ∧
      ∀ y : EuclideanSpace ℝ (Fin 2),
        morseNormalForm hk (e p 2) (EuclideanSpace.equiv (Fin 2) ℝ y) =
          e p 2 + α / 2 * ‖y‖ ^ 2 := by
    rcases hindex with hzero | htwo
    · refine ⟨0, Nat.zero_le 2, 1, Or.inl rfl, hzero, ?_⟩
      intro y
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [morseNormalForm, posIdx, negIdx, Fin.sum_univ_two]
    · refine ⟨2, le_rfl, -1, Or.inr rfl, htwo, ?_⟩
      intro y
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [morseNormalForm, posIdx, negIdx, Fin.sum_univ_two]
      ring
  obtain ⟨k, hk, α, hα, hindex', hquad⟩ := hmodel
  obtain ⟨R, hR, χ, Φ, hRs, hχ0, hheight, hnormal⟩ :=
    exists_global_height_preserving_normal_form he k hk hnd hindex'
  let χ' := DifferentialGeometry.Topology.PartialDiffeomorph.restrict χ (ball 0 R) isOpen_ball
  have hsource : χ'.source = ball 0 R := inter_eq_right.mpr (ball_subset_closedBall.trans hRs)
  refine ⟨α, hα, R, hR, χ', Φ, hsource, hχ0, hheight, ?_⟩
  intro y hy
  have hn : Φ ((EuclideanSpace.equivProdLast 2).symm (y, e p 2 + α / 2 * ‖y‖ ^ 2)) = e (χ' y) := by
    change Φ ((EuclideanSpace.equivProdLast 2).symm (y, e p 2 + α / 2 * ‖y‖ ^ 2)) = e (χ y)
    simpa only [hquad] using hnormal y (ball_subset_closedBall (hsource ▸ hy))
  refine ⟨?_, hn⟩
  rw [← hn, hheight]
  exact EuclideanSpace.equivProdLast_symm_last (n := 2) _

end DifferentialGeometry.Topology.SphereSeparation
