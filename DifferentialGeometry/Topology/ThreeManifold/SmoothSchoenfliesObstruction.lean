import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

theorem not_nonempty_linearIsometryEquiv_of_finrank_ne {m n : ℕ} (hmn : m ≠ n) :
    ¬ Nonempty (EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) := by
  rintro ⟨L⟩
  have h := LinearEquiv.finrank_eq L.toLinearEquiv
  rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h
  exact hmn h

theorem not_nonempty_linearIsometryEquiv_euclideanThree_complex :
    ¬ Nonempty (ℝ³ ≃ₗᵢ[ℝ] ℂ) := by
  rintro ⟨L⟩
  have h := LinearEquiv.finrank_eq L.toLinearEquiv
  rw [finrank_euclideanSpace_fin, Complex.finrank_real_complex] at h
  exact absurd h (by norm_num)

theorem not_nonempty_linearIsometry_euclideanThree_complex :
    ¬ Nonempty (ℝ³ →ₗᵢ[ℝ] ℂ) := by
  rintro ⟨L⟩
  have h := LinearMap.finrank_le_finrank_of_injective L.injective
  rw [finrank_euclideanSpace_fin, Complex.finrank_real_complex] at h
  exact absurd h (by norm_num)

theorem not_nonempty_linearIsometry_euclideanThree_euclideanTwo :
    ¬ Nonempty (ℝ³ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) := by
  rintro ⟨L⟩
  have h := LinearMap.finrank_le_finrank_of_injective L.injective
  rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h
  exact absurd h (by norm_num)

theorem isEmbedding_homeomorph_comp_subtype (F : ℝ³ ≃ₜ ℝ³) :
    Topology.IsEmbedding ((F : ℝ³ → ℝ³) ∘ (Subtype.val : S² → ℝ³)) :=
  F.isEmbedding.comp Topology.IsEmbedding.subtypeVal

theorem exists_homeomorph_image_sphere_eq_range_homeomorph_comp_subtype (F : ℝ³ ≃ₜ ℝ³) :
    ∃ G : ℝ³ ≃ₜ ℝ³,
      G '' S² = Set.range ((F : ℝ³ → ℝ³) ∘ (Subtype.val : S² → ℝ³)) := by
  refine ⟨F, ?_⟩
  rw [Set.range_comp, Subtype.range_coe]

end DifferentialGeometry.Topology.ThreeManifold
