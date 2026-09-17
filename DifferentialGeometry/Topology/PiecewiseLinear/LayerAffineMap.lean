import DifferentialGeometry.Topology.PiecewiseLinear.StdConeLayers

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def coeffLin (p q : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  p • LinearMap.fst ℝ ℝ ℝ + q • LinearMap.snd ℝ ℝ ℝ

theorem coeffLin_apply (p q : ℝ) (z : ℝ × ℝ) : coeffLin p q z = p * z.1 + q * z.2 := by
  simp [coeffLin]

noncomputable def affineOfCoeffs (l₁ l₂ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (c w₁ w₂ : F) : (ℝ × ℝ) →ᵃ[ℝ] F :=
  AffineMap.const ℝ (ℝ × ℝ) c + (l₁.smulRight w₁ + l₂.smulRight w₂).toAffineMap

theorem affineOfCoeffs_apply (l₁ l₂ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (c w₁ w₂ : F) (z : ℝ × ℝ) :
    affineOfCoeffs l₁ l₂ c w₁ w₂ z = c + l₁ z • w₁ + l₂ z • w₂ := by
  simp [affineOfCoeffs, add_assoc]

noncomputable def layerLowMap (σ' σ : ℝ) (v₀ v₁ v₂ : F) : (ℝ × ℝ) →ᵃ[ℝ] F :=
  affineOfCoeffs (coeffLin 0 (1 / σ')) (coeffLin (1 / (σ - σ')) (1 / (σ - σ')))
    (v₀ - (σ' / (σ - σ')) • (v₂ - v₀)) (v₁ - v₀) (v₂ - v₀)

noncomputable def layerHighMap (σ' σ : ℝ) (v₁ v₂ v₃ : F) : (ℝ × ℝ) →ᵃ[ℝ] F :=
  affineOfCoeffs (coeffLin (1 / σ) 0) (coeffLin (σ' / (σ * (σ - σ'))) (1 / (σ - σ')))
    (v₁ - (σ' / (σ - σ')) • (v₃ - v₁)) (v₂ - v₁) (v₃ - v₁)

theorem layerLowMap_vertex₀ {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (v₀ v₁ v₂ : F) :
    layerLowMap σ' σ v₀ v₁ v₂ (σ', 0) = v₀ := by
  have hd : σ - σ' ≠ 0 := sub_ne_zero.mpr (ne_of_gt hσ)
  have hs' : σ' ≠ 0 := ne_of_gt hσ'
  have hs : σ ≠ 0 := ne_of_gt (lt_trans hσ' hσ)
  rw [layerLowMap, affineOfCoeffs_apply, coeffLin_apply, coeffLin_apply]
  match_scalars <;> field_simp <;> ring

theorem layerLowMap_vertex₁ {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (v₀ v₁ v₂ : F) :
    layerLowMap σ' σ v₀ v₁ v₂ (0, σ') = v₁ := by
  have hd : σ - σ' ≠ 0 := sub_ne_zero.mpr (ne_of_gt hσ)
  have hs' : σ' ≠ 0 := ne_of_gt hσ'
  have hs : σ ≠ 0 := ne_of_gt (lt_trans hσ' hσ)
  rw [layerLowMap, affineOfCoeffs_apply, coeffLin_apply, coeffLin_apply]
  match_scalars <;> field_simp <;> ring

theorem layerLowMap_vertex₂ {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (v₀ v₁ v₂ : F) :
    layerLowMap σ' σ v₀ v₁ v₂ (σ, 0) = v₂ := by
  have hd : σ - σ' ≠ 0 := sub_ne_zero.mpr (ne_of_gt hσ)
  have hs' : σ' ≠ 0 := ne_of_gt hσ'
  have hs : σ ≠ 0 := ne_of_gt (lt_trans hσ' hσ)
  rw [layerLowMap, affineOfCoeffs_apply, coeffLin_apply, coeffLin_apply]
  match_scalars <;> field_simp <;> ring

theorem layerHighMap_vertex₁ {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (v₁ v₂ v₃ : F) :
    layerHighMap σ' σ v₁ v₂ v₃ (0, σ') = v₁ := by
  have hd : σ - σ' ≠ 0 := sub_ne_zero.mpr (ne_of_gt hσ)
  have hs' : σ' ≠ 0 := ne_of_gt hσ'
  have hs : σ ≠ 0 := ne_of_gt (lt_trans hσ' hσ)
  rw [layerHighMap, affineOfCoeffs_apply, coeffLin_apply, coeffLin_apply]
  match_scalars <;> field_simp <;> ring

theorem layerHighMap_vertex₂ {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (v₁ v₂ v₃ : F) :
    layerHighMap σ' σ v₁ v₂ v₃ (σ, 0) = v₂ := by
  have hd : σ - σ' ≠ 0 := sub_ne_zero.mpr (ne_of_gt hσ)
  have hs' : σ' ≠ 0 := ne_of_gt hσ'
  have hs : σ ≠ 0 := ne_of_gt (lt_trans hσ' hσ)
  rw [layerHighMap, affineOfCoeffs_apply, coeffLin_apply, coeffLin_apply]
  match_scalars <;> field_simp <;> ring

theorem layerHighMap_vertex₃ {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (v₁ v₂ v₃ : F) :
    layerHighMap σ' σ v₁ v₂ v₃ (0, σ) = v₃ := by
  have hd : σ - σ' ≠ 0 := sub_ne_zero.mpr (ne_of_gt hσ)
  have hs' : σ' ≠ 0 := ne_of_gt hσ'
  have hs : σ ≠ 0 := ne_of_gt (lt_trans hσ' hσ)
  rw [layerHighMap, affineOfCoeffs_apply, coeffLin_apply, coeffLin_apply]
  match_scalars <;> field_simp <;> ring

end DifferentialGeometry.Topology.PiecewiseLinear
