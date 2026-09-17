import DifferentialGeometry.Topology.PiecewiseLinear.StdConeLayers
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineCover

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

theorem inter_layer_subset_segment {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) :
    stdConeLayerLow σ' σ ∩ stdConeLayerHigh σ' σ ⊆
      segment ℝ ((0, σ') : ℝ × ℝ) ((σ, 0) : ℝ × ℝ) := by
  rintro ⟨x, y⟩ ⟨⟨h1, h2, h3, h4, h5⟩, -, -, -, -, h6⟩
  have hσ0 : (0 : ℝ) < σ := lt_trans hσ' hσ
  have hline : σ' * x + σ * y = σ' * σ := le_antisymm h5 h6
  have hx : x ≤ σ := by simp only at *; linarith
  refine ⟨1 - x / σ, x / σ, by
      rw [sub_nonneg, div_le_one hσ0]
      exact hx, by positivity, by ring, ?_⟩
  have hy : y = σ' * (σ - x) / σ := by
    field_simp at hline ⊢
    linarith
  rw [Prod.ext_iff]
  constructor
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    field_simp
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hy]
    field_simp
    ring

theorem eqOn_layerMaps {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (v₀ v₁ v₂ v₃ : F) :
    EqOn (layerLowMap σ' σ v₀ v₁ v₂) (layerHighMap σ' σ v₁ v₂ v₃)
      (stdConeLayerLow σ' σ ∩ stdConeLayerHigh σ' σ) :=
  fun _ hz => eqOn_of_affineMap_eq_of_mem_segment
    ((layerLowMap_vertex₁ hσ' hσ v₀ v₁ v₂).trans (layerHighMap_vertex₁ hσ' hσ v₁ v₂ v₃).symm)
    ((layerLowMap_vertex₂ hσ' hσ v₀ v₁ v₂).trans (layerHighMap_vertex₂ hσ' hσ v₁ v₂ v₃).symm)
    (inter_layer_subset_segment hσ' hσ hz)

end DifferentialGeometry.Topology.PiecewiseLinear
