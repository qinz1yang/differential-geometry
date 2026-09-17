import DifferentialGeometry.Topology.PiecewiseLinear.LayerAffineMap
import DifferentialGeometry.Topology.PiecewiseLinear.Pasting

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem inner_edge_subset_low {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' ≤ σ) :
    {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 = σ'} ⊆ stdConeLayerLow σ' σ := by
  rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  refine ⟨h1, h2, le_of_eq h3.symm, by linarith, ?_⟩
  have : σ' * x + σ * y = σ' * σ' + (σ - σ') * y := by nlinarith
  rw [this]
  nlinarith

theorem outer_edge_subset_high {σ' σ : ℝ} (hσ' : 0 ≤ σ') (hσ : σ' ≤ σ) :
    {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 = σ} ⊆ stdConeLayerHigh σ' σ := by
  rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  refine ⟨h1, h2, by linarith, le_of_eq h3, ?_⟩
  have : σ' * x + σ * y = σ' * σ + (σ - σ') * y := by nlinarith
  rw [this]
  nlinarith

open Classical in
theorem exists_isPiecewiseAffineOn_layer {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (hσ1 : σ ≤ 1)
    (v₀ v₁ v₂ v₃ : F) :
    ∃ Ψ : ℝ × ℝ → F, IsPiecewiseAffineOn Ψ (stdConeLayer σ' σ) ∧
      EqOn Ψ (layerLowMap σ' σ v₀ v₁ v₂) (stdConeLayerLow σ' σ) ∧
      EqOn Ψ (layerHighMap σ' σ v₁ v₂ v₃) (stdConeLayerHigh σ' σ) := by
  classical
  set Ψ : ℝ × ℝ → F :=
    @Set.piecewise (ℝ × ℝ) (fun _ => F) (stdConeLayerLow σ' σ)
      (layerLowMap σ' σ v₀ v₁ v₂) (layerHighMap σ' σ v₁ v₂ v₃)
      (fun j => Classical.propDecidable _) with hΨdef
  have hmem : ∀ z ∈ stdConeLayerLow σ' σ, Ψ z = layerLowMap σ' σ v₀ v₁ v₂ z := by
    intro z hz
    rw [hΨdef]
    exact if_pos hz
  have hnot : ∀ z ∉ stdConeLayerLow σ' σ, Ψ z = layerHighMap σ' σ v₁ v₂ v₃ z := by
    intro z hz
    rw [hΨdef]
    exact if_neg hz
  refine ⟨Ψ, ?_, hmem, ?_⟩
  · rw [← stdConeLayer_union_split]
    exact (isPiecewiseAffineOn_of_affine_of_isHPolytope _
      (isHPolytope_stdConeLayerLow hσ1)).piecewise_of_isClosed
      (isPiecewiseAffineOn_of_affine_of_isHPolytope _ (isHPolytope_stdConeLayerHigh hσ1))
      (isHPolytope_stdConeLayerLow hσ1).isClosed (isHPolytope_stdConeLayerHigh hσ1).isClosed
      (eqOn_layerMaps hσ' hσ v₀ v₁ v₂ v₃)
  · intro z hz
    by_cases hzl : z ∈ stdConeLayerLow σ' σ
    · rw [hmem z hzl]
      exact eqOn_layerMaps hσ' hσ v₀ v₁ v₂ v₃ ⟨hzl, hz⟩
    · rw [hnot z hzl]

theorem mem_convexHull_triple {v₀ v₁ v₂ : F} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) : a • v₀ + b • v₁ + c • v₂ ∈ convexHull ℝ ({v₀, v₁, v₂} : Set F) := by
  have h0 : v₀ ∈ ({v₀, v₁, v₂} : Set F) := mem_insert _ _
  have h1 : v₁ ∈ ({v₀, v₁, v₂} : Set F) := mem_insert_of_mem _ (mem_insert _ _)
  have h2 : v₂ ∈ ({v₀, v₁, v₂} : Set F) := mem_insert_of_mem _ (mem_insert_of_mem _ rfl)
  have hsum : a • v₀ + b • v₁ + c • v₂ = ∑ i : Fin 3, ![a, b, c] i • ![v₀, v₁, v₂] i := by
    simp [Fin.sum_univ_three]
  rw [hsum]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => ?_) ?_ (fun i _ => ?_)
  · fin_cases i <;> assumption
  · rw [Fin.sum_univ_three]
    change a + b + c = (1 : ℝ)
    exact habc
  · fin_cases i
    · exact subset_convexHull ℝ _ h0
    · exact subset_convexHull ℝ _ h1
    · exact subset_convexHull ℝ _ h2

theorem layerLowMap_mem_convexHull {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (v₀ v₁ v₂ : F)
    {z : ℝ × ℝ} (hz : z ∈ stdConeLayerLow σ' σ) :
    layerLowMap σ' σ v₀ v₁ v₂ z ∈ convexHull ℝ ({v₀, v₁, v₂} : Set F) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hz
  have hd : (0 : ℝ) < σ - σ' := by linarith
  have hkey : 1 - z.2 / σ' - (z.1 + z.2 - σ') / (σ - σ')
      = (σ' * σ - (σ' * z.1 + σ * z.2)) / (σ' * (σ - σ')) := by
    field_simp
    ring
  rw [layerLowMap_eq_combo]
  refine mem_convexHull_triple ?_ (by positivity) (div_nonneg (by linarith) hd.le) ?_
  · rw [hkey]
    exact div_nonneg (by linarith) (by positivity)
  · field_simp
    ring

theorem layerHighMap_mem_convexHull {σ' σ : ℝ} (hσ' : 0 < σ') (hσ : σ' < σ) (v₁ v₂ v₃ : F)
    {z : ℝ × ℝ} (hz : z ∈ stdConeLayerHigh σ' σ) :
    layerHighMap σ' σ v₁ v₂ v₃ z ∈ convexHull ℝ ({v₁, v₂, v₃} : Set F) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hz
  have hσ0 : (0 : ℝ) < σ := lt_trans hσ' hσ
  have hd : (0 : ℝ) < σ - σ' := by linarith
  have hw₂ : (σ' * z.1 / σ + z.2 - σ') / (σ - σ')
      = (σ' * z.1 + σ * z.2 - σ' * σ) / (σ * (σ - σ')) := by
    field_simp
  have hw₀ : 1 - z.1 / σ - (σ' * z.1 / σ + z.2 - σ') / (σ - σ')
      = (σ - z.1 - z.2) / (σ - σ') := by
    field_simp
    ring
  rw [layerHighMap_eq_combo (ne_of_gt hσ0) (ne_of_gt hd)]
  refine mem_convexHull_triple ?_ (by positivity) ?_ ?_
  · rw [hw₀]
    exact div_nonneg (by linarith) hd.le
  · rw [hw₂]
    exact div_nonneg (by linarith) (by positivity)
  · field_simp
    ring

end DifferentialGeometry.Topology.PiecewiseLinear
