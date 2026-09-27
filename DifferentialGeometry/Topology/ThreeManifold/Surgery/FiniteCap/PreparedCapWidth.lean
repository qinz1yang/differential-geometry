import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CutCoreCollar

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

def preparedCapWidth (c δ : ℝ) : ℝ := (c * δ)⁻¹ / 2

theorem preparedCapWidth_bounds (c δ : ℝ) (hc : 4 ≤ c) (hδ : 0 < δ) :
    0 < preparedCapWidth c δ ∧ preparedCapWidth c δ ≤ cuttingCollarWidth δ ∧
      preparedCapWidth c δ < (c * δ)⁻¹ := by
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hp : 0 < (c * δ)⁻¹ := inv_pos.mpr (mul_pos hcpos hδ)
  have hinv : (c * δ)⁻¹ ≤ δ⁻¹ := by
    apply (inv_le_inv₀ (mul_pos hcpos hδ) hδ).mpr
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ c from le_trans (by norm_num) hc) hδ.le
    simpa only [one_mul] using h
  change 0 < (c * δ)⁻¹ / 2 ∧ (c * δ)⁻¹ / 2 ≤ δ⁻¹ / 2 ∧ (c * δ)⁻¹ / 2 < (c * δ)⁻¹
  exact ⟨div_pos hp (by norm_num), div_le_div_of_nonneg_right hinv (by norm_num), by linarith⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
