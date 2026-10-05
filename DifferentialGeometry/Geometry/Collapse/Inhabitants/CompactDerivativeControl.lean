import DifferentialGeometry.Geometry.Collapse.CompactBounds

/-!
A fixed compact smooth metric has curvature derivative control at every positive volume threshold.
Both the global derivative bound and the radius bound for the actual volume tests are constructed
from the same metric; the resulting control function is not asserted uniform in varying metrics.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem exists_compact_curvatureDerivativeControl (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧ curvatureDerivativesControlled g K A w₀ := by
  obtain ⟨R, _hRpos, hR⟩ := exists_radius_bound_of_volume_lower W g w₀ hw₀
  obtain ⟨B, hB, hderiv⟩ := exists_bound_curvatureDerivativeNorm_of_compactSpace g K
  let C := B * (max 1 R) ^ (K + 2) + 1
  have hC : 0 < C := by
    have hn : 0 ≤ B * (max 1 R) ^ (K + 2) :=
      mul_nonneg hB (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
    dsimp [C]
    linarith
  refine ⟨fun _w => C, fun _w => hC, ?_⟩
  intro p w r hw _hwc hr _hrR hv k hk q _hq
  have hv₀ : ENNReal.ofReal (w₀ * r ^ 3) ≤ ballVolume g p r :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hw (pow_nonneg hr.le 3))).trans hv
  have hrR : r ≤ max 1 R := (hR p r hr hv₀).trans (le_max_right _ _)
  have hp : r ^ (k + 2) ≤ (max 1 R) ^ (K + 2) :=
    (pow_le_pow_left₀ hr.le hrR _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  refine (hderiv k hk q).trans ?_
  change B ≤ C * (r ^ (k + 2))⁻¹
  rw [le_mul_inv_iff₀ (pow_pos hr _)]
  have hb := mul_le_mul_of_nonneg_left hp hB
  dsimp [C]
  linarith

end DifferentialGeometry.Geometry.Collapse
