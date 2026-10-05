import DifferentialGeometry.Geometry.Collapse.EdgeModelFibreDisk
import DifferentialGeometry.Topology.Handle.Embedding

/-!
# Consumer: the flat edge model fibre is a closed disk

On the flat plane `Z = E2` with `z₀ = 0` and `h(z) = 4‖z‖²` (smooth everywhere, `dh(z)(z) = 8‖z‖²`), the
standard inclusion of `ClosedCell 2` is a smooth embedding onto `{r < 9, h ≤ 4}`. The I6 assembly
`edgeModelCylinder_fibre_closedCell` then gives: the model fibre `{t = 0, Δ h ≤ 4Δ}` in the cylinder
`(-6Δ, 6Δ) × B(0, 9) ⊆ ℝ × E2` is diffeomorphic (hence homeomorphic) to `ClosedCell 2`, compact and
connected (`flatEdgeModel_fibre_closedCell`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Manifold.RegularLevel DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

/-- The differential of the flat height `4‖·‖²` evaluated on the position vector. -/
theorem flatEdgeHeight_mvfderiv_self (z : E2) :
    mvfderiv (𝓡 2) (fun y : E2 => 4 * ‖y‖ ^ 2) z z = 8 * ‖z‖ ^ 2 := by
  have hd : HasFDerivAt (fun y : E2 => 4 * ‖y‖ ^ 2) ((4 : ℝ) • (2 • innerSL ℝ z)) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul 4
  rw [mvfderiv_eq_fderiv, hd.fderiv]
  change (4 : ℝ) * (2 • innerSL ℝ z z) = 8 * ‖z‖ ^ 2
  rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, two_smul]
  ring

/-- **Concrete consumer.** The flat edge model fibre `{t = 0, 4Δ‖z‖² ≤ 4Δ}` in the cylinder
`(-6Δ, 6Δ) × B(0, 9)` is homeomorphic to `ClosedCell 2` (through the smooth diffeomorphism of the
I6 assembly), compact and connected. -/
theorem flatEdgeModel_fibre_closedCell {Δ : ℝ} (hΔ : 0 < Δ) :
    Nonempty (ClosedCell 2 ≃ₜ {x : edgeModelCylinder (0 : E2) Δ //
        (((x : ℝ × E2).1, Δ * (4 * ‖(x : ℝ × E2).2‖ ^ 2)) : ℝ × ℝ).1 = 0 ∧
        0 ≤ 4 * Δ - (((x : ℝ × E2).1, Δ * (4 * ‖(x : ℝ × E2).2‖ ^ 2)) : ℝ × ℝ).2}) ∧
    CompactSpace {x : edgeModelCylinder (0 : E2) Δ //
        (((x : ℝ × E2).1, Δ * (4 * ‖(x : ℝ × E2).2‖ ^ 2)) : ℝ × ℝ).1 = 0 ∧
        0 ≤ 4 * Δ - (((x : ℝ × E2).1, Δ * (4 * ‖(x : ℝ × E2).2‖ ^ 2)) : ℝ × ℝ).2} ∧
    ConnectedSpace {x : edgeModelCylinder (0 : E2) Δ //
        (((x : ℝ × E2).1, Δ * (4 * ‖(x : ℝ × E2).2‖ ^ 2)) : ℝ × ℝ).1 = 0 ∧
        0 ≤ 4 * Δ - (((x : ℝ × E2).1, Δ * (4 * ‖(x : ℝ × E2).2‖ ^ 2)) : ℝ × ℝ).2} := by
  have hh : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun y : E2 => 4 * ‖y‖ ^ 2) univ :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).contMDiff.contMDiffOn
  have h4 : ∀ x : E2, dist x 0 < 9 → 4 * ‖x‖ ^ 2 = 4 →
      mvfderiv (𝓡 2) (fun y : E2 => 4 * ‖y‖ ^ 2) x ≠ 0 := by
    intro x _ hx hzero
    have h8 := flatEdgeHeight_mvfderiv_self x
    rw [hzero] at h8
    change (0 : ℝ) = 8 * ‖x‖ ^ 2 at h8
    nlinarith
  have hb : IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (Subtype.val : ClosedCell 2 → E2) :=
    Handle.closedCellInclusion_isSmoothEmbedding (m := 1)
  have hrange : range (Subtype.val : ClosedCell 2 → E2) =
      {x | dist x (0 : E2) < 9 ∧ 4 * ‖x‖ ^ 2 ≤ 4} := by
    rw [Subtype.range_coe_subtype]
    ext x
    simp only [mem_ofPred_eq, dist_zero_right]
    constructor
    · intro hx
      refine ⟨by linarith, ?_⟩
      nlinarith [norm_nonneg x]
    · rintro ⟨-, hx⟩
      nlinarith [norm_nonneg x]
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo
    (edgeModelCylinder_contMDiff_time (𝓡 2) (0 : E2) Δ (fun y : E2 => 4 * ‖y‖ ^ 2))
    (edgeModelCylinder_contMDiff_height isOpen_univ (subset_univ _) hh Δ (4 * Δ))
    (edgeModelCylinder_regular (𝓡 2) (0 : E2) Δ (4 * Δ) (fun y : E2 => 4 * ‖y‖ ^ 2))
    (edgeModelCylinder_regular_boundary isOpen_univ (subset_univ _) hh h4 hΔ)
  obtain ⟨⟨φ⟩, hc, hconn, -⟩ := edgeModelCylinder_fibre_closedCell finrank_real_prod_euclideanTwo
    isOpen_univ (subset_univ _) hh h4 hb hrange hΔ
  exact ⟨⟨φ.toHomeomorph⟩, hc, hconn⟩

end DifferentialGeometry.Geometry.Collapse
