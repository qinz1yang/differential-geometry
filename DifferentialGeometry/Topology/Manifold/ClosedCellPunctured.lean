import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.ModelImmersion
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

variable (m : ℕ)
private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨by simp⟩
local notation "Sphere" => Metric.sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1
local notation "PI" => ModelWithCorners.prod (𝓡 m) (𝓡∂ 1)

private abbrev puncturedCell : TopologicalSpace.Opens (ClosedCell (m + 1)) :=
  ⟨{x | x.val ≠ 0}, isOpen_ne_fun continuous_subtype_val continuous_const⟩

private def halfScalar : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)

private theorem half_height_smooth : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
    (fun h : EuclideanHalfSpace 1 => h.val 0) :=
  halfScalar.contDiff.contMDiff.comp (𝓡∂ 1).contMDiff

private def radialPunctured (p : Sphere × EuclideanHalfSpace 1) : puncturedCell m :=
  ⟨⟨(1 + p.2.val 0)⁻¹ • p.1.val, by
    have hpos : 0 < 1 + p.2.val 0 := by linarith [p.2.property]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      norm_eq_of_mem_sphere, mul_one]
    exact (inv_le_one₀ hpos).mpr (by linarith [p.2.property])⟩,
    smul_ne_zero (inv_ne_zero (by linarith [p.2.property]))
      (ne_zero_of_mem_unit_sphere p.1)⟩

private theorem radialPunctured_norm (p : Sphere × EuclideanHalfSpace 1) :
    ‖(radialPunctured m p).val.val‖ = (1 + p.2.val 0)⁻¹ := by
  change ‖(1 + p.2.val 0)⁻¹ • p.1.val‖ = _
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by linarith [p.2.property])), norm_eq_of_mem_sphere, mul_one]

private def puncturedRadial (x : puncturedCell m) : Sphere × EuclideanHalfSpace 1 :=
  (⟨‖x.val.val‖⁻¹ • x.val.val, mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm x.property)⟩,
    ⟨halfScalar.symm (‖x.val.val‖⁻¹ - 1), by
      change 0 ≤ ‖x.val.val‖⁻¹ - 1
      exact sub_nonneg.mpr ((one_le_inv₀ (norm_pos_iff.mpr x.property)).mpr x.val.property)⟩)

private theorem radialPunctured_contMDiff :
    ContMDiff PI (𝓡∂ (m + 1)) ∞ (radialPunctured m) := by
  have hr : ContMDiff PI 𝓘(ℝ) ∞
      (fun p : Sphere × EuclideanHalfSpace 1 => (1 + p.2.val 0)⁻¹) :=
    (contMDiff_const.add (half_height_smooth.comp contMDiff_snd)).inv₀
      (fun p => by
        change (1 : ℝ) + p.2.val 0 ≠ 0
        linarith [p.2.property])
  have hcoord : ContMDiff PI (𝓡 (m + 1)) ∞
      (fun p : Sphere × EuclideanHalfSpace 1 => (radialPunctured m p).val.val) :=
    hr.smul (contMDiff_coe_sphere.comp contMDiff_fst)
  have hcell : ContMDiff PI (𝓡∂ (m + 1)) ∞
      (fun p : Sphere × EuclideanHalfSpace 1 => (radialPunctured m p).val) := by
    apply (ContMDiff.iff_comp_isImmersion
      (isSmoothEmbedding_closedCell_inclusion m).isImmersion).mpr
    exact ⟨hcoord.continuous.subtype_mk _, hcoord⟩
  exact (ContMDiff.subtypeVal_comp_iff (puncturedCell m) (radialPunctured m)).mp hcell

private theorem puncturedRadial_contMDiff :
    ContMDiff (𝓡∂ (m + 1)) PI ∞ (puncturedRadial m) := by
  have hc : ContMDiff (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (fun x : puncturedCell m => x.val.val) :=
    (isSmoothEmbedding_closedCell_inclusion m).contMDiff.comp contMDiff_subtype_val
  have hn : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ) ∞
      (fun x : puncturedCell m => ‖x.val.val‖) :=
    fun x => (contDiffAt_norm ℝ x.property).contMDiffAt.comp x (hc x)
  have hi := hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)
  have hs : ContMDiff (𝓡∂ (m + 1)) (𝓡 m) ∞
      (fun x : puncturedCell m => (puncturedRadial m x).1) :=
    (hi.smul hc).codRestrict_sphere _
  have ht : ContMDiff (𝓡∂ (m + 1)) (𝓡∂ 1) ∞
      (fun x : puncturedCell m => (puncturedRadial m x).2) := by
    have he : ContMDiff (𝓡∂ (m + 1)) (𝓡 1) ∞
        (fun x : puncturedCell m => (puncturedRadial m x).2.val) :=
      halfScalar.symm.contDiff.contMDiff.comp (hi.sub contMDiff_const)
    apply (ContMDiff.iff_comp_isImmersion ((𝓡∂ 1).isImmersion_coe ∞)).mpr
    exact ⟨he.continuous.subtype_mk _, he⟩
  exact hs.prodMk ht

def closedCellPuncturedDiffeomorph :
    (Sphere × EuclideanHalfSpace 1) ≃ₘ⟮PI, 𝓡∂ (m + 1)⟯ (⟨{x : ClosedCell (m + 1) | x.val ≠ 0},
      isOpen_ne_fun continuous_subtype_val continuous_const⟩ :
        TopologicalSpace.Opens (ClosedCell (m + 1))) where
  toFun := radialPunctured m
  invFun := puncturedRadial m
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ‖(radialPunctured m p).val.val‖⁻¹ • ((1 + p.2.val 0)⁻¹ • p.1.val) = p.1.val
      rw [radialPunctured_norm, inv_inv, smul_smul,
        mul_inv_cancel₀ (by linarith [p.2.property]), one_smul]
    · apply Subtype.ext
      apply halfScalar.injective
      change halfScalar (halfScalar.symm (‖(radialPunctured m p).val.val‖⁻¹ - 1)) = p.2.val 0
      rw [ContinuousLinearEquiv.apply_symm_apply, radialPunctured_norm, inv_inv]
      ring
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change (1 + (‖x.val.val‖⁻¹ - 1))⁻¹ • (‖x.val.val‖⁻¹ • x.val.val) = x.val.val
    rw [show (1 : ℝ) + (‖x.val.val‖⁻¹ - 1) = ‖x.val.val‖⁻¹ by ring, inv_inv,
      smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr x.property), one_smul]
  contMDiff_toFun := radialPunctured_contMDiff m
  contMDiff_invFun := puncturedRadial_contMDiff m

theorem closedCellPuncturedDiffeomorph_apply (p : Sphere × EuclideanHalfSpace 1) :
    (closedCellPuncturedDiffeomorph m p).val.val = (1 + p.2.val 0)⁻¹ • p.1.val := rfl

theorem closedCellPuncturedDiffeomorph_symm_apply (x : (⟨{x : ClosedCell (m + 1) | x.val ≠ 0},
      isOpen_ne_fun continuous_subtype_val continuous_const⟩ :
        TopologicalSpace.Opens (ClosedCell (m + 1)))) :
    ((closedCellPuncturedDiffeomorph m).symm x).2.val 0 = ‖x.val.val‖⁻¹ - 1 := rfl

theorem closedCellPuncturedDiffeomorph_norm (p : Sphere × EuclideanHalfSpace 1) :
    ‖(closedCellPuncturedDiffeomorph m p).val.val‖ = (1 + p.2.val 0)⁻¹ :=
  radialPunctured_norm m p

theorem closedCellPuncturedDiffeomorph_symm_apply_fst (x : (⟨{x : ClosedCell (m + 1) | x.val ≠ 0},
      isOpen_ne_fun continuous_subtype_val continuous_const⟩ :
        TopologicalSpace.Opens (ClosedCell (m + 1)))) :
    (((closedCellPuncturedDiffeomorph m).symm x).1).val =
      ‖x.val.val‖⁻¹ • x.val.val := rfl

theorem closedCellPuncturedDiffeomorph_boundary_iff (p : Sphere × EuclideanHalfSpace 1) :
    ‖(closedCellPuncturedDiffeomorph m p).val.val‖ = 1 ↔ p.2.val 0 = 0 := by
  rw [closedCellPuncturedDiffeomorph_norm, inv_eq_one]
  constructor <;> intro h <;> linarith

end DifferentialGeometry.Topology.Manifold
