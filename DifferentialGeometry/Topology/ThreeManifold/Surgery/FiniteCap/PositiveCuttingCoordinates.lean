import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev PositiveE3 := EuclideanSpace ℝ (Fin 3)
private abbrev PositiveS2 := Metric.sphere (0 : PositiveE3) 1
private abbrev PositiveIC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ PositiveE3 = 2 + 1) := ⟨by simp⟩

def positiveCuttingCylinder (r : ℝ) : Opens (PositiveS2 × ℝ) :=
  ⟨{q | 0 < q.2 ∧ q.2 < r}, isOpen_Ioo.preimage continuous_snd⟩

def positiveCuttingAnnulus (L r : ℝ) : Opens PositiveE3 :=
  ⟨{x | L < ‖x‖ ∧ ‖x‖ < L + r},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

private theorem radial_norm {L r : ℝ} (hL : 0 < L) (q : positiveCuttingCylinder r) :
    ‖(L + q.val.2) • q.val.1.val‖ = L + q.val.2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos hL q.property.1),
    mem_sphere_zero_iff_norm.mp q.val.1.property, mul_one]
private def positiveRadial {L : ℝ} (hL : 0 < L) (r : ℝ) :
    positiveCuttingCylinder r → positiveCuttingAnnulus L r :=
  fun q => ⟨(L + q.val.2) • q.val.1.val, by
    change L < ‖(L + q.val.2) • q.val.1.val‖ ∧ ‖(L + q.val.2) • q.val.1.val‖ < L + r
    rw [radial_norm hL]
    exact ⟨lt_add_of_pos_right L q.property.1, (add_lt_add_iff_left L).mpr q.property.2⟩⟩
private theorem point_ne_zero {L r : ℝ} (hL : 0 < L) (x : positiveCuttingAnnulus L r) : x.val ≠ 0 :=
  norm_pos_iff.mp (hL.trans x.property.1)
private def positiveRadialBack {L : ℝ} (hL : 0 < L) (r : ℝ) :
    positiveCuttingAnnulus L r → positiveCuttingCylinder r :=
  fun x => ⟨((homeomorphUnitSphereProd PositiveE3 ⟨x.val, point_ne_zero hL x⟩).1, ‖x.val‖ - L),
    by change 0 < ‖x.val‖ - L ∧ ‖x.val‖ - L < r; constructor <;> linarith [x.property.1, x.property.2]⟩
private theorem back_direction {L : ℝ} (hL : 0 < L) (r : ℝ) (x : positiveCuttingAnnulus L r) :
    (positiveRadialBack hL r x).val.1.val = ‖x.val‖⁻¹ • x.val :=
  homeomorphUnitSphereProd_apply_fst_coe PositiveE3 _
private theorem positiveRadial_left {L : ℝ} (hL : 0 < L) (r : ℝ) (q : positiveCuttingCylinder r) :
    positiveRadialBack hL r (positiveRadial hL r q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rw [back_direction]
    change ‖(L + q.val.2) • q.val.1.val‖⁻¹ • ((L + q.val.2) • q.val.1.val) = q.val.1.val
    rw [radial_norm hL, smul_smul, inv_mul_cancel₀ (add_pos hL q.property.1).ne', one_smul]
  · change ‖(L + q.val.2) • q.val.1.val‖ - L = q.val.2
    rw [radial_norm hL]
    ring
private theorem positiveRadial_right {L : ℝ} (hL : 0 < L) (r : ℝ) (x : positiveCuttingAnnulus L r) :
    positiveRadial hL r (positiveRadialBack hL r x) = x := by
  apply Subtype.ext
  change (L + (‖x.val‖ - L)) • (positiveRadialBack hL r x).val.1.val = x.val
  rw [back_direction, show L + (‖x.val‖ - L) = ‖x.val‖ by ring,
    smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (point_ne_zero hL x)), one_smul]
private theorem positiveRadial_smooth {L : ℝ} (hL : 0 < L) (r : ℝ) :
    ContMDiff PositiveIC (𝓡 3) ∞ (positiveRadial hL r) := by
  apply (ContMDiff.subtypeVal_comp_iff (positiveCuttingAnnulus L r) (positiveRadial hL r)).mp
  have hv := contMDiff_subtype_val (I := PositiveIC) (n := ∞) (U := positiveCuttingCylinder r)
  exact (contMDiff_const.add (contMDiff_snd.comp hv)).smul
    ((contMDiff_coe_sphere (n := 2)).comp (contMDiff_fst.comp hv))
private theorem positiveRadialBack_smooth {L : ℝ} (hL : 0 < L) (r : ℝ) :
    ContMDiff (𝓡 3) PositiveIC ∞ (positiveRadialBack hL r) := by
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (fun x : positiveCuttingAnnulus L r => ‖x.val‖) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := positiveCuttingAnnulus L r)).mpr
    exact (contDiffAt_norm ℝ (point_ne_zero hL x)).contMDiffAt
  have hv : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : positiveCuttingAnnulus L r => (positiveRadialBack hL r x).val.1.val) := by
    simp_rw [back_direction]
    exact (hn.inv₀ (fun x => norm_ne_zero_iff.mpr (point_ne_zero hL x))).smul
      (contMDiff_subtype_val (U := positiveCuttingAnnulus L r))
  have hy : ContMDiff (𝓡 3) (𝓡 2) ∞ (fun x : positiveCuttingAnnulus L r => (positiveRadialBack hL r x).val.1) :=
    ContMDiff.codRestrict_sphere hv (fun x => (positiveRadialBack hL r x).val.1.property)
  apply (ContMDiff.subtypeVal_comp_iff (positiveCuttingCylinder r) (positiveRadialBack hL r)).mp
  exact hy.prodMk (hn.sub contMDiff_const)

def positiveCuttingDiffeomorph {L : ℝ} (hL : 0 < L) (r : ℝ) :
    positiveCuttingCylinder r ≃ₘ⟮PositiveIC, 𝓡 3⟯ positiveCuttingAnnulus L r where
  toEquiv :=
    { toFun := positiveRadial hL r
      invFun := positiveRadialBack hL r
      left_inv := positiveRadial_left hL r
      right_inv := positiveRadial_right hL r }
  contMDiff_toFun := positiveRadial_smooth hL r
  contMDiff_invFun := positiveRadialBack_smooth hL r

theorem positiveCuttingDiffeomorph_apply {L : ℝ} (hL : 0 < L) (r : ℝ) (q : positiveCuttingCylinder r) :
    (positiveCuttingDiffeomorph hL r q).val = (L + q.val.2) • q.val.1.val := rfl

theorem positiveCuttingDiffeomorph_symm_direction {L : ℝ} (hL : 0 < L) (r : ℝ) (x : positiveCuttingAnnulus L r) :
    ((positiveCuttingDiffeomorph hL r).symm x).val.1.val = ‖x.val‖⁻¹ • x.val := back_direction hL r x

theorem positiveCuttingDiffeomorph_symm_height {L : ℝ} (hL : 0 < L) (r : ℝ) (x : positiveCuttingAnnulus L r) :
    ((positiveCuttingDiffeomorph hL r).symm x).val.2 = ‖x.val‖ - L := rfl
end DifferentialGeometry.Topology.ThreeManifold.Surgery
