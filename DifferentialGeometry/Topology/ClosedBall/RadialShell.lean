import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homotopy.Equiv

noncomputable section
open Set Metric

namespace DifferentialGeometry.Topology.ClosedBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev UnitShell (E : Type*) [NormedAddCommGroup E] (a : ℝ) :=
  {x : closedBall (0 : E) 1 // a < ‖(x : E)‖}

variable {a : ℝ}

omit [NormedSpace ℝ E] in
private theorem unitShell_norm_pos (ha : 0 ≤ a) (x : UnitShell E a) : 0 < ‖(x.val : E)‖ :=
  ha.trans_lt x.property

omit [NormedSpace ℝ E] in
private theorem unitShell_norm_le_one (x : UnitShell E a) : ‖(x.val : E)‖ ≤ 1 := by
  simpa only [mem_closedBall_zero_iff] using x.val.property

def unitShellRadialMap (ha : 0 ≤ a) : C(UnitShell E a, sphere (0 : E) 1) :=
  ⟨fun x => ⟨NormedSpace.normalize (x.val : E), mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize (norm_pos_iff.mp (unitShell_norm_pos ha x)))⟩, by
    apply Continuous.subtype_mk
    have hval : Continuous (fun x : UnitShell E a => (x.val : E)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (hval.norm.inv₀ (fun x => (unitShell_norm_pos ha x).ne')).smul hval⟩

@[simp] theorem unitShellRadialMap_apply (ha : 0 ≤ a) (x : UnitShell E a) :
    (unitShellRadialMap ha x : E) = ‖(x.val : E)‖⁻¹ • (x.val : E) := rfl

omit [NormedSpace ℝ E] in
def sphereToUnitShell (ha₁ : a < 1) : C(sphere (0 : E) 1, UnitShell E a) := by
  refine ⟨fun x => ⟨⟨x.val, sphere_subset_closedBall x.property⟩, ?_⟩, ?_⟩
  · change a < ‖x.val‖
    rw [mem_sphere_zero_iff_norm.mp x.property]
    exact ha₁
  · exact (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [NormedSpace ℝ E] in
@[simp] theorem sphereToUnitShell_apply (ha₁ : a < 1) (x : sphere (0 : E) 1) :
    ((sphereToUnitShell ha₁ x).val : E) = x.val := rfl

@[simp] theorem unitShellRadialMap_sphereToUnitShell (ha : 0 ≤ a) (ha₁ : a < 1) (x : sphere (0 : E) 1) :
    unitShellRadialMap ha (sphereToUnitShell ha₁ x) = x := by
  apply Subtype.ext
  change NormedSpace.normalize x.val = x.val
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp x.property)

private def unitShellRadialHomotopyPoint (ha : 0 ≤ a)
    (t : unitInterval) (x : UnitShell E a) : UnitShell E a := by
  let r := ‖(x.val : E)‖
  let k := (1 - (t : ℝ)) + (t : ℝ) * r⁻¹
  have hr : 0 < r := unitShell_norm_pos ha x
  have hrat : a < r := x.property
  have hr1 : r ≤ 1 := unitShell_norm_le_one x
  have ht0 : 0 ≤ (t : ℝ) := t.property.1
  have ht1 : (t : ℝ) ≤ 1 := t.property.2
  have hk : 0 ≤ k := add_nonneg (sub_nonneg.mpr ht1) (mul_nonneg ht0 (inv_nonneg.mpr hr.le))
  have hnorm : ‖k • (x.val : E)‖ = (1 - (t : ℝ)) * r + (t : ℝ) := by
    rw [norm_smul, Real.norm_of_nonneg hk]
    change k * r = _
    dsimp [k]
    rw [add_mul, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
  refine ⟨⟨k • (x.val : E), ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff, hnorm]
    nlinarith
  · change a < ‖k • (x.val : E)‖
    rw [hnorm]
    nlinarith

def unitShellRadialDeformation (ha : 0 ≤ a) (ha₁ : a < 1) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (UnitShell E a))
      ((sphereToUnitShell ha₁).comp (unitShellRadialMap ha))
      {x | ‖(x.val : E)‖ = 1} where
  toFun tx := unitShellRadialHomotopyPoint ha tx.1 tx.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hval : Continuous (fun p : unitInterval × UnitShell E a => (p.2.val : E)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    have ht : Continuous (fun p : unitInterval × UnitShell E a => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).add
      (ht.mul (hval.norm.inv₀ (fun p => (unitShell_norm_pos ha p.2).ne')))).smul hval
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (0 : ℝ)) + 0 * ‖(x.val : E)‖⁻¹) • (x.val : E) = x.val
    simp
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (1 : ℝ)) + 1 * ‖(x.val : E)‖⁻¹) • (x.val : E) =
      ‖(x.val : E)‖⁻¹ • (x.val : E)
    simp
  prop' t x hx := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (t : ℝ)) + (t : ℝ) * ‖(x.val : E)‖⁻¹) • (x.val : E) = x.val
    change ‖(x.val : E)‖ = 1 at hx
    rw [hx, inv_one, mul_one, sub_add_cancel, one_smul]

@[simp] theorem unitShellRadialDeformation_apply (ha : 0 ≤ a) (ha₁ : a < 1)
    (t : unitInterval) (x : UnitShell E a) :
    ((unitShellRadialDeformation ha ha₁ (t, x)).val : E) =
      ((1 - (t : ℝ)) + (t : ℝ) * ‖(x.val : E)‖⁻¹) • (x.val : E) := rfl

def unitShellRadialHomotopyEquiv (ha : 0 ≤ a) (ha₁ : a < 1) :
    ContinuousMap.HomotopyEquiv (UnitShell E a) (sphere (0 : E) 1) where
  toFun := unitShellRadialMap ha
  invFun := sphereToUnitShell ha₁
  left_inv := ⟨(unitShellRadialDeformation ha ha₁).toHomotopy.symm⟩
  right_inv := by
    have he : (unitShellRadialMap (E := E) ha).comp (sphereToUnitShell ha₁) =
        ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro x
      exact unitShellRadialMap_sphereToUnitShell ha ha₁ x
    rw [he]

end DifferentialGeometry.Topology.ClosedBall
