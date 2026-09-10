import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped unitInterval
namespace Poincare.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (a : E) (r : ℝ) (p : E) (hp : p ∈ ball a r)

include hp in
private theorem sphereRadialFamily_nonzero (t : I) (v : sphere (0 : E) 1) :
    r • v.val - (t : ℝ) • (p-a) ≠ 0 := by
  intro hz
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hp
  have he := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_smul, Real.norm_of_nonneg hr.le, mem_sphere_zero_iff_norm.mp v.property, mul_one,
    norm_smul, Real.norm_of_nonneg t.property.1] at he
  have ht : (t : ℝ) * ‖p-a‖ ≤ ‖p-a‖ :=
    (mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)).trans_eq (one_mul _)
  have hn : ‖p-a‖ < r := by simpa only [mem_ball,dist_eq_norm] using hp
  linarith

private def sphereRadialFamily : C(I × sphere (0 : E) 1, sphere (0 : E) 1) :=
  ⟨fun q => (homeomorphUnitSphereProd E
      ⟨r • q.2.val - (q.1 : ℝ) • (p-a), sphereRadialFamily_nonzero a r p hp q.1 q.2⟩).1,
    (homeomorphUnitSphereProd E).continuous.fst.comp
      (((continuous_const.smul (continuous_subtype_val.comp continuous_snd)).sub
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)).subtype_mk _)⟩


def sphereRadialMap : C(sphere (0 : E) 1, sphere (0 : E) 1) :=
  (sphereRadialFamily a r p hp).curry 1


@[simp]
theorem sphereRadialMap_apply (v : sphere (0 : E) 1) :
    (sphereRadialMap a r p hp v : E) =
      ‖a+r • v.val-p‖⁻¹ • (a+r • v.val-p) := by
  have hh := homeomorphUnitSphereProd_apply_fst_coe E
    (⟨r • v.val - (1 : ℝ) • (p-a), sphereRadialFamily_nonzero a r p hp 1 v⟩ : ({0}ᶜ : Set E))
  have he : r • v.val - (1 : ℝ) • (p-a) = a+r • v.val-p := by rw [one_smul]; abel
  exact hh.trans (congrArg (fun z : E => ‖z‖⁻¹ • z) he)


def sphereRadialHomotopy : (ContinuousMap.id (sphere (0 : E) 1)).Homotopy
    (sphereRadialMap a r p hp) where
  toContinuousMap := sphereRadialFamily a r p hp
  map_zero_left v := by
    apply Subtype.ext
    have hr : 0 < r := lt_of_le_of_lt dist_nonneg hp
    have hh := homeomorphUnitSphereProd_apply_fst_coe E
      (⟨r • v.val - (0 : ℝ) • (p-a), sphereRadialFamily_nonzero a r p hp 0 v⟩ : ({0}ᶜ : Set E))
    change ((sphereRadialFamily a r p hp) (0,v) : E) = v.val
    apply hh.trans
    change ‖r • v.val - (0 : ℝ) • (p-a)‖⁻¹ • (r • v.val - (0 : ℝ) • (p-a)) = v.val
    rw [zero_smul,sub_zero,norm_smul,Real.norm_of_nonneg hr.le,
      mem_sphere_zero_iff_norm.mp v.property,mul_one,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  map_one_left _ := rfl


@[simp]
theorem sphereRadialHomotopy_apply (t : I) (v : sphere (0 : E) 1) :
    (sphereRadialHomotopy a r p hp (t,v) : E) =
      ‖r • v.val - (t : ℝ) • (p-a)‖⁻¹ • (r • v.val - (t : ℝ) • (p-a)) :=
  homeomorphUnitSphereProd_apply_fst_coe E _

end Poincare.Topology
