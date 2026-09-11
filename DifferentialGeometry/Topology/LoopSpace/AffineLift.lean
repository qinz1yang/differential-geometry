import DifferentialGeometry.Topology.LoopSpace.PeriodicDescent
import DifferentialGeometry.Topology.LoopSpace.Lipschitz



noncomputable section

open Function
open scoped NNReal

namespace DifferentialGeometry.Topology


def affineCircleMap (f : ℝ → ℝ) (hc : Continuous f)
    (hp : ∀ t, f (t + 1) = f t + 1) : C(loopCircle, loopCircle) :=
  periodicLoop (fun t => (f t : loopCircle)) (by
    intro t
    change (f (t + 1) : loopCircle) = (f t : loopCircle)
    rw [hp, QuotientAddGroup.mk_add]
    simp only [AddCircle.coe_period, add_zero])
    ((AddCircle.continuous_mk' (1 : ℝ)).comp hc)

@[simp] theorem affineCircleMap_coe (f : ℝ → ℝ) (hc : Continuous f)
    (hp : ∀ t, f (t + 1) = f t + 1) (t : ℝ) :
    affineCircleMap f hc hp (t : loopCircle) = (f t : loopCircle) := rfl


theorem inverse_affinePeriodic (f : ℝ ≃ₜ ℝ) (hp : ∀ t, f (t + 1) = f t + 1) :
    ∀ t, f.symm (t + 1) = f.symm t + 1 := by
  intro t
  apply f.injective
  rw [f.apply_symm_apply, hp, f.apply_symm_apply]



def affineCircleHomeomorph (f : ℝ ≃ₜ ℝ) (hp : ∀ t, f (t + 1) = f t + 1) :
    loopCircle ≃ₜ loopCircle where
  toFun := affineCircleMap f f.continuous hp
  invFun := affineCircleMap f.symm f.symm.continuous (inverse_affinePeriodic f hp)
  left_inv := by
    intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    simp only [affineCircleMap_coe, f.symm_apply_apply]
  right_inv := by
    intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    simp only [affineCircleMap_coe, f.apply_symm_apply]
  continuous_toFun := (affineCircleMap f f.continuous hp).continuous
  continuous_invFun := (affineCircleMap f.symm f.symm.continuous (inverse_affinePeriodic f hp)).continuous


theorem affineCircleMap_lipschitz (f : ℝ → ℝ) (hc : Continuous f)
    (hp : ∀ t, f (t + 1) = f t + 1) {K : ℝ≥0} (hK : LipschitzWith K f) :
    LipschitzWith K (affineCircleMap f hc hp) := by
  apply loop_lipschitz_of_lift
  simpa only [one_mul, affineCircleMap_coe, Function.comp_def] using! loopCircle_projection_lipschitz.comp hK


theorem affineCircleHomeomorph_lipschitz (f : ℝ ≃ₜ ℝ)
    (hp : ∀ t, f (t + 1) = f t + 1) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : LipschitzWith L f.symm) :
    LipschitzWith K (affineCircleHomeomorph f hp) ∧
      LipschitzWith L (affineCircleHomeomorph f hp).symm :=
  ⟨affineCircleMap_lipschitz f f.continuous hp hK,
    affineCircleMap_lipschitz f.symm f.symm.continuous (inverse_affinePeriodic f hp) hL⟩

end DifferentialGeometry.Topology
