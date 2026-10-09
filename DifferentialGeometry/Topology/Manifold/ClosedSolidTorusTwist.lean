import DifferentialGeometry.Topology.Manifold.ClosedSolidTorusAction

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

private theorem twist_contMDiff (k : ℤ) :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) ((𝓡∂ 2).prod (𝓡 1)) ∞
      (fun x : ClosedCell 2 × Circle => (closedDiskRotation (x.2 ^ k) x.1, x.2)) :=
  (closedDiskRotation_contMDiff.comp
    (((contMDiff_fst.comp (Circle.slopeMap_contMDiff ![k, 0])).comp
      contMDiff_snd).prodMk contMDiff_fst)).prodMk contMDiff_snd

def closedSolidTorusTwist (k : ℤ) :
    (ClosedCell 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), (𝓡∂ 2).prod (𝓡 1)⟯
      (ClosedCell 2 × Circle) where
  toFun x := (closedDiskRotation (x.2 ^ k) x.1, x.2)
  invFun x := (closedDiskRotation (x.2 ^ (-k)) x.1, x.2)
  left_inv x := by
    refine Prod.ext ?_ rfl
    change closedDiskRotation (x.2 ^ (-k)) (closedDiskRotation (x.2 ^ k) x.1) = x.1
    rw [← closedDiskRotation_mul, ← zpow_add]
    simp
  right_inv x := by
    refine Prod.ext ?_ rfl
    change closedDiskRotation (x.2 ^ k) (closedDiskRotation (x.2 ^ (-k)) x.1) = x.1
    rw [← closedDiskRotation_mul, ← zpow_add]
    simp
  contMDiff_toFun := twist_contMDiff k
  contMDiff_invFun := twist_contMDiff (-k)

theorem closedSolidTorusTwist_apply (k : ℤ) (x : ClosedCell 2 × Circle) :
    closedSolidTorusTwist k x = (closedDiskRotation (x.2 ^ k) x.1, x.2) := rfl

@[simp] theorem closedSolidTorusTwist_symm_apply (k : ℤ) (x : ClosedCell 2 × Circle) :
    (closedSolidTorusTwist k).symm x = closedSolidTorusTwist (-k) x := rfl

@[simp] theorem closedSolidTorusTwist_norm (k : ℤ) (x : ClosedCell 2 × Circle) :
    ‖(closedSolidTorusTwist k x).1.val‖ = ‖x.1.val‖ :=
  closedDiskRotation_norm (x.2 ^ k) x.1

theorem closedSolidTorusTwist_action (k q p : ℤ) (t : Circle)
    (x : ClosedCell 2 × Circle) :
    closedSolidTorusTwist k (closedSolidTorusAction q p t x) =
      closedSolidTorusAction (q + k * p) p t (closedSolidTorusTwist k x) := by
  refine Prod.ext ?_ rfl
  change closedDiskRotation ((t ^ p * x.2) ^ k) (closedDiskRotation (t ^ q) x.1) =
    closedDiskRotation (t ^ (q + k * p)) (closedDiskRotation (x.2 ^ k) x.1)
  rw [← closedDiskRotation_mul, ← closedDiskRotation_mul]
  congr 1
  simp only [mul_zpow, ← zpow_mul, zpow_add, mul_comm p k,
    mul_comm, mul_assoc]

theorem closedSolidTorusTwist_multiplicity_one (q p : ℤ) (hp : p * p = 1)
    (t : Circle) (x : ClosedCell 2 × Circle) :
    closedSolidTorusTwist (-q * p) (closedSolidTorusAction q p t x) =
      closedSolidTorusAction 0 p t (closedSolidTorusTwist (-q * p) x) := by
  have he : q + (-q * p) * p = 0 := by
    calc
      _ = q * (1 - p * p) := by ring
      _ = 0 := by rw [hp]; ring
  simpa only [he] using closedSolidTorusTwist_action (-q * p) q p t x

end DifferentialGeometry.Topology.Manifold
