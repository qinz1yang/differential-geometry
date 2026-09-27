import DifferentialGeometry.Topology.Manifold.OpenSphereCylinder
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition

set_option autoImplicit false
noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

abbrev SphereCylinder := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ
abbrev SphereCylinderModel := (𝓡 2).prod 𝓘(ℝ)

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def cylinderExponentialChart (v : S2) : PartialDiffeomorph SphereCylinderModel (𝓡 3) SphereCylinder E3 ∞ :=
  (sphereProdRealDiffeomorphPunctured (n := 2) v).toPartialDiffeomorph.trans
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) (puncturedSpace E3)
      ⟨⟨v.val, ne_zero_of_mem_unit_sphere v⟩⟩)

@[simp] theorem cylinderExponentialChart_apply (v : S2) (q : SphereCylinder) :
    cylinderExponentialChart v q = Real.exp q.2 • (q.1 : E3) := rfl

@[simp] theorem cylinderExponentialChart_source (v : S2) :
    (cylinderExponentialChart v).source = univ := by
  ext q
  change (q ∈ univ ∧ _ ∈ univ) ↔ q ∈ univ
  simp

@[simp] theorem cylinderExponentialChart_target (v : S2) :
    (cylinderExponentialChart v).target = {0}ᶜ := by
  ext x
  change (x ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) (puncturedSpace E3)
      ⟨⟨v.val, ne_zero_of_mem_unit_sphere v⟩⟩).target ∧ _ ∈ univ) ↔ x ∈ ({0}ᶜ : Set E3)
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  simp [puncturedSpace]

theorem cylinderExponentialChart_symm_apply (v : S2) (x : E3) (hx : x ≠ 0) :
    (cylinderExponentialChart v).symm x = (sphereDirection v x, Real.log ‖x‖) := by
  change (sphereProdRealDiffeomorphPunctured (n := 2) v).symm
    ((DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) (puncturedSpace E3)
      ⟨⟨v.val, ne_zero_of_mem_unit_sphere v⟩⟩).symm x) = _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply _ _ _ hx]
  rfl

theorem norm_cylinderExponentialChart (v : S2) (q : SphereCylinder) :
    ‖cylinderExponentialChart v q‖ = Real.exp q.2 := by
  rw [cylinderExponentialChart_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_eq_of_mem_sphere, mul_one]

theorem cylinderExponentialChart_zero (v p : S2) :
    cylinderExponentialChart v (p, 0) = p.val := by
  simp

theorem cylinderExponentialChart_symm_sphere (v p : S2) :
    (cylinderExponentialChart v).symm p.val = (p, 0) := by
  rw [← cylinderExponentialChart_zero v p]
  exact (cylinderExponentialChart v).left_inv (by rw [cylinderExponentialChart_source]; trivial)

end DifferentialGeometry.Topology.Manifold
