import DifferentialGeometry.Topology.Ehresmann.LocalTrivOverArcBCF
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle

/-!
# Consumer of the annulus kernel (lane S-BCF03b)

The trivial product `ℝ × S¹ → ℝ` (chart `id` over the arc `id : [0, 1] → ℝ`) has the annulus
parametrization of `[0, 1] × S¹`, and the sphere-circle homeomorphism is inverse to itself.
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology

theorem exists_annulus_param_example_BCF :
    ∃ e : Circle × Icc (0 : ℝ) 1 → ℝ × Circle, Continuous e ∧ Injective e ∧
      range e = (univ : Set (ℝ × Circle)) ∩ Prod.fst ⁻¹' (id '' Icc 0 1) ∧
      (∀ q, (e q).1 = id q.2) ∧
      e '' {q | (q.2 : ℝ) = 0} = (univ : Set (ℝ × Circle)) ∩ Prod.fst ⁻¹' {id 0} ∧
      e '' {q | (q.2 : ℝ) = 1} = (univ : Set (ℝ × Circle)) ∩ Prod.fst ⁻¹' {id 1} := by
  refine exists_annulus_param_BCF (X := (univ : Set (ℝ × Circle))) (f := Prod.fst)
    (Bs := (univ : Set ℝ)) (E := ℝ) (Q := Circle) (a := id) continuous_id.continuousOn
    injective_id.injOn (subset_univ _) ?_
  intro y _
  refine ⟨id, id, univ, y, rfl, Topology.IsEmbedding.id, isOpen_univ, by simp, continuous_id,
    injective_id, by simp, fun x z => rfl⟩

theorem circleSphere_symm_apply_BCF (x : Circle) :
    circleSphereHomeomorph_BCF.symm (circleSphereHomeomorph_BCF x) = x :=
  circleSphereHomeomorph_BCF.symm_apply_apply x

end DifferentialGeometry.Topology
