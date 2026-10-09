import DifferentialGeometry.Topology.Ehresmann.LoopBundleBCF
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle

/-!
# Consumer of the loop-bundle kernels (lane S-BCF03b)

The trivial circle bundle `Prod.fst : S¹ × S¹ → S¹` over the loop `id : S¹ → S¹` (chart `id`) has
the continuous open projection of `circle_base`, and its total space is preconnected.
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology

theorem trivialCharts_loop_BCF :
    ∀ y ∈ range (id : Circle → Circle), ∃ (σ : Circle → Circle)
      (φ : Circle × Circle → Circle × Circle) (O : Set Circle) (x₀ : Circle),
      σ x₀ = y ∧ IsEmbedding σ ∧ IsOpen O ∧
      range σ = (univ : Set Circle) ∩ O ∧ Continuous φ ∧
      range φ = (univ : Set (Circle × Circle)) ∩ Prod.fst ⁻¹' range σ ∧
      ∀ x z, (φ (x, z)).1 = σ x := by
  intro y _
  exact ⟨id, id, univ, y, rfl, Topology.IsEmbedding.id, isOpen_univ, by simp, continuous_id,
    by simp, fun x z => rfl⟩

theorem exists_circleBase_example_BCF :
    ∃ p : ((univ : Set (Circle × Circle)) ∩ Prod.fst ⁻¹' range (id : Circle → Circle) :
        Set (Circle × Circle)) → Circle, Continuous p ∧ IsOpenMap p ∧ ∀ x, id (p x) = x.1.1 :=
  exists_circleBase_of_loop_BCF (X := (univ : Set (Circle × Circle))) (f := Prod.fst)
    (Bs := (univ : Set Circle)) (E := Circle) (Q := Circle) continuous_id injective_id
    (subset_univ _) continuous_fst.continuousOn trivialCharts_loop_BCF

theorem isPreconnected_loop_example_BCF :
    IsPreconnected ((univ : Set (Circle × Circle)) ∩
      Prod.fst ⁻¹' range (id : Circle → Circle)) := by
  refine isPreconnected_preimage_loop_BCF (X := (univ : Set (Circle × Circle))) (f := Prod.fst)
    (Bs := (univ : Set Circle)) (E := Circle) (Q := Circle) continuous_id (subset_univ _)
    trivialCharts_loop_BCF (fun y _ => ?_) fun y _ => ?_
  · exact ⟨(y, y), mem_univ _, rfl⟩
  · have : ((univ : Set (Circle × Circle)) ∩ Prod.fst ⁻¹' {y}) = {y} ×ˢ univ := by
      ext q
      simp
    rw [this]
    exact isPreconnected_singleton.prod isPreconnected_univ

end DifferentialGeometry.Topology
