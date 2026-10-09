import DifferentialGeometry.Topology.Ehresmann.BundleOverArcBCF
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle

/-!
# Consumer of the arc-bundle kernel: the product bundle over `[0, 1]` (lane S-BCF03)

`exists_trivialization_product_BCF`: the kernel applied to the product bundle `S¹ × ℝ → ℝ` over the
arc `a = id` with the identity as the local trivialization (a non-vacuous instance: the produced
parametrization is a continuous injective map of `S¹ × [0, 1]` onto `S¹ × [0, 1]` over the arc).
-/

set_option autoImplicit false

open Set Function Topology

namespace DifferentialGeometry.Topology

theorem exists_trivialization_product_BCF :
    ∃ E : Circle × ℝ → Circle × ℝ, ContinuousOn E (univ ×ˢ Icc 0 1) ∧
      InjOn E (univ ×ˢ Icc 0 1) ∧
      (∀ z, ∀ s ∈ Icc (0 : ℝ) 1, (E (z, s)).2 = s) ∧
      E '' (univ ×ˢ Icc 0 1) = (univ : Set (Circle × ℝ)) ∩ Prod.snd ⁻¹' (id '' Icc (0 : ℝ) 1) := by
  refine exists_bundle_trivialization_over_arc_BCF (π := Prod.snd) (a := id)
    (P := (univ : Set (Circle × ℝ))) (injOn_id _) fun t _ => ?_
  refine ⟨univ, isOpen_univ, mem_univ t, id, continuousOn_id, injOn_id _, fun z s _ => rfl, ?_⟩
  ext p
  constructor
  · rintro ⟨q, ⟨-, hq⟩, rfl⟩
    exact ⟨mem_univ _, q.2, hq, rfl⟩
  · rintro ⟨-, s, hs, hps⟩
    refine ⟨p, ⟨mem_univ _, ?_⟩, rfl⟩
    have h2 : p.2 = s := hps.symm
    rw [h2]
    exact hs

end DifferentialGeometry.Topology
