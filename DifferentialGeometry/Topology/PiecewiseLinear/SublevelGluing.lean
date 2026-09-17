import DifferentialGeometry.Topology.SlabBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isSimplyEmbedded_frontier_sublevel_of_slab (I : SchoenfliesInput)
    {P : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsClosed P)
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) {a b : ℝ} (hab : a < b)
    (hleft : IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' Iic a)))
    (hslab : IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' Icc a b)))
    {g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (P ∩ {x | ℓ x = a}))
    (hgb : g '' stdSimplexBoundary 2 = frontier P ∩ {x | ℓ x = a}) :
    IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' Iic b)) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => f x) h
  have h := I.isSimplyEmbedded_union_sdiff_diskInterior _ _ _ g ℓ.toLinearMap a
    hleft hslab hg hlinear inter_subset_right (Topology.frontier_sublevel_inter_frontier_slab hP ℓ hℓ hab.le)
  rw [hgb] at h
  rwa [Topology.frontier_sublevel_slab_union_sdiff hP ℓ hℓ hab] at h

theorem isSimplyEmbedded_frontier_of_sublevel_superlevel (I : SchoenfliesInput)
    {P : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsClosed P)
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (a : ℝ)
    (hleft : IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' Iic a)))
    (hright : IsSimplyEmbedded (frontier (P ∩ ℓ ⁻¹' Ici a)))
    {g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) (P ∩ {x | ℓ x = a}))
    (hgb : g '' stdSimplexBoundary 2 = frontier P ∩ {x | ℓ x = a}) :
    IsSimplyEmbedded (frontier P) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun f : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ => f x) h
  have h := I.isSimplyEmbedded_union_sdiff_diskInterior _ _ _ g ℓ.toLinearMap a
    hleft hright hg hlinear inter_subset_right (Topology.frontier_sublevel_inter_frontier_superlevel hP ℓ hℓ a)
  rw [hgb] at h
  rwa [Topology.frontier_sublevel_union_superlevel_sdiff hP ℓ hℓ a] at h

end DifferentialGeometry.Topology.PiecewiseLinear
