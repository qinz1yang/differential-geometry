import DifferentialGeometry.Topology.PiecewiseLinear.SkeletonReduction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem isEmbedding_domRestrict_id_and_exists_isPLHomeomorphInto_dist_lt_univ :
    IsOpen (univ : Set (EuclideanSpace ℝ (Fin 3))) ∧
      Topology.IsEmbedding ((univ : Set (EuclideanSpace ℝ (Fin 3))).domRestrict id) ∧
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphInto 3 f univ ∧
          ∀ x ∈ (univ : Set (EuclideanSpace ℝ (Fin 3))), dist (f x) (id x) < 1 := by
  refine ⟨isOpen_univ, ?_, exists_isPLHomeomorphInto_dist_lt_id_of_isOpen isOpen_univ
    fun _ _ => one_pos⟩
  rw [Set.domRestrict_id]
  exact Topology.IsEmbedding.subtypeVal

end DifferentialGeometry.Topology.PiecewiseLinear
