import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCellPush

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.exists_relative_sphere_surgery
    {S C U : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 (S ∩ C)) (hDC : S ∩ C ⊆ frontier C)
    (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn φ univ univ ∧ EqOn φ id Uᶜ ∧
      EqOn φ id (closure (S \ C)) ∧
      φ '' S = closure (S \ C) ∪ closure (frontier C \ S) := by
  exact (hasPushProperty_of_isSimplyEmbedded_frontier hC
    hC.isPLSphere_frontier.isSimplyEmbedded).exists_isPLHomeomorphOn_sphere_surgery
      hS hD hDC hU hCU

theorem IsPLBall.exists_relative_sphere_surgery_preserving
    {S C U T : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 (S ∩ C)) (hDC : S ∩ C ⊆ frontier C)
    (hU : IsOpen U) (hCU : C ⊆ U) (hprotect : U ⊆ T ∨ Disjoint U T) :
    ∃ φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn φ univ univ ∧ EqOn φ id Uᶜ ∧
      EqOn φ id (closure (S \ C)) ∧ φ '' T = T ∧
      φ '' S = closure (S \ C) ∪ closure (frontier C \ S) := by
  obtain ⟨φ, hφ, hfix, hrest, himage⟩ := hC.exists_relative_sphere_surgery hS hD hDC hU hCU
  refine ⟨φ, hφ, hfix, hrest, ?_, himage⟩
  rcases hprotect with hsub | hdisj
  · exact image_eq_of_homeomorph_eqOn_compl_of_subset φ hfix hsub
  · have hfixT : EqOn φ id T := fun x hx =>
      hfix (fun hxU => disjoint_left.mp hdisj hxU hx)
    simpa only [image_id] using hfixT.image_eq

theorem IsPLBall.exists_relative_sphere_surgery_of_disjoint_frontier
    {S C U T : Set (EuclideanSpace ℝ (Fin 3))} (hC : IsPLBall 3 C)
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 (S ∩ C)) (hDC : S ∩ C ⊆ frontier C)
    (hU : IsOpen U) (hCU : C ⊆ U) (hconn : IsPreconnected U)
    (hfront : Disjoint U (frontier T)) :
    ∃ φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn φ univ univ ∧ EqOn φ id Uᶜ ∧
      EqOn φ id (closure (S \ C)) ∧ φ '' T = T ∧
      φ '' S = closure (S \ C) ∪ closure (frontier C \ S) := by
  apply hC.exists_relative_sphere_surgery_preserving hS hD hDC hU hCU
  by_cases hmeet : (U ∩ T).Nonempty
  · exact Or.inl
      (DifferentialGeometry.Topology.PiecewiseLinear.IsPreconnected.subset_of_disjoint_frontier
        hconn hmeet hfront)
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet))

end DifferentialGeometry.Topology.PiecewiseLinear
