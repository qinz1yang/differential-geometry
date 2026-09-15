import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.PushProperty

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem HasPushPropertyAt.exists_homeomorph_fixed_on_of_inter_subset
    {C D A U : Set (EuclideanSpace ℝ (Fin 3))} (hCD : HasPushPropertyAt C D)
    {f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D)
    (hA : IsPolyhedron A) (hCA : C ∩ A ⊆ f '' stdSimplexBoundary 2)
    (hdense : A ⊆ closure (A \ C)) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn h univ univ ∧ h '' D = closure (frontier C \ D) ∧
      EqOn h id A ∧ EqOn h id Uᶜ ∧
      h '' (D ∪ A) = closure (frontier C \ D) ∪ A := by
  obtain ⟨N, hN, hCN, hNU, hNA⟩ :=
    exists_isPolyhedron_neighborhood_sdiff hCD.1.isPolyhedron hA hU hCU
  have hNbd : C \ (f '' stdSimplexBoundary 2) ⊆ interior N := by
    intro x hx
    exact hCN ⟨hx.1, fun hxA => hx.2 (hCA ⟨hx.1, hxA⟩)⟩
  obtain ⟨h, hh, hD, hfix⟩ := hCD.2.2.2 f hf N hN hNbd
  have hfix' : EqOn h id (A \ C) := by
    intro x hx
    apply hfix
    intro hxN
    exact hx.2 ((hNA ▸ (show x ∈ N ∩ A from ⟨hxN, hx.1⟩)).1)
  have hfixA : EqOn h id A := (hfix'.closure h.continuous continuous_id).mono hdense
  refine ⟨h, hh, hD, hfixA, fun x hx => hfix (fun hxN => hx (hNU hxN)), ?_⟩
  rw [image_union, hD, hfixA.image_eq, image_id]

end DifferentialGeometry.Topology.PiecewiseLinear
