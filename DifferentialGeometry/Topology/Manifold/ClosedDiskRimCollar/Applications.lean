import DifferentialGeometry.Topology.Manifold.ClosedDiskRimCollar.Straighten

/-!
# Rim collar straightening: time-one form

Consumer of `exists_closedCell_isotopy_to_identity_near_boundary_of_fix_boundary`. A
diffeomorphism of the closed cell that fixes the boundary sphere pointwise is joined, by a jointly
smooth isotopy through boundary-fixing diffeomorphisms, to a diffeomorphism that is the identity on
an open neighbourhood of the boundary sphere.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {m : ℕ}

local instance closedCellChartsApp_D2S1RIM :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m

local instance closedCellSmoothApp_D2S1RIM : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

/-- **Time-one form.** A diffeomorphism `μ` of the closed cell fixing the boundary sphere pointwise
is joined to a diffeomorphism `μ'` that is the identity on an open neighbourhood of the boundary
sphere, by a jointly smooth isotopy `K` (with `K 0 = μ`, `K 1 = μ'`) through diffeomorphisms fixing
the boundary sphere pointwise. -/
theorem exists_closedCell_diffeomorph_eq_id_near_boundary_of_fix_boundary
    (μ : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1))
    (hμ : ∀ x : ClosedCell (m + 1), ‖x.val‖ = 1 → μ x = x) :
    ∃ μ' : ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1),
      (∃ N : Set (ClosedCell (m + 1)), IsOpen N ∧ {x | ‖x.val‖ = 1} ⊆ N ∧ ∀ x ∈ N, μ' x = x) ∧
      ∃ K : ℝ → (ClosedCell (m + 1) ≃ₘ⟮𝓡∂ (m + 1), 𝓡∂ (m + 1)⟯ ClosedCell (m + 1)),
        ContMDiff ((𝓡∂ (m + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (m + 1)) ∞
          (fun x : ClosedCell (m + 1) × ℝ => K x.2 x.1) ∧
        K 0 = μ ∧ K 1 = μ' ∧ ∀ t (x : ClosedCell (m + 1)), ‖x.val‖ = 1 → K t x = x := by
  obtain ⟨K, hK, -, hfix, hlo, N, hN, hSN, hhi⟩ :=
    exists_closedCell_isotopy_to_identity_near_boundary_of_fix_boundary μ hμ
  refine ⟨K 1, ⟨N, hN, hSN, fun x hx => hhi 1 x hx (by norm_num)⟩, K, hK, ?_, rfl, hfix⟩
  exact Diffeomorph.ext fun x => hlo 0 x (by norm_num)

end DifferentialGeometry.Topology.Manifold
