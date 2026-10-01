import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnulusParametrizationOfProductCircleCut
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_isPLAnnulusWithEnds_component_compl_polygons
    (S : Set E3) (hS : IsCombinatorialSolidTorus S) (n : ℕ) (G : Fin n → Set E3)
    (hn : 1 < n) (hG : ∀ i, IsPLSphere 1 (G i)) (hGS : ∀ i, G i ⊆ frontier S)
    (hdisj : Pairwise fun i j => Disjoint (G i) (G j))
    (hess : ∀ i, ¬ ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
        Δ ⊆ frontier S ∧ G i = r '' stdSimplexBoundary 2)
    (x : E3) (hx : x ∈ frontier S \ (⋃ i, G i)) :
    ∃ i j : Fin n, i ≠ j ∧
      IsPLAnnulusWithEnds (closure (connectedComponentIn (frontier S \ ⋃ i, G i) x))
        (G i) (G j) := by
  classical
  obtain ⟨J, Q, f, q, hJ, hQ, hf, hq, hinj, hfamily⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hS G hn hG hGS hdisj hess
  have hG_eq : G = fun i => f '' (J ×ˢ {q i}) := funext hfamily
  rw [hG_eq] at hx ⊢
  obtain ⟨i, j, hij, ρ, hρ, hzero, hone⟩ :=
    exists_annulus_parametrization_of_product_circle_cut hJ hQ hf hn q hq hinj hx
  exact ⟨i, j, hij, J, ρ, hJ, hρ, hzero, hone⟩

end DifferentialGeometry.Topology.PiecewiseLinear
