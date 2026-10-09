import DifferentialGeometry.Geometry.Comparison.OrthogonalLineSplitting
import DifferentialGeometry.Geometry.Comparison.AlignedEuclideanCoordinates
import DifferentialGeometry.Geometry.Comparison.LineBusemann

set_option autoImplicit false
open Set Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

theorem exists_oriented_euclidean_coordinates {k : ℕ} {X : Type u} [MetricSpace X] [ProperSpace X]
    (p : X) (hs : fourPointComparison 0 (univ : Set X))
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (γ : Fin k → ℝ → X) (hγ : ∀ j, Isometry (γ j)) (hγ0 : ∀ j, γ j 0 = p)
    (hangle : ∀ j l, j ≠ l → germComparisonAngle 0 (γ j) (γ l) = Real.pi / 2) :
    ∃ (Z : Type u) (m : MetricSpace Z), letI := m
      ∃ (z : Z) (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)),
        e p = WithLp.toLp 2 (0, z) ∧
        (∀ j t, e (γ j t) = WithLp.toLp 2 (PiLp.single 2 j t, z)) ∧
        (∀ j x, lineCoordinate (γ j) x = (e x).fst j) ∧
        (∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-(e x).fst j))) ∧
        ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
        (∀ a b : Z, ∃ f : Icc (0 : ℝ) 1 → Z,
          Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) := by
  obtain ⟨Z, m, z, e, he0, heaxis, hp, hc, hsZ, hsegZ⟩ :=
    exists_oriented_euclidean_splitting p hs hsegments γ hγ hγ0 hangle
  let := m
  have hcoord (j : Fin k) (x : X) : lineCoordinate (γ j) x = (e x).fst j :=
    lineCoordinate_eq_euclidean_coordinate_of_aligned_isometry e (heaxis j) x
  refine ⟨Z, m, z, e, he0, heaxis, hcoord, ?_, hp, hc, hsZ, hsegZ⟩
  intro j x
  rw [← hcoord j x]
  exact tendsto_dist_line_sub_lineCoordinate hs (hγ j) hsegments x

end DifferentialGeometry.Geometry.Comparison.Toponogov
