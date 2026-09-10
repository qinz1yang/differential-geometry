import DifferentialGeometry.Geometry.Boundary.ParametrizationInterior
import DifferentialGeometry.Geometry.Boundary.ProductHalfSpace
import DifferentialGeometry.Topology.Manifold.NestedBallShell

noncomputable section
open Set Metric Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Boundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem positive_dimension (v : sphere (0 : E) 1) : 0 < Module.finrank ℝ E := by
  have hv : (v : E) ≠ 0 := by
    intro h
    have := v.property
    simp [h] at this
  have : Nontrivial E := ⟨⟨v, 0, hv⟩⟩
  exact Module.finrank_pos

theorem isPreconnected_interior_nestedBallShell [PreconnectedSpace (sphere (0 : E) 1)]
    (outer inner : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r R : ℝ} (hr : 0 < r)
    (houter : closedBall (0 : E) R ⊆ outer.source)
    (hinner : closedBall (0 : E) r ⊆ inner.source)
    (hnested : inner '' closedBall 0 r ⊆ outer '' ball 0 R)
    (v : sphere (0 : E) 1) :
    IsPreconnected (interior (outer '' closedBall 0 R \ inner '' ball 0 r)) := by
  let n := Module.finrank ℝ E - 1
  have : Fact (Module.finrank ℝ E = n + 1) :=
    ⟨(Nat.sub_add_cancel (positive_dimension v)).symm⟩
  obtain ⟨e, hes, het, he, hei⟩ :=
    Poincare.Topology.Manifold.exists_smooth_nestedBallShell_parametrization (n := n)
      outer inner hr houter hinner hnested v
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, finrank_euclideanSpace_fin] using
      (Fact.out : Module.finrank ℝ E = n + 1).symm
  have h := isPreconnected_interior_target_of_smooth_parametrization e hes he hei hdim
  rwa [het] at h

theorem closure_interior_nestedBallShell
    (outer inner : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    {r R : ℝ} (hr : 0 < r)
    (houter : closedBall (0 : E) R ⊆ outer.source)
    (hinner : closedBall (0 : E) r ⊆ inner.source)
    (hnested : inner '' closedBall 0 r ⊆ outer '' ball 0 R)
    (v : sphere (0 : E) 1) :
    closure (interior (outer '' closedBall 0 R \ inner '' ball 0 r)) =
      outer '' closedBall 0 R \ inner '' ball 0 r := by
  let n := Module.finrank ℝ E - 1
  have : Fact (Module.finrank ℝ E = n + 1) :=
    ⟨(Nat.sub_add_cancel (positive_dimension v)).symm⟩
  obtain ⟨e, hes, het, he, hei⟩ :=
    Poincare.Topology.Manifold.exists_smooth_nestedBallShell_parametrization (n := n)
      outer inner hr houter hinner hnested v
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, finrank_euclideanSpace_fin] using
      (Fact.out : Module.finrank ℝ E = n + 1).symm
  have h := closure_interior_target_of_smooth_parametrization e hes he hei hdim
  rwa [het] at h

end Poincare.Geometry.Boundary
