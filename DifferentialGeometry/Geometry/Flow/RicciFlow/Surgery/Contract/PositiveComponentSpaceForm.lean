import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardGeometricFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoverClassification
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectivePresentation
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering
import DifferentialGeometry.Geometry.Curvature.ProjectiveSpace

open private diffeomorphOfPartialDiffeomorphUniv from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardGeometricFrontier

noncomputable section

open scoped Manifold ContDiff
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

theorem admitsConstantPositiveSectionalCurvature_of_positiveComponent
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (R : PositiveComponent (M := M.Carrier) Set.univ) :
    admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := M.Carrier) := by
  cases R with
  | sphere F hs ht =>
    exact admitsConstantPositiveSectionalCurvature_of_positiveComponent_sphere M hs ht
  | projective Z presentation F hs ht =>
    obtain ⟨e, he⟩ := presentation.exists_realProjectiveThree_diffeomorph
    let d := e.trans (diffeomorphOfPartialDiffeomorphUniv F hs ht)
    exact ⟨Diffeomorph.pullbackMetric roundProjectiveMetric d.symm,
      constantPositiveSectionalCurvatureMetric_pullback roundProjectiveMetric
        constantPositiveSectionalCurvatureMetric_roundProjectiveMetric d.symm⟩

theorem MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveOrRoundComponent
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : ∀ C : ConnectedComponents E.discarded.Carrier,
      Nonempty (PositiveComponent
        (M := (E.discarded.toClosedOrientedManifold.component C).Carrier) Set.univ) ∨
      ∃ (D' : RealTimeInterval)
        (S : SolutionOn (I := ThreeModel)
          (M := (E.discarded.toClosedOrientedManifold.component C).Carrier) D')
        (ε : ℝ) (x : (E.discarded.toClosedOrientedManifold.component C).Carrier) (t : ℝ),
        Nonempty (RoundComponent S ε x t Set.univ)) : E.poincareStandardDiscarded := by
  apply MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct
    E
  intro C
  refine ⟨[E.discarded.toClosedOrientedManifold.component C], ?_,
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
  intro F hF
  rw [List.mem_singleton] at hF
  subst F
  apply Or.inl
  rcases h C with hpositive | hround
  · obtain ⟨R⟩ := hpositive
    exact admitsConstantPositiveSectionalCurvature_of_positiveComponent _ R
  · obtain ⟨D', S, ε, x, t, ⟨R⟩⟩ := hround
    exact admitsConstantPositiveSectionalCurvature_of_roundComponent _ R

open Set in
theorem isPoincareStandard_of_ball_cap_cover
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {K : Set M.Carrier} (B : PartialDiffeomorph I3 I3 ThreeSpace M.Carrier ∞)
    (hB : Metric.closedBall (0 : ThreeSpace) 1 ⊆ B.source)
    (cap : CapCore K)
    (hcover : B '' Metric.closedBall (0 : ThreeSpace) 1 ∪ K = univ) :
    isPoincareStandard M.Carrier := by
  obtain ⟨W⟩ := nonempty_positiveComponent_of_ball_cap_cover B hB cap hcover
  exact isPoincareStandard_of_standard_factor M
    (isStandardFactor_of_admitsConstantPositiveSectionalCurvature (M := M)
      (admitsConstantPositiveSectionalCurvature_of_positiveComponent M W))


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
