import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimInstance

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u uE uH

theorem euclideanFlatFlow_scalarBounded :
    PointedFlowScalarBounded (I := I3) euclideanFlatFlow 0 := by
  intro t _ht x
  have h : euclideanFlatFlow.S.scalar t x = 0 := by
    simp only [euclideanFlatFlow, SolutionOn.const, SolutionOn.scalar, SolutionFamily.scalar]
    exact DifferentialGeometry.Geometry.euclideanMetric_scalarCurvature x
  rw [h]
  exact ⟨le_rfl, le_rfl⟩

theorem euclideanFlatFlow_scalarBounded_and_nonnegativeCurvatureOperator :
    PointedFlowScalarBounded (I := I3) euclideanFlatFlow 0 ∧
      ∀ t : ℝ, PointedFlowNonnegativeCurvatureOperator (I := I3) euclideanFlatFlow t :=
  ⟨euclideanFlatFlow_scalarBounded, euclideanFlatFlow_nonnegativeCurvatureOperator⟩

theorem exists_scalarBounded_and_nonnegativeCurvatureOperator_of_isAncientKappaSolution
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {F : PointedFlowData.{u, uE, uH} (I := I) D} {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) :
    (∃ C : ℝ, PointedFlowScalarBounded (I := I) F C) ∧
      ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) F t :=
  ⟨hF.globalScalarBound, hF.nonnegativeCurvatureOperator⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
