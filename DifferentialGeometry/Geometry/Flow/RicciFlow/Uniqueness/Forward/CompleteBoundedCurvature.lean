import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Noncompact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M] [NoncompactSpace M]

namespace CompleteBoundedCurvatureSolutionOn

def timeRestrict
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    (hcar : D'.carrier ⊆ D.carrier) (hreg : D'.regular ⊆ D.regular) :
    CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D') where
  solution := S.solution.timeRestrict D'
  isSolution := isSoln_timeRestrict S.isSolution hcar hreg
  complete := by
    intro t ht
    exact S.complete t (hcar ht)
  curvatureBound := by
    intro t ht
    exact S.curvatureBound t (hcar ht)

omit [NoncompactSpace M] in
@[simp] theorem timeRestrict_solution
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    (hcar : D'.carrier ⊆ D.carrier) (hreg : D'.regular ⊆ D.regular) :
    (S.timeRestrict hcar hreg).solution = S.solution.timeRestrict D' := by
  rfl

omit [NoncompactSpace M] in
theorem timeRestrict_complete
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    (hcar : D'.carrier ⊆ D.carrier) (hreg : D'.regular ⊆ D.regular)
    (t : Real) (ht : t ∈ D'.carrier) :
    DifferentialGeometry.RiemannianMetricComplete (I := I)
      ((S.timeRestrict hcar hreg).solution.base.metric t) := by
  exact S.complete t (hcar ht)

omit [NoncompactSpace M] in
theorem timeRestrict_curvature_bound
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D))
    (hcar : D'.carrier ⊆ D.carrier) (hreg : D'.regular ⊆ D.regular)
    (t : Real) (ht : t ∈ D'.carrier) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
      normSq0S (I := I) ((S.timeRestrict hcar hreg).solution.base.metric t) x 4
        (metricRm04At (I := I) ((S.timeRestrict hcar hreg).solution.base.metric t) x) ≤ C := by
  exact S.curvatureBound t (hcar ht)

def timeShift
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D)) (τ : Real) :
    CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D.timeShift τ) where
  solution := S.solution.timeShift τ
  isSolution := isSolutionOn_timeShift S.isSolution τ
  complete := by
    intro t ht
    exact S.complete (t + τ) ht
  curvatureBound := by
    intro t ht
    change ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
      normSq0S (I := I) (S.solution.base.metric (t + τ)) x 4
        (metricRm04At (I := I) (S.solution.base.metric (t + τ)) x) ≤ C
    exact S.curvatureBound (t + τ) ht

omit [NoncompactSpace M] in
@[simp] theorem timeShift_solution
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D)) (τ : Real) :
    (S.timeShift τ).solution = S.solution.timeShift τ := by
  rfl

omit [NoncompactSpace M] in
theorem timeShift_complete
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D)) (τ t : Real)
    (ht : t ∈ (D.timeShift τ).carrier) :
    DifferentialGeometry.RiemannianMetricComplete (I := I)
      ((S.timeShift τ).solution.base.metric t) := by
  exact S.complete (t + τ) ht

omit [NoncompactSpace M] in
theorem timeShift_curvature_bound
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D)) (τ t : Real)
    (ht : t ∈ (D.timeShift τ).carrier) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
      normSq0S (I := I) ((S.timeShift τ).solution.base.metric t) x 4
        (metricRm04At (I := I) ((S.timeShift τ).solution.base.metric t) x) ≤ C := by
  change ∃ C : Real, 0 ≤ C ∧ ∀ x : M,
    normSq0S (I := I) (S.solution.base.metric (t + τ)) x 4
      (metricRm04At (I := I) (S.solution.base.metric (t + τ)) x) ≤ C
  exact S.curvatureBound (t + τ) ht

end CompleteBoundedCurvatureSolutionOn

omit [NoncompactSpace M] in
theorem ricci_flow_forward_unique_of_complete_bounded_curvature
    {a b : Real} (hab : a < b)
    (S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
      (D := DifferentialGeometry.Geometry.Curvature.RealTimeInterval.closedOpen a b hab))
    (henergyCont : ContinuousOn
      (forwardUniqueEnergy (I := I) (M := M)
        S₁.solution.base.metric S₂.solution.base.metric) (Set.Icc a b))
    (henergy' : Real → Real)
    (henergyDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt
        (forwardUniqueEnergy (I := I) (M := M)
          S₁.solution.base.metric S₂.solution.base.metric)
        (henergy' t) t)
    (K : Real)
    (henergyBound : ∀ t ∈ Set.Ioo a b,
      henergy' t ≤
        K * forwardUniqueEnergy (I := I) (M := M)
          S₁.solution.base.metric S₂.solution.base.metric t)
    (hinitial : S₁.solution.base.metric a = S₂.solution.base.metric a)
    (hdensityCont : ∀ t ∈ Set.Icc a b,
      Continuous (fun x =>
        forwardUniqueDensity (I := I) S₁.solution.base.metric S₂.solution.base.metric t x))
    (hdensityIntegrable : ∀ t ∈ Set.Icc a b,
      Integrable (fun x =>
        forwardUniqueDensity (I := I) S₁.solution.base.metric S₂.solution.base.metric t x)
        (riemannianMeasureFamily (I := I) (M := M) S₁.solution.base.metric t)) :
    ∀ t ∈ Set.Ico a b,
      S₁.solution.base.metric t = S₂.solution.base.metric t := by
  have hcriterion :
      NoncompactForwardUniquenessCriterion (I := I)
        S₁.solution.base.metric S₂.solution.base.metric a b K henergy' :=
    { interval := hab
      energyCont := henergyCont
      energyDerivative := henergyDeriv
      energyBound := henergyBound
      initial := hinitial
      densityCont := hdensityCont
      densityIntegrable := hdensityIntegrable }
  have huniq := forward_unique_of_noncompact_criterion (I := I)
    S₁.solution.base.metric S₂.solution.base.metric hcriterion
  intro t ht
  exact huniq t ⟨ht.1, ht.2.le⟩

end DifferentialGeometry.PDE.RicciFlow

end
