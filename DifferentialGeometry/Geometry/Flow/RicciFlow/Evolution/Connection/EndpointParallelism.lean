import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.EndpointConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.ConnectionEvaluation

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem LeviCivita_eq_zero_right_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (R : SmoothRiemannianMetric I M) (α : M)
    {a b B KShi : ℝ} (hab : a < b)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    {K : Set M} (hK : IsCompact K) (hchart : K ⊆ coordinateFrameSet (I := I) α)
    {U : Set E} (hU : IsOpen U) (hUchart : U ⊆ interior (extChartAt I α).target)
    (hUK : MapsTo (extChartAt I α).symm U K)
    (hmetric : ∀ t ∈ Icc a b, MetricUniformEquivalentOn K R (S.family.metric t) B)
    (hShi : MovingShiBoundOn K a b (fun _ t => S.family.metric t) 1 KShi)
    {x : M} (hx : x ∈ K) (hxU : extChartAt I α x ∈ U)
    {X : ∀ y : M, TangentSpace I y} (hX : MDiffAt (T% X) x)
    (hparallel : ∀ᶠ t in 𝓝[Ioo a b] b,
      ∀ v : TangentSpace I x, (LeviCivita (S.family.metric t)) X x v = 0)
    (v : TangentSpace I x) : (LeviCivita (S.family.metric b)) X x v = 0 := by
  let : NeBot (𝓝[Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source, extChartAt_source]
    exact hchart hx
  apply LeviCivita_eq_zero_of_tendsto_chartChristoffel
    (fun t => S.family.metric t) (S.family.metric b) α hxgood hX _ hparallel v
  intro i j k
  exact (tendstoUniformlyOn_chartChristoffel_right_endpoint S hS R α hab hcarrier
    hregular hK hchart hU hUchart hUK hmetric hShi i j k).tendsto_at hxU

end DifferentialGeometry.PDE.RicciFlow
