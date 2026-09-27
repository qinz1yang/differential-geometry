import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open Bundle Filter
open scoped Topology Manifold ContDiff BigOperators
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem tendsto_LeviCivita_apply_of_tendsto_chartChristoffel
    {ι : Type*} {l : Filter ι} (g : ι → SmoothRiemannianMetric I M)
    (g₀ : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {X : ∀ y : M, TangentSpace I y} (hX : MDiffAt (T% X) x)
    (hΓ : ∀ i j k, Tendsto
      (fun t => chartChristoffel (g t) α i j k (extChartAt I α x)) l
      (𝓝 (chartChristoffel g₀ α i j k (extChartAt I α x))))
    (v : TangentSpace I x) :
    Tendsto (fun t => (LeviCivita (g t)) X x v) l (𝓝 ((LeviCivita g₀) X x v)) := by
  simp_rw [LeviCivita_chart_apply _ α hx hX v, chartLeviCivita_apply _ α X hx v,
    christoffelCorrection_apply]
  apply ((trivFromE (I := I) α x).continuous.tendsto _).comp
  apply tendsto_const_nhds.add
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro k _
  exact (tendsto_const_nhds.mul (hΓ i j k)).smul tendsto_const_nhds

theorem LeviCivita_eq_zero_of_tendsto_chartChristoffel
    {ι : Type*} {l : Filter ι} [l.NeBot] (g : ι → SmoothRiemannianMetric I M)
    (g₀ : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    {X : ∀ y : M, TangentSpace I y} (hX : MDiffAt (T% X) x)
    (hΓ : ∀ i j k, Tendsto
      (fun t => chartChristoffel (g t) α i j k (extChartAt I α x)) l
      (𝓝 (chartChristoffel g₀ α i j k (extChartAt I α x))))
    (hparallel : ∀ᶠ t in l, ∀ v : TangentSpace I x, (LeviCivita (g t)) X x v = 0)
    (v : TangentSpace I x) : (LeviCivita g₀) X x v = 0 := by
  apply tendsto_nhds_unique (tendsto_LeviCivita_apply_of_tendsto_chartChristoffel
    g g₀ α hx hX hΓ v)
  exact tendsto_const_nhds.congr' (hparallel.mono fun t ht => (ht v).symm)

end DifferentialGeometry.Geometry.Connection
