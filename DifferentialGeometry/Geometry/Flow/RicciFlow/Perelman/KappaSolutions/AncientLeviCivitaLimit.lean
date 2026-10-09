import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientConnectionContinuity
import DifferentialGeometry.Geometry.Connection.Convergence.Endpoint
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance ancientLeviCivitaC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem solution_leviCivita_continuousWithinAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b t : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (ht : t ≤ b) (σ : (x : M) → TangentSpace I x) (x : M)
    (hσ : MDifferentiableAt I (I.tangent) (fun y => TotalSpace.mk' E y (σ y)) x)
    (Y : TangentSpace I x) :
    ContinuousWithinAt
      (fun s => leviCivitaConnectionOfMetric (I := I) (S.base.metric s) σ x Y)
      (Iic b) t := by
  have hx := self_mem_chartLeviCivitaGoodSet (I := I) x
  have hcorr : ContinuousWithinAt
      (fun s => christoffelCorrection (I := I) (S.base.metric s) x x
        (chartESectionRepr (I := I) x σ x) Y) (Iic b) t := by
    simp_rw [christoffelCorrection_apply]
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      tendsto_finsetSum _ fun k _ => ?_
    exact (continuousWithinAt_const.mul
      (solution_chartChristoffel_continuousWithinAt S hS hcarrier hregular ht x
        (mem_extChartAt_target x) i j k)).smul continuousWithinAt_const
  have heq (s : ℝ) :
      leviCivitaConnectionOfMetric (I := I) (S.base.metric s) σ x Y =
        trivFromE (I := I) x x
          (fderiv ℝ (chartESectionRepr (I := I) x σ ∘ (extChartAt I x).symm)
              (extChartAt I x x) (trivToE (I := I) x x Y) +
            christoffelCorrection (I := I) (S.base.metric s) x x
              (chartESectionRepr (I := I) x σ x) Y) := by
    rw [← LeviCivita_eq_leviCivitaConnectionOfMetric,
      LeviCivita_chart_apply (S.base.metric s) x hx hσ Y,
      chartLeviCivita_apply (S.base.metric s) x σ hx Y]
  simp_rw [heq]
  exact (trivFromE (I := I) x x).continuous.continuousAt.comp_continuousWithinAt
    (continuousWithinAt_const.add hcorr)


theorem solution_leviCivita_mem_at_left_endpoint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (hab : a < b) (K : (x : M) → Submodule ℝ (TangentSpace I x))
    (σ : (x : M) → TangentSpace I x) (x : M)
    (hσ : MDifferentiableAt I (I.tangent) (fun y => TotalSpace.mk' E y (σ y)) x)
    (Y : TangentSpace I x)
    (hmem : ∀ s ∈ Ioo a b,
      leviCivitaConnectionOfMetric (I := I) (S.base.metric s) σ x Y ∈ K x) :
    leviCivitaConnectionOfMetric (I := I) (S.base.metric b) σ x Y ∈ K x := by
  exact covariantDerivative_mem_at_left_endpoint
    (fun s => leviCivitaConnectionOfMetric (I := I) (S.base.metric s)) K hab σ x Y
    ((solution_leviCivita_continuousWithinAt S hS hcarrier hregular le_rfl σ x hσ Y).mono
      Iio_subset_Iic_self) hmem

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
