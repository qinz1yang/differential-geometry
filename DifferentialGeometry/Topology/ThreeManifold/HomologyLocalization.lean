import DifferentialGeometry.Topology.Homology.ManifoldLocalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology

noncomputable section
open Set Module
open scoped Manifold ContDiff Topology
universe u
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem absoluteToRelative_family_injective
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [T2Space M] [CompactSpace M] :
    Function.Injective (fun a : IntegralHomology M 3 =>
      fun x : M => absoluteToRelative M ({x}ᶜ) 3 a) := by
  let uliftChart := (Homeomorph.ulift (X := ThreeSpace)).symm.toOpenPartialHomeomorph
  let : ChartedSpace (ULift.{u} ThreeSpace) M :=
    { atlas := (fun e : OpenPartialHomeomorph M ThreeSpace => e.trans uliftChart) ''
        atlas ThreeSpace M
      chartAt := fun x => (chartAt ThreeSpace x).trans uliftChart
      mem_chart_source := fun x => by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨mem_chart_source ThreeSpace x, trivial⟩
      chart_mem_atlas := fun x => ⟨chartAt ThreeSpace x, chart_mem_atlas ThreeSpace x, rfl⟩ }
  exact DifferentialGeometry.Topology.integralAbsoluteToRelative_family_injective
    (E := ULift.{u} ThreeSpace) 3 (by
      rw [(ULift.moduleEquiv (R := ℝ) (M := ThreeSpace)).finrank_eq]
      simp)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
