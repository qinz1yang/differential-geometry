import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff ENNReal _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

def asymptoticReducedVolume (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) : ℝ≥0∞ :=
  ⨅ tau : Set.Ioi (0 : ℝ), redVolume S T p tau

theorem asymptoticReducedVolume_le_redVolume
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M) {tau : ℝ} (htau : 0 < tau) :
    asymptoticReducedVolume S T p ≤ redVolume S T p tau :=
  iInf_le (fun r : Set.Ioi (0 : ℝ) => redVolume S T p r) ⟨tau, htau⟩

theorem redVolume_tendsto_atTop_of_antitone
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (p : M)
    (hmono : AntitoneOn (redVolume S T p) (Ioi 0)) :
    Tendsto (redVolume S T p) atTop (𝓝 (asymptoticReducedVolume S T p)) := by
  apply tendsto_comp_val_Ioi_atTop.mp
  exact tendsto_atTop_iInf (fun a b hab => hmono a.property b.property hab)

end DifferentialGeometry.PDE.RicciFlow.Perelman
