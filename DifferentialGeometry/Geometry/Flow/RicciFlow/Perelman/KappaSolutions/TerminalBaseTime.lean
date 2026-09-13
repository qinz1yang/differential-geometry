import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.RegularBaseTime

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

universe u uE uH

section Slab

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

omit [FiniteDimensional ℝ E] in
theorem terminal_icoSlab_subset_regular (tau : ℝ) :
    Set.Ico (0 - tau) 0 ⊆ ancientTimeInterval.regular := by
  intro t ht
  simpa only [ancientTimeInterval_regular, Set.mem_Iio] using ht.2

omit [FiniteDimensional ℝ E] in
theorem terminal_iccSlab_not_subset_regular {tau : ℝ} (htau : 0 ≤ tau) :
    ¬ Set.Icc (0 - tau) 0 ⊆ ancientTimeInterval.regular := by
  intro h
  have h0 : (0 : ℝ) ∈ Set.Icc (0 - tau) 0 := ⟨by linarith, le_rfl⟩
  have hlt : (0 : ℝ) < 0 := by
    simpa only [ancientTimeInterval_regular, Set.mem_Iio] using h h0
  exact absurd hlt (lt_irrefl 0)

end Slab

section Terminal

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance terminalBaseTimeTopology : TopologicalSpace F.M := F.topology
local instance terminalBaseTimeCharted : ChartedSpace H F.M := F.charted
local instance terminalBaseTimeSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalBaseTimeT2 : T2Space F.M := F.t2
local instance terminalBaseTimeSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem lExpPosDom_terminal_eq_empty (x : F.M) :
    lExpPosDom F.S 0 x = ∅ :=
  lExpPosDom_eq_empty_of_notMem_regular F.S 0 x (by simp)

theorem lMinDomain_terminal_eq_empty (x : F.M) :
    lMinDomain F.S 0 x = ∅ :=
  lMinDomain_eq_empty_of_notMem_regular F.S 0 x (by simp)

theorem lInjDomain_terminal_eq_empty (x : F.M) (tau : ℝ) :
    lInjDomain F.S 0 x tau = ∅ :=
  lInjDomain_eq_empty_of_notMem_regular F.S 0 x tau (by simp)

end Terminal

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
