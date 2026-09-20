import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeMonotonicity



noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance normalizedSourceTopology : TopologicalSpace F.M := F.topology
local instance normalizedSourceCharted : ChartedSpace H F.M := F.charted
local instance normalizedSourceSmooth : IsManifold I ∞ F.M := F.smooth
local instance normalizedSourceT2 : T2Space F.M := F.t2
local instance normalizedSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact


theorem ancient_reducedVolume_antitone
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    AntitoneOn (intrinsicReducedVolume F.S 0 p) (Ioi 0) := by
  have hdim : Module.finrank ℝ E ≠ 0 := by
    intro hzero
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    have hb := ancientKappa_rmNormLeScalar_finrank F hF t ht x
    rw [hzero, Nat.cast_zero] at hb
    norm_num at hb
    have hn : 0 ≤ F.rmNormSq (I := I) t x := by
      simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
        DifferentialGeometry.Tensor0SBundle.normSq0S_nonneg
          (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
    have hz : Real.sqrt (F.rmNormSq (I := I) t x) = 0 :=
      le_antisymm hb (Real.sqrt_nonneg _)
    exact hx ((Real.sqrt_eq_zero hn).mp hz)
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  intro tau₁ h₁ tau₂ h₂ h₁₂
  apply le_of_tendsto_of_tendsto
    (ancient_reducedVolume_tendsto_terminal F hF h₂ p)
    (ancient_reducedVolume_tendsto_terminal F hF h₁ p)
  filter_upwards [self_mem_nhdsWithin] with T hT
  exact (ancient_reducedVolume_antitone_of_regular_base F hF p
    (T := T) hT) h₁ h₂ h₁₂

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
