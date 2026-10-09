import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.UniformNonroundWindowedBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedRoundCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointNeckArmReduction

noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (delta : ℝ) (o : TangentOrientationSection M) (x : M) (t : ℝ),
          delta ≤ delta0 → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          OrientedWitness S o delta kappa x t →
            ∃ B : BufferedCanonical S alpha C H x t, B.witness.capTubeHasNeckChart alpha := by
  obtain ⟨Cn, dn, hCn, hdn, hdn1, hnonround⟩ :=
    exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts.{u} ha hsmall H
  obtain ⟨Cr, dr, hCr, hdr, hround⟩ := exists_windowed_bufferedCanonical_with_cap_neck_charts_of_round_model ha hsmall H
  refine ⟨max Cn Cr + 1, min dn dr, by linarith [le_max_left Cn Cr], lt_min hdn hdr,
    (min_le_left _ _).trans_lt hdn1, ?_⟩
  intro kappa M _ _ _ _ _ D S hS delta o x t hd hreg hw
  obtain ⟨W, orient, _⟩ := hw
  by_cases hr : IsShrinkingSphericalSpaceFormFlow W.model
  · obtain ⟨B, hB⟩ := hround W (hd.trans (min_le_right _ _)) hS hreg hr
    refine ⟨B.enlargeConstants (by linarith [le_max_right Cn Cr]), ?_⟩
    exact hB.enlarge_constants (by linarith [le_max_right Cn Cr])
      (by linarith [le_max_right Cn Cr])
  · obtain ⟨B, hB⟩ := hnonround kappa M D S hS delta x t W
      (hd.trans (min_le_left _ _)) hreg hr orient
    refine ⟨B.enlargeConstants (by linarith [le_max_left Cn Cr]), ?_⟩
    exact hB.enlarge_constants (by linarith [le_max_left Cn Cr])
      (by linarith [le_max_left Cn Cr])


theorem exists_uniform_windowed_bufferedCanonical
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 11) (H : ℝ) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (delta : ℝ) (o : TangentOrientationSection M) (x : M) (t : ℝ),
          delta ≤ delta0 → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          OrientedWitness S o delta kappa x t → Nonempty (BufferedCanonical S alpha C H x t) := by
  obtain ⟨C, delta0, hC, hd, hd1, hmain⟩ :=
    exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts.{u} ha hsmall H
  refine ⟨C, delta0, hC, hd, hd1, ?_⟩
  intro kappa M _ _ _ _ _ D S hS delta o x t hd hreg hw
  obtain ⟨B, _⟩ := hmain kappa M D S hS delta o x t hd hreg hw
  exact ⟨B⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
