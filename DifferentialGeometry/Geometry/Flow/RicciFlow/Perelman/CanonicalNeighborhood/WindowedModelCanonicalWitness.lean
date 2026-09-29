import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedBufferedCanonical

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem exists_uniform_canonicalWitness_with_cap_neck_charts_of_windowedModelWitness
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 11) :
    ∃ C delta0 : ℝ, 1 ≤ C ∧ 0 < delta0 ∧ delta0 < 1 ∧
      ∀ (kappa : ℝ) (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → ∀ (delta : ℝ) (x : M) (t : ℝ)
          (W : WindowedModelWitness delta kappa S x t),
          delta ≤ delta0 → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
          TangentOrientationSection W.model.M →
            ∃ K : CanonicalWitness S alpha C C x t, K.capTubeHasNeckChart alpha := by
  obtain ⟨Cn, dn, hCn, hdn, hdn1, hnonround⟩ :=
    exists_universal_nonround_windowed_bufferedCanonical_with_cap_neck_charts.{u} ha hsmall 1
  obtain ⟨Cr, dr, hCr, hdr, hround⟩ :=
    exists_windowed_bufferedCanonical_with_cap_neck_charts_of_round_model.{u} ha hsmall 1
  refine ⟨max Cn Cr, min dn dr, hCn.trans (le_max_left _ _), lt_min hdn hdr,
    (min_le_left _ _).trans_lt hdn1, ?_⟩
  intro kappa M _ _ _ _ _ D S hS delta x t W hd hreg orient
  have key : ∀ C' : ℝ, C' ≤ max Cn Cr → (∃ B : BufferedCanonical S alpha C' 1 x t,
      B.witness.capTubeHasNeckChart alpha) →
      ∃ K : CanonicalWitness S alpha (max Cn Cr) (max Cn Cr) x t,
        K.capTubeHasNeckChart alpha := by
    rintro C' hC' ⟨B, hB⟩
    exact ⟨(B.canonicalWitnessMono B.tolerance_lt.le hsmall).enlargeConstants hC' hC',
      (hB.mono_eps B.tolerance_lt.le hsmall).enlarge_constants hC' hC'⟩
  by_cases hr : IsShrinkingSphericalSpaceFormFlow W.model
  · exact key Cr (le_max_right _ _) (hround W (hd.trans (min_le_right _ _)) hS hreg hr)
  · exact key Cn (le_max_left _ _)
      (hnonround kappa M D S hS delta x t W (hd.trans (min_le_left _ _)) hreg hr orient)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
