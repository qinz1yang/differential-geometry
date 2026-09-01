import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrectionZeroMixedConnectionExpansion

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem reindexedPureTrace_sub
    (g gT gU : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) :
    reindexedPureTrace (I := I) (M := M) g gT p σ -
      reindexedPureTrace (I := I) (M := M) g gU p σ =
      reindexCoeffGen (I := I) (M := M) g (p + 2) p
        (pureTrace (I := I) (M := M) g gT p -
          pureTrace (I := I) (M := M) g gU p) σ := by
  rw [reindexedPureTrace, reindexedPureTrace, ← reindexCoeffGen_sub]

omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_reindexedPureTrace
    (g gm : SmoothRiemannianMetric I M) (p m : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) :
    covariantJetNormSq (I := I) (M := M) g m
        (reindexedPureTrace (I := I) (M := M) g gm p σ) =
      covariantJetNormSq (I := I) (M := M) g m
        (pureTrace (I := I) (M := M) g gm p) := by
  rw [reindexedPureTrace, covariantJetNormSq_reindexCoeffGen]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
