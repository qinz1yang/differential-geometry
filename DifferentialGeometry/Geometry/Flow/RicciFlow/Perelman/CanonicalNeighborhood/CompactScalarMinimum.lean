import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem BackwardExtension.exists_scalar_le_one_of_compact
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    [CompactSpace L.space.M] {a : ℝ} {ha : a ≤ 0}
    (B : BackwardExtension L (RealTimeInterval.closed a 0 ha))
    {t : ℝ} (ht : t ∈ Icc a 0) :
    ∃ x : L.space.M, B.solution.scalar t x ≤ 1 := by
  obtain ⟨x, hx⟩ := exists_scalar_le_at_earlier_time_of_compact B.solution B.isSolution ht.2
    (show Icc t 0 ⊆ Icc a 0 from fun _ hu => ⟨ht.1.trans hu.1, hu.2⟩)
    (show Ioo t 0 ⊆ Ioo a 0 from fun _ hu => ⟨ht.1.trans_lt hu.1, hu.2⟩)
    L.space.basepoint
  refine ⟨x, ?_⟩
  have hterminal : B.solution.scalar 0 L.space.basepoint = 1 := by
    change metricScalarAt (B.solution.base.metric 0) L.space.basepoint = 1
    rw [B.terminal]
    exact L.scalar_one
  simpa only [hterminal] using hx

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
