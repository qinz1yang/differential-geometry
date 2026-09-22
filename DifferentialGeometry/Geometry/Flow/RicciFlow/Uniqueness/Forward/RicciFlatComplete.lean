import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.BufferedReference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem metric_eq_of_ricci_flat_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b u v : ℝ} (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (huv : u ≤ v)
    (hreg : Ioo a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ Ioo a b, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ r s, a < r → r < s → s < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc r s, ∀ x : M,
        normSq0S (I := I) (S.family.metric t) x 4
          (metricRm04At (S.family.metric t) x) ≤ C)
    (hRicci : ∀ (x : M) (w z : TangentSpace I x),
      ricciTensor (S.family.metric u) x w z = 0) :
    S.family.metric v = S.family.metric u := by
  obtain ⟨c, hvc, hcb⟩ := exists_between hv.2
  have huc : u < c := huv.trans_lt hvc
  let U := SolutionOn.const (S.family.metric u) (RealTimeInterval.closedOpen u c huc)
  have hU : IsSolutionOn U :=
    isSolutionOn_const_of_ricciTensor_eq_zero (S.family.metric u) hRicci _
  obtain ⟨C, hC, hcurv⟩ := hbound u c hu.1 huc hcb
  have hUbound : ∀ t ∈ Ico u c, ∀ x : M,
      normSq0S (U.base.metric t) x 4 (U.base.rm04 t x) ≤ C := by
    intro t _ x
    exact hcurv u ⟨le_rfl, huc.le⟩ x
  have heq := forward_unique_on_closedOpen_of_complete_bounded_curvature_of_buffered_reference
    huc U S hU hS hu hcb hreg hcomplete hbound hC hUbound rfl
  exact (heq v ⟨huv, hvc⟩).symm

end DifferentialGeometry.PDE.RicciFlow
