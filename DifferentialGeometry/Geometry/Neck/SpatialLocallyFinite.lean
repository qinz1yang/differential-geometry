import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Neck.SpatialChart
import DifferentialGeometry.Topology.LocallyFinite.Superlevel
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M}

theorem SpatialNeck.locallyFinite_of_scalar_tendsto_atTop
    {ι : Type*} {eps : ι → ℝ} {x : ι → M}
    (nk : ∀ i, SpatialNeck g (eps i) (x i))
    {eta : ℝ} (hsmall : eta < 1 / 4323) (heps : ∀ i, eps i ≤ eta)
    (hscalar : Tendsto (fun i => metricScalarAt g (x i)) cofinite atTop) :
    LocallyFinite (fun i => (nk i).map '' (univ ×ˢ Ioo (-(eps i)⁻¹) (eps i)⁻¹)) := by
  have hc : 0 < 1 - 4323 * eta := by linarith
  apply (metricScalar_smooth g).continuous.upperSemicontinuous.locallyFinite_of_tendsto_lower_bound
    (hscalar.const_mul_atTop hc)
  rintro i z ⟨p, hp, rfl⟩
  have hratio := (abs_le.mp ((nk i).abs_scalar_ratio_sub_one_le hp)).1
  have hlow : 1 - 4323 * eta ≤
      metricScalarAt g ((nk i).map p) / metricScalarAt g (x i) := by
    linarith [heps i]
  exact (le_div_iff₀ (nk i).Q_pos).mp hlow

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
