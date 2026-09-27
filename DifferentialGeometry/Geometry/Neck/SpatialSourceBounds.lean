import DifferentialGeometry.Geometry.Neck.SpatialNormalization
import DifferentialGeometry.Geometry.Neck.ScaleComparison
import DifferentialGeometry.Geometry.Metric.PullbackScaling

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps δ : ℝ} {x : M}

theorem SpatialNeck.scalar_upper_bound_neckBuffer (nk : SpatialNeck g eps x)
    (hfit : δ⁻¹ + 1 ≤ eps⁻¹) (z : neckBuffer δ) :
    metricScalarAt g (nk.map z.val) ≤ (1 + 4323 * eps) * metricScalarAt g x := by
  obtain ⟨V, Φ, hmap, hbound⟩ := nk.exists_neckBuffer_pullback_bound hfit
  let C : Geometry.Neck.cylindricalChart I3 (M := M) :=
    { domain := neckBuffer δ
      target := V
      chart := Φ
      scale := metricScalarAt g x
      scale_pos := nk.Q_pos }
  have hinv : (2 : ℝ) ≤ eps⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ nk.eps_pos).2
    linarith [nk.eps_small]
  have hceil : 2 ≤ Nat.ceil eps⁻¹ := by
    exact_mod_cast hinv.trans (Nat.le_ceil eps⁻¹)
  have hclose : C.metricCloseOn g eps Set.univ := by
    intro y _ j hj
    change metricDerivNorm j
      (Diffeomorph.pullbackMetricCross
        (DifferentialGeometry.scaleMetric (metricScalarAt g x) nk.Q_pos (g.restrictOpen V)) Φ)
      _ _ y ≤ eps
    rw [Diffeomorph.pullbackMetricCross_scaleMetric, ← roundCylinderMetric_eq_geometry]
    exact hbound j (hj.trans hceil) y
  have hscalar := C.scalar_comparison_of_metricCloseOn g eps
    (by linarith [nk.eps_small]) hclose (Φ z : M)
    ⟨Φ z, ⟨z, Set.mem_univ _, rfl⟩, rfl⟩
  have hu := (abs_le.mp hscalar).2
  change metricScalarAt g (Φ z : M) / metricScalarAt g x - 1 ≤ 4323 * eps at hu
  rw [hmap] at hu
  apply (div_le_iff₀ nk.Q_pos).mp
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
