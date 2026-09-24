import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarDiameter
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

noncomputable section

open Manifold Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

theorem exists_uniform_spatial_neck_core_diameter :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (x : M)
      (nk : SpatialNeck g eps x),
      ∀ v ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10),
        ∀ w ∈ nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10),
          metricDistance g v w ≤ C / Real.sqrt (metricScalarAt g x) := by
  obtain ⟨D, hD, hband⟩ := exists_uniform_collar_band_diameter_of_axis (M := M)
  refine ⟨D + 40, by linarith, ?_⟩
  intro g eps x nk v hv w hw
  have hslab : (univ : Set (Sphere 2)) ×ˢ Icc (-10 : ℝ) 10 ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    have hi : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
      (by linarith [nk.eps_small])
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have haxis (p : Sphere 2) (z : ℝ) (hz : z ∈ Icc (-10 : ℝ) 10) :
      riemannianEDistOf (scaleMetric (metricScalarAt g x) nk.Q_pos g)
        (nk.map (p, z)) (nk.map (p, 0)) ≤ ENNReal.ofReal (20 : ℝ) := by
    have hax := collar_axial_edist_le nk.cylinder _ nk.map nk.comparison rfl
      nk.eps_pos.le (by simp) nk.domain hslab p hz
    have hsqrt : Real.sqrt (1 + eps) ≤ 2 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · norm_num
      · linarith [nk.eps_small]
    have habs : |z| ≤ 10 := abs_le.mpr hz
    exact hax.trans (ENNReal.ofReal_le_ofReal (by
      nlinarith [Real.sqrt_nonneg (1 + eps), abs_nonneg z]))
  have hbound := hband nk.cylinder (fun _ => nk.cylinder.metric 0)
    (fun _ => scaleMetric (metricScalarAt g x) nk.Q_pos g) nk.map
    (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) {0} (⌈eps⁻¹⌉₊) eps 20
    nk.comparison rfl nk.eps_pos.le (by linarith [nk.eps_small])
    (by simp) nk.domain hslab (by norm_num) haxis v hv w hw
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [edistOf_scale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ D + 2 * 20)] at hreal
  apply (le_div_iff₀ (Real.sqrt_pos.mpr nk.Q_pos)).mpr
  change (riemannianEDistOf g v w).toReal * Real.sqrt (metricScalarAt g x) ≤ D + 40
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
