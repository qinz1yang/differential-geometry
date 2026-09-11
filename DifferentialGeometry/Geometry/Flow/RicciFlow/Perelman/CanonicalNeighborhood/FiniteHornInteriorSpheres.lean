import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarNoReturn

set_option autoImplicit false
noncomputable section
open Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_exists_sphere_point_near_endpoint (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (x : W) {rho : ℝ} (hrho : 0 ≤ rho)
    (hr : rho < dist (x : UniformSpace.Completion W) H.endpoint) :
    ∃ y : W, dist x y = rho ∧
      dist (y : UniformSpace.Completion W) H.endpoint <
        2 * (dist (x : UniformSpace.Completion W) H.endpoint - rho) := by
  let r := dist (x : UniformSpace.Completion W) H.endpoint
  change rho < r at hr
  have hrpos : 0 < r := hrho.trans_lt hr
  let s : ℝ := min H.axial.length (r - rho) / 4
  have hs : 0 < s := div_pos (lt_min H.axial.length_pos (sub_pos.mpr hr)) (by norm_num)
  have hsL : s ≤ H.axial.length := by
    have h := min_le_left H.axial.length (r - rho)
    dsimp [s]
    linarith [H.axial.length_pos]
  have hsgap : 3 * s < r - rho := by
    have h := min_le_right H.axial.length (r - rho)
    dsimp [s]
    linarith
  have hsdom : s ∈ Ioc (0 : ℝ) H.axial.length := ⟨hs, hsL⟩
  have hupper : dist x (H.axial.point s) ≤ r + s := by
    have h := dist_triangle (x : UniformSpace.Completion W) H.endpoint
      (H.axial.point s : UniformSpace.Completion W)
    rw [UniformSpace.Completion.dist_eq, dist_comm H.endpoint,
      H.axial.radial s hsdom] at h
    exact h
  have hcross : rho < dist x (H.axial.point s) := by
    have h := dist_triangle (x : UniformSpace.Completion W)
      (H.axial.point s : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq, H.axial.radial s hsdom] at h
    change r ≤ dist x (H.axial.point s) + s at h
    linarith
  have hedist : riemannianEDistOf g x (H.axial.point s) < ENNReal.ofReal (r + 2 * s) := by
    rw [H.edist_eq_ofReal_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  obtain ⟨gamma, hstart, hend, hsmooth, hlength⟩ := exists_lt_of_edistOf_lt g hedist
  have hc : ContinuousOn (fun t => dist x (gamma t)) (Icc (0 : ℝ) 1) :=
    (continuous_const.dist continuous_id).comp_continuousOn hsmooth.continuousOn
  obtain ⟨t, ht, hxt⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
    (show rho ∈ Icc (dist x (gamma 0)) (dist x (gamma 1)) by
      simpa only [hstart, hend, dist_self, mem_Icc] using And.intro hrho hcross.le)
  change dist x (gamma t) = rho at hxt
  have hleft : ENNReal.ofReal rho ≤ metricPathELength g gamma 0 t := by
    have h := edistOf_le_metricPathELength g ht.1
      (hsmooth.mono (Icc_subset_Icc le_rfl ht.2))
    rw [hstart, H.edist_eq_ofReal_dist, hxt] at h
    exact h
  have hright : ENNReal.ofReal (dist (gamma t) (H.axial.point s)) ≤
      metricPathELength g gamma t 1 := by
    have h := edistOf_le_metricPathELength g ht.2
      (hsmooth.mono (Icc_subset_Icc ht.1 le_rfl))
    rw [hend, H.edist_eq_ofReal_dist] at h
    exact h
  have hsum := (add_le_add hleft hright).trans_eq (metricPathELength_add g gamma ht.1 ht.2)
  have hshort := hsum.trans_lt hlength
  rw [← ENNReal.ofReal_add hrho dist_nonneg] at hshort
  have hreal : rho + dist (gamma t) (H.axial.point s) < r + 2 * s :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hshort
  refine ⟨gamma t, hxt, ?_⟩
  have h := dist_triangle (gamma t : UniformSpace.Completion W)
    (H.axial.point s : UniformSpace.Completion W) H.endpoint
  rw [UniformSpace.Completion.dist_eq, H.axial.radial s hsdom] at h
  change dist (gamma t : UniformSpace.Completion W) H.endpoint < 2 * (r - rho)
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
