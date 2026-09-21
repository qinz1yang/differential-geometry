import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckOverlap

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x y : M}

private theorem central_sphere_edist_le (nk : SpatialNeck g eps x)
    {z : M} (hz : z ∈ nk.map '' (univ ×ˢ ({0} : Set ℝ))) :
    riemannianEDistOf g x z ≤ ENNReal.ofReal (7 / Real.sqrt (metricScalarAt g x)) := by
  have hz' : z ∈ nk.map '' (univ ×ˢ Icc (-(0 : ℝ)) 0) := by simpa using hz
  have hb := nk.image_slab_subset_closedBall le_rfl (inv_pos.mpr nk.eps_pos) hz'
  have hnum : ((0 : ℝ) + 6) * Real.sqrt (1 + eps) ≤ 7 := by
    have hh := Real.sq_sqrt (by linarith [nk.eps_pos] : 0 ≤ 1 + eps)
    nlinarith [nk.eps_small, Real.sqrt_nonneg (1 + eps)]
  exact hb.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)))

private theorem central_sphere_mem_region (nk : SpatialNeck g eps x)
    {z : M} (hz : z ∈ nk.map '' (univ ×ˢ ({0} : Set ℝ))) :
    z ∈ nk.cylindricalChart.region univ := by
  obtain ⟨q, hq, rfl⟩ := hz
  have hsrc : q ∈ nk.cylindricalChart.domain := by
    have hq0 : q.2 = 0 := hq.2
    have hi := inv_pos.mpr nk.eps_pos
    exact ⟨hq.1, by rw [hq0]; constructor <;> linarith⟩
  exact ⟨nk.cylindricalChart.chart ⟨q, hsrc⟩, ⟨⟨q, hsrc⟩, mem_univ _, rfl⟩, rfl⟩

variable [T2Space M]

theorem SpatialNeck.disjoint_central_spheres_of_edist_gt
    (nk₀ : SpatialNeck g eps x) (nk₁ : SpatialNeck g eps y)
    (hsmall : eps < 1 / 1000000)
    (hfar : ENNReal.ofReal (21 / Real.sqrt (metricScalarAt g x)) < riemannianEDistOf g x y) :
    Disjoint (nk₀.map '' (univ ×ˢ ({0} : Set ℝ)))
      (nk₁.map '' (univ ×ˢ ({0} : Set ℝ))) := by
  apply Set.disjoint_left.mpr
  intro z hz₀ hz₁
  have hratio := nk₀.cylindricalChart.scale_ratio_of_metricCloseOn nk₁.cylindricalChart g
    eps (by linarith) nk₀.cylindricalChart_metricCloseOn nk₁.cylindricalChart_metricCloseOn z
    (central_sphere_mem_region nk₀ hz₀) (central_sphere_mem_region nk₁ hz₁)
  change |metricScalarAt g x / metricScalarAt g y - 1| ≤ 17292 * eps at hratio
  have hQ : metricScalarAt g x ≤ 4 * metricScalarAt g y := by
    have hh : metricScalarAt g x / metricScalarAt g y ≤ 4 := by
      linarith [(abs_le.mp hratio).2]
    exact (div_le_iff₀ nk₁.Q_pos).mp hh
  have hsQ : Real.sqrt (metricScalarAt g x) ≤ 2 * Real.sqrt (metricScalarAt g y) := by
    have hx := Real.sq_sqrt nk₀.Q_pos.le
    have hy := Real.sq_sqrt nk₁.Q_pos.le
    nlinarith [Real.sqrt_nonneg (metricScalarAt g x), Real.sqrt_nonneg (metricScalarAt g y)]
  have hdiv : 7 / Real.sqrt (metricScalarAt g y) ≤ 14 / Real.sqrt (metricScalarAt g x) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr nk₁.Q_pos) (Real.sqrt_pos.mpr nk₀.Q_pos)).mpr
    linarith
  have hother := (central_sphere_edist_le nk₁ hz₁).trans (ENNReal.ofReal_le_ofReal hdiv)
  rw [riemannianEDistOf_comm g y z] at hother
  have hh := (riemannianEDistOf_triangle g x z y).trans
    (add_le_add (central_sphere_edist_le nk₀ hz₀) hother)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div] at hh
  norm_num only at hh
  exact (not_lt_of_ge hh) hfar

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
