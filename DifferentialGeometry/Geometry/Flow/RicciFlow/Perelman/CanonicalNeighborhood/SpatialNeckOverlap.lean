import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Neck.CrossSectionGraph

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M}
  {eps : ℝ} {x y : M}

private theorem neck_slab_subset_window {r : ℝ} (hr : r < eps⁻¹) :
    (univ : Set (Sphere 2)) ×ˢ Icc (-r) r ⊆ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
  intro z hz
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

variable [T2Space M]

theorem SpatialNeck.image_slab_subset_of_center_mem_slab
    (nk₀ : SpatialNeck g eps x) (nk₁ : SpatialNeck g eps y)
    (hsmall : eps < 1 / 1000000) {r₀ r₁ : ℝ}
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁)
    (hfit₀ : r₀ ≤ eps⁻¹ / 10) (hfit₁ : r₁ ≤ eps⁻¹ / 10)
    (hy : y ∈ nk₀.map '' (univ ×ˢ Icc (-r₀) r₀)) :
    nk₁.map '' (univ ×ˢ Icc (-r₁) r₁) ⊆
      nk₀.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
  have hi : (1000000 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk₀.eps_pos).mpr
    (by simpa only [one_div] using hsmall)
  have hr₀' : r₀ < eps⁻¹ := by linarith
  have hr₁' : r₁ < eps⁻¹ := by linarith
  have hratio : |metricScalarAt g y / metricScalarAt g x - 1| ≤ 4323 * eps := by
    obtain ⟨z, hz, rfl⟩ := hy
    exact nk₀.abs_scalar_ratio_sub_one_le (neck_slab_subset_window hr₀' hz)
  have hQ : metricScalarAt g x ≤ 4 * metricScalarAt g y := by
    have hl := (abs_le.mp hratio).1
    have hr : (1 : ℝ) / 2 ≤ metricScalarAt g y / metricScalarAt g x := by linarith
    have hh := (le_div_iff₀ nk₀.Q_pos).mp hr
    linarith [nk₁.Q_pos]
  have hsQ : Real.sqrt (metricScalarAt g x) ≤ 2 * Real.sqrt (metricScalarAt g y) := by
    have hx := Real.sq_sqrt nk₀.Q_pos.le
    have hy' := Real.sq_sqrt nk₁.Q_pos.le
    nlinarith [Real.sqrt_nonneg (metricScalarAt g x), Real.sqrt_nonneg (metricScalarAt g y)]
  let d₀ := (r₀ + 6) * Real.sqrt (1 + eps)
  let d₁ := (r₁ + 6) * Real.sqrt (1 + eps)
  have hd₀ : 0 ≤ d₀ := by dsimp only [d₀]; positivity
  have hd₁ : 0 ≤ d₁ := by dsimp only [d₁]; positivity
  have hdiv : d₁ / Real.sqrt (metricScalarAt g y) ≤
      2 * d₁ / Real.sqrt (metricScalarAt g x) := by
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr nk₁.Q_pos) (Real.sqrt_pos.mpr nk₀.Q_pos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsQ hd₁]
  have hroot : d₀ + 2 * d₁ < (eps⁻¹ / 2) * Real.sqrt (1 - eps) := by
    have hp : Real.sqrt (1 + eps) ≤ 11 / 10 := by
      have hh := Real.sq_sqrt (by linarith [nk₀.eps_pos] : 0 ≤ 1 + eps)
      nlinarith [Real.sqrt_nonneg (1 + eps)]
    have hm : 9 / 10 ≤ Real.sqrt (1 - eps) := by
      have hh := Real.sq_sqrt (by linarith : 0 ≤ 1 - eps)
      nlinarith [Real.sqrt_nonneg (1 - eps)]
    have hu := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ r₀ + 2 * r₁ + 18)
    have hl := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ eps⁻¹ / 2)
    dsimp only [d₀, d₁]
    nlinarith
  intro z hz
  apply image_mono (neck_slab_subset_window (by linarith : eps⁻¹ / 2 < eps⁻¹))
  apply nk₀.ball_subset_image_slab (by linarith : 0 < eps⁻¹ / 2) (by linarith)
  have hcenter := nk₀.image_slab_subset_closedBall hr₀ hr₀' hy
  have hpoint := nk₁.image_slab_subset_closedBall hr₁ hr₁' hz
  have hdist := (riemannianEDistOf_triangle g x y z).trans
    (add_le_add hcenter (hpoint.trans (ENNReal.ofReal_le_ofReal hdiv)))
  change riemannianEDistOf g x z ≤ ENNReal.ofReal (d₀ / Real.sqrt (metricScalarAt g x)) +
    ENNReal.ofReal (2 * d₁ / Real.sqrt (metricScalarAt g x)) at hdist
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_div] at hdist
  exact hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
    (div_pos (lt_of_le_of_lt (by positivity) hroot) (Real.sqrt_pos.mpr nk₀.Q_pos))).mpr
    (div_lt_div_of_pos_right hroot (Real.sqrt_pos.mpr nk₀.Q_pos)))

theorem SpatialNeck.exists_graph_in_nearby_neck
    (nk₀ : SpatialNeck g eps x) (nk₁ : SpatialNeck g eps y)
    (hsmall : eps < 1 / 1000000)
    (hy : y ∈ nk₀.map '' (univ ×ˢ Icc (-(eps⁻¹ / 10)) (eps⁻¹ / 10)))
    {t : ℝ} (ht : t ∈ Icc (-(eps⁻¹ / 10)) (eps⁻¹ / 10)) :
    ∃ (eta : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (a : Sphere 2 → ℝ),
      ContMDiff I2 𝓘(ℝ, ℝ) ∞ a ∧
      (∀ p, a p ∈ Ioo (-eps⁻¹) eps⁻¹) ∧
      ∀ p, nk₀.map (p, a p) = nk₁.map (eta p, t) := by
  have hi : 0 < eps⁻¹ := inv_pos.mpr nk₀.eps_pos
  have hsection (p : Sphere 2) : (p, t) ∈ nk₁.cylindricalChart.domain :=
    neck_slab_subset_window (by linarith : eps⁻¹ / 10 < eps⁻¹) ⟨mem_univ _, ht⟩
  have htarget (p : Sphere 2) :
      (nk₁.cylindricalChart.chart ⟨(p, t), hsection p⟩ : M) ∈ nk₀.cylindricalChart.target :=
    nk₀.image_slab_subset_of_center_mem_slab nk₁ hsmall
      (by positivity) (by positivity) le_rfl le_rfl hy ⟨(p, t), ⟨mem_univ _, ht⟩, rfl⟩
  obtain ⟨eta, a, ha, hmem, heq, _⟩ :=
    nk₁.cylindricalChart.exists_smoothTwoSidedCollar_of_full_cross_section_of_metric_close
      nk₀.cylindricalChart g t hsection htarget isOpen_univ isOpen_univ eps hsmall
      nk₁.cylindricalChart_metricCloseOn nk₀.cylindricalChart_metricCloseOn
      (fun _ => mem_univ _) (fun _ => mem_univ _) (by norm_num : (0 : ℝ) < 1)
  exact ⟨eta, a, ha, fun p => (hmem p).2, heq⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
