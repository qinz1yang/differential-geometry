import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Neck.SpatialChart

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {eps : ℝ} {p y : M}

theorem SpatialNeck.image_slab_subset_of_ball_subset
    {g : SmoothRiemannianMetric I3 M} (nk : SpatialNeck g eps p) (heps : eps ≤ 1 / 8646)
    (q : Sphere 2) {level : ℝ} (hlevel : |level| ≤ 4) (hy : nk.map (q, level) = y)
    {V : Set M}
    (hball : riemannianBallOf g y (1000 / Real.sqrt (metricScalarAt g y)) ⊆ V) :
    nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ V := by
  have hlen : (4 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
  have hscalar := nk.abs_scalar_ratio_sub_one_le
    (show (q, level) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ from
      ⟨mem_univ _, by constructor <;>
        linarith [(abs_le.mp hlevel).1, (abs_le.mp hlevel).2]⟩)
  rw [hy] at hscalar
  have hypos : 0 < metricScalarAt g y := by
    have hratio : 0 < metricScalarAt g y / metricScalarAt g p := by
      linarith [(abs_le.mp hscalar).1]
    exact (div_pos_iff.mp hratio).elim (fun h => h.1) (fun h => (nk.Q_pos.not_gt h.2).elim)
  have hQ : metricScalarAt g y ≤ 2 * metricScalarAt g p := by
    have hratio : metricScalarAt g y / metricScalarAt g p ≤ 2 := by
      linarith [(abs_le.mp hscalar).2]
    exact (div_le_iff₀ nk.Q_pos).mp hratio
  have hroot : Real.sqrt (metricScalarAt g y) ≤ 2 * Real.sqrt (metricScalarAt g p) := by
    nlinarith [Real.sq_sqrt hypos.le, Real.sq_sqrt nk.Q_pos.le,
      Real.sqrt_nonneg (metricScalarAt g y), Real.sqrt_nonneg (metricScalarAt g p)]
  have hepsroot : Real.sqrt (1 + eps) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + eps by linarith [nk.eps_pos]),
      Real.sqrt_nonneg (1 + eps)]
  let R := 20 * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt g p)
  have hRlt : R < 1000 / Real.sqrt (metricScalarAt g y) := by
    apply (div_lt_div_iff₀ (Real.sqrt_pos.mpr nk.Q_pos) (Real.sqrt_pos.mpr hypos)).mpr
    have hp := Real.sqrt_pos.mpr nk.Q_pos
    have hq := Real.sqrt_pos.mpr hypos
    have hprod := mul_le_mul hepsroot hroot (by positivity : 0 ≤ Real.sqrt (metricScalarAt g y))
      (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hybound := nk.image_slab_subset_closedBall (by norm_num : (0 : ℝ) ≤ 4) hlen
    ⟨(q, level), ⟨mem_univ _, abs_le.mp hlevel⟩, hy⟩
  rintro z ⟨w, hw, rfl⟩
  apply hball
  have hwbound := nk.image_slab_subset_closedBall (by norm_num : (0 : ℝ) ≤ 4) hlen
    ⟨w, hw, rfl⟩
  change riemannianEDistOf g p y ≤ _ at hybound
  change riemannianEDistOf g p (nk.map w) ≤ _ at hwbound
  have hyp : riemannianEDistOf g y p ≤
      ENNReal.ofReal ((4 + 6) * Real.sqrt (1 + eps) /
        Real.sqrt (metricScalarAt g p)) := by
    rw [riemannianEDistOf_comm]
    exact hybound
  have hdist := (riemannianEDistOf_triangle g y p (nk.map w)).trans
    (add_le_add hyp hwbound)
  have hsum : ENNReal.ofReal ((4 + 6) * Real.sqrt (1 + eps) /
      Real.sqrt (metricScalarAt g p)) +
      ENNReal.ofReal ((4 + 6) * Real.sqrt (1 + eps) /
      Real.sqrt (metricScalarAt g p)) = ENNReal.ofReal R := by
    have hn : 0 ≤ (4 + 6) * Real.sqrt (1 + eps) /
        Real.sqrt (metricScalarAt g p) :=
      div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    rw [← ENNReal.ofReal_add hn hn]
    congr 1
    dsimp only [R]
    ring
  exact (hdist.trans_eq hsum).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (div_pos (by norm_num) (Real.sqrt_pos.mpr hypos))).mpr hRlt)


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
