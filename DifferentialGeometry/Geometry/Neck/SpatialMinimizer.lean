import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Topology.MetricSpace.GeodesicSeparator
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

noncomputable section

open Set Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {g : SmoothRiemannianMetric I3 M} {δ α : ℝ} {v : M}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem SpatialNeck.exists_at_minimizing_point_of_frontier_eq_slice
    (nk : SpatialNeck g δ v)
    (hα : α < 1 / 11) (hreserve : 13000 * δ ≤ α)
    {K : Set M} (hfront : frontier K = range (fun z : Sphere 2 => nk.map (z, 1 / 2)))
    {γ : ℝ → M} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hmin : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b, riemannianEDistOf g (γ s) (γ u) = ENNReal.ofReal |s - u|)
    (ha : γ a ∉ interior K) (hb : γ b ∉ interior K) (ht : γ t ∈ interior K) :
    Nonempty (SpatialNeck g α (γ t)) := by
  have hδ : δ < 1 / 20000 := by linarith
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I3
  let _ : RegularSpace M := inferInstance
  let _ : Bundle.RiemannianBundle (TangentSpace I3 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (TangentSpace I3 : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I3 M
  by_cases hband : γ t ∈ nk.map '' (univ ×ˢ Icc (-50 : ℝ) 50)
  · obtain ⟨⟨z, w⟩, hw, heq⟩ := hband
    have hshift : |w| * δ ≤ 1 / 2 := by
      have habs : |w| ≤ 50 := abs_le.mpr hw.2
      have hh := mul_le_mul_of_nonneg_right habs nk.eps_pos.le
      nlinarith
    obtain ⟨N, _, _⟩ := nk.exists_at_coordinate_of_tolerance hα hreserve z hshift
    exact heq ▸ ⟨N⟩
  · have hlen : (50 : ℝ) < δ⁻¹ := by
      apply (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
      linarith
    have hroot : 0 < Real.sqrt (metricScalarAt g v) := Real.sqrt_pos.mpr nk.Q_pos
    have hrootlow : 9 / 10 ≤ Real.sqrt (1 - δ) := by
      apply (Real.le_sqrt (by norm_num) (by linarith [nk.eps_pos])).mpr
      nlinarith
    have hfar : ENNReal.ofReal (45 / Real.sqrt (metricScalarAt g v)) ≤
        riemannianEDistOf g v (γ t) := by
      have hnot : ¬ riemannianEDistOf g v (γ t) <
          ENNReal.ofReal (50 * Real.sqrt (1 - δ) / Real.sqrt (metricScalarAt g v)) := by
        intro hnear
        exact hband (nk.ball_subset_image_slab (by norm_num : (0 : ℝ) < 50) hlen hnear)
      exact (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by linarith) hroot.le)).trans (le_of_not_gt hnot)
    have hboundary (z) (hz : z ∈ frontier K) : edist v z ≤ ENNReal.ofReal (14 / Real.sqrt (metricScalarAt g v)) := by
      rw [hfront] at hz
      obtain ⟨w, rfl⟩ := hz
      have hbound := nk.image_slab_subset_closedBall (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (1 : ℝ) < δ⁻¹) ⟨(w, 1 / 2), ⟨mem_univ _, by norm_num⟩, rfl⟩
      have hsqrt : Real.sqrt (1 + δ) ≤ 2 := by
        apply (Real.sqrt_le_iff).mpr
        constructor
        · norm_num
        · linarith [nk.eps_pos]
      have hnum : (1 + 6) * Real.sqrt (1 + δ) / Real.sqrt (metricScalarAt g v) ≤
          14 / Real.sqrt (metricScalarAt g v) :=
        div_le_div_of_nonneg_right (by linarith) hroot.le
      exact hbound.trans (ENNReal.ofReal_le_ofReal hnum)
    have hgap : ENNReal.ofReal (2 * (14 / Real.sqrt (metricScalarAt g v))) < edist v (γ t) := by
      have hstrict : 2 * (14 / Real.sqrt (metricScalarAt g v)) <
          45 / Real.sqrt (metricScalarAt g v) := by
        rw [← mul_div_assoc]
        exact div_lt_div_of_pos_right (by norm_num) hroot
      exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hstrict).trans_le hfar
    exact False.elim ((EMetric.not_mem_interior_of_minimizing_of_frontier_edist_lt hat htb hmin ha hb
      (fun x hx y hy => EMetric.edist_lt_edist_add_edist_of_close_to_center (by positivity)
        (hboundary x hx) (hboundary y hy) hgap)) ht)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
