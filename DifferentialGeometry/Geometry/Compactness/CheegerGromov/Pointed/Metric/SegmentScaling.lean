import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scaling
import DifferentialGeometry.Geometry.Metric.Segment
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false
noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem PointedRiemannianManifold.exists_isometric_segment_scaleMetric
    (L : PointedRiemannianManifold.{u, uE, uH} I) (hL : PathConnectedSpace L.M)
    (c : ℝ) (hc : 0 < c) {rho : ℝ} (hrho : 0 < rho) :
    let _ : EMetricSpace L.M := L.emetricSpace
    ∀ g : C(Ico 0 rho, L.M), Isometry g → g ⟨0, le_rfl, hrho⟩ = L.basepoint →
      Tendsto (fun t => metricScalarAt L.metric (g t))
        (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop →
      let LB := L.scaleMetric c hc
      let _ : PathConnectedSpace LB.M := hL
      let _ : EMetricSpace LB.M := LB.emetricSpace
      let _ : MetricSpace LB.M := EMetricSpace.toMetricSpace
        (fun x y => riemannianEDistOf_ne_top LB.metric x y)
      ∃ gB : C(Ico 0 (Real.sqrt c * rho), LB.M),
        (∀ t, gB t = g ⟨t / Real.sqrt c,
          div_nonneg t.property.1 (Real.sqrt_nonneg c),
          (div_lt_iff₀ (Real.sqrt_pos.mpr hc)).mpr (by simpa [mul_comm] using t.property.2)⟩) ∧
        Isometry gB ∧ gB ⟨0, le_rfl, mul_pos (Real.sqrt_pos.mpr hc) hrho⟩ = LB.basepoint ∧
        Tendsto (fun t => metricScalarAt LB.metric (gB t))
          (comap (Subtype.val : Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho))) atTop ∧
        ∃ q : UniformSpace.Completion LB.M,
          Tendsto (fun t => (gB t : UniformSpace.Completion LB.M))
            (comap (Subtype.val : Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho))) (𝓝 q) ∧
          (∀ t : Ico 0 (Real.sqrt c * rho),
            dist q (gB t : UniformSpace.Completion LB.M) = Real.sqrt c * rho - t) ∧
          q ∉ range (fun x : LB.M => (x : UniformSpace.Completion LB.M)) := by
  let _ : EMetricSpace L.M := L.emetricSpace
  dsimp only
  intro g hg hbase hblow
  let LB := L.scaleMetric c hc
  let _ : PathConnectedSpace LB.M := hL
  let _ : EMetricSpace LB.M := LB.emetricSpace
  let _ : MetricSpace LB.M := EMetricSpace.toMetricSpace
    (fun x y => riemannianEDistOf_ne_top LB.metric x y)
  have hk := Real.sqrt_pos.mpr hc
  let d : Ico 0 (Real.sqrt c * rho) → Ico 0 rho := fun t =>
    ⟨t / Real.sqrt c, div_nonneg t.property.1 hk.le,
      (div_lt_iff₀ hk).mpr (by simpa [mul_comm] using t.property.2)⟩
  have hdcont : Continuous d := (continuous_subtype_val.div_const _).subtype_mk _
  let gB : C(Ico 0 (Real.sqrt c * rho), LB.M) := ⟨fun t => g (d t), g.continuous.comp hdcont⟩
  have hiso : Isometry gB := by
    intro s t
    change riemannianEDistOf (DifferentialGeometry.scaleMetric c hc L.metric) (g (d s)) (g (d t)) = edist s t
    rw [edistOf_scale]
    have hh := hg.edist_eq (d s) (d t)
    change riemannianEDistOf L.metric (g (d s)) (g (d t)) = _ at hh
    rw [hh]
    change ENNReal.ofReal (Real.sqrt c) * edist ((s : ℝ) / Real.sqrt c) ((t : ℝ) / Real.sqrt c) =
      edist (s : ℝ) (t : ℝ)
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← ENNReal.ofReal_mul hk.le]
    congr 1
    rw [← sub_div, abs_div, abs_of_pos hk, mul_div_cancel₀ _ hk.ne']
  have hbaseB : gB ⟨0, le_rfl, mul_pos hk hrho⟩ = LB.basepoint := by
    have hd0 : d ⟨0, le_rfl, mul_pos hk hrho⟩ = ⟨0, le_rfl, hrho⟩ :=
      Subtype.ext (zero_div _)
    change g (d ⟨0, le_rfl, mul_pos hk hrho⟩) = L.basepoint
    rw [hd0]
    exact hbase
  have hd : Tendsto d
      (comap (Subtype.val : Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho)))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) := by
    apply tendsto_comap_iff.mpr
    have hh := (tendsto_comap : Tendsto (Subtype.val : Ico 0 (Real.sqrt c * rho) → ℝ)
      (comap Subtype.val (𝓝 (Real.sqrt c * rho))) (𝓝 (Real.sqrt c * rho))).div_const (Real.sqrt c)
    simpa only [d, Function.comp_def, mul_div_cancel_left₀ rho hk.ne'] using hh
  have hblowB : Tendsto (fun t => metricScalarAt LB.metric (gB t))
      (comap (Subtype.val : Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho))) atTop := by
    have hh := (hblow.comp hd).const_mul_atTop (inv_pos.mpr hc)
    convert hh using 1
    funext t
    change metricScalarAt (DifferentialGeometry.scaleMetric c hc L.metric) (g (d t)) =
      c⁻¹ * metricScalarAt L.metric (g (d t))
    exact metricScalarAt_scaleMetric c hc L.metric (g (d t))
  have hmap : NeBot (map (Subtype.val : Ico 0 (Real.sqrt c * rho) → ℝ)
      (comap (Subtype.val : Ico 0 (Real.sqrt c * rho) → ℝ) (𝓝 (Real.sqrt c * rho)))) := by
    rw [map_comap_setCoe_val]
    exact right_nhdsWithin_Ico_neBot (mul_pos hk hrho)
  let _ := hmap.of_map
  obtain ⟨q, hq, hdist⟩ :=
    DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry (mul_pos hk hrho) hiso
  have hmissing : q ∉ range (fun x : LB.M => (x : UniformSpace.Completion LB.M)) := by
    rintro ⟨x, hx⟩
    exact (UniformSpace.Completion.ne_coe_of_tendsto_atTop
      (f := fun x => metricScalarAt LB.metric x) hq hblowB x
      (metricScalar_smooth LB.metric).continuous.continuousAt) hx.symm
  exact ⟨gB, fun _ => rfl, hiso, hbaseB, hblowB, q, hq, hdist, hmissing⟩

end DifferentialGeometry.CheegerGromovCompactness
