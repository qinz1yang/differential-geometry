import DifferentialGeometry.Geometry.Collapse.LocalExport.CircleChart
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

/-!
A real three-dimensional plane-circle product with a small circle has a normalized circle chart.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology.Ehresmann
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

abbrev CircleModel := EuclideanSpace ℝ (Fin 2) × Circle

@[instance_reducible]
def circleModelMetric : MetricSpace CircleModel :=
  (inferInstance : MetricSpace CircleModel).rescale (1 / 2) (by norm_num)

local instance (priority := 2000) modelMetric : MetricSpace CircleModel := circleModelMetric

local instance (priority := 2000) modelPseudoMetric : PseudoMetricSpace CircleModel :=
  circleModelMetric.toPseudoMetricSpace

local instance (priority := 2000) modelPseudoEMetric : PseudoEMetricSpace CircleModel :=
  circleModelMetric.toPseudoEMetricSpace

abbrev circleModelCorners := (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod (𝓡 1)

theorem circleModel_dist (x y : CircleModel) :
    dist x y = (1 / 2) * max (dist x.1 y.1) (dist x.2 y.2) := by
  exact MetricSpace.rescale_dist (Prod.metricSpaceMax) (1 / 2) (by norm_num) x y

private theorem circle_dist_le_two (t s : Circle) : dist t s ≤ 2 := by
  change dist (t : ℂ) (s : ℂ) ≤ 2
  rw [dist_eq_norm]
  simpa only [Circle.norm_coe, one_add_one_eq_two] using norm_sub_le (t : ℂ) (s : ℂ)

theorem circleModel_mem_ball (z : EuclideanSpace ℝ (Fin 2)) (t : Circle)
    (hz : ‖z‖ < 100) : (z, t) ∈ ball (0, (1 : Circle)) (200 : ℝ) := by
  rw [mem_ball, circleModel_dist, dist_zero_right]
  have ht := circle_dist_le_two t 1
  have hm : max ‖z‖ (dist t 1) < 400 := max_lt (by linarith) (by linarith)
  nlinarith

theorem circleModel_rank (x : CircleModel) :
    Surjective (mfderiv circleModelCorners 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Prod.fst x) := by
  rw [mfderiv_fst]
  exact fun v => ⟨(v, 0), rfl⟩

private theorem circleModel_fst_smooth :
    ContMDiff circleModelCorners 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      (Prod.fst : CircleModel → EuclideanSpace ℝ (Fin 2)) := contMDiff_fst

abbrev circleModelDomain : TopologicalSpace.Opens CircleModel :=
  diskPreimageOpens (ball (0, (1 : Circle)) 200) isOpen_ball
    (Prod.fst : CircleModel → EuclideanSpace ℝ (Fin 2))
      circleModel_fst_smooth.continuous.continuousOn 100

def circleModelProjection : circleModelDomain → planeBallOpens 100 :=
  diskPreimageMap (ball (0, (1 : Circle)) 200) isOpen_ball Prod.fst
    circleModel_fst_smooth.continuous.continuousOn 100

def circleModelProductHomeomorph : circleModelDomain ≃ₜ (planeBallOpens 100 × Circle) where
  toFun x := (circleModelProjection x, x.val.2)
  invFun p := ⟨(p.1.val, p.2),
    ⟨circleModel_mem_ball p.1.val p.2 (mem_planeBallOpens_iff.mp p.1.property),
      p.1.property⟩⟩
  left_inv _x := rfl
  right_inv _p := rfl
  continuous_toFun := (continuous_diskPreimageMap isOpen_ball _ 100).prodMk
    (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) _

theorem circleModelProjection_proper : IsProperMap circleModelProjection :=
  isProperMap_fst_of_compactSpace.comp circleModelProductHomeomorph.isProperMap

theorem circleModelProjection_surjective : Surjective circleModelProjection := by
  intro z
  exact ⟨circleModelProductHomeomorph.symm (z, 1), rfl⟩

theorem circleModelProjection_fibres (z : planeBallOpens 100) :
    IsCompact (circleModelProjection ⁻¹' {z}) ∧
      IsConnected (circleModelProjection ⁻¹' {z}) := by
  refine ⟨circleModelProjection_proper.isCompact_preimage isCompact_singleton, ?_⟩
  have he : circleModelProjection ⁻¹' {z} =
      range (fun t : Circle => circleModelProductHomeomorph.symm (z, t)) := by
    ext x
    constructor
    · intro hx
      refine ⟨x.val.2, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg Subtype.val (show circleModelProjection x = z from hx).symm
      · rfl
    · rintro ⟨t, rfl⟩
      rfl
  rw [he]
  exact isConnected_range (circleModelProductHomeomorph.symm.continuous.comp
    (continuous_const.prodMk continuous_id))

def standardCircleChart : CircleChart circleModelCorners CircleModel where
  center := (0, 1)
  coord := Prod.fst
  contMDiffOn_coord := circleModel_fst_smooth.contMDiffOn
  rank x hx := circleModel_rank x
  lipschitz := by
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [circleModel_dist]
    change dist x.1 y.1 ≤ (2 : ℝ) * ((1 / 2) * max (dist x.1 y.1) (dist x.2 y.2))
    ring_nf
    exact le_max_left _ _
  coord_center := rfl
  enclosure := by
    intro x hx hnorm
    rw [mem_ball, circleModel_dist, dist_zero_right]
    have ht := circle_dist_le_two x.2 1
    have hm : max ‖x.1‖ (dist x.2 1) < 204 := max_lt (by linarith) (by linarith)
    linarith
  zero_enclosure := by
    intro x hx hzero
    rw [mem_ball, circleModel_dist, hzero, dist_self]
    have ht := circle_dist_le_two x.2 1
    rw [max_eq_right dist_nonneg]
    linarith
  isProperMap := circleModelProjection_proper
  surjective := circleModelProjection_surjective
  fibres := circleModelProjection_fibres
  trivial := by
    intro R hR hRr
    let instLocal : LocallyCompactSpace circleModelDomain :=
      circleModelDomain.isOpen.locallyCompactSpace
    exact exists_trivialization_over_planeBall_of_proper circleModelProjection
      (contMDiff_diskPreimageMap isOpen_ball circleModel_fst_smooth.contMDiffOn 100)
      circleModelProjection_proper
      (fun x => surjective_mfderiv_diskPreimageMap isOpen_ball
        circleModel_fst_smooth.contMDiffOn (fun y hy => circleModel_rank y) 100 x) hR hRr

theorem standardCircleChart_dimension :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) = 3 := by
  simp

theorem standardCircleChart_fibre :
    let f := diskPreimageMap (ball standardCircleChart.center 200) isOpen_ball
      standardCircleChart.coord standardCircleChart.contMDiffOn_coord.continuousOn 100
    let z : planeBallOpens 100 := ⟨0, by simp [planeBallOpens]⟩
    let instFibre := DifferentialGeometry.Topology.Manifold.regularFiberChartedSpace f z
      standardCircleChart.contMDiff_restrict
      (fun x _hx => standardCircleChart.surjective_mfderiv_restrict x)
    Nonempty (Circle ≃ₘ⟮𝓡 1,
      𝓘(ℝ, Fin (Module.finrank ℝ
        (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) -
          Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) → ℝ)⟯ {x // f x = z}) :=
  standardCircleChart.nonempty_circle_diffeomorph standardCircleChart_dimension _

end DifferentialGeometry.Geometry.Collapse
