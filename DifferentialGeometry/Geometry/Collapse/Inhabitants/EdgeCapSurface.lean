import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Curvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Curvature.ContinuousEvaluation
import DifferentialGeometry.Geometry.Metric.Completeness.ProperMap
import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.InnerProductSpace.PiL2
/-! A complete nonnegatively curved capped plane from the actual standard-cap metric. -/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff InnerProductSpace Topology
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry.Collapse.EdgeCapSurface

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E3 := EuclideanSpace ℝ (Fin 3)
open DifferentialGeometry.PDE.RicciFlow.StandardCap (metric)
def planeMap : E2 →L[ℝ] E3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _i : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 3 =>
      if i = 0 then PiLp.proj 2 (fun _j : Fin 2 => ℝ) 0
      else if i = 1 then PiLp.proj 2 (fun _j : Fin 2 => ℝ) 1 else 0))
theorem planeMap_inner (x y : E2) : ⟪planeMap x, planeMap y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_succ, planeMap]
def planeEmbedding : E2 →ₗᵢ[ℝ] E3 where
  toLinearMap := planeMap.toLinearMap
  norm_map' x := by
    change ‖planeMap x‖ = ‖x‖
    have h := planeMap_inner x x
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (planeMap x), norm_nonneg x]
theorem planeMap_mfderiv (x : E2) : mfderiv (𝓡 2) (𝓡 3) planeMap x = planeMap := by
  rw [mfderiv_eq_fderiv]
  exact planeMap.fderiv

def surfaceMetric : SmoothRiemannianMetric (𝓡 2) E2 :=
  metric.pullback planeMap planeMap.contDiff.contMDiff
    (fun x => by rw [planeMap_mfderiv]; exact planeEmbedding.injective)
theorem surfaceMetric_inner (x v w : E2) :
    surfaceMetric.inner x v w = metric.inner (planeMap x) (planeMap v) (planeMap w) := by
  change metric.inner (planeMap x) (mfderiv (𝓡 2) (𝓡 3) planeMap x v)
    (mfderiv (𝓡 2) (𝓡 3) planeMap x w) = _
  rw [planeMap_mfderiv]
  rfl

def surfaceTargets : Prop :=
  DifferentialGeometry.RiemannianMetricComplete surfaceMetric ∧
    (∀ x : E2, SectionalBoundedBelowAt surfaceMetric x 0) ∧
    Nonempty (ManifoldOrientation (𝓡 2) E2 2)

theorem surfaceOrientation : Nonempty (ManifoldOrientation (𝓡 2) E2 2) :=
  DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_of_simply_connected (by simp)

theorem surfaceMetric_inner_radial {x : E2} (hx : x ≠ 0) (v w : E2) :
    surfaceMetric.inner x v w =
      radialBilinearField DifferentialGeometry.PDE.RicciFlow.StandardCap.warpingFunction x v w := by
  have hF : planeMap x ≠ 0 := by
    intro h
    apply hx
    apply planeEmbedding.injective
    change planeMap x = planeMap 0
    simpa using h
  have hn : ‖planeMap x‖ = ‖x‖ := planeEmbedding.norm_map x
  rw [surfaceMetric_inner,
    DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_inner_of_ne_zero hF]
  simp only [radialBilinearField_apply, hn, planeMap_inner]
theorem surfaceRm_away {x : E2} (hx : x ≠ 0) (u v : E2) :
    0 ≤ metricRm04StandardAt surfaceMetric x u v v u := by
  have hg : (fun y : E2 => tangentBilinearFormToModel y (surfaceMetric.inner y)) =ᶠ[𝓝 x]
      radialBilinearField DifferentialGeometry.PDE.RicciFlow.StandardCap.warpingFunction := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    ext a b
    exact surfaceMetric_inner_radial hy a b
  apply metricRm04StdAt_radialBilinearField_nonneg surfaceMetric hg
    DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_warpingFunction hx
    (DifferentialGeometry.PDE.RicciFlow.StandardCap.warpingFunction_pos (norm_pos_iff.mpr hx))
    (DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_warpingFunction_nonpos
      (norm_nonneg x))
  rw [abs_of_nonneg
    (DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_nonneg (norm_nonneg x))]
  exact DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_le_one ‖x‖

theorem surfaceRm_nonneg (x u v : E2) : 0 ≤ metricRm04StandardAt surfaceMetric x u v v u := by
  have hslot (a : E2) :
      Continuous (fun y : E2 => (⟨y, a⟩ : TangentBundle (𝓡 2) E2)) := by
    exact (tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hc : Continuous (fun y : E2 => metricRm04StandardAt surfaceMetric y u v v u) :=
    DifferentialGeometry.Geometry.continuous_sectional_contraction surfaceMetric id continuous_id
      (fun _y => u) (fun _y => v) (hslot u) (hslot v)
  have hclosed : IsClosed {y : E2 | 0 ≤ metricRm04StandardAt surfaceMetric y u v v u} :=
    isClosed_Ici.preimage hc
  have hsub : ({(0 : E2)}ᶜ : Set E2) ⊆
      {y : E2 | 0 ≤ metricRm04StandardAt surfaceMetric y u v v u} := by
    intro y hy
    exact surfaceRm_away (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy) u v
  have hclosure := hclosed.closure_subset_iff.mpr hsub
  rw [closure_compl_singleton] at hclosure
  exact hclosure (Set.mem_univ x)
theorem surfaceSectional (x : E2) : SectionalBoundedBelowAt surfaceMetric x 0 := by
  intro u v
  simpa only [zero_mul] using surfaceRm_nonneg x u v

def smoothRadius (x : E2) : ℝ := Real.sqrt (1 + ‖x‖ ^ 2)
theorem smoothRadius_contDiff : ContDiff ℝ ∞ smoothRadius := by
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun x => by positivity)
theorem norm_le_smoothRadius (x : E2) : ‖x‖ ≤ smoothRadius x := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + ‖x‖ ^ 2 by positivity)
  have h0 := Real.sqrt_nonneg (1 + ‖x‖ ^ 2)
  dsimp [smoothRadius]
  nlinarith [norm_nonneg x]
theorem smoothRadius_isProper : IsProperMap smoothRadius := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨smoothRadius_contDiff.continuous, ?_⟩
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  apply (isCompact_closedBall (0 : E2) R).of_isClosed_subset
    (hK.isClosed.preimage smoothRadius_contDiff.continuous)
  intro x hx
  have hr : dist (smoothRadius x) 0 ≤ R := hR hx
  have hf0 : 0 ≤ smoothRadius x := Real.sqrt_nonneg _
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hf0] at hr
  simpa only [Metric.mem_closedBall, dist_zero_right] using (norm_le_smoothRadius x).trans hr

theorem smoothRadius_mfderiv (x v : E2) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) smoothRadius x v = ⟪x, v⟫_ℝ / smoothRadius x := by
  have hs : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hf := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1).sqrt hs.ne'
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (fun y : E2 => Real.sqrt (1 + ‖y‖ ^ 2)) x v = _
  rw [hf.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, smoothRadius]
  ring

theorem smoothRadius_fderiv (x v : E2) :
    fderiv ℝ smoothRadius x v = ⟪x, v⟫_ℝ / smoothRadius x := by
  have h := smoothRadius_mfderiv x v
  rw [mfderiv_eq_fderiv] at h
  change fderiv ℝ smoothRadius x v = _ at h
  exact h
theorem smoothRadius_speed_bound (x v : E2) :
    ‖fderiv ℝ smoothRadius x v‖ ≤
      Real.sqrt (surfaceMetric.inner x v v) := by
  rw [smoothRadius_fderiv, Real.norm_eq_abs]
  by_cases hx : x = 0
  · subst x
    simp only [inner_zero_left, zero_div, abs_zero]
    exact Real.sqrt_nonneg _
  · have hF : planeMap x ≠ 0 := by
      intro h
      apply hx
      apply planeEmbedding.injective
      change planeMap x = planeMap 0
      simpa using h
    have hn : ‖planeMap x‖ = ‖x‖ := planeEmbedding.norm_map x
    have hrad : (⟪x, v⟫_ℝ / ‖x‖) ^ 2 ≤ surfaceMetric.inner x v v := by
      have h := DifferentialGeometry.PDE.RicciFlow.StandardCap.inner_sq_le_metric hF (planeMap v)
      simpa only [NormedSpace.normalize, real_inner_smul_left, hn, planeMap_inner,
        surfaceMetric_inner, div_eq_mul_inv, mul_comm] using h
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hmul : ⟪x, v⟫_ℝ ^ 2 ≤ surfaceMetric.inner x v v * ‖x‖ ^ 2 :=
      (div_le_iff₀ (sq_pos_of_pos hnorm)).mp (by simpa only [div_pow] using hrad)
    have hg : 0 ≤ surfaceMetric.inner x v v := metric_inner_self_nonneg surfaceMetric x v
    have hs : 0 < smoothRadius x := Real.sqrt_pos.mpr (by positivity)
    have hs2 : smoothRadius x ^ 2 = 1 + ‖x‖ ^ 2 := Real.sq_sqrt (by positivity)
    have hdf2 : |⟪x, v⟫_ℝ / smoothRadius x| ^ 2 ≤ surfaceMetric.inner x v v := by
      rw [sq_abs, div_pow]
      apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
      rw [hs2]
      nlinarith
    have hg2 := Real.sq_sqrt hg
    have h0 := Real.sqrt_nonneg (surfaceMetric.inner x v v)
    nlinarith [abs_nonneg (⟪x, v⟫_ℝ / smoothRadius x)]
theorem surfaceComplete : DifferentialGeometry.RiemannianMetricComplete surfaceMetric := by
  apply DifferentialGeometry.RiemannianMetricComplete.of_isProperMap_of_mfderiv_bound
    surfaceMetric (C := (1 : NNReal))
    (smoothRadius_contDiff.contMDiff.of_le (by decide)) smoothRadius_isProper (by norm_num)
  intro x v
  rw [mfderiv_eq_fderiv]
  change ‖fderiv ℝ smoothRadius x v‖ ≤ (1 : ℝ) * Real.sqrt (surfaceMetric.inner x v v)
  simpa only [one_mul] using smoothRadius_speed_bound x v

theorem surface_targets : surfaceTargets :=
  ⟨surfaceComplete, surfaceSectional, surfaceOrientation⟩

end DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
