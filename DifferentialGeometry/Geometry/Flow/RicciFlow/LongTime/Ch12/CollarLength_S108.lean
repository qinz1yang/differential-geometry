import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HAbs_S105
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.WeakLength
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# CH12-S108, group 1 (part 1): h-length of the vertical collar segment

For a `NormalizedNeck h δ k`, the vertical segment `t ↦ chart (y, t)`, `t ∈ [0, z]`, `z < δ⁻¹`, has
`h`-length at most `√(2 / scale) * z` (speed `≤ √((1+δ)/q) ≤ √(2/q)`; the normalized metric is
`δ`-close to the round cylinder on the closed test region and the vertical unit vector has round
norm 1).
-/

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

/-- The vertical collar curve `t ↦ (y, clamp t)` into the central domain (a function, not a hypothesis). -/
def collarCurve_S108 (δ : ℝ) (hδ : 0 < δ) (y : Sphere 2) (z : ℝ) (hz : z < δ⁻¹) :
    ℝ → neckCentralDomain δ := fun t =>
  ⟨⟨(y, max 0 (min t z)), by
    have h0 : 0 < δ⁻¹ := inv_pos.mpr hδ
    have h1 : 0 ≤ max 0 (min t z) := le_max_left _ _
    have h2 : max 0 (min t z) < δ⁻¹ := max_lt h0 (lt_of_le_of_lt (min_le_right _ _) hz)
    change -δ⁻¹ - 1 < max 0 (min t z) ∧ max 0 (min t z) < δ⁻¹ + 1
    constructor <;> linarith⟩, by
    have h0 : 0 < δ⁻¹ := inv_pos.mpr hδ
    have h1 : 0 ≤ max 0 (min t z) := le_max_left _ _
    have h2 : max 0 (min t z) < δ⁻¹ := max_lt h0 (lt_of_le_of_lt (min_le_right _ _) hz)
    change -δ⁻¹ < max 0 (min t z) ∧ max 0 (min t z) < δ⁻¹
    constructor <;> linarith⟩

theorem collarCurve_val_S108 (δ : ℝ) (hδ : 0 < δ) (y : Sphere 2) (z : ℝ) (hz : z < δ⁻¹) (t : ℝ) :
    (((collarCurve_S108 δ hδ y z hz t).1 : neckBuffer δ) : NeckCylinder) =
      (y, max 0 (min t z)) := rfl

theorem collarCurve_continuous_S108 (δ : ℝ) (hδ : 0 < δ) (y : Sphere 2) (z : ℝ) (hz : z < δ⁻¹) :
    Continuous (collarCurve_S108 δ hδ y z hz) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact continuous_const.prodMk (continuous_const.max (continuous_id.min continuous_const))

theorem collarCurve_val_of_mem_S108 (δ : ℝ) (hδ : 0 < δ) (y : Sphere 2) {z : ℝ} (hz : z < δ⁻¹)
    {t : ℝ} (ht : t ∈ Icc 0 z) :
    (((collarCurve_S108 δ hδ y z hz t).1 : neckBuffer δ) : NeckCylinder) = (y, t) := by
  rw [collarCurve_val_S108, min_eq_left ht.2, max_eq_right ht.1]

/-- The vertical unit vector `(0, 1)` has round-cylinder norm `1`. -/
theorem roundCylinder_vertical_S108 (x : NeckCylinder) (V : TangentSpace NeckCylinderModel x)
    (h1 : V.1 = 0) (h2 : V.2 = 1) : roundCylinderMetric.inner x V V = 1 := by
  rw [roundCylinderMetric_eq_geometry, DifferentialGeometry.Geometry.Metric.roundCylinderMetric_inner,
    h1, h2]
  have hz : DifferentialGeometry.Geometry.dIncl (E := ThreeSpace) (n := 2) x.1
      (0 : TangentSpace (𝓡 2) x.1) = 0 := map_zero _
  simp only [inner_self_eq_norm_sq_to_K, Real.ringHom_apply, mul_one, add_eq_right, mul_eq_zero,
    OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero, false_or]
  exact hz

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem collar_length_le_S108 {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ} (N : NormalizedNeck h δ k)
    (y : Sphere 2) {z : ℝ} (hz0 : 0 ≤ z) (hzδ : z < δ⁻¹) :
    riemannianCurveLength h
      (fun t => N.chart (collarCurve_S108 δ N.delta_pos y z hzδ t).1) 0 z ≤
      ENNReal.ofReal (Real.sqrt (2 / N.scale) * z) := by
  classical
  set γ := collarCurve_S108 δ N.delta_pos y z hzδ with hγ
  have hq := N.scale_pos
  have hσ : ContMDiff 𝓘(ℝ, ℝ) NeckCylinderModel ∞ (fun t : ℝ => ((y, t) : NeckCylinder)) :=
    contMDiff_const.prodMk contMDiff_id
  have h1 : ContMDiffOn 𝓘(ℝ, ℝ) NeckCylinderModel 1
      (fun t => (((γ t).1 : neckBuffer δ) : NeckCylinder)) (Icc 0 z) :=
    (hσ.of_le (by simp)).contMDiffOn.congr
      (fun t ht => collarCurve_val_of_mem_S108 δ N.delta_pos y hzδ ht)
  have h2 : ContMDiffOn 𝓘(ℝ, ℝ) NeckCylinderModel 1 (fun t => ((γ t).1 : neckBuffer δ)) (Icc 0 z) :=
    (DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff (neckBuffer δ)
      (fun t => (γ t).1) _).mp h1
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (fun t => N.chart (γ t).1) (Icc 0 z) :=
    (N.chart_smooth.contMDiff.of_le (by simp)).comp_contMDiffOn h2
  let : RiemannianBundle (TangentSpace ThreeModel : M → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (TangentSpace ThreeModel : M → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hle := riemannianCurveLength_le_pathELength h hc
  refine hle.trans ?_
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  have hspeed : ∀ t ∈ Ioo (0 : ℝ) z,
      ‖mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun t => N.chart (γ t).1) t 1‖ₑ ≤
        ENNReal.ofReal (Real.sqrt (2 / N.scale)) := by
    intro t ht
    have htI : t ∈ Icc 0 z := Ioo_subset_Icc_self ht
    have hγt : ContMDiffAt 𝓘(ℝ, ℝ) NeckCylinderModel 1 (fun t => ((γ t).1 : neckBuffer δ)) t :=
      (h2 t htI).contMDiffAt (Icc_mem_nhds ht.1 ht.2)
    have hchart : MDifferentiableAt NeckCylinderModel ThreeModel N.chart (γ t).1 :=
      (N.chart_smooth.contMDiff (γ t).1).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp t hchart (hγt.mdifferentiableAt one_ne_zero)
    have hV : mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel (fun t => ((γ t).1 : neckBuffer δ)) t 1 =
        ((0 : TangentSpace (𝓡 2) y), (1 : ℝ)) := by
      have e1 := DifferentialGeometry.mfderiv_subtypeVal_comp
        (I := 𝓘(ℝ, ℝ)) (J := NeckCylinderModel) (U := neckBuffer δ) (fun t => (γ t).1) t
      have hev : (fun t => (((γ t).1 : neckBuffer δ) : NeckCylinder)) =ᶠ[nhds t]
          (fun t : ℝ => ((y, t) : NeckCylinder)) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        exact collarCurve_val_of_mem_S108 δ N.delta_pos y hzδ (Ioo_subset_Icc_self hs)
      have e2 := hev.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := NeckCylinderModel)
      have e3 : mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel (fun t : ℝ => ((y, t) : NeckCylinder)) t =
          ContinuousLinearMap.inr ℝ (TangentSpace (𝓡 2) y) (TangentSpace 𝓘(ℝ, ℝ) t) :=
        mfderiv_prod_right
      rw [← e1, e2, e3]
      rfl
    have hD : mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun t => N.chart (γ t).1) t 1 =
        mfderiv NeckCylinderModel ThreeModel N.chart (γ t).1
          (mfderiv 𝓘(ℝ, ℝ) NeckCylinderModel (fun t => ((γ t).1 : neckBuffer δ)) t 1) :=
      congrArg (fun L => L (1 : ℝ)) hcomp
    have hxK : (γ t).1 ∈ neckClosedTest δ := by
      have h0 : 0 < δ⁻¹ := inv_pos.mpr N.delta_pos
      have h1 : 0 ≤ max 0 (min t z) := le_max_left _ _
      have h2 : max 0 (min t z) ≤ δ⁻¹ := max_le h0.le ((min_le_right _ _).trans hzδ.le)
      change -δ⁻¹ ≤ max 0 (min t z) ∧ max 0 (min t z) ≤ δ⁻¹
      exact ⟨by linarith, h2⟩
    have hsmall : metricDerivNorm 0 N.normalizedMetric
        (roundCylinderMetric.restrictOpen (neckBuffer δ))
        (roundCylinderMetric.restrictOpen (neckBuffer δ)) (γ t).1 ≤ δ :=
      (derivNorm_le_sup (isCompact_neckClosedTest δ) (Nat.zero_le k) _ _ _ hxK).trans
        N.closeness.le
    set V : TangentSpace NeckCylinderModel ((γ t).1 : neckBuffer δ) :=
      ((0 : TangentSpace (𝓡 2) y), (1 : ℝ)) with hVdef
    have hone : (roundCylinderMetric.restrictOpen (neckBuffer δ)).inner (γ t).1 V V = 1 := by
      rw [SmoothRiemannianMetric.restrictOpen_inner]
      exact roundCylinder_vertical_S108 ((γ t).1 : NeckCylinder) V rfl rfl
    have hb := (DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le (roundCylinderMetric.restrictOpen (neckBuffer δ))
      N.normalizedMetric (γ t).1 hsmall V).2
    have hN := N.normalized_inner (γ t).1 V V
    have hδ1 := N.delta_lt_one
    have hin : h.inner (N.chart (γ t).1) (mfderiv NeckCylinderModel ThreeModel N.chart (γ t).1 V)
        (mfderiv NeckCylinderModel ThreeModel N.chart (γ t).1 V) ≤ 2 / N.scale := by
      have h3 : h.inner (N.chart (γ t).1) (mfderiv NeckCylinderModel ThreeModel N.chart (γ t).1 V)
          (mfderiv NeckCylinderModel ThreeModel N.chart (γ t).1 V) =
          N.scale⁻¹ * N.normalizedMetric.inner (γ t).1 V V := by
        rw [hN]; field_simp
      rw [h3, hone, mul_one] at *
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hq.le)
    rw [hD, hV]
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hin)
  calc ∫⁻ t in Ioo (0 : ℝ) z, ‖mfderiv 𝓘(ℝ, ℝ) ThreeModel (fun t => N.chart (γ t).1) t 1‖ₑ
      ≤ ∫⁻ _ in Ioo (0 : ℝ) z, ENNReal.ofReal (Real.sqrt (2 / N.scale)) :=
        setLIntegral_mono' measurableSet_Ioo hspeed
    _ = ENNReal.ofReal (Real.sqrt (2 / N.scale)) * ENNReal.ofReal (z - 0) := by
        rw [setLIntegral_const, Real.volume_Ioo]
    _ = ENNReal.ofReal (Real.sqrt (2 / N.scale) * z) := by
        rw [sub_zero, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

end GC.LongTime.Ch12
