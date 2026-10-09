import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RegularCanonicalCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LocalKappaP6B

set_option autoImplicit false

/-!
# CX-SPINE G24：exact hb 生产同一 moving seed ball 的 regular spatial 供给

原hb仅在放大因子51200*exp(57)*A处调用，生产的是原A*r移动球上的空间witness。
实际earlier seed半径为r/100；因此阈值10000*KG，晚期时间2*TG。
不调用更大A的κ、不生成full Good；正stage-age仍明确保留。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 原RegularSlice hb在同一原seed的regular半窗内给空间供给，常数先于全部queries。 -/
theorem seed_spatial_window_of_regular_supply_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} (hb : LargerBallCanonicalLateSupply_C11E F ε C1 C2)
    {A : ℝ} (hA : 0 < A) :
    ∃ Kwin Twin : ℝ, 0 < Kwin ∧ 0 < Twin ∧
      ∀ n, let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        Twin ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
        (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
        (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) → H.time (H.activeStage v) < (v : ℝ) →
      ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        Kwin * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) y →
        ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage v) v) ε C1 C2 y,
          W.capTubeHasNeckChart ε := by
  let A' : ℝ := 51200 * Real.exp 57 * A
  have hA' : A' = 51200 * Real.exp 57 * A := rfl
  have hA'pos : 0 < A' := by dsimp only [A']; positivity
  obtain ⟨KG, TG, hKG, hTG, hbody⟩ := regular_history_canonical_of_supply_CXSP hb hA'pos
  refine ⟨10000 * KG, 2 * TG, by positivity, by positivity, ?_⟩
  intro n H t p r hTt htime hsmall hvol aSeed haT hclock seedTrace v hav hvt hv hage y hy hR
  have hr : 0 < r := hsmall.1
  obtain ⟨hseedV, hvolV, htimeV⟩ :=
    earlier_seed_on_half_depth_P6B haT p r A htime hclock hsmall hvol seedTrace v hav hvt hv
  set O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)
  have hexp : 1 ≤ Real.exp 57 := Real.one_le_exp (by norm_num)
  have hTv : TG ≤ (v : ℝ) := by nlinarith [sq_nonneg r]
  have hinv : A'⁻¹ ≤ A⁻¹ * Real.exp (-57) / 512 := by
    rw [hA', Real.exp_neg]
    have he : 0 < Real.exp 57 := Real.exp_pos 57
    rw [mul_inv, mul_inv]
    have : (51200 : ℝ)⁻¹ ≤ 1 / 512 := by norm_num
    calc (51200 : ℝ)⁻¹ * (Real.exp 57)⁻¹ * A⁻¹ ≤ 1 / 512 * (Real.exp 57)⁻¹ * A⁻¹ := by
          gcongr
      _ = A⁻¹ * (Real.exp 57)⁻¹ / 512 := by ring
  have hvolA' : ENNReal.ofReal (A'⁻¹ * (r / 100) ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage v) v) O (r / 100) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hinv (by positivity))).trans hvolV
  have hball : A * r ≤ A' * (r / 100) := by
    rw [hA']
    have : A * r ≤ 512 * Real.exp 57 * A * r := by
      have h1 : 1 ≤ 512 * Real.exp 57 := by nlinarith
      nlinarith [mul_pos hA hr]
    nlinarith
  have hy' := riemannianBallOf_mono _ O hball hy
  have hscale : KG * ((r / 100) ^ 2)⁻¹ = (10000 * KG) * (r ^ 2)⁻¹ := by
    rw [div_pow, inv_div, div_eq_mul_inv]
    ring
  have hRV : KG * ((r / 100) ^ 2)⁻¹ ≤
      metricScalarAt (H.stageMetric (H.activeStage v) v) y := by
    rw [hscale]
    exact hR
  exact hbody n v O (r / 100) hTv hage htimeV hseedV hvolA' y hy' hRV

end GC.LongTime.Ch11
