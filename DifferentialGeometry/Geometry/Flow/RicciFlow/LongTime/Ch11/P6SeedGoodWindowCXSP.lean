import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LocalKappaP6B
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection

/-!
# Full late Good supply on the moving half-depth seed window

The input `hgood` is the full history-uniform late
`HasSpatialCanonicalTimeControl` statement at `A' = 51200 * exp 57 * A`.
Its source must be paid by an upstream producer retaining the complete Good
predicate, such as `lateGoodAt_of_selected_CXSP` with its closure hypothesis paid.
The projected spatial statement P6(b) alone does not supply this input.

The geometric step is `earlier_seed_on_half_depth_P6B`
(`P6SeedShiftP6B.lean`, lines 161–179). The volume coefficient and ball inclusion
are the same estimates used in `localKappaWindow_of_late_P6B`
(`P6LocalKappaP6B.lean`, lines 188–213). Applying the given late Good statement
to the resulting seed of radius `r / 100` gives threshold `10000 * KG` and the
conservative late time `2 * TG` on the original moving ball of radius `A * r`.
All history indices, seed times, seed traces, and test points follow these constants.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- A full late Good supply at the enlarged factor gives full Good throughout
the original seed's moving half-depth window. Its time-control projection retains
the positive-stage-age and pre-horizon guards in `HasSpatialCanonicalTimeControl`. -/
theorem seedGoodWindow_of_lateGood_CXSP {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {A KG TG : ℝ} (hA : 0 < A)
    (hgood : ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        TG ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal ((51200 * Real.exp 57 * A)⁻¹ * r ^ 3) ≤
          ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p
            ((51200 * Real.exp 57 * A) * r),
          KG * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime t y) :
    ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        2 * TG ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
        (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
        (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
      ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        (10000 * KG) * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) y →
        H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v y := by
  intro n H t p r hTt htime hsmall hvol aSeed haT hclock seedTrace v hav hvt hv y hy hR
  have hr : 0 < r := hsmall.1
  obtain ⟨hseedV, hvolV, htimeV⟩ :=
    earlier_seed_on_half_depth_P6B haT p r A htime hclock hsmall hvol seedTrace v hav hvt hv
  set O := seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)
  set A' : ℝ := 51200 * Real.exp 57 * A with hA'
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
  exact hgood n v O (r / 100) hTv htimeV hseedV hvolA' y hy' hRV

end GC.LongTime.Ch11
