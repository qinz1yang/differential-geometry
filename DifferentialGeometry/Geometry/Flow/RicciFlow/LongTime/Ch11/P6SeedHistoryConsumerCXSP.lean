import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedComponentCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedHistoryCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedNeckCXSP

set_option autoImplicit false

/-!
# CX-SPINE G2：任意实际 history stage 的 seed-tail / neck consumer

ObservedHistory 的 stage 紧，但不必 connected。先从原 seed 球生产 component 内的
最短段，再调用 G1 阈值与 G2 canonical cap/neck 几何。适用全部 stageAt 时刻；这里
不把空间结论升级为 backward StrongNeck，也不宣称已证 Claim 2。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 无 supplied-segment / connected-stage 假设的实际 history high-tail producer。 -/
theorem exists_history_seed_tail_CXSP
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p x : (H.stageAt t).Carrier} {r A Kb : ℝ}
    (hsmall : hasSmallParabolicCurvature H t p r) (hA : 0 < A)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r))
    (hhigh : max 4 (2 * Kb) * (r ^ 2)⁻¹ <
      metricScalarAt (H.stageMetric (H.activeStage t) t) x) :
    ∃ (L : ℝ) (γ : ℝ → (H.stageAt t).Carrier) (s : ℝ),
      s ∈ Ioo (0 : ℝ) L ∧ γ 0 = p ∧ γ L = x ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
      metricScalarAt (H.stageMetric (H.activeStage t) t) (γ s) =
        max 4 (2 * Kb) * (r ^ 2)⁻¹ ∧
      (∀ v ∈ Icc (0 : ℝ) (L - s),
        γ (s + v) ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r) ∧
        (max 4 (2 * Kb) / 2) * (r ^ 2)⁻¹ <
          metricScalarAt (H.stageMetric (H.activeStage t) t) (γ (s + v))) ∧
      (∀ v ∈ Ioc (0 : ℝ) (L - s),
        max 4 (2 * Kb) * (r ^ 2)⁻¹ <
          metricScalarAt (H.stageMetric (H.activeStage t) t) (γ (s + v))) ∧
      riemannianEDistOf (H.stageMetric (H.activeStage t) t) (γ s) x =
        ENNReal.ofReal (L - s) ∧
      L - s < (2 * A * Real.sqrt (max 4 (2 * Kb))) /
        Real.sqrt (max 4 (2 * Kb) * (r ^ 2)⁻¹) ∧
      ∀ a ∈ Icc (0 : ℝ) (L - s), ∀ b ∈ Icc (0 : ℝ) (L - s),
        riemannianEDistOf (H.stageMetric (H.activeStage t) t) (γ (s + a)) (γ (s + b)) =
          ENNReal.ofReal |a - b| := by
  have hr : 0 < r := hsmall.1
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hseed : metricScalarAt (H.stageMetric (H.activeStage t) t) p <
      max 4 (2 * Kb) * (r ^ 2)⁻¹ :=
    ((le_abs_self _).trans (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hp)).trans_lt
      (seed_threshold_bounds_CXSP Kb hr).2.1
  have hpx : p ≠ x := fun he => by rw [he] at hseed; exact (hseed.trans hhigh).false
  obtain ⟨L, γ, hL, hlen, hstart, hend, hsmooth, _, hdist⟩ :=
    exists_seed_segment_of_compact_CXSP (H.stageMetric (H.activeStage t) t) p x hx hpx
  obtain ⟨s, hs, hQ, hclosed, hopen, hdistend, hshort, htaildist⟩ :=
    exists_seed_scalar_tail_CXSP hsmall hA γ hstart hsmooth.continuous.continuousOn
      hL hlen hdist (by simpa only [hend] using hhigh)
  exact ⟨L, γ, s, hs, hstart, hend, hsmooth, hQ, hclosed, hopen,
    by simpa only [hend] using hdistend, hshort, htaildist⟩

/-- 同一 history seed 球的 canonical supply 实际给 high segment 上的 SpatialNeck。 -/
theorem exists_history_seed_neck_CXSP
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p x : (H.stageAt t).Carrier} {r A Kb ε C1 C2 α : ℝ}
    (hsmall : hasSmallParabolicCurvature H t p r)
    (hC2 : 1 ≤ C2) (hα : α < 1 / 11) (hε : 13000 * (13000 * ε) ≤ α)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r))
    (hhigh : 2 * C2 ^ 2 * (max 4 (2 * Kb) * (r ^ 2)⁻¹) <
      metricScalarAt (H.stageMetric (H.activeStage t) t) x)
    (hW : ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
      Kb * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
        ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
          W.capTubeHasNeckChart ε) :
    ∃ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
      metricScalarAt (H.stageMetric (H.activeStage t) t) y =
        2 * C2 * (max 4 (2 * Kb) * (r ^ 2)⁻¹) ∧
      Nonempty (SpatialNeck (H.stageMetric (H.activeStage t) t) α y) := by
  obtain ⟨hQ, h3, hKb, hhalf⟩ := seed_threshold_bounds_CXSP Kb hsmall.1
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hsmall.1
  have hseed : metricScalarAt (H.stageMetric (H.activeStage t) t) p <
      max 4 (2 * Kb) * (r ^ 2)⁻¹ :=
    ((le_abs_self _).trans (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hp)).trans_lt h3
  have hlarge : max 4 (2 * Kb) * (r ^ 2)⁻¹ <
      metricScalarAt (H.stageMetric (H.activeStage t) t) x := by
    have hsq : 1 ≤ C2 ^ 2 := one_le_pow₀ hC2
    nlinarith [mul_le_mul_of_nonneg_right hsq hQ.le]
  have hpx : p ≠ x := fun he => by rw [he] at hseed; exact (hseed.trans hlarge).false
  obtain ⟨L, γ, hL, hlen, hstart, hend, hsmooth, _, hdist⟩ :=
    exists_seed_segment_of_compact_CXSP (H.stageMetric (H.activeStage t) t) p x hx hpx
  obtain ⟨m, _, hm, hRm, hneck, _⟩ :=
    exists_spatialNeck_in_seed_ball_CXSP (H.stageMetric (H.activeStage t) t)
      hC2 hQ hα hε hsmooth.continuous.continuousOn hL hlen hdist
      (by simpa only [hstart] using hseed) (by simpa only [hend] using hhigh)
      (fun y hy hRy => hW y (by simpa only [hstart] using hy)
        (hKb.trans (hhalf.le.trans hRy)))
  exact ⟨γ m, by simpa only [hstart] using hm, hRm, hneck⟩

end GC.LongTime.Ch11
