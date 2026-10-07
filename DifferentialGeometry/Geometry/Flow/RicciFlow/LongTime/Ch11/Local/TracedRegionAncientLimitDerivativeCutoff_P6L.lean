import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitDerivativeCutoff

/-!
# `abs_derivWithin_scalar_le_of_survivor_maps_of_lt` 的局部化副本（O-CH11-P6D G1，后缀 `_P6L`）

原定理：`ObservedHistory.abs_derivWithin_scalar_le_of_survivor_maps_of_lt`
（`ST/TracedRegionAncientLimitDerivativeCutoff.lean:19`）。

**唯一改动**：全局时间导数前提 `hstage`（`∀ v < t₀`, 非 event, `∀ p : (H.stageAt v).Carrier`）换成
**survivor 点形**：只在 `f ⟨H.activeStage v, _, _⟩ z`（`a ≤ v ≤ t`、`z : W`）上要
`|∂ₜ⁻ R| ≤ C R²`。原证明只在 `f j z` 一点求值（[V] 原文 `hstage v hst₀ hreg' (f j z) hqz`），
证明体照抄，使用点补 `hav` / `hvt`（原证明已构造）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

/-- `abs_derivWithin_scalar_le_of_survivor_maps_of_lt` 的局部化：`hstage` 只在 survivor 点上要求。 -/
theorem abs_derivWithin_scalar_le_of_survivor_maps_of_lt_P6L (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) {R θ t₀ q qD C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hqD : q ≤ R * qD) {W : TopologicalSpace.Opens (H.stageAt t).Carrier}
    {h : ℝ → SmoothRiemannianMetric ThreeModel W}
    (a : Icc (0 : ℝ) H.horizon) (ha : (a : ℝ) = t - θ / R)
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
      (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hp : ∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      (t : ℝ) + s / R ∈ H.stageDomain j.val →
        h s = scaleMetric R hR
          (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j)))
    (hstage : ∀ v : Icc (0 : ℝ) H.horizon, (v : ℝ) < t₀ → H.time (H.activeStage v) < v →
      ∀ (hav : a ≤ v) (hvt : v ≤ t) (z : W),
        q < metricScalarAt (H.stageMetric (H.activeStage v) v)
          (f ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩ z) →
        |derivWithin (fun v' => metricScalarAt (H.stageMetric (H.activeStage v) v')
            (f ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩ z))
          (Iic (v : ℝ)) v| ≤
          C * metricScalarAt (H.stageMetric (H.activeStage v) v)
            (f ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩ z) ^ 2)
    {s : ℝ} (hs : s ∈ Ioc (-θ) 0) (hst₀ : (t : ℝ) + s / R < t₀)
    (hreg : ∀ hv : (t : ℝ) + s / R ∈ Icc (0 : ℝ) H.horizon,
      H.time (H.activeStage ⟨_, hv⟩) < (t : ℝ) + s / R)
    (z : W) (hz : qD < metricScalarAt (h s) z) :
    |derivWithin (fun s' => metricScalarAt (h s') z) (Iic s) s| ≤
      C * metricScalarAt (h s) z ^ 2 := by
  have hvI : (t : ℝ) + s / R ∈ Icc (a : ℝ) t := by
    have h1 : -θ / R ≤ s / R := div_le_div_of_nonneg_right hs.1.le hR.le
    have h2 : s / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hR.le
    rw [neg_div] at h1
    constructor <;> linarith
  let v : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) + s / R, a.2.1.trans hvI.1, hvI.2.trans t.2.2⟩
  have hav : a ≤ v := hvI.1
  have hvt : v ≤ t := hvI.2
  have hreg' := hreg v.2
  let j : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hlow : H.time (H.activeStage v) - t < s / R := by
    change H.time (H.activeStage v) < (t : ℝ) + s / R at hreg'
    linarith
  have hlowR : (H.time (H.activeStage v) - t) * R < s := by
    rwa [lt_div_iff₀ hR] at hlow
  have hev : ∀ᶠ s' in 𝓝[Iic s] s, h s' = scaleMetric R hR
      (localPullMetric (H.stageMetric j.val ((t : ℝ) + s' / R)) (f j) (hf j)) := by
    filter_upwards [Ioc_mem_nhdsLE (max_lt hs.1 hlowR)] with s' hs'
    have h1 : -θ < s' := (le_max_left _ _).trans_lt hs'.1
    have h2 : (H.time (H.activeStage v) - t) * R < s' := (le_max_right _ _).trans_lt hs'.1
    refine hp s' ⟨h1.le, hs'.2.trans hs.2⟩ j
      (H.mem_stageDomain_activeStage_of_le v ?_ ?_)
    · have : H.time (H.activeStage v) - t < s' / R := by rwa [lt_div_iff₀ hR]
      linarith
    · change (t : ℝ) + s' / R ≤ (t : ℝ) + s / R
      have := div_le_div_of_nonneg_right hs'.2 hR.le
      linarith
  have hs0 := hp s ⟨hs.1.le, hs.2⟩ j (H.activeStage_mem v)
  have hRz : metricScalarAt (h s) z =
      R⁻¹ * metricScalarAt (H.stageMetric j.val ((t : ℝ) + s / R)) (f j z) := by
    rw [hs0, metricScalarAt_scaleMetric, metricScalarAt_localPull]
  have hqz : q < metricScalarAt (H.stageMetric (H.activeStage v) v) (f j z) := by
    have h1 : R * qD < R * metricScalarAt (h s) z := mul_lt_mul_of_pos_left hz hR
    rw [hRz, ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at h1
    exact hqD.trans_lt h1
  -- 局部化：导数界只在 survivor 点 `f j z` 取
  exact abs_derivWithin_scalar_le_of_scaleMetric_localPullMetric (hf j) hR hC hev hs0 z
    (hstage v hst₀ hreg' hav hvt z hqz)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
