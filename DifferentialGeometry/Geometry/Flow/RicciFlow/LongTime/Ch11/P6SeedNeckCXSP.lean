import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedGeodesicCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceNecks

set_option autoImplicit false

/-!
# CX-SPINE G2：high scalar segment 中生产实际 SpatialNeck

末次过阈值给一个 middle point；两端的 scalar gaps 排除 whole-component 分支，
既有 minimizing-segment theorem 实际处理 canonical cap 的 tube/core 分支。
输出仍为 spatial neck，不声称由此得到 strong backward flow 或完整 Claim 2。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 同一 minimizing segment 上，从两端 scalar gap 与区域 canonical 数据生产 neck 中心。 -/
theorem exists_spatialNeck_on_high_segment_CXSP
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) {ε C1 C2 α Q a b : ℝ} {γ : ℝ → M}
    (hC2 : 1 ≤ C2) (hQ : 0 < Q) (hα : α < 1 / 11)
    (hε : 13000 * (13000 * ε) ≤ α)
    (hγ : ContinuousOn γ (Icc a b)) (hab : a ≤ b)
    (hmin : ∀ v ∈ Icc a b, ∀ w ∈ Icc a b,
      riemannianEDistOf g (γ v) (γ w) = ENNReal.ofReal |v - w|)
    (hleft : metricScalarAt g (γ a) = Q)
    (hright : 2 * C2 ^ 2 * Q < metricScalarAt g (γ b))
    (hW : ∀ v ∈ Icc a b, Q ≤ metricScalarAt g (γ v) →
      ∃ W : SpatialCanonicalWitness g ε C1 C2 (γ v), W.capTubeHasNeckChart ε) :
    ∃ m ∈ Ioo a b, metricScalarAt g (γ m) = 2 * C2 * Q ∧
      Nonempty (SpatialNeck g α (γ m)) ∧
      ∀ v ∈ Ioc m b, 2 * C2 * Q < metricScalarAt g (γ v) := by
  have hCQ : 0 < C2 * Q := mul_pos (zero_lt_one.trans_le hC2) hQ
  have hQQ : Q ≤ C2 * Q := by nlinarith [mul_le_mul_of_nonneg_right hC2 hQ.le]
  have hmid : Q < 2 * C2 * Q := by linarith
  have hprod : 0 ≤ (C2 - 1) * (C2 * Q) :=
    mul_nonneg (sub_nonneg.mpr hC2) hCQ.le
  have htop : 2 * C2 * Q < metricScalarAt g (γ b) := by nlinarith
  have hf : ContinuousOn (fun v => metricScalarAt g (γ v)) (Icc a b) :=
    (metricScalar_smooth g).continuous.comp_continuousOn hγ
  obtain ⟨m, hm, hRm, _, _, htail⟩ :=
    exists_last_threshold_CXSP hf hab (by simpa only [hleft] using hmid) htop
  obtain ⟨W, hchart⟩ := hW m ⟨hm.1.le, hm.2.le⟩ (by rw [hRm]; exact hmid.le)
  have hneck : Nonempty (SpatialNeck g α (γ m)) :=
    W.nonempty_spatialNeck_of_minimizing_segment hchart hα hε hm.1 hm.2 hmin rfl
      (by rw [hleft, hRm]; linarith)
      (by rw [hRm]; nlinarith)
  exact ⟨m, hm, hRm, hneck, htail⟩

/-- 原 seed 球的 canonical 数据足以供给末段 neck；未要求扩大到 B(p,3ρ)。 -/
theorem exists_spatialNeck_in_seed_ball_CXSP
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) {ε C1 C2 α Q L ρ : ℝ} {γ : ℝ → M}
    (hC2 : 1 ≤ C2) (hQ : 0 < Q) (hα : α < 1 / 11)
    (hε : 13000 * (13000 * ε) ≤ α)
    (hγ : ContinuousOn γ (Icc 0 L)) (hL : 0 ≤ L) (hlen : L < ρ)
    (hmin : ∀ v ∈ Icc (0 : ℝ) L, ∀ w ∈ Icc (0 : ℝ) L,
      riemannianEDistOf g (γ v) (γ w) = ENNReal.ofReal |v - w|)
    (hseed : metricScalarAt g (γ 0) < Q)
    (hhigh : 2 * C2 ^ 2 * Q < metricScalarAt g (γ L))
    (hW : ∀ x ∈ riemannianBallOf g (γ 0) ρ, Q ≤ metricScalarAt g x →
      ∃ W : SpatialCanonicalWitness g ε C1 C2 x, W.capTubeHasNeckChart ε) :
    ∃ m ∈ Ioo (0 : ℝ) L, γ m ∈ riemannianBallOf g (γ 0) ρ ∧
      metricScalarAt g (γ m) = 2 * C2 * Q ∧ Nonempty (SpatialNeck g α (γ m)) ∧
      ∀ v ∈ Ioc m L, 2 * C2 * Q < metricScalarAt g (γ v) := by
  have hC2sq : 1 ≤ C2 ^ 2 := one_le_pow₀ hC2
  have hhighQ : Q < metricScalarAt g (γ L) := by
    nlinarith [mul_le_mul_of_nonneg_right hC2sq hQ.le]
  obtain ⟨s, hs, hRs, _, _, _, _, _, _⟩ :=
    exists_scalar_high_tail_on_segment_CXSP g hγ hL hlen hmin hseed hhighQ
  have hball (v : ℝ) (hv : v ∈ Icc (0 : ℝ) L) :
      γ v ∈ riemannianBallOf g (γ 0) ρ := by
    change riemannianEDistOf g (γ 0) (γ v) < ENNReal.ofReal ρ
    rw [hmin 0 ⟨le_rfl, hL⟩ v hv, zero_sub, abs_neg, abs_of_nonneg hv.1]
    exact (ENNReal.ofReal_lt_ofReal_iff (hL.trans_lt hlen)).mpr (hv.2.trans_lt hlen)
  have hsub : Icc s L ⊆ Icc (0 : ℝ) L := Icc_subset_Icc hs.1.le le_rfl
  obtain ⟨m, hm, hRm, hneck, htail⟩ := exists_spatialNeck_on_high_segment_CXSP g hC2 hQ
    hα hε (hγ.mono hsub) hs.2.le
    (fun v hv w hw => hmin v (hsub hv) w (hsub hw)) hRs hhigh
    (fun v hv hRv => hW (γ v) (hball v (hsub hv)) hRv)
  exact ⟨m, ⟨hs.1.trans hm.1, hm.2⟩,
    hball m ⟨(hs.1.trans hm.1).le, hm.2.le⟩, hRm, hneck, htail⟩

end GC.LongTime.Ch11
