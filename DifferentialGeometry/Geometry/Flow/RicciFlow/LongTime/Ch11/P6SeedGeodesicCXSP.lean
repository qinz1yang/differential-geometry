import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LastCrossingCXSP
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background

set_option autoImplicit false

/-!
# CX-SPINE G1：同一 minimizing metric segment 上的 scalar high tail

输入是指定曲线的实际 riemannianEDistOf 等式，故不把一般路径伪装为 shortest geodesic。
返回同一曲线 γ 的尾段 γ(s+v)，保留 pairwise distance、seed 球包含和 strict/closed threshold。
这里只生产 Claim 2 的几何输入，不提供 curvature-at-distance 结论。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 指定 minimizing segment 的 last crossing；尾段仍在原 seed 球内，且仍然 minimizing。 -/
theorem exists_scalar_high_tail_on_segment_CXSP
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) {γ : ℝ → M} {L ρ Q : ℝ}
    (hγ : ContinuousOn γ (Icc 0 L)) (hL : 0 ≤ L) (hρ : L < ρ)
    (hdist : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      riemannianEDistOf g (γ a) (γ b) = ENNReal.ofReal |a - b|)
    (hseed : metricScalarAt g (γ 0) < Q) (hend : Q < metricScalarAt g (γ L)) :
    ∃ s ∈ Ioo (0 : ℝ) L, metricScalarAt g (γ s) = Q ∧
      (∀ w ∈ Icc (0 : ℝ) L, metricScalarAt g (γ w) = Q → w ≤ s) ∧
      (∀ v ∈ Icc (0 : ℝ) (L - s),
        γ (s + v) ∈ riemannianBallOf g (γ 0) ρ ∧ Q ≤ metricScalarAt g (γ (s + v))) ∧
      (∀ v ∈ Ioc (0 : ℝ) (L - s), Q < metricScalarAt g (γ (s + v))) ∧
      riemannianEDistOf g (γ s) (γ L) = ENNReal.ofReal (L - s) ∧
      L - s < ρ ∧
      ∀ a ∈ Icc (0 : ℝ) (L - s), ∀ b ∈ Icc (0 : ℝ) (L - s),
        riemannianEDistOf g (γ (s + a)) (γ (s + b)) = ENNReal.ofReal |a - b| := by
  have hf : ContinuousOn (fun v => metricScalarAt g (γ v)) (Icc 0 L) :=
    (metricScalar_smooth g).continuous.comp_continuousOn hγ
  obtain ⟨s, hs, hQ, hlast, hclosed, hopen⟩ :=
    exists_last_threshold_CXSP hf hL hseed hend
  have hmem (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (L - s)) : s + v ∈ Icc (0 : ℝ) L :=
    ⟨by linarith [hs.1, hv.1], by linarith [hv.2]⟩
  refine ⟨s, hs, hQ, hlast, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    refine ⟨?_, hclosed (s + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩⟩
    change riemannianEDistOf g (γ 0) (γ (s + v)) < ENNReal.ofReal ρ
    rw [hdist 0 ⟨le_rfl, hL⟩ (s + v) (hmem v hv),
      zero_sub, abs_neg, abs_of_nonneg (hmem v hv).1]
    exact (ENNReal.ofReal_lt_ofReal_iff (hL.trans_lt hρ)).mpr
      ((hmem v hv).2.trans_lt hρ)
  · intro v hv
    exact hopen (s + v) ⟨by linarith [hv.1], by linarith [hv.2]⟩
  · rw [hdist s ⟨hs.1.le, hs.2.le⟩ L ⟨hL, le_rfl⟩,
      abs_of_nonpos (sub_nonpos.mpr hs.2.le), neg_sub]
  · linarith [hs.1]
  · intro a ha b hb
    rw [hdist (s + a) (hmem a ha) (s + b) (hmem b hb)]
    congr 2
    ring

end GC.LongTime.Ch11
