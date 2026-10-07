import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedGeodesicCXSP
import DifferentialGeometry.Geometry.Geodesic.Ray

set_option autoImplicit false

/-!
# CX-SPINE G1：complete connected slice 的实际 minimizing-geodesic consumer

由现有 Hopf-Rinow producer 选同一 γ，再调用 last-threshold engine。
connected/complete 是本 consumer 的真实几何假设；未把 disconnected history stage 当 connected。
history consumer 可直接用 P6SeedGeodesicCXSP 的 supplied-segment 版本。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 从 actual complete metric 生产 γ，保留 smooth / geodesic / unit-speed 与整段距离等式。 -/
theorem exists_scalar_high_tail_of_complete_CXSP
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [T2Space (TangentBundle ThreeModel M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric ThreeModel M)
    (hcomplete : DifferentialGeometry.RiemannianMetricComplete g)
    (p x : M) {ρ Q : ℝ} (hx : x ∈ riemannianBallOf g p ρ)
    (hseed : metricScalarAt g p < Q) (hhigh : Q < metricScalarAt g x) :
    let L := (riemannianEDistOf g p x).toReal
    ∃ (γ : ℝ → M) (s : ℝ), s ∈ Ioo (0 : ℝ) L ∧
      γ 0 = p ∧ γ L = x ∧ ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
      (∀ v, IsGeodesicAt g γ v) ∧
      (∀ v, g.inner (γ v) (mfderiv 𝓘(ℝ, ℝ) ThreeModel γ v 1)
        (mfderiv 𝓘(ℝ, ℝ) ThreeModel γ v 1) = 1) ∧
      (∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
        riemannianEDistOf g (γ a) (γ b) = ENNReal.ofReal |a - b|) ∧
      metricScalarAt g (γ s) = Q ∧
      (∀ v ∈ Icc (0 : ℝ) (L - s),
        γ (s + v) ∈ riemannianBallOf g p ρ ∧ Q ≤ metricScalarAt g (γ (s + v))) ∧
      (∀ v ∈ Ioc (0 : ℝ) (L - s), Q < metricScalarAt g (γ (s + v))) ∧
      riemannianEDistOf g (γ s) x = ENNReal.ofReal (L - s) ∧ L - s < ρ := by
  let L := (riemannianEDistOf g p x).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hfinite (a b : M) : riemannianEDistOf g a b =
      ENNReal.ofReal (riemannianEDistOf g a b).toReal :=
    (ENNReal.ofReal_toReal (riemannianEDistOf_ne_top g a b)).symm
  have hρ : 0 < ρ := by
    exact ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hx)
  have hlen : L < ρ := by
    have hreal : ENNReal.ofReal L < ENNReal.ofReal ρ := by
      rw [← hfinite p x]
      exact hx
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).mp hreal
  have hpx : p ≠ x := by
    intro h
    rw [h] at hseed
    exact (lt_trans hseed hhigh).false
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨γ, hstart, hend, hsmooth, hgeo, hunit, hdist⟩ :=
    DifferentialGeometry.Geometry.exists_unitSpeed_minimizing_geodesic_of_complete
      g hcomplete p x hpx
  change γ L = x at hend
  change ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
    (riemannianEDistOf g (γ a) (γ b)).toReal = |a - b| at hdist
  have hdistE : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      riemannianEDistOf g (γ a) (γ b) = ENNReal.ofReal |a - b| := by
    intro a ha b hb
    rw [hfinite, hdist a ha b hb]
  obtain ⟨s, hs, hQ, _, hclosed, hopen, hdistend, hshort, _⟩ :=
    exists_scalar_high_tail_on_segment_CXSP g hsmooth.continuous.continuousOn hL hlen hdistE
      (by simpa only [hstart] using hseed) (by simpa only [hend] using hhigh)
  refine ⟨γ, s, hs, hstart, hend, hsmooth, hgeo, hunit, hdistE, hQ, ?_, hopen, ?_, hshort⟩
  · intro v hv
    simpa only [hstart] using hclosed v hv
  · simpa only [hend] using hdistend

end GC.LongTime.Ch11
