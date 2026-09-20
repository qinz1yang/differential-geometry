import DifferentialGeometry.Geometry.Geodesic.ChartAcceleration
import DifferentialGeometry.Analysis.Calculus.UpperSupport.AffineComparison


noncomputable section

open Filter Manifold Set
open scoped ContDiff Manifold Topology NNReal

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_affine_chart_upper_support_of_geodesic_upper_support
    (g : SmoothRiemannianMetric I M) (p : M)
    {f : M → ℝ} {s : Set E} {L : ℝ≥0}
    (hf : LipschitzOnWith L (f ∘ (extChartAt I p).symm) s)
    {γ : ℝ → M} (hγ : IsGeodesicAt (I := I) g γ 0)
    (hp : γ 0 ∈ (chartAt H p).source) (hs : s ∈ 𝓝 (extChartAt I p (γ 0)))
    {C D : ℝ} (hC : 0 ≤ C)
    (hΓ : ∀ i j k, ‖chartChristoffel g p i j k (extChartAt I p (γ 0))‖ ≤ C)
    {φ : ℝ → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (htouch : φ 0 = f (γ 0))
    (hupper : (fun r => f (γ r)) ≤ᶠ[𝓝 (0 : ℝ)] φ)
    (hsecond : deriv (deriv φ) 0 ≤ D * ‖deriv ((extChartAt I p) ∘ γ) 0‖ ^ 2) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = f (γ 0) ∧
      (fun r => f ((extChartAt I p).symm
        (extChartAt I p (γ 0) + r • deriv ((extChartAt I p) ∘ γ) 0))) ≤ᶠ[𝓝 (0 : ℝ)] ψ ∧
      deriv (deriv ψ) 0 ≤
        (D + 2 * (L : ℝ) *
          (C * (∑ i, ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) ^ 2 *
            (∑ k, ‖chartModelBasis E k‖) + 1)) *
          ‖deriv ((extChartAt I p) ∘ γ) 0‖ ^ 2 := by
  have hγsmooth := DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hγ
  have hcoord : ContDiffAt ℝ 2 ((extChartAt I p) ∘ γ) 0 :=
    ((contMDiffAt_extChartAt' hp).comp 0 hγsmooth).contDiffAt.of_le (by norm_cast)
  have hsource : ∀ᶠ r in 𝓝 (0 : ℝ), γ r ∈ (chartAt H p).source :=
    hγsmooth.continuousAt.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hp)
  have hback : ∀ᶠ r in 𝓝 (0 : ℝ),
      (extChartAt I p).symm (extChartAt I p (γ r)) = γ r := by
    filter_upwards [hsource] with r hr
    exact (extChartAt I p).left_inv (by simpa only [extChartAt_source] using hr)
  have hzero : (extChartAt I p).symm (extChartAt I p (γ 0)) = γ 0 :=
    Filter.EventuallyEq.eq_of_nhds hback
  have hupper' :
      (fun r => (f ∘ (extChartAt I p).symm) (((extChartAt I p) ∘ γ) r))
        ≤ᶠ[𝓝 (0 : ℝ)] φ := by
    filter_upwards [hback, hupper] with r hr hu
    simpa only [Function.comp_apply, hr] using hu
  obtain ⟨ψ, hψ, hψzero, hψupper, hψsecond⟩ :=
    DifferentialGeometry.Analysis.exists_affine_upper_support_of_curve_upper_support
      hf hs hcoord rfl rfl
      (norm_deriv_deriv_extChartAt_comp_le_of_isGeodesicAt g hγ p hp hC hΓ)
      hφ (by simpa only [Function.comp_apply, hzero] using htouch) hupper' hsecond
  refine ⟨ψ, hψ, ?_, hψupper, hψsecond⟩
  simpa only [Function.comp_apply, hzero] using hψzero

end DifferentialGeometry.Geometry.Riemannian.Geodesic
