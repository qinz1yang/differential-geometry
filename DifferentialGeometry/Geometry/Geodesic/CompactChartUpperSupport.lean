import DifferentialGeometry.Geometry.Metric.Coordinates.ChartVelocityBound
import DifferentialGeometry.Geometry.Geodesic.ChartInitialVelocity
import DifferentialGeometry.Geometry.Geodesic.AffineUpperSupport
import DifferentialGeometry.Analysis.Calculus.UpperSupport.UnitDirections


noncomputable section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology NNReal BigOperators

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.Coordinates

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_affine_chart_upper_support_bounds_of_geodesic_support_bounds
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set M}
    (hK : IsCompact K) (hchart : K ⊆ (chartAt H p).source) :
    ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧
      ∀ (f : M → ℝ) (L : ℝ≥0) (D : ℝ),
        (∀ γ : ℝ → M, IsGeodesicAt (I := I) g γ 0 → γ 0 ∈ K →
          Real.sqrt (g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)
            (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) ≤ B →
          ∃ φ : ℝ → ℝ, ContDiffAt ℝ 2 φ 0 ∧ φ 0 = f (γ 0) ∧
            (fun r => f (γ r)) ≤ᶠ[𝓝 (0 : ℝ)] φ ∧ deriv (deriv φ) 0 ≤ D) →
        ∀ q ∈ K, ∀ s : Set E,
          s ∈ 𝓝 (extChartAt I p q) →
          LipschitzOnWith L (f ∘ (extChartAt I p).symm) s →
          ∀ w : E, ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧ ψ 0 = f q ∧
            (fun r => f ((extChartAt I p).symm (extChartAt I p q + r • w)))
              ≤ᶠ[𝓝 (0 : ℝ)] ψ ∧
            deriv (deriv ψ) 0 ≤ (D + 2 * (L : ℝ) * (C + 1)) * ‖w‖ ^ 2 := by
  have hbase : K ⊆ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hchart
  obtain ⟨B, hB, hspeed⟩ := exists_pos_sqrt_inner_symmL_le_mul_norm_on_compact g p hK hbase
  have hcoords : IsCompact ((extChartAt I p) '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt (I := I) p).mono
      (by simpa only [extChartAt_source] using hchart))
  have htarget : (extChartAt I p) '' K ⊆ interior (extChartAt I p).target := by
    rintro _ ⟨q, hq, rfl⟩
    rw [(isOpen_extChartAt_target (I := I) p).interior_eq]
    exact (extChartAt I p).map_source (by simpa only [extChartAt_source] using hchart hq)
  obtain ⟨A, hA, hΓ⟩ := exists_norm_chartChristoffel_le_of_isCompact g p hcoords htarget
  let C : ℝ := A * (∑ i, ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) ^ 2 *
    (∑ k, ‖chartModelBasis E k‖)
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hA (sq_nonneg _))
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  refine ⟨B, C, hB, hC, ?_⟩
  intro f L D hsupport q hq s hs hf w
  have hqinv : (extChartAt I p).symm (extChartAt I p q) = q :=
    (extChartAt I p).left_inv (by simpa only [extChartAt_source] using hchart hq)
  have hunits : ∀ u : E, ‖u‖ = 1 → ∃ φ : ℝ → ℝ,
      ContDiffAt ℝ 2 φ 0 ∧ φ 0 = (f ∘ (extChartAt I p).symm) (extChartAt I p q) ∧
      (fun r => (f ∘ (extChartAt I p).symm) (extChartAt I p q + r • u))
        ≤ᶠ[𝓝 (0 : ℝ)] φ ∧
      deriv (deriv φ) 0 ≤ D + 2 * (L : ℝ) * (C + 1) := by
    intro u hu
    obtain ⟨γ, hγzero, hγ, hvelocity⟩ :=
      exists_geodesic_with_initial_chart_velocity_at g p q (hchart hq) u
    have hrep := MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      ((DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt hγ).mdifferentiableAt
        (by simp)) p (by rw [hγzero]; exact hchart hq)
    change (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) = deriv ((extChartAt I p) ∘ γ) 0 at hrep
    rw [hvelocity] at hrep
    have hactual : (mfderiv 𝓘(ℝ, ℝ) I γ 0 1 : E) =
        (trivializationAt E (TangentSpace I) p).symmL ℝ (γ 0) u := by
      rw [← hrep]
      exact ((trivializationAt E (TangentSpace I) p).symmL_continuousLinearMapAt
        (R := ℝ) (by rw [hγzero]; exact hbase hq) _).symm
    have hspeedγ : Real.sqrt (g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) ≤ B := by
      rw [hactual, hγzero]
      simpa only [hu, mul_one] using hspeed q hq u
    obtain ⟨φ, hφ, htouch, hupper, hsecond⟩ :=
      hsupport γ hγ (by rwa [hγzero]) hspeedγ
    obtain ⟨ψ, hψ, hψzero, hψupper, hψsecond⟩ :=
      exists_affine_chart_upper_support_of_geodesic_upper_support g p hf hγ
        (by rw [hγzero]; exact hchart hq) (by rwa [hγzero]) hA
        (hΓ _ (mem_image_of_mem _ (by rwa [hγzero]))) hφ htouch hupper
        (by simpa only [hvelocity, hu, one_pow, mul_one] using hsecond)
    refine ⟨ψ, hψ, ?_, ?_, ?_⟩
    · simpa only [Function.comp_apply, hqinv, hγzero] using hψzero
    · simpa only [Function.comp_apply, hγzero, hvelocity] using hψupper
    · simpa only [hvelocity, hu, one_pow, mul_one] using hψsecond
  obtain ⟨ψ, hψ, hψzero, hψupper, hψsecond⟩ :=
    DifferentialGeometry.Analysis.exists_affine_upper_support_of_unit_directions hunits w
  refine ⟨ψ, hψ, ?_, hψupper, hψsecond⟩
  simpa only [Function.comp_apply, hqinv] using hψzero

end DifferentialGeometry.Geometry.Riemannian.Geodesic
