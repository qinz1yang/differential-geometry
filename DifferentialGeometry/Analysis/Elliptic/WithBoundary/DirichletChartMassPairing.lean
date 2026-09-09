import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletWeakPartialDual
import DifferentialGeometry.Analysis.Integration.Lp.ProductL2

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

theorem integral_mass_inner_eq_integral_chart_prod
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Ω)
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (τ : Lp ℝ 2 μ) (v : Lp (H1ComplDirichlet q) 2 μ)
    (P : Lp (Lp ℝ 2 (volume.restrict Ω)) 2 μ)
    (F : Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (hF : ∀ᵐ t ∂μ, (fun x => F (t, x)) =ᵐ[volume.restrict Ω] (P t : EuStd → ℝ))
    (z : H1ComplDirichlet q)
    (hv : ∀ᵐ t ∂μ, (H1ComplDirichletToLp q (v t) : M → ℝ) =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
      chartPullback I_hs α (fun x => η x * P t x)) :
    (∫ t, τ t * inner ℝ (H1ComplDirichletToLp q (v t))
      (H1ComplDirichletToLp q z) ∂μ) =
      ∫ p, τ p.1 * η p.2 * MetricExtension.densityOnEuclid q α p.2 * F p *
        H1ComplDirichletToLp q z ((extChartAt I_hs α).symm
          ((toEuclidean (E := EuN)).symm p.2)) ∂μ.prod (volume.restrict Ω) := by
  let c : EuStd → ℝ := fun x => MetricExtension.densityOnEuclid q α x * η x
  have hcs : tsupport c ⊆ Ω := tsupport_mul_subset_right.trans hηs
  have hc : ContDiff ℝ (⊤ : ℕ∞) c :=
    (((MetricExtension.densityOnEuclid_contDiffOn q α).mono
      (subset_closure.trans (hΩs.trans (image_mono interior_subset)))).mul
        hη.contDiffOn).contDiff_of_tsupport_subset hΩ hcs
  have hcm : MemLp c ∞ (volume.restrict Ω) :=
    hc.continuous.memLp_top_of_hasCompactSupport hηc.mul_left _
  let R := chartRestrictionLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q z)
  have hR : (R : EuStd → ℝ) =ᵐ[volume.restrict Ω] fun x =>
      H1ComplDirichletToLp q z ((extChartAt I_hs α).symm
        ((toEuclidean (E := EuN)).symm x)) :=
    chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q z)
  let ψ : EuStd → ℝ := fun x => c x * H1ComplDirichletToLp q z
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm x))
  have hψ : MemLp ψ 2 (volume.restrict Ω) :=
    ((Lp.memLp R).ae_eq hR).mul' hcm
  calc
    _ = ∫ t, τ t * (∫ x in Ω, P t x * ψ x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hv] with t hvt
      rw [inner_eq_integral_chartPullback_mul q α hΩs hη hηs (P t) (v t) z hvt]
      apply congrArg (fun r : ℝ => τ t * r)
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [ψ, c]
      exact mul_assoc _ _ _
    _ = ∫ p, τ p.1 * F p * ψ p.2 ∂μ.prod (volume.restrict Ω) :=
      MeasureTheory.integral_mul_integral_lp_eq_integral_prod P F hF τ hψ
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [ψ, c]
      ring

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
