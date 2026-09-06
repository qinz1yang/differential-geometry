import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDivergence
import DifferentialGeometry.Geometry.Operator.HessianTraceChartGramRegularity
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.LocalFormula

noncomputable section

open Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem

theorem integral_chart_diffusion_eq_neg_sum_integral
    (q h : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (u : H1ComplDirichlet q) {ψ : EuStd → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ω) :
    let e := toEuclidean (E := EuN)
    let ρ := fun z => chartDensityOnE (I := I_hs) h α (e.symm z)
    let C := fun i j z => ρ z * chartInvGramOnE (I := I_hs) h α i j (e.symm z)
    (∫ z in Ω, H1ComplDirichletToLp q u ((extChartAt I_hs α).symm (e.symm z)) *
      ∑ i, fderiv ℝ (fun y => ∑ j, C i j y * fderiv ℝ ψ y (EuclideanSpace.single j 1)) z
        (EuclideanSpace.single i 1)) =
      -∑ i, ∫ z in Ω, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u z *
        ∑ j, C i j z * fderiv ℝ ψ z (EuclideanSpace.single j 1) := by
  intro e ρ C
  have hy {z : EuStd} (hz : z ∈ Ω) : e.symm z ∈ (extChartAt I_hs α).target := by
    obtain ⟨y, hy, he⟩ := hΩs (subset_closure hz)
    subst z
    exact interior_subset (by simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy)
  have hC (i j : Fin (Module.finrank ℝ EuN)) :
      ContDiffOn ℝ (⊤ : ℕ∞) (C i j) Ω := by
    exact ((chartDensityOnE_contDiffOn (I := I_hs) h α).comp e.symm.contDiff.contDiffOn
      (fun _ hz => hy hz)).mul
        ((chartInvGramOnE_contDiffOn (I := I_hs) h α i j).comp e.symm.contDiff.contDiffOn
          (fun _ hz => hy hz))
  have hval : MemLp (fun z => H1ComplDirichletToLp q u
      ((extChartAt I_hs α).symm (e.symm z))) 2 (volume.restrict Ω) := by
    have ht := hΩs.trans (image_mono interior_subset)
    exact (Lp.memLp (chartRestrictionLp q α hΩ.measurableSet hΩc ht 2
      (H1ComplDirichletToLp q u))).ae_eq
      (chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc ht 2 (H1ComplDirichletToLp q u))
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.integral_mul_sum_fderiv_mul_eq_neg_sum_integral
    hΩ (hval.locallyIntegrable (by norm_num))
    (fun i => hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u)
    hC hψ hψc hψs

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
