import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSobolev
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Euclidean
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

private theorem ofReal_add_sum_mul {ι : Type*} [Fintype ι]
    (a : ℝ) (b : ι → ℝ) (c : ℝ) (ha : 0 ≤ a) (hb : ∀ i, 0 ≤ b i) (hc : 0 ≤ c) :
    ENNReal.ofReal (a * c) + ∑ i, ENNReal.ofReal (b i * c) =
      ENNReal.ofReal ((a + ∑ i, b i) * c) := by
  classical
  rw [add_mul, Finset.sum_mul, ENNReal.ofReal_add (mul_nonneg ha hc)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hb i) hc),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hb i) hc)]

theorem exists_wkpNorm_chartInverse_H1ComplDirichletToLp_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1ComplDirichlet q,
      iteratedWeakSobolevNorm 1 2 (fun z => H1ComplDirichletToLp q u
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω ≤
        ENNReal.ofReal (C * ‖u‖) := by
  let R := (chartRestrictionLp q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset)) 2).comp (H1ComplDirichletToLp q)
  let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
  refine ⟨‖R‖ + ∑ i, ‖D i‖, add_nonneg (norm_nonneg R)
    (Finset.sum_nonneg fun i _ => norm_nonneg (D i)), ?_⟩
  intro u
  let v : EuStd → ℝ := fun z => H1ComplDirichletToLp q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  have hv : MemWkp 1 2 v Ω := memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u
  have heq : (R u : EuStd → ℝ) =ᵐ[volume.restrict Ω] v :=
    chartRestrictionLp_coeFn q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) 2 (H1ComplDirichletToLp q u)
  have hD (i : Fin (Module.finrank ℝ EuN)) : chosenWeakPartial' 2 i v Ω =ᵐ[volume.restrict Ω]
      (D i u : EuStd → ℝ) :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ
      (chosenWeakPartial'_isWeakPartial_of_mem hv.memW1p i)
      (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i u)
      ((chosenWeakPartial'_memLp_of_mem hv.memW1p i).locallyIntegrable (by norm_num))
      ((Lp.memLp _).locallyIntegrable (by norm_num))
  have hzero : eLpNorm v 2 (volume.restrict Ω) ≤ ENNReal.ofReal (‖R‖ * ‖u‖) := by
    rw [← eLpNorm_congr_ae heq, ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (R.le_opNorm u)
  have hpart (i : Fin (Module.finrank ℝ EuN)) :
      eLpNorm (chosenWeakPartial' 2 i v Ω) 2 (volume.restrict Ω) ≤
        ENNReal.ofReal (‖D i‖ * ‖u‖) := by
    rw [eLpNorm_congr_ae (hD i), ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((D i).le_opNorm u)
  change iteratedWeakSobolevNorm 1 2 v Ω ≤ _
  rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial 0 2 Ω v]
  simp only [wkpNorm_zero]
  calc
    _ ≤ ENNReal.ofReal (‖R‖ * ‖u‖) + ∑ i, ENNReal.ofReal (‖D i‖ * ‖u‖) :=
      add_le_add hzero (Finset.sum_le_sum fun i _ => hpart i)
    _ = ENNReal.ofReal ((‖R‖ + ∑ i, ‖D i‖) * ‖u‖) := by
      exact ofReal_add_sum_mul ‖R‖ (fun i => ‖D i‖) ‖u‖
        (norm_nonneg R) (fun i => norm_nonneg (D i)) (norm_nonneg u)

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
