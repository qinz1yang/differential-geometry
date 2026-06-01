import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentArbitraryKQuant
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorMemWtwokTwo
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartLocality

/-!
# Manifold-aggregated `W^{2k, 2}` bound for the connection-Laplacian eigenvector

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and an order `k : ℕ`,
this file ships the **manifold-wide Sobolev bound** for the smooth representative
of the resolvent eigenvector, re-keyed onto the intrinsic compact-operator
eigenbasis `tensorResolventEigenbasisVec`. With resolvent eigenvalue
`μ := i.fst.val ∈ (0, 1]`, the global tensor Sobolev norm
`wtwokTwoNorm g k (eigenvectorSmooth g r s i)` is bounded by
`ENNReal.ofReal (C · μ⁻¹^(2k + 1))` times the `ℝ≥0∞`-valued `L²` norm of the
intrinsic eigenbasis vector, with a single geometric constant `C ≥ 0` uniform
over every eigenbasis index `i`.

## The mechanism

The tensor Sobolev norm `wtwokTwoNorm g k T` decomposes, via the canonical
finite cover `chartAtlasPOU_finset I M`, as a finite double sum of the
chart-component Euclidean Sobolev norms `wkpNorm (2 * k) 2` of the scalar chart
components `tensorChartComp g r s T α Idx Jdx` over their chart targets
(`wtwokTwoNorm_eq_finset_sum`). On the smooth representative
`eigenvectorSmooth g r s i`, each scalar chart component agrees
almost-everywhere with the eigenvector chart component
`eigenvectorChartComponentFun_unconditional`
(`eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun`).

`wkpNorm` is invariant under a.e. equality (`wkpNorm_congr_ae`), and the
arbitrary-order chart-base-uniform Sobolev bound
`eigenvector_chartComponent_wkpNorm_arbitrary` (with order
`K := 2 * k`) yields, for each `α ∈ chartAtlasPOU_finset I M` and component
multi-index pair, a geometric constant `C(α, Idx, Jdx) ≥ 0`, uniform over `i`,
such that
`wkpNorm (2 * k) 2 (eigenvectorChartComponentFun_unconditional α (Idx, Jdx)) ≤
  ENNReal.ofReal (C(α, Idx, Jdx) · μ⁻¹^(2 * k + 1)) · ENNReal.ofReal ‖vec‖`.
Summing those constants over the finite cover and the finite component-index
set produces a single global geometric constant.

## Main result

* `eigenvectorSmooth_wtwokTwoNorm_le_uniform` — the global
  manifold-aggregated `W^{2k, 2}` bound: with a single uniform geometric
  constant `C ≥ 0`,
  `wtwokTwoNorm g k (eigenvectorSmooth g r s i) ≤
    ENNReal.ofReal (C · μ⁻¹^(2k + 1)) · ENNReal.ofReal ‖vec‖`
  for every eigenbasis index `i`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

namespace EigenvectorManifoldAggregateUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)

/-- Chart-locality-free twin of `perChartCompConstant`. -/
private noncomputable def perChartCompConstant
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : ℝ :=
  Classical.choose
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))

/-- Chart-locality-free twin of `perChartCompConstant_nonneg`. -/
private lemma perChartCompConstant_nonneg
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    0 ≤ perChartCompConstant (I := I) (M := M) g r s k α Idx Jdx :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))).1

/-- Chart-locality-free twin of `perChartCompConstant_bound`. -/
private lemma perChartCompConstant_bound
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α (Idx, Jdx))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))).2 i

/-- Chart-locality-free twin of `aggregateConstant`. -/
private noncomputable def aggregateConstant : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        perChartCompConstant (I := I) (M := M) g r s k α Idx Jdx

/-- Chart-locality-free twin of `aggregateConstant_nonneg`. -/
private lemma aggregateConstant_nonneg :
    0 ≤ aggregateConstant (I := I) (M := M) g r s k := by
  classical
  unfold aggregateConstant
  refine Finset.sum_nonneg fun α _ => ?_
  refine Finset.sum_nonneg fun Idx _ => ?_
  refine Finset.sum_nonneg fun Jdx _ => ?_
  exact perChartCompConstant_nonneg
    (I := I) (M := M) g r s k α Idx Jdx

end EigenvectorManifoldAggregateUnconditional

open EigenvectorManifoldAggregateUnconditional

/-- Chart-locality-free twin of `tensorChartComp_eigenvectorSmooth_wkpNorm_le`. -/
private lemma tensorChartComp_eigenvectorSmooth_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s i) α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
  have h_ae :
      tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s i) α Idx Jdx
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α
        (Idx, Jdx) :=
    eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun
      (I := I) (M := M) g r s i α Idx Jdx
  have h_eq :
      wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s
            (eigenvectorSmooth (I := I) (M := M) g r s i)
            α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) =
        wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α (Idx, Jdx))
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae
  rw [h_eq]
  exact perChartCompConstant_bound
    (I := I) (M := M) g r s k α Idx Jdx i

/-- Chart-locality-free twin of `chartTerm_eigenvectorSmooth_le`. -/
private lemma chartTerm_eigenvectorSmooth_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) (α : M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s
              (eigenvectorSmooth (I := I) (M := M) g r s i)
              α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal
          ((∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                perChartCompConstant (I := I) (M := M)
                  g r s k α Idx Jdx)
            * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i‖ := by
  classical
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  have h_double_le :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s
                (eigenvectorSmooth (I := I) (M := M) g r s i)
                α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (perChartCompConstant
                  (I := I) (M := M) g r s k α Idx Jdx *
                    (i.fst.val)⁻¹ ^ (2 * k + 1))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ := by
    intro Idx _hIdx
    refine le_trans (Finset.sum_le_sum (fun Jdx _ =>
      tensorChartComp_eigenvectorSmooth_wkpNorm_le
        (I := I) (M := M) g r s k α Idx Jdx i)) ?_
    rw [← Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum h_double_le) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  have h_inner :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (perChartCompConstant (I := I) (M := M)
                  g r s k α Idx Jdx *
                (i.fst.val)⁻¹ ^ (2 * k + 1))) =
          ENNReal.ofReal
            ((∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              perChartCompConstant (I := I) (M := M)
                g r s k α Idx Jdx) *
              (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
    intro Idx _hIdx
    rw [Finset.sum_mul]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun Jdx _ =>
      mul_nonneg (perChartCompConstant_nonneg
        (I := I) (M := M) g r s k α Idx Jdx) hμ_pow_nn)]
  rw [Finset.sum_congr rfl h_inner]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun Idx _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Jdx _ =>
        perChartCompConstant_nonneg
          (I := I) (M := M) g r s k α Idx Jdx)) hμ_pow_nn)]
  have h_eq :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx) *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) =
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant (I := I) (M := M)
              g r s k α Idx Jdx) *
          (i.fst.val)⁻¹ ^ (2 * k + 1) := by
    rw [Finset.sum_mul]
  rw [h_eq]

/-- Chart-locality-free twin of `eigenvectorSmooth_wtwokTwoNorm_le_uniform`. -/
theorem eigenvectorSmooth_wtwokTwoNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        wtwokTwoNorm (I := I) (M := M) g k
            (eigenvectorSmooth (I := I) (M := M) g r s i)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  refine ⟨aggregateConstant (I := I) (M := M) g r s k,
    aggregateConstant_nonneg (I := I) (M := M) g r s k,
    fun i => ?_⟩
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  rw [wtwokTwoNorm_eq_finset_sum (I := I) (M := M) g k
    (eigenvectorSmooth (I := I) (M := M) g r s i)]
  refine le_trans (Finset.sum_le_sum
    (fun α _hα => chartTerm_eigenvectorSmooth_le
      (I := I) (M := M) g r s k α i)) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Idx _ =>
        Finset.sum_nonneg (fun Jdx _ =>
          perChartCompConstant_nonneg
            (I := I) (M := M) g r s k α Idx Jdx))) hμ_pow_nn)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_mul]
  exact le_of_eq rfl

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
