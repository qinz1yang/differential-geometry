import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentArbitraryKQuant
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorMemWtwokTwo
import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartLocality

/-!
# Manifold-aggregated `W^{2k, 2}` bound for the connection-Laplacian eigenvector

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, and an order `k : ℕ`, this file ships the **manifold-wide
Sobolev bound** for the smooth representative of the resolvent eigenvector. With
resolvent eigenvalue `μ := i.fst.val ∈ (0, 1]`, the global tensor Sobolev norm
`wtwokTwoNorm g k (eigenvectorSmooth g r s h_atlas i)` is bounded by
`ENNReal.ofReal (C · μ⁻¹^(2k + 1))` times `ENNReal.ofReal ‖tensorResolventEigenbasisVec h_atlas i‖`,
with a single geometric constant `C ≥ 0` uniform over every eigenbasis index `i`.

## The mechanism

The tensor Sobolev norm `wtwokTwoNorm g k T` decomposes, via the canonical
finite cover `chartAtlasPOU_finset I M`, as a finite double sum of the
chart-component Euclidean Sobolev norms `wkpNorm (2 * k) 2` of the scalar chart
components `tensorChartComp g r s T α Idx Jdx` over their chart targets
(`wtwokTwoNorm_eq_finset_sum`). On the smooth representative
`eigenvectorSmooth g r s h_atlas i`, each scalar chart component agrees
almost-everywhere with the eigenvector chart component
`eigenvectorChartComponentFun` (`eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun`).

`wkpNorm` is invariant under a.e. equality (`wkpNorm_congr_ae`), and the
arbitrary-order chart-base-uniform Sobolev bound
`eigenvector_chartComponent_wkpNorm_arbitrary` (with order `K := 2 * k`) yields,
for each `α ∈ chartAtlasPOU_finset I M` and component multi-index pair, a
geometric constant `C(α, Idx, Jdx) ≥ 0`, uniform over `i`, such that
`wkpNorm (2 * k) 2 (eigenvectorChartComponentFun α (Idx, Jdx)) ≤
  ENNReal.ofReal (C(α, Idx, Jdx) · μ⁻¹^(2 * k + 1)) · ENNReal.ofReal ‖vec‖`.
Summing those constants over the finite cover and the finite component-index
set produces a single global geometric constant.

## Main result

* `eigenvectorSmooth_wtwokTwoNorm_le_uniform` — the global manifold-aggregated
  `W^{2k, 2}` bound: with a single uniform geometric constant `C ≥ 0`,
  `wtwokTwoNorm g k (eigenvectorSmooth g r s h_atlas i) ≤
    ENNReal.ofReal (C · μ⁻¹^(2k + 1)) · ENNReal.ofReal ‖tensorResolventEigenbasisVec h_atlas i‖`
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

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Per chart-base-point and per component-index constants

For each chart base point `α ∈ chartAtlasPOU_finset I M` and each component
multi-index pair `(Idx, Jdx)`, the arbitrary-order chart-base-uniform headline
`eigenvector_chartComponent_wkpNorm_arbitrary` (specialised to order `2 * k`)
provides a chart-geometric constant `C(α, Idx, Jdx) ≥ 0`, uniform over every
eigenbasis index `i`, witnessing the per-component Sobolev bound. We pick the
witness with `Classical.choose` and aggregate the constants. -/

namespace EigenvectorManifoldAggregate

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (k : ℕ)

/-- The per-`(α, Idx, Jdx)` chart-geometric constant from the arbitrary-order
chart-base-uniform headline at order `2 * k`. -/
private noncomputable def perChartCompConstant
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : ℝ :=
  Classical.choose
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s h_atlas (2 * k) α (Idx, Jdx))

/-- The per-`(α, Idx, Jdx)` chart-geometric constant is non-negative. -/
private lemma perChartCompConstant_nonneg
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    0 ≤ perChartCompConstant (I := I) (M := M) g r s h_atlas k α Idx Jdx :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s h_atlas (2 * k) α (Idx, Jdx))).1

/-- The per-`(α, Idx, Jdx)` chart-geometric constant witnesses the bound on the
eigenvector chart component, uniformly in the eigenbasis index `i`. -/
private lemma perChartCompConstant_bound
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α (Idx, Jdx))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant (I := I) (M := M) g r s h_atlas k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M) h_atlas i‖ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary (I := I) (M := M)
      g r s h_atlas (2 * k) α (Idx, Jdx))).2 i

/-- The aggregated chart-geometric constant: sum of `perChartCompConstant` over
the canonical finite cover and the finite component-index set. -/
private noncomputable def aggregateConstant : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        perChartCompConstant (I := I) (M := M) g r s h_atlas k α Idx Jdx

/-- The aggregated chart-geometric constant is non-negative. -/
private lemma aggregateConstant_nonneg :
    0 ≤ aggregateConstant (I := I) (M := M) g r s h_atlas k := by
  classical
  unfold aggregateConstant
  refine Finset.sum_nonneg fun α _ => ?_
  refine Finset.sum_nonneg fun Idx _ => ?_
  refine Finset.sum_nonneg fun Jdx _ => ?_
  exact perChartCompConstant_nonneg
    (I := I) (M := M) g r s h_atlas k α Idx Jdx

end EigenvectorManifoldAggregate

open EigenvectorManifoldAggregate

/-! ## Per-`(α, Idx, Jdx)` bound on the chart component of the smooth representative

The bound from `eigenvector_chartComponent_wkpNorm_arbitrary` is on
`eigenvectorChartComponentFun`; the global Sobolev norm `wtwokTwoNorm` uses
`tensorChartComp`. The almost-everywhere identity
`eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun` plus
`wkpNorm_congr_ae` transports the bound. -/

/-- The per-chart, per-component Sobolev bound on `tensorChartComp` of the
smooth eigenvector representative, transported from
`eigenvector_chartComponent_wkpNorm_arbitrary` via the a.e.-identity. -/
private lemma tensorChartComp_eigenvectorSmooth_wkpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (k : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i) α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant (I := I) (M := M) g r s h_atlas k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M) h_atlas i‖ := by
  -- A.e.-identity between the two chart components on the chart target.
  have h_ae :
      tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i) α Idx Jdx
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α
        (Idx, Jdx) :=
    eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun
      (I := I) (M := M) g r s h_atlas i α Idx Jdx
  -- The `wkpNorm` is invariant under a.e. equality.
  have h_eq :
      wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s
            (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i) α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) =
        wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α
            (Idx, Jdx))
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae
  rw [h_eq]
  exact perChartCompConstant_bound
    (I := I) (M := M) g r s h_atlas k α Idx Jdx i

/-! ## Aggregation step: bound each chart-base summand of `wtwokTwoNorm`

For each chart base point `α ∈ chartAtlasPOU_finset I M`, the per-`α`
contribution to `wtwokTwoNorm` — itself a finite double sum over component
multi-indices — is bounded by the corresponding per-`α` sum of the
chart-geometric constants times `μ⁻¹^(2k + 1)` times `ofReal ‖vec‖`. -/

/-- For each chart base point, the per-`α` contribution to the global Sobolev
norm is bounded by the per-`α` partial sum of the chart-geometric constants. -/
private lemma chartTerm_eigenvectorSmooth_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (k : ℕ) (α : M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s
              (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i) α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal
          ((∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                perChartCompConstant (I := I) (M := M) g r s h_atlas k α Idx Jdx)
            * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec
            (I := I) (M := M) h_atlas i‖ := by
  classical
  -- Eigenvalue inverse is at least one (in particular non-negative).
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s h_atlas i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  -- Pointwise bound on each `(Idx, Jdx)` summand.
  have h_double_le :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s
                (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i) α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (perChartCompConstant
                  (I := I) (M := M) g r s h_atlas k α Idx Jdx *
                    (i.fst.val)⁻¹ ^ (2 * k + 1))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M) h_atlas i‖ := by
    intro Idx _hIdx
    -- First: each Jdx-summand is bounded.
    refine le_trans (Finset.sum_le_sum (fun Jdx _ =>
      tensorChartComp_eigenvectorSmooth_wkpNorm_le
        (I := I) (M := M) g r s h_atlas k α Idx Jdx i)) ?_
    -- Now we have ∑ Jdx of `ofReal ... * ofReal ‖vec‖`; factor out the second.
    rw [← Finset.sum_mul]
  -- Sum the bound over Idx.
  refine le_trans (Finset.sum_le_sum h_double_le) ?_
  -- Factor out `ofReal ‖vec‖` from the outer sum.
  rw [← Finset.sum_mul]
  -- Combine the double sum of `ofReal(C * μ_pow)` into a single `ofReal`.
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  -- Convert the double sum of `ofReal` constants into one `ofReal` of the
  -- double sum.
  have h_inner :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (perChartCompConstant (I := I) (M := M) g r s h_atlas k α Idx Jdx *
                (i.fst.val)⁻¹ ^ (2 * k + 1))) =
          ENNReal.ofReal
            ((∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              perChartCompConstant (I := I) (M := M) g r s h_atlas k α Idx Jdx) *
              (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
    intro Idx _hIdx
    -- Push `(i.fst.val)⁻¹^(2k+1)` out of the `ofReal` and the inner sum.
    rw [Finset.sum_mul]
    -- Pull `ofReal` outside: sum of `ofReal` of nonneg = `ofReal` of sum.
    rw [← ENNReal.ofReal_sum_of_nonneg (fun Jdx _ =>
      mul_nonneg (perChartCompConstant_nonneg
        (I := I) (M := M) g r s h_atlas k α Idx Jdx) hμ_pow_nn)]
  rw [Finset.sum_congr rfl h_inner]
  -- Now the outer sum is ∑ Idx, ofReal((∑ Jdx C_α_Idx_Jdx) * μ⁻¹^(2k+1)).
  -- Combine to a single `ofReal` of the triple sum (here double, Idx × Jdx).
  rw [← ENNReal.ofReal_sum_of_nonneg (fun Idx _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Jdx _ =>
        perChartCompConstant_nonneg
          (I := I) (M := M) g r s h_atlas k α Idx Jdx)) hμ_pow_nn)]
  -- Pull `(i.fst.val)⁻¹^(2k+1)` out of the outer sum.
  have h_eq :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant (I := I) (M := M) g r s h_atlas k α Idx Jdx) *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) =
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant (I := I) (M := M) g r s h_atlas k α Idx Jdx) *
          (i.fst.val)⁻¹ ^ (2 * k + 1) := by
    rw [Finset.sum_mul]
  rw [h_eq]

/-! ## The manifold-aggregated headline -/

/-- **Manifold-aggregated `W^{2k, 2}` Sobolev bound for the connection-Laplacian
eigenvector.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, the uniform-Sobolev
hypothesis `h_atlas`, and an order `k : ℕ`, there is a chart-geometric
constant `C ≥ 0` — uniform over *every* eigenbasis index `i` — such that the
global tensor Sobolev norm `wtwokTwoNorm g k (eigenvectorSmooth …)` of the
smooth representative of the resolvent eigenvector is bounded by
`ENNReal.ofReal (C * μ⁻¹^(2k + 1))` times the `ℝ≥0∞`-valued `L²` norm of the
abstract eigenbasis vector `tensorResolventEigenbasisVec h_atlas i`, where
`μ := i.fst.val ∈ (0, 1]` is the resolvent eigenvalue.

The proof aggregates the chart-base-uniform Sobolev bound
`eigenvector_chartComponent_wkpNorm_arbitrary` (at order `2 * k`) over the
canonical finite cover `chartAtlasPOU_finset I M` and the finite component-index
set. Each chart component of the smooth representative agrees almost-everywhere
on the chart target with the corresponding eigenvector chart component
(`eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun`), so `wkpNorm` is
invariant. -/
theorem eigenvectorSmooth_wtwokTwoNorm_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        wtwokTwoNorm (I := I) (M := M) g k
            (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec
                (I := I) (M := M) h_atlas i‖ := by
  classical
  refine ⟨aggregateConstant (I := I) (M := M) g r s h_atlas k,
    aggregateConstant_nonneg (I := I) (M := M) g r s h_atlas k, fun i => ?_⟩
  -- Eigenvalue inverse is at least one (in particular non-negative).
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s h_atlas i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  -- Decompose `wtwokTwoNorm` as a finite sum over the canonical cover.
  rw [wtwokTwoNorm_eq_finset_sum (I := I) (M := M) g k
    (eigenvectorSmooth (I := I) (M := M) g r s h_atlas i)]
  -- Bound each summand using `chartTerm_eigenvectorSmooth_le`.
  refine le_trans (Finset.sum_le_sum
    (fun α _hα => chartTerm_eigenvectorSmooth_le
      (I := I) (M := M) g r s h_atlas k α i)) ?_
  -- Factor out `ofReal ‖vec‖` from the outer sum.
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  -- Convert the sum of `ofReal` of nonneg into one `ofReal`.
  rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Idx _ =>
        Finset.sum_nonneg (fun Jdx _ =>
          perChartCompConstant_nonneg
            (I := I) (M := M) g r s h_atlas k α Idx Jdx))) hμ_pow_nn)]
  -- Factor out `(i.fst.val)⁻¹^(2k+1)` from the outer sum.
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_mul]
  exact le_of_eq rfl

/-! ## Chart-locality-free twins

The declarations below re-establish the manifold-aggregated `W^{2k, 2}` bound on
the smooth eigenvector representative *without* the chart-locality hypothesis,
re-keying every chart-uniform input onto the intrinsic compact-operator
eigenbasis `tensorResolventEigenbasisVec_ofCompact`. -/

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

namespace EigenvectorManifoldAggregateUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)

/-- Chart-locality-free twin of `perChartCompConstant`. -/
private noncomputable def perChartCompConstant_unconditional
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) : ℝ :=
  Classical.choose
    (eigenvector_chartComponent_wkpNorm_arbitrary_unconditional (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))

/-- Chart-locality-free twin of `perChartCompConstant_nonneg`. -/
private lemma perChartCompConstant_nonneg_unconditional
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    0 ≤ perChartCompConstant_unconditional (I := I) (M := M) g r s k α Idx Jdx :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary_unconditional (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))).1

/-- Chart-locality-free twin of `perChartCompConstant_bound`. -/
private lemma perChartCompConstant_bound_unconditional
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α (Idx, Jdx))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant_unconditional (I := I) (M := M)
              g r s k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_arbitrary_unconditional (I := I) (M := M)
      g r s (2 * k) α (Idx, Jdx))).2 i

/-- Chart-locality-free twin of `aggregateConstant`. -/
private noncomputable def aggregateConstant_unconditional : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        perChartCompConstant_unconditional (I := I) (M := M) g r s k α Idx Jdx

/-- Chart-locality-free twin of `aggregateConstant_nonneg`. -/
private lemma aggregateConstant_nonneg_unconditional :
    0 ≤ aggregateConstant_unconditional (I := I) (M := M) g r s k := by
  classical
  unfold aggregateConstant_unconditional
  refine Finset.sum_nonneg fun α _ => ?_
  refine Finset.sum_nonneg fun Idx _ => ?_
  refine Finset.sum_nonneg fun Jdx _ => ?_
  exact perChartCompConstant_nonneg_unconditional
    (I := I) (M := M) g r s k α Idx Jdx

end EigenvectorManifoldAggregateUnconditional

open EigenvectorManifoldAggregateUnconditional

/-- Chart-locality-free twin of `tensorChartComp_eigenvectorSmooth_wkpNorm_le`. -/
private lemma tensorChartComp_eigenvectorSmooth_wkpNorm_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i) α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perChartCompConstant_unconditional (I := I) (M := M)
              g r s k α Idx Jdx *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
  -- A.e.-identity between the two chart components on the chart target.  The
  -- intrinsic eigenvector chart component `eigenvectorChartComponentFun_ofCompact`
  -- and the canonical chart component `eigenvectorChartComponentFun_unconditional`
  -- share their definitional body, so the a.e.-identity transports verbatim.
  have h_ae :
      tensorChartComp (I := I) (M := M) g r s
          (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i) α Idx Jdx
        =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α
        (Idx, Jdx) :=
    eigenvectorSmooth_tensorChartComp_aeEq_chartComponentFun_unconditional
      (I := I) (M := M) g r s i α Idx Jdx
  -- The `wkpNorm` is invariant under a.e. equality.
  have h_eq :
      wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s
            (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)
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
  exact perChartCompConstant_bound_unconditional
    (I := I) (M := M) g r s k α Idx Jdx i

/-- Chart-locality-free twin of `chartTerm_eigenvectorSmooth_le`. -/
private lemma chartTerm_eigenvectorSmooth_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) (α : M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s
              (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)
              α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal
          ((∑ Idx : Fin r → Fin (Module.finrank ℝ E),
              ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
                perChartCompConstant_unconditional (I := I) (M := M)
                  g r s k α Idx Jdx)
            * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact
            (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
  classical
  -- Eigenvalue inverse is at least one (in particular non-negative).
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le_unconditional (I := I) (M := M) g r s i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  -- Pointwise bound on each `(Idx, Jdx)` summand.
  have h_double_le :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s
                (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)
                α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              ENNReal.ofReal
                (perChartCompConstant_unconditional
                  (I := I) (M := M) g r s k α Idx Jdx *
                    (i.fst.val)⁻¹ ^ (2 * k + 1))) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖ := by
    intro Idx _hIdx
    -- First: each Jdx-summand is bounded.
    refine le_trans (Finset.sum_le_sum (fun Jdx _ =>
      tensorChartComp_eigenvectorSmooth_wkpNorm_le_unconditional
        (I := I) (M := M) g r s k α Idx Jdx i)) ?_
    -- Now we have ∑ Jdx of `ofReal ... * ofReal ‖vec‖`; factor out the second.
    rw [← Finset.sum_mul]
  -- Sum the bound over Idx.
  refine le_trans (Finset.sum_le_sum h_double_le) ?_
  -- Factor out `ofReal ‖vec‖` from the outer sum.
  rw [← Finset.sum_mul]
  -- Combine the double sum of `ofReal(C * μ_pow)` into a single `ofReal`.
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  -- Convert the double sum of `ofReal` constants into one `ofReal` of the
  -- double sum.
  have h_inner :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ _hIdx : Idx ∈ (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))),
        (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (perChartCompConstant_unconditional (I := I) (M := M)
                  g r s k α Idx Jdx *
                (i.fst.val)⁻¹ ^ (2 * k + 1))) =
          ENNReal.ofReal
            ((∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              perChartCompConstant_unconditional (I := I) (M := M)
                g r s k α Idx Jdx) *
              (i.fst.val)⁻¹ ^ (2 * k + 1)) := by
    intro Idx _hIdx
    -- Push `(i.fst.val)⁻¹^(2k+1)` out of the `ofReal` and the inner sum.
    rw [Finset.sum_mul]
    -- Pull `ofReal` outside: sum of `ofReal` of nonneg = `ofReal` of sum.
    rw [← ENNReal.ofReal_sum_of_nonneg (fun Jdx _ =>
      mul_nonneg (perChartCompConstant_nonneg_unconditional
        (I := I) (M := M) g r s k α Idx Jdx) hμ_pow_nn)]
  rw [Finset.sum_congr rfl h_inner]
  -- Now the outer sum is ∑ Idx, ofReal((∑ Jdx C_α_Idx_Jdx) * μ⁻¹^(2k+1)).
  -- Combine to a single `ofReal` of the triple sum (here double, Idx × Jdx).
  rw [← ENNReal.ofReal_sum_of_nonneg (fun Idx _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Jdx _ =>
        perChartCompConstant_nonneg_unconditional
          (I := I) (M := M) g r s k α Idx Jdx)) hμ_pow_nn)]
  -- Pull `(i.fst.val)⁻¹^(2k+1)` out of the outer sum.
  have h_eq :
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          (∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant_unconditional (I := I) (M := M)
              g r s k α Idx Jdx) *
            (i.fst.val)⁻¹ ^ (2 * k + 1)) =
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            perChartCompConstant_unconditional (I := I) (M := M)
              g r s k α Idx Jdx) *
          (i.fst.val)⁻¹ ^ (2 * k + 1) := by
    rw [Finset.sum_mul]
  rw [h_eq]

/-- Chart-locality-free twin of `eigenvectorSmooth_wtwokTwoNorm_le_uniform`. -/
theorem eigenvectorSmooth_wtwokTwoNorm_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        wtwokTwoNorm (I := I) (M := M) g k
            (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (2 * k + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact
                (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  refine ⟨aggregateConstant_unconditional (I := I) (M := M) g r s k,
    aggregateConstant_nonneg_unconditional (I := I) (M := M) g r s k,
    fun i => ?_⟩
  -- Eigenvalue inverse is at least one (in particular non-negative).
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    le_trans zero_le_one
      (sharpDiff_eigen_inv_one_le_unconditional (I := I) (M := M) g r s i)
  have hμ_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (2 * k + 1) :=
    pow_nonneg hμ_inv_nn _
  -- Decompose `wtwokTwoNorm` as a finite sum over the canonical cover.
  rw [wtwokTwoNorm_eq_finset_sum (I := I) (M := M) g k
    (eigenvectorSmooth_unconditional (I := I) (M := M) g r s i)]
  -- Bound each summand using `chartTerm_eigenvectorSmooth_le_unconditional`.
  refine le_trans (Finset.sum_le_sum
    (fun α _hα => chartTerm_eigenvectorSmooth_le_unconditional
      (I := I) (M := M) g r s k α i)) ?_
  -- Factor out `ofReal ‖vec‖` from the outer sum.
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  -- Convert the sum of `ofReal` of nonneg into one `ofReal`.
  rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun Idx _ =>
        Finset.sum_nonneg (fun Jdx _ =>
          perChartCompConstant_nonneg_unconditional
            (I := I) (M := M) g r s k α Idx Jdx))) hμ_pow_nn)]
  -- Factor out `(i.fst.val)⁻¹^(2k+1)` from the outer sum.
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_mul]
  exact le_of_eq rfl

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
