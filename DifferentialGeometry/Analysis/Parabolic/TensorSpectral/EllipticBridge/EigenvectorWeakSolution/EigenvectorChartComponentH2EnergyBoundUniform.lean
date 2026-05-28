import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentH2EnergyBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedData
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TensorChartComponentSobolevBound

/-!
# A chart-base-uniform order-2 Sobolev energy bound for the eigenvector chart
component

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, the per-`(α, P₀)`
order-2 Sobolev energy bound
`eigenvector_chartComponent_wkpNorm_two_energy_le` exposes, for each pair of a
chart base point `α : M` and a chart-component multi-index
`P₀ : TensorCompIdx r s`, a chart-geometric constant `C(α, P₀) ≥ 0` —
eigenbasis-uniform — bounding the `wkpNorm 2 2`-norm of the eigenvector chart
component on the Euclidean chart target by `C(α, P₀) · μ⁻¹ · ‖vec‖`. This file
hoists the chart base point `α` and the component multi-index `P₀` inside the
universal quantifier of a single existential, yielding a single constant `C`
that controls the chart component for *every* `(α, P₀, i)` simultaneously.

The strategy mirrors `TensorChartComponentSobolevBound`: on a compact
manifold the chart-atlas partition of unity is locally finite, so only finitely
many `α : M` have non-empty support of `chartAtlasPOU α`. For the inactive `α`,
the chart component is almost everywhere zero on the chart target — its
partition-of-unity kernel `chartPouKernel α` reduces to the empty set, so the
already committed a.e.-vanishing-off-kernel lemma gives a.e.-vanishing on the
entire chart target, hence a zero `wkpNorm`. For the finitely many active `α`,
the per-`(α, P₀)` constant is the `Classical.choose` of the per-`(α, P₀)`
bound; summing those constants over the finite product of the active finset
with `TensorCompIdx r s` yields the single chart-base-uniform constant.

## Main result

* `eigenvector_chartComponent_wkpNorm_two_energy_le_uniform_β` — the
  chart-base-uniform order-2 Sobolev energy bound: a single constant `C ≥ 0`
  bounds the chart component for every `(α, P₀, i)`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Bridge between the two `chartTargetEuclid` definitions

The chart target set `toEuclidean '' (extChartAt I α).target` is defined twice
in the codebase — once in `Sobolev.Chart` (the one used in this file's
signatures), once in `Laplacian.MetricExtension` (the one used by the
`eigenvectorChartComponentFun_ae_zero_off_chartPouKernel` lemma). The two are
the same set on the nose. -/

private lemma chartTargetEuclid_eq (α : M) :
    (chartTargetEuclid (I := I) (M := M) α : Set EuclN) =
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
        (I := I) (M := M) α := rfl

/-! ## The partition-of-unity kernel vanishes on inactive chart base points

If `α : M` is *inactive* — meaning `chartAtlasPOU I M α` is identically zero —
then the closed support of that weight is empty, and consequently the
partition-of-unity kernel `chartPouKernel α` itself is empty. The eigenvector
chart component then vanishes almost everywhere on the entire chart target,
because the committed `eigenvectorChartComponentFun_ae_zero_off_chartPouKernel`
gives a.e.-vanishing on `chartTargetEuclid α \ chartPouKernel α =
chartTargetEuclid α \ ∅ = chartTargetEuclid α`. -/

/-- The partition-of-unity kernel `chartPouKernel α` is empty whenever
`chartAtlasPOU I M α` is identically zero. -/
private lemma chartPouKernel_eq_empty_of_pou_zero {α : M}
    (h_zero : ∀ x : M,
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) :
    chartPouKernel (I := I) (M := M) α = (∅ : Set EuclN) := by
  classical
  have h_supp_empty :
      Function.support (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
    ext x
    simp [Function.mem_support, h_zero x]
  have h_tsupp_empty :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
    unfold tsupport
    rw [h_supp_empty]
    exact closure_empty
  unfold chartPouKernel
  rw [h_tsupp_empty]
  rw [Set.image_empty, Set.image_empty]

/-- The partition-of-unity kernel `chartPouKernel α` is empty whenever `α : M`
is not in the active finset `chartAtlasPOU_activeFinset I M`. -/
private lemma chartPouKernel_eq_empty_of_notMem_activeFinset
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M) :
    chartPouKernel (I := I) (M := M) α = (∅ : Set EuclN) :=
  chartPouKernel_eq_empty_of_pou_zero
    (chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα)

/-- For an inactive chart base point, the eigenvector chart component is
almost everywhere zero on the entire chart target. -/
private lemma eigenvectorChartComponentFun_ae_zero_of_notMem_activeFinset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_kernel_empty :
      chartPouKernel (I := I) (M := M) α = (∅ : Set EuclN) :=
    chartPouKernel_eq_empty_of_notMem_activeFinset (I := I) (M := M) hα
  -- The committed a.e.-vanishing on
  -- `MetricExtension.chartTargetEuclid α \ chartPouKernel α`.
  have h_ae := eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s h_atlas i α P₀
  -- Bridge the two `chartTargetEuclid` namespaces (they are propositionally
  -- equal on the nose).
  have h_target_eq := chartTargetEuclid_eq (I := I) (M := M) α
  -- Rewrite the restriction set: with the kernel empty, the difference is the
  -- whole chart target.
  have h_set_eq :
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
            (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α := by
    rw [h_kernel_empty, Set.diff_empty, ← h_target_eq]
  rw [h_set_eq] at h_ae
  exact h_ae

/-- For an inactive chart base point, the `wkpNorm 2 2` of the eigenvector
chart component on the chart target is zero. -/
private lemma wkpNorm_two_eigenvectorChartComponentFun_eq_zero_of_notMem_activeFinset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  classical
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_ae_zero :=
    eigenvectorChartComponentFun_ae_zero_of_notMem_activeFinset
      (I := I) (M := M) g r s h_atlas i hα P₀
  have h_swap :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 2 2
          (fun _ : EuclN => (0 : ℝ))
          (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open
      h_ae_zero
  rw [h_swap]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open

/-! ## The per-`(α, P₀)` constant extracted by `Classical.choose` -/

/-- The per-`(α, P₀)` constant from the per-`(α, P₀)` order-2 Sobolev energy
bound, extracted by `Classical.choose`. -/
private noncomputable def perAlphaPCConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : ℝ :=
  Classical.choose
    (eigenvector_chartComponent_wkpNorm_two_energy_le
      (I := I) (M := M) g r s h_atlas α P₀)

private lemma perAlphaPCConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    0 ≤ perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_two_energy_le
      (I := I) (M := M) g r s h_atlas α P₀)).1

private lemma perAlphaPCConstant_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀ *
            (i.fst.val)⁻¹) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_two_energy_le
      (I := I) (M := M) g r s h_atlas α P₀)).2 i

/-! ## The chart-base-uniform constant `C`: sum over the active finset and
`TensorCompIdx` -/

/-- The chart-base-uniform constant: sum of `perAlphaPCConstant g r s h_atlas
α P₀` over `α` in the active finset and `P₀ : TensorCompIdx`. -/
private noncomputable def totalActivePCConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M) :
    ℝ :=
  ∑ α ∈ chartAtlasPOU_activeFinset I M,
    ∑ P₀ : TensorCompIdx (E := E) r s,
      perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀

private lemma totalActivePCConstant_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M) :
    0 ≤ totalActivePCConstant (I := I) (M := M) g r s h_atlas := by
  classical
  unfold totalActivePCConstant
  refine Finset.sum_nonneg fun α _ => ?_
  exact Finset.sum_nonneg fun P₀ _ =>
    perAlphaPCConstant_nonneg (I := I) (M := M) g r s h_atlas α P₀

private lemma perAlphaPCConstant_le_totalActivePCConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    {α : M} (hα : α ∈ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) :
    perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀ ≤
      totalActivePCConstant (I := I) (M := M) g r s h_atlas := by
  classical
  unfold totalActivePCConstant
  -- First peel off the outer α-sum.
  have h_inner_le :
      perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀ ≤
        ∑ Q : TensorCompIdx (E := E) r s,
          perAlphaPCConstant (I := I) (M := M) g r s h_atlas α Q :=
    Finset.single_le_sum
      (f := fun Q : TensorCompIdx (E := E) r s =>
        perAlphaPCConstant (I := I) (M := M) g r s h_atlas α Q)
      (fun Q _ => perAlphaPCConstant_nonneg (I := I) (M := M) g r s h_atlas α Q)
      (Finset.mem_univ P₀)
  have h_outer_le :
      (∑ Q : TensorCompIdx (E := E) r s,
          perAlphaPCConstant (I := I) (M := M) g r s h_atlas α Q) ≤
        ∑ β ∈ chartAtlasPOU_activeFinset I M,
          ∑ Q : TensorCompIdx (E := E) r s,
            perAlphaPCConstant (I := I) (M := M) g r s h_atlas β Q :=
    Finset.single_le_sum
      (f := fun β : M =>
        ∑ Q : TensorCompIdx (E := E) r s,
          perAlphaPCConstant (I := I) (M := M) g r s h_atlas β Q)
      (fun β _ => Finset.sum_nonneg fun Q _ =>
        perAlphaPCConstant_nonneg (I := I) (M := M) g r s h_atlas β Q) hα
  exact h_inner_le.trans h_outer_le

/-! ## Headline: a chart-base-uniform order-2 Sobolev energy bound for the
eigenvector chart component

The headline drops the per-`(α, P₀)` quantification of
`eigenvector_chartComponent_wkpNorm_two_energy_le` into the inside of the
universal quantifier of a single existential, giving a single constant `C ≥ 0`
controlling the order-2 Sobolev norm of the chart component for *every*
`(α, P₀, i)` simultaneously.

On the *inactive* chart base points — those `α : M` with identically vanishing
`chartAtlasPOU α` — the left-hand `wkpNorm` is `0`, so the bound is trivial for
any nonnegative `C`. On the finitely many *active* chart base points the
per-`(α, P₀)` constant is bounded by the total active constant, which serves
as the chart-base-uniform witness. -/

set_option maxHeartbeats 800000 in
/-- **A chart-base-uniform order-2 Sobolev energy bound for the eigenvector
chart component.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and the
uniform-Sobolev hypothesis `h_atlas`, there is a chart-geometric constant
`C ≥ 0` — uniform over *every* chart base point `α : M`, every chart-component
multi-index `P₀ : TensorCompIdx r s`, and every eigenbasis index `i` — such
that, with resolvent eigenvalue `μ := i.fst.val ∈ (0, 1]`, the order-2
Euclidean Sobolev norm of the eigenvector chart component
`eigenvectorChartComponentFun g r s h_atlas i α P₀` on the chart target is
bounded by `ENNReal.ofReal (C · μ⁻¹)` times the abstract `L²` norm of the
eigenbasis vector `tensorResolventEigenbasisVec h_atlas i`. -/
theorem eigenvector_chartComponent_wkpNorm_two_energy_le_uniform_β
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 2 2
            (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal
              (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  refine ⟨totalActivePCConstant (I := I) (M := M) g r s h_atlas,
    totalActivePCConstant_nonneg (I := I) (M := M) g r s h_atlas, ?_⟩
  intro α P₀ i
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · -- Active case: chain the per-`(α, P₀)` bound with the upper bound by the
    -- total active constant.
    have h_per :=
      perAlphaPCConstant_bound (I := I) (M := M) g r s h_atlas α P₀ i
    have h_C_le :
        perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀ ≤
          totalActivePCConstant (I := I) (M := M) g r s h_atlas :=
      perAlphaPCConstant_le_totalActivePCConstant
        (I := I) (M := M) g r s h_atlas hα P₀
    have hμ_pos : 0 < i.fst.val := by
      have h_norm := tensorResolventEigenbasisVec_orthonormal
        (I := I) (M := M) (g := g) (r := r) (s := s) h_atlas
      have h_one : ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
        h_norm.norm_eq_one i
      have h_nonzero :
          tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i ≠ 0 := by
        intro h_zero
        rw [h_zero, norm_zero] at h_one
        exact one_ne_zero h_one.symm
      exact (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M)
        g r s (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
        h_nonzero).1
    have hμinv_nn : 0 ≤ (i.fst.val)⁻¹ := (inv_pos.mpr hμ_pos).le
    have h_per_const_nn :
        0 ≤ perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀ :=
      perAlphaPCConstant_nonneg (I := I) (M := M) g r s h_atlas α P₀
    have h_real_le :
        perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀ *
            (i.fst.val)⁻¹ ≤
          totalActivePCConstant (I := I) (M := M) g r s h_atlas *
            (i.fst.val)⁻¹ :=
      mul_le_mul_of_nonneg_right h_C_le hμinv_nn
    have h_const_le :
        ENNReal.ofReal
            (perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀ *
              (i.fst.val)⁻¹) ≤
          ENNReal.ofReal
            (totalActivePCConstant (I := I) (M := M) g r s h_atlas *
              (i.fst.val)⁻¹) :=
      ENNReal.ofReal_le_ofReal h_real_le
    have h_envelope :
        ENNReal.ofReal
            (perAlphaPCConstant (I := I) (M := M) g r s h_atlas α P₀ *
              (i.fst.val)⁻¹) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ ≤
        ENNReal.ofReal
            (totalActivePCConstant (I := I) (M := M) g r s h_atlas *
              (i.fst.val)⁻¹) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
      mul_le_mul_of_nonneg_right h_const_le (zero_le _)
    exact h_per.trans h_envelope
  · -- Inactive case: the chart component is a.e. zero on the chart target, so
    -- the `wkpNorm` is zero.
    have h_zero :=
      wkpNorm_two_eigenvectorChartComponentFun_eq_zero_of_notMem_activeFinset
        (I := I) (M := M) g r s h_atlas i hα P₀
    rw [h_zero]
    exact zero_le _

/-! ## Chart-locality-free twins

The declarations above carry a chart-selection hypothesis. The following additive
twins prove the same statements without that hypothesis, re-keying the
eigenvector chart component
onto the chart-locality-free `eigenvectorChartComponentFun_unconditional` and the
intrinsic compact-operator eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic
g r s) i`. The proofs transfer verbatim with dependency-name substitution; the
per-`(α, P₀)` Sobolev energy bound routes through the committed upstream twin
`eigenvector_chartComponent_wkpNorm_two_energy_le_unconditional`, whose chart
component `(eigenvectorTensorChartBilinearData_unconditional g r s i α P₀).u_chart`
is definitionally `eigenvectorChartComponentFun_unconditional g r s i α P₀`. The
originals above are kept intact. -/

/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_ae_zero_of_notMem_activeFinset`. -/
private lemma eigenvectorChartComponentFun_ae_zero_of_notMem_activeFinset_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_kernel_empty :
      chartPouKernel (I := I) (M := M) α = (∅ : Set EuclN) :=
    chartPouKernel_eq_empty_of_notMem_activeFinset (I := I) (M := M) hα
  -- The committed a.e.-vanishing on
  -- `MetricExtension.chartTargetEuclid α \ chartPouKernel α`.
  have h_ae := eigenvectorChartComponentFun_ofCompact_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s i α P₀
  -- Bridge the two `chartTargetEuclid` namespaces (they are propositionally
  -- equal on the nose).
  have h_target_eq := chartTargetEuclid_eq (I := I) (M := M) α
  -- Rewrite the restriction set: with the kernel empty, the difference is the
  -- whole chart target. (`eigenvectorChartComponentFun_ofCompact` is, by
  -- definition, `eigenvectorChartComponentFun_unconditional`, hence `h_ae`
  -- discharges the goal up to the empty-kernel set rewrite and the
  -- `chartTargetEuclid` namespace bridge.)
  have h_set_eq :
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid
            (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α =
        chartTargetEuclid (I := I) (M := M) α := by
    rw [h_kernel_empty, Set.diff_empty, ← h_target_eq]
  rw [h_set_eq] at h_ae
  exact h_ae

/-- Chart-locality-free twin of
`wkpNorm_two_eigenvectorChartComponentFun_eq_zero_of_notMem_activeFinset`. -/
private lemma wkpNorm_two_eigenvectorChartComponentFun_eq_zero_of_notMem_activeFinset_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  classical
  have h_chart_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_ae_zero :=
    eigenvectorChartComponentFun_ae_zero_of_notMem_activeFinset_unconditional
      (I := I) (M := M) g r s i hα P₀
  have h_swap :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 2 2
          (fun _ : EuclN => (0 : ℝ))
          (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open
      h_ae_zero
  rw [h_swap]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_chart_open

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `perAlphaPCConstant`. -/
private noncomputable def perAlphaPCConstant_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : ℝ :=
  Classical.choose
    (eigenvector_chartComponent_wkpNorm_two_energy_le_unconditional
      (I := I) (M := M) g r s α P₀)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `perAlphaPCConstant_nonneg`. -/
private lemma perAlphaPCConstant_nonneg_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    0 ≤ perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀ :=
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_two_energy_le_unconditional
      (I := I) (M := M) g r s α P₀)).1

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `perAlphaPCConstant_bound`. -/
private lemma perAlphaPCConstant_bound_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal
          (perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀ *
            (i.fst.val)⁻¹) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ :=
  -- The upstream twin's chart component
  -- `(eigenvectorTensorChartBilinearData_unconditional g r s i α P₀).u_chart`
  -- is definitionally `eigenvectorChartComponentFun_unconditional g r s i α P₀`,
  -- so the `Classical.choose_spec` bound discharges the goal directly.
  (Classical.choose_spec
    (eigenvector_chartComponent_wkpNorm_two_energy_le_unconditional
      (I := I) (M := M) g r s α P₀)).2 i

/-- Chart-locality-free twin of `totalActivePCConstant`. -/
private noncomputable def totalActivePCConstant_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ℝ :=
  ∑ α ∈ chartAtlasPOU_activeFinset I M,
    ∑ P₀ : TensorCompIdx (E := E) r s,
      perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀

/-- Chart-locality-free twin of `totalActivePCConstant_nonneg`. -/
private lemma totalActivePCConstant_nonneg_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActivePCConstant_unconditional (I := I) (M := M) g r s := by
  classical
  unfold totalActivePCConstant_unconditional
  refine Finset.sum_nonneg fun α _ => ?_
  exact Finset.sum_nonneg fun P₀ _ =>
    perAlphaPCConstant_nonneg_unconditional (I := I) (M := M) g r s α P₀

/-- Chart-locality-free twin of
`perAlphaPCConstant_le_totalActivePCConstant`. -/
private lemma perAlphaPCConstant_le_totalActivePCConstant_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∈ chartAtlasPOU_activeFinset I M)
    (P₀ : TensorCompIdx (E := E) r s) :
    perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀ ≤
      totalActivePCConstant_unconditional (I := I) (M := M) g r s := by
  classical
  unfold totalActivePCConstant_unconditional
  -- First peel off the outer α-sum.
  have h_inner_le :
      perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀ ≤
        ∑ Q : TensorCompIdx (E := E) r s,
          perAlphaPCConstant_unconditional (I := I) (M := M) g r s α Q :=
    Finset.single_le_sum
      (f := fun Q : TensorCompIdx (E := E) r s =>
        perAlphaPCConstant_unconditional (I := I) (M := M) g r s α Q)
      (fun Q _ =>
        perAlphaPCConstant_nonneg_unconditional (I := I) (M := M) g r s α Q)
      (Finset.mem_univ P₀)
  have h_outer_le :
      (∑ Q : TensorCompIdx (E := E) r s,
          perAlphaPCConstant_unconditional (I := I) (M := M) g r s α Q) ≤
        ∑ β ∈ chartAtlasPOU_activeFinset I M,
          ∑ Q : TensorCompIdx (E := E) r s,
            perAlphaPCConstant_unconditional (I := I) (M := M) g r s β Q :=
    Finset.single_le_sum
      (f := fun β : M =>
        ∑ Q : TensorCompIdx (E := E) r s,
          perAlphaPCConstant_unconditional (I := I) (M := M) g r s β Q)
      (fun β _ => Finset.sum_nonneg fun Q _ =>
        perAlphaPCConstant_nonneg_unconditional (I := I) (M := M) g r s β Q) hα
  exact h_inner_le.trans h_outer_le

set_option maxHeartbeats 800000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of
`eigenvector_chartComponent_wkpNorm_two_energy_le_uniform_β`.

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, there is a
chart-geometric constant `C ≥ 0` — uniform over *every* chart base point
`α : M`, every chart-component multi-index `P₀ : TensorCompIdx r s`, and every
eigenbasis index `i` — such that, with resolvent eigenvalue
`μ := i.fst.val ∈ (0, 1]`, the order-2 Euclidean Sobolev norm of the
chart-locality-free eigenvector chart component
`eigenvectorChartComponentFun_unconditional g r s i α P₀` on the chart target is
bounded by `ENNReal.ofReal (C · μ⁻¹)` times the abstract `L²` norm of the
intrinsic-compactness eigenbasis vector
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic
g r s) i`. No chart-selection hypothesis appears. -/
theorem eigenvector_chartComponent_wkpNorm_two_energy_le_uniform_β_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 2 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal
              (C * (i.fst.val)⁻¹) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  refine ⟨totalActivePCConstant_unconditional (I := I) (M := M) g r s,
    totalActivePCConstant_nonneg_unconditional (I := I) (M := M) g r s, ?_⟩
  intro α P₀ i
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · -- Active case: chain the per-`(α, P₀)` bound with the upper bound by the
    -- total active constant.
    have h_per :=
      perAlphaPCConstant_bound_unconditional (I := I) (M := M) g r s α P₀ i
    have h_C_le :
        perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀ ≤
          totalActivePCConstant_unconditional (I := I) (M := M) g r s :=
      perAlphaPCConstant_le_totalActivePCConstant_unconditional
        (I := I) (M := M) g r s hα P₀
    have hμ_pos : 0 < i.fst.val := by
      have h_norm := tensorResolventEigenbasisVec_ofCompact_orthonormal
        (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
      have h_one :
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ = 1 :=
        h_norm.norm_eq_one i
      have h_nonzero :
          tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i ≠ 0 := by
        intro h_zero
        rw [h_zero, norm_zero] at h_one
        exact one_ne_zero h_one.symm
      exact (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M)
        g r s
        (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i)
        h_nonzero).1
    have hμinv_nn : 0 ≤ (i.fst.val)⁻¹ := (inv_pos.mpr hμ_pos).le
    have h_per_const_nn :
        0 ≤ perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀ :=
      perAlphaPCConstant_nonneg_unconditional (I := I) (M := M) g r s α P₀
    have h_real_le :
        perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀ *
            (i.fst.val)⁻¹ ≤
          totalActivePCConstant_unconditional (I := I) (M := M) g r s *
            (i.fst.val)⁻¹ :=
      mul_le_mul_of_nonneg_right h_C_le hμinv_nn
    have h_const_le :
        ENNReal.ofReal
            (perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀ *
              (i.fst.val)⁻¹) ≤
          ENNReal.ofReal
            (totalActivePCConstant_unconditional (I := I) (M := M) g r s *
              (i.fst.val)⁻¹) :=
      ENNReal.ofReal_le_ofReal h_real_le
    have h_envelope :
        ENNReal.ofReal
            (perAlphaPCConstant_unconditional (I := I) (M := M) g r s α P₀ *
              (i.fst.val)⁻¹) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ ≤
        ENNReal.ofReal
            (totalActivePCConstant_unconditional (I := I) (M := M) g r s *
              (i.fst.val)⁻¹) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ :=
      mul_le_mul_of_nonneg_right h_const_le (zero_le _)
    exact h_per.trans h_envelope
  · -- Inactive case: the chart component is a.e. zero on the chart target, so
    -- the `wkpNorm` is zero.
    have h_zero :=
      wkpNorm_two_eigenvectorChartComponentFun_eq_zero_of_notMem_activeFinset_unconditional
        (I := I) (M := M) g r s i hα P₀
    rw [h_zero]
    exact zero_le _

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
