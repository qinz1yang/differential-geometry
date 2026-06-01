import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartComponentL2
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.CutoffChartPartialUniformBound

/-!
# The cutoff chart partials of an eigenvector chart component as an `L²`-limit of smooth ones

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, fix an eigenbasis
index `i : TensorEigenIdx g r s` with nonzero resolvent eigenvalue
`μ := i.fst.val`. The companion file `EigenvectorChartPartialL2.lean` realised
the candidate weak chart partials of the eigenvector chart component, weighted
by the chart-atlas partition-of-unity function, as the `n → ∞` `L²`-limit of
the chosen weak chart partials of the smooth approximating sequence
`eigenvectorSmoothApprox g r s i : ℕ → SmoothCcTensorH1 g r s`.

This file produces the corresponding limit for the **cutoff**-weighted chart
component `cutoffComponentEuclid g r s S α P` — the chart push-forward of the
chart-kernel cutoff `chartKernelCutoff α` times the raw chart component. The
construction is the verbatim cutoff-weight analogue of `eigenvectorChartPartialLp`:
the cutoff component is, on the chart target, the chart push-forward of a
globally smooth compactly-supported manifold scalar field, hence `W^{1,2}`
there, so its chosen weak partial lies in `L²`; the cutoff uniform chart-Sobolev
`H¹` bound `exists_const_sum_eLpNorm_chosenWeakPartial'_cutoffComponentEuclid_le_uniform`
makes the resulting `L²` map a continuous linear map, which extends along the
dense embedding of smooth sections into the `H¹` completion.

## The construction

For a fixed chart-coordinate direction `k`, the chosen weak `k`-th chart partial
of the cutoff Euclidean chart component of a smooth section
`S : SmoothCcTensorH1 g r s` is an `L²`-finite function on the chart target —
the cutoff chart component is globally `C^∞` with compact support inside the
chart target, hence `W^{1,2}` there, so its chosen weak partial lies in `L²`
(`chosenWeakPartial'_memLp_of_mem`). Its `L²` class is therefore an element

* `smoothCutoffChartPartialLp g r s S α P₀ k : Lp ℝ 2 (chartL2Measure α)`.

Because `cutoffComponentEuclid` is `ℝ`-linear in `S` and `chosenWeakPartial'` is
almost-everywhere additive and `ℝ`-homogeneous, `smoothCutoffChartPartialLp` is
`ℝ`-linear in `S`. The cutoff uniform chart-partial `L²` bound gives, on slicing
off a single summand, a uniform-in-`S` operator-norm bound, so
`smoothCutoffChartPartialLp` assembles into a continuous `ℝ`-linear map
`SmoothCcTensorH1 g r s →L[ℝ] Lp ℝ 2 (chartL2Measure α)`. Continuously extending
it along the dense embedding `SmoothCcTensorH1 g r s ↪ TensorH1Compl g r s`
yields `eigenvectorCutoffChartPartialCLM`, a continuous linear map on the `H¹`
completion.

## Main definitions

* `eigenvectorCutoffChartPartialCLM g r s α P₀ k` — the continuous linear map on
  the `H¹` completion `TensorH1Compl g r s` sending a class to the `L²` class of
  the chosen weak `k`-th chart partial of its cutoff `(α, P₀)`-chart component.
* `eigenvectorCutoffChartPartialLp g r s i α P₀ k` — the candidate
  weak `k`-th chart partial of the cutoff eigenvector chart component: `μ⁻¹`
  times the value of `eigenvectorCutoffChartPartialCLM` on the eigenvector
  resolvent.

## Main results

* `eigenvectorCutoffChartPartialLp_approx_eq` — the `n`-th
  approximant cutoff chart partial is `μ⁻¹` times the `L²` class of the concrete
  chosen weak `k`-th chart partial of
  `cutoffComponentEuclid g r s (eigenvectorSmoothApprox … n).toCcTensor α P₀.1 P₀.2`.
* `eigenvectorCutoffChartPartialLp_tendsto` — **the headline**:
  those approximant cutoff chart partials converge, in `Lp ℝ 2 (chartL2Measure α)`,
  to `eigenvectorCutoffChartPartialLp g r s i α P₀ k`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The cutoff Euclidean chart component is globally `C^∞` on the Euclidean
model space. -/
private lemma cutoffComponentEuclid_contDiff'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  classical
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  refine DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
    (I := I) (M := M) ?_ ?_
  · exact cutoffComponentScalar_contMDiff
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
  · exact cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx

/-- The cutoff Euclidean chart component has compact support. -/
private lemma cutoffComponentEuclid_hasCompactSupport'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx) := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

/-- The topological support of the cutoff Euclidean chart component is contained
in the Euclidean chart target. -/
private lemma cutoffComponentEuclid_tsupport_subset'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tsupport (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      ⊆ chartTargetEuclid (I := I) (M := M) α := by
  rw [cutoffComponentEuclid_eq_chartPushedRaw]
  exact DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.tsupport_chartPushedRaw_subset_chartTargetEuclid
    (I := I) (M := M)
    (cutoffComponentScalar_tsupport_subset_source
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)

/-- The cutoff Euclidean chart component of a smooth compactly-supported `H¹`
section lies in `W^{1,2}` of the Euclidean chart target. -/
lemma cutoffComponentEuclid_memW1p
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_W1 : MemWkp (d := Module.finrank ℝ E) 1 2
      (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp_of_smooth_compactSupport (d := Module.finrank ℝ E) hΩ_open
      (cutoffComponentEuclid_contDiff' (I := I) (M := M) g r s S α Idx Jdx)
      (cutoffComponentEuclid_hasCompactSupport' (I := I) (M := M)
        g r s S α Idx Jdx)
      (cutoffComponentEuclid_tsupport_subset' (I := I) (M := M)
        g r s S α Idx Jdx)
      hp_one 1
  exact MemWkp.one_iff_memW1p.mp h_W1

/-- The chosen weak `k`-th chart partial of the cutoff Euclidean chart component
is in `MemLp 2` of the Euclidean `L²` reference measure of the chart. -/
lemma chosenWeakPartial'_cutoffComponentEuclid_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (k : Fin (Module.finrank ℝ E)) :
    MemLp
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)) 2
      (chartL2Measure (I := I) (M := M) α) := by
  have h := chosenWeakPartial'_memLp_of_mem
    (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S α Idx Jdx) k
  rwa [chartL2Measure]

/-- The `L²` class of the chosen weak `k`-th chart partial of the cutoff
Euclidean chart component of a smooth compactly-supported `H¹` tensor section. -/
private def smoothCutoffChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chosenWeakPartial'_cutoffComponentEuclid_memLp
    (I := I) (M := M) g r s S α P₀.1 P₀.2 k).toLp _

/-- The function underlying `smoothCutoffChartPartialLp` agrees almost everywhere
with the concrete chosen weak `k`-th chart partial. -/
private lemma smoothCutoffChartPartialLp_coeFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ((smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M) g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) := by
  unfold smoothCutoffChartPartialLp
  exact MemLp.coeFn_toLp _

private lemma smoothCutoffChartPartialLp_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothCutoffChartPartialLp (I := I) (M := M) g r s (S₁ + S₂) α P₀ k =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k +
        smoothCutoffChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      cutoffComponentEuclid (I := I) (M := M) g r s
          (S₁ + S₂).toCcTensor α P₀.1 P₀.2 =
        (fun y => cutoffComponentEuclid (I := I) (M := M)
            g r s S₁.toCcTensor α P₀.1 P₀.2 y +
          cutoffComponentEuclid (I := I) (M := M)
            g r s S₂.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_add,
      cutoffComponentEuclid_add (I := I) (M := M)
        g r s S₁.toCcTensor S₂.toCcTensor α P₀.1 P₀.2]
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (S₁ + S₂).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y =>
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S₁.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y +
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S₂.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartL2Measure, h_fun]
    exact chosenWeakPartial'_add_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S₁ α P₀.1 P₀.2)
      (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S₂ α P₀.1 P₀.2) k
  refine (smoothCutoffChartPartialLp_coeFn
    (I := I) (M := M) g r s (S₁ + S₂) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_add :=
    Lp.coeFn_add (smoothCutoffChartPartialLp (I := I) (M := M) g r s S₁ α P₀ k)
      (smoothCutoffChartPartialLp (I := I) (M := M) g r s S₂ α P₀ k)
  refine (Filter.EventuallyEq.add
    (smoothCutoffChartPartialLp_coeFn (I := I) (M := M) g r s S₁ α P₀ k)
    (smoothCutoffChartPartialLp_coeFn (I := I) (M := M) g r s S₂ α P₀ k)).symm.trans
    h_add.symm

private lemma smoothCutoffChartPartialLp_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    smoothCutoffChartPartialLp (I := I) (M := M) g r s (c • S) α P₀ k =
      c • smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  classical
  apply Lp.ext
  have h_fun :
      cutoffComponentEuclid (I := I) (M := M) g r s
          (c • S).toCcTensor α P₀.1 P₀.2 =
        (fun y => c • cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2 y) := by
    rw [SmoothCcTensorH1.toCcTensor_smul,
      cutoffComponentEuclid_smul (I := I) (M := M)
        g r s c S.toCcTensor α P₀.1 P₀.2]
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_partial_ae :
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M) g r s
            (c • S).toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => c * chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α) y) := by
    rw [chartL2Measure]
    have h_fun' :
        cutoffComponentEuclid (I := I) (M := M) g r s
            (c • S).toCcTensor α P₀.1 P₀.2 =
          (fun y => c * cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2 y) := by
      rw [h_fun]; funext y; rw [smul_eq_mul]
    rw [h_fun']
    exact chosenWeakPartial'_const_smul_ae (d := Module.finrank ℝ E) hp_one hΩ_open
      (cutoffComponentEuclid_memW1p (I := I) (M := M) g r s S α P₀.1 P₀.2) c k
  refine (smoothCutoffChartPartialLp_coeFn
    (I := I) (M := M) g r s (c • S) α P₀ k).trans (h_partial_ae.trans ?_)
  have h_smul :=
    Lp.coeFn_smul c (smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k)
  refine Filter.EventuallyEq.trans ?_ h_smul.symm
  filter_upwards [smoothCutoffChartPartialLp_coeFn
    (I := I) (M := M) g r s S α P₀ k] with y hy
  rw [Pi.smul_apply, hy, smul_eq_mul]

/-- The `ℝ`-linear map sending a smooth compactly-supported `H¹` tensor section
to the `L²` class of the chosen weak `k`-th chart partial of its cutoff
Euclidean chart component at `(α, P₀)`. -/
private def smoothCutoffChartPartialLpLin
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →ₗ[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) where
  toFun S := smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k
  map_add' S₁ S₂ :=
    smoothCutoffChartPartialLp_add (I := I) (M := M) g r s S₁ S₂ α P₀ k
  map_smul' c S :=
    smoothCutoffChartPartialLp_smul (I := I) (M := M) g r s c S α P₀ k

@[simp] private lemma smoothCutoffChartPartialLpLin_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k S =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

/-- The operator-norm bound for `smoothCutoffChartPartialLpLin`: the `L²` norm of
the chosen weak cutoff chart partial is bounded by a uniform constant times
`‖S‖`.

The constant is obtained by slicing a single chart-coordinate summand off the
cutoff uniform summed bound
`exists_const_sum_eLpNorm_chosenWeakPartial'_cutoffComponentEuclid_le_uniform`. -/
private lemma smoothCutoffChartPartialLpLin_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensorH1 g r s,
        ‖smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖
          ≤ C * ‖S‖ := by
  classical
  obtain ⟨C, hC_nn, h_bound⟩ :=
    exists_const_sum_eLpNorm_chosenWeakPartial'_cutoffComponentEuclid_le_uniform
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_sum := h_bound S P₀.1 P₀.2
  have h_single :
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ∑ j : Fin (Module.finrank ℝ E),
        eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) :=
    Finset.single_le_sum
      (f := fun j : Fin (Module.finrank ℝ E) =>
        eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 j
            (cutoffComponentEuclid (I := I) (M := M)
              g r s S.toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)))
      (fun j _ => zero_le _) (Finset.mem_univ k)
  have h_eLp :
      eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartL2Measure (I := I) (M := M) α) ≤
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
    rw [chartL2Measure]
    exact h_single.trans h_sum
  have h_norm_eq :
      ‖smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k S‖ =
        (eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (cutoffComponentEuclid (I := I) (M := M)
            g r s S.toCcTensor α P₀.1 P₀.2)
          (chartTargetEuclid (I := I) (M := M) α)) 2
          (chartL2Measure (I := I) (M := M) α)).toReal := by
    rw [smoothCutoffChartPartialLpLin_apply]
    unfold smoothCutoffChartPartialLp
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [h_norm_eq]
  have h_rhs_lt_top :
      ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top).ne
  have h_toReal_le :
      (eLpNorm (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (cutoffComponentEuclid (I := I) (M := M)
          g r s S.toCcTensor α P₀.1 P₀.2)
        (chartTargetEuclid (I := I) (M := M) α)) 2
        (chartL2Measure (I := I) (M := M) α)).toReal ≤
        (ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)).toReal :=
    ENNReal.toReal_mono h_rhs_lt_top h_eLp
  refine h_toReal_le.trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_nn,
    ENNReal.coe_toReal, coe_nnnorm]

/-- The continuous `ℝ`-linear map from smooth compactly-supported `H¹` tensor
sections to the cutoff chart-partial `L²` space, with operator norm controlled
by the cutoff uniform chart-partial `L²` bound. -/
private def smoothCutoffChartPartialLpCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    SmoothCcTensorH1 g r s →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (smoothCutoffChartPartialLpLin (I := I) (M := M) g r s α P₀ k).mkContinuous
    (smoothCutoffChartPartialLpLin_norm_le (I := I) (M := M) g r s α P₀ k).choose
    (smoothCutoffChartPartialLpLin_norm_le
      (I := I) (M := M) g r s α P₀ k).choose_spec.2

@[simp] private lemma smoothCutoffChartPartialLpCLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    smoothCutoffChartPartialLpCLM (I := I) (M := M) g r s α P₀ k S =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := rfl

/-- The canonical embedding `SmoothCcTensorH1 g r s ↪ TensorH1Compl g r s` is
uniform-inducing. -/
private lemma isUniformInducing_smoothToTensorH1Compl'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsUniformInducing (smoothToTensorH1Compl (I := I) (M := M) g r s) := by
  rw [show (smoothToTensorH1Compl (I := I) (M := M) g r s :
        SmoothCcTensorH1 g r s → TensorH1Compl g r s) =
      ((↑) : SmoothCcTensorH1 g r s →
        UniformSpace.Completion (SmoothCcTensorH1 g r s)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 g r s)

/-- **The canonical cutoff chart-partial continuous linear map on the `H¹`
completion.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart
center `α : M`, a component multi-index `P₀`, and a chart-coordinate direction
`k`, this is the continuous linear map `TensorH1Compl g r s →L[ℝ] Lp ℝ 2
(chartL2Measure α)` sending an element of the `H¹` completion to the `L²` class
of the chosen weak `k`-th chart partial of its cutoff `(α, P₀)`-chart-frame
scalar component.

It is defined by continuously extending, along the dense embedding of smooth
compactly-supported `H¹` sections into the `H¹` completion, the bounded
`ℝ`-linear map `smoothCutoffChartPartialLpCLM` that sends a smooth section to the
`L²` class of the chosen weak `k`-th chart partial of its cutoff chart
component. On a smooth section it recovers that concrete chosen weak cutoff chart
partial (`eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl`). -/
def eigenvectorCutoffChartPartialCLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    TensorH1Compl g r s →L[ℝ] Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  ContinuousLinearMap.extend
    (smoothCutoffChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (smoothToTensorH1Compl (I := I) (M := M) g r s)

/-- **Compatibility on smooth sections.** For a smooth compactly-supported `H¹`
tensor section `S`, the canonical cutoff chart-partial continuous linear map,
evaluated at the completion embedding of `S`, equals the `L²` class of the
chosen weak `k`-th chart partial of the concrete cutoff Euclidean chart
component of `S`. -/
theorem eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
        (smoothToTensorH1Compl (I := I) (M := M) g r s S) =
      smoothCutoffChartPartialLp (I := I) (M := M) g r s S α P₀ k := by
  unfold eigenvectorCutoffChartPartialCLM
  rw [ContinuousLinearMap.extend_eq
    (smoothCutoffChartPartialLpCLM (I := I) (M := M) g r s α P₀ k)
    (denseRange_smoothToTensorH1Compl (I := I) (M := M) g r s)
    (isUniformInducing_smoothToTensorH1Compl' (I := I) (M := M) g r s) S]
  rfl

/-- **The candidate weak `k`-th cutoff chart partial of an eigenvector chart
component (chart-locality-free).** Chart-locality-free twin of
`eigenvectorCutoffChartPartialLp`. -/
def eigenvectorCutoffChartPartialLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (i.fst.val)⁻¹ •
    eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
      (eigenvectorResolvent (I := I) (M := M) g r s i)

/-- **The concrete characterisation of the approximant cutoff chart partial
(chart-locality-free).** Chart-locality-free twin of
`eigenvectorCutoffChartPartialLp_approx_eq`. -/
theorem eigenvectorCutoffChartPartialLp_approx_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    (i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)) =
      (i.fst.val)⁻¹ •
        (chosenWeakPartial'_cutoffComponentEuclid_memLp (I := I) (M := M)
          g r s
          (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)
          α P₀.1 P₀.2 k).toLp
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (cutoffComponentEuclid (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α P₀.1 P₀.2)
            (chartTargetEuclid (I := I) (M := M) α)) := by
  rw [eigenvectorCutoffChartPartialCLM_smoothToTensorH1Compl
    (I := I) (M := M) g r s
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n) α P₀ k]
  rfl

/-- **The cutoff chart partials of an eigenvector chart component as an
`L²`-limit of smooth cutoff chart partials (chart-locality-free).**
Chart-locality-free twin of `eigenvectorCutoffChartPartialLp_tendsto`. -/
theorem eigenvectorCutoffChartPartialLp_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        eigenvectorCutoffChartPartialCLM (I := I) (M := M) g r s α P₀ k
          (smoothToTensorH1Compl (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)))
      atTop
      (𝓝 (eigenvectorCutoffChartPartialLp (I := I) (M := M)
        g r s i α P₀ k)) := by
  have h_clm :=
    ((eigenvectorCutoffChartPartialCLM
        (I := I) (M := M) g r s α P₀ k).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  have h_smul := h_clm.const_smul (i.fst.val)⁻¹
  simp only [Function.comp_def] at h_smul
  exact h_smul

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
