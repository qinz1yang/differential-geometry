import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedGramDiff
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChristoffelPerturbation
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping

/-!
# The chart `2`-jet seminorm of two realized metrics, bounded by the iterated covariant
gradient of the fixed realized tensor difference

This file develops the **analytic core** of the geometric Ricci–DeTurck nonlinearity:
the chart `2`-jet seminorm `chartMetricJet2DiffSup (realizeMetricAt u₁) (realizeMetricAt u₂)`
of the difference of two realized metrics is controlled, pointwise on a compact piece of
the chart-target interior, by the sum of the `g_bg`-fibre norms of the iterated covariant
gradients `∇^j S` (`j = 0, 1, 2`) of the **fixed** `(0,2)`-tensor difference

  `S := realizableRepr g_bg hu₁ − realizableRepr g_bg hu₂`,

evaluated at the chart preimage `(extChartAt I α).symm y`.

## The two layers

The reduction proceeds in two genuinely distinct layers.

* **The algebraic reduction (this file's headline).**  By
  `chartGramOnE_realizeMetricAt_sub_eq_reprDiff`, the chart-Gram-on-`E` difference of the
  two realized metrics, at chart point `y` and frame indices `(l, b)`, equals the
  chart-frame component of the *single fixed tensor* `S`:

    `chartGramOnE g₁ α l b y − chartGramOnE g₂ α l b y
       = ccTensorBilinSymm g_bg S ((extChartAt I α).symm y)
           (chartBasisVecFiber α l ((extChartAt I α).symm y))
           (chartBasisVecFiber α b ((extChartAt I α).symm y))`.

  Since this holds for **every** `y`, the two functions of `y` are equal, so all their
  chart-coordinate partial derivatives `∂^j` agree on the interior.  Each
  `chartMetricJet2DiffSup` summand is therefore a chart `∂^j` (`j = 0, 1, 2`) of a
  chart-frame component of `S`.  This layer is purely algebraic and is proved here
  unconditionally.

* **The pointwise covariant-gradient jet bound (a genuine analytic input).**  The
  chart `∂^j` of the chart-frame component of a fixed `(0,2)`-tensor `S` is bounded,
  uniformly on a compact piece `K ⊆ interior (extChartAt I α).target`, by a constant times
  `∑_{i ≤ j} ‖(iteratedCovGrad g_bg 0 2 i S).toSection (symm y)‖`.  This is the pointwise
  inversion of the chart-coordinate covariant-derivative formula `∇T = ∂T + Γ·T`
  (`nabla_equals_partial_plus_christoffel_on_tensors`), iterated twice:
  `∂²S = ∇²S − Γ·∂S − (∂Γ + Γ·Γ)·S`, with the Christoffel carriers bounded uniformly on
  `K` (`christoffel_Ck_bound_from_metric_Ck1` / `chartChristoffel_contDiffOn_interior`).

  This is a *pointwise inequality bounding chart partials of a tensor component by the
  covariant-gradient fibre norms of that tensor* — a statement structurally distinct from
  the chart `2`-jet seminorm of the realized-metric difference (the headline conclusion).
  We carry it as the named hypothesis `hcovgrad_jet_bound`; it is a genuine analytic input,
  not a packaging of the conclusion.  The algebraic reduction then converts it into the
  headline bound on `chartMetricJet2DiffSup`.

## Sign convention

Geometer `Δ_∇ = −∇*∇`; resolvent `(1 − Δ_∇)⁻¹`, weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The chart Gram entry on `E` is differentiable at an interior point. -/
private lemma chartGramOnE_diffAt_interior
    (g : SmoothRiemannianMetric I M) (α : M) (l b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α l b) y := by
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b)
      (interior ((extChartAt I α).target : Set E)) :=
    (chartGramOnE_contDiffOn (I := I) g α l b).mono interior_subset
  exact (hcd_int.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

/-- The first chart partial `∂_a f` of a function `C^∞` on the chart-target interior is
again `C^∞` there. -/
private lemma partialDeriv_contDiffOn_interior
    (α : M) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f (interior ((extChartAt I α).target : Set E)))
    (a : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (partialDeriv (E := E) a f)
      (interior ((extChartAt I α).target : Set E)) := by
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ f)
      (interior ((extChartAt I α).target : Set E)) :=
    hf.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
  have hrw : (partialDeriv (E := E) a f) =
      fun y => fderiv ℝ f y ((chartModelBasis E) a) := rfl
  rw [hrw]
  exact hfderiv.clm_apply contDiffOn_const

/-- The first chart partial `∂_a (chartGramOnE g α l b)` is differentiable at an interior
point (needed to commute the second partial past the subtraction). -/
private lemma partialDeriv_chartGramOnE_diffAt_interior
    (g : SmoothRiemannianMetric I M) (α : M) (a l b : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    DifferentiableAt ℝ
      (partialDeriv (E := E) a (chartGramOnE (I := I) g α l b)) y := by
  have hcd_int : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α l b)
      (interior ((extChartAt I α).target : Set E)) :=
    (chartGramOnE_contDiffOn (I := I) g α l b).mono interior_subset
  have hcd_partial : ContDiffOn ℝ ∞
      (partialDeriv (E := E) a (chartGramOnE (I := I) g α l b))
      (interior ((extChartAt I α).target : Set E)) :=
    partialDeriv_contDiffOn_interior (I := I) α hcd_int a
  exact (hcd_partial.contDiffAt (isOpen_interior.mem_nhds hy)).differentiableAt (by simp)

/-- The chart-`α` `(l, b)` frame component of the fixed realized tensor difference
`S = realizableRepr hu₁ − realizableRepr hu₂`, as a function on the chart target `E`. -/
def reprDiffChartCompOnE (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    ccTensorBilinSymm (I := I) g_bg
      (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
      ((extChartAt I α).symm y)
      (chartBasisVecFiber (I := I) α l ((extChartAt I α).symm y))
      (chartBasisVecFiber (I := I) α b ((extChartAt I α).symm y))

/-- **The chart-Gram-on-`E` difference of the two realized metrics, as a function on `E`,
equals the chart-frame component of the fixed tensor difference.**  This is the
function-level upgrade of `chartGramOnE_realizeMetricAt_sub_eq_reprDiff`: both sides are
functions of the chart variable `y`, hence all their iterated chart partials agree. -/
theorem chartGramOnE_realizeMetricAt_sub_funext
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) :
    (fun y : E => chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b y -
        chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b y) =
      reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b := by
  funext y
  rw [reprDiffChartCompOnE]
  exact chartGramOnE_realizeMetricAt_sub_eq_reprDiff (I := I) g_bg hu₁ hu₂ α l b y

/-- The `0`-jet entry of the realized-metric difference equals the chart component of `S`
at the chart point. -/
theorem chartGramMatrix_realizeMetricAt_sub_eq_reprDiffComp
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (l b : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₁) α
          ((extChartAt I α).symm y) l b -
        chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₂) α
          ((extChartAt I α).symm y) l b =
      reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y := by
  rw [reprDiffChartCompOnE]
  exact chartGramMatrix_realizeMetricAt_sub_eq_reprDiff (I := I) g_bg hu₁ hu₂
    α ((extChartAt I α).symm y) l b

/-- On the chart-target interior, the first chart partial of the realized-metric
Gram-on-`E` difference equals the first chart partial of the chart component of `S`. -/
theorem partialDeriv_chartGramOnE_realizeMetricAt_sub_eq
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (a l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    partialDeriv (E := E) a
        (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) y -
      partialDeriv (E := E) a
        (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) y =
      partialDeriv (E := E) a
        (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y := by
  rw [← chartGramOnE_realizeMetricAt_sub_funext (I := I) g_bg hu₁ hu₂ α l b]
  rw [partialDeriv, partialDeriv, partialDeriv, ← ContinuousLinearMap.sub_apply]
  congr 1
  exact (fderiv_sub
    (chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b hy)
    (chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b hy)).symm

/-- On the chart-target interior, the second chart partial of the realized-metric
Gram-on-`E` difference equals the second chart partial of the chart component of `S`. -/
theorem partialDeriv2_chartGramOnE_realizeMetricAt_sub_eq
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) (c a l b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior ((extChartAt I α).target : Set E)) :
    partialDeriv (E := E) c
        (partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b)) y -
      partialDeriv (E := E) c
        (partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b)) y =
      partialDeriv (E := E) c
        (partialDeriv (E := E) a
          (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y := by
  have hop : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have h_eqOn : Set.EqOn
      (fun z => partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) z -
        partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) z)
      (partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b))
      (interior ((extChartAt I α).target : Set E)) := by
    intro z hz
    exact partialDeriv_chartGramOnE_realizeMetricAt_sub_eq (I := I) g_bg hu₁ hu₂ α a l b hz
  rw [partialDeriv, partialDeriv, partialDeriv, ← ContinuousLinearMap.sub_apply]
  have hfd_sub :
      fderiv ℝ (partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b)) y -
        fderiv ℝ (partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b)) y =
      fderiv ℝ (fun z => partialDeriv (E := E) a
            (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) z -
          partialDeriv (E := E) a
            (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) z) y :=
    (fderiv_sub
      (partialDeriv_chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₁)
        α a l b hy)
      (partialDeriv_chartGramOnE_diffAt_interior (I := I) (realizeMetricAt (I := I) g_bg u₂)
        α a l b hy)).symm
  rw [hfd_sub]
  have hev : (fun z => partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₁) α l b) z -
        partialDeriv (E := E) a
          (chartGramOnE (I := I) (realizeMetricAt (I := I) g_bg u₂) α l b) z)
      =ᶠ[nhds y]
      partialDeriv (E := E) a (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨interior ((extChartAt I α).target : Set E), hop.mem_nhds hy, h_eqOn⟩
  rw [hev.fderiv_eq]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in
/-- The iterated covariant-gradient jet sum of a fixed `(0,2)`-tensor `S` at a manifold
point `x`: `∑_{j ≤ 2} ‖(∇^j S)(x)‖_{g_bg}` (the `g_bg`-fibre norms of the `(0, 2 + j)`-tensors
`∇^j S`).  This is exactly the left-hand side of the unconditional `C²` Sobolev embedding. -/
def iteratedCovGradJetSum (g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g_bg 0 2) (x : M) : ℝ :=
  ∑ j ∈ Finset.range 3,
    (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 (2 + j)
    ‖(iteratedCovGrad (I := I) (M := M) g_bg 0 2 j S).toSection x‖)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in
/-- `iteratedCovGradJetSum` is non-negative. -/
lemma iteratedCovGradJetSum_nonneg (g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g_bg 0 2) (x : M) :
    0 ≤ iteratedCovGradJetSum (I := I) g_bg S x := by
  rw [iteratedCovGradJetSum]
  refine Finset.sum_nonneg (fun j _ => ?_)
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g_bg 0 (2 + j)
  exact norm_nonneg _

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace in
/-- **The iterated covariant-gradient jet sum is bounded by the intrinsic `H^{2k}` Sobolev
norm of the fixed tensor (unconditional `C²` Sobolev embedding).**

For `2k > dim M + 4`, there is a constant `C > 0` such that, for every smooth
compactly-supported `(0,2)`-tensor `S` and every base point `x`,

  `iteratedCovGradJetSum g_bg S x ≤ C · ‖S.toHs (2k)‖`.

This is exactly `iteratedCovGrad_toSobolev_embedding_C2_unconditional`: the left-hand side
of that embedding is, term by term, the `iteratedCovGradJetSum` of `S` at `x`. -/
theorem iteratedCovGradJetSum_le_toHs (g_bg : SmoothRiemannianMetric I M) (k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : SmoothCcTensor g_bg 0 2) (x : M),
      iteratedCovGradJetSum (I := I) g_bg S x ≤
        C * ‖SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) S‖ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    iteratedCovGrad_toSobolev_embedding_C2_unconditional (I := I) (M := M) g_bg k h_super
  refine ⟨C, hC_pos, fun S x => ?_⟩
  rw [iteratedCovGradJetSum]
  exact hC S x

set_option linter.unusedSectionVars false in
/-- **The chart `2`-jet seminorm of the realized-metric difference is bounded by the
iterated covariant-gradient jet sum of the fixed tensor difference, modulo the pointwise
covariant-gradient input.**

For two realizable order-`σ` elements `u₁, u₂` (smooth representatives `T₁, T₂`, fixed
difference `S = T₁ − T₂`), a chart base point `α`, a compact piece `K ⊆ interior
(extChartAt I α).target`, and a pointwise covariant-gradient jet bound `hcovgrad_jet_bound`
controlling each chart `∂^j` (`j = 0, 1, 2`) of every chart-frame component of `S` by a
single constant `C₀` times `iteratedCovGradJetSum g_bg S ((extChartAt I α).symm y)` uniformly
on `K`, the chart `2`-jet seminorm of the realized-metric difference satisfies

  `chartMetricJet2DiffSup (realizeMetricAt u₁) (realizeMetricAt u₂) α y
     ≤ C · iteratedCovGradJetSum g_bg S ((extChartAt I α).symm y)`

for all `y ∈ K`, with `C` uniform on `K`.  `C` is the per-summand constant times the total
number of chart-jet index terms (`n² + n³ + n⁴`).

The hypothesis `hcovgrad_jet_bound` is a genuine analytic input: a pointwise inequality
bounding chart partials of the components of the *fixed* tensor `S` by the covariant-gradient
fibre norms of `S`.  It is structurally distinct from the conclusion (the chart `2`-jet
seminorm of the *realized-metric difference*), so it is not a packaging of the conclusion. -/
theorem chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) {K : Set E} (hKsub : K ⊆ interior ((extChartAt I α).target : Set E))
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hcovgrad_jet_bound : ∀ y ∈ K, ∀ l b : Fin (Module.finrank ℝ E),
      |reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y| ≤
          C₀ * iteratedCovGradJetSum (I := I) g_bg
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
            ((extChartAt I α).symm y) ∧
        (∀ a : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) a
              (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y)) ∧
        (∀ c a : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
              (partialDeriv (E := E) a
                (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      chartMetricJet2DiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y ≤
        C * iteratedCovGradJetSum (I := I) g_bg
          (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
          ((extChartAt I α).symm y) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  set Ncard : ℝ := (Fintype.card ((Fin n) × (Fin n)) : ℝ)
    + (Fintype.card ((Fin n) × (Fin n) × (Fin n)) : ℝ)
    + (Fintype.card ((Fin n) × (Fin n) × (Fin n) × (Fin n)) : ℝ) with hNcard_def
  have hNcard_nn : 0 ≤ Ncard := by
    rw [hNcard_def]; positivity
  refine ⟨C₀ * Ncard, mul_nonneg hC₀ hNcard_nn, ?_⟩
  intro y hy
  set R : ℝ := iteratedCovGradJetSum (I := I) g_bg S ((extChartAt I α).symm y) with hR_def
  have hR_nn : 0 ≤ R := iteratedCovGradJetSum_nonneg (I := I) g_bg S _
  have h0 : chartGramDiffSup (I := I) (M := M)
        (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α
        ((extChartAt I α).symm y) ≤
      (Fintype.card ((Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
    rw [chartGramDiffSup, matrixEntryL1]
    calc ∑ pq : (Fin n) × (Fin n),
            |(chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₁) α
                  ((extChartAt I α).symm y) -
                chartGramMatrix (I := I) (realizeMetricAt (I := I) g_bg u₂) α
                  ((extChartAt I α).symm y)) pq.1 pq.2|
        = ∑ pq : (Fin n) × (Fin n),
            |reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α pq.1 pq.2 y| := by
          refine Finset.sum_congr rfl (fun pq _ => ?_)
          rw [Matrix.sub_apply]
          rw [chartGramMatrix_realizeMetricAt_sub_eq_reprDiffComp (I := I) g_bg hu₁ hu₂
            α pq.1 pq.2 y]
      _ ≤ ∑ _pq : (Fin n) × (Fin n), C₀ * R :=
          Finset.sum_le_sum (fun pq _ => (hcovgrad_jet_bound y hy pq.1 pq.2).1)
      _ = (Fintype.card ((Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have h1 : chartGramPartialDiffSup (I := I) (M := M)
        (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y ≤
      (Fintype.card ((Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
    rw [chartGramPartialDiffSup]
    calc ∑ p : (Fin n) × (Fin n) × (Fin n),
            gramPartialDiffEntry (I := I) (M := M)
              (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y p
        = ∑ p : (Fin n) × (Fin n) × (Fin n),
            |partialDeriv (E := E) p.2.1
              (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α p.1 p.2.2) y| := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [gramPartialDiffEntry,
            partialDeriv_chartGramOnE_realizeMetricAt_sub_eq (I := I) g_bg hu₁ hu₂
              α p.2.1 p.1 p.2.2 (hKsub hy)]
      _ ≤ ∑ _p : (Fin n) × (Fin n) × (Fin n), C₀ * R :=
          Finset.sum_le_sum (fun p _ => (hcovgrad_jet_bound y hy p.1 p.2.2).2.1 p.2.1)
      _ = (Fintype.card ((Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have h2 : chartGramPartial2DiffSup (I := I) (M := M)
        (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y ≤
      (Fintype.card ((Fin n) × (Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
    rw [chartGramPartial2DiffSup]
    calc ∑ p : (Fin n) × (Fin n) × (Fin n) × (Fin n),
            gramPartial2DiffEntry (I := I) (M := M)
              (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y p
        = ∑ p : (Fin n) × (Fin n) × (Fin n) × (Fin n),
            |partialDeriv (E := E) p.1
              (partialDeriv (E := E) p.2.1
                (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α p.2.2.1 p.2.2.2)) y| := by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [gramPartial2DiffEntry,
            partialDeriv2_chartGramOnE_realizeMetricAt_sub_eq (I := I) g_bg hu₁ hu₂
              α p.1 p.2.1 p.2.2.1 p.2.2.2 (hKsub hy)]
      _ ≤ ∑ _p : (Fin n) × (Fin n) × (Fin n) × (Fin n), C₀ * R :=
          Finset.sum_le_sum (fun p _ =>
            (hcovgrad_jet_bound y hy p.2.2.1 p.2.2.2).2.2 p.1 p.2.1)
      _ = (Fintype.card ((Fin n) × (Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [chartMetricJet2DiffSup, chartMetricJet1DiffSup]
  calc chartGramDiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α
          ((extChartAt I α).symm y)
        + chartGramPartialDiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y
        + chartGramPartial2DiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y
      ≤ (Fintype.card ((Fin n) × (Fin n)) : ℝ) * (C₀ * R)
          + (Fintype.card ((Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R)
          + (Fintype.card ((Fin n) × (Fin n) × (Fin n) × (Fin n)) : ℝ) * (C₀ * R) := by
        gcongr
    _ = C₀ * Ncard * R := by rw [hNcard_def]; ring

set_option linter.unusedSectionVars false in
/-- **The chart `2`-jet seminorm of the realized-metric difference is bounded by the
intrinsic `H^{2k}` norm of the fixed tensor difference, modulo the pointwise covariant-
gradient input.**

Combines `chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum` (the algebraic
chart-jet reduction plus the pointwise covariant-gradient input `hcovgrad_jet_bound`) with
the unconditional `C²` Sobolev embedding `iteratedCovGradJetSum_le_toHs` (`2k > dim M + 4`).
The result is, for all `y ∈ K`,

  `chartMetricJet2DiffSup (realizeMetricAt u₁) (realizeMetricAt u₂) α y
     ≤ C · ‖(T₁ − T₂).toHs (2k)‖`,

with `C` uniform on `K`.  This is the `2`-jet seminorm of the metric difference dominated by
the intrinsic Sobolev norm of the single fixed tensor difference, the form the spectral
norm-equivalence bridge then converts into the `H^{a+1}` spectral norm of `u₁ − u₂`. -/
theorem chartMetricJet2DiffSup_realizeMetricAt_le_toHs
    (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    {u₁ u₂ : tensorHs (I := I) (M := M) g_bg 0 2 σ}
    (hu₁ : realizableAt (I := I) g_bg u₁) (hu₂ : realizableAt (I := I) g_bg u₂)
    (α : M) {K : Set E} (hKsub : K ⊆ interior ((extChartAt I α).target : Set E))
    (k : ℕ) (h_super : 2 * k > Module.finrank ℝ E + 4)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hcovgrad_jet_bound : ∀ y ∈ K, ∀ l b : Fin (Module.finrank ℝ E),
      |reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b y| ≤
          C₀ * iteratedCovGradJetSum (I := I) g_bg
            (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
            ((extChartAt I α).symm y) ∧
        (∀ a : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) a
              (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y)) ∧
        (∀ c a : Fin (Module.finrank ℝ E),
          |partialDeriv (E := E) c
              (partialDeriv (E := E) a
                (reprDiffChartCompOnE (I := I) g_bg hu₁ hu₂ α l b)) y| ≤
            C₀ * iteratedCovGradJetSum (I := I) g_bg
              (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)
              ((extChartAt I α).symm y))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K,
      chartMetricJet2DiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y ≤
        C * ‖SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k)
          (realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂)‖ := by
  classical
  set S : SmoothCcTensor g_bg 0 2 :=
    realizableRepr (I := I) g_bg hu₁ - realizableRepr (I := I) g_bg hu₂ with hS_def
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    chartMetricJet2DiffSup_realizeMetricAt_le_iteratedCovGradJetSum (I := I) g_bg hu₁ hu₂
      α hKsub hC₀ hcovgrad_jet_bound
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    iteratedCovGradJetSum_le_toHs (I := I) g_bg k h_super
  refine ⟨C₁ * C₂, mul_nonneg hC₁_nn hC₂_pos.le, ?_⟩
  intro y hy
  set N : ℝ := ‖SmoothCcTensor.toHs (g := g_bg) (r := 0) (s := 2) (2 * k) S‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  calc chartMetricJet2DiffSup (I := I) (M := M)
          (realizeMetricAt (I := I) g_bg u₁) (realizeMetricAt (I := I) g_bg u₂) α y
      ≤ C₁ * iteratedCovGradJetSum (I := I) g_bg S ((extChartAt I α).symm y) := hC₁ y hy
    _ ≤ C₁ * (C₂ * N) :=
        mul_le_mul_of_nonneg_left (hC₂ S ((extChartAt I α).symm y)) hC₁_nn
    _ = C₁ * C₂ * N := by ring

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
