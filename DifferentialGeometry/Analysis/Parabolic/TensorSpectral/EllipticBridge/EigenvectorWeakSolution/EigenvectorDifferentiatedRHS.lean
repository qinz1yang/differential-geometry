import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorLeibnizCommutator

/-!
# The level-`m` differentiated right-hand side of the eigenvector chart identity

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the chart
`P₀`-component of the resolvent eigenvector of the connection Laplacian satisfies
the divergence-form variational identity `eigenvectorChartVariationalIdentity`

```
∫ ∑ weightedInvGramOnEuclid · eigenvectorChartWeakPartial · ∂_jψ
  + ∫ densityOnEuclid · u_chart · ψ
  = ∫ densityOnEuclid · eigenvectorChartRHS · ψ
```

with right-hand side the seven-term object `eigenvectorChartRHS`. The
arbitrary-order interior-regularity bootstrap iterates the elliptic
Leibniz-commutator step `tensorChartComponent_diff_variational_identity`: each
application differentiates the variational identity once, producing a *new*
divergence-form identity with the **same** principal symbol
`weightedInvGramOnEuclid` and a differentiated right-hand side. After `m` such
steps the right-hand side is the level-`m` differentiated source built here.

## The level-`m` differentiated right-hand side

`eigenvectorChartRHSDiff g r s i α P₀ l` (with `l : Fin m → Fin n` the
`m`-direction multi-index) is the level-`m` differentiated right-hand side of the
eigenvector chart variational identity. It is defined by recursion on `m`:

* level `0` is the seven-term `eigenvectorChartRHS`;
* level `m + 1` is the indicator, of the compact partition-of-unity kernel
  `chartPouKernel α`, of the chart-density-divided level-`m` *differentiated
  numerator* `eigenvectorChartRHSDiffNumerator`.

The level-`m` differentiated numerator is the five-layer Leibniz combination
produced by one more integration by parts in the new direction
`lₙ := l (Fin.last m)` (mirroring the scalar campaign's `diffVariationalSource`):

* `A` — the `∂_j`-partial of the Leibniz cross-coefficient
  `weightedInvGramDerivOnEuclid g α i j lₙ` against the level-`m` mixed weak
  partial of the chart component;
* `B` — `weightedInvGramDerivOnEuclid g α i j lₙ` against the once-more
  `∂_j`-differentiated level-`m` mixed weak partial;
* `C` — the zeroth-order Leibniz term `densityDerivOnEuclid g α lₙ · (m-fold
  mixed weak partial)`, with a sign;
* `D` — the differentiated genuine source `densityDerivOnEuclid g α lₙ ·
  (level-m differentiated right-hand side)`;
* `E` — `densityOnEuclid g α · (∂_{lₙ}-weak-partial of the level-m differentiated
  right-hand side)`.

The `m`-fold mixed weak partials of the eigenvector chart component are taken via
the canonical chosen weak partial `chosenWeakPartial'`, packaged here as the
recursive `eigenvectorChartIteratedPartial`.

## Weighted `L²` regularity

`eigenvectorChartRHSDiff_memLp_weighted` is the headline: the
level-`m` differentiated right-hand side is `MemLp 2` with respect to the
chart-pulled weighted measure restricted to `chartTargetEuclid α`.

The membership is established **unconditionally** — with no regularity hypothesis
on the eigenvector, keyed on the intrinsic compactness witness used to name the
eigenvector. The mechanism is that every constituent of the
differentiated numerator is unconditionally `MemLp 2` of the plain Lebesgue
volume restricted to the chart target:

* the eigenvector chart component is the coercion of an `Lp` element of the
  chart `L²` reference measure (`= volume.restrict (chartTargetEuclid α)`), hence
  is `MemLp 2` of that measure;
* the canonical chosen weak partial `chosenWeakPartial' 2 k w Ω` is a **total**
  function — when its argument is not in `W^{1,2}(Ω)` it is the zero function —
  and is therefore `MemLp 2 (volume.restrict Ω)` for *every* `w`, with no
  `W^{1,2}` hypothesis: either it is a genuine weak partial of a `W^{1,2}`
  element (`chosenWeakPartial'_memLp_of_mem`) or it is `0`
  (`chosenWeakPartial'_of_not_mem`);
* the level-`m` differentiated right-hand side is, by the inductive hypothesis,
  weighted-`MemLp 2`, hence `MemLp 2 (volume.restrict K)` on every compact
  `K ⊆ chartTargetEuclid α`.

Each of the five layers is one such object multiplied by a `C^∞`-on-the-chart-
target coefficient bounded on the compact kernel; the indicator construction
then upgrades the plain-volume membership to the chart-pulled weighted measure.

This is the route reported for the limit-object weak-partial regularity: the
`W^{1,2}`-regularity question for the seven `eigenvectorChartRHS` limit objects
never arises, because the differentiated right-hand side differentiates the
**assembled** level-`m` right-hand side as a single unit, and the totality of
`chosenWeakPartial'` makes that one weak partial unconditionally `MemLp 2`.

## Main definitions

* `eigenvectorChartIteratedPartial` — the recursive `m`-fold mixed
  weak partial, via `chosenWeakPartial'`, of the eigenvector chart component.
* `eigenvectorChartRHSDiffNumerator` — the five-layer
  differentiated numerator.
* `eigenvectorChartRHSDiff` — the level-`m` differentiated
  right-hand side.

## Main theorems

* `eigenvectorChartRHSDiff_memLp_weighted` — the level-`m`
  differentiated right-hand side is `MemLp 2` with respect to the chart-pulled
  weighted measure restricted to `chartTargetEuclid α`.

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
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
/-- **Unconditional `L²` membership of the canonical chosen weak partial.** For
*any* function `w` and *any* direction `k`, the canonical chosen weak partial
`chosenWeakPartial' 2 k w Ω` is `MemLp 2 (volume.restrict Ω)`. No `W^{1,2}`
hypothesis on `w` is needed: by a case split on `DeGiorgi.MemW1p 2 w Ω`, the
chosen weak partial is either the genuine `L²` weak partial of a `W^{1,2}`
element or the zero function. -/
private lemma chosenWeakPartial'_memLp_volume_unconditional
    {Ω : Set EuclN} (k : Fin (Module.finrank ℝ E)) (w : EuclN → ℝ) :
    MemLp (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k w Ω) 2
      ((volume : Measure EuclN).restrict Ω) := by
  classical
  by_cases hw : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 w Ω
  · exact chosenWeakPartial'_memLp_of_mem hw k
  · rw [chosenWeakPartial'_of_not_mem hw k]
    exact MemLp.zero

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- The reciprocal `1 / densityOnEuclid g α` of the chart density is `C^∞` on the
open Euclidean chart target: the chart density is `C^∞`
(`densityOnEuclid_contDiffOn`) and strictly positive (`densityOnEuclid_pos`)
there. -/
private lemma one_div_densityOnEuclid_contDiffOn'
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (fun y => 1 / densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div (densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy => (densityOnEuclid_pos (I := I) g α hy).ne')

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- Multiplication of a `MemLp 2 (volume.restrict K)` factor (on a compact
`K ⊆ chartTargetEuclid α`) by a `C^∞`-on-the-chart-target coefficient stays in
`MemLp 2 (volume.restrict K)`: the coefficient is continuous on the chart target,
hence bounded on the compact `K`, and bounded-measurable × `L²` is `L²`.

This is a reusable building block, consumed by the iterated divergence-form
scaffold for the chart-density-divided differentiated numerator. -/
lemma memLp_volume_compact_contDiffOn_mul
    (α : M)
    {c : EuclN → ℝ}
    (hc : ContDiffOn ℝ ∞ c (chartTargetEuclid (I := I) (M := M) α))
    {K : Set EuclN} (hK_compact : IsCompact K) (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {w : EuclN → ℝ}
    (hw : MemLp w 2 ((volume : Measure EuclN).restrict K)) :
    MemLp (fun y => c y * w y) 2 ((volume : Measure EuclN).restrict K) := by
  classical
  have hc_contOn_K : ContinuousOn c K := hc.continuousOn.mono hK_in
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖c y‖ ≤ C := by
    by_cases hK_empty : K = ∅
    · exact ⟨0, le_refl _, fun y hy => absurd (hK_empty ▸ hy) (Set.notMem_empty y)⟩
    · obtain ⟨C₀, hC₀⟩ := hK_compact.bddAbove_image hc_contOn_K.norm
      exact ⟨max C₀ 0, le_max_right _ _,
        fun y hy => (hC₀ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_nn, hC_bd⟩ := hbdd
  have hc_meas : AEStronglyMeasurable c
      ((volume : Measure EuclN).restrict K) :=
    hc_contOn_K.aestronglyMeasurable hK_meas
  have hc_ae_bd : ∀ᵐ y ∂((volume : Measure EuclN).restrict K), ‖c y‖ ≤ C :=
    (ae_restrict_iff' hK_meas).mpr (Filter.Eventually.of_forall hC_bd)
  refine ⟨hc_meas.mul hw.1, ?_⟩
  have hpt : ∀ᵐ y ∂((volume : Measure EuclN).restrict K),
      ‖c y * w y‖ ≤ ‖(C : ℝ) • w y‖ := by
    filter_upwards [hc_ae_bd] with y hy
    rw [norm_mul, norm_smul]
    have hC_norm : ‖c y‖ ≤ ‖(C : ℝ)‖ := by
      rw [Real.norm_of_nonneg hC_nn]; exact hy
    exact mul_le_mul_of_nonneg_right hC_norm (norm_nonneg _)
  exact lt_of_le_of_lt
    (eLpNorm_mono_ae (μ := (volume : Measure EuclN).restrict K) hpt)
    (hw.const_smul (C : ℝ)).2

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The chart `P₀`-component of the resolvent eigenvector, chart-locality-free:
the coercion-to-function of the `Lp ℝ 2 (chartL2Measure α)` element
`tensorL2ChartComponent g r s (tensorResolventEigenbasisVec …) α P₀`.
Chart-locality-free twin of `eigenvectorChartComponentFun`, re-keyed onto the
intrinsic compactness witness. -/
def eigenvectorChartComponentFun
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- The chart-locality-free eigenvector chart component is `MemLp 2` of the plain
Lebesgue volume restricted to the chart target: it is the coercion of an `Lp`
element of `chartL2Measure α = volume.restrict (chartTargetEuclid α)`.
Chart-locality-free twin of `eigenvectorChartComponentFun_memLp_volume`. -/
lemma eigenvectorChartComponentFun_memLp_volume
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemLp (eigenvectorChartComponentFun (I := I) (M := M)
        g r s i α P₀) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  have h := Lp.memLp (tensorL2ChartComponent (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M)
        g r s) i) α P₀)
  exact h

/-- The recursive `m`-fold mixed weak partial of the eigenvector chart component
in the directions `l : Fin m → Fin n`, via `chosenWeakPartial'`, chart-locality-
free. At `m = 0` it is the chart-locality-free chart component
`eigenvectorChartComponentFun`; at `m + 1` it is the chosen weak
`l (Fin.last m)`-partial of the level-`m` mixed partial. Chart-locality-free twin
of `eigenvectorChartIteratedPartial`. -/
def eigenvectorChartIteratedPartial
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _ => eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀
  | m + 1, l =>
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (eigenvectorChartIteratedPartial g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α)

/-- Definitional unfolding of `eigenvectorChartIteratedPartial` at
`m = 0`. -/
@[simp] theorem eigenvectorChartIteratedPartial_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin 0 → Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ 0 l =
      eigenvectorChartComponentFun (I := I) (M := M)
        g r s i α P₀ := rfl

/-- Definitional unfolding of `eigenvectorChartIteratedPartial` at
`m + 1`. -/
theorem eigenvectorChartIteratedPartial_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) l =
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (chartTargetEuclid (I := I) (M := M) α) := rfl

/-- **Unconditional `L²` membership of every `m`-fold mixed weak partial**
(chart-locality-free). For *every* level `m` and *every* direction multi-index
`l : Fin m → Fin n`, the `m`-fold mixed weak partial
`eigenvectorChartIteratedPartial g r s i α P₀ m l` is `MemLp 2` of
the plain Lebesgue volume restricted to the chart target. Chart-locality-free
twin of `eigenvectorChartIteratedPartial_memLp_volume`. -/
theorem eigenvectorChartIteratedPartial_memLp_volume
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  induction m with
  | zero =>
      rw [eigenvectorChartIteratedPartial_zero]
      exact eigenvectorChartComponentFun_memLp_volume
        (I := I) (M := M) g r s i α P₀
  | succ m _ih =>
      rw [eigenvectorChartIteratedPartial_succ]
      exact chosenWeakPartial'_memLp_volume_unconditional
        (l (Fin.last m)) _

/-- The chart-locality-free `m`-fold mixed weak partial is `MemLp 2` on every
compact subset of the chart target. Chart-locality-free twin of
`eigenvectorChartIteratedPartial_memLp_volume_compact`. -/
private lemma eigenvectorChartIteratedPartial_memLp_volume_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_meas : MeasurableSet K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m l) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_global := eigenvectorChartIteratedPartial_memLp_volume
    (I := I) (M := M) g r s i α P₀ m l
  have h_eq : ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

/-- The five-layer differentiated numerator at level `m + 1`, chart-locality-free.
Chart-locality-free twin of `eigenvectorChartRHSDiffNumerator`, with the recursive
`m`-fold mixed weak partials re-keyed onto
`eigenvectorChartIteratedPartial`. -/
def eigenvectorChartRHSDiffNumerator
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : EuclN → ℝ) (y : EuclN) : ℝ :=
  (∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y)
  + (∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y)
  - densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m (Fin.init l) y
  + densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y * fChartEffPrev y
  + densityOnEuclid (I := I) g α y *
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y

/-- **The chart-locality-free differentiated numerator is `MemLp 2
(volume.restrict (chartPouKernel α))`.** Chart-locality-free twin of
`eigenvectorChartRHSDiffNumerator_memLp_volume_compact`; the proof body transfers
verbatim, with the `m`-fold mixed weak partials re-keyed onto the
chart-locality-free iterated partial. -/
lemma eigenvectorChartRHSDiffNumerator_memLp_volume_compact
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (h_prev : MemLp fChartEffPrev 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))) :
    MemLp (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l fChartEffPrev y) 2
      ((volume : Measure EuclN).restrict
        (chartPouKernel (I := I) (M := M) α)) := by
  classical
  set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K := chartPouKernel_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K :=
    chartPouKernel_measurableSet (I := I) (M := M) α
  have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
  have h_prev_K : MemLp fChartEffPrev 2 ((volume : Measure EuclN).restrict K) :=
    memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure
      (g := g) (α := α) h_prev hK_compact hK_meas hK_in
  have hA : MemLp (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1) *
          eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)) y) 2
      ((volume : Measure EuclN).restrict K) := by
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    have h_coeff : ContDiffOn ℝ ∞
        (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
            (EuclideanSpace.single b 1))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_diffOn : ContDiffOn ℝ ∞
          (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
      have h_fderiv : ContDiffOn ℝ ∞
          (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
              (l (Fin.last m))) y)
          (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
      exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)
    exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      h_coeff hK_compact hK_meas hK_in
      (eigenvectorChartIteratedPartial_memLp_volume_compact
        (I := I) (M := M) g r s i α P₀ (m + 1)
        (Fin.cons a (Fin.init l)) hK_meas hK_in)
  have hB : MemLp (fun y => ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α) y) 2
      ((volume : Measure EuclN).restrict K) := by
    refine memLp_finset_sum _ (fun a _ => memLp_finset_sum _ (fun b _ => ?_))
    refine memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
      hK_compact hK_meas hK_in ?_
    have h_global := chosenWeakPartial'_memLp_volume_unconditional
      (Ω := chartTargetEuclid (I := I) (M := M) α) b
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
    have h_eq : ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [← h_eq]
    exact h_global.restrict K
  have hC : MemLp (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s i α P₀ m (Fin.init l) y) 2
      ((volume : Measure EuclN).restrict K) :=
    memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in
      (eigenvectorChartIteratedPartial_memLp_volume_compact
        (I := I) (M := M) g r s i α P₀ m (Fin.init l)
        hK_meas hK_in)
  have hD : MemLp (fun y =>
      densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
        fChartEffPrev y) 2
      ((volume : Measure EuclN).restrict K) :=
    memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
      hK_compact hK_meas hK_in h_prev_K
  have hE : MemLp (fun y =>
      densityOnEuclid (I := I) g α y *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) y) 2
      ((volume : Measure EuclN).restrict K) := by
    refine memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
      (densityOnEuclid_contDiffOn (I := I) g α) hK_compact hK_meas hK_in ?_
    have h_global := chosenWeakPartial'_memLp_volume_unconditional
      (Ω := chartTargetEuclid (I := I) (M := M) α) (l (Fin.last m)) fChartEffPrev
    have h_eq : ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
      rw [Measure.restrict_restrict hK_meas]
      congr 1
      exact Set.inter_eq_self_of_subset_left hK_in
    rw [← h_eq]
    exact h_global.restrict K
  have h_total := ((((hA.add hB).sub hC).add hD).add hE)
  refine h_total.ae_eq (Filter.Eventually.of_forall (fun y => ?_))
  simp only [eigenvectorChartRHSDiffNumerator, Pi.add_apply,
    Pi.sub_apply]

/-- **The level-`m` differentiated right-hand side of the eigenvector chart
variational identity** (chart-locality-free). Chart-locality-free twin of
`eigenvectorChartRHSDiff`, with the level-`0` leaf the chart-locality-free
seven-term `eigenvectorChartRHS`. -/
def eigenvectorChartRHSDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _ => eigenvectorChartRHS (I := I) (M := M) g r s i α P₀
  | m + 1, l =>
      Set.indicator (chartPouKernel (I := I) (M := M) α)
        (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s i α P₀ m l
            (eigenvectorChartRHSDiff g r s i α P₀ m (Fin.init l)) y /
          densityOnEuclid (I := I) g α y)

/-- Definitional unfolding of `eigenvectorChartRHSDiff` at `m = 0`. -/
@[simp] theorem eigenvectorChartRHSDiff_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin 0 → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff (I := I) (M := M) g r s i α P₀ 0 l =
      eigenvectorChartRHS (I := I) (M := M) g r s i α P₀ := rfl

/-- Definitional unfolding of `eigenvectorChartRHSDiff` at `m + 1`. -/
theorem eigenvectorChartRHSDiff_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ (m + 1) l =
      Set.indicator (chartPouKernel (I := I) (M := M) α)
        (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
            g r s i α P₀ m l
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m (Fin.init l)) y /
          densityOnEuclid (I := I) g α y) := rfl

/-- At level `m + 1`, the chart-locality-free differentiated right-hand side
vanishes pointwise off the compact partition-of-unity kernel `chartPouKernel α`.
Chart-locality-free twin of
`eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel`. -/
theorem eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ (m + 1) l y = 0 := by
  rw [eigenvectorChartRHSDiff_succ, Set.indicator_of_notMem hy]

/-- **Weighted-`L²` membership of the level-`m` differentiated right-hand side**
(chart-locality-free). Chart-locality-free twin of
`eigenvectorChartRHSDiff_memLp_weighted`; the level-`0` leaf is the committed
`eigenvectorChartRHS_memLp_weighted`, and the proof body transfers
verbatim. -/
theorem eigenvectorChartRHSDiff_memLp_weighted
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    MemLp (eigenvectorChartRHSDiff (I := I) (M := M)
        g r s i α P₀ m l) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  induction m with
  | zero =>
      rw [eigenvectorChartRHSDiff_zero]
      exact eigenvectorChartRHS_memLp_weighted
        (I := I) (M := M) g r s i α P₀
  | succ m ih =>
      classical
      set K : Set EuclN := chartPouKernel (I := I) (M := M) α with hK_def
      have hK_compact : IsCompact K :=
        chartPouKernel_isCompact (I := I) (M := M) α
      have hK_meas : MeasurableSet K :=
        chartPouKernel_measurableSet (I := I) (M := M) α
      have hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
        chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
      have h_prev := ih (Fin.init l)
      have h_num := eigenvectorChartRHSDiffNumerator_memLp_volume_compact
        (I := I) (M := M) g r s i α P₀ m l h_prev
      have h_div : MemLp (fun y => eigenvectorChartRHSDiffNumerator
          (I := I) (M := M) g r s i α P₀ m l
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m (Fin.init l)) y /
          densityOnEuclid (I := I) g α y) 2
          ((volume : Measure EuclN).restrict K) := by
        have h_eq : (fun y => eigenvectorChartRHSDiffNumerator
            (I := I) (M := M) g r s i α P₀ m l
              (eigenvectorChartRHSDiff (I := I) (M := M)
                g r s i α P₀ m (Fin.init l)) y /
            densityOnEuclid (I := I) g α y) =
            fun y => (1 / densityOnEuclid (I := I) g α y) *
              eigenvectorChartRHSDiffNumerator (I := I) (M := M)
                g r s i α P₀ m l
                (eigenvectorChartRHSDiff (I := I) (M := M)
                  g r s i α P₀ m (Fin.init l)) y := by
          funext y
          rw [one_div, mul_comm, ← div_eq_mul_inv]
        rw [h_eq]
        exact memLp_volume_compact_contDiffOn_mul (I := I) (M := M) α
          (one_div_densityOnEuclid_contDiffOn' (I := I) (M := M) g α)
          hK_compact hK_meas hK_in h_num
      have h_plain : MemLp (eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ (m + 1) l) 2
          ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)) := by
        rw [eigenvectorChartRHSDiff_succ]
        rw [memLp_indicator_iff_restrict hK_meas]
        have h_double : ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)).restrict K =
            (volume : Measure EuclN).restrict K := by
          rw [Measure.restrict_restrict hK_meas]
          congr 1
          exact Set.inter_eq_self_of_subset_left hK_in
        rw [h_double]
        exact h_div
      refine memLp_chartPulledWeightedMeasure_of_memLp_volume_of_ae_zero_off_compact
        (I := I) (M := M) g α hK_compact hK_meas hK_in
        (Filter.Eventually.of_forall (fun y hy =>
          eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s i α P₀ m l hy))
        h_plain

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
