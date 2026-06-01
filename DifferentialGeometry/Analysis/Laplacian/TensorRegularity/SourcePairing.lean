import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.WeakSolution

/-!
# Chart factorisation of the `L²` source pairing against the rotated test section

For a smooth Riemannian metric `g` on a closed manifold `(M, g)`, a chart center
`α : M`, tensor ranks `(r, s)`, and a component multi-index `P₀`, this file
expresses the `L²` pairing of a smooth source `(r, s)`-tensor section `F`
against the inverse-Gram-rotated test section `rotatedTestSection g r s α P₀ χ`
as a chart-Euclidean integral whose integrand factors as

```
(chart density) · (chart-pushed bump χ̃) · (a test-function-independent C∞ coefficient).
```

The chart density `densityOnEuclid g α` and the chart-pushed scalar bump
`chartPushedRaw I α χ` carry all the dependence on the cut-off `χ`; the
remaining factor `sourcePairingCoeff g r s F α P₀` is a plain function
`EuclideanSpace ℝ (Fin n) → ℝ`, smooth on the chart target and independent of
the bump. This is the source-side counterpart of the chart-pull of the
`H^1` Dirichlet form, and feeds the per-component scalar weak-solution
assembly.

## The factorisation

The rotated test section is a finite sum, over component multi-indices `Q`, of
chart-frame constant basis tensor sections cut off by the chart-pulled inverse
Gram column `covChartMetricGramInv g r s α · Q P₀` times `χ`. The pointwise
tensor inner product `tensorInnerPointwise` is additive in its second slot, so
the integrand splits as a finite sum over `Q`. Each summand pairs the source
`F` against a single chart-frame constant basis section; the bundle-fibre
component expansion `tensorInnerPointwise_toModel_eq_component_sum` rewrites it,
in chart coordinates, into a component-coupled sum through the chart-frame
tensor-metric Gram `covChartMetricGram`. The chart component of the basis
section collapses to a Kronecker delta times the chart-pushed cut-off, leaving,
for each `Q`, the chart-pushed inverse-Gram-weighted bump times a finite sum
over `P` of `covChartMetricGram` against the chart component of `F`.

## Main definitions

* `sourcePairingCoeff g r s F α P₀` — the bump-independent chart coefficient:
  `∑ Q, covChartMetricGramInv g r s α · Q P₀ · (∑ P, covChartMetricGram g r s α
  P Q · tensorComponentEuclid g r s F α P)`, a function
  `EuclideanSpace ℝ (Fin n) → ℝ`.

## Main results

* `sourcePairingCoeff_contDiffOn` — the chart coefficient is `ContDiffOn ℝ ∞`
  on the Euclidean chart target.
* `tensorL2Inner_rotatedTestSection_chart_pull` — the headline: the `L²`
  pairing of `F` against `rotatedTestSection g r s α P₀ χ` equals the
  chart-Euclidean integral of `densityOnEuclid g α · chartPushedRaw I α χ ·
  sourcePairingCoeff g r s F α P₀`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

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

/-- **The bump-independent chart coefficient of the `L²` source pairing.** For
a smooth source `(r, s)`-tensor section `F`, a chart center `α`, and a
component multi-index `P₀`, this is the chart-coordinate assembly

```
∑ Q, covChartMetricGramInv g r s α y Q P₀ ·
  (∑ P, covChartMetricGram g r s α P Q y · tensorComponentEuclid g r s F α P y).
```

The inner sum over `P` is the chart-frame component pairing of the source `F`
against the chart-frame basis tensor indexed by `Q`; the outer sum rotates it
through the inverse Gram column `Q ↦ covChartMetricGramInv g r s α y Q P₀`. The
coefficient is a plain function `EuclideanSpace ℝ (Fin n) → ℝ`, independent of
any test cut-off. -/
noncomputable def sourcePairingCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) : EuclN → ℝ :=
  fun y =>
    ∑ Q : CompIdx E r s,
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
        ∑ P : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s F α P y

/-- Unfolding lemma for `sourcePairingCoeff`. -/
lemma sourcePairingCoeff_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) (y : EuclN) :
    sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y =
      ∑ Q : CompIdx E r s,
        covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
          ∑ P : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s F α P y := rfl

/-- **The bump-independent chart coefficient is `ContDiffOn ℝ ∞` on the
Euclidean chart target.** Each inverse-Gram entry, each Gram entry, and the
Euclidean chart component of `F` are `C^∞` on the chart target; finite sums and
products preserve `ContDiffOn ℝ ∞`. -/
theorem sourcePairingCoeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s) :
    ContDiffOn ℝ ∞ (sourcePairingCoeff (I := I) (M := M) g r s F α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ContDiffOn.sum (fun Q _ => ?_)
  refine ContDiffOn.mul ?_ ?_
  · exact covChartMetricGramInv_entry_contDiffOn (I := I) (M := M) g r s α Q P₀
  · refine ContDiffOn.sum (fun P _ => ?_)
    refine ContDiffOn.mul ?_ ?_
    · exact covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q
    · exact tensorComponentEuclid_contDiffOn (I := I) (M := M) g r s F α P

/-- The bump cutting the `Q`-th summand of the rotated test section: the
chart-pulled inverse-Gram column entry `gramInvWeight g r s α P₀ Q` times the
scalar bump `χ`. -/
private noncomputable def rotatedSummandBump
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ Q : CompIdx E r s) (χ : M → ℝ) : M → ℝ :=
  fun b => gramInvWeight (I := I) (M := M) g r s α P₀ Q b * χ b

/-- The `Q`-th summand of the rotated test section: the chart-frame constant
basis tensor section indexed by `Q`, cut off by `rotatedSummandBump`. -/
private noncomputable def rotatedSummand
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) : SmoothCcTensor g r s :=
  chartBasisTensorSection (I := I) (M := M) g r s α
    (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ)
    (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q hχs)
    (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q hχt)
    Q

/-- The rotated test section equals the `Finset`-sum, over component
multi-indices `Q`, of the chart-frame constant basis sections `rotatedSummand`.
This is the definitional unfolding of `rotatedTestSection`, repackaged through
the `rotatedSummand` abbreviation. -/
private lemma rotatedTestSection_eq_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt =
      ∑ Q : CompIdx E r s,
        rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q := rfl

/-- The underlying-map coercion of a `Finset`-sum of `SmoothCcTensor`s is the
pointwise finite sum of the underlying maps, evaluated at a point. -/
private lemma smoothCcTensor_finsetSum_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {ι : Type*} (t : Finset ι) (S : ι → SmoothCcTensor g r s) (x : M) :
    (∑ i ∈ t, S i).toFun x = ∑ i ∈ t, (S i).toFun x := by
  classical
  induction t using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, SmoothCcTensor.toFun_zero,
        Pi.zero_apply]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        SmoothCcTensor.toFun_add, Pi.add_apply, ih]

/-- The underlying map of the rotated test section is the pointwise finite sum,
over component multi-indices `Q`, of the underlying maps of the chart-frame
constant basis sections `rotatedSummand`. -/
private lemma rotatedTestSection_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) (x : M) :
    (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun x =
      ∑ Q : CompIdx E r s,
        (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun x := by
  rw [rotatedTestSection_eq_sum (I := I) (M := M) g r s α P₀ hχs hχt]
  exact smoothCcTensor_finsetSum_toFun_apply (I := I) (M := M) g r s
    Finset.univ _ x

/-- The underlying-map value of the `Q`-th rotated summand at `x` is the bump
`rotatedSummandBump … Q x` times the canonical model image of the chart-frame
constant basis fiber section. -/
private lemma rotatedSummand_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) (x : M) :
    (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun x =
      TensorRSSpace.toModel
        (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ x •
          chartBasisFiberSection (I := I) (M := M) r s α Q x) := by
  unfold rotatedSummand rotatedSummandBump
  rw [SmoothCcTensor.toFun_apply,
    chartBasisTensorSection_toSection_apply (I := I) (M := M) g r s α
      (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q hχs)
      (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q hχt) Q x]

/-- Wherever the scalar bump `χ` vanishes the `Q`-th rotated summand vanishes:
the bump `rotatedSummandBump … Q` factors through `χ`. -/
private lemma rotatedSummand_toFun_eq_zero_of_bump_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s) {x : M} (hx : χ x = 0) :
    (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun x = 0 := by
  rw [rotatedSummand_toFun_apply (I := I) (M := M) g r s α P₀ hχs hχt Q x]
  have hbump : rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ x = 0 := by
    unfold rotatedSummandBump
    rw [hx, mul_zero]
  rw [hbump, zero_smul, TensorRSSpace.toModel_zero]

/-- Wherever the scalar bump `χ` vanishes the underlying map of the rotated
test section vanishes: each summand vanishes there. -/
private lemma rotatedTestSection_toFun_eq_zero_of_bump_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {x : M} (hx : χ x = 0) :
    (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun x = 0 := by
  classical
  rw [rotatedTestSection_toFun_apply (I := I) (M := M) g r s α P₀ hχs hχt x]
  refine Finset.sum_eq_zero (fun Q _ => ?_)
  exact rotatedSummand_toFun_eq_zero_of_bump_eq_zero (I := I) (M := M)
    g r s α P₀ hχs hχt Q hx

/-- The `L²` source-pairing integrand `x ↦ ⟨F(x), (rotated test section)(x)⟩`
vanishes wherever the scalar bump `χ` vanishes: the rotated test section
vanishes there and the pointwise inner product is then `0`. -/
private lemma sourcePairingIntegrand_eq_zero_of_bump_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {x : M} (hx : χ x = 0) :
    tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
        ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun x) =
      0 := by
  rw [rotatedTestSection_toFun_eq_zero_of_bump_eq_zero (I := I) (M := M)
    g r s α P₀ hχs hχt hx]
  exact tensorInnerPointwise_zero_right (I := I) (M := M) g r s x (F.toFun x)

/-- The topological support of the `L²` source-pairing integrand sits inside the
chart-`α` source: the integrand vanishes off the support of `χ`, whose closure
the hypothesis `hχt` places inside the chart source. -/
private lemma sourcePairingIntegrand_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    tsupport
        (fun x : M =>
          tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
            ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
              x)) ⊆
      (chartAt H α).source := by
  refine (closure_minimal ?_ (isClosed_tsupport χ)).trans hχt
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notsupp
  exact hx (sourcePairingIntegrand_eq_zero_of_bump_eq_zero (I := I) (M := M)
    g r s F α P₀ hχs hχt
    (image_eq_zero_of_notMem_tsupport hx_notsupp))

/-- The `L²` source-pairing integrand is continuous on `M`. -/
private lemma sourcePairingIntegrand_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    Continuous
      (fun x : M =>
        tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
          ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
            x)) :=
  DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_cross
    (I := I) (M := M)
    F (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt)

/-- The bridge between the wrapped raw-component projection of the source `F`'s
section value and its raw chart-frame scalar component: both unfold to the
chart-frame component projection of the trivialisation-projected value. -/
private lemma wrappedComponentProj_F_section_eq_tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M) (b : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx (F.toSection b) =
      tensorChartComponentRaw (I := I) (M := M) g r s F α Idx Jdx b := by
  rw [wrappedComponentProj_apply, tensorChartComponentRaw_def]
  rfl

/-- The wrapped raw-component projection of the `Q`-th rotated summand's section
value, on the Euclidean chart target, is the chart-pushed bump
`chartPushedRaw I α (rotatedSummandBump … Q) y` times the Kronecker delta
`[(Idx, Jdx) = Q]`. -/
private lemma wrappedComponentProj_rotatedSummand_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    wrappedComponentProj (I := I) (M := M) r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) Idx Jdx
        ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      chartPushedRaw I α (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ)
          y *
        (if (Idx, Jdx) = Q then (1 : ℝ) else 0) := by
  rw [wrappedComponentProj_apply]
  rw [show tensorChartComponentProjection (E := E) r s Idx Jdx
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))) =
      tensorChartComponentRaw (I := I) (M := M) g r s
          (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q) α Idx Jdx
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) from rfl]
  exact chartBasisTensorSection_chartComp (I := I) (M := M) g r s α
    (gramInvWeight_mul_bump_contMDiffOn (I := I) (M := M) g r s α P₀ Q hχs)
    (gramInvWeight_mul_bump_tsupport (I := I) (M := M) g r s α P₀ Q hχt)
    Q Idx Jdx hy

/-- The chart-pushed `Q`-th summand bump, on the Euclidean chart target, is the
inverse-Gram entry `covChartMetricGramInv g r s α y Q P₀` times the chart-pushed
scalar bump `chartPushedRaw I α χ y`. -/
private lemma chartPushedRaw_rotatedSummandBump_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ Q : CompIdx E r s) {χ : M → ℝ}
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw I α (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ) y =
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
        chartPushedRaw I α χ y := by
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  unfold rotatedSummandBump
  have hb_eq : (toEuclidean (E := E))
      ((extChartAt I α)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
    have hy' : y ∈ (toEuclidean (E := E)).symm ⁻¹' (extChartAt I α).target := by
      rw [← chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]; exact hy
    rw [(extChartAt I α).right_inv hy', ContinuousLinearEquiv.apply_symm_apply]
  rw [show gramInvWeight (I := I) (M := M) g r s α P₀ Q
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ from by
    unfold gramInvWeight; rw [hb_eq]]
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α χ hy]

/-- **Chart-coordinate factorisation of one source-pairing summand.** On the
Euclidean chart target, the pointwise tensor inner product of the source `F`
against the `Q`-th rotated summand, read at the chart-source preimage of `y`,
equals the inverse-Gram-weighted chart-pushed bump
`covChartMetricGramInv g r s α y Q P₀ · chartPushedRaw I α χ y` times the
chart-frame component pairing `∑ P, covChartMetricGram g r s α P Q y ·
tensorComponentEuclid g r s F α P y`. -/
private lemma tensorInnerPointwise_F_rotatedSummand_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    (Q : CompIdx E r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorInnerPointwise (I := I) (M := M) g r s
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (F.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      covChartMetricGramInv (I := I) (M := M) g r s α y Q P₀ *
        chartPushedRaw I α χ y *
        ∑ P : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s F α P y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [show F.toFun b = TensorRSSpace.toModel (F.toSection b) from rfl]
  rw [show (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun b =
      TensorRSSpace.toModel
        ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection b)
      from rfl]
  rw [tensorInnerPointwise_toModel_eq_component_sum (I := I) (M := M)
    g r s α hb_chart (F.toSection b)
    ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection b)]
  have hterm : ∀ P Q' : CompIdx E r s,
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
            (tensorChartBasisElement (E := E) r s P.1 P.2)
            (tensorChartBasisElement (E := E) r s Q'.1 Q'.2) *
          (wrappedComponentProj (I := I) (M := M) r s α b P.1 P.2
              (F.toSection b) *
            wrappedComponentProj (I := I) (M := M) r s α b Q'.1 Q'.2
              ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toSection
                b)) =
        covChartMetricGram (I := I) (M := M) g r s α P Q' y *
          (tensorComponentEuclid (I := I) (M := M) g r s F α P y *
            (chartPushedRaw I α
                (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ) y *
              (if (Q'.1, Q'.2) = Q then (1 : ℝ) else 0))) := by
    intro P Q'
    rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
          (tensorChartBasisElement (E := E) r s P.1 P.2)
          (tensorChartBasisElement (E := E) r s Q'.1 Q'.2) =
        covChartMetricGram (I := I) (M := M) g r s α P Q' y from by
      rw [covChartMetricGram_def, ← hb_def]]
    rw [wrappedComponentProj_F_section_eq_tensorChartComponentRaw
      (I := I) (M := M) g r s F α b P.1 P.2]
    rw [show tensorChartComponentRaw (I := I) (M := M) g r s F α P.1 P.2 b =
        tensorComponentEuclid (I := I) (M := M) g r s F α P y from by
      rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s F α P hy,
        hb_def]]
    rw [wrappedComponentProj_rotatedSummand_section (I := I) (M := M)
      g r s α P₀ hχs hχt Q Q'.1 Q'.2 hy]
  rw [Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl
    (fun Q' _ => hterm P Q'))]
  have hcollapse : ∀ P : CompIdx E r s,
      (∑ Q' : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q' y *
            (tensorComponentEuclid (I := I) (M := M) g r s F α P y *
              (chartPushedRaw I α
                  (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ) y *
                (if (Q'.1, Q'.2) = Q then (1 : ℝ) else 0)))) =
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          (tensorComponentEuclid (I := I) (M := M) g r s F α P y *
            chartPushedRaw I α
              (rotatedSummandBump (I := I) (M := M) g r s α P₀ Q χ) y) := by
    intro P
    rw [Finset.sum_eq_single Q]
    · rw [show ((Q.1, Q.2) : CompIdx E r s) = Q from Prod.ext rfl rfl,
        if_pos rfl, mul_one]
    · intro Q' _ hne
      rw [if_neg (fun h => hne (Prod.ext (congrArg Prod.fst h)
        (congrArg Prod.snd h))), mul_zero, mul_zero, mul_zero]
    · intro hQ
      exact absurd (Finset.mem_univ Q) hQ
  rw [Finset.sum_congr rfl (fun P _ => hcollapse P)]
  rw [chartPushedRaw_rotatedSummandBump_eq (I := I) (M := M) g r s α P₀ Q
    (χ := χ) hy]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  ring

/-- **Chart-coordinate factorisation of the source-pairing integrand.** On the
Euclidean chart target the pointwise tensor inner product of the source `F`
against the rotated test section, read at the chart-source preimage of `y`,
factors as the chart-pushed scalar bump `chartPushedRaw I α χ y` times the
bump-independent coefficient `sourcePairingCoeff g r s F α P₀ y`. -/
private lemma tensorInnerPointwise_F_rotatedTestSection_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorInnerPointwise (I := I) (M := M) g r s
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (F.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      chartPushedRaw I α χ y * sourcePairingCoeff (I := I) (M := M) g r s F α P₀
        y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  rw [rotatedTestSection_toFun_apply (I := I) (M := M) g r s α P₀ hχs hχt b]
  have hadd :
      tensorInnerPointwise (I := I) (M := M) g r s b (F.toFun b)
          (∑ Q : CompIdx E r s,
            (rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun b) =
        ∑ Q : CompIdx E r s,
          tensorInnerPointwise (I := I) (M := M) g r s b (F.toFun b)
            ((rotatedSummand (I := I) (M := M) g r s α P₀ hχs hχt Q).toFun b) := by
    induction (Finset.univ : Finset (CompIdx E r s)) using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        exact tensorInnerPointwise_zero_right (I := I) (M := M) g r s b
          (F.toFun b)
    | insert Q A hQ ih =>
        rw [Finset.sum_insert hQ, Finset.sum_insert hQ,
          tensorInnerPointwise_add_right, ih]
  rw [hadd]
  rw [Finset.sum_congr rfl (fun Q _ =>
    tensorInnerPointwise_F_rotatedSummand_chart (I := I) (M := M) g r s F α P₀
      hχs hχt Q hy)]
  rw [sourcePairingCoeff_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  ring

/-- **Chart factorisation of the `L²` source pairing.** For a smooth source
`(r, s)`-tensor section `F` on a closed Riemannian manifold `(M, g)`, a chart
center `α`, a component multi-index `P₀`, and a scalar bump `χ` smooth on the
chart-`α` source with `tsupport χ ⊆ (chartAt H α).source`, the global `L²`
pairing of `F` against the inverse-Gram-rotated test section
`rotatedTestSection g r s α P₀ χ` equals the chart-Euclidean integral

```
∫ y in chartTargetEuclid α,
  densityOnEuclid g α y · chartPushedRaw I α χ y · sourcePairingCoeff g r s F α P₀ y
  ∂(Measure.map toEuclidean modelHaar).
```

The chart density `densityOnEuclid g α` and the chart-pushed bump
`chartPushedRaw I α χ` carry the dependence on the cut-off `χ`; the remaining
factor `sourcePairingCoeff g r s F α P₀` is bump-independent and `C^∞` on the
chart target (`sourcePairingCoeff_contDiffOn`). -/
theorem tensorL2Inner_rotatedTestSection_chart_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) (α : M)
    (P₀ : CompIdx E r s)
    {χ : M → ℝ} (hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ χ (chartAt H α).source)
    (hχt : tsupport χ ⊆ (chartAt H α).source) :
    tensorL2Inner (I := I) (M := M) g r s F.toFun
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * chartPushedRaw I α χ y *
          sourcePairingCoeff (I := I) (M := M) g r s F α P₀ y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  classical
  rw [show tensorL2Inner (I := I) (M := M) g r s F.toFun
        (rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun =
      ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
          ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from rfl]
  have hcont : Continuous
      (fun x : M =>
        tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
          ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
            x)) :=
    sourcePairingIntegrand_continuous (I := I) (M := M) g r s F α P₀ hχs hχt
  have hsupp : tsupport
      (fun x : M =>
        tensorInnerPointwise (I := I) (M := M) g r s x (F.toFun x)
          ((rotatedTestSection (I := I) (M := M) g r s α P₀ χ hχs hχt).toFun
            x)) ⊆
      (chartAt H α).source :=
    sourcePairingIntegrand_tsupport_subset (I := I) (M := M) g r s F α P₀ hχs
      hχt
  rw [integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α hcont hsupp]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  refine setIntegral_congr_fun hctE_meas (fun y hy => ?_)
  rw [tensorInnerPointwise_F_rotatedTestSection_chart (I := I) (M := M)
    g r s F α P₀ hχs hχt hy]
  ring

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
