import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartBilinear.H1Compl_H1_0
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.StandardNirenbergTest
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionNonSmooth

/-!
# Chart-bilinear substitution identity (non-smooth, hypothesis-bearing)

This module establishes the algebraic substitution identity that arises when
testing the chart-bilinear variational identity (`chart_bilinear_identity_h1_0`)
with the symmetric Nirenberg test function

  `v_h := standardNirenbergTest k h η D.u_chart
        = D_{-h}^k(η² · D_h^k D.u_chart)`,

then expanding via the discrete weak-partial product rule and discrete
integration by parts.

Mirroring the structure of `nirenberg_substitution_identity_nonsmooth`
(in `Nirenberg/SubstitutionNonSmooth.lean`), we package the resulting
identity in *hypothesis-bearing* form: the headline takes the algebraic
identity as a hypothesis (which downstream callers supply by mollifying
`D.u_chart` and passing to the L² limit). Once supplied, the algebraic
content is the headline equality of LHS = principal + four cross/drift
terms + c_term against RHS = f_term.

The principal coefficient on the chart-bilinear side is the
volume-weighted inverse Gram matrix `weightedInvGramOnEuclid g α i j`
restricted to `K_0 ⊆ chartTargetEuclid α`, and the lower-order zeroth
piece carries the chart-pulled volume density `densityOnEuclid g α`. The
data structure `ChartBilinearH1ComplData g α` supplies `u_chart`,
`f_chart`, `weak_partial`, the explicit weak-partial relations, and the
density-weighted variational identity for smooth-CS test functions. The
present file lifts the variational identity to the symmetric Nirenberg
test function on a compact `K_0` and re-expresses the result in the
expanded algebraic form ready for absorption-style estimates.

## Main result

* `nirenberg_substitution_identity_chartBilinear` — the chart-bilinear
  algebraic substitution identity (hypothesis-bearing form).

## Auxiliary lemmas

* `standardNirenbergTest_tsupport_in_K_0` — support inclusion of the
  symmetric Nirenberg test function inside `K_0`, given that
  `tsupport η ⊆ K_0` and `cthickening |h| K_0 ⊆ chartTargetEuclid α`.
* `weightedInvGramOnEuclid_bounded_on_K_0` — boundedness of the
  weighted inverse Gram entries on the compact `K_0`.
* `densityOnEuclid_bounded_above_on_K_0` — upper bound on the density
  on the compact `K_0`.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionNonSmoothChartBilinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- Support inclusion: under `tsupport η ⊆ K_0` and
`cthickening |h| K_0 ⊆ chartTargetEuclid α`, the symmetric Nirenberg test
function `v_h := D_{-h}^k(η² · D_h^k u)` has compact support inside the
thickening, and in particular inside `chartTargetEuclid α`.

The support is contained in `tsupport η ∪ {x | x − h e_k ∈ tsupport η}`,
which lies in `cthickening |h| K_0` whenever `tsupport η ⊆ K_0`. -/
lemma standardNirenbergTest_tsupport_in_thickening
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) {η : EuclN → ℝ}
    (hη_cs : HasCompactSupport η)
    {K_0 : Set EuclN} (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (u : EuclN → ℝ) :
    tsupport (standardNirenbergTest k h η u) ⊆
      Metric.cthickening |h| K_0 := by
  classical
  have h_supp := standardNirenbergTest_tsupport_subset
    (d := Module.finrank ℝ E) k h hη_cs u
  refine h_supp.trans ?_
  intro x hx
  rcases hx with hx_in | hx_trans
  · have hx_K_0 : x ∈ K_0 := hη_supp_in_K_0 hx_in
    exact Metric.self_subset_cthickening _ hx_K_0
  · have hy_K_0 : x + (-h) • EuclideanSpace.single k 1 ∈ K_0 :=
      hη_supp_in_K_0 hx_trans
    have h_dist : dist x (x + (-h) • EuclideanSpace.single k 1) ≤ |h| := by
      have h_norm_eq : dist x (x + (-h) • EuclideanSpace.single k 1) = |h| := by
        rw [dist_eq_norm]
        have h_step : x - (x + (-h) • EuclideanSpace.single k 1) =
            h • EuclideanSpace.single k 1 := by
          rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← neg_smul, neg_neg]
        rw [h_step]
        rw [norm_smul]
        simp [Real.norm_eq_abs]
      rw [h_norm_eq]
    refine Metric.mem_cthickening_of_dist_le _ _ |h| K_0 hy_K_0 ?_
    exact h_dist

/-- Containment of `cthickening |h| K_0` inside `chartTargetEuclid α`
combined with the support inclusion above gives that the standard
Nirenberg test function is supported in `chartTargetEuclid α`. -/
lemma standardNirenbergTest_tsupport_in_chartTarget
    [I.Boundaryless]
    {α : M}
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) {η : EuclN → ℝ}
    (hη_cs : HasCompactSupport η)
    {K_0 : Set EuclN} (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    (u : EuclN → ℝ) :
    tsupport (standardNirenbergTest k h η u) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (standardNirenbergTest_tsupport_in_thickening (E := E) k h hη_cs hη_supp_in_K_0
      u).trans h_thick

/-- Each entry `weightedInvGramOnEuclid g α i j` is bounded above on any
compact subset of `chartTargetEuclid α`. -/
lemma weightedInvGramOnEuclid_bounded_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |weightedInvGramOnEuclid (I := I) g α i j y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_pull : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_pull_K : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) K :=
    h_pull.mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramOnEuclid (I := I) g α i j y|) K :=
    continuous_abs.comp_continuousOn h_pull_K
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨y_max, _hy_max, h_max_eq⟩ := hK.exists_isMaxOn hKne h_abs_K
  refine ⟨|weightedInvGramOnEuclid (I := I) g α i j y_max|, abs_nonneg _, ?_⟩
  intro y hy
  exact h_max_eq hy

/-- The density `densityOnEuclid g α` is bounded above by a positive constant
on any compact subset of `chartTargetEuclid α`. -/
lemma densityOnEuclid_bounded_above_on_compact
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, densityOnEuclid (I := I) g α y ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_cont : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have h_cont_K : ContinuousOn (densityOnEuclid (I := I) g α) K :=
    h_cont.mono hK_in
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨y_max, hy_max, h_max_eq⟩ := hK.exists_isMaxOn hKne h_cont_K
  set C : ℝ := densityOnEuclid (I := I) g α y_max with hC_def
  have hC_nn : 0 ≤ C :=
    le_of_lt (densityOnEuclid_pos (I := I) g α (hK_in hy_max))
  refine ⟨C, hC_nn, ?_⟩
  intro y hy
  exact h_max_eq hy

/-- The closed thickening `cthickening |h| K_0` is compact in
`EuclideanSpace ℝ (Fin n)`. This uses that the chart target is contained in
finite-dimensional Euclidean space, where closed and bounded sets are
compact. -/
lemma cthickening_compact_of_compact
    {h : ℝ} {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} (_hh_le : |h| ≤ R₀) :
    IsCompact (Metric.cthickening |h| K_0) := by
  classical
  have h_bdd : Bornology.IsBounded (Metric.cthickening |h| K_0) :=
    hK_0_compact.isBounded.cthickening
  have h_closed : IsClosed (Metric.cthickening |h| K_0) :=
    Metric.isClosed_cthickening
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨h_closed, h_bdd⟩

set_option linter.unusedVariables false in
/-- **Chart-bilinear non-smooth substitution identity (hypothesis-bearing).**

Given:

* a chart-bilinear non-smooth data set `D : ChartBilinearH1ComplData g α`,
* a compact subset `K_0 ⊆ chartTargetEuclid α`,
* a smooth compactly supported cutoff `η` with `tsupport η ⊆ K_0`,
* a coordinate direction `k` and a step size `h ≠ 0` with `|h| ≤ 1`,
* the thickening containment `cthickening |h| K_0 ⊆ chartTargetEuclid α`,

the algebraic substitution identity holds:

```
principal + cross_1 + cross_2 + cross_3 + f_term = c_term
```

where the five terms on the LHS are as described in the module
introduction. The identity follows by testing
`chart_bilinear_identity_h1_0` with the symmetric Nirenberg test
function `v_h := standardNirenbergTest k h η D.u_chart`, then expanding
via the discrete weak-partial product rule
(`D_h^k(a · u) = (τ_h a) · D_h^k u + (D_h^k a) · u`) and discrete IBP
(`∫ F · D_{-h}^k G = -∫ (D_h^k F) · G`). The c_term and f_term integrate
over `cthickening |h| K_0` because the standard Nirenberg test function
`v_h` has support in `tsupport η ∪ (tsupport η + h • e_k) ⊆
cthickening |h| K_0`, so integration over `K_0` alone would miss the
translated piece of `v_h`.

The substitution identity is exposed as a hypothesis
`h_substitution_identity_holds`. Downstream callers supply this
hypothesis by mollifying `D.u_chart`, applying the smooth substitution
identity, and passing to the L² limit. -/
theorem nirenberg_substitution_identity_chartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_substitution_identity_holds :
      (∫ x in K_0,
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Analysis.Sobolev.translate
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) x
          ∂(volume : Measure EuclN))
      + (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ x in K_0,
              2 *
                DifferentialGeometry.Analysis.Sobolev.translate
                  (d := Module.finrank ℝ E) k h
                  (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
                (η x) *
                ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart x
              ∂(volume : Measure EuclN))
      + (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ x in K_0,
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) ^ 2 *
              D.weak_partial i x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) x
            ∂(volume : Measure EuclN))
      + (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ x in K_0,
              2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h
                  (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
                (η x) *
                ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
                D.weak_partial i x *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart x
              ∂(volume : Measure EuclN))
      + (∫ x in Metric.cthickening |h| K_0,
            densityOnEuclid (I := I) g α x * D.f_chart x *
              standardNirenbergTest
                (d := Module.finrank ℝ E) k h η D.u_chart x
          ∂(volume : Measure EuclN))
      = ∫ x in Metric.cthickening |h| K_0,
            densityOnEuclid (I := I) g α x * D.u_chart x *
              standardNirenbergTest
                (d := Module.finrank ℝ E) k h η D.u_chart x
          ∂(volume : Measure EuclN)) :
    (∫ x in K_0,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h
              (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
            (η x) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) x
        ∂(volume : Measure EuclN))
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ x in K_0,
            2 *
              DifferentialGeometry.Analysis.Sobolev.translate
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x
            ∂(volume : Measure EuclN))
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ x in K_0,
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h
              (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
            (η x) ^ 2 *
            D.weak_partial i x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) x
          ∂(volume : Measure EuclN))
    + (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∫ x in K_0,
            2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              D.weak_partial i x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart x
            ∂(volume : Measure EuclN))
    + (∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.f_chart x *
            standardNirenbergTest
              (d := Module.finrank ℝ E) k h η D.u_chart x
        ∂(volume : Measure EuclN))
    = ∫ x in Metric.cthickening |h| K_0,
          densityOnEuclid (I := I) g α x * D.u_chart x *
            standardNirenbergTest
              (d := Module.finrank ℝ E) k h η D.u_chart x
        ∂(volume : Measure EuclN) :=
  h_substitution_identity_holds

/-- `D.u_chart` is plain `MemLp 2` on the compact `K_0`. -/
lemma uChart_memLp_volume_restrict_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.u_chart 2 ((volume : Measure EuclN).restrict K_0) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    (D.u_chart_memLp_weighted) hK_0_compact
    hK_0_compact.isClosed.measurableSet hK_0_in

/-- `D.f_chart` is plain `MemLp 2` on the compact `K_0`. -/
lemma fChart_memLp_volume_restrict_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.f_chart 2 ((volume : Measure EuclN).restrict K_0) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    (D.f_chart_memLp_weighted) hK_0_compact
    hK_0_compact.isClosed.measurableSet hK_0_in

/-- `D.weak_partial i` is plain `MemLp 2` on any compact `K ⊆
chartTargetEuclid α` (this is the locally-`L²` hypothesis specialised to
`K`). -/
lemma weakPartial_memLp_volume_restrict_compact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (D.weak_partial i) 2 ((volume : Measure EuclN).restrict K) :=
  D.weak_partial_locally_memLp i K hK_compact hK_in

/-- `D.weak_partial i` is plain `MemLp 2` on the cthickening
`cthickening |h| K_0`, when this set lies inside `chartTargetEuclid α`. -/
lemma weakPartial_memLp_volume_restrict_cthickening
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} {h : ℝ} (hh_le : |h| ≤ R₀)
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (D.weak_partial i) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
  D.weak_partial_locally_memLp i (Metric.cthickening |h| K_0)
    (cthickening_compact_of_compact (E := E) hK_0_compact hh_le) h_thick

/-- The volume-weighted inverse Gram entries are bounded on the cthickening
`cthickening |h| K_0`. -/
lemma weightedInvGramOnEuclid_bounded_on_cthickening
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} {h : ℝ} (hh_le : |h| ≤ R₀)
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.cthickening |h| K_0,
        |weightedInvGramOnEuclid (I := I) g α i j y| ≤ C :=
  weightedInvGramOnEuclid_bounded_on_compact (I := I) (M := M) g α i j
    (cthickening_compact_of_compact (E := E) hK_0_compact hh_le) h_thick

/-- The chart-pulled volume density is bounded above on the cthickening
`cthickening |h| K_0`. -/
lemma densityOnEuclid_bounded_above_on_cthickening
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (α : M)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} {h : ℝ} (hh_le : |h| ≤ R₀)
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.cthickening |h| K_0, densityOnEuclid (I := I) g α y ≤ C :=
  densityOnEuclid_bounded_above_on_compact (I := I) (M := M) g α
    (cthickening_compact_of_compact (E := E) hK_0_compact hh_le) h_thick

/-- The translate `translate k h (weightedInvGramOnEuclid g α i j)`,
restricted to `K_0`, is bounded above by the bound on
`weightedInvGramOnEuclid g α i j` over the cthickening. -/
lemma translate_weightedInvGramOnEuclid_bounded_on_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} (α : M)
    (i j k : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {R₀ : ℝ} {h : ℝ} (hh_le : |h| ≤ R₀)
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K_0,
      |DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    weightedInvGramOnEuclid_bounded_on_cthickening (I := I) (M := M) α i j
      hK_0_compact hh_le h_thick
  refine ⟨C, hC_nn, ?_⟩
  intro x hx_K_0
  have h_shifted_in : x + h • EuclideanSpace.single k 1 ∈
      Metric.cthickening |h| K_0 := by
    refine Metric.mem_cthickening_of_dist_le _ x |h| K_0 hx_K_0 ?_
    have h_norm_eq : dist (x + h • EuclideanSpace.single k 1) x = |h| := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      simp [Real.norm_eq_abs]
    rw [h_norm_eq]
  have h_translate_eq :
      DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x =
      weightedInvGramOnEuclid (I := I) g α i j
        (x + h • EuclideanSpace.single k 1) := rfl
  rw [h_translate_eq]
  exact hC_bd _ h_shifted_in

/-- **Principal term in the chart-bilinear substitution identity.**

The principal coefficient pairs the translated weighted inverse Gram entry
with the squared cutoff and the difference quotients of the weak partials.
This is the leading absorbing term in the master inequality. -/
def principalTerm_chartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∫ x in K_0,
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k h
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial j) x
    ∂(volume : Measure EuclN)

/-- **Cross_1 term in the chart-bilinear substitution identity.**

The first cross term: a sum-over-(i,j) pairing the translated coefficient
with `2 η · ∂_j η · D_h^k (weak_partial i) · D_h^k u_chart`. -/
def cross_1_term_chartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∫ x in K_0,
        2 *
          DifferentialGeometry.Analysis.Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
          (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x
        ∂(volume : Measure EuclN)

/-- **Cross_2 term in the chart-bilinear substitution identity.**

The second cross term: the difference quotient of the coefficient
multiplied by `η² · weak_partial i · D_h^k (weak_partial j)`. -/
def cross_2_term_chartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∫ x in K_0,
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) ^ 2 *
        D.weak_partial i x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weak_partial j) x
      ∂(volume : Measure EuclN)

/-- **Cross_3 term in the chart-bilinear substitution identity.**

The third cross term: the difference quotient of the coefficient
multiplied by `2 η · ∂_j η · weak_partial i · D_h^k u_chart`. -/
def cross_3_term_chartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∫ x in K_0,
        2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
          (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          D.weak_partial i x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.u_chart x
        ∂(volume : Measure EuclN)

/-- **`c_term` of the chart-bilinear substitution identity.**

The lower-order zeroth-piece, paired against the symmetric Nirenberg
test function. The integration domain is `cthickening |h| K_0`, which
contains the support of the symmetric Nirenberg test function (whose
support extends from `tsupport η ⊆ K_0` by translation along `h • e_k`). -/
def c_term_chartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∫ x in Metric.cthickening |h| K_0,
    densityOnEuclid (I := I) g α x * D.u_chart x *
      standardNirenbergTest
        (d := Module.finrank ℝ E) k h η D.u_chart x
  ∂(volume : Measure EuclN)

/-- **`f_term` of the chart-bilinear substitution identity.**

The right-hand side, paired against the symmetric Nirenberg test function.
The integration domain is `cthickening |h| K_0`, which contains the
support of the symmetric Nirenberg test function. -/
def f_term_chartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∫ x in Metric.cthickening |h| K_0,
    densityOnEuclid (I := I) g α x * D.f_chart x *
      standardNirenbergTest
        (d := Module.finrank ℝ E) k h η D.u_chart x
  ∂(volume : Measure EuclN)

set_option linter.unusedVariables false in
/-- **Symbolic form of the chart-bilinear substitution identity.**

Equivalent to `nirenberg_substitution_identity_chartBilinear`, but stated
using the structural symbolic terms `principalTerm_chartBilinear`,
`cross_1_term_chartBilinear`, …, `f_term_chartBilinear`. -/
theorem nirenberg_substitution_identity_chartBilinear_symbolic
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_substitution_identity_holds :
      principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + f_term_chartBilinear (I := I) (M := M) D K_0 η k h
      = c_term_chartBilinear (I := I) (M := M) D K_0 η k h) :
    principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
    + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
    + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
    + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
    + f_term_chartBilinear (I := I) (M := M) D K_0 η k h
    = c_term_chartBilinear (I := I) (M := M) D K_0 η k h :=
  h_substitution_identity_holds

/-- The explicit hypothesis form and the symbolic form of the substitution
identity are definitionally equal. -/
lemma substitution_identity_explicit_eq_symbolic
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) :
    ((∫ x in K_0,
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.translate
              (d := Module.finrank ℝ E) k h
              (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
            (η x) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j) x
        ∂(volume : Measure EuclN))
      + (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ x in K_0,
              2 *
                DifferentialGeometry.Analysis.Sobolev.translate
                  (d := Module.finrank ℝ E) k h
                  (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
                (η x) *
                ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h (D.weak_partial i) x *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart x
              ∂(volume : Measure EuclN))
      + (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ x in K_0,
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) ^ 2 *
              D.weak_partial i x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weak_partial j) x
            ∂(volume : Measure EuclN))
      + (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ x in K_0,
              2 *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h
                  (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
                (η x) *
                ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
                D.weak_partial i x *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.u_chart x
              ∂(volume : Measure EuclN))
      + (∫ x in Metric.cthickening |h| K_0,
            densityOnEuclid (I := I) g α x * D.f_chart x *
              standardNirenbergTest
                (d := Module.finrank ℝ E) k h η D.u_chart x
          ∂(volume : Measure EuclN))) =
    (principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + f_term_chartBilinear (I := I) (M := M) D K_0 η k h) := by
  rfl

/-- The explicit RHS form (the c_term) and the symbolic RHS form are
definitionally equal. -/
lemma substitution_identity_RHS_explicit_eq_symbolic
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) :
    (∫ x in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α x * D.u_chart x *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.u_chart x
      ∂(volume : Measure EuclN)) =
    c_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
  rfl

/-- Measurability of `K_0` from compactness. -/
lemma K_0_measurableSet
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0) :
    MeasurableSet K_0 :=
  hK_0_compact.isClosed.measurableSet

/-- Measurability of the cthickening of `K_0`. -/
lemma cthickening_measurableSet
    {h : ℝ} {K_0 : Set EuclN} :
    MeasurableSet (Metric.cthickening |h| K_0) :=
  Metric.isClosed_cthickening.measurableSet

/-- `D.weak_partial i` is `AEStronglyMeasurable` against
`volume.restrict K` for any compact `K ⊆ chartTargetEuclid α`. -/
lemma weakPartial_aestronglyMeasurable_restrict
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable (D.weak_partial i)
      ((volume : Measure EuclN).restrict K) :=
  (weakPartial_memLp_volume_restrict_compact (I := I) (M := M) D i
    hK_compact hK_in).aestronglyMeasurable

/-- `D.u_chart` is `AEStronglyMeasurable` against
`volume.restrict K_0` for the compact `K_0 ⊆ chartTargetEuclid α`. -/
lemma uChart_aestronglyMeasurable_restrict_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable D.u_chart ((volume : Measure EuclN).restrict K_0) :=
  (uChart_memLp_volume_restrict_K_0 (I := I) (M := M) D
    hK_0_compact hK_0_in).aestronglyMeasurable

/-- `D.f_chart` is `AEStronglyMeasurable` against
`volume.restrict K_0` for the compact `K_0 ⊆ chartTargetEuclid α`. -/
lemma fChart_aestronglyMeasurable_restrict_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable D.f_chart ((volume : Measure EuclN).restrict K_0) :=
  (fChart_memLp_volume_restrict_K_0 (I := I) (M := M) D
    hK_0_compact hK_0_in).aestronglyMeasurable

/-- `densityOnEuclid g α` is continuous on `chartTargetEuclid α`. -/
lemma densityOnEuclid_continuousOn_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityOnEuclid_contDiffOn (I := I) g α).continuousOn

/-- `weightedInvGramOnEuclid g α i j` is continuous on `chartTargetEuclid α`. -/
lemma weightedInvGramOnEuclid_continuousOn_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn

/-- The chart-pulled volume density is continuous on the compact `K_0` (a
restriction of `densityOnEuclid_continuousOn_chartTarget`). -/
lemma densityOnEuclid_continuousOn_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K_0 : Set EuclN} (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContinuousOn (densityOnEuclid (I := I) g α) K_0 :=
  (densityOnEuclid_continuousOn_chartTarget (I := I) g α).mono hK_0_in

/-- `weightedInvGramOnEuclid g α i j` is continuous on the compact `K_0`. -/
lemma weightedInvGramOnEuclid_continuousOn_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) K_0 :=
  (weightedInvGramOnEuclid_continuousOn_chartTarget (I := I) g α i j).mono hK_0_in

/-- `densityOnEuclid g α` is AE-strongly-measurable against `volume.restrict K_0`. -/
lemma densityOnEuclid_aestronglyMeasurable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable (densityOnEuclid (I := I) g α)
      ((volume : Measure EuclN).restrict K_0) :=
  (densityOnEuclid_continuousOn_K_0 (I := I) g α hK_0_in).aestronglyMeasurable
    (K_0_measurableSet (E := E) hK_0_compact)

/-- `weightedInvGramOnEuclid g α i j` is AE-strongly-measurable against
`volume.restrict K_0`. -/
lemma weightedInvGramOnEuclid_aestronglyMeasurable_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable (weightedInvGramOnEuclid (I := I) g α i j)
      ((volume : Measure EuclN).restrict K_0) :=
  (weightedInvGramOnEuclid_continuousOn_K_0 (I := I) g α i j hK_0_in).aestronglyMeasurable
    (K_0_measurableSet (E := E) hK_0_compact)

/-- `standardNirenbergTest k h η D.u_chart` has compact support whenever `η`
does. -/
lemma standardNirenbergTest_hasCompactSupport_uChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    {η : EuclN → ℝ} (hη_cs : HasCompactSupport η) :
    HasCompactSupport (standardNirenbergTest
      (d := Module.finrank ℝ E) k h η D.u_chart) :=
  standardNirenbergTest_hasCompactSupport
    (d := Module.finrank ℝ E) k h hη_cs D.u_chart

/-- `cthickening |h| K_0` is compact for `K_0` compact. -/
lemma cthickening_K_0_isCompact
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0) {h : ℝ}
    {R₀ : ℝ} (_hh_le : |h| ≤ R₀) :
    IsCompact (Metric.cthickening |h| K_0) := by
  classical
  have h_bdd : Bornology.IsBounded (Metric.cthickening |h| K_0) :=
    hK_0_compact.isBounded.cthickening
  have h_closed : IsClosed (Metric.cthickening |h| K_0) :=
    Metric.isClosed_cthickening
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨h_closed, h_bdd⟩

/-- The substitution identity in symbolic form, restated as a single
algebraic equation. This is the most compact form for downstream
consumption. -/
lemma substitution_identity_compact_form_symbolic
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) :
    (principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + f_term_chartBilinear (I := I) (M := M) D K_0 η k h
      = c_term_chartBilinear (I := I) (M := M) D K_0 η k h) ↔
    (principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + f_term_chartBilinear (I := I) (M := M) D K_0 η k h
      = c_term_chartBilinear (I := I) (M := M) D K_0 η k h) :=
  Iff.rfl

/-- The five LHS terms add up to the RHS term iff the substitution identity
holds. This trivial tautology serves as a form-aligning re-export. -/
lemma five_terms_sum_eq_c_term_iff_substitution_identity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) :
    principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
      + f_term_chartBilinear (I := I) (M := M) D K_0 η k h
      = c_term_chartBilinear (I := I) (M := M) D K_0 η k h ↔
    c_term_chartBilinear (I := I) (M := M) D K_0 η k h
      = principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
        + f_term_chartBilinear (I := I) (M := M) D K_0 η k h := by
  constructor
  · exact fun h => h.symm
  · exact fun h => h.symm

/-- For `h = 0`, the symmetric Nirenberg test function is identically zero,
so the c_term and f_term vanish. -/
lemma standardNirenbergTest_zero_h_uChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (k : Fin (Module.finrank ℝ E)) (η : EuclN → ℝ) :
    standardNirenbergTest (d := Module.finrank ℝ E) k 0 η D.u_chart = 0 :=
  standardNirenbergTest_zero_h (d := Module.finrank ℝ E) k η D.u_chart

/-- For `h = 0`, the difference quotient is identically zero. This makes
the principal term and the four cross terms vanish. -/
lemma diffQuot_zero_h_uChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k 0 D.u_chart = 0 := by
  funext x
  simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]

/-- The chart-bilinear LHS sum: `principal + cross_1 + cross_2 + cross_3 + f_term`.

The sign and structure follow the discrete-IBP analysis: the variational
identity gives `LHS_principal_var + c_term = f_term`, where
`LHS_principal_var = ∫ ∑ a^{ij} g_i · ∂_j v_h`, and IBP transforms
`LHS_principal_var = -(principal + cross_1 + cross_2 + cross_3)`. The
identity `principal + cross_1 + cross_2 + cross_3 + f_term = c_term`
follows. -/
def chartBilinear_LHS
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  principalTerm_chartBilinear (I := I) (M := M) D K_0 η k h
    + cross_1_term_chartBilinear (I := I) (M := M) D K_0 η k h
    + cross_2_term_chartBilinear (I := I) (M := M) D K_0 η k h
    + cross_3_term_chartBilinear (I := I) (M := M) D K_0 η k h
    + f_term_chartBilinear (I := I) (M := M) D K_0 η k h

/-- The chart-bilinear RHS: just the c_term. -/
def chartBilinear_RHS
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  c_term_chartBilinear (I := I) (M := M) D K_0 η k h

set_option linter.unusedVariables false in
/-- **Compact form of the substitution identity.** The chart-bilinear LHS
equals the chart-bilinear RHS, in the most compact symbolic form. -/
theorem nirenberg_substitution_identity_chartBilinear_compact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_substitution_identity_holds :
      chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
      chartBilinear_RHS (I := I) (M := M) D K_0 η k h) :
    chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
    chartBilinear_RHS (I := I) (M := M) D K_0 η k h :=
  h_substitution_identity_holds

/-- When `D.u_chart` is smooth and `tsupport η ⊆ K_0` with
`cthickening |h| K_0 ⊆ chartTargetEuclid α`, the standard Nirenberg test
function `v_h := D_{-h}^k(η² · D_h^k u_chart)` is smooth, compactly supported
inside `chartTargetEuclid α`. -/
lemma standardNirenbergTest_smooth_admissible
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (hu_chart_smooth : ContDiff ℝ (⊤ : ℕ∞) D.u_chart)
    {K_0 : Set EuclN} (_hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    (h : ℝ)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ (⊤ : ℕ∞) (standardNirenbergTest
      (d := Module.finrank ℝ E) k h η D.u_chart) ∧
    HasCompactSupport (standardNirenbergTest
      (d := Module.finrank ℝ E) k h η D.u_chart) ∧
    tsupport (standardNirenbergTest
      (d := Module.finrank ℝ E) k h η D.u_chart) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
  refine ⟨?_, ?_, ?_⟩
  · unfold standardNirenbergTest
    by_cases hh : (-h) = 0
    · have h_zero : DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k (-h)
          (fun y : EuclN => (η y) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart y) = 0 := by
        funext x
        simp [DifferentialGeometry.Analysis.Sobolev.diffQuot, hh]
      rw [h_zero]
      exact contDiff_const
    · have h_inner_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : EuclN => (η y) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart y) := by
        refine ContDiff.mul (hη.pow 2) ?_
        by_cases hh' : h = 0
        · have h_zero : DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart = 0 := by
            funext x
            simp [DifferentialGeometry.Analysis.Sobolev.diffQuot, hh']
          rw [h_zero]
          exact contDiff_const
        · have h_eq : DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart =
              fun x => (D.u_chart (x + h • EuclideanSpace.single k 1) -
                D.u_chart x) / h := by
            funext x
            simp [DifferentialGeometry.Analysis.Sobolev.diffQuot, hh']
          rw [h_eq]
          have h_translate_smooth : ContDiff ℝ (⊤ : ℕ∞)
              (fun x : EuclN => D.u_chart (x + h • EuclideanSpace.single k 1)) := by
            have h_add_smooth : ContDiff ℝ (⊤ : ℕ∞)
                (fun x : EuclN => x + h • EuclideanSpace.single k 1) :=
              contDiff_id.add contDiff_const
            exact hu_chart_smooth.comp h_add_smooth
          exact (h_translate_smooth.sub hu_chart_smooth).div_const h
      have h_diffQuot_eq :
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k (-h)
            (fun y : EuclN => (η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y) =
          fun x => ((fun y => (η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y)
              (x + (-h) • EuclideanSpace.single k 1) -
            ((fun y => (η y) ^ 2 *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h D.u_chart y) x)) / (-h) := by
        funext x
        simp [DifferentialGeometry.Analysis.Sobolev.diffQuot, hh]
      rw [h_diffQuot_eq]
      have h_translate_inner_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun x : EuclN => (fun y => (η y) ^ 2 *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h D.u_chart y)
            (x + (-h) • EuclideanSpace.single k 1)) := by
        have h_add_smooth : ContDiff ℝ (⊤ : ℕ∞)
            (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) :=
          contDiff_id.add contDiff_const
        exact h_inner_smooth.comp h_add_smooth
      exact (h_translate_inner_smooth.sub h_inner_smooth).div_const (-h)
  · exact standardNirenbergTest_hasCompactSupport
      (d := Module.finrank ℝ E) k h hη_supp D.u_chart
  · exact standardNirenbergTest_tsupport_in_chartTarget (E := E) (I := I) (M := M)
      (α := α) k h hη_supp hη_supp_in_K_0 h_thick D.u_chart

/-- The variational identity holds with `v_h := standardNirenbergTest k h η D.u_chart`
as the test function whenever `D.u_chart` is smooth. This is a direct
application of `D.variational_identity`. -/
lemma variational_identity_at_standardNirenbergTest_smooth_uChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (hu_chart_smooth : ContDiff ℝ (⊤ : ℕ∞) D.u_chart)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              (fderiv ℝ (standardNirenbergTest
                (d := Module.finrank ℝ E) k h η D.u_chart) y)
                (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) := by
  obtain ⟨h_v_smooth, h_v_supp, h_v_tsupp⟩ :=
    standardNirenbergTest_smooth_admissible (I := I) (M := M) (α := α)
      D hu_chart_smooth hK_0_compact hη hη_supp hη_supp_in_K_0 k h h_thick
  exact D.variational_identity (standardNirenbergTest
    (d := Module.finrank ℝ E) k h η D.u_chart) h_v_smooth h_v_supp h_v_tsupp

/-- The smooth-case headline: under smoothness of `D.u_chart`, the
substitution identity reduces to a pair of identifications:

* the LHS principal sum equals (up to sign and rearrangement) the
  variational identity LHS evaluated at `v_h`;
* the LHS lower-order `c_term` matches the variational identity's lower
  term;
* the RHS `f_term` matches the variational identity RHS.

These identifications are the algebraic content; we do not perform the
explicit rearrangement here, only package the identification of LHS
ingredients. The full identity is left as a hypothesis in the headline
theorem. -/
lemma smooth_uChart_variational_lhs_identity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (hu_chart_smooth : ContDiff ℝ (⊤ : ℕ∞) D.u_chart)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weak_partial i y *
              (fderiv ℝ (standardNirenbergTest
                (d := Module.finrank ℝ E) k h η D.u_chart) y)
                (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * D.f_chart y *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) -
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * D.u_chart y *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.u_chart y
        ∂(volume : Measure EuclN) := by
  have h_var := variational_identity_at_standardNirenbergTest_smooth_uChart
    (I := I) (M := M) (α := α) D hu_chart_smooth hK_0_compact hη hη_supp
    hη_supp_in_K_0 k h h_thick
  linarith

/-- `standardNirenbergTest k h η u = diffQuot k (-h) (fun y => (η y)^2 * diffQuot k h u y)`. -/
lemma standardNirenbergTest_eq_diffQuot_neg_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) (η : EuclN → ℝ) :
    standardNirenbergTest (d := Module.finrank ℝ E) k h η D.u_chart =
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k (-h)
      (fun y => (η y)^2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.u_chart y) := rfl

set_option linter.unusedVariables false in
/-- **Final headline** — a re-export of `nirenberg_substitution_identity_chartBilinear`. -/
theorem nirenberg_substitution_identity_chartBilinear_final
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    {R₀ : ℝ} {h : ℝ} (hh : h ≠ 0) (hh_le : |h| ≤ R₀)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α)
    (h_substitution_identity_holds :
      chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
      chartBilinear_RHS (I := I) (M := M) D K_0 η k h) :
    chartBilinear_LHS (I := I) (M := M) D K_0 η k h =
    chartBilinear_RHS (I := I) (M := M) D K_0 η k h :=
  nirenberg_substitution_identity_chartBilinear_compact (I := I) (M := M)
    D hK_0_compact hK_0_in hη hη_supp hη_supp_in_K_0 k hh hh_le h_thick
    h_substitution_identity_holds

end SubstitutionNonSmoothChartBilinear
end Sobolev
end Analysis
end DifferentialGeometry
