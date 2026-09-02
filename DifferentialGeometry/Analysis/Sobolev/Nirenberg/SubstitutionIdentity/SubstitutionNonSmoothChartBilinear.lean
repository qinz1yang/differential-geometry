import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartBilinear.H1Compl_H1_0
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.WeakRegularity
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmooth


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionNonSmoothChartBilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
open DifferentialGeometry.Analysis.Sobolev.NirenbergTranslatedCutoffDiffQuot

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma standardNirenbergTest_tsupport_in_thickening
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) {η : EuclN → ℝ}
    {K_0 : Set EuclN} (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (u : EuclN → ℝ) :
    tsupport (standardNirenbergTest k h η u) ⊆
      Metric.cthickening |h| K_0 := by
  classical
  have h_supp := standardNirenbergTest_tsupport_subset
    (d := Module.finrank ℝ E) (η := η) k h u
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

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma standardNirenbergTest_tsupport_in_chartTarget
    {α : M}
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) {η : EuclN → ℝ}
    {K_0 : Set EuclN} (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α)
    (u : EuclN → ℝ) :
    tsupport (standardNirenbergTest k h η u) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (standardNirenbergTest_tsupport_in_thickening (E := E) k h hη_supp_in_K_0
      u).trans h_thick

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramOnEuclid_bounded_on_compact
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

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_bounded_above_on_compact
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma cthickening_compact_of_compact
    {h : ℝ} {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0) :
    IsCompact (Metric.cthickening |h| K_0) := by
  classical
  have h_bdd : Bornology.IsBounded (Metric.cthickening |h| K_0) :=
    hK_0_compact.isBounded.cthickening
  have h_closed : IsClosed (Metric.cthickening |h| K_0) :=
    Metric.isClosed_cthickening
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨h_closed, h_bdd⟩

omit [NeZero (Module.finrank ℝ E)] in
lemma uChart_memLp_volume_restrict_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.uChart 2 ((volume : Measure EuclN).restrict K_0) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    (D.u_chart_memLp_weighted) hK_0_compact
    hK_0_compact.isClosed.measurableSet hK_0_in

omit [NeZero (Module.finrank ℝ E)] in
lemma fChart_memLp_volume_restrict_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp D.fChart 2 ((volume : Measure EuclN).restrict K_0) :=
  memLp_volume_restrict_of_memLp_chartPulledWeightedMeasure (I := I) (M := M)
    (D.f_chart_memLp_weighted) hK_0_compact
    hK_0_compact.isClosed.measurableSet hK_0_in

omit [NeZero (Module.finrank ℝ E)] in
lemma weakPartial_memLp_volume_restrict_compact
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (D.weakPartial i) 2 ((volume : Measure EuclN).restrict K) :=
  D.weak_partial_locally_memLp i K hK_compact hK_in

omit [NeZero (Module.finrank ℝ E)] in
lemma weakPartial_memLp_volume_restrict_cthickening
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (D.weakPartial i) 2
      ((volume : Measure EuclN).restrict (Metric.cthickening |h| K_0)) :=
  D.weak_partial_locally_memLp i (Metric.cthickening |h| K_0)
    (cthickening_compact_of_compact (E := E) hK_0_compact) h_thick

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramOnEuclid_bounded_on_cthickening
    {g : SmoothRiemannianMetric I M} (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.cthickening |h| K_0,
        |weightedInvGramOnEuclid (I := I) g α i j y| ≤ C :=
  weightedInvGramOnEuclid_bounded_on_compact (I := I) (M := M) g α i j
    (cthickening_compact_of_compact (E := E) hK_0_compact) h_thick

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_bounded_above_on_cthickening
    {g : SmoothRiemannianMetric I M} (α : M)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.cthickening |h| K_0, densityOnEuclid (I := I) g α y ≤ C :=
  densityOnEuclid_bounded_above_on_compact (I := I) (M := M) g α
    (cthickening_compact_of_compact (E := E) hK_0_compact) h_thick

omit [NeZero (Module.finrank ℝ E)] in
lemma translate_weightedInvGramOnEuclid_bounded_on_K_0
    {g : SmoothRiemannianMetric I M} (α : M)
    (i j k : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    {h : ℝ}
    (h_thick :
      Metric.cthickening |h| K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K_0,
      |DifferentialGeometry.Analysis.Sobolev.translate
        (d := Module.finrank ℝ E) k h
        (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x| ≤ C := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    weightedInvGramOnEuclid_bounded_on_cthickening (I := I) (M := M) α i j
      hK_0_compact h_thick
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

def principalTermChartBilinear
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
          (d := Module.finrank ℝ E) k h (D.weakPartial i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) x
    ∂(volume : Measure EuclN)

def cross1TermChartBilinear
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
            (d := Module.finrank ℝ E) k h (D.weakPartial i) x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart x
        ∂(volume : Measure EuclN)

def cross2TermChartBilinear
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
        D.weakPartial i x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) x
      ∂(volume : Measure EuclN)

def cross3TermChartBilinear
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
          D.weakPartial i x *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart x
        ∂(volume : Measure EuclN)

def cTermChartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∫ x in Metric.cthickening |h| K_0,
    densityOnEuclid (I := I) g α x * D.uChart x *
      standardNirenbergTest
        (d := Module.finrank ℝ E) k h η D.uChart x
  ∂(volume : Measure EuclN)

def fTermChartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∫ x in Metric.cthickening |h| K_0,
    densityOnEuclid (I := I) g α x * D.fChart x *
      standardNirenbergTest
        (d := Module.finrank ℝ E) k h η D.uChart x
  ∂(volume : Measure EuclN)

omit [NeZero (Module.finrank ℝ E)] in
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
              (d := Module.finrank ℝ E) k h (D.weakPartial i) x *
            DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weakPartial j) x
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
                  (d := Module.finrank ℝ E) k h (D.weakPartial i) x *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart x
              ∂(volume : Measure EuclN))
      + (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∫ x in K_0,
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h
                (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
              (η x) ^ 2 *
              D.weakPartial i x *
              DifferentialGeometry.Analysis.Sobolev.diffQuot
                (d := Module.finrank ℝ E) k h (D.weakPartial j) x
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
                D.weakPartial i x *
                DifferentialGeometry.Analysis.Sobolev.diffQuot
                  (d := Module.finrank ℝ E) k h D.uChart x
              ∂(volume : Measure EuclN))
      + (∫ x in Metric.cthickening |h| K_0,
            densityOnEuclid (I := I) g α x * D.fChart x *
              standardNirenbergTest
                (d := Module.finrank ℝ E) k h η D.uChart x
          ∂(volume : Measure EuclN))) =
    (principalTermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
      + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h
      + fTermChartBilinear (I := I) (M := M) D K_0 η k h) := by
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma substitution_identity_RHS_explicit_eq_symbolic
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) :
    (∫ x in Metric.cthickening |h| K_0,
        densityOnEuclid (I := I) g α x * D.uChart x *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.uChart x
      ∂(volume : Measure EuclN)) =
    cTermChartBilinear (I := I) (M := M) D K_0 η k h := by
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma K_0_measurableSet
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0) :
    MeasurableSet K_0 :=
  hK_0_compact.isClosed.measurableSet

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma cthickening_measurableSet
    {h : ℝ} {K_0 : Set EuclN} :
    MeasurableSet (Metric.cthickening |h| K_0) :=
  Metric.isClosed_cthickening.measurableSet

omit [NeZero (Module.finrank ℝ E)] in
lemma weakPartial_aestronglyMeasurable_restrict
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (i : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable (D.weakPartial i)
      ((volume : Measure EuclN).restrict K) :=
  (weakPartial_memLp_volume_restrict_compact (I := I) (M := M) D i
    hK_compact hK_in).aestronglyMeasurable

omit [NeZero (Module.finrank ℝ E)] in
lemma uChart_aestronglyMeasurable_restrict_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable D.uChart ((volume : Measure EuclN).restrict K_0) :=
  (uChart_memLp_volume_restrict_K_0 (I := I) (M := M) D
    hK_0_compact hK_0_in).aestronglyMeasurable

omit [NeZero (Module.finrank ℝ E)] in
lemma fChart_aestronglyMeasurable_restrict_K_0
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable D.fChart ((volume : Measure EuclN).restrict K_0) :=
  (fChart_memLp_volume_restrict_K_0 (I := I) (M := M) D
    hK_0_compact hK_0_in).aestronglyMeasurable

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_continuousOn_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityOnEuclid_contDiffOn (I := I) g α).continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramOnEuclid_continuousOn_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_continuousOn_K_0
    (g : SmoothRiemannianMetric I M) (α : M)
    {K_0 : Set EuclN} (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContinuousOn (densityOnEuclid (I := I) g α) K_0 :=
  (densityOnEuclid_continuousOn_chartTarget (I := I) g α).mono hK_0_in

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramOnEuclid_continuousOn_K_0
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) K_0 :=
  (weightedInvGramOnEuclid_continuousOn_chartTarget (I := I) g α i j).mono hK_0_in

omit [NeZero (Module.finrank ℝ E)] in
lemma densityOnEuclid_aestronglyMeasurable_K_0
    (g : SmoothRiemannianMetric I M) (α : M)
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable (densityOnEuclid (I := I) g α)
      ((volume : Measure EuclN).restrict K_0) :=
  (densityOnEuclid_continuousOn_K_0 (I := I) g α hK_0_in).aestronglyMeasurable
    (K_0_measurableSet (E := E) hK_0_compact)

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramOnEuclid_aestronglyMeasurable_K_0
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0)
    (hK_0_in : K_0 ⊆ chartTargetEuclid (I := I) (M := M) α) :
    AEStronglyMeasurable (weightedInvGramOnEuclid (I := I) g α i j)
      ((volume : Measure EuclN).restrict K_0) :=
  (weightedInvGramOnEuclid_continuousOn_K_0 (I := I) g α i j hK_0_in).aestronglyMeasurable
    (K_0_measurableSet (E := E) hK_0_compact)

omit [NeZero (Module.finrank ℝ E)] in
lemma standardNirenbergTest_hasCompactSupport_uChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    {η : EuclN → ℝ} (hη_cs : HasCompactSupport η) :
    HasCompactSupport (standardNirenbergTest
      (d := Module.finrank ℝ E) k h η D.uChart) :=
  standardNirenbergTest_hasCompactSupport
    (d := Module.finrank ℝ E) k h hη_cs D.uChart

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma cthickening_K_0_isCompact
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0) {h : ℝ} :
    IsCompact (Metric.cthickening |h| K_0) := by
  classical
  have h_bdd : Bornology.IsBounded (Metric.cthickening |h| K_0) :=
    hK_0_compact.isBounded.cthickening
  have h_closed : IsClosed (Metric.cthickening |h| K_0) :=
    Metric.isClosed_cthickening
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨h_closed, h_bdd⟩


omit [NeZero (Module.finrank ℝ E)] in
lemma standardNirenbergTest_zero_h_uChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (k : Fin (Module.finrank ℝ E)) (η : EuclN → ℝ) :
    standardNirenbergTest (d := Module.finrank ℝ E) k 0 η D.uChart = 0 :=
  standardNirenbergTest_zero_h (d := Module.finrank ℝ E) k η D.uChart

omit [NeZero (Module.finrank ℝ E)] in
lemma diffQuot_zero_h_uChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (k : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k 0 D.uChart = 0 := by
  funext x
  simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]

def chartBilinearLHS
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  principalTermChartBilinear (I := I) (M := M) D K_0 η k h
    + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
    + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
    + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h
    + fTermChartBilinear (I := I) (M := M) D K_0 η k h

def chartBilinearRHS
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  cTermChartBilinear (I := I) (M := M) D K_0 η k h

omit [NeZero (Module.finrank ℝ E)] in
lemma standardNirenbergTest_smooth_admissible
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (hu_chart_smooth : ContDiff ℝ (⊤ : ℕ∞) D.uChart)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E))
    (h : ℝ)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ContDiff ℝ (⊤ : ℕ∞) (standardNirenbergTest
      (d := Module.finrank ℝ E) k h η D.uChart) ∧
    HasCompactSupport (standardNirenbergTest
      (d := Module.finrank ℝ E) k h η D.uChart) ∧
    tsupport (standardNirenbergTest
      (d := Module.finrank ℝ E) k h η D.uChart) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
  refine ⟨?_, ?_, ?_⟩
  · by_cases hh : h = 0
    · subst h
      rw [standardNirenbergTest_zero_h]
      exact contDiff_const
    · exact NirenbergTestFunction.contDiff_nirenbergTestFunction
        (d := Module.finrank ℝ E) hη hu_chart_smooth k hh
  · exact standardNirenbergTest_hasCompactSupport
      (d := Module.finrank ℝ E) k h hη_supp D.uChart
  · exact standardNirenbergTest_tsupport_in_chartTarget (E := E) (I := I) (M := M)
      (α := α) k h hη_supp_in_K_0 h_thick D.uChart

omit [NeZero (Module.finrank ℝ E)] in
lemma variational_identity_at_standardNirenbergTest_smooth_uChart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (hu_chart_smooth : ContDiff ℝ (⊤ : ℕ∞) D.uChart)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              (fderiv ℝ (standardNirenbergTest
                (d := Module.finrank ℝ E) k h η D.uChart) y)
                (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * D.uChart y *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * D.fChart y *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN) := by
  obtain ⟨h_v_smooth, h_v_supp, h_v_tsupp⟩ :=
    standardNirenbergTest_smooth_admissible (I := I) (M := M) (α := α)
      D hu_chart_smooth hη hη_supp hη_supp_in_K_0 k h h_thick
  exact D.variational_identity (standardNirenbergTest
    (d := Module.finrank ℝ E) k h η D.uChart) h_v_smooth h_v_supp h_v_tsupp

omit [NeZero (Module.finrank ℝ E)] in
lemma smooth_uChart_variational_lhs_identity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (hu_chart_smooth : ContDiff ℝ (⊤ : ℕ∞) D.uChart)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_supp_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ)
    (h_thick : Metric.cthickening |h| K_0 ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              D.weakPartial i y *
              (fderiv ℝ (standardNirenbergTest
                (d := Module.finrank ℝ E) k h η D.uChart) y)
                (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) =
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * D.fChart y *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN) -
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * D.uChart y *
          standardNirenbergTest
            (d := Module.finrank ℝ E) k h η D.uChart y
        ∂(volume : Measure EuclN) := by
  have h_var := variational_identity_at_standardNirenbergTest_smooth_uChart
    (I := I) (M := M) (α := α) D hu_chart_smooth hη hη_supp
    hη_supp_in_K_0 k h h_thick
  linarith

omit [NeZero (Module.finrank ℝ E)] in
lemma standardNirenbergTest_eq_diffQuot_neg_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) (η : EuclN → ℝ) :
    standardNirenbergTest (d := Module.finrank ℝ E) k h η D.uChart =
    DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k (-h)
      (fun y => (η y)^2 * DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k h D.uChart y) := rfl



end SubstitutionNonSmoothChartBilinear
end Sobolev
end Analysis
end DifferentialGeometry
