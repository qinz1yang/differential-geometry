import DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionIBPExpand
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.ChartBilinearDischarge.SubstitutionChartBilinear


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace SubstitutionChartBilinearTrivialCases

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
open DifferentialGeometry.Analysis.Sobolev.NirenbergTranslatedCutoffDiffQuot
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeSmoothApprox
open DifferentialGeometry.Analysis.Sobolev.SubstitutionDischargeIBPExpand
open DifferentialGeometry.Analysis.Sobolev.SubstitutionNonSmoothChartBilinear

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
private lemma principalTerm_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    principalTermChartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold principalTermChartBilinear
  have h_eq : (fun x : EuclN =>
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k 0
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 (D.weakPartial i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 (D.weakPartial j) x)) =
      (fun _ => (0 : ℝ)) := by
    funext x
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have h_dq : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0 (D.weakPartial i) x = 0 := by
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma cross_1_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    cross1TermChartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold cross1TermChartBilinear
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h_eq : (fun x : EuclN =>
      2 *
        DifferentialGeometry.Analysis.Sobolev.translate
          (d := Module.finrank ℝ E) k 0
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 (D.weakPartial i) x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 D.uChart x) = (fun _ => (0 : ℝ)) := by
    funext x
    have h_dq : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0 (D.weakPartial i) x = 0 := by
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma cross_2_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    cross2TermChartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold cross2TermChartBilinear
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h_eq : (fun x : EuclN =>
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0
        (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
      (η x) ^ 2 *
      D.weakPartial i x *
      DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0 (D.weakPartial j) x) =
      (fun _ => (0 : ℝ)) := by
    funext x
    have h_dq : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0
        (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x = 0 := by
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma cross_3_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    cross3TermChartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold cross3TermChartBilinear
  refine Finset.sum_eq_zero (fun i _ => ?_)
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h_eq : (fun x : EuclN =>
      2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        D.weakPartial i x *
        DifferentialGeometry.Analysis.Sobolev.diffQuot
          (d := Module.finrank ℝ E) k 0 D.uChart x) = (fun _ => (0 : ℝ)) := by
    funext x
    have h_dq : DifferentialGeometry.Analysis.Sobolev.diffQuot
        (d := Module.finrank ℝ E) k 0 D.uChart x = 0 := by
      simp [DifferentialGeometry.Analysis.Sobolev.diffQuot]
    rw [h_dq]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma c_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    cTermChartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold cTermChartBilinear
  have h_eq : (fun x : EuclN =>
      densityOnEuclid (I := I) g α x * D.uChart x *
        nirenbergTestFunction
          (d := Module.finrank ℝ E) k 0 η D.uChart x) = (fun _ => (0 : ℝ)) := by
    funext x
    have h_test : nirenbergTestFunction
        (d := Module.finrank ℝ E) k 0 η D.uChart x = 0 := by
      have := nirenbergTestFunction_zero_h
        (d := Module.finrank ℝ E) k η D.uChart
      exact congrArg (fun f : EuclN → ℝ => f x) this
    rw [h_test]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma f_term_chartBilinear_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    fTermChartBilinear (I := I) (M := M) D K_0 η k 0 = 0 := by
  unfold fTermChartBilinear
  have h_eq : (fun x : EuclN =>
      densityOnEuclid (I := I) g α x * D.fChart x *
        nirenbergTestFunction
          (d := Module.finrank ℝ E) k 0 η D.uChart x) = (fun _ => (0 : ℝ)) := by
    funext x
    have h_test : nirenbergTestFunction
        (d := Module.finrank ℝ E) k 0 η D.uChart x = 0 := by
      have := nirenbergTestFunction_zero_h
        (d := Module.finrank ℝ E) k η D.uChart
      exact congrArg (fun f : EuclN → ℝ => f x) this
    rw [h_test]; ring
  rw [h_eq]
  simp

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartBilinear_substitution_identity_zero_h
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    chartBilinearLHS (I := I) (M := M) D K_0 η k 0 =
    chartBilinearRHS (I := I) (M := M) D K_0 η k 0 := by
  unfold chartBilinearLHS chartBilinearRHS
  rw [principalTerm_chartBilinear_zero_h, cross_1_term_chartBilinear_zero_h,
    cross_2_term_chartBilinear_zero_h, cross_3_term_chartBilinear_zero_h,
    f_term_chartBilinear_zero_h, c_term_chartBilinear_zero_h]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartBilinear_substitution_identity_K_0_empty
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN} (hK_0_empty : K_0 = ∅)
    (η : EuclN → ℝ)
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) :
    chartBilinearLHS (I := I) (M := M) D K_0 η k h =
    chartBilinearRHS (I := I) (M := M) D K_0 η k h := by
  classical
  have hη_zero : η = 0 := by
    have h_support_empty : tsupport η = ∅ := by
      rw [hK_0_empty] at hη_support_in_K_0
      exact Set.subset_empty_iff.mp hη_support_in_K_0
    funext x
    by_contra hηx
    have hx_in_support : x ∈ tsupport η := subset_tsupport η hηx
    rw [h_support_empty] at hx_in_support
    exact hx_in_support
  have h_test_zero : nirenbergTestFunction
      (d := Module.finrank ℝ E) k h η D.uChart = 0 := by
    rw [hη_zero]
    funext x
    change DifferentialGeometry.Analysis.Sobolev.diffQuot
      (d := Module.finrank ℝ E) k (-h)
        (fun y : EuclN => (0 : ℝ) ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart y) x = 0
    have h_inner :
        (fun y : EuclN => (0 : ℝ) ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart y) = 0 := by
      funext y
      simp
    rw [h_inner, DifferentialGeometry.Analysis.Sobolev.diffQuot_zero]
    rfl
  unfold chartBilinearLHS chartBilinearRHS
  unfold principalTermChartBilinear cross1TermChartBilinear
    cross2TermChartBilinear cross3TermChartBilinear
    cTermChartBilinear fTermChartBilinear
  rw [hK_0_empty]
  simp only [Measure.restrict_empty, integral_zero_measure, Finset.sum_const,
    Finset.card_univ, smul_zero, zero_add]
  have h_cthick_empty : Metric.cthickening |h| (∅ : Set EuclN) = ∅ :=
    Metric.cthickening_empty |h|
  rw [h_cthick_empty]
  simp [Measure.restrict_empty, integral_zero_measure]


omit [NeZero (Module.finrank ℝ E)] in
theorem chart_bilinear_substitution_identity_of_nonzero_nonempty
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    {K_0 : Set EuclN}
    {η : EuclN → ℝ}
    (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (k : Fin (Module.finrank ℝ E)) {h : ℝ}
    (h_substitution_identity_holds :
      h ≠ 0 → K_0 ≠ ∅ →
      chartBilinearLHS (I := I) (M := M) D K_0 η k h =
      chartBilinearRHS (I := I) (M := M) D K_0 η k h) :
    chartBilinearLHS (I := I) (M := M) D K_0 η k h =
    chartBilinearRHS (I := I) (M := M) D K_0 η k h := by
  classical
  by_cases hh : h = 0
  · rw [hh]
    exact chartBilinear_substitution_identity_zero_h (I := I) (M := M)
      D K_0 η k
  · by_cases hK_0_empty : K_0 = ∅
    · exact chartBilinear_substitution_identity_K_0_empty (I := I) (M := M)
        D hK_0_empty η hη_support_in_K_0 k h
    · exact h_substitution_identity_holds hh hK_0_empty



end SubstitutionChartBilinearTrivialCases
end Sobolev
end Analysis
end DifferentialGeometry
