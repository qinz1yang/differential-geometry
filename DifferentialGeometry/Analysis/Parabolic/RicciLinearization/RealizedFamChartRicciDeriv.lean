import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization
import DifferentialGeometry.Analysis.Calculus.TimeJetCommute

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator


noncomputable section


open Set Function MeasureTheory Bundle
open scoped Topology Manifold BigOperators ContDiff

namespace DifferentialGeometry
namespace PDE
namespace DeTurck
namespace RicciLinearization

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma hasDerivAt_of_shift {f : ℝ → ℝ} {f' s₀ : ℝ}
    (hshift : HasDerivAt (fun u => f (s₀ + u)) f' 0) : HasDerivAt f f' s₀ := by
  have hz : (s₀ : ℝ) - s₀ = 0 := by ring
  have hshift' : HasDerivAt (fun u => f (s₀ + u)) f' (s₀ - s₀) := by rw [hz]; exact hshift
  have hcomp := HasDerivAt.comp_sub_const s₀ s₀ hshift'
  have heq : (fun s : ℝ => f (s₀ + (s - s₀))) = f := by funext s; congr 1; ring
  rwa [heq] at hcomp

omit [NeZero (Module.finrank ℝ E)] in
private lemma hasDerivAt_partialDeriv_comm_at
    (Φ : ℝ × E → ℝ) (p : Fin (Module.finrank ℝ E)) (s₀ : ℝ) (y₀ : E)
    (hΦ : ContDiffAt ℝ ∞ Φ (s₀, y₀)) :
    HasDerivAt
      (fun s => partialDeriv (E := E) p (fun y => Φ (s, y)) y₀)
      (partialDeriv (E := E) p (fun y => deriv (fun s => Φ (s, y)) s₀) y₀) s₀ := by
  unfold partialDeriv
  exact DifferentialGeometry.Analysis.fderiv_deriv_hasDerivAt_comm Φ s₀ y₀
    (chartModelBasis E p) hΦ

def realizedGramDeriv (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) α i j y -
      chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α i j y

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_chartGramOnE (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) (y : E) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt (fun s : ℝ => chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) α i j y)
      (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' α i j y) s₀ := by
  set F : ℝ :=
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T' hδ'_lt hδ') α i j y with hF
  set G : ℝ :=
    chartGramOnE (I := I) (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ) α i j y with hG
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  have heq : (fun s : ℝ => chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) α i j y)
      =ᶠ[nhds s₀] (fun s : ℝ => (1 - s) * F + s * G) := by
    filter_upwards [hSopen.mem_nhds hs₀] with s hs
    rw [hF, hG]
    exact realizedFam_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' hs α i j y
  have h1 : HasDerivAt (fun s : ℝ => (1 - s) * F) (-F) s₀ := by
    have := ((hasDerivAt_const s₀ (1 : ℝ)).sub (hasDerivAt_id s₀)).mul_const F
    simpa using this
  have h2 : HasDerivAt (fun s : ℝ => s * G) G s₀ := by
    simpa using (hasDerivAt_id s₀).mul_const G
  have hbase : HasDerivAt (fun s : ℝ => (1 - s) * F + s * G) (G - F) s₀ := by
    have := h1.add h2; convert this using 1; ring
  refine (hbase.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [realizedGramDeriv, hF, hG]

omit [CompactSpace M] in
private lemma realizedGramDeriv_eq_deriv (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (α : M) (i j : Fin (Module.finrank ℝ E)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    (fun y => deriv (fun s : ℝ =>
        chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) α i j y) s₀) =
      realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' α i j := by
  funext y
  exact (hasDerivAt_realizedFam_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' α i j y hs₀).deriv

omit [CompactSpace M] in
private lemma s_differentiableAt_realizedFam_chartInvGramOnE (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    DifferentiableAt ℝ
      (fun s : ℝ => chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k l y)
        s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hjoint := chartInvGramOnE_contDiffAt_joint (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') x
    hG k l hs₀ hy
  have hcomp : (fun s : ℝ => chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k l
    y)
      = (fun p : ℝ × E => chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' p.1) x k l
        p.2)
        ∘ (fun s : ℝ => (s, y)) := by funext s; rfl
  rw [hcomp]
  exact (hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)).differentiableAt (by simp)

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_chartInvGramOnE (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt (fun s : ℝ => chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k l
      y)
      (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k p y *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
            chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q l y)) s₀ := by
  classical
  set gs : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s₀ with hgs
  have hSopen : IsOpen (realizedSmallSet (δ := δ) (δ' := δ')) := realizedSmallSet_isOpen
  have hsub : (fun s : ℝ => chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k l
    y)
      =ᶠ[nhds s₀] (fun s : ℝ => chartInvGramOnE (I := I) gs x k l y +
        (∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k p y *
            (chartGramOnE (I := I) gs x p q y -
              chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x p q y) *
            chartInvGramOnE (I := I) gs x q l y)) := by
    filter_upwards [hSopen.mem_nhds hs₀] with s _
    have := invGramOnE_sub_eq (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) gs x k l hy
    linarith [this]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hsub
  have hconst : HasDerivAt (fun _ : ℝ => chartInvGramOnE (I := I) gs x k l y) 0 s₀ :=
    hasDerivAt_const s₀ _
  have hgram : ∀ p q : Fin (Module.finrank ℝ E),
      HasDerivAt
        (fun s : ℝ => chartGramOnE (I := I) gs x p q y -
          chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x p q y)
        (-(realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y)) s₀ := by
    intro p q
    have hconstg : HasDerivAt (fun _ : ℝ => chartGramOnE (I := I) gs x p q y) 0 s₀ :=
      hasDerivAt_const s₀ _
    have hg := hasDerivAt_realizedFam_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y hs₀
    simpa using hconstg.sub hg
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k p y *
            (chartGramOnE (I := I) gs x p q y -
              chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x p q y) *
            chartInvGramOnE (I := I) gs x q l y)
      (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) gs x k p y *
            realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
            chartInvGramOnE (I := I) gs x q l y)) s₀ := by
    rw [show (-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) gs x k p y *
              realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
              chartInvGramOnE (I := I) gs x q l y)) =
          (∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) gs x k p y *
              (-(realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y)) *
              chartInvGramOnE (I := I) gs x q l y) from by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      ring]
    refine HasDerivAt.fun_sum (fun q _ => ?_)
    refine HasDerivAt.fun_sum (fun p _ => ?_)
    have hA_diff : DifferentiableAt ℝ
        (fun s : ℝ => chartInvGramOnE (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) x k p y) s₀ :=
      s_differentiableAt_realizedFam_chartInvGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x k p hy
        hs₀
    have hAB : HasDerivAt (fun s : ℝ =>
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k p y *
            (chartGramOnE (I := I) gs x p q y -
              chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x p q y))
        (chartInvGramOnE (I := I) gs x k p y *
          (-(realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y))) s₀ := by
      have hmul := hA_diff.hasDerivAt.mul (hgram p q)
      refine hmul.congr_deriv ?_
      simp only [hgs, sub_self, mul_zero, zero_add, mul_neg]
    have hABC := hAB.mul_const (chartInvGramOnE (I := I) gs x q l y)
    refine hABC.congr_deriv ?_
    ring
  have hfinal := hconst.add hsum
  rw [zero_add] at hfinal
  exact hfinal

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_partial_chartGramOnE (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j p : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ => partialDeriv (E := E) p
        (chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j) y)
      (partialDeriv (E := E) p
        (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) y) s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hjoint : ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) x i j r.2)
      (s₀, y) := hG.1 i j hs₀ hy
  have hcomm := hasDerivAt_partialDeriv_comm_at
    (fun r : ℝ × E => chartGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) x i j r.2)
    p s₀ y hjoint
  refine hcomm.congr_deriv ?_
  congr 1
  exact realizedGramDeriv_eq_deriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j hs₀

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_gramBracket (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt (fun s : ℝ => gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j l y)
      (partialDeriv (E := E) i (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j) y +
        partialDeriv (E := E) j (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i) y -
        partialDeriv (E := E) l
          (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) y) s₀ := by
  have h1 := hasDerivAt_realizedFam_partial_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j
    i
    hy hs₀
  have h2 := hasDerivAt_realizedFam_partial_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i
    j
    hy hs₀
  have h3 := hasDerivAt_realizedFam_partial_chartGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j
    l
    hy hs₀
  have hsum := (h1.add h2).sub h3
  have heq : (fun s : ℝ => gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j l y) =
      (fun s : ℝ =>
        partialDeriv (E := E) i (chartGramOnE (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) x l j) y +
          partialDeriv (E := E) j (chartGramOnE (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) x l i) y -
          partialDeriv (E := E) l (chartGramOnE (I := I)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j) y) := by
    funext s; rw [gramBracket]
  rw [heq]; exact hsum

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_chartChristoffel (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt (fun s : ℝ => chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j
      k y)
      ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        ((-(∑ q : Fin (Module.finrank ℝ E), ∑ p : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k p y *
                realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x p q y *
                chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x q l y)) *
            gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x i j l y +
          chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s₀) x k l y *
            (partialDeriv (E := E) i
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l j) y +
              partialDeriv (E := E) j
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x l i) y -
              partialDeriv (E := E) l
                (realizedGramDeriv (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j) y))) s₀ := by
  classical
  have heq : (fun s : ℝ =>
        chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k y) =
      (fun s : ℝ => (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x k l y *
          gramBracket (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j l y) := by
    funext s; rw [chartChristoffel_eq_sum_invGramOnE_bracket]
  rw [heq]
  refine HasDerivAt.const_mul (1 / 2 : ℝ) ?_
  refine HasDerivAt.fun_sum (fun l _ => ?_)
  have hG := hasDerivAt_realizedFam_chartInvGramOnE (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x k l hy
    hs₀
  have hbr := hasDerivAt_realizedFam_gramBracket (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j l hy hs₀
  exact hG.mul hbr

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_partial_chartChristoffel (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (m i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ => partialDeriv (E := E) m
        (fun y' => chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k y') y)
      (partialDeriv (E := E) m
        (fun y' => deriv (fun s : ℝ =>
          chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k y') s₀) y)
            s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hjoint : ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) x i j k r.2) (s₀, y) :=
    gen_joint_christoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') x hG i j k hs₀ hy
  exact hasDerivAt_partialDeriv_comm_at
    (fun r : ℝ × E =>
      chartChristoffel (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) x i j k r.2) m s₀ y hjoint

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_chartRiemannTensor (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i j k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ => chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k l y)
      (deriv (fun s : ℝ =>
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k l y) s₀)
          s₀ := by
  have hG := realizedFam_genJointGram (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x
  have hjoint : ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) x i j k l r.2)
      (s₀, y) :=
    gen_joint_riemann (I := I) (realizedFam (I := I) g₀ T T' hδ hδ') x hG i j k l hs₀ hy
  have hcomp : (fun s : ℝ =>
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k l y) =
      (fun r : ℝ × E =>
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' r.1) x i j k l r.2)
        ∘ (fun s : ℝ => (s, y)) := by funext s; rfl
  rw [hcomp]
  exact ((hjoint.comp s₀ ((contDiffAt_id).prodMk contDiffAt_const)).differentiableAt
    (by simp)).hasDerivAt

omit [CompactSpace M] in
theorem hasDerivAt_realizedFam_chartRicciTensor (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (i k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I x).target) {s₀ : ℝ}
    (hs₀ : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ')) :
    HasDerivAt
      (fun s : ℝ => chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k y)
      (∑ j : Fin (Module.finrank ℝ E),
        deriv (fun s : ℝ =>
          chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k j y) s₀)
            s₀ := by
  have heq : (fun s : ℝ =>
        chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k y) =
      (fun s : ℝ => ∑ j : Fin (Module.finrank ℝ E),
        chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k j y) := by
    funext s; rw [chartRicciTensor_def]
  rw [heq]
  refine HasDerivAt.fun_sum (fun j _ => ?_)
  exact hasDerivAt_realizedFam_chartRiemannTensor (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i j k j hy
    hs₀

omit [CompactSpace M] in
theorem hasDerivAt_realizedRicciChartSum_general (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (x : M) (v w : TangentSpace I x) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w)
      (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          (∑ j : Fin (Module.finrank ℝ E),
            deriv (fun s : ℝ =>
              chartRiemannTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i j k j
                (extChartAt I x x)) s₀)) s₀ := by
  have hmem : s₀ ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs₀.1.le, hs₀.2.le⟩
  have hy : (extChartAt I x x) ∈ interior (extChartAt I x).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x (mem_extChartAt_target x)
  have hbody : (realizedRicciChartSum (I := I) g₀ T T' hδ hδ' x v w) =
      (fun s : ℝ => ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        ((chartModelBasis E).repr v) k * ((chartModelBasis E).repr w) i *
          chartRicciTensor (I := I) (realizedFam (I := I) g₀ T T' hδ hδ' s) x i k
            (extChartAt I x x)) := by
    funext s; rw [realizedRicciChartSum]
  rw [hbody]
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  refine HasDerivAt.fun_sum (fun k _ => ?_)
  exact (hasDerivAt_realizedFam_chartRicciTensor (I := I) g₀ T T' hδ_lt hδ hδ'_lt hδ' x i k hy
    hmem).const_mul _

end RicciLinearization
end DeTurck
end PDE
end DifferentialGeometry

end
