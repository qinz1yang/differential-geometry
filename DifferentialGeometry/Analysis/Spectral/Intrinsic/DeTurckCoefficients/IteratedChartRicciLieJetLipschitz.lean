import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartJetLipschitzClosure
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz

/-!
# All-order chart-jet Faà-di-Bruno Lipschitz of the chart Ricci and Lie–DeTurck components

The two genuine deliverables of the chart-jet Faà-di-Bruno tower: the **all-order**
(general order `N`) Lipschitz dependence of the chart-frame Ricci tensor
`chartRicciTensor` and of the chart-frame Lie–DeTurck (gauge) summand
`chartLieDeTurckComp` on the chart-Gram jet of the metric difference, uniform on a compact
subset of the chart-target interior.

Both components are polynomials in the chart-Gram entries, the inverse chart-Gram, and
their first/second partial derivatives (the coordinate Christoffel/Ricci/Lie formulas).
By the closure algebra `HasChartJetLip`, the order-`N` iterated derivative of each
difference expands by Faà-di-Bruno/Leibniz into a sum of products of `iteratedFDerivWithin l`
(`l ≤ N + 2`) of the Gram entries (the `+2` is the two derivatives of the curvature
expression), with constants uniform over a compact `R`-ball of metrics:
```
‖iteratedFDerivWithin ℝ N (chartRicciTensor g₁ α i k − chartRicciTensor g₂ α i k) s y‖ ≤
    C · chartGramJetDiffSeminormSum (N + 2) g₁ g₂ α s y
```
and likewise for `chartLieDeTurckComp`.  These are the all-order generalizations of the
`N = 0` atoms `exists_chartRicciTensor_lipschitz_on_compact` and
`exists_chartLieDeTurckComp_lipschitz_on_compact`.

## Main results

* `hasChartJetLip_gramBracket`, `hasChartJetLip_chartChristoffel` — derivative loss `1`.
* `hasChartJetLip_chartDeTurckVFComp` — derivative loss `1`.
* `hasChartJetLip_chartRicciTensor`, `hasChartJetLip_chartLieDeTurckComp` — loss `2`.
* `exists_chartRicciTensor_iteratedFDeriv_lipschitz_on_compact`,
  `exists_chartLieDeTurckComp_iteratedFDeriv_lipschitz_on_compact` — the unpacked
  all-order chart-jet Faà-di-Bruno Lipschitz estimates.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurckCoefficients

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- The `gramBracket` field (a combination of three first chart-Gram partials) has
chart-jet Lipschitz with derivative loss `1`. -/
theorem hasChartJetLip_gramBracket
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i j l : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K (fun g => gramBracket (I := I) g α i j l) 1 := by
  have hbr : HasChartJetLip g₁ g₂ α K
      (fun g => fun z =>
        (DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i
            (chartGramOnE (I := I) g α l j) z +
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv j
            (chartGramOnE (I := I) g α l i) z) +
        (-1 : ℝ) * DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv l
            (chartGramOnE (I := I) g α i j) z) 1 := by
    have h1 := (hasChartJetLip_chartGramOnE g₁ g₂ α hK hKsub l j).partialDeriv hKsub i
    have h2 := (hasChartJetLip_chartGramOnE g₁ g₂ α hK hKsub l i).partialDeriv hKsub j
    have h3 := (hasChartJetLip_chartGramOnE g₁ g₂ α hK hKsub i j).partialDeriv hKsub l
    have h3' := h3.const_smul hKsub (-1 : ℝ)
    have h12 := (h1.add hKsub h2)
    have h123 := h12.add hKsub h3'
    simpa only [max_self, zero_add] using h123
  refine hbr.congr ?_
  intro g
  funext z
  simp only [gramBracket]
  ring

/-- The chart Christoffel symbol field has chart-jet Lipschitz with derivative loss `1`. -/
theorem hasChartJetLip_chartChristoffel
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K (fun g => chartChristoffel (I := I) g α i j k) 1 := by
  have hprodL : ∀ l : Fin (Module.finrank ℝ E),
      HasChartJetLip g₁ g₂ α K
        (fun g => fun z => chartInvGramOnE (I := I) g α k l z *
          gramBracket (I := I) g α i j l z) 1 := by
    intro l
    have hinv := hasChartJetLip_chartInvGramOnE g₁ g₂ α hK hKsub k l
    have hbr := hasChartJetLip_gramBracket g₁ g₂ α hK hKsub i j l
    have := hinv.mul hKsub hbr
    simpa only [max_eq_right (Nat.zero_le 1)] using this
  have hsum := HasChartJetLip.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun l g => fun z => chartInvGramOnE (I := I) g α k l z *
      gramBracket (I := I) g α i j l z) (fun l _ => hprodL l)
  have hsmul := hsum.const_smul hKsub (1 / 2 : ℝ)
  refine hsmul.congr ?_
  intro g
  funext z
  rw [chartChristoffel_eq_sum_invGramOnE_bracket]

/-- The chart DeTurck vector-field component field has chart-jet Lipschitz with derivative
loss `1` (relative to a fixed background metric `g_bg`). -/
theorem hasChartJetLip_chartDeTurckVFComp
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (k : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K
      (fun g => fun z => chartDeTurckVFComp (I := I) g g_bg α k z) 1 := by
  have hbgconst : ∀ a b : Fin (Module.finrank ℝ E),
      HasChartJetLip g₁ g₂ α K
        (fun _ => fun z => chartChristoffel (I := I) g_bg α a b k z) 0 := by
    intro a b
    refine hasChartJetLip_const g₁ g₂ α hK hKsub
      (f₀ := fun z => chartChristoffel (I := I) g_bg α a b k z)
      (chartChristoffel_contDiffOn_interior (I := I) g_bg α a b k)
      (fun _ => rfl)
  have hprodAB : ∀ a b : Fin (Module.finrank ℝ E),
      HasChartJetLip g₁ g₂ α K
        (fun g => fun z => chartInvGramOnE (I := I) g α a b z *
          (chartChristoffel (I := I) g α a b k z -
            chartChristoffel (I := I) g_bg α a b k z)) 1 := by
    intro a b
    have hinv := hasChartJetLip_chartInvGramOnE g₁ g₂ α hK hKsub a b
    have hΓ := hasChartJetLip_chartChristoffel g₁ g₂ α hK hKsub a b k
    have hΓbg := hbgconst a b
    have hΓbg' := hΓbg.const_smul hKsub (-1 : ℝ)
    have hΓdiff := (hΓ.add hKsub hΓbg')
    have hΓdiff1 : HasChartJetLip g₁ g₂ α K
        (fun g => fun z => chartChristoffel (I := I) g α a b k z -
          chartChristoffel (I := I) g_bg α a b k z) 1 := by
      refine (hΓdiff.congr ?_)
      intro g; funext z; ring
    have := hinv.mul hKsub hΓdiff1
    simpa only [max_eq_right (Nat.zero_le 1)] using this
  have hsumB : ∀ a : Fin (Module.finrank ℝ E),
      HasChartJetLip g₁ g₂ α K
        (fun g => fun z => ∑ b : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α a b z *
            (chartChristoffel (I := I) g α a b k z -
              chartChristoffel (I := I) g_bg α a b k z)) 1 :=
    fun a => HasChartJetLip.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (F := fun b g => fun z => chartInvGramOnE (I := I) g α a b z *
        (chartChristoffel (I := I) g α a b k z -
          chartChristoffel (I := I) g_bg α a b k z)) (fun b _ => hprodAB a b)
  have hsumA := HasChartJetLip.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun a g => fun z => ∑ b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α a b z *
        (chartChristoffel (I := I) g α a b k z -
          chartChristoffel (I := I) g_bg α a b k z)) (fun a _ => hsumB a)
  refine hsumA.congr ?_
  intro g
  funext z
  rw [chartDeTurckVFComp_def]

/-- The chart Riemann tensor field has chart-jet Lipschitz with derivative loss `2`. -/
theorem hasChartJetLip_chartRiemannTensor
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i j k l : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K
      (fun g => fun z => chartRiemannTensor (I := I) g α i j k l z) 2 := by
  have hdΓ1 : HasChartJetLip g₁ g₂ α K
      (fun g => DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv j
        (chartChristoffel (I := I) g α i k l)) 2 := by
    have := (hasChartJetLip_chartChristoffel g₁ g₂ α hK hKsub i k l).partialDeriv hKsub j
    simpa using this
  have hdΓ2 : HasChartJetLip g₁ g₂ α K
      (fun g => fun z => (-1 : ℝ) *
        DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv k
          (chartChristoffel (I := I) g α i j l) z) 2 := by
    have h := (hasChartJetLip_chartChristoffel g₁ g₂ α hK hKsub i j l).partialDeriv hKsub k
    have h' := h.const_smul hKsub (-1 : ℝ)
    simpa using h'
  have hprodM : ∀ m : Fin (Module.finrank ℝ E),
      HasChartJetLip g₁ g₂ α K
        (fun g => fun z => chartChristoffel (I := I) g α j m l z *
            chartChristoffel (I := I) g α i k m z +
          (-1 : ℝ) * (chartChristoffel (I := I) g α k m l z *
            chartChristoffel (I := I) g α i j m z)) 2 := by
    intro m
    have hA := (hasChartJetLip_chartChristoffel g₁ g₂ α hK hKsub j m l).mul hKsub
      (hasChartJetLip_chartChristoffel g₁ g₂ α hK hKsub i k m)
    have hB := (hasChartJetLip_chartChristoffel g₁ g₂ α hK hKsub k m l).mul hKsub
      (hasChartJetLip_chartChristoffel g₁ g₂ α hK hKsub i j m)
    have hB' := hB.const_smul hKsub (-1 : ℝ)
    have hAB := (hA.add hKsub hB')
    exact (hAB.of_le (by norm_num)).congr (fun g => rfl)
  have hsumM := HasChartJetLip.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun m g => fun z => chartChristoffel (I := I) g α j m l z *
        chartChristoffel (I := I) g α i k m z +
      (-1 : ℝ) * (chartChristoffel (I := I) g α k m l z *
        chartChristoffel (I := I) g α i j m z)) (fun m _ => hprodM m)
  have htotal := ((hdΓ1.add hKsub hdΓ2).add hKsub hsumM)
  refine (htotal.of_le (by norm_num)).congr ?_
  intro g
  funext z
  rw [chartRiemannTensor_def]
  rw [show (∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m l z *
            chartChristoffel (I := I) g α i k m z +
          (-1 : ℝ) * (chartChristoffel (I := I) g α k m l z *
            chartChristoffel (I := I) g α i j m z))) =
      ∑ m : Fin (Module.finrank ℝ E),
        (chartChristoffel (I := I) g α j m l z *
            chartChristoffel (I := I) g α i k m z -
          chartChristoffel (I := I) g α k m l z *
            chartChristoffel (I := I) g α i j m z) from by
    refine Finset.sum_congr rfl (fun m _ => by ring)]
  ring

/-- **All-order chart-jet Faà-di-Bruno Lipschitz of the chart Ricci tensor.**

The chart Ricci tensor field `chartRicciTensor` has chart-jet Lipschitz with derivative
loss `2`. -/
theorem hasChartJetLip_chartRicciTensor
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i k : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K (fun g => chartRicciTensor (I := I) g α i k) 2 := by
  have hsum := HasChartJetLip.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun j g => fun z => chartRiemannTensor (I := I) g α i j k j z)
    (fun j _ => hasChartJetLip_chartRiemannTensor g₁ g₂ α hK hKsub i j k j)
  refine hsum.congr ?_
  intro g
  funext z
  rw [chartRicciTensor_def]

/-- **All-order chart-jet Faà-di-Bruno Lipschitz of the chart Lie–DeTurck summand.**

The chart Lie–DeTurck (gauge) summand field `chartLieDeTurckComp` has chart-jet Lipschitz
with derivative loss `2`. -/
theorem hasChartJetLip_chartLieDeTurckComp
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    HasChartJetLip g₁ g₂ α K
      (fun g => chartLieDeTurckComp (I := I) g g_bg α i j) 2 := by
  have hgroup0 : ∀ k : Fin (Module.finrank ℝ E),
      HasChartJetLip g₁ g₂ α K
        (fun g => fun z => chartDeTurckVFComp (I := I) g g_bg α k z *
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv k
            (chartGramOnE (I := I) g α i j) z) 2 := by
    intro k
    have hW := hasChartJetLip_chartDeTurckVFComp g₁ g₂ g_bg α hK hKsub k
    have hdG := (hasChartJetLip_chartGramOnE g₁ g₂ α hK hKsub i j).partialDeriv hKsub k
    have := hW.mul hKsub hdG
    exact this.of_le (by norm_num)
  have hgroup1 : ∀ k : Fin (Module.finrank ℝ E),
      HasChartJetLip g₁ g₂ α K
        (fun g => fun z => chartGramOnE (I := I) g α k j z *
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i
            (fun w => chartDeTurckVFComp (I := I) g g_bg α k w) z) 2 := by
    intro k
    have hG := hasChartJetLip_chartGramOnE g₁ g₂ α hK hKsub k j
    have hdW := (hasChartJetLip_chartDeTurckVFComp g₁ g₂ g_bg α hK hKsub k).partialDeriv hKsub i
    have := hG.mul hKsub hdW
    exact this.of_le (by norm_num)
  have hgroup2 : ∀ k : Fin (Module.finrank ℝ E),
      HasChartJetLip g₁ g₂ α K
        (fun g => fun z => chartGramOnE (I := I) g α i k z *
          DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv j
            (fun w => chartDeTurckVFComp (I := I) g g_bg α k w) z) 2 := by
    intro k
    have hG := hasChartJetLip_chartGramOnE g₁ g₂ α hK hKsub i k
    have hdW := (hasChartJetLip_chartDeTurckVFComp g₁ g₂ g_bg α hK hKsub k).partialDeriv hKsub j
    have := hG.mul hKsub hdW
    exact this.of_le (by norm_num)
  have hsum0 := HasChartJetLip.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun k g => fun z => chartDeTurckVFComp (I := I) g g_bg α k z *
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv k
        (chartGramOnE (I := I) g α i j) z) (fun k _ => hgroup0 k)
  have hsum1 := HasChartJetLip.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun k g => fun z => chartGramOnE (I := I) g α k j z *
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv i
        (fun w => chartDeTurckVFComp (I := I) g g_bg α k w) z) (fun k _ => hgroup1 k)
  have hsum2 := HasChartJetLip.sum hKsub (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (F := fun k g => fun z => chartGramOnE (I := I) g α i k z *
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv j
        (fun w => chartDeTurckVFComp (I := I) g g_bg α k w) z) (fun k _ => hgroup2 k)
  have htotal := ((hsum0.add hKsub hsum1).add hKsub hsum2)
  refine (htotal.of_le (by norm_num)).congr ?_
  intro g
  funext z
  rw [chartLieDeTurckComp_def]

/-- **The unpacked all-order chart-jet Faà-di-Bruno Lipschitz estimate for the chart Ricci
tensor**, on the chart-target interior `s = interior (extChartAt I α).target`.

For two smooth Riemannian metrics `g₁, g₂`, a chart base point `α`, a compact subset `K`
of `s`, and any order `N`, there is a single constant `C > 0` such that for every `y ∈ K`
and all indices `(i, k)`,
```
‖iteratedFDerivWithin ℝ N (chartRicciTensor g₁ α i k − chartRicciTensor g₂ α i k) s y‖ ≤
    C · chartGramJetDiffSeminormSum (N + 2) g₁ g₂ α s y .
```
This is the all-order generalization of `exists_chartRicciTensor_lipschitz_on_compact`. -/
theorem exists_chartRicciTensor_iteratedFDeriv_lipschitz_on_compact
    (g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i k : Fin (Module.finrank ℝ E),
      ‖iteratedFDerivWithin ℝ N
          (fun z => chartRicciTensor (I := I) g₁ α i k z -
            chartRicciTensor (I := I) g₂ α i k z)
          (interior (extChartAt I α).target) y‖ ≤
        C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + 2) g₁ g₂ α
          (interior (extChartAt I α).target) y := by
  classical
  have hindexed : ∀ i k : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K,
        ‖iteratedFDerivWithin ℝ N
            (fun z => chartRicciTensor (I := I) g₁ α i k z -
              chartRicciTensor (I := I) g₂ α i k z)
            (interior (extChartAt I α).target) y‖ ≤
          C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + 2) g₁ g₂ α
            (interior (extChartAt I α).target) y :=
    fun i k => (hasChartJetLip_chartRicciTensor g₁ g₂ α hK hKsub i k).lip N
  choose Cik hCik_pos hCik using hindexed
  refine ⟨(Finset.univ : Finset (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).sup'
      Finset.univ_nonempty (fun p => Cik p.1 p.2), ?_, fun y hy i k => ?_⟩
  · obtain ⟨p₀⟩ := (inferInstance :
      Nonempty (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)))
    exact lt_of_lt_of_le (hCik_pos p₀.1 p₀.2)
      (Finset.le_sup' (fun p => Cik p.1 p.2) (Finset.mem_univ p₀))
  · refine (hCik i k y hy).trans ?_
    refine mul_le_mul_of_nonneg_right ?_
      (chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + 2) g₁ g₂ α _ y)
    exact Finset.le_sup' (fun p => Cik p.1 p.2) (Finset.mem_univ (i, k))

/-- **The unpacked all-order chart-jet Faà-di-Bruno Lipschitz estimate for the chart
Lie–DeTurck summand**, on the chart-target interior.

For two smooth Riemannian metrics `g₁, g₂`, a fixed background metric `g_bg`, a chart base
point `α`, a compact subset `K` of the chart-target interior, and any order `N`, there is a
single constant `C > 0` such that for every `y ∈ K` and all indices `(i, j)`,
```
‖iteratedFDerivWithin ℝ N (chartLieDeTurckComp g₁ g_bg α i j −
    chartLieDeTurckComp g₂ g_bg α i j) s y‖ ≤ C · chartGramJetDiffSeminormSum (N + 2) g₁ g₂ α s y .
```
This is the all-order generalization of `exists_chartLieDeTurckComp_lipschitz_on_compact`. -/
theorem exists_chartLieDeTurckComp_iteratedFDeriv_lipschitz_on_compact
    (g₁ g₂ g_bg : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      ‖iteratedFDerivWithin ℝ N
          (fun z => chartLieDeTurckComp (I := I) g₁ g_bg α i j z -
            chartLieDeTurckComp (I := I) g₂ g_bg α i j z)
          (interior (extChartAt I α).target) y‖ ≤
        C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + 2) g₁ g₂ α
          (interior (extChartAt I α).target) y := by
  classical
  have hindexed : ∀ i j : Fin (Module.finrank ℝ E),
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K,
        ‖iteratedFDerivWithin ℝ N
            (fun z => chartLieDeTurckComp (I := I) g₁ g_bg α i j z -
              chartLieDeTurckComp (I := I) g₂ g_bg α i j z)
            (interior (extChartAt I α).target) y‖ ≤
          C * chartGramJetDiffSeminormSum (I := I) (M := M) (N + 2) g₁ g₂ α
            (interior (extChartAt I α).target) y :=
    fun i j => (hasChartJetLip_chartLieDeTurckComp g₁ g₂ g_bg α hK hKsub i j).lip N
  choose Cij hCij_pos hCij using hindexed
  refine ⟨(Finset.univ : Finset (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))).sup'
      Finset.univ_nonempty (fun p => Cij p.1 p.2), ?_, fun y hy i j => ?_⟩
  · obtain ⟨p₀⟩ := (inferInstance :
      Nonempty (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)))
    exact lt_of_lt_of_le (hCij_pos p₀.1 p₀.2)
      (Finset.le_sup' (fun p => Cij p.1 p.2) (Finset.mem_univ p₀))
  · refine (hCij i j y hy).trans ?_
    refine mul_le_mul_of_nonneg_right ?_
      (chartGramJetDiffSeminormSum_nonneg (I := I) (M := M) (N + 2) g₁ g₂ α _ y)
    exact Finset.le_sup' (fun p => Cij p.1 p.2) (Finset.mem_univ (i, j))

end DeTurckCoefficients
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
