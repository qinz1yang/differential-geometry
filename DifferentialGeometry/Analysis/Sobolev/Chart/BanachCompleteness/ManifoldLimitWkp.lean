import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.BanachManifold
import DifferentialGeometry.Analysis.Sobolev.Chart.CrossChartBounds.CrossChartAe

/-!
# Sobolev membership of the assembled manifold limit

This file assembles the fixed-support cross-chart producer over the finite
canonical partition of unity.  It proves that the already-defined
`manifoldLimitFun` belongs to the chart Sobolev class.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The measurable pullback used in the completeness construction is the same
pointwise function as the chart pullback used by the cross-chart estimates. -/
lemma pullback_eq_chart (α : M) (v : EuclN → ℝ) :
    pullbackToManifold (I := I) α v = chartPullback I α v := by
  funext x
  by_cases hx : x ∈ (chartAt H α).source
  · rw [pullbackToManifold_apply_of_mem (I := I) (α := α) v hx,
      chartPullback_apply_of_mem (I := I) (M := M) α v hx]
  · rw [pullbackToManifold_apply_of_notMem (I := I) (α := α) v hx,
      chartPullback_apply_of_notMem (I := I) (M := M) α v hx]

/-- The finite POU assembly of the chosen chart limits belongs to
`MemWkpChart g k p`. -/
theorem limitFun_memWkp
    [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {hp : 1 ≤ p}
    {f : ℕ → WkpChart (I := I) (M := M) g k p hp}
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormChart (I := I) (M := M) g k p
        (fun x => wkpChartFun (f m) x - wkpChartFun (f n) x) ≤
        ENNReal.ofReal ε) :
    MemWkpChart (I := I) (M := M) g k p
      (manifoldLimitFun (I := I) (M := M) hp_one hp_top h_cauchy) := by
  classical
  intro γ
  let ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M
  let S := DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset
    (I := I) (M := M)
  let L : M → EuclN → ℝ := fun β =>
    chartLimit (I := I) (M := M) hp_one hp_top h_cauchy β
  let q : M → EuclN → ℝ := fun β =>
    chartPushed (I := I) (M := M) ρ γ (chartPullback I β (L β))
  have hq_mem : ∀ β : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p (q β)
        (chartTargetEuclid (I := I) (M := M) γ) := by
    intro β
    let Kβ : Set M := tsupport ((ρ β : C^∞⟮I, M; ℝ⟯) : M → ℝ)
    have hKβ_compact : IsCompact Kβ := (isClosed_tsupport _).isCompact
    have hKβ_sub : Kβ ⊆ (chartAt H β).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
    obtain ⟨_C, _hC, hcross⟩ := crossChartAeJoint (I := I) (M := M)
      g k hp_one hp_top γ β hKβ_compact hKβ_sub
    have hL_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p (L β)
        (chartTargetEuclid (I := I) (M := M) β) :=
      chartLimit_memWkp (I := I) (M := M) (g := g)
        hp_one hp_top h_cauchy β
    have hL_zero : L β =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) β \
          (fun x : M => (toEuclidean (E := E)) (extChartAt I β x)) '' Kβ)] 0 := by
      simpa only [L, Kβ, ρ, Set.image_image, Function.comp_apply] using
        (chartLimit_ae_zero (I := I) (M := M) (g := g)
          hp_one hp_top h_cauchy β)
    exact (hcross hL_mem hL_zero).1
  have hsum_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) k p (fun y => ∑ β ∈ S, q β y)
      (chartTargetEuclid (I := I) (M := M) γ) := by
    have hΩ : IsOpen (chartTargetEuclid (I := I) (M := M) γ) :=
      chartTargetEuclid_isOpen (I := I) (M := M) γ
    induction S using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
          (d := Module.finrank ℝ E) hp_one hΩ
    | @insert β T hβ ih =>
        have h_eq :
            (fun y : EuclN => ∑ δ ∈ insert β T, q δ y) =
              (fun y : EuclN => q β y + ∑ δ ∈ T, q δ y) := by
          funext y
          rw [Finset.sum_insert hβ]
        rw [h_eq]
        exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
          (d := Module.finrank ℝ E) hp_one hΩ
          (hq_mem β) ih
  have hpushed_eq :
      chartPushed (I := I) (M := M) ρ γ
          (manifoldLimitFun (I := I) (M := M) hp_one hp_top h_cauchy) =
        fun y => ∑ β ∈ S, q β y := by
    funext y
    unfold manifoldLimitFun chartPushed
    change (ρ γ : C^∞⟮I, M; ℝ⟯)
          ((extChartAt I γ).symm ((toEuclidean (E := E)).symm y)) *
        (∑ β ∈ S, pullbackToManifold (I := I) β (L β)
          ((extChartAt I γ).symm ((toEuclidean (E := E)).symm y))) =
      ∑ β ∈ S,
        (ρ γ : C^∞⟮I, M; ℝ⟯)
            ((extChartAt I γ).symm ((toEuclidean (E := E)).symm y)) *
          chartPullback I β (L β)
            ((extChartAt I γ).symm ((toEuclidean (E := E)).symm y))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro β _
    rw [pullback_eq_chart (I := I) (M := M)]
  rw [hpushed_eq]
  exact hsum_mem

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
