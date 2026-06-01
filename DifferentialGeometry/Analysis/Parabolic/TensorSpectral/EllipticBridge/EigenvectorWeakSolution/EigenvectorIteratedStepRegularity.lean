import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHSWkp

/-!
# Polymorphic-in-`K` `W^{k,2}` regularity of the per-step effective source

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the standalone
inductive step `eigenvectorChartIteratedStep` of the eigenvector chart
variational identity is the indicator, of the compact partition-of-unity kernel
`chartPouKernel α`, of the chart-density-divided differentiated numerator
`eigenvectorChartIteratedStepNumerator / densityOnEuclid g α`.

This module discharges its polymorphic `W^{k,2}` regularity: for each `K : ℕ`,
given

* `MemWkp (m + 2 + K) 2` of the eigenvector chart component
  `eigenvectorChartComponentFun`, and
* `MemWkp (K + 1) 2` of the level-`m` effective source `fChartEffPrev` (which is
  ae-zero off the partition-of-unity kernel `chartPouKernel α`),

the level-`(m+1)` effective source `eigenvectorChartIteratedStep` lies in
`MemWkp K 2` on the open chart target.

## Strategy

The work is a thin wrapper over the already-proven differentiated-numerator
regularity. By definition

```
eigenvectorChartIteratedStep … fChartEffPrev l
  = Set.indicator (chartPouKernel α)
      (fun y => eigenvectorChartIteratedStepNumerator … fChartEffPrev l y /
                densityOnEuclid g α y),
```

and `eigenvectorChartIteratedStepNumerator … m dirs fChartEffPrev l` coincides
(via `eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator`) with the
level-`(m+1)`-indexed `eigenvectorChartRHSDiffNumerator … m (Fin.snoc dirs l)`.

Writing `Q := numerator / densityOnEuclid g α`:

* `Q` lies in `MemWkp K 2` on the chart target — this is exactly the substep-2a
  campaign lemma `eigenvectorChartRHSDiffNumerator_div_density_memWkp`;
* `Q` ae-vanishes on `chartTargetEuclid α \ chartPouKernel α` — the public
  restatement
  `eigenvectorChartRHSDiffNumerator_div_density_ae_zero_off_chartPouKernel`;
* therefore `Set.indicator (chartPouKernel α) Q =ᵐ Q` on the open chart target
  (split `chartTargetEuclid α = chartPouKernel α ∪ (chartTargetEuclid α \
  chartPouKernel α)`: on the kernel the indicator returns `Q`; off the kernel
  both the indicator and `Q` ae-vanish).

`MemWkp_congr_ae` then transfers `MemWkp K 2` of `Q` to
`eigenvectorChartIteratedStep`.

## Main results

* `eigenvectorChartIteratedStep_memWkp_K_two` — the headline
  regularity propagator at every `K ≥ 0`.
* `eigenvectorChartIteratedStep_memW1p_two` — the `K = 1` corollary,
  restated as `DeGiorgi.MemW1p 2` via `MemWkp.one_iff_memW1p`.

These are the tensor analogues of the scalar campaign's
`fChartEffStep_memWkp_K_two` and `fChartEffStep_memW1p_two`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

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

/-- **Polymorphic `MemWkp K 2` regularity of the per-step effective source.**
Given:

* `MemWkp (m + 2 + K) 2` regularity of the eigenvector chart component
  `eigenvectorChartComponentFun` on the chart target;
* `MemWkp (K + 1) 2` regularity of the previous-level effective source
  `fChartEffPrev` on the chart target;
* ae-vanishing of `fChartEffPrev` on `chartTargetEuclid α \ chartPouKernel α`,

the level-`(m+1)` standalone inductive step `eigenvectorChartIteratedStep`
lies in `MemWkp K 2` on `chartTargetEuclid α`. This discharges the per-step
regularity propagator at every `K ≥ 0`. -/
theorem eigenvectorChartIteratedStep_memWkp_K_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (l : Fin (Module.finrank ℝ E))
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_memWkp_succ :
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Q : EuclN → ℝ := fun y =>
    eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m (Fin.snoc dirs l) fChartEffPrev y /
    densityOnEuclid (I := I) g α y with hQ_def
  have h_step_eq :
      eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l =
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
    unfold eigenvectorChartIteratedStep
    have h_num := eigenvectorChartIteratedStepNumerator_eq_rhsDiffNumerator
      (I := I) (M := M) g r s i α P₀ m dirs fChartEffPrev l
    funext y
    simp only [hQ_def]
    rw [h_num]
  have hQ_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 Q
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartRHSDiffNumerator_div_density_memWkp (I := I) (M := M)
      g r s i α P₀ m K (Fin.snoc dirs l)
      h_comp h_prev_memWkp_succ h_prev_ae_zero
  have hQ_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) :=
    eigenvectorChartRHSDiffNumerator_div_density_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ m (Fin.snoc dirs l)
      h_prev_ae_zero
  have h_indicator_ae_eq_Q :
      Set.indicator (chartPouKernel (I := I) (M := M) α) Q =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)] Q := by
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    set Kα : Set EuclN := chartPouKernel (I := I) (M := M) α with hKα_def
    have hΩ_meas : MeasurableSet Ω :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    have hKα_meas : MeasurableSet Kα :=
      chartPouKernel_measurableSet (I := I) (M := M) α
    have hKα_sub_Ω : Kα ⊆ Ω :=
      chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α
    have h_inter_meas : MeasurableSet (Ω ∩ Kα) := hΩ_meas.inter hKα_meas
    have h_eq_on_inter : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω ∩ Kα)] Q := by
      refine (ae_restrict_iff' h_inter_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_mem hy.2 _
    have h_diff_meas : MeasurableSet (Ω \ Kα) := hΩ_meas.diff hKα_meas
    have h_indicator_ae_zero : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) := by
      refine (ae_restrict_iff' h_diff_meas).mpr ?_
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact Set.indicator_of_notMem hy.2 _
    have h_eq_on_diff : Set.indicator Kα Q =ᵐ[
        (volume : Measure EuclN).restrict (Ω \ Kα)] Q := by
      filter_upwards [h_indicator_ae_zero, hQ_ae_zero] with y h0 hQ0
      rw [h0, hQ0]
    have h_cover : Ω = (Ω ∩ Kα) ∪ (Ω \ Kα) := by
      ext y; constructor
      · intro hy
        by_cases h : y ∈ Kα
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr ⟨hy, h⟩
      · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
    have h_disj : Disjoint (Ω ∩ Kα) (Ω \ Kα) := by
      refine Set.disjoint_left.mpr ?_
      intro y hy hy'; exact hy'.2 hy.2
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Kα) ∪ (Ω \ Kα)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, MeasureTheory.Measure.restrict_union h_disj h_diff_meas]
    exact (MeasureTheory.ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  rw [h_step_eq]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    h_indicator_ae_eq_Q).mpr hQ_memWkp

/-- **`K = 1` corollary.** At `K = 1`, the regularity propagator gives
`MemWkp 1 2 (eigenvectorChartIteratedStep)`, restated as
`DeGiorgi.MemW1p 2` via `MemWkp.one_iff_memW1p`. -/
theorem eigenvectorChartIteratedStep_memW1p_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    {fChartEffPrev : EuclN → ℝ}
    (l : Fin (Module.finrank ℝ E))
    (h_comp : MemWkp (d := Module.finrank ℝ E) (m + 3) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_memWkp_two :
      MemWkp (d := Module.finrank ℝ E) 2 2 fChartEffPrev
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_ae_zero : fChartEffPrev =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)]
      (fun _ => (0 : ℝ))) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartIteratedStep (I := I) (M := M)
        g r s i α P₀ m dirs fChartEffPrev l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_prev_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (1 + 1) 2
      fChartEffPrev (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : (1 + 1 : ℕ) = 2 := by norm_num
    rw [h_eq]; exact h_prev_memWkp_two
  have h_comp' : MemWkp (d := Module.finrank ℝ E) (m + 2 + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : m + 2 + 1 = m + 3 := by ring
    rw [h_eq]; exact h_comp
  have h_mem := eigenvectorChartIteratedStep_memWkp_K_two (I := I) (M := M)
    g r s i α P₀ m 1 dirs (fChartEffPrev := fChartEffPrev) l
    h_comp' h_prev_memWkp_succ h_prev_ae_zero
  rw [MemWkp.one_iff_memW1p] at h_mem
  exact h_mem

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
