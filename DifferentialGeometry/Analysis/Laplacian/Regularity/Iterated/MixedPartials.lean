import DifferentialGeometry.Analysis.Laplacian.Regularity.Iterated.ChosenThirdMixedPartial
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplViaH3
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev

/-!
# Iterated mixed weak partials of the canonical chart-pushed representative

For a closed Riemannian manifold `(M, g)` and an element
`u_h : H1Compl g`, the canonical chart-pushed POU-cut representative
`chartPushed POU α (H1ComplToLp g u_h).coeFn` is a scalar function on the
open chart target `chartTargetEuclid α ⊆ EuclideanSpace ℝ (Fin n)`. This
module packages the polymorphic-in-`m` chosen `m`-fold mixed weak partial of
that representative, together with the structural regularity bridge

```
MemWkp (k + m) 2 (chart-pushed parent) Ω
  ⇒ MemWkp k 2 (m-mixed partial)        Ω
```

## Indexing convention

The `m` differentiation directions are encoded by a multi-index
`idx : Fin m → Fin n`. The recursive definition

```
chosenMthMixedPartialChartPushedU g α u_h (m+1) idx
  := chosenWeakPartial' 2 (idx (Fin.last m))
       (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init idx))
       (chartTargetEuclid α)
```

treats the **last** entry `idx (Fin.last m)` as the **outermost** (final)
differentiation direction. Concretely, at `m = 2` with `idx 0 = i`,
`idx 1 = l`, this collapses to

```
chosenWeakPartial' 2 l (chosenWeakPartial' 2 i (chart-pushed parent) Ω) Ω
  = chosenSecondPartialChartPushedU g α u_h i l,
```

and at `m = 3` with `idx 0 = i, idx 1 = l, idx 2 = j` it collapses to

```
chosenWeakPartial' 2 j (chosenSecondPartialChartPushedU g α u_h i l) Ω
  = chosenThirdMixedPartialChartPushedU g α u_h i l j.
```

## Main definitions

* `chosenMthMixedPartialChartPushedU` — the canonical chosen `m`-fold mixed
  weak partial of the chart-pushed POU representative of `H1ComplToLp g u_h`
  in the directions encoded by `idx : Fin m → Fin n`, on the open chart
  target.

## Main theorems

* `chosenMthMixedPartialChartPushedU_zero` /
  `chosenMthMixedPartialChartPushedU_succ` — definitional unfolding.

* `chosenMthMixedPartialChartPushedU_one_eq_chosenFirstPartial` — the
  `m = 1` instance coincides with `chartPushedChosenFirstPartial`.

* `chosenMthMixedPartialChartPushedU_two_eq_chosenSecondPartialChartPushedU`
  — the `m = 2` instance coincides with `chosenSecondPartialChartPushedU`
  (for matched indices).

* `chosenMthMixedPartialChartPushedU_three_eq_chosenThirdMixedPartialChartPushedU`
  — the `m = 3` instance coincides with `chosenThirdMixedPartialChartPushedU`
  (for matched indices).

* `chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp` — the
  polymorphic regularity bridge: chart-`H^{k+m}` of the parent ⇒ chart-`H^k`
  of the `m`-mixed partial.

* `chosenMthMixedPartialChartPushedU_memLp_two` — the `k = 0` corollary:
  `MemLp 2` on the chart target.

* `chosenMthMixedPartialChartPushedU_memW1p_two` — the `k = 1` corollary:
  `MemW1p 2` on the chart target.

* `chosenMthMixedPartialChartPushedU_locally_memLp` — the local `L²`
  corollary on every compact subset of the chart target.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedMixedPartials

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The canonical chosen `m`-fold mixed weak partial of the chart-pushed POU
representative of `H1ComplToLp g u_h` in the directions encoded by
`idx : Fin m → Fin n`, on the open chart target. Recursive definition: at
the inductive step, the **last** entry `idx (Fin.last m)` is the outermost
(final) differentiation direction. -/
noncomputable def chosenMthMixedPartialChartPushedU
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _ =>
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)
  | m + 1, idx =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 (idx (Fin.last m))
        (chosenMthMixedPartialChartPushedU g α u_h m (Fin.init idx))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)

/-- Definitional unfolding at `m = 0`. -/
@[simp] theorem chosenMthMixedPartialChartPushedU_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (idx : Fin 0 → Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 0 idx =
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := rfl

/-- Definitional unfolding at `m + 1`. -/
theorem chosenMthMixedPartialChartPushedU_succ
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (m : ℕ) (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h (m + 1) idx =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 (idx (Fin.last m))
        (chosenMthMixedPartialChartPushedU (I := I) (M := M)
          g α u_h m (Fin.init idx))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := rfl

/-- The `m = 1` instance: for any `idx : Fin 1 → Fin n`, the chosen first
mixed partial agrees on the nose with `chartPushedChosenFirstPartial g α u_h
(idx 0)`. -/
theorem chosenMthMixedPartialChartPushedU_one_eq_chosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (idx : Fin 1 → Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1 idx =
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h (idx 0) := by
  rw [chosenMthMixedPartialChartPushedU_succ]
  rw [chosenMthMixedPartialChartPushedU_zero]
  unfold chartPushedChosenFirstPartial
  rfl

/-- The `m = 2` instance: for any `idx : Fin 2 → Fin n` with `idx 0 = i` and
`idx 1 = l`, the chosen second mixed partial agrees on the nose with
`chosenSecondPartialChartPushedU g α u_h i l`. -/
theorem chosenMthMixedPartialChartPushedU_two_eq_chosenSecondPartialChartPushedU
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i l : Fin (Module.finrank ℝ E))
    (idx : Fin 2 → Fin (Module.finrank ℝ E))
    (h_idx_0 : idx 0 = i) (h_idx_1 : idx 1 = l) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 2 idx =
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l := by
  rw [chosenMthMixedPartialChartPushedU_succ]
  rw [chosenMthMixedPartialChartPushedU_succ]
  rw [chosenMthMixedPartialChartPushedU_zero]
  have h_last_1 : idx (Fin.last 1) = l := by
    have : (Fin.last 1 : Fin 2) = 1 := rfl
    rw [this, h_idx_1]
  have h_inner_last : (Fin.init idx) (Fin.last 0) = i := by
    have h0 : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [h0]
    simp [Fin.init, h_idx_0]
  rw [h_last_1, h_inner_last]
  rfl

/-- The `m = 3` instance: for any `idx : Fin 3 → Fin n` with `idx 0 = i`,
`idx 1 = l`, `idx 2 = j`, the chosen third mixed partial agrees on the nose
with `chosenThirdMixedPartialChartPushedU g α u_h i l j`. -/
theorem chosenMthMixedPartialChartPushedU_three_eq_chosenThirdMixedPartialChartPushedU
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i l j : Fin (Module.finrank ℝ E))
    (idx : Fin 3 → Fin (Module.finrank ℝ E))
    (h_idx_0 : idx 0 = i) (h_idx_1 : idx 1 = l) (h_idx_2 : idx 2 = j) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 3 idx =
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l j := by
  rw [chosenMthMixedPartialChartPushedU_succ]
  have h_last_2 : idx (Fin.last 2) = j := by
    have : (Fin.last 2 : Fin 3) = 2 := rfl
    rw [this, h_idx_2]
  rw [h_last_2]
  have h_init_0 : (Fin.init idx) 0 = i := by
    simp [Fin.init, h_idx_0]
  have h_init_1 : (Fin.init idx) 1 = l := by
    simp [Fin.init, h_idx_1]
  have h_inner_eq := chosenMthMixedPartialChartPushedU_two_eq_chosenSecondPartialChartPushedU
    (I := I) (M := M) g α u_h i l (Fin.init idx) h_init_0 h_init_1
  rw [h_inner_eq]
  unfold chosenThirdMixedPartialChartPushedU
  rfl

/-- **Polymorphic regularity bridge.** From chart-`H^{k+m}` of the canonical
chart-pushed POU representative of `u_h.coeFn` on the chart target, every
`m`-fold chosen mixed weak partial lies in chart-`H^k` on the chart target,
for arbitrary `m, k : ℕ` and arbitrary multi-index `idx : Fin m → Fin n`. -/
theorem chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (m : ℕ) :
    ∀ (k : ℕ),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (k + m) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) →
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k 2
          (chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h m idx)
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent _idx
      simpa [chosenMthMixedPartialChartPushedU_zero] using h_parent
  | succ m ih =>
      intro k h_parent idx
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) ((k + 1) + m) 2
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M) (chartAtlasPOU I M) α
              ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α) := by
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq]
        exact h_parent
      have h_inner :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (k + 1) 2
            (chosenMthMixedPartialChartPushedU
              (I := I) (M := M) g α u_h m (Fin.init idx))
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α) :=
        ih (k + 1) h_parent' (Fin.init idx)
      have h_step := h_inner.chosenWeakPartial_mem (idx (Fin.last m))
      rw [chosenMthMixedPartialChartPushedU_succ]
      exact h_step

/-- **`k = 0` corollary.** From chart-`H^m` of the chart-pushed parent, every
`m`-fold chosen mixed weak partial is `MemLp 2` on the chart target. -/
theorem chosenMthMixedPartialChartPushedU_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (m : ℕ)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    MemLp
      (chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m idx) 2
      ((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)) := by
  have h_parent' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (0 + m) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
    simpa [Nat.zero_add] using h_parent
  have h_memWkp_0 :=
    chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
      (I := I) (M := M) g α u_h m 0 h_parent' idx
  exact h_memWkp_0

/-- **`k = 1` corollary.** From chart-`H^{m+1}` of the chart-pushed parent,
every `m`-fold chosen mixed weak partial is `MemW1p 2` on the chart target.
This is the headline `H¹` regularity needed for downstream weak-form
manipulations. -/
theorem chosenMthMixedPartialChartPushedU_memW1p_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (m : ℕ)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m idx)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  have h_parent' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (1 + m) 2
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α) := by
    have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
    rw [h_eq]
    exact h_parent
  have h_memWkp_1 :=
    chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
      (I := I) (M := M) g α u_h m 1 h_parent' idx
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h_memWkp_1
  exact h_memWkp_1

/-- **Local `L²` corollary.** From chart-`H^m` of the chart-pushed parent,
every `m`-fold chosen mixed weak partial is `MemLp 2 (volume.restrict K)`
for every compact `K ⊆ chartTargetEuclid α`. -/
theorem chosenMthMixedPartialChartPushedU_locally_memLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (m : ℕ)
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) m 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
      (I := I) (M := M) α) :
    MemLp
      (chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m idx) 2
      ((volume : Measure EuclN).restrict K) := by
  have h_global := chosenMthMixedPartialChartPushedU_memLp_two
    (I := I) (M := M) g α u_h m h_parent idx
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have h_chart_open :
      IsOpen (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have h_eq : ((volume : Measure EuclN).restrict
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
          (I := I) (M := M) α)).restrict K =
        (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  rw [← h_eq]
  exact h_global.restrict K

end IteratedMixedPartials
end Laplacian
end Analysis
end DifferentialGeometry

end
