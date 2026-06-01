import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.TwiceBilinearH1Compl

/-!
# Iterated Frechet derivatives of the smooth chart-target coefficients

The chart-target Leibniz cross-coefficients `weightedInvGramOnEuclid g α i j`
and `densityOnEuclid g α` are smooth real-valued functions on the open chart
target `chartTargetEuclid α ⊆ EuclideanSpace ℝ (Fin n)`. Their first
coordinate Frechet derivatives are packaged as `weightedInvGramDerivOnEuclid`
and `densityDerivOnEuclid`, and the mixed second-order derivatives as
`weightedInvGramSecondDerivOnEuclid` and `densitySecondDerivOnEuclid`.

This module generalises both layers to a single polymorphic-in-`m` recursive
definition that produces the `m`-fold mixed Frechet derivative against an
arbitrary multi-index `idx : Fin m → Fin n` of coordinate directions, together
with the corresponding polymorphic smoothness, continuity, and
boundedness-on-compact-subsets lemmas.

## Indexing convention

The multi-index `idx : Fin m → Fin n` encodes the differentiation directions.
The recursive step

```
weightedInvGramMthDerivOnEuclid g α i j (m+1) idx y
  := fderiv ℝ (weightedInvGramMthDerivOnEuclid g α i j m (Fin.init idx)) y
        (EuclideanSpace.single (idx (Fin.last m)) 1)
```

treats the **last** entry `idx (Fin.last m)` as the **outermost** (final)
differentiation direction. The remaining inner entries `Fin.init idx` are
fed recursively to produce the inner `m`-fold derivative. This convention is
chosen to match the layering used by the analogous polymorphic-in-`m`
multi-mixed-partial machinery for chart-pushed `H¹` representatives.

## Main definitions

* `weightedInvGramMthDerivOnEuclid g α i j m idx` — the `m`-fold mixed Frechet
  derivative of `weightedInvGramOnEuclid g α i j` in the directions encoded
  by `idx`.
* `densityMthDerivOnEuclid g α m idx` — the `m`-fold mixed Frechet
  derivative of `densityOnEuclid g α` in the directions encoded by `idx`.

## Compatibility theorems

* `*_zero` — at `m = 0`, the polymorphic derivative coincides with the
  underlying coefficient.
* `*_one_eq_*DerivOnEuclid` — at `m = 1`, the polymorphic derivative coincides
  with the hard-coded first-derivative version.
* `*_two_eq_*SecondDerivOnEuclid` — at `m = 2`, the polymorphic derivative
  coincides with the hard-coded mixed-second-derivative version.

## Polymorphic regularity

* `*_contDiffOn` — the `m`-fold mixed derivative is `C^∞` on
  `chartTargetEuclid α` for arbitrary `m` and `idx`. Proof: induction on `m`,
  using smoothness of the base coefficient at the base case and the
  smooth-fderiv-of-smooth-function step at the inductive case.
* `*_continuousOn` — continuity wrapper.
* `*_bounded_on_compact` — a `C^∞` function is in particular continuous on
  the open chart target, so attains a uniform bound on every compact subset.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedLeibnizCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffTwiceChartBilinearH1Compl

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The `m`-fold mixed Frechet derivative of `weightedInvGramOnEuclid g α i j`
in the directions encoded by `idx : Fin m → Fin n`. Recursive definition:
at the inductive step, the **last** entry `idx (Fin.last m)` is the
outermost (final) differentiation direction. -/
noncomputable def weightedInvGramMthDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _, y => weightedInvGramOnEuclid (I := I) g α i j y
  | m + 1, idx, y =>
      (fderiv ℝ
          (weightedInvGramMthDerivOnEuclid g α i j m (Fin.init idx)) y)
        (EuclideanSpace.single (idx (Fin.last m)) 1)

/-- The `m`-fold mixed Frechet derivative of `densityOnEuclid g α` in the
directions encoded by `idx : Fin m → Fin n`. Recursive definition: at the
inductive step, the **last** entry `idx (Fin.last m)` is the outermost
(final) differentiation direction. -/
noncomputable def densityMthDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (m : ℕ), (Fin m → Fin (Module.finrank ℝ E)) → EuclN → ℝ
  | 0, _, y => densityOnEuclid (I := I) g α y
  | m + 1, idx, y =>
      (fderiv ℝ
          (densityMthDerivOnEuclid g α m (Fin.init idx)) y)
        (EuclideanSpace.single (idx (Fin.last m)) 1)

/-- Definitional unfolding at `m = 0`: the polymorphic derivative reduces to
the underlying weighted-inverse-Gram coefficient. -/
@[simp] theorem weightedInvGramMthDerivOnEuclid_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    (idx : Fin 0 → Fin (Module.finrank ℝ E)) (y : EuclN) :
    weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j 0 idx y =
      weightedInvGramOnEuclid (I := I) g α i j y := rfl

/-- Definitional unfolding at `m + 1`. -/
theorem weightedInvGramMthDerivOnEuclid_succ
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (m : ℕ)
    (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)) (y : EuclN) :
    weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j (m + 1) idx y =
      (fderiv ℝ
          (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
            g α i j m (Fin.init idx)) y)
        (EuclideanSpace.single (idx (Fin.last m)) 1) := rfl

/-- Definitional unfolding at `m = 0`: the polymorphic density derivative
reduces to the underlying density coefficient. -/
@[simp] theorem densityMthDerivOnEuclid_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (idx : Fin 0 → Fin (Module.finrank ℝ E)) (y : EuclN) :
    densityMthDerivOnEuclid (I := I) (M := M) g α 0 idx y =
      densityOnEuclid (I := I) g α y := rfl

/-- Definitional unfolding at `m + 1`. -/
theorem densityMthDerivOnEuclid_succ
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    (idx : Fin (m + 1) → Fin (Module.finrank ℝ E)) (y : EuclN) :
    densityMthDerivOnEuclid (I := I) (M := M) g α (m + 1) idx y =
      (fderiv ℝ
          (densityMthDerivOnEuclid (I := I) (M := M)
            g α m (Fin.init idx)) y)
        (EuclideanSpace.single (idx (Fin.last m)) 1) := rfl

/-- The `m = 1` instance: for any `idx : Fin 1 → Fin n`, the polymorphic
mixed Frechet derivative agrees on the nose with
`weightedInvGramDerivOnEuclid g α i j (idx 0)`. -/
theorem weightedInvGramMthDerivOnEuclid_one_eq_weightedInvGramDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    (idx : Fin 1 → Fin (Module.finrank ℝ E)) :
    weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j 1 idx =
      weightedInvGramDerivOnEuclid (I := I) g α i j (idx 0) := by
  funext y
  rfl

/-- The `m = 1` instance: for any `idx : Fin 1 → Fin n`, the polymorphic
density derivative agrees on the nose with `densityDerivOnEuclid g α (idx 0)`. -/
theorem densityMthDerivOnEuclid_one_eq_densityDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (idx : Fin 1 → Fin (Module.finrank ℝ E)) :
    densityMthDerivOnEuclid (I := I) (M := M) g α 1 idx =
      densityDerivOnEuclid (I := I) g α (idx 0) := by
  funext y
  rfl

/-- The `m = 2` instance: for any `idx : Fin 2 → Fin n`, the polymorphic
mixed Frechet derivative agrees on the nose with
`weightedInvGramSecondDerivOnEuclid g α i j (idx 0) (idx 1)`. -/
theorem weightedInvGramMthDerivOnEuclid_two_eq_weightedInvGramSecondDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    (idx : Fin 2 → Fin (Module.finrank ℝ E)) :
    weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j 2 idx =
      weightedInvGramSecondDerivOnEuclid (I := I) g α i j (idx 0) (idx 1) := by
  funext y
  rw [weightedInvGramMthDerivOnEuclid_succ]
  have h_last_1 : (Fin.last 1 : Fin 2) = 1 := rfl
  rw [h_last_1]
  rw [weightedInvGramMthDerivOnEuclid_one_eq_weightedInvGramDerivOnEuclid]
  have h_init_0 : (Fin.init idx) 0 = idx 0 := by
    simp [Fin.init]
  rw [h_init_0]
  rfl

/-- The `m = 2` instance: for any `idx : Fin 2 → Fin n`, the polymorphic
density derivative agrees on the nose with
`densitySecondDerivOnEuclid g α (idx 0) (idx 1)`. -/
theorem densityMthDerivOnEuclid_two_eq_densitySecondDerivOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (idx : Fin 2 → Fin (Module.finrank ℝ E)) :
    densityMthDerivOnEuclid (I := I) (M := M) g α 2 idx =
      densitySecondDerivOnEuclid (I := I) g α (idx 0) (idx 1) := by
  funext y
  rw [densityMthDerivOnEuclid_succ]
  have h_last_1 : (Fin.last 1 : Fin 2) = 1 := rfl
  rw [h_last_1]
  rw [densityMthDerivOnEuclid_one_eq_densityDerivOnEuclid]
  have h_init_0 : (Fin.init idx) 0 = idx 0 := by
    simp [Fin.init]
  rw [h_init_0]
  rfl

/-- Polymorphic smoothness of the `m`-fold mixed Frechet derivative of
`weightedInvGramOnEuclid g α i j` on the open chart target. Proof is by
induction on `m`: the base case is the smoothness of
`weightedInvGramOnEuclid`, and the inductive step uses the smooth-fderiv
characterisation of `C^∞`-on-open and post-composition with the smooth
linear evaluation map `L ↦ L(v)`. -/
lemma weightedInvGramMthDerivOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (m : ℕ)
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
      g α i j m idx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      have h_eq : weightedInvGramMthDerivOnEuclid (I := I) (M := M)
          g α i j 0 idx = weightedInvGramOnEuclid (I := I) g α i j := by
        funext y
        exact weightedInvGramMthDerivOnEuclid_zero
          (I := I) (M := M) g α i j idx y
      rw [h_eq]
      exact weightedInvGramOnEuclid_contDiffOn (I := I) g α i j
  | succ m ih =>
      have h_inner :
          ContDiffOn ℝ ∞ (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
            g α i j m (Fin.init idx))
            (chartTargetEuclid (I := I) (M := M) α) :=
        ih (Fin.init idx)
      have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_fderiv :
          ContDiffOn ℝ ∞ (fun y => fderiv ℝ
            (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
              g α i j m (Fin.init idx)) y)
            (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_inner).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) =>
            L (EuclideanSpace.single (idx (Fin.last m)) 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single (idx (Fin.last m)) (1 : ℝ))).contDiff
      have h_eq : weightedInvGramMthDerivOnEuclid (I := I) (M := M)
          g α i j (m + 1) idx =
          (fun y => (fderiv ℝ
              (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
                g α i j m (Fin.init idx)) y)
            (EuclideanSpace.single (idx (Fin.last m)) 1)) := by
        funext y
        exact weightedInvGramMthDerivOnEuclid_succ
          (I := I) (M := M) g α i j m idx y
      rw [h_eq]
      exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

/-- Polymorphic smoothness of the `m`-fold mixed Frechet derivative of
`densityOnEuclid g α` on the open chart target. -/
lemma densityMthDerivOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (m : ℕ) (idx : Fin m → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (densityMthDerivOnEuclid (I := I) (M := M) g α m idx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      have h_eq : densityMthDerivOnEuclid (I := I) (M := M)
          g α 0 idx = densityOnEuclid (I := I) g α := by
        funext y
        exact densityMthDerivOnEuclid_zero
          (I := I) (M := M) g α idx y
      rw [h_eq]
      exact densityOnEuclid_contDiffOn (I := I) g α
  | succ m ih =>
      have h_inner :
          ContDiffOn ℝ ∞ (densityMthDerivOnEuclid (I := I) (M := M)
            g α m (Fin.init idx))
            (chartTargetEuclid (I := I) (M := M) α) :=
        ih (Fin.init idx)
      have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_fderiv :
          ContDiffOn ℝ ∞ (fun y => fderiv ℝ
            (densityMthDerivOnEuclid (I := I) (M := M)
              g α m (Fin.init idx)) y)
            (chartTargetEuclid (I := I) (M := M) α) :=
        ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_inner).2
      have h_eval : ContDiff ℝ ∞
          (fun (L : EuclN →L[ℝ] ℝ) =>
            L (EuclideanSpace.single (idx (Fin.last m)) 1)) :=
        (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single (idx (Fin.last m)) (1 : ℝ))).contDiff
      have h_eq : densityMthDerivOnEuclid (I := I) (M := M)
          g α (m + 1) idx =
          (fun y => (fderiv ℝ
              (densityMthDerivOnEuclid (I := I) (M := M)
                g α m (Fin.init idx)) y)
            (EuclideanSpace.single (idx (Fin.last m)) 1)) := by
        funext y
        exact densityMthDerivOnEuclid_succ
          (I := I) (M := M) g α m idx y
      rw [h_eq]
      exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

/-- Continuity wrapper for `weightedInvGramMthDerivOnEuclid` on the chart
target. -/
lemma weightedInvGramMthDerivOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (m : ℕ)
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    ContinuousOn (weightedInvGramMthDerivOnEuclid (I := I) (M := M)
      g α i j m idx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (weightedInvGramMthDerivOnEuclid_contDiffOn
    (I := I) (M := M) g α i j m idx).continuousOn

/-- Continuity wrapper for `densityMthDerivOnEuclid` on the chart target. -/
lemma densityMthDerivOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (m : ℕ) (idx : Fin m → Fin (Module.finrank ℝ E)) :
    ContinuousOn (densityMthDerivOnEuclid (I := I) (M := M) g α m idx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (densityMthDerivOnEuclid_contDiffOn
    (I := I) (M := M) g α m idx).continuousOn

/-- The polymorphic Leibniz cross-coefficient
`weightedInvGramMthDerivOnEuclid` is bounded on every compact subset of
`chartTargetEuclid α`. -/
lemma weightedInvGramMthDerivOnEuclid_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (m : ℕ)
    (idx : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K,
      |weightedInvGramMthDerivOnEuclid (I := I) (M := M)
        g α i j m idx y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn
      (weightedInvGramMthDerivOnEuclid (I := I) (M := M) g α i j m idx) K :=
    (weightedInvGramMthDerivOnEuclid_continuousOn
      (I := I) (M := M) g α i j m idx).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramMthDerivOnEuclid (I := I) (M := M)
        g α i j m idx y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|weightedInvGramMthDerivOnEuclid (I := I) (M := M)
    g α i j m idx y_max|, ?_⟩
  intro y hy
  exact h_max hy

/-- The polymorphic Leibniz cross-coefficient `densityMthDerivOnEuclid` is
bounded on every compact subset of `chartTargetEuclid α`. -/
lemma densityMthDerivOnEuclid_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (m : ℕ) (idx : Fin m → Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK_compact : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, ∀ y ∈ K,
      |densityMthDerivOnEuclid (I := I) (M := M) g α m idx y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_K_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have h_cont_K : ContinuousOn
      (densityMthDerivOnEuclid (I := I) (M := M) g α m idx) K :=
    (densityMthDerivOnEuclid_continuousOn
      (I := I) (M := M) g α m idx).mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |densityMthDerivOnEuclid (I := I) (M := M)
        g α m idx y|) K :=
    continuous_abs.comp_continuousOn h_cont_K
  obtain ⟨y_max, hy_max, h_max⟩ :=
    hK_compact.exists_isMaxOn h_K_ne h_abs_K
  refine ⟨|densityMthDerivOnEuclid (I := I) (M := M)
    g α m idx y_max|, ?_⟩
  intro y hy
  exact h_max hy

end IteratedLeibnizCoefficients
end Laplacian
end Analysis
end DifferentialGeometry

end
