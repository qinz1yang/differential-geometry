import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevHalfSpace
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Integral.L2.CompactSupport
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance

/-!
# Chart-based Sobolev space `W^{k,p}_chart(M)` on a smooth manifold-with-boundary

This is the with-boundary parallel of `Analysis/Sobolev/Chart.lean`. We mirror
the boundaryless predicate `MemWkpChart` and norm `wkpNormChart`, replacing the
underlying open-set Sobolev predicate by the half-space-friendly Dirichlet
variant from `EuclideanIteratedSobolevHalfSpace.lean`.

Specifically, given a smooth manifold `M` modelled on the canonical Euclidean
half-space `EuclideanHalfSpace n` (via `modelWithCornersEuclideanHalfSpace n`),
each extended chart target `(extChartAt I α).target` is a subset of
`EuclideanSpace ℝ (Fin n)` that is *relatively open in the closed half-space*
`{y : EuclideanSpace ℝ (Fin n) | 0 ≤ y 0}` — see
`extChartAt_target_isHalfSpaceRelOpen`. We then say:

* `MemWkpChart g k p u`: the predicate that, for every chart `α : M`, the
  chart-pushed function `(ρ_α u) ∘ (extChartAt I α).symm` is in
  `W^{k,p}_0(chart-target)` (Dirichlet half-space variant).
* `wkpNormChart g k p u`: the corresponding norm, given as a `tsum` over chart
  index points.

We establish the analogues of every structural / closure / a.e.-invariance /
norm theorem from the boundaryless chart-Sobolev module.

## Scope note

This module is restricted to manifolds modelled on the canonical
`EuclideanHalfSpace n`. The abstract `[HasSmoothBoundary E H I]` typeclass
generally does not provide enough alignment between the boundary direction in
`E` and the canonical coordinate-`0` half-space in
`EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` for chart targets to be
half-space-friendly under the standard Mathlib equivalence
`toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`. The
present formulation works directly on `EuclideanSpace ℝ (Fin n)` (the model
space of `EuclideanHalfSpace n`), avoiding any transport.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

/-- The chart-pushed scalar function: given `u : M → ℝ`, the partition-of-unity
weight `ρ α : M → ℝ`, and a chart `α : M`, return the function on the standard
Euclidean space `EuclideanSpace ℝ (Fin n)` defined by
`(ρ α u) ∘ (extChartAt I α).symm`. -/
def chartPushed
    (ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M Set.univ)
    (α : M) (u : M → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun y =>
    (ρ α : C^∞⟮modelWithCornersEuclideanHalfSpace n, M; ℝ⟯)
        ((extChartAt (modelWithCornersEuclideanHalfSpace n) α).symm y) *
      u ((extChartAt (modelWithCornersEuclideanHalfSpace n) α).symm y)

/-- The chart-target set in `EuclideanSpace ℝ (Fin n)`. For `M` modelled on
`EuclideanHalfSpace n`, this is precisely `(extChartAt I α).target` — a subset
of `EuclideanSpace ℝ (Fin n)` that is half-space-friendly. -/
def chartTargetEuclid (α : M) : Set (EuclideanSpace ℝ (Fin n)) :=
  (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target

/-- Each chart target is `IsHalfSpaceRelOpen`, i.e., the intersection of an
open subset of `EuclideanSpace ℝ (Fin n)` with the closed half-space
`{y | 0 ≤ y 0}`. -/
theorem chartTargetEuclid_isHalfSpaceRelOpen (α : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.IsHalfSpaceRelOpen (d := n)
      (chartTargetEuclid (n := n) (M := M) α) :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.extChartAt_target_isHalfSpaceRelOpen
    (n := n) (M := M) α

/-- `MemWkpChart g k p u`: for every chart `α : M` in the canonical atlas, the
chart-pushed function `chartPushed ρ α u` is in `MemWkpHalfSpace k p` of the
chart target. The partition of unity `ρ` is the canonical
`chartAtlasPOU I M`. -/
def MemWkpChart [T2Space M] [SigmaCompactSpace M]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α)

/-- The chart-based half-space `W^{k,p}` norm. We sum, over all chart points
`α : M` in the canonical atlas, the half-space iterated `W^{k,p}` norm of the
chart-pushed function. -/
def wkpNormChart [T2Space M] [SigmaCompactSpace M]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  ∑' α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α)

/-- Decomposition of the chart-based norm. -/
theorem wkpNormChart_eq_tsum
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChart (n := n) (M := M) g k p u =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) k p
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) := rfl

/-- Equivalent membership characterization. -/
theorem MemWkpChart_iff
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    MemWkpChart (n := n) (M := M) g k p u ↔
      ∀ α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
          (d := n) k p
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) := Iff.rfl

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
/-- The chart-pushed function for the zero scalar function is zero. -/
theorem chartPushed_zero
    (ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M Set.univ)
    (α : M) :
    chartPushed (n := n) (M := M) ρ α (fun _ => (0 : ℝ)) =
      (fun _ => (0 : ℝ)) := by
  funext y
  unfold chartPushed
  simp

/-- Membership of the zero function in `W^{k,p}_chart(M)`. -/
theorem MemWkpChart_zero_fun
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemWkpChart (n := n) (M := M) g k p (fun _ : M => (0 : ℝ)) := by
  intro α
  rw [chartPushed_zero]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_zero_fun
    (d := n) hp (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)

/-- The chart-based norm of the zero function is zero. -/
theorem wkpNormChart_zero_fun
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wkpNormChart (n := n) (M := M) g k p (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChart
  have hpt : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
        (d := n) k p
        (chartPushed (n := n) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M) α
          (fun _ : M => (0 : ℝ)))
        (chartTargetEuclid (n := n) (M := M) α) = 0 := by
    intro α
    rw [chartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_fun_zero
      (d := n) hp
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  rw [tsum_congr hpt]
  exact tsum_zero

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
/-- The chart-pushed function is linear in `u`:
`chartPushed ρ α (u + v) = chartPushed ρ α u + chartPushed ρ α v`. -/
theorem chartPushed_add
    (ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M Set.univ)
    (α : M) (u v : M → ℝ) :
    chartPushed (n := n) (M := M) ρ α (fun x => u x + v x) =
      (fun y =>
        chartPushed (n := n) (M := M) ρ α u y +
          chartPushed (n := n) (M := M) ρ α v y) := by
  funext y
  unfold chartPushed
  ring

omit [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] in
/-- The chart-pushed function is linear in `u` for scalar multiples. -/
theorem chartPushed_const_smul
    (ρ : SmoothPartitionOfUnity M (modelWithCornersEuclideanHalfSpace n) M Set.univ)
    (α : M) (c : ℝ) (u : M → ℝ) :
    chartPushed (n := n) (M := M) ρ α (fun x => c * u x) =
      (fun y => c * chartPushed (n := n) (M := M) ρ α u y) := by
  funext y
  unfold chartPushed
  ring

/-- `MemWkpChart` is closed under addition. -/
theorem MemWkpChart_add
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k p u)
    (hv : MemWkpChart (n := n) (M := M) g k p v) :
    MemWkpChart (n := n) (M := M) g k p (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.add
    (d := n) hp
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu α) (hv α)

/-- `MemWkpChart` is closed under scalar multiplication. -/
theorem MemWkpChart_const_smul
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k p u) :
    MemWkpChart (n := n) (M := M) g k p (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace.const_smul
    (d := n) hp
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu α) c

/-- `MemWkpChart` is closed under negation. -/
theorem MemWkpChart_neg
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k p u) :
    MemWkpChart (n := n) (M := M) g k p (fun x => -u x) := by
  have h := MemWkpChart_const_smul (n := n) (M := M) g hp (-1) hu
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

/-- `MemWkpChart` is closed under subtraction. -/
theorem MemWkpChart_sub
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k p u)
    (hv : MemWkpChart (n := n) (M := M) g k p v) :
    MemWkpChart (n := n) (M := M) g k p (fun x => u x - v x) := by
  have hneg := MemWkpChart_neg (n := n) (M := M) g hp hv
  have h := MemWkpChart_add (n := n) (M := M) g hp hu hneg
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

/-- The chart-based Sobolev subspace as an `AddSubgroup` of `M → ℝ`,
parametrised by the metric `g`, the order `k`, the exponent `p`, and the
assumption `1 ≤ p`. -/
def wkpChartAddSubgroup
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : AddSubgroup (M → ℝ) where
  carrier := { u | MemWkpChart (n := n) (M := M) g k p u }
  zero_mem' := MemWkpChart_zero_fun (n := n) (M := M) g hp
  add_mem' := fun hu hv => MemWkpChart_add (n := n) (M := M) g hp hu hv
  neg_mem' := fun hu => MemWkpChart_neg (n := n) (M := M) g hp hu

/-- The chart-based Sobolev subspace as a `Submodule ℝ` of `M → ℝ`. -/
def wkpChartSubmodule
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Submodule ℝ (M → ℝ) where
  carrier := { u | MemWkpChart (n := n) (M := M) g k p u }
  zero_mem' := MemWkpChart_zero_fun (n := n) (M := M) g hp
  add_mem' := fun hu hv => MemWkpChart_add (n := n) (M := M) g hp hu hv
  smul_mem' := fun c u hu => by
    have h := MemWkpChart_const_smul (n := n) (M := M) g hp c hu
    have hEq : (c • u : M → ℝ) = fun x => c * u x := by
      funext x
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hEq]
    exact h

/-- The chart-based Sobolev space `WkpChart g k p` as a subtype of `M → ℝ`,
implemented as the underlying subtype of `wkpChartSubmodule`. -/
def WkpChart
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  ↥(wkpChartSubmodule (n := n) (M := M) g k p hp)

instance
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    AddCommGroup (WkpChart (n := n) (M := M) g k p hp) :=
  inferInstanceAs (AddCommGroup ↥(wkpChartSubmodule (n := n) (M := M) g k p hp))

instance
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Module ℝ (WkpChart (n := n) (M := M) g k p hp) :=
  inferInstanceAs (Module ℝ ↥(wkpChartSubmodule (n := n) (M := M) g k p hp))

/-- Membership in `W^{k+1,p}_chart` implies membership in `W^{k,p}_chart`. -/
theorem MemWkpChart.le_succ
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemWkpChart (n := n) (M := M) g (k + 1) p u) :
    MemWkpChart (n := n) (M := M) g k p u := by
  intro α
  exact (h α).le_succ

/-- Membership in `W^{k',p}_chart` implies membership in `W^{k,p}_chart`
whenever `k ≤ k'`. -/
theorem MemWkpChart.le_of_le
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k k' : ℕ} {p : ℝ≥0∞} {u : M → ℝ}
    (hk : k ≤ k') (h : MemWkpChart (n := n) (M := M) g k' p u) :
    MemWkpChart (n := n) (M := M) g k p u := by
  intro α
  exact (h α).le_of_le hk

/-- The chart-pushed-equivalence relation: two functions `u, v : M → ℝ` are
chart-pushed equivalent if every chart-pushed image `chartPushed ρ α u` agrees
a.e. with `chartPushed ρ α v` on the *interior part* of the chart target image.
The interior part is `chartTarget ∩ openHalfSpace`, which is open in `E` and
where the underlying half-space-Sobolev predicate is evaluated. -/
def ChartPushedAEEq
    [T2Space M] [SigmaCompactSpace M]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (u v : M → ℝ) : Prop :=
  ∀ α : M,
    chartPushed (n := n) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M) α u
        =ᵐ[MeasureTheory.volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))]
      chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α v

/-- `ChartPushedAEEq` is reflexive. -/
theorem ChartPushedAEEq.rfl
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (u : M → ℝ) :
    ChartPushedAEEq (n := n) (M := M) g u u := by
  intro α
  exact Filter.EventuallyEq.rfl

/-- `ChartPushedAEEq` is symmetric. -/
theorem ChartPushedAEEq.symm
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {u v : M → ℝ} (h : ChartPushedAEEq (n := n) (M := M) g u v) :
    ChartPushedAEEq (n := n) (M := M) g v u := by
  intro α
  exact (h α).symm

/-- `ChartPushedAEEq` is transitive. -/
theorem ChartPushedAEEq.trans
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {u v w : M → ℝ}
    (huv : ChartPushedAEEq (n := n) (M := M) g u v)
    (hvw : ChartPushedAEEq (n := n) (M := M) g v w) :
    ChartPushedAEEq (n := n) (M := M) g u w := by
  intro α
  exact (huv α).trans (hvw α)

/-- If `u, v` are chart-pushed-a.e.-equal and one is in `W^{k,p}_chart`, so is
the other. -/
theorem MemWkpChart_congr_chartPushed_ae
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} (huv : ChartPushedAEEq (n := n) (M := M) g u v) :
    MemWkpChart (n := n) (M := M) g k p u ↔
      MemWkpChart (n := n) (M := M) g k p v := by
  refine ⟨fun h α => ?_, fun h α => ?_⟩
  · exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae
      (d := n) hp
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
      (huv α)).mp (h α)
  · exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace_congr_ae
      (d := n) hp
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
      (huv α).symm).mp (h α)

/-- The chart-based norm is invariant under chart-by-chart-a.e.-equality of
inputs, provided `1 ≤ p`. -/
theorem wkpNormChart_congr_chartPushed_ae
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} (huv : ChartPushedAEEq (n := n) (M := M) g u v) :
    wkpNormChart (n := n) (M := M) g k p u =
      wkpNormChart (n := n) (M := M) g k p v := by
  unfold wkpNormChart
  refine tsum_congr ?_
  intro α
  unfold DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := n) hp
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace_isOpen
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α))
    (huv α)

/-- The triangle inequality for the chart-based norm. -/
theorem wkpNormChart_add_le
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k p u)
    (hv : MemWkpChart (n := n) (M := M) g k p v) :
    wkpNormChart (n := n) (M := M) g k p (fun x => u x + v x) ≤
      wkpNormChart (n := n) (M := M) g k p u +
        wkpNormChart (n := n) (M := M) g k p v := by
  unfold wkpNormChart
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_add_le
    (d := n) hp
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu α) (hv α)

/-- The scalar-multiplication identity for the chart-based norm. -/
theorem wkpNormChart_const_smul
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k p u) :
    wkpNormChart (n := n) (M := M) g k p (fun x => c * u x) =
      ‖c‖ₑ * wkpNormChart (n := n) (M := M) g k p u := by
  unfold wkpNormChart
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_const_smul
    (d := n) hp
    (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
    (hu α) c

/-- The chart-based norm is finite for any function in `MemWkpChart`, when `M`
is compact and `1 ≤ p`. (Compactness ensures the partition-of-unity has
finitely many supports.) -/
theorem wkpNormChart_lt_top_of_memWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (n := n) (M := M) g k p u) :
    wkpNormChart (n := n) (M := M) g k p u < ⊤ := by
  classical
  unfold wkpNormChart
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α) with hf_def
  have hPOU_locFin : LocallyFinite
      (fun α : M => Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU
      (modelWithCornersEuclideanHalfSpace n) M).locallyFinite
  have hSupport_finite : {α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty}.Finite :=
    hPOU_locFin.finite_nonempty_of_compact
  have hf_zero_off : ∀ α : M, (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
      (d := n) k p
      (chartPushed (n := n) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M) α u)
      (chartTargetEuclid (n := n) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_zero_fun_zero
      (d := n) hp
      (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
  set S : Set M := {α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU
        (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty}
      with hS_def
  have hS_finite : S.Finite := hSupport_finite
  have hf_supp_S : Function.support f ⊆ S := by
    intro α hα
    by_contra hαS
    apply hα
    have h_not_in_S : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α h_not_in_S
  have htsum_eq : ∑' α : M, f α = ∑ α ∈ hS_finite.toFinset, f α := by
    rw [tsum_eq_sum]
    intro α hα
    have hαS : α ∉ S := by
      intro hαS
      apply hα
      exact (Set.Finite.mem_toFinset _).mpr hαS
    have hempty : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU
            (modelWithCornersEuclideanHalfSpace n) M α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α hempty
  rw [htsum_eq]
  apply ENNReal.sum_lt_top.mpr
  intro α _
  rw [hf_def]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace_lt_top_of_memWkpHalfSpace
    (hu α)

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
