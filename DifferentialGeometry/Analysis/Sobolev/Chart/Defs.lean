import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import DifferentialGeometry.Integral.Measure.Properties
import DifferentialGeometry.Integral.L2.CompactSupport
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Chart-based Sobolev space `W^{k,p}_chart(M)` on a smooth manifold

Given a smooth manifold `M` modelled on a finite-dim real inner product space
`E` (via `(I : ModelWithCorners ℝ E H)`), and the canonical chart-atlas
partition of unity `chartAtlasPOU I M`, we define:

* `MemWkpChart g k p u`: the predicate that `u : M → ℝ` is in
  `W^{k,p}_chart(M)` — i.e. each chart-pushed `(ρ_α u) ∘ (extChartAt I α).symm`,
  composed with `(toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)))`,
  is in the iterated Euclidean Sobolev space `W^{k,p}` of the chart target.
* `wkpNormChart g k p u`: the chart-based Sobolev norm.
* `WkpChart g k p`: the subtype of functions satisfying `MemWkpChart`.

We establish:

* `wkpNormChart_eq_tsum`, `MemWkpChart_zero_fun` (basic structural lemmas).
* `WkpChart` carries an `AddCommGroup` structure inherited from `M → ℝ`
  (when arithmetic operations stay inside the predicate, which we check).

Deeper analytical theorems — Banach completeness, atlas independence, smooth
density — require substantial PDE machinery and are not developed here.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart-pushed scalar function: given `u : M → ℝ`, the partition-of-unity
weight `ρ α : M → ℝ`, and a chart `α : M`, return the function on the standard
Euclidean space `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` defined by
`(ρ α u) ∘ (extChartAt I α).symm ∘ toEuclidean.symm`. -/
def chartPushed
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y)) *
      u ((extChartAt I α).symm (toEuclidean.symm y))

/-- The chart-target image of the extended chart at `α`, transferred to
`EuclideanSpace ℝ (Fin (finrank ℝ E))` via `toEuclidean`. -/
def chartTargetEuclid (α : M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  toEuclidean '' (extChartAt I α).target

/-- `MemWkpChart g k p u`: for every chart `α : M` in the canonical atlas, the
chart-pushed function `chartPushed ρ α u` is in `MemWkp k p` of the chart
target image (under `toEuclidean`). The partition of unity `ρ` is the canonical
`chartAtlasPOU I M`. -/
def MemWkpChart [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : Prop :=
  ∀ α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α)

/-- The chart-based `W^{k,p}` norm. We sum, over all chart points `α` in the
canonical atlas, the iterated Euclidean Sobolev norm of the chart-pushed
function. The sum is a `tsum` because the partition of unity is countable. -/
def wkpNormChart [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  ∑' α : M,
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α)

/-- Decomposition of the chart-based norm. -/
theorem wkpNormChart_eq_tsum
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) g k p u =
      ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E)
          k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := rfl

/-- Equivalent membership characterization. -/
theorem MemWkpChart_iff
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    MemWkpChart (I := I) (M := M) g k p u ↔
      ∀ α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E)
          k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := Iff.rfl

omit [IsManifold I ∞ M] in
/-- The chart-pushed function for the zero scalar function is zero. -/
theorem chartPushed_zero
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    chartPushed (I := I) (M := M) ρ α (fun _ => (0 : ℝ)) =
      (fun _ => (0 : ℝ)) := by
  funext y
  unfold chartPushed
  simp

omit [IsManifold I ∞ M] in
/-- The chart target image (under `toEuclidean`) is open in
`EuclideanSpace ℝ (Fin _)` when `I` has no boundary. -/
theorem chartTargetEuclid_isOpen
    [I.Boundaryless] (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chartTargetEuclid
  have hOpenE : IsOpen ((extChartAt I α).target) :=
    isOpen_extChartAt_target (I := I) α
  exact toEuclidean.toHomeomorph.isOpenMap _ hOpenE

/-- Membership of the zero function in `W^{k,p}_chart(M)`. -/
theorem MemWkpChart_zero_fun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemWkpChart (I := I) (M := M) g k p (fun _ : M => (0 : ℝ)) := by
  intro α
  rw [chartPushed_zero]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
    (d := Module.finrank ℝ E) hp (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-- The chart-based norm of the zero function is zero. -/
theorem wkpNormChart_zero_fun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wkpNormChart (I := I) (M := M) g k p (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChart
  have hpt : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (fun _ : M => (0 : ℝ)))
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
    intro α
    rw [chartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_congr hpt]
  exact tsum_zero

omit [IsManifold I ∞ M] in
/-- The chart-pushed function is linear in `u`: `chartPushed ρ α (u + v) = chartPushed ρ α u + chartPushed ρ α v`. -/
theorem chartPushed_add
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (u v : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => u x + v x) =
      (fun y =>
        chartPushed (I := I) (M := M) ρ α u y +
          chartPushed (I := I) (M := M) ρ α v y) := by
  funext y
  unfold chartPushed
  ring

omit [IsManifold I ∞ M] in
/-- The chart-pushed function is linear in `u` for scalar multiples. -/
theorem chartPushed_const_smul
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (c : ℝ) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => c * u x) =
      (fun y => c * chartPushed (I := I) (M := M) ρ α u y) := by
  funext y
  unfold chartPushed
  ring

/-- `MemWkpChart` is closed under addition. -/
theorem MemWkpChart_add
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g k p u)
    (hv : MemWkpChart (I := I) (M := M) g k p v) :
    MemWkpChart (I := I) (M := M) g k p (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

/-- `MemWkpChart` is closed under scalar multiplication. -/
theorem MemWkpChart_const_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g k p u) :
    MemWkpChart (I := I) (M := M) g k p (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

/-- `MemWkpChart` is closed under negation. -/
theorem MemWkpChart_neg
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g k p u) :
    MemWkpChart (I := I) (M := M) g k p (fun x => -u x) := by
  have h := MemWkpChart_const_smul (I := I) (M := M) g hp (-1) hu
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

/-- `MemWkpChart` is closed under subtraction. -/
theorem MemWkpChart_sub
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g k p u)
    (hv : MemWkpChart (I := I) (M := M) g k p v) :
    MemWkpChart (I := I) (M := M) g k p (fun x => u x - v x) := by
  have hneg := MemWkpChart_neg (I := I) (M := M) g hp hv
  have h := MemWkpChart_add (I := I) (M := M) g hp hu hneg
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

/-- The chart-based Sobolev subspace as an `AddSubgroup` of `M → ℝ`, parametrised
by the metric `g`, the order `k`, the exponent `p`, and the assumption `1 ≤ p`. -/
def wkpChartAddSubgroup
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : AddSubgroup (M → ℝ) where
  carrier := { u | MemWkpChart (I := I) (M := M) g k p u }
  zero_mem' := MemWkpChart_zero_fun (I := I) (M := M) g hp
  add_mem' := fun hu hv => MemWkpChart_add (I := I) (M := M) g hp hu hv
  neg_mem' := fun hu => MemWkpChart_neg (I := I) (M := M) g hp hu

/-- The chart-based Sobolev subspace as a `Submodule ℝ` of `M → ℝ`. -/
def wkpChartSubmodule
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Submodule ℝ (M → ℝ) where
  carrier := { u | MemWkpChart (I := I) (M := M) g k p u }
  zero_mem' := MemWkpChart_zero_fun (I := I) (M := M) g hp
  add_mem' := fun hu hv => MemWkpChart_add (I := I) (M := M) g hp hu hv
  smul_mem' := fun c u hu => by
    have h := MemWkpChart_const_smul (I := I) (M := M) g hp c hu
    have hEq : (c • u : M → ℝ) = fun x => c * u x := by
      funext x
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hEq]
    exact h

/-- The chart-based Sobolev space `WkpChart g k p` as a subtype of `M → ℝ`,
implemented as the underlying subtype of `wkpChartSubmodule`. -/
def WkpChart
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  ↥(wkpChartSubmodule (I := I) (M := M) g k p hp)

instance
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    AddCommGroup (WkpChart (I := I) (M := M) g k p hp) :=
  inferInstanceAs (AddCommGroup ↥(wkpChartSubmodule (I := I) (M := M) g k p hp))

instance
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Module ℝ (WkpChart (I := I) (M := M) g k p hp) :=
  inferInstanceAs (Module ℝ ↥(wkpChartSubmodule (I := I) (M := M) g k p hp))

/-- Membership in `W^{k+1,p}_chart` implies membership in `W^{k,p}_chart`. -/
theorem MemWkpChart.le_succ
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemWkpChart (I := I) (M := M) g (k + 1) p u) :
    MemWkpChart (I := I) (M := M) g k p u := by
  intro α
  exact (h α).le_succ

/-- Membership in `W^{k',p}_chart` implies membership in `W^{k,p}_chart`
whenever `k ≤ k'`. -/
theorem MemWkpChart.le_of_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k k' : ℕ} {p : ℝ≥0∞} {u : M → ℝ}
    (hk : k ≤ k') (h : MemWkpChart (I := I) (M := M) g k' p u) :
    MemWkpChart (I := I) (M := M) g k p u := by
  intro α
  exact (h α).le_of_le hk

/-- The chart-pushed-equivalence relation: two functions `u, v : M → ℝ` are
chart-pushed equivalent if every chart-pushed image `chartPushed ρ α u` agrees a.e.
with `chartPushed ρ α v` on the chart target image. -/
def ChartPushedAEEq
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (_g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (u v : M → ℝ) : Prop :=
  ∀ α : M,
    chartPushed (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u
        =ᵐ[MeasureTheory.volume.restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v

/-- `ChartPushedAEEq` is reflexive. -/
theorem ChartPushedAEEq.rfl
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (u : M → ℝ) :
    ChartPushedAEEq (I := I) (M := M) g u u := by
  intro α
  exact Filter.EventuallyEq.rfl

/-- `ChartPushedAEEq` is symmetric. -/
theorem ChartPushedAEEq.symm
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {u v : M → ℝ} (h : ChartPushedAEEq (I := I) (M := M) g u v) :
    ChartPushedAEEq (I := I) (M := M) g v u := by
  intro α
  exact (h α).symm

/-- `ChartPushedAEEq` is transitive. -/
theorem ChartPushedAEEq.trans
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {u v w : M → ℝ}
    (huv : ChartPushedAEEq (I := I) (M := M) g u v)
    (hvw : ChartPushedAEEq (I := I) (M := M) g v w) :
    ChartPushedAEEq (I := I) (M := M) g u w := by
  intro α
  exact (huv α).trans (hvw α)

/-- If `u, v` are chart-pushed-a.e.-equal and one is in `W^{k,p}_chart`, so is
the other. -/
theorem MemWkpChart_congr_chartPushed_ae
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} (huv : ChartPushedAEEq (I := I) (M := M) g u v) :
    MemWkpChart (I := I) (M := M) g k p u ↔
      MemWkpChart (I := I) (M := M) g k p v := by
  refine ⟨fun h α => ?_, fun h α => ?_⟩
  · exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (huv α)).mp (h α)
  · exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (huv α).symm).mp (h α)

/-- The chart-based norm is invariant under chart-by-chart-a.e.-equality of inputs,
provided `1 ≤ p`. -/
theorem wkpNormChart_congr_chartPushed_ae
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} (huv : ChartPushedAEEq (I := I) (M := M) g u v) :
    wkpNormChart (I := I) (M := M) g k p u =
      wkpNormChart (I := I) (M := M) g k p v := by
  unfold wkpNormChart
  refine tsum_congr ?_
  intro α
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (huv α)

/-- The triangle inequality for the chart-based norm. -/
theorem wkpNormChart_add_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g k p u)
    (hv : MemWkpChart (I := I) (M := M) g k p v) :
    wkpNormChart (I := I) (M := M) g k p (fun x => u x + v x) ≤
      wkpNormChart (I := I) (M := M) g k p u +
        wkpNormChart (I := I) (M := M) g k p v := by
  unfold wkpNormChart
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [chartPushed_add]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_add_le
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

/-- The scalar-multiplication identity for the chart-based norm. -/
theorem wkpNormChart_const_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g k p u) :
    wkpNormChart (I := I) (M := M) g k p (fun x => c * u x) =
      ‖c‖ₑ * wkpNormChart (I := I) (M := M) g k p u := by
  unfold wkpNormChart
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [chartPushed_const_smul]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

/-- The chart-based norm is finite for any function in `MemWkpChart`, when `M` is
compact and `1 ≤ p`. (Compactness ensures the partition-of-unity has finitely many
supports.) -/
theorem wkpNormChart_lt_top_of_memWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g k p u) :
    wkpNormChart (I := I) (M := M) g k p u < ⊤ := by
  classical
  unfold wkpNormChart
  set f : M → ℝ≥0∞ := fun α =>
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) with hf_def
  have hPOU_locFin : LocallyFinite
      (fun α : M => Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)) :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).locallyFinite
  have hSupport_finite : {α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)).Nonempty}.Finite :=
    hPOU_locFin.finite_nonempty_of_compact
  have hf_zero_off : ∀ α : M, (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support (DifferentialGeometry.Integral.Measure.chartAtlasPOU
          I M α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  set S : Set M := {α : M | (Function.support
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)).Nonempty}
      with hS_def
  have hS_finite : S.Finite := hSupport_finite
  have hf_supp_S : Function.support f ⊆ S := by
    intro α hα
    by_contra hαS
    apply hα
    have h_not_in_S : (Function.support
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)).Nonempty := by
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
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α hempty
  rw [htsum_eq]
  apply ENNReal.sum_lt_top.mpr
  intro α _
  rw [hf_def]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_lt_top_of_memWkp
    (d := Module.finrank ℝ E) (hu α)

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
