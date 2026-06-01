import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.NullSubmodule
import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Seminormed and normed structures on the chart-based Sobolev space `W^{k,p}_chart(M)` with boundary

Building on `WithBoundary/Chart.lean`, we equip the subtype
`WkpChart g k p hp := ↥(wkpChartSubmodule g k p hp)` with a seminormed real
vector-space structure, using the chart-based half-space-Sobolev norm
`wkpNormChart g k p u` (taken in real form via `ENNReal.toReal`).

For compact `M` the norm is finite for any element of `WkpChart`, and the
three core seminorm axioms (nonnegativity, homogeneity, triangle) are direct
consequences of the `wkpNormChart` triangle and scalar-multiplication
identities established in `WithBoundary/Chart.lean`.

The standard quotient `SeparationQuotient (WkpChart …)` then carries a
`NormedAddCommGroup` structure (Mathlib's `SeparationQuotient` machinery),
with the canonical projection providing a continuous linear surjection.
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

/-- Real-valued (`ℝ≥0∞.toReal`) version of the chart-based half-space-Sobolev
norm. -/
def wkpNormChartReal
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : ℝ :=
  (wkpNormChart (n := n) (M := M) g k p u).toReal

@[simp]
lemma wkpNormChartReal_def
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChartReal (n := n) (M := M) g k p u =
      (wkpNormChart (n := n) (M := M) g k p u).toReal := rfl

/-- The real-valued chart-based norm is non-negative. -/
lemma wkpNormChartReal_nonneg
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    0 ≤ wkpNormChartReal (n := n) (M := M) g k p u :=
  ENNReal.toReal_nonneg

/-- The real-valued chart-based norm of the zero function is zero. -/
lemma wkpNormChartReal_zero
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wkpNormChartReal (n := n) (M := M) g k p (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChartReal
  rw [wkpNormChart_zero_fun (n := n) (M := M) g hp]
  simp

/-- The triangle inequality for the real-valued chart-based norm, when both
inputs are in `MemWkpChart` and the manifold is compact. -/
lemma wkpNormChartReal_add_le
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k p u)
    (hv : MemWkpChart (n := n) (M := M) g k p v) :
    wkpNormChartReal (n := n) (M := M) g k p (fun x => u x + v x) ≤
      wkpNormChartReal (n := n) (M := M) g k p u +
        wkpNormChartReal (n := n) (M := M) g k p v := by
  unfold wkpNormChartReal
  have hu_lt : wkpNormChart (n := n) (M := M) g k p u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp hu
  have hv_lt : wkpNormChart (n := n) (M := M) g k p v < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp hv
  have hu_ne : wkpNormChart (n := n) (M := M) g k p u ≠ ⊤ := hu_lt.ne
  have hv_ne : wkpNormChart (n := n) (M := M) g k p v ≠ ⊤ := hv_lt.ne
  have hSum_le := wkpNormChart_add_le (n := n) (M := M) g hp hu hv
  have hRHS_ne : wkpNormChart (n := n) (M := M) g k p u +
      wkpNormChart (n := n) (M := M) g k p v ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hu_ne, hv_ne⟩
  have hToReal := ENNReal.toReal_mono hRHS_ne hSum_le
  rw [ENNReal.toReal_add hu_ne hv_ne] at hToReal
  exact hToReal

/-- The real-valued chart-based norm satisfies homogeneity:
`‖c • u‖ = ‖c‖ * ‖u‖`. -/
lemma wkpNormChartReal_const_smul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ} (hu : MemWkpChart (n := n) (M := M) g k p u) :
    wkpNormChartReal (n := n) (M := M) g k p (fun x => c * u x) =
      ‖c‖ * wkpNormChartReal (n := n) (M := M) g k p u := by
  unfold wkpNormChartReal
  rw [wkpNormChart_const_smul (n := n) (M := M) g hp c hu]
  rw [ENNReal.toReal_mul, toReal_enorm]

/-- The underlying `M → ℝ` function of an element `u : WkpChart g k p hp`.
Implementation: `WkpChart` is by definition the submodule subtype, so we
extract `.val` directly. -/
def wkpChartFun
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (n := n) (M := M) g k p hp) : M → ℝ :=
  Subtype.val (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (n := n) (M := M) g k p hp) u

/-- The membership property of the underlying function of an element of
`WkpChart`. -/
lemma wkpChartFun_memWkpChart
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (n := n) (M := M) g k p hp) :
    MemWkpChart (n := n) (M := M) g k p (wkpChartFun u) :=
  Subtype.property
    (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (n := n) (M := M) g k p hp) u

@[simp]
lemma wkpChartFun_add
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u v : WkpChart (n := n) (M := M) g k p hp) :
    wkpChartFun (u + v) = fun x => wkpChartFun u x + wkpChartFun v x := by
  ext x
  rfl

@[simp]
lemma wkpChartFun_smul
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (c : ℝ) (u : WkpChart (n := n) (M := M) g k p hp) :
    wkpChartFun (c • u) = fun x => c * wkpChartFun u x := by
  ext x
  rfl

/-- `Norm` instance on `WkpChart g k p hp`, with norm
`(wkpNormChart g k p u).toReal`. -/
instance instNormWkpChart
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Norm (WkpChart (n := n) (M := M) g k p hp) where
  norm u := (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal

/-- The norm of `u : WkpChart g k p hp` equals
`(wkpNormChart g k p (wkpChartFun u)).toReal`. -/
@[simp]
lemma norm_wkpChart_def
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (n := n) (M := M) g k p hp) :
    ‖u‖ = (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal := rfl

/-- The `SeminormedSpace.Core` for `WkpChart g k p hp` (compact `M`). -/
lemma wkpChart_seminormedSpace_core
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    SeminormedSpace.Core ℝ (WkpChart (n := n) (M := M) g k p hp) where
  norm_nonneg u := ENNReal.toReal_nonneg
  norm_smul c u := by
    have hu_mem := wkpChartFun_memWkpChart u
    change (wkpNormChart (n := n) (M := M) g k p (wkpChartFun (c • u))).toReal =
      ‖c‖ * (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal
    rw [wkpChartFun_smul]
    rw [wkpNormChart_const_smul (n := n) (M := M) g hp c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]
  norm_triangle u v := by
    have hu_mem := wkpChartFun_memWkpChart u
    have hv_mem := wkpChartFun_memWkpChart v
    change (wkpNormChart (n := n) (M := M) g k p (wkpChartFun (u + v))).toReal ≤
      (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal +
        (wkpNormChart (n := n) (M := M) g k p (wkpChartFun v)).toReal
    rw [wkpChartFun_add]
    have h_add_le := wkpNormChart_add_le (n := n) (M := M) g hp hu_mem hv_mem
    have hu_lt : wkpNormChart (n := n) (M := M) g k p (wkpChartFun u) < ⊤ :=
      wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp hu_mem
    have hv_lt : wkpNormChart (n := n) (M := M) g k p (wkpChartFun v) < ⊤ :=
      wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp hv_mem
    have hu_ne : wkpNormChart (n := n) (M := M) g k p (wkpChartFun u) ≠ ⊤ := hu_lt.ne
    have hv_ne : wkpNormChart (n := n) (M := M) g k p (wkpChartFun v) ≠ ⊤ := hv_lt.ne
    have hRHS_ne : wkpNormChart (n := n) (M := M) g k p (wkpChartFun u) +
        wkpNormChart (n := n) (M := M) g k p (wkpChartFun v) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hu_ne, hv_ne⟩
    have hToReal := ENNReal.toReal_mono hRHS_ne h_add_le
    rw [ENNReal.toReal_add hu_ne hv_ne] at hToReal
    exact hToReal

/-- The `SeminormedAddCommGroup` instance on `WkpChart g k p hp` for compact
`M`. -/
instance instSeminormedAddCommGroupWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    SeminormedAddCommGroup (WkpChart (n := n) (M := M) g k p hp) :=
  SeminormedAddCommGroup.ofCore (wkpChart_seminormedSpace_core (n := n) (M := M) g k p hp)

/-- `WkpChart g k p hp` is a normed real vector space (well, seminormed). -/
instance instNormedSpaceRealWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedSpace ℝ (WkpChart (n := n) (M := M) g k p hp) where
  norm_smul_le c u := by
    have hu_mem := wkpChartFun_memWkpChart u
    change (wkpNormChart (n := n) (M := M) g k p (wkpChartFun (c • u))).toReal ≤
      ‖c‖ * (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal
    rw [wkpChartFun_smul]
    rw [wkpNormChart_const_smul (n := n) (M := M) g hp c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]

/-- The `SeparationQuotient` of `WkpChart g k p hp` is a `NormedAddCommGroup`
(automatically inherited from the seminormed structure). -/
def WkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)

instance instAddCommGroupWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    AddCommGroup (WkpChartQuot (n := n) (M := M) g k p hp) :=
  inferInstanceAs (AddCommGroup
    (SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)))

instance instNormedAddCommGroupWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedAddCommGroup (WkpChartQuot (n := n) (M := M) g k p hp) :=
  inferInstanceAs (NormedAddCommGroup
    (SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)))

instance instModuleWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Module ℝ (WkpChartQuot (n := n) (M := M) g k p hp) :=
  inferInstanceAs (Module ℝ
    (SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)))

instance instNormedSpaceRealWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedSpace ℝ (WkpChartQuot (n := n) (M := M) g k p hp) :=
  inferInstanceAs (NormedSpace ℝ
    (SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)))

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
