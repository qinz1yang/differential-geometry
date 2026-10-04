import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import DifferentialGeometry.Bundle.FiberBundleHausdorff

/-!
# A sequence of metrics on one manifold, as a pointed Riemannian sequence

`pointedMetricSeq p gSeq` packages a sequence of smooth Riemannian metrics `gSeq n` on one fixed
manifold `M`, all with the same basepoint `p`, as a `PointedRiemannianSeq` (`Pointed/Defs.lean`):
the `n`-th object has carrier `M`, its given topology, charts and smooth structure, basepoint `p`
and metric `gSeq n`. Every instance field is inferred from the context; no hypothesis is added.
This is the packaging of the merged LFR50 design (§5 item 5, §6) for positive-time slices of
Ricci flows on a fixed closed manifold.
-/

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- The pointed Riemannian sequence of the metrics `gSeq n` on the fixed manifold `M`, based at
`p`. -/
def pointedMetricSeq (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj n :=
    { M := M
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      sigmaCompact := inferInstance
      t2 := inferInstance
      t2TangentBundle := inferInstance
      basepoint := p
      metric := gSeq n }

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem pointedMetricSeq_obj_M (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (n : ℕ) : ((pointedMetricSeq p gSeq).obj n).M = M :=
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem pointedMetricSeq_obj_topology (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (n : ℕ) : ((pointedMetricSeq p gSeq).obj n).topology = ‹TopologicalSpace M› :=
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem pointedMetricSeq_obj_basepoint (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (n : ℕ) : ((pointedMetricSeq p gSeq).obj n).basepoint = p :=
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem pointedMetricSeq_obj_metric (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (n : ℕ) : ((pointedMetricSeq p gSeq).obj n).metric = gSeq n :=
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem pointedMetricSeq_basepoint (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (n : ℕ) : (pointedMetricSeq p gSeq).basepoint n = p :=
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
@[simp] theorem pointedMetricSeq_subseq (p : M) (gSeq : ℕ → SmoothRiemannianMetric I M)
    (f : ℕ → ℕ) : (pointedMetricSeq p gSeq).subseq f = pointedMetricSeq p (gSeq ∘ f) :=
  rfl

end CheegerGromovCompactness
end DifferentialGeometry
