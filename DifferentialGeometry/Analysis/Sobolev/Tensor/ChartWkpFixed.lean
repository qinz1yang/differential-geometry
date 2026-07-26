import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpQuot

/-!
# Fixed-point closedness in the explicit tensor Sobolev quotient

`WkpTensorQuot` deliberately has no global metric or complete-space instance.
Its theorem-valued distance and completeness API is nevertheless enough to
show that the fixed set of a Lipschitz endomorphism is sequentially closed.
This is the form needed by a retraction/coretraction parametrix: a sequence of
genuine tensor states has a genuine tensor limit.  It does not assert that a
chartwise heat generator commutes with the chart projection.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- A `W^{k,p}` Cauchy sequence fixed by a Lipschitz endomorphism has a fixed
quotient limit.  No `MetricSpace` or `CompleteSpace` instance is installed. -/
theorem qfixed_limit
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (P : WkpTensorQuot (I := I) (M := M) g r s k p hp →
      WkpTensorQuot (I := I) (M := M) g r s k p hp)
    (L : ℝ) (hLip : ∀ a b,
      qdist (I := I) (M := M) g r s k p hp (P a) (P b) ≤
        L * qdist (I := I) (M := M) g r s k p hp a b)
    (u : ℕ → WkpTensorQuot (I := I) (M := M) g r s k p hp)
    (hu : ∀ n, P (u n) = u n)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      qdist (I := I) (M := M) g r s k p hp (u m) (u n) < ε) :
    ∃ v : WkpTensorQuot (I := I) (M := M) g r s k p hp,
      Tendsto
          (fun n => qdist (I := I) (M := M) g r s k p hp (u n) v)
          atTop (𝒩 0) ∧
        P v = v := by
  obtain ⟨v, hv⟩ :=
    qdist_limit (I := I) (M := M) g r s k hp hp_top u h_cauchy
  refine ⟨v, hv, ?_⟩
  let d := qdist (I := I) (M := M) g r s k p hp
  have hbound : ∀ n, d (P v) v ≤ (L + 1) * d (u n) v := by
    intro n
    calc
      d (P v) v ≤ d (P v) (P (u n)) + d (P (u n)) v :=
        qdist_triangle (I := I) (M := M) g r s k hp
          (P v) (P (u n)) v
      _ = d (P v) (P (u n)) + d (u n) v := by
        rw [hu n]
      _ ≤ L * d v (u n) + d (u n) v := by
        exact add_le_add_right (hLip v (u n)) _
      _ = (L + 1) * d (u n) v := by
        rw [qdist_symm (I := I) (M := M) g r s k hp v (u n)]
        ring
  have hscaled :
      Tendsto (fun n => (L + 1) * d (u n) v) atTop (𝒩 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => L + 1) atTop (𝒩 (L + 1)) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hconst.mul hv
  have hle : d (P v) v ≤ 0 :=
    le_of_tendsto hscaled (Eventually.of_forall hbound)
  have heq : d (P v) v = 0 :=
    le_antisymm hle
      (qdist_nonneg (I := I) (M := M) g r s k hp (P v) v)
  exact (qdist_eq_zero (I := I) (M := M) g r s k hp (P v) v).mp heq

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
