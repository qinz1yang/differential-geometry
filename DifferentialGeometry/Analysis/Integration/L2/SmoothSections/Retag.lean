import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

/-!
# Retagging smooth compactly-supported tensors

The metric parameter of `SmoothCcTensor g r s` is phantom: it does not occur
in the underlying smooth section or compact-support witness.  This file exposes
the resulting canonical linear equivalence between tensors carrying different
metric tags.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace L2
namespace SmoothCcTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The canonical linear equivalence obtained by changing only the phantom
metric tag of a smooth compactly-supported tensor. -/
def retagEquiv
    (g h : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s ≃ₗ[ℝ] SmoothCcTensor h r s where
  toFun S := ⟨S.toSection, S.hasCompactSupport⟩
  invFun S := ⟨S.toSection, S.hasCompactSupport⟩
  left_inv S := by
    ext
    rfl
  right_inv S := by
    ext
    rfl
  map_add' S T := by
    ext
    rfl
  map_smul' c S := by
    ext
    rfl

/-- Retagging preserves the underlying smooth tensor section definitionally. -/
@[simp]
theorem retag_toSection
    (g h : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    (retagEquiv g h r s S).toSection = S.toSection := rfl

end SmoothCcTensor
end L2
end Integral
end DifferentialGeometry
