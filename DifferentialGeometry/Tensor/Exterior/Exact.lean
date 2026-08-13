import DifferentialGeometry.Tensor.Exterior.Basic

noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry
namespace DifferentialForm

attribute [local instance] seminormedAddCommGroupTangentSpace
attribute [local instance] normedAddCommGroupTangentSpace
attribute [local instance] normedSpaceTangentSpace

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {k : ℕ}

def isClosed [BoundarylessManifold IM M] (α : DifferentialForm IM M k) : Prop :=
  exteriorDerivative α = 0

def isExact [BoundarylessManifold IM M] (α : DifferentialForm IM M (k + 1)) : Prop :=
  ∃ β : DifferentialForm IM M k, exteriorDerivative β = α

theorem exact_closed [BoundarylessManifold IM M] {α : DifferentialForm IM M (k + 1)}
    (h : isExact α) : isClosed α := by
  rcases h with ⟨β, hβ⟩
  rw [isClosed, ← hβ]
  exact exteriorDerivative_sq β

theorem isClosed_iff_mem_ker [BoundarylessManifold IM M] (α : DifferentialForm IM M k) :
    isClosed α ↔ α ∈ LinearMap.ker (exteriorDerivativeLinearMap (IM := IM) (M := M) k) := by
  simp [isClosed, exteriorDerivativeLinearMap]

theorem isExact_iff_mem_range [BoundarylessManifold IM M] (α : DifferentialForm IM M (k + 1)) :
    isExact α ↔ α ∈ LinearMap.range (exteriorDerivativeLinearMap (IM := IM) (M := M) k) := by
  simp [isExact, exteriorDerivativeLinearMap]

end DifferentialForm
end DifferentialGeometry

end
