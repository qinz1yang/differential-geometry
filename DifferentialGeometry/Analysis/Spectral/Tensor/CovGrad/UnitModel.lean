import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs

noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def unitTensor (x : M) : Tensor0SSpace 0 I x :=
  Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.constOfIsEmpty ℝ
      (fun _ : Fin 0 => E) (1 : ℝ))

def unitModel (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) : Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))

@[simp] theorem unitModel_zero (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    unitModel (I := I) (M := M) g s (0 : SmoothCcTensor g 0 s) x = 0 := by
  rw [unitModel, SmoothCcTensor.toSection_zero]
  rfl

@[simp] theorem unitModel_add (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S T : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S + T) x =
      unitModel (I := I) (M := M) g s S x + unitModel (I := I) (M := M) g s T x := by
  rw [unitModel, unitModel, unitModel, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply, add_apply, Tensor0SSpace.toModel_add]

@[simp] theorem unitModel_neg (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (-S) x = -unitModel (I := I) (M := M) g s S x := by
  rw [unitModel, unitModel, SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg,
    Pi.neg_apply, neg_apply, Tensor0SSpace.toModel_neg]

@[simp] theorem unitModel_sub (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S T : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - T) x =
      unitModel (I := I) (M := M) g s S x - unitModel (I := I) (M := M) g s T x := by
  simpa only [sub_eq_add_neg, unitModel_neg] using
    unitModel_add (I := I) (M := M) g s S (-T) x

@[simp] theorem unitModel_smul (g : SmoothRiemannianMetric I M) (s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (c • S) x =
      c • unitModel (I := I) (M := M) g s S x := by
  rw [unitModel, unitModel, SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul,
    Pi.smul_apply, smul_apply, Tensor0SSpace.toModel_smul]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
