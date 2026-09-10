import DifferentialGeometry.Topology.Manifold.PrescribedDifferential
import DifferentialGeometry.Bundle.PartialMfderiv.Basic

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace Poincare.Topology.Manifold

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem mfderiv_mlieBracket_of_related
    {φ : M → N} (hφ : ContMDiff I J ∞ φ)
    (X Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (X' Y' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _))
    (hX : ∀ x, mfderiv I J φ x (X x) = X' (φ x))
    (hY : ∀ x, mfderiv I J φ x (Y x) = Y' (φ x)) (x : M) :
    mfderiv I J φ x (VectorField.mlieBracket I X Y x) =
      VectorField.mlieBracket J X' Y' (φ x) := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have chain (f : N → ℝ) (hf : ContMDiff J 𝓘(ℝ) ∞ f)
      (Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
      (Z' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _))
      (hZ : ∀ y, mfderiv I J φ y (Z y) = Z' (φ y)) :
      (fun y ↦ mvfderiv I (f ∘ φ) y (Z y)) =
        (fun y ↦ mvfderiv J f (φ y) (Z' (φ y))) := by
    funext y
    rw [mvfderiv_comp y (hf.mdifferentiable (by simp) (φ y))
      (hφ.mdifferentiable (by simp) y)]
    change mvfderiv J f (φ y) (mfderiv I J φ y (Z y)) = _
    rw [hZ y]
  apply tangent_eq_of_smooth_function_differentials
  intro f hf _
  have hfX := DifferentialGeometry.mvfderiv_apply_contMDiff J f hf X'
  have hfY := DifferentialGeometry.mvfderiv_apply_contMDiff J f hf Y'
  have hcomp := mvfderiv_comp x (hf.mdifferentiable (by simp) (φ x))
    (hφ.mdifferentiable (by simp) x)
  have hreg : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  have hbr := DifferentialGeometry.mvfderiv_apply_mlieBracket X Y (f ∘ φ) x
    (X.contMDiff.contMDiffAt.of_le hreg) (Y.contMDiff.contMDiffAt.of_le hreg)
    ((hf.comp hφ).contMDiffAt.of_le hreg)
  have hbr' := DifferentialGeometry.mvfderiv_apply_mlieBracket X' Y' f (φ x)
    (X'.contMDiff.contMDiffAt.of_le hreg) (Y'.contMDiff.contMDiffAt.of_le hreg)
    (hf.contMDiffAt.of_le hreg)
  rw [chain f hf Y Y' hY, chain f hf X X' hX] at hbr
  have hfirst := congrFun (chain _ hfY X X' hX) x
  have hsecond := congrFun (chain _ hfX Y Y' hY) x
  dsimp only [Function.comp_def] at hfirst hsecond
  rw [hfirst, hsecond] at hbr
  rw [hbr']
  rw [hcomp] at hbr
  exact hbr

end Poincare.Topology.Manifold
