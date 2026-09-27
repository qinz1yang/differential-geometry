import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Geometry.Operator.Laplacian.Basic
open DifferentialGeometry.Geometry.Operator


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Forms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

def codifferentialOfVectorField
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : M → ℝ :=
  fun y => -divergenceG (I := I) g X y

@[simp] lemma codifferentialOfVectorField_def (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    codifferentialOfVectorField (I := I) g X y =
      -divergenceG (I := I) g X y := rfl

theorem codifferentialOfVectorField_contMDiff [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (codifferentialOfVectorField (I := I) g X) := by
  have hdiv : ContMDiff I 𝓘(ℝ) ∞ (divergenceG (I := I) g X) :=
    divergence_g_contMDiff (I := I) g X
  have hneg : ContMDiff I 𝓘(ℝ) ∞ (fun y : M => -divergenceG (I := I) g X y) :=
    hdiv.neg
  exact hneg

theorem codifferentialOfVectorField_add [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    codifferentialOfVectorField (I := I) g (X + Y) y =
      codifferentialOfVectorField (I := I) g X y +
        codifferentialOfVectorField (I := I) g Y y := by
  change -divergenceG (I := I) g (X + Y) y =
    -divergenceG (I := I) g X y + -divergenceG (I := I) g Y y
  rw [divergence_g_add (I := I) g X Y y]
  ring

theorem codifferentialOfVectorField_zero [I.Boundaryless] (g : SmoothRiemannianMetric I M) (y : M) :
    codifferentialOfVectorField (I := I) g
        (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y = 0 := by
  change -divergenceG (I := I) g
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y = 0
  rw [divergence_g_zero (I := I) g y]
  exact neg_zero

def formLaplacianScalar [I.Boundaryless] (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) : M → ℝ :=
  codifferentialOfVectorField (I := I) g (gradG (I := I) g ⟨_, hf⟩)

@[simp] lemma formLaplacianScalar_def [I.Boundaryless] (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    formLaplacianScalar (I := I) g hf y =
      codifferentialOfVectorField (I := I) g (gradG (I := I) g ⟨_, hf⟩) y := rfl

theorem formLaplacianScalar_eq_neg_Δ_g [I.Boundaryless] (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    formLaplacianScalar (I := I) g hf y =
      -DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hf⟩ y := by
  change codifferentialOfVectorField (I := I) g (gradG (I := I) g ⟨_, hf⟩) y =
    -DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hf⟩ y
  rw [codifferentialOfVectorField_def (I := I) g (gradG (I := I) g ⟨_, hf⟩) y]
  rw [DifferentialGeometry.Geometry.Operator.Δ_g_def (I := I) g ⟨_, hf⟩ y]

theorem formLaplacianScalar_contMDiff [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (formLaplacianScalar (I := I) g hf) :=
  codifferentialOfVectorField_contMDiff (I := I) g (gradG (I := I) g ⟨_, hf⟩)

theorem formLaplacianScalar_zero [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (h0 : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ))) (y : M) :
    formLaplacianScalar (I := I) g h0 y = 0 := by
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g h0 y]
  have hgrad_zero : (gradG (I := I) g ⟨_, h0⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    apply ContMDiffSection.ext
    intro x
    change gradFun (I := I) g (fun _ : M => (0 : ℝ)) x =
        (0 : TangentSpace I x)
    apply gradFun_eq_zero_of_mfderiv_eq_zero
    exact mfderiv_const
  change -DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, h0⟩ y = 0
  rw [DifferentialGeometry.Geometry.Operator.Δ_g_def (I := I) g ⟨_, h0⟩ y]
  rw [hgrad_zero]
  rw [divergence_g_zero (I := I) g y]
  exact neg_zero

theorem formLaplacianScalar_add [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hfh : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f + h)) (y : M) :
    formLaplacianScalar (I := I) g hfh y =
      formLaplacianScalar (I := I) g hf y +
        formLaplacianScalar (I := I) g hh y := by
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g hfh y]
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g hf y]
  rw [formLaplacianScalar_eq_neg_Δ_g (I := I) g hh y]
  have hgrad_sum :
      (gradG (I := I) g ⟨_, hfh⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) =
        (gradG (I := I) g ⟨_, hf⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) +
        (gradG (I := I) g ⟨_, hh⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) := by
    apply ContMDiffSection.ext
    intro x
    change gradFun (I := I) g (f + h) x =
      gradFun (I := I) g f x + gradFun (I := I) g h x
    exact gradFun_add (I := I) g
      (hf.mdifferentiable (by simp) x) (hh.mdifferentiable (by simp) x)
  change -DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hfh⟩ y =
    -DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hf⟩ y +
      -DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hh⟩ y
  rw [DifferentialGeometry.Geometry.Operator.Δ_g_def (I := I) g ⟨_, hfh⟩ y]
  rw [DifferentialGeometry.Geometry.Operator.Δ_g_def (I := I) g ⟨_, hf⟩ y]
  rw [DifferentialGeometry.Geometry.Operator.Δ_g_def (I := I) g ⟨_, hh⟩ y]
  rw [hgrad_sum]
  rw [divergence_g_add (I := I) g
        (gradG (I := I) g ⟨_, hf⟩) (gradG (I := I) g ⟨_, hh⟩) y]
  ring

end Forms
end Riemannian
end Geometry
end DifferentialGeometry
