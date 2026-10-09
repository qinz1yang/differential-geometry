import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Manifold
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula

noncomputable section

open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def spaceVectorField (v : E) (x : Hyperboloid E) : TangentSpace 𝓘(ℝ, E) x :=
  (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v

theorem tangentConstAt_spaceVectorField (x : Hyperboloid E) (v : E) :
    Geometry.Connection.tangentConstAt x (spaceVectorField v x) = spaceVectorField v := by
  funext y
  have h := Geometry.Connection.tangentConstAt_self x (spaceVectorField v x)
  unfold Geometry.Connection.tangentConstAt TensorLieDeriv.tangentConstInChart at h ⊢
  rw [tangent_trivializationAt_symmL] at h ⊢
  exact h

theorem mdifferentiableAt_spaceVectorField (x : Hyperboloid E) (v : E) :
    MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun y : Hyperboloid E =>
        (⟨y, spaceVectorField v y⟩ : TangentBundle 𝓘(ℝ, E) (Hyperboloid E))) x := by
  rw [← tangentConstAt_spaceVectorField x v]
  exact Geometry.Connection.mdifferentiableAt_tangentConstAt_self x (spaceVectorField v x)

end DifferentialGeometry.Hyperboloid
