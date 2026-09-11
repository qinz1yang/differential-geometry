import DifferentialGeometry.Topology.Manifold.OrientationLinearVariation

set_option autoImplicit false
noncomputable section
open Set Function
namespace DifferentialGeometry.Topology.Manifold
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

def tangentOrientationEquiv (e : E ≃ₗ[ℝ] F) :
    Orientation ℝ E (Fin (Module.finrank ℝ E)) ≃
      Orientation ℝ F (Fin (Module.finrank ℝ F)) :=
  (Orientation.map _ e).trans
    (Orientation.reindex ℝ F (finCongr e.finrank_eq))

theorem tangentOrientationEquiv_self (e : E ≃ₗ[ℝ] E)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    tangentOrientationEquiv e o = Orientation.map _ e o := by
  change Orientation.reindex ℝ E (Equiv.refl _) (Orientation.map _ e o) = _
  rw [Orientation.reindex_refl]
  rfl

theorem tangentOrientationEquiv_refl
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    tangentOrientationEquiv (LinearEquiv.refl ℝ E) o = o := by
  rw [tangentOrientationEquiv_self, Orientation.map_refl]
  rfl

theorem tangentOrientationEquiv_trans (e : E ≃ₗ[ℝ] F) (f : F ≃ₗ[ℝ] G)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    tangentOrientationEquiv (e.trans f) o = tangentOrientationEquiv f (tangentOrientationEquiv e o) := by
  induction o using Module.Ray.ind with
  | h o ho => rfl

theorem tangentOrientationEquiv_symm (e : E ≃ₗ[ℝ] F)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    tangentOrientationEquiv e.symm (tangentOrientationEquiv e o) = o := by
  rw [← tangentOrientationEquiv_trans]
  have he : e.trans e.symm = LinearEquiv.refl ℝ E := by
    apply LinearEquiv.ext
    intro x
    exact e.symm_apply_apply x
  rw [he, tangentOrientationEquiv_refl]

theorem tangentOrientationEquiv_neg (e : E ≃ₗ[ℝ] F)
    (o : Orientation ℝ E (Fin (Module.finrank ℝ E))) :
    tangentOrientationEquiv e (-o) = -tangentOrientationEquiv e o := by
  change Orientation.reindex ℝ F _ (Orientation.map _ e (-o)) = _
  rw [Orientation.map_neg, Orientation.reindex_neg]
  rfl
end DifferentialGeometry.Topology.Manifold
