import DifferentialGeometry.Topology.Manifold.OrientationLinearVariation
import DifferentialGeometry.Tensor.LinearAlgebra.Orientation

section

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

end

end

section

noncomputable section

namespace DifferentialGeometry

private theorem orientation_map_reindex_comm
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {ι κ : Type*} (e : V ≃ₗ[ℝ] W) (i : ι ≃ κ) (o : Orientation ℝ V ι) :
    Orientation.map κ e (Orientation.reindex ℝ V i o) =
      Orientation.reindex ℝ W i (Orientation.map ι e o) := by
  induction o using Module.Ray.ind with
  | h v hv =>
    simp only [Orientation.map_apply, Orientation.reindex_apply]
    have heq : (v.domDomCongr i).compLinearMap (e.symm : W →ₗ[ℝ] V) =
        (v.compLinearMap (e.symm : W →ₗ[ℝ] V)).domDomCongr i := by
      ext x
      rfl
    simp only [heq]

theorem orientation_map_inverse_trans_of_tangentOrientationEquiv
    {V E : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n) (A B : V ≃ₗ[ℝ] E)
    (o : Orientation ℝ V (Fin (Module.finrank ℝ V)))
    {oA oB : Orientation ℝ E (Fin (Module.finrank ℝ E))}
    (hA : Topology.Manifold.tangentOrientationEquiv A o = oA)
    (hB : Topology.Manifold.tangentOrientationEquiv B o = oB) :
    Orientation.map (Fin n) (A.symm.trans B)
      (Orientation.reindex ℝ E (finCongr hn) oA) =
        Orientation.reindex ℝ E (finCongr hn) oB := by
  rw [orientation_map_reindex_comm]
  congr 1
  rw [← Topology.Manifold.tangentOrientationEquiv_self,
    Topology.Manifold.tangentOrientationEquiv_trans, ← hA,
    Topology.Manifold.tangentOrientationEquiv_symm, hB]

end DifferentialGeometry

end

end
