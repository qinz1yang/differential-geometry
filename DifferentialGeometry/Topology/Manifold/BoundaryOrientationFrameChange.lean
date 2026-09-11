import DifferentialGeometry.Topology.Manifold.BoundaryOrientationContraction
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
open Function Module
namespace DifferentialGeometry.Topology.Manifold
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

theorem normalFirstContraction_tangent_zero (e : (ℝ × F) ≃ₗ[ℝ] E)
    (b : Basis (Fin 2) ℝ F) (w : F) (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) :
    (ω.curryLeft (e (0, w))).compLinearMap
      (e.toLinearMap.comp (LinearMap.inr ℝ ℝ F)) = 0 := by
  let : FiniteDimensional ℝ F := b.finiteDimensional_of_finite
  let ωF : F [⋀^Fin 3]→ₗ[ℝ] ℝ :=
    ω.compLinearMap (e.toLinearMap.comp (LinearMap.inr ℝ ℝ F))
  have hz (u : Fin 3 → F) : ωF u = 0 := by
    apply ωF.map_linearDependent
    intro hi
    have hcard := hi.fintype_card_le_finrank
    rw [Module.finrank_eq_card_basis b] at hcard
    norm_num at hcard
  ext v
  have h := hz (Matrix.vecCons w v)
  change ω (fun i => e (0, Matrix.vecCons w v i)) = 0 at h
  change ω (Matrix.vecCons (e (0, w)) (fun i => e (0, v i))) = 0
  convert h using 1
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

theorem normalFirstContraction_change_normal (e e' : (ℝ × F) ≃ₗ[ℝ] E)
    (b : Basis (Fin 2) ℝ F) (c : ℝ) (w : F)
    (hn : e' (1, 0) = c • e (1, 0) + e (0, w))
    (ht : ∀ v : F, e' (0, v) = e (0, v)) (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) :
    normalFirstContraction e' ω = c • normalFirstContraction e ω := by
  ext v
  rw [normalFirstContraction_apply, hn]
  simp_rw [ht]
  change ω.curryLeft (c • e (1, 0) + e (0, w)) (fun i => e (0, v i)) =
    c • ω.curryLeft (e (1, 0)) (fun i => e (0, v i))
  have hz := congrArg (fun a : F [⋀^Fin 2]→ₗ[ℝ] ℝ => a v)
    (normalFirstContraction_tangent_zero e b w ω)
  change ω.curryLeft (e (0, w)) (fun i => e (0, v i)) = 0 at hz
  rw [map_add, map_smul]
  change c • ω.curryLeft (e (1, 0)) (fun i => e (0, v i)) +
    ω.curryLeft (e (0, w)) (fun i => e (0, v i)) = _
  rw [hz, add_zero]

theorem normalFirstOrientation_change_positive_normal (e e' : (ℝ × F) ≃ₗ[ℝ] E)
    (b : Basis (Fin 2) ℝ F) (c : ℝ) (hc : 0 < c) (w : F)
    (hn : e' (1, 0) = c • e (1, 0) + e (0, w))
    (ht : ∀ v : F, e' (0, v) = e (0, v)) (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation e' b o = normalFirstOrientation e b o := by
  induction o using Module.Ray.ind with
  | h ω hω =>
    rw [normalFirstOrientation_apply, normalFirstOrientation_apply]
    apply (ray_eq_iff _ _).mpr
    rw [normalFirstContraction_change_normal e e' b c w hn ht ω]
    exact SameRay.sameRay_pos_smul_left _ hc

theorem normalFirstOrientation_change_boundary (e : (ℝ × F) ≃ₗ[ℝ] E)
    (g : G ≃ₗ[ℝ] F) (b : Basis (Fin 2) ℝ F) (b' : Basis (Fin 2) ℝ G)
    (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation (((LinearEquiv.refl ℝ ℝ).prodCongr g).trans e) b' o =
      Orientation.map (Fin 2) g.symm (normalFirstOrientation e b o) := by
  induction o using Module.Ray.ind with
  | h ω hω =>
    rw [normalFirstOrientation_apply, normalFirstOrientation_apply, Orientation.map_apply]
    congr 1
    ext v
    simp only [normalFirstContraction_apply, AlternatingMap.compLinearMap_apply,
      LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      map_zero, LinearEquiv.symm_symm]
    rfl
end DifferentialGeometry.Topology.Manifold
