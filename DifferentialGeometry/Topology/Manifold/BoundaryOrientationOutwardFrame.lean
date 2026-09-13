import DifferentialGeometry.Topology.Manifold.BoundaryFrameOrientationSign

set_option autoImplicit false
noncomputable section
open Function Module

namespace DifferentialGeometry.Topology.Manifold

variable {E F G : Type*} [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

def halfSpaceOutwardNormalFirstOrientation (b : Basis (Fin 2) ℝ F)
    (o : Orientation ℝ (ℝ × F) (Fin 3)) : Orientation ℝ F (Fin 2) :=
  normalFirstOrientation (normalFirstReflection.trans (LinearEquiv.refl ℝ (ℝ × F))) b o

theorem halfSpaceOutwardNormalFirstOrientation_eq_neg (b : Basis (Fin 2) ℝ F)
    (o : Orientation ℝ (ℝ × F) (Fin 3)) :
    halfSpaceOutwardNormalFirstOrientation b o =
      -normalFirstOrientation (LinearEquiv.refl ℝ (ℝ × F)) b o :=
  normalFirstOrientation_reflect_normal (LinearEquiv.refl ℝ (ℝ × F)) b o

theorem halfSpaceInwardNormalFirstOrientation_apply (b : Basis (Fin 2) ℝ F)
    (ω : (ℝ × F) [⋀^Fin 3]→ₗ[ℝ] ℝ) (hω : ω ≠ 0) :
    normalFirstOrientation (LinearEquiv.refl ℝ (ℝ × F)) b (rayOfNeZero ℝ ω hω) =
      rayOfNeZero ℝ (normalFirstContraction (LinearEquiv.refl ℝ (ℝ × F)) ω)
        (normalFirstContraction_ne_zero (LinearEquiv.refl ℝ (ℝ × F)) b ω hω) := rfl

theorem halfSpaceOutwardNormalFirstOrientation_apply (b : Basis (Fin 2) ℝ F)
    (ω : (ℝ × F) [⋀^Fin 3]→ₗ[ℝ] ℝ) (hω : ω ≠ 0) :
    halfSpaceOutwardNormalFirstOrientation b (rayOfNeZero ℝ ω hω) =
      -(rayOfNeZero ℝ (normalFirstContraction (LinearEquiv.refl ℝ (ℝ × F)) ω)
        (normalFirstContraction_ne_zero (LinearEquiv.refl ℝ (ℝ × F)) b ω hω)) := by
  rw [halfSpaceOutwardNormalFirstOrientation_eq_neg,
    halfSpaceInwardNormalFirstOrientation_apply]

theorem halfSpaceOutwardNormalFirstOrientation_change_boundary (e : (ℝ × F) ≃ₗ[ℝ] E)
    (g : F ≃ₗ[ℝ] G) (b : Basis (Fin 2) ℝ F) (b' : Basis (Fin 2) ℝ G)
    (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation
        (((LinearEquiv.refl ℝ ℝ).prodCongr g.symm).trans
          ((normalFirstReflection (F := F)).trans e)) b' o =
      Orientation.map (Fin 2) g
        (normalFirstOrientation ((normalFirstReflection (F := F)).trans e) b o) :=
  by
    simpa only [LinearEquiv.symm_symm] using
      normalFirstOrientation_change_boundary ((normalFirstReflection (F := F)).trans e)
        g.symm b b' o

theorem halfSpaceOutwardNormalFirstOrientation_change_positive_normal
    (e e' : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F) (c : ℝ) (hc : 0 < c) (w : F)
    (hn : e' (1, 0) = c • e (1, 0) + e (0, w))
    (ht : ∀ v : F, e' (0, v) = e (0, v)) (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation ((normalFirstReflection (F := F)).trans e') b o =
      normalFirstOrientation ((normalFirstReflection (F := F)).trans e) b o := by
  calc
    normalFirstOrientation ((normalFirstReflection (F := F)).trans e') b o
        = -normalFirstOrientation e' b o := normalFirstOrientation_reflect_normal e' b o
    _ = -normalFirstOrientation e b o :=
      congrArg Neg.neg (normalFirstOrientation_change_positive_normal e e' b c hc w hn ht o)
    _ = normalFirstOrientation ((normalFirstReflection (F := F)).trans e) b o :=
      (normalFirstOrientation_reflect_normal e b o).symm

end DifferentialGeometry.Topology.Manifold
