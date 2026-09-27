import Mathlib.LinearAlgebra.Orientation
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false
noncomputable section
open Function Module
namespace DifferentialGeometry.Topology.Manifold
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

private def normalFirstBasis (e : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F) : Basis (Fin 3) ℝ E :=
  (((Basis.singleton (Fin 1) ℝ).prod b).reindex finSumFinEquiv).map e

private theorem normalFirstBasis_zero (e : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F) :
    normalFirstBasis e b 0 = e (1, 0) := by
  simp only [normalFirstBasis, Basis.map_apply, Basis.coe_reindex]
  change e (((Basis.singleton (Fin 1) ℝ).prod b) (Sum.inl 0)) = e (1, 0)
  simp [Basis.prod_apply]

private theorem normalFirstBasis_succ (e : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F) (i : Fin 2) :
    normalFirstBasis e b i.succ = e (0, b i) := by
  simp only [normalFirstBasis, Basis.map_apply, Basis.coe_reindex]
  fin_cases i
  · change e (((Basis.singleton (Fin 1) ℝ).prod b) (Sum.inr 0)) = e (0, b 0)
    simp [Basis.prod_apply]
  · change e (((Basis.singleton (Fin 1) ℝ).prod b) (Sum.inr 1)) = e (0, b 1)
    simp [Basis.prod_apply]

def normalFirstContraction (e : (ℝ × F) ≃ₗ[ℝ] E) :
    (E [⋀^Fin 3]→ₗ[ℝ] ℝ) →ₗ[ℝ] (F [⋀^Fin 2]→ₗ[ℝ] ℝ) where
  toFun ω := (ω.curryLeft (e (1, 0))).compLinearMap
    (e.toLinearMap.comp (LinearMap.inr ℝ ℝ F))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem normalFirstContraction_apply (e : (ℝ × F) ≃ₗ[ℝ] E)
    (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) (v : Fin 2 → F) :
    normalFirstContraction e ω v = ω (Matrix.vecCons (e (1, 0)) (fun i => e (0, v i))) := rfl

theorem normalFirstContraction_ne_zero (e : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F)
    (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) (hω : ω ≠ 0) : normalFirstContraction e ω ≠ 0 := by
  intro hz
  have hval : normalFirstContraction e ω b = ω (normalFirstBasis e b) := by
    rw [normalFirstContraction_apply]
    congr 1
    funext i
    cases i using Fin.cases with
    | zero => exact (normalFirstBasis_zero e b).symm
    | succ i => exact (normalFirstBasis_succ e b i).symm
  have hne := (ω.map_basis_ne_zero_iff (normalFirstBasis e b)).mpr hω
  apply hne
  rw [← hval, hz]
  rfl

def normalFirstOrientation (e : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F) :
    Orientation ℝ E (Fin 3) → Orientation ℝ F (Fin 2) :=
  Quotient.map (fun ω => (⟨normalFirstContraction e ω.val,
    normalFirstContraction_ne_zero e b ω.val ω.property⟩ : RayVector ℝ (F [⋀^Fin 2]→ₗ[ℝ] ℝ)))
    (fun _ _ h => h.map (normalFirstContraction e))

theorem normalFirstOrientation_apply (e : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F)
    (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) (hω : ω ≠ 0) :
    normalFirstOrientation e b (rayOfNeZero ℝ ω hω) =
      rayOfNeZero ℝ (normalFirstContraction e ω) (normalFirstContraction_ne_zero e b ω hω) := rfl

theorem normalFirstOrientation_basis_independent (e : (ℝ × F) ≃ₗ[ℝ] E)
    (b b' : Basis (Fin 2) ℝ F) (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation e b o = normalFirstOrientation e b' o := rfl

theorem normalFirstOrientation_neg (e : (ℝ × F) ≃ₗ[ℝ] E) (b : Basis (Fin 2) ℝ F)
    (o : Orientation ℝ E (Fin 3)) : normalFirstOrientation e b (-o) = -normalFirstOrientation e b o := by
  induction o using Module.Ray.ind with
  | h ω hω =>
    rw [neg_rayOfNeZero, normalFirstOrientation_apply, normalFirstOrientation_apply, neg_rayOfNeZero]
    congr 1

def normalFirstReflection : (ℝ × F) ≃ₗ[ℝ] (ℝ × F) :=
  (LinearEquiv.neg ℝ : ℝ ≃ₗ[ℝ] ℝ).prodCongr (LinearEquiv.refl ℝ F)

private theorem normalFirstContraction_reflect (e : (ℝ × F) ≃ₗ[ℝ] E)
    (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) :
    normalFirstContraction (normalFirstReflection.trans e) ω = -normalFirstContraction e ω := by
  ext v
  simp only [normalFirstContraction_apply, normalFirstReflection, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.neg_apply, LinearEquiv.refl_apply, neg_zero,
    AlternatingMap.neg_apply]
  change ω.curryLeft (e (-1, 0)) (fun i => e (0, v i)) =
    -(ω.curryLeft (e (1, 0)) (fun i => e (0, v i)))
  have he : e (-1, 0) = -e (1, 0) := by
    have h := map_neg e (1, (0 : F))
    simpa only [Prod.neg_mk, neg_zero] using h
  rw [he, map_neg]
  rfl

theorem normalFirstOrientation_reflect_normal (e : (ℝ × F) ≃ₗ[ℝ] E)
    (b : Basis (Fin 2) ℝ F) (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation (normalFirstReflection.trans e) b o = -normalFirstOrientation e b o := by
  induction o using Module.Ray.ind with
  | h ω hω =>
    rw [normalFirstOrientation_apply, normalFirstOrientation_apply, neg_rayOfNeZero]
    congr 1
    exact normalFirstContraction_reflect e ω

theorem normalFirstOrientation_map (e : (ℝ × F) ≃ₗ[ℝ] E) (g : E ≃ₗ[ℝ] G)
    (b : Basis (Fin 2) ℝ F) (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation (e.trans g) b (Orientation.map (Fin 3) g o) = normalFirstOrientation e b o := by
  induction o using Module.Ray.ind with
  | h ω hω =>
    rw [Orientation.map_apply, normalFirstOrientation_apply, normalFirstOrientation_apply]
    congr 1
    ext v
    simp only [normalFirstContraction_apply, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    cases i using Fin.cases <;> simp
end DifferentialGeometry.Topology.Manifold
