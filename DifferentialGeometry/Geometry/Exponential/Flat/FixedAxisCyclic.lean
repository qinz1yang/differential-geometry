import DifferentialGeometry.Geometry.Exponential.Flat.FinitePlaneRotations
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
A finite positive group of actual three-dimensional isometries fixing a nonzero vector
is cyclic. The actual perpendicular plane action is faithful and positive, with both
properties obtained from its direct-sum decomposition with the fixed vector's span.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem finitePositive_fixedAxis_isCyclic (H : Subgroup (E3 ≃ₗᵢ[ℝ] E3))
    [instH : Finite H] (hpos : ∀ g : H, 0 < LinearMap.det g.val.toLinearMap)
    (q : E3) (hq : q ≠ 0) (hfix : ∀ g : H, g.val q = q) : IsCyclic H := by
  let S : Submodule ℝ E3 := ℝ ∙ q
  let W := Sᗮ
  have hw : finrank ℝ W = 2 := by
    have he := S.finrank_add_finrank_orthogonal
    rw [show finrank ℝ S = 1 from finrank_span_singleton hq] at he
    have he3 : finrank ℝ E3 = 3 := by simp
    rw [he3] at he
    change 1 + finrank ℝ W = 3 at he
    omega
  have hmem (g : H) (x : W) : g.val (x : E3) ∈ W := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    have hi := g.val.inner_map_map q (x : E3)
    rw [hfix g] at hi
    rw [hi]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  let T (g : H) : W ≃ₗᵢ[ℝ] W :=
    { toFun := fun x => ⟨g.val (x : E3), hmem g x⟩
      invFun := fun x => ⟨g.val.symm (x : E3), hmem g⁻¹ x⟩
      left_inv := by intro x; apply Subtype.ext; exact g.val.symm_apply_apply x.val
      right_inv := by intro x; apply Subtype.ext; exact g.val.apply_symm_apply x.val
      map_add' := by intro x y; apply Subtype.ext; exact g.val.map_add x.val y.val
      map_smul' := by intro a x; apply Subtype.ext; exact g.val.map_smul a x.val
      norm_map' := by intro x; exact g.val.norm_map x.val }
  let rho : H →* (W ≃ₗᵢ[ℝ] W) :=
    { toFun := T
      map_one' := by ext x; rfl
      map_mul' := by intro g h; ext x; rfl }
  have hT (g : H) (x : W) : (T g x : E3) = g.val (x : E3) := rfl
  have hS (g : H) (x : S) : g.val (x : E3) = x := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
    rw [← ha, map_smul, hfix g]
  let e : (S × W) ≃ₗ[ℝ] E3 := S.prodEquivOfIsCompl W S.isCompl_orthogonal
  have he (x : S × W) : e x = (x.1 : E3) + (x.2 : E3) := rfl
  have hinj : Function.Injective rho := by
    intro g h ht
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [he, map_add, map_add, hS g y.1, hS h y.1]
    have hy := congrArg (fun K : W ≃ₗᵢ[ℝ] W => (K y.2 : E3)) ht
    exact congrArg (fun z : E3 => (y.1 : E3) + z) hy
  have hp (g : H) : 0 < LinearMap.det (rho g).toLinearMap := by
    have hc : e.symm.toLinearMap ∘ₗ g.val.toLinearMap ∘ₗ e.toLinearMap =
        LinearMap.prodMap (1 : S →ₗ[ℝ] S) (T g).toLinearMap := by
      apply LinearMap.ext
      intro x
      apply e.injective
      change e (e.symm (g.val (e x))) = e (x.1, T g x.2)
      rw [e.apply_symm_apply, he, map_add, hS g x.1, he, hT]
    have hd := LinearMap.det_conj g.val.toLinearMap e.symm
    change LinearMap.det (e.symm.toLinearMap ∘ₗ g.val.toLinearMap ∘ₗ e.toLinearMap) =
      LinearMap.det g.val.toLinearMap at hd
    rw [hc, LinearMap.det_prodMap, map_one, one_mul] at hd
    change 0 < LinearMap.det (T g).toLinearMap
    rw [hd]
    exact hpos g
  exact finitePositive_twoDimensionalAction_isCyclic W hw H rho hinj hp

end DifferentialGeometry.Geometry.FlatSurface
