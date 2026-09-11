import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Module.Equiv

set_option autoImplicit false

noncomputable section

open Topology

namespace DifferentialGeometry.ProjectiveSpace

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]


instance topologicalSpace : TopologicalSpace (Projectivization K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))


theorem isQuotientMap_mk' :
    IsQuotientMap (Projectivization.mk' K : {v : V // v ≠ 0} → Projectivization K V) :=
  isQuotientMap_quotient_mk'


@[fun_prop]
theorem continuous_mk' :
    Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → Projectivization K V) :=
  (isQuotientMap_mk' K V).continuous

variable {K V} {W : Type*} [AddCommGroup W] [Module K W] [TopologicalSpace W]

theorem continuous_map (f : V →ₗ[K] W) (hf : Function.Injective f) (hc : Continuous f) :
    Continuous (Projectivization.map f hf) := by
  apply (isQuotientMap_mk' K V).continuous_iff.mpr
  let f' : {v : V // v ≠ 0} → {w : W // w ≠ 0} :=
    fun v ↦ ⟨f v, fun h ↦ v.prop (hf (by simpa using h))⟩
  have hf' : Continuous f' := (hc.comp continuous_subtype_val).subtype_mk _
  exact (continuous_mk' K W).comp hf'

def homeomorphMap (e : V ≃L[K] W) : Projectivization K V ≃ₜ Projectivization K W where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv x := by
    induction x using Projectivization.ind with
    | h v hv =>
      change Projectivization.mk K (e.symm (e v)) _ = Projectivization.mk K v hv
      simp only [ContinuousLinearEquiv.symm_apply_apply]
  right_inv x := by
    induction x using Projectivization.ind with
    | h v hv =>
      change Projectivization.mk K (e (e.symm v)) _ = Projectivization.mk K v hv
      simp only [ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := continuous_map e.toLinearMap e.injective e.continuous
  continuous_invFun := continuous_map e.symm.toLinearMap e.symm.injective e.symm.continuous

@[simp]
theorem homeomorphMap_mk (e : V ≃L[K] W) (v : V) (hv : v ≠ 0) :
    homeomorphMap e (Projectivization.mk K v hv) =
      Projectivization.mk K (e v) (e.map_ne_zero_iff.mpr hv) := rfl

end DifferentialGeometry.ProjectiveSpace
