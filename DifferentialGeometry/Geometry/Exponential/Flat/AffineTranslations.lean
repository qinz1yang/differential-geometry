import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# Actual translation subgroups of Euclidean affine groups

The translation vectors and the linear-part kernel are constructed from the given affine group.
Conjugation transports a translation by the actual linear part. Bounded orbit finiteness passes
to the actual translation vectors without any full-rank or finite-index premise.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instSpace : NormedSpace ℝ V]

def affineLinearHom : (V ≃ᵃⁱ[ℝ] V) →* (V ≃ₗᵢ[ℝ] V) where
  toFun g := g.linearIsometryEquiv
  map_one' := by ext x; rfl
  map_mul' g h := by ext x; rfl

theorem affineIsometry_apply (g : V ≃ᵃⁱ[ℝ] V) (x : V) :
    g x = g.linearIsometryEquiv x + g 0 := by
  simpa using g.map_vadd (0 : V) x

theorem affine_constVAdd_add (v w : V) :
    AffineIsometryEquiv.constVAdd ℝ V (v + w) =
      AffineIsometryEquiv.constVAdd ℝ V v * AffineIsometryEquiv.constVAdd ℝ V w := by
  ext x
  change v + w + x = v + (w + x)
  exact add_assoc v w x

theorem affine_constVAdd_neg (v : V) :
    AffineIsometryEquiv.constVAdd ℝ V (-v) =
      (AffineIsometryEquiv.constVAdd ℝ V v)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  ext x
  change -v + (v + x) = x
  abel

def affineTranslationVectors (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) : AddSubgroup V where
  carrier := {v | AffineIsometryEquiv.constVAdd ℝ V v ∈ G}
  zero_mem' := by
    change AffineIsometryEquiv.constVAdd ℝ V 0 ∈ G
    rw [AffineIsometryEquiv.constVAdd_zero]
    exact G.one_mem
  add_mem' := by
    intro v w hv hw
    change AffineIsometryEquiv.constVAdd ℝ V (v + w) ∈ G
    rw [affine_constVAdd_add]
    exact G.mul_mem hv hw
  neg_mem' := by
    intro v hv
    change AffineIsometryEquiv.constVAdd ℝ V (-v) ∈ G
    rw [affine_constVAdd_neg]
    exact G.inv_mem hv

def affineTranslationModule (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) : Submodule ℤ V :=
  (affineTranslationVectors G).toIntSubmodule

theorem mem_affineTranslationModule {G : Subgroup (V ≃ᵃⁱ[ℝ] V)} {v : V} :
    v ∈ affineTranslationModule G ↔ AffineIsometryEquiv.constVAdd ℝ V v ∈ G := Iff.rfl

def affineTranslationKernel (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) : Subgroup G :=
  (affineLinearHom.comp G.subtype).ker

instance affineTranslationKernel_normal (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) :
    (affineTranslationKernel G).Normal := MonoidHom.normal_ker (affineLinearHom.comp G.subtype)

theorem mem_affineTranslationKernel {G : Subgroup (V ≃ᵃⁱ[ℝ] V)} {g : G} :
    g ∈ affineTranslationKernel G ↔ (g : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv = 1 := Iff.rfl

theorem affine_conjugate_constVAdd (g : V ≃ᵃⁱ[ℝ] V) (v : V) :
    g * AffineIsometryEquiv.constVAdd ℝ V v * g⁻¹ =
      AffineIsometryEquiv.constVAdd ℝ V (g.linearIsometryEquiv v) := by
  ext x
  change g (v + g.symm x) = g.linearIsometryEquiv v + x
  simpa using g.map_vadd (g.symm x) v

theorem affineTranslationModule_linear_mem (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (g : G) {v : V} (hv : v ∈ affineTranslationModule G) :
    (g : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv v ∈ affineTranslationModule G := by
  change AffineIsometryEquiv.constVAdd ℝ V
    ((g : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv v) ∈ G
  rw [← affine_conjugate_constVAdd]
  exact G.mul_mem (G.mul_mem g.property hv) (G.inv_mem g.property)

theorem affineTranslationModule_bounded_finite (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) (R : ℝ)
    (hfin : Set.Finite {g : G | ‖(g : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R}) :
    Set.Finite {v : V | v ∈ affineTranslationModule G ∧ ‖v‖ ≤ R} := by
  have himage := hfin.image (fun g : G => (g : V ≃ᵃⁱ[ℝ] V) 0)
  refine himage.subset ?_
  intro v hv
  refine ⟨⟨AffineIsometryEquiv.constVAdd ℝ V v, hv.1⟩, ?_, ?_⟩
  · simpa using hv.2
  · simp

end DifferentialGeometry.Geometry.FlatSurface
