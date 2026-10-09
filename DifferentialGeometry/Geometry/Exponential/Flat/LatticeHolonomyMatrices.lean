import DifferentialGeometry.Geometry.Exponential.Flat.AffineTranslations
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.GroupTheory.OrderOfElement

/-!
The actual affine point group acts by integral matrices on its translation lattice basis.
Its finite order and positive determinant force integral determinant one, and the same
matrix gives an integer trace. No classification or integral representation is supplied.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V] [instSpace : NormedSpace ℝ V]
  {ι : Type*} [instIndex : Fintype ι] [instDec : DecidableEq ι]

theorem exists_affineLinear_integerMatrix (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis ι ℝ V)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (γ : G) (hpos : 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap) :
    ∃ A : Matrix ι ι ℤ,
      A.map (Int.castRingHom ℝ) =
        LinearMap.toMatrix b b γ.val.linearIsometryEquiv.toLinearMap ∧
      A.det = 1 ∧ ∃ z : ℤ, LinearMap.trace ℝ V γ.val.linearIsometryEquiv.toLinearMap = z := by
  classical
  have hentry (i j : ι) :
      ∃ z : ℤ, LinearMap.toMatrix b b γ.val.linearIsometryEquiv.toLinearMap i j = z := by
    have hbmem : b j ∈ affineTranslationModule G :=
      hb ▸ Submodule.subset_span ⟨j, rfl⟩
    have hmem := affineTranslationModule_linear_mem G γ hbmem
    have hc := (b.mem_span_iff_repr_mem ℤ (γ.val.linearIsometryEquiv (b j))).mp
      (hb.symm ▸ hmem) i
    obtain ⟨z, hz⟩ := hc
    refine ⟨z, ?_⟩
    rw [LinearMap.toMatrix_apply]
    change b.repr (γ.val.linearIsometryEquiv (b j)) i = (z : ℝ)
    simpa only [algebraMap_int_eq, Int.coe_castRingHom] using hz.symm
  choose entries hA using hentry
  let A : Matrix ι ι ℤ := entries
  have hcast : A.map (Int.castRingHom ℝ) =
      LinearMap.toMatrix b b γ.val.linearIsometryEquiv.toLinearMap := by
    ext i j
    exact (hA i j).symm
  let rho : (V ≃ₗᵢ[ℝ] V) →* Matrix ι ι ℝ :=
    { toFun := fun L => LinearMap.toMatrix b b L.toLinearMap
      map_one' := by
        change LinearMap.toMatrix b b (1 : V →ₗ[ℝ] V) = 1
        exact LinearMap.toMatrix_one b
      map_mul' := by
        intro L K
        change LinearMap.toMatrix b b (L.toLinearMap * K.toLinearMap) = _
        exact LinearMap.toMatrix_mul b L.toLinearMap K.toLinearMap }
  let delta := Matrix.detMonoidHom.comp rho
  let r := (affineLinearHom.comp G.subtype).rangeRestrict
  have hlin : γ.val.linearIsometryEquiv ^ orderOf (r γ) = 1 :=
    congrArg Subtype.val (pow_orderOf_eq_one (r γ))
  have hvalue (L : V ≃ₗᵢ[ℝ] V) : delta L = LinearMap.det L.toLinearMap :=
    LinearMap.det_toMatrix b L.toLinearMap
  have hp : delta γ.val.linearIsometryEquiv ^ orderOf (r γ) = 1 := by
    rw [← map_pow, hlin, map_one]
  rw [hvalue] at hp
  have hdet : LinearMap.det γ.val.linearIsometryEquiv.toLinearMap = 1 :=
    (pow_eq_one_iff_of_nonneg hpos.le (orderOf_pos (r γ)).ne').mp hp
  refine ⟨A, hcast, ?_, A.trace, ?_⟩
  · have hd : (A.det : ℝ) = 1 := by
      rw [Int.cast_det]
      change (A.map (Int.castRingHom ℝ)).det = 1
      rw [hcast, LinearMap.det_toMatrix, hdet]
    exact_mod_cast hd
  · rw [LinearMap.trace_eq_matrix_trace ℝ b, ← hcast]
    exact (AddMonoidHom.map_trace (Int.castRingHom ℝ) A).symm

end DifferentialGeometry.Geometry.FlatSurface
