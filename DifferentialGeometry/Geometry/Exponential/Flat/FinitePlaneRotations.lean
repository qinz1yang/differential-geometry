import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Every faithful positive finite group action by real linear isometries of the complex plane
is cyclic. Actual positive plane rotations make evaluation at one an injective homomorphism
to the complex field, where the polynomial root bound proves cyclicity.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

attribute [local instance] Complex.finrank_real_complex_fact

theorem finitePositive_planeAction_isCyclic (H : Type*) [instG : Group H]
    [instF : Finite H] (rho : H →* (ℂ ≃ₗᵢ[ℝ] ℂ)) (hinj : Function.Injective rho)
    (hpos : ∀ g : H, 0 < LinearMap.det (rho g).toLinearMap) : IsCyclic H := by
  have hmul (g : H) (z : ℂ) : rho g z = rho g 1 * z := by
    obtain ⟨theta, ht⟩ :=
      Complex.orientation.exists_linearIsometryEquiv_eq_of_det_pos (hpos g)
    rw [ht, Complex.rotation, Complex.rotation, mul_one]
  let f : H →* ℂ :=
    { toFun := fun g => rho g 1
      map_one' := by
        change rho 1 1 = 1
        rw [rho.map_one]
        rfl
      map_mul' := by
        intro g h
        rw [map_mul]
        change rho g (rho h 1) = rho g 1 * rho h 1
        exact hmul g (rho h 1) }
  have hf : Function.Injective f := by
    intro g h he
    apply hinj
    apply LinearIsometryEquiv.ext
    intro z
    rw [hmul g z, hmul h z]
    change rho g 1 = rho h 1 at he
    rw [he]
  exact isCyclic_of_injective_ringHom f hf

theorem finitePositive_twoDimensionalAction_isCyclic (V : Type*)
    [instV : NormedAddCommGroup V] [instInner : InnerProductSpace ℝ V]
    [instFD : FiniteDimensional ℝ V] (hv : finrank ℝ V = 2)
    (H : Type*) [instG : Group H] [instF : Finite H]
    (rho : H →* (V ≃ₗᵢ[ℝ] V)) (hinj : Function.Injective rho)
    (hpos : ∀ g : H, 0 < LinearMap.det (rho g).toLinearMap) : IsCyclic H := by
  let e : V ≃ₗᵢ[ℝ] ℂ := (stdOrthonormalBasis ℝ V).equiv
    (stdOrthonormalBasis ℝ ℂ) (finCongr (hv.trans Complex.finrank_real_complex.symm))
  let rhoc : H →* (ℂ ≃ₗᵢ[ℝ] ℂ) :=
    { toFun := fun g => e.symm.trans ((rho g).trans e)
      map_one' := by ext z; simp
      map_mul' := by intro g h; ext z; simp }
  have hc (g : H) (z : ℂ) : rhoc g z = e (rho g (e.symm z)) := rfl
  have hic : Function.Injective rhoc := by
    intro g h he
    apply hinj
    apply LinearIsometryEquiv.ext
    intro v
    have hx := congrArg (fun L : ℂ ≃ₗᵢ[ℝ] ℂ => L (e v)) he
    simp only [hc, e.symm_apply_apply] at hx
    exact e.injective hx
  have hpc (g : H) : 0 < LinearMap.det (rhoc g).toLinearMap := by
    have hd := LinearMap.det_conj (rho g).toLinearMap e.toLinearEquiv
    change LinearMap.det (rhoc g).toLinearMap = LinearMap.det (rho g).toLinearMap at hd
    rw [hd]
    exact hpos g
  exact finitePositive_planeAction_isCyclic H rhoc hic hpc

end DifferentialGeometry.Geometry.FlatSurface
