import DifferentialGeometry.Topology.VectorBundle.RankOneQuotient.Basic
import DifferentialGeometry.Bundle.Orientation.Transport
import DifferentialGeometry.Bundle.Orientation.BasisContinuity
import Mathlib.Topology.Homeomorph.Defs

/-!
# Unit vectors and orientations of an actual rank-one inner-product space

The singleton basis at a unit vector identifies its unit sphere with its orientation torsor.
Negating the vector negates the orientation. This is the fibre kernel of LFR51's orientation-cover
identification; it does not assert a global identification with the base tangent orientation cover.
-/

set_option autoImplicit false

noncomputable section

open Module FiniteDimensional

namespace DifferentialGeometry.Topology.VectorBundle

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

omit [InnerProductSpace ℝ W] in
private theorem unit_nonzero (u : {u : W // ‖u‖ = 1}) : u.val ≠ 0 := by
  intro hz
  have hu := u.property
  rw [hz, norm_zero] at hu
  exact zero_ne_one hu

def unitOrientation (hW : finrank ℝ W = 1) (u : {u : W // ‖u‖ = 1}) :
    Orientation ℝ W (Fin 1) :=
  (basisSingleton (Fin 1) hW u.val (unit_nonzero u)).orientation

variable {hW : finrank ℝ W = 1}

theorem unitOrientation_neg (u : {u : W // ‖u‖ = 1}) :
    unitOrientation hW ⟨-u.val, by simpa using u.property⟩ = -unitOrientation hW u := by
  let b := basisSingleton (Fin 1) hW u.val (unit_nonzero u)
  have hb : basisSingleton (Fin 1) hW (-u.val)
      (unit_nonzero ⟨-u.val, by simpa using u.property⟩) =
      b.unitsSMul (Function.update 1 0 (-1)) := by
    apply Basis.eq_of_apply_eq
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    simp [b, Basis.unitsSMul_apply]
  change (basisSingleton (Fin 1) hW (-u.val) _).orientation = -b.orientation
  rw [hb, Basis.orientation_neg_single]

theorem unitOrientation_bijective (hW : finrank ℝ W = 1) :
    Function.Bijective (unitOrientation hW) := by
  constructor
  · intro u v huv
    rcases RankOneQuotient.eq_or_eq_neg_of_finrank_eq_one hW u.property v.property with h | h
    · exact Subtype.ext h.symm
    · have hv : v = ⟨-u.val, by simpa using u.property⟩ := Subtype.ext h
      rw [hv, unitOrientation_neg] at huv
      exact False.elim (Module.Ray.ne_neg_self (unitOrientation hW u) huv)
  · intro o
    obtain ⟨u, hu⟩ := RankOneQuotient.exists_norm_eq_one_of_finrank_eq_one hW
    let b := basisSingleton (Fin 1) hW u (unit_nonzero ⟨u, hu⟩)
    rcases b.orientation_eq_or_eq_neg o with ho | ho
    · exact ⟨⟨u, hu⟩, ho.symm⟩
    · refine ⟨⟨-u, by simpa using hu⟩, ?_⟩
      rw [unitOrientation_neg (hW := hW) ⟨u, hu⟩]
      exact ho.symm

def unitOrientationEquiv (hW : finrank ℝ W = 1) :
    {u : W // ‖u‖ = 1} ≃ Orientation ℝ W (Fin 1) :=
  Equiv.ofBijective (unitOrientation hW) (unitOrientation_bijective hW)

attribute [local instance] DifferentialGeometry.VectorBundle.orientationTopology

local instance unitOrientationDiscrete : DiscreteTopology (Orientation ℝ W (Fin 1)) := ⟨rfl⟩

def unitOrientationHomeomorph (hW : finrank ℝ W = 1) :
    {u : W // ‖u‖ = 1} ≃ₜ Orientation ℝ W (Fin 1) := by
  letI unitOrientationsFinite : Finite (Orientation ℝ W (Fin 1)) :=
    Finite.of_equiv Bool (DifferentialGeometry.VectorBundle.orientationEquivBool
      (basisSingleton (Fin 1) hW
        (Classical.choose (RankOneQuotient.exists_norm_eq_one_of_finrank_eq_one hW))
        (unit_nonzero ⟨_, Classical.choose_spec
          (RankOneQuotient.exists_norm_eq_one_of_finrank_eq_one hW)⟩))).symm
  letI unitVectorsFinite : Finite {u : W // ‖u‖ = 1} :=
    Finite.of_equiv (Orientation ℝ W (Fin 1)) (unitOrientationEquiv hW).symm
  exact (unitOrientationEquiv hW).toHomeomorphOfDiscrete

theorem unitOrientation_map {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W']
    (hW : finrank ℝ W = 1) (hW' : finrank ℝ W' = 1) (e : W ≃ₗᵢ[ℝ] W')
    (u : {u : W // ‖u‖ = 1}) :
    unitOrientation hW' ⟨e u.val, by simpa using u.property⟩ =
      Orientation.map (Fin 1) e.toLinearEquiv (unitOrientation hW u) := by
  have hb : basisSingleton (Fin 1) hW' (e u.val)
      (unit_nonzero ⟨e u.val, by simpa using u.property⟩) =
      (basisSingleton (Fin 1) hW u.val (unit_nonzero u)).map e.toLinearEquiv := by
    apply Basis.eq_of_apply_eq
    intro i
    simp only [basisSingleton_apply, Basis.map_apply]
    rfl
  unfold unitOrientation
  rw [hb, Basis.orientation_map]

end DifferentialGeometry.Topology.VectorBundle
