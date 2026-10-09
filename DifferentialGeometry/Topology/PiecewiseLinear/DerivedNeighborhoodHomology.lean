/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.BettiNumber
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

open Classical in
noncomputable instance finite_derivedNeighborhood_faces
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Finite (derivedNeighborhood K L).faces :=
  (derivedNeighborhood_faces_finite K L).to_subtype

open Classical in
noncomputable def derivedNeighborhoodHomotopyEquiv (hL : L.faces ⊆ K.faces) :
    ContinuousMap.HomotopyEquiv (derivedNeighborhood K L).space L.space := by
  let e : derivedNeighborhoodSubcomplex K L ≃ₜ L.space := {
    toFun := fun x => ⟨x.1.1, x.2⟩
    invFun := fun x => ⟨⟨x.1, subcomplex_space_subset_derivedNeighborhood hL x.2⟩, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact (derivedNeighborhoodStrongDeformationRetract hL).toHomotopyEquiv.trans e.toHomotopyEquiv

open Classical in
theorem bettiNumber_derivedNeighborhood_eq (k : Type) [Field k] (hL : L.faces ⊆ K.faces) (q : ℕ) :
    Homology.bettiNumber k (TopCat.of (derivedNeighborhood K L).space) q =
      Homology.bettiNumber k (TopCat.of L.space) q :=
  Homology.bettiNumber_eq_of_homotopyEquiv k
    (X := TopCat.of (derivedNeighborhood K L).space) (Y := TopCat.of L.space)
    (derivedNeighborhoodHomotopyEquiv hL) q

open Classical in
theorem bettiOne_derivedNeighborhood_eq (hL : L.faces ⊆ K.faces) :
    Homology.bettiOne (derivedNeighborhood K L).space = Homology.bettiOne L.space :=
  bettiNumber_derivedNeighborhood_eq ℚ hL 1

open Classical in
theorem eulerChar_derivedNeighborhood_eq [Finite L.faces] (hL : L.faces ⊆ K.faces) :
    eulerChar (derivedNeighborhood K L) = eulerChar L := by
  rw [eulerChar_eq_singular (derivedNeighborhood K L) ℚ, eulerChar_eq_singular L ℚ]
  exact Homology.eulerChar_eq_of_homotopyEquiv ℚ
    (X := TopCat.of (derivedNeighborhood K L).space) (Y := TopCat.of L.space)
    (derivedNeighborhoodHomotopyEquiv hL)

end DifferentialGeometry.Topology.PiecewiseLinear
