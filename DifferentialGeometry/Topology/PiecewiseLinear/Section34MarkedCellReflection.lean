import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def section34SquareSign (a b : Bool) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  (if a then LinearEquiv.neg ℝ else LinearEquiv.refl ℝ ℝ).prodCongr
    (if b then LinearEquiv.neg ℝ else LinearEquiv.refl ℝ ℝ)

def section34CellSign (a b : Bool) : ((ℝ × ℝ) × ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × ℝ) :=
  (section34SquareSign a b).prodCongr (LinearEquiv.refl ℝ ℝ)

def section34SpokeSignPerm (a b : Bool) : Equiv.Perm (Fin 4) :=
  (if a then Equiv.swap 0 2 else Equiv.refl _).trans
    (if b then Equiv.swap 1 3 else Equiv.refl _)

private theorem square_sign_involutive (a b : Bool) :
    Function.Involutive (section34SquareSign a b) := by
  intro p
  cases a <;> cases b <;> simp [section34SquareSign]

private theorem square_sign_mapsTo (a b : Bool) :
    MapsTo (section34SquareSign a b) spliceSquare spliceSquare := by
  rintro ⟨x, y⟩ ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩
  cases a <;> cases b <;>
    simp only [section34SquareSign, Bool.false_eq_true, ↓reduceIte, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply, LinearEquiv.neg_apply, spliceSquare,
      mem_prod, mem_Icc] <;>
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private theorem square_sign_image (a b : Bool) :
    section34SquareSign a b '' spliceSquare = spliceSquare := by
  apply Subset.antisymm (image_subset_iff.mpr (square_sign_mapsTo a b))
  intro p hp
  exact ⟨section34SquareSign a b p, square_sign_mapsTo a b hp,
    square_sign_involutive a b p⟩

private theorem square_sign_leaf (a b : Bool) (i : Fin 4) :
    section34SquareSign a b (fourSpokeModelLeaf i) =
      fourSpokeModelLeaf (section34SpokeSignPerm a b i) := by
  cases a <;> cases b <;> fin_cases i <;>
    norm_num [section34SquareSign, section34SpokeSignPerm, fourSpokeModelLeaf,
      Equiv.swap_apply_def, Fin.ext_iff]

theorem section34_cell_sign_axis (a b : Bool) (t : ℝ) :
    section34CellSign a b (0, t) = (0, t) := by
  simp [section34CellSign]

theorem section34_cell_sign_face_image (a b : Bool) (T : Set ℝ) :
    section34CellSign a b '' (spliceSquare ×ˢ T) = spliceSquare ×ˢ T := by
  change Prod.map (section34SquareSign a b) id '' _ = _
  rw [prodMap_image_prod, square_sign_image, image_id]

theorem section34_cell_sign_ribbon_image (a b : Bool) (i : Fin 4) :
    section34CellSign a b '' section34MarkedRibbon i =
      section34MarkedRibbon (section34SpokeSignPerm a b i) := by
  change Prod.map (section34SquareSign a b) id '' _ = _
  rw [section34MarkedRibbon, prodMap_image_prod, image_id]
  have h := image_segment ℝ (section34SquareSign a b).toLinearMap.toAffineMap
    (0 : ℝ × ℝ) (fourSpokeModelLeaf i)
  change section34SquareSign a b '' _ =
    segment ℝ (section34SquareSign a b 0)
      (section34SquareSign a b (fourSpokeModelLeaf i)) at h
  rw [map_zero, square_sign_leaf] at h
  rw [h]
  rfl

theorem isPLHomeomorphOn_section34_cell_sign (a b : Bool) :
    IsPLHomeomorphOn (section34CellSign a b) spliceCylinder spliceCylinder := by
  have hpoly := isHPolytope_spliceCylinder.isPolyhedron
  have h := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    ((isPiecewiseAffineOn_of_affine
      (section34CellSign a b).toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hpoly (subset_univ _)) (section34CellSign a b).injective.injOn.bijOn_image
  change IsPLHomeomorphOn (section34CellSign a b) spliceCylinder
    (section34CellSign a b '' (spliceSquare ×ˢ Icc (0 : ℝ) 1)) at h
  rwa [section34_cell_sign_face_image] at h

end DifferentialGeometry.Topology.PiecewiseLinear
