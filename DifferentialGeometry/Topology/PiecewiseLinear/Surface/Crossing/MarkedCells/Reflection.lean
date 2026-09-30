import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedCellSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def crossingSquareReflection (a b : Bool) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  (if a then LinearEquiv.neg ℝ else LinearEquiv.refl ℝ ℝ).prodCongr
    (if b then LinearEquiv.neg ℝ else LinearEquiv.refl ℝ ℝ)

def crossingCylinderReflection (a b : Bool) : ((ℝ × ℝ) × ℝ) ≃ₗ[ℝ] ((ℝ × ℝ) × ℝ) :=
  (crossingSquareReflection a b).prodCongr (LinearEquiv.refl ℝ ℝ)

def crossingSpokeReflection (a b : Bool) : Equiv.Perm (Fin 4) :=
  (if a then Equiv.swap 0 2 else Equiv.refl _).trans
    (if b then Equiv.swap 1 3 else Equiv.refl _)

private theorem square_sign_involutive (a b : Bool) :
    Function.Involutive (crossingSquareReflection a b) := by
  intro p
  cases a <;> cases b <;> simp [crossingSquareReflection]

private theorem square_sign_mapsTo (a b : Bool) :
    MapsTo (crossingSquareReflection a b) spliceSquare spliceSquare := by
  rintro ⟨x, y⟩ ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩
  cases a <;> cases b <;>
    simp only [crossingSquareReflection, Bool.false_eq_true, ↓reduceIte, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply, LinearEquiv.neg_apply, spliceSquare,
      mem_prod, mem_Icc] <;>
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private theorem square_sign_image (a b : Bool) :
    crossingSquareReflection a b '' spliceSquare = spliceSquare := by
  apply Subset.antisymm (image_subset_iff.mpr (square_sign_mapsTo a b))
  intro p hp
  exact ⟨crossingSquareReflection a b p, square_sign_mapsTo a b hp,
    square_sign_involutive a b p⟩

private theorem square_sign_leaf (a b : Bool) (i : Fin 4) :
    crossingSquareReflection a b (fourSpokeModelLeaf i) =
      fourSpokeModelLeaf (crossingSpokeReflection a b i) := by
  cases a <;> cases b <;> fin_cases i <;>
    norm_num [crossingSquareReflection, crossingSpokeReflection, fourSpokeModelLeaf,
      Equiv.swap_apply_def, Fin.ext_iff]

theorem crossingCylinderReflection_image_axis (a b : Bool) (t : ℝ) :
    crossingCylinderReflection a b (0, t) = (0, t) := by
  simp [crossingCylinderReflection]

theorem crossingCylinderReflection_image_cap (a b : Bool) (T : Set ℝ) :
    crossingCylinderReflection a b '' (spliceSquare ×ˢ T) = spliceSquare ×ˢ T := by
  change Prod.map (crossingSquareReflection a b) id '' _ = _
  rw [prodMap_image_prod, square_sign_image, image_id]

theorem crossingCylinderReflection_image_ribbon (a b : Bool) (i : Fin 4) :
    crossingCylinderReflection a b '' section34MarkedRibbon i =
      section34MarkedRibbon (crossingSpokeReflection a b i) := by
  change Prod.map (crossingSquareReflection a b) id '' _ = _
  rw [section34MarkedRibbon, prodMap_image_prod, image_id]
  have h := image_segment ℝ (crossingSquareReflection a b).toLinearMap.toAffineMap
    (0 : ℝ × ℝ) (fourSpokeModelLeaf i)
  change crossingSquareReflection a b '' _ =
    segment ℝ (crossingSquareReflection a b 0)
      (crossingSquareReflection a b (fourSpokeModelLeaf i)) at h
  rw [map_zero, square_sign_leaf] at h
  rw [h]
  rfl

theorem isPLHomeomorphOn_crossingCylinderReflection (a b : Bool) :
    IsPLHomeomorphOn (crossingCylinderReflection a b) spliceCylinder spliceCylinder := by
  have hpoly := isHPolytope_spliceCylinder.isPolyhedron
  have h := isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly
    ((isPiecewiseAffineOn_of_affine
      (crossingCylinderReflection a b).toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hpoly (subset_univ _)) (crossingCylinderReflection a b).injective.injOn.bijOn_image
  change IsPLHomeomorphOn (crossingCylinderReflection a b) spliceCylinder
    (crossingCylinderReflection a b '' (spliceSquare ×ˢ Icc (0 : ℝ) 1)) at h
  rwa [crossingCylinderReflection_image_cap] at h

end DifferentialGeometry.Topology.PiecewiseLinear
