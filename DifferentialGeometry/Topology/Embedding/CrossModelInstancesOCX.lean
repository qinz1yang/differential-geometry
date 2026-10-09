import DifferentialGeometry.Topology.Embedding.CrossModelHalfSpaceOCX
import DifferentialGeometry.Topology.Manifold.InteriorAtlas

/-!
# Cross-model immersions, part 3: model changes and compiled instances (lane O-CROSS, G1)

* `halfCollarLinearEquiv_OCX`: the coordinate permutation `((a, b), c) ↦ (c, a, b)` of
  `(ℝ¹ × ℝ¹) × ℝ¹` onto `ℝ³`; it matches `range (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))` (the model
  `torusModel.prod (𝓡∂ 1)` of `T² × [0, 1]`) with `range (𝓡∂ 3)`
  (`halfCollarLinearEquiv_OCX_range`).
* `halfCollarModelDiffeomorph_OCX : H³ ≃ₘ⟮𝓡∂ 3, torusModel.prod (𝓡∂ 1)⟯ (ℝ¹ × ℝ¹) × H¹`, and its
  smooth-embedding instance of the linear kernel
  (`isSmoothEmbedding_halfCollarModelDiffeomorph_OCX`).
* EASY / HARD instances on the open half-space `U = int H³` with its two structures (the
  `𝓡∂ 3` structure of an open subset and the boundaryless `𝓘(ℝ, ℝ³)` structure of
  `interiorChartedSpace`): `interiorAtlasDiffeomorph` is a smooth embedding `𝓡∂ 3 → 𝓘(ℝ, ℝ³)`
  (`isSmoothEmbedding_interiorAtlasDiffeomorph_OCX`) and its inverse one `𝓘(ℝ, ℝ³) → 𝓡∂ 3`
  (`isSmoothEmbedding_interiorAtlasDiffeomorph_symm_OCX`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace Manifold

/-- The coordinate permutation `((a, b), c) ↦ (c, a, b)`. -/
def halfCollarLinearEquiv_OCX :
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => WithLp.toLp 2 ![v.2 0, v.1.1 0, v.1.2 0]
      map_add' := fun v w => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun c v => by
        ext i
        fin_cases i <;> simp
      invFun := fun z =>
        ((WithLp.toLp 2 ![z 1], WithLp.toLp 2 ![z 2]), WithLp.toLp 2 ![z 0])
      left_inv := fun v => by
        refine Prod.ext (Prod.ext ?_ ?_) ?_ <;>
        · ext i
          fin_cases i
          simp
      right_inv := fun z => by
        ext i
        fin_cases i <;> simp }

theorem halfCollarLinearEquiv_OCX_apply_zero
    (v : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) :
    halfCollarLinearEquiv_OCX v 0 = v.2 0 := rfl

/-- `halfCollarLinearEquiv_OCX` matches the range of the half-collar model with the half-space. -/
theorem halfCollarLinearEquiv_OCX_range
    {v : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)} :
    halfCollarLinearEquiv_OCX v + 0 ∈ range (𝓡∂ 3) ↔
      v ∈ range (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) := by
  rw [add_zero, range_modelWithCornersEuclideanHalfSpace, ModelWithCorners.range_prod,
    ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace]
  simp [halfCollarLinearEquiv_OCX_apply_zero]

/-- The model change `H³ ≅ (ℝ¹ × ℝ¹) × H¹` between `𝓡∂ 3` and the half-collar model. -/
def halfCollarModelDiffeomorph_OCX :
    Diffeomorph (𝓡∂ 3) (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (EuclideanHalfSpace 3)
      (ModelProd (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
        (EuclideanHalfSpace 1)) ∞ :=
  modelAffineDiffeomorph_OCX (𝓡∂ 3) (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
    halfCollarLinearEquiv_OCX.symm 0 (fun v => by
      rw [add_zero, ← halfCollarLinearEquiv_OCX_range, ContinuousLinearEquiv.apply_symm_apply,
        add_zero])

/-- **Instance of the linear kernel**: the model change is a smooth embedding between the two
models (identity followed by a cross-model diffeomorphism). -/
theorem isSmoothEmbedding_halfCollarModelDiffeomorph_OCX :
    IsSmoothEmbedding (𝓡∂ 3) (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞
      halfCollarModelDiffeomorph_OCX := by
  have h := (IsSmoothEmbedding.id (I := 𝓡∂ 3) (M := EuclideanHalfSpace 3)
    (n := ∞)).diffeomorph_comp_linear_OCX halfCollarLinearEquiv_OCX.symm
      (fun v => by
        rw [add_zero, ← halfCollarLinearEquiv_OCX_range, ContinuousLinearEquiv.apply_symm_apply,
          add_zero])
      halfCollarModelDiffeomorph_OCX
  exact h

section Interior

/-- The open half-space `int H³` (as the intrinsic interior of the model `H³`). -/
abbrev openHalfSpaceOpens_OCX : TopologicalSpace.Opens (EuclideanHalfSpace 3) :=
  DifferentialGeometry.Manifold.intrinsicInterior (𝓡∂ 3) ∞ (by simp)

/-- **EASY-direction instance**: `int H³` with its `𝓡∂ 3` structure is smoothly embedded in
`int H³` with the boundaryless `𝓘(ℝ, ℝ³)` structure by the identity. -/
theorem isSmoothEmbedding_interiorAtlasDiffeomorph_OCX :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace (𝓡∂ 3) ∞
      (M := openHalfSpaceOpens_OCX)
    haveI := DifferentialGeometry.Manifold.interiorIsManifold (𝓡∂ 3) ∞
      (M := openHalfSpaceOpens_OCX)
    IsSmoothEmbedding (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph (𝓡∂ 3) ∞
        (M := openHalfSpaceOpens_OCX)) := by
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace (𝓡∂ 3) ∞
    (M := openHalfSpaceOpens_OCX)
  have _ := DifferentialGeometry.Manifold.interiorIsManifold (𝓡∂ 3) ∞
    (M := openHalfSpaceOpens_OCX)
  exact (IsSmoothEmbedding.id (I := 𝓡∂ 3) (M := openHalfSpaceOpens_OCX)
    (n := ∞)).diffeomorph_comp_fromHalfSpace_OCX
      (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph (𝓡∂ 3) ∞
        (M := openHalfSpaceOpens_OCX))

/-- **HARD-direction instance**: the inverse identification `int H³ (𝓘(ℝ, ℝ³)) → int H³ (𝓡∂ 3)`
is a smooth embedding (recentring along `e₀` of the boundaryless source model). -/
theorem isSmoothEmbedding_interiorAtlasDiffeomorph_symm_OCX :
    letI := DifferentialGeometry.Manifold.interiorChartedSpace (𝓡∂ 3) ∞
      (M := openHalfSpaceOpens_OCX)
    haveI := DifferentialGeometry.Manifold.interiorIsManifold (𝓡∂ 3) ∞
      (M := openHalfSpaceOpens_OCX)
    IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡∂ 3) ∞
      (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph (𝓡∂ 3) ∞
        (M := openHalfSpaceOpens_OCX)).symm := by
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace (𝓡∂ 3) ∞
    (M := openHalfSpaceOpens_OCX)
  have _ := DifferentialGeometry.Manifold.interiorIsManifold (𝓡∂ 3) ∞
    (M := openHalfSpaceOpens_OCX)
  have hs : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
    simp at h1
  exact (IsSmoothEmbedding.id (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
    (M := openHalfSpaceOpens_OCX) (n := ∞)).diffeomorph_comp_toHalfSpace_OCX
      (EuclideanSpace.single 0 1) hs (fun _ => modelWithCornersSelf_shift_range_OCX _)
      (DifferentialGeometry.Manifold.interiorAtlasDiffeomorph (𝓡∂ 3) ∞
        (M := openHalfSpaceOpens_OCX)).symm

/-- The boundary direction of `𝓡∂ 2` satisfies the source hypothesis of the HARD direction (the
fibre disks of the edge bundle are modelled on `𝓡∂ 2`). -/
theorem halfSpaceBoundaryShift_OCX_two :
    halfSpaceBoundaryShift_OCX 0 ≠ 0 ∧
      ∀ v, v + halfSpaceBoundaryShift_OCX 0 ∈ range (𝓡∂ 2) ↔ v ∈ range (𝓡∂ 2) :=
  ⟨halfSpaceBoundaryShift_OCX_ne_zero 0, fun _ => halfSpaceBoundaryShift_OCX_range⟩

end Interior

end Manifold
