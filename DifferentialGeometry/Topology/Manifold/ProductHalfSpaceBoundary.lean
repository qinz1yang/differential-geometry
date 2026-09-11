import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev ER := E2 × E1
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private def zH : EuclideanHalfSpace 1 := ⟨0, by simp⟩
private def inward : ER := (0, WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)))

def productHalfSpaceBoundaryInclusion (x : E2) : IH := (x, zH)

theorem productHalfSpaceBoundaryInclusion_apply (x : E2) :
    IR (productHalfSpaceBoundaryInclusion x) = (x, (0 : E1)) := rfl

private theorem frontier_product : frontier (range IR) = {x : ER | x.2 = 0} := by
  rw [ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ,
    frontier_univ_prod_eq, EuclideanHalfSpaceInstance.frontier_range_modelWithCornersEuclideanHalfSpace_eq]
  ext x
  simp only [mem_prod, mem_univ, true_and, mem_ofPred_eq]
  constructor
  · intro h
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h
  · intro h
    rw [h]
    rfl
private theorem range_inclusion : range (IR ∘ productHalfSpaceBoundaryInclusion) = {x : ER | x.2 = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    refine ⟨x.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact h.symm
private theorem inward_enters (y : ER) (hy : y ∈ frontier (range IR)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioc (0 : ℝ) ε, y + t • inward ∈ interior (range IR) := by
  rw [frontier_product] at hy
  refine ⟨1, one_pos, ?_⟩
  intro t ht
  rw [ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ,
    interior_prod_eq, interior_univ, interior_range_modelWithCornersEuclideanHalfSpace]
  change True ∧ 0 < y.2 0 + t * 1
  refine ⟨trivial, ?_⟩
  have hz : y.2 = 0 := hy
  rw [hz]
  simpa using ht.1
private theorem inclusion_derivative (y : E2) :
    fderiv ℝ (IR ∘ productHalfSpaceBoundaryInclusion ∘ (𝓡 2).symm) y =
      ContinuousLinearMap.inl ℝ E2 E1 := by
  change fderiv ℝ (ContinuousLinearMap.inl ℝ E2 E1 : E2 → ER) y = _
  exact (ContinuousLinearMap.inl ℝ E2 E1).fderiv
private theorem inward_transverse (y : E2) :
    inward ∉ range (fderiv ℝ (IR ∘ productHalfSpaceBoundaryInclusion ∘ (𝓡 2).symm) y) := by
  rw [inclusion_derivative]
  rintro ⟨x, hx⟩
  have h := congrArg (fun z : ER => z.2 0) hx
  change (0 : ℝ) = 1 at h
  exact zero_ne_one h
private theorem frontier_haar_zero :
    letI : MeasurableSpace ER := borel ER
    haveI : BorelSpace ER := ⟨rfl⟩
    ((Module.finBasis ℝ ER).addHaar : MeasureTheory.Measure ER) (frontier (range IR)) = 0 := by
  let : MeasurableSpace ER := borel ER
  let : BorelSpace ER := ⟨rfl⟩
  let K : Submodule ℝ ER := (ContinuousLinearMap.snd ℝ E2 E1).toLinearMap.ker
  have hK : {x : ER | x.2 = 0} = (K : Set ER) := by
    ext x
    rfl
  have hne : K ≠ ⊤ := by
    intro h
    have hm : inward ∈ K := h ▸ Submodule.mem_top
    have hz : inward.2 = 0 := hm
    have he := congrArg (fun z : E1 => z 0) hz
    change (1 : ℝ) = 0 at he
    exact one_ne_zero he
  rw [frontier_product, hK]
  exact MeasureTheory.Measure.addHaar_submodule (Module.finBasis ℝ ER).addHaar K hne

abbrev productHalfSpaceBoundaryModel : HasSmoothBoundary ER IH IR where
  boundaryE := E2
  boundaryENormedGroup := inferInstance
  boundaryENormedSpace := inferInstance
  boundaryEInnerProductSpace := inferInstance
  boundaryEFiniteDimensional := inferInstance
  boundaryH := E2
  boundaryHTopologicalSpace := inferInstance
  boundaryI := 𝓡 2
  boundaryIBoundaryless := inferInstance
  inclH := productHalfSpaceBoundaryInclusion
  inclH_continuous := continuous_id.prodMk continuous_const
  inclH_injective := fun _ _ h => congrArg Prod.fst h
  inclH_isInducing := _root_.isInducing_prodMkLeft zH
  inclH_isClosed_image := by
    rw [range_inclusion]
    exact isClosed_singleton.preimage continuous_snd
  projE := Prod.fst
  projE_continuous := continuous_fst
  projE_contDiff := contDiff_fst
  I_inclH_boundaryI_symm_contDiff := by
    change ContDiff ℝ ∞ (fun x : E2 => (x, (0 : E1)))
    exact contDiff_id.prodMk contDiff_const
  range_I_inclH := range_inclusion.trans frontier_product.symm
  proj_inclH_compat := fun _ => rfl
  inwardCoordE := inward
  inwardCoordE_enters := inward_enters
  inwardCoordE_transverse := inward_transverse
  range_frontier_basis_addHaar_zero := by
    intro _
    exact frontier_haar_zero
  finrank_boundaryE_succ := by
    intro _
    simp [ER, E2, E1]
end DifferentialGeometry.Topology.Manifold
