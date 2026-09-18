import DifferentialGeometry.Topology.PiecewiseLinear.HeightCone
import DifferentialGeometry.Topology.PiecewiseLinear.ConeNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ConeBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_coneComplex_frontier_eq_lower_cap
    (K : Geometry.SimplicialComplex ℝ E) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) {p : E} {r : ℝ} (hp : p ∈ K.vertices) (hpr : ℓ p < r)
    (hother : ∀ v ∈ K.vertices, v ≠ p → r < ℓ v)
    {D : Set E} {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D)
    (hDr : D ⊆ {x | ℓ x = r}) (hgJ : g '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = r}) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (hpL : IsConeBase p L),
      L.faces.Finite ∧ IsPLBall 2 L.space ∧ L.space = D ∧
      frontier (coneComplex hpL).space = (K.space ∩ {x | ℓ x ≤ r}) ∪ D := by
  classical
  have hD : IsPLBall 2 D := ⟨g, hg⟩
  obtain ⟨L, hLfin, hLD⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 2 L.space := hLD.symm ▸ hD
  have hpL : IsConeBase p L := isConeBase_of_subset_fiber ℓ L (hLD.trans_le hDr) hpr.ne
  have hboundary := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L (hLD.symm ▸ hg)
  rw [simplexBoundary_stdVertices_space, hgJ] at hboundary
  have hcone := inter_le_eq_coneComplex_space_of_lt_other_vertices K ℓ.toAffineMap hp hpr hother
    (boundaryComplex 2 L) (hpL.of_faces_subset (boundaryComplex_faces_subset 2 L)) hboundary
  refine ⟨L, hpL, hLfin, hL, hLD, ?_⟩
  rw [frontier_coneComplex hdimE hpL hL, hLD, ← hcone, union_comm]
  rfl

theorem isSimplyEmbedded_lower_cap_of_lt_other_vertices (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) {p : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hp : p ∈ K.vertices) (hpr : ℓ p < r)
    (hother : ∀ v ∈ K.vertices, v ≠ p → r < ℓ v)
    {D : Set (EuclideanSpace ℝ (Fin 3))} {g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D)
    (hDr : D ⊆ {x | ℓ x = r}) (hgJ : g '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = r}) :
    IsSimplyEmbedded ((K.space ∩ {x | ℓ x ≤ r}) ∪ D) := by
  obtain ⟨L, hpL, hLfin, hL, -, hfront⟩ :=
    exists_coneComplex_frontier_eq_lower_cap K (by simp) ℓ hp hpr hother hg hDr hgJ
  rw [← hfront]
  convert I.isSimplyEmbedded_frontier_coneComplex L p hpL hLfin hL using 1
  congr 1
  ext x
  simp only [mem_coneComplex_space_iff]

theorem isSimplyEmbedded_upper_cap_of_other_vertices_lt (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) {p : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hp : p ∈ K.vertices) (hpr : r < ℓ p)
    (hother : ∀ v ∈ K.vertices, v ≠ p → ℓ v < r)
    {D : Set (EuclideanSpace ℝ (Fin 3))} {g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D)
    (hDr : D ⊆ {x | ℓ x = r}) (hgJ : g '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = r}) :
    IsSimplyEmbedded ((K.space ∩ {x | r ≤ ℓ x}) ∪ D) := by
  have hDr' : D ⊆ {x | (-ℓ) x = -r} := fun x hx => by
    simpa only [LinearMap.neg_apply, neg_inj] using hDr hx
  have hgJ' : g '' stdSimplexBoundary 2 = K.space ∩ {x | (-ℓ) x = -r} := by
    simpa only [LinearMap.neg_apply, neg_inj] using hgJ
  have h := isSimplyEmbedded_lower_cap_of_lt_other_vertices I K (-ℓ) hp (neg_lt_neg hpr)
    (fun v hv hvp => neg_lt_neg (hother v hv hvp)) hg hDr' hgJ'
  simpa only [LinearMap.neg_apply, neg_le_neg_iff] using h

end DifferentialGeometry.Topology.PiecewiseLinear
