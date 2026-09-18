import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialPairImage
import DifferentialGeometry.Topology.PiecewiseLinear.VertexBranchSection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_linearEquiv_normalForm_of_isCombinatorialManifold
    (hn : Module.finrank ℝ E = 3) (K M : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite M.faces] (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces)
    (hK : K.space ∈ 𝓝 p) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hMan : IsCombinatorialManifold 2 M)
    (hfiber : IsPLSphere 1 (M.space ∩ {x | ℓ x = ℓ p}))
    {u v : E} (hu : u ∈ closedStar M p) (hv : v ∈ closedStar M p)
    (hult : ℓ u < ℓ p) (hvlt : ℓ p < ℓ v) :
    ∃ (U V : Set E) (h : E → E) (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ IsPLHomeomorphOn h U V ∧ h p = 0 ∧
        ∀ᶠ y in 𝓝 p, (y ∈ M.space → (L (h y)).2.2 = 0) ∧ (ℓ y = ℓ p → (L (h y)).2.1 = 0) := by
  classical
  have hlinkM : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space := hMan p hp
  have hnegM := exists_mem_geometricLink_apply_lt_of_mem_closedStar M hp ℓ.toLinearMap hu hult
  have hposM := exists_mem_geometricLink_lt_apply_of_mem_closedStar M hp ℓ.toLinearMap hv hvlt
  obtain ⟨R, hRfin, -, hRK, -, hRside⟩ := exists_triangulation_union_with_halfSpace_faces K
    (isPolyhedron_space K) ℓ.toLinearMap.toAffineMap (ℓ p)
  let _ : Finite R.faces := hRfin.to_subtype
  change IsSubdivision (restrict R K.space) K at hRK
  let K₂ := restrict R K.space
  let _ : Finite K₂.faces := (restrict_faces_finite R K.space).to_subtype
  have hK₂space : K₂.space = K.space := hRK.space_eq
  have hside₂ : ∀ s ∈ K₂.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x} := by
    intro s hs
    simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] using
      hRside s (restrict_faces_subset R K.space hs)
  have hM₂ : IsSubdivision (restrict K₂ M.space) M := hRK.restrict M hM
  let M₂ := restrict K₂ M.space
  let _ : Finite M₂.faces := (restrict_faces_finite K₂ M.space).to_subtype
  have hM₂space : M₂.space = M.space := hM₂.space_eq
  have hM₂faces : M₂.faces ⊆ K₂.faces := restrict_faces_subset K₂ M.space
  have hpM₂ : ({p} : Finset E) ∈ M₂.faces := hM₂.singleton_mem hp
  have hsideM₂ : ∀ s ∈ M₂.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ.toLinearMap x ≤ ℓ.toLinearMap p}
      ∨ convexHull ℝ (s : Set E) ⊆ {x | ℓ.toLinearMap p ≤ ℓ.toLinearMap x} := by
    intro s hs
    simpa only [ContinuousLinearMap.coe_coe] using hside₂ s (hM₂faces hs)
  obtain ⟨f, hf, -, hflt, hfgt⟩ :=
    exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_preserving_height_sign hM₂ hp
      ℓ.toLinearMap hsideM₂
  have hlink₂ : IsPLSphere 1 (SimplicialComplex.geometricLink M₂ {p}).space :=
    hlinkM.of_isPLHomeomorphOn hf.symm
  have hneg₂ : ∃ x ∈ (SimplicialComplex.geometricLink M₂ {p}).space, ℓ x < ℓ p := by
    obtain ⟨x, hx, hlt⟩ := hnegM
    obtain ⟨y, hy, -⟩ := hflt.symm.subset ⟨hx, hlt⟩
    exact ⟨y, hy.1, hy.2⟩
  have hpos₂ : ∃ x ∈ (SimplicialComplex.geometricLink M₂ {p}).space, ℓ p < ℓ x := by
    obtain ⟨x, hx, hlt⟩ := hposM
    obtain ⟨y, hy, -⟩ := hfgt.symm.subset ⟨hx, hlt⟩
    exact ⟨y, hy.1, hy.2⟩
  obtain ⟨a, b, hab, hlevel⟩ := exists_pair_geometricLink_fiber_of_isPLSphere_one M₂ hpM₂
    ℓ.toLinearMap (by rw [hM₂space]; exact hfiber)
  obtain ⟨U, V, h, L, hU, hV, hpU, hPLh, hhp, hnear⟩ :=
    exists_linearEquiv_normalForm_of_geometricLink_section hn K₂ M₂ hM₂faces hpM₂
      (by rw [hK₂space]; exact hK) ℓ hℓ hside₂ hlink₂ hab hlevel hpos₂ hneg₂
  refine ⟨U, V, h, L, hU, hV, hpU, hPLh, hhp, ?_⟩
  rw [← hM₂space]
  exact hnear

end DifferentialGeometry.Topology.PiecewiseLinear
