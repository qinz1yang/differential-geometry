import DifferentialGeometry.Topology.PiecewiseLinear.CirclePartition
import DifferentialGeometry.Topology.PiecewiseLinear.FiberCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalCycles

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_finite_isPLSphere_decomposition_of_subset_fiber
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hG : IsCombinatorialManifold 1 G) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hGr : G.space ⊆ {x | ℓ x = r}) :
    ∃ C : Set (Set E), C.Finite ∧ (∀ S ∈ C, IsPLSphere 1 S) ∧
      C.PairwiseDisjoint id ∧ G.space = ⋃₀ C := by
  classical
  obtain ⟨e, π, hleft, hfixed, -⟩ := exists_affine_coordinates_of_linear_fiber hdimE ℓ hℓ r
  have hπinj : InjOn π G.space := by
    intro x hx y hy hxy
    exact ((hfixed x).mpr (hGr hx)).symm.trans ((congrArg e hxy).trans ((hfixed y).mpr (hGr hy)))
  obtain ⟨L, hLfin, hLspace, -, hπ⟩ := exists_simplicialComplex_image_of_affineOn_faces G (f := π)
    (fun _ _ => ⟨π.toAffineMap, fun _ _ => rfl⟩) hπinj
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsCombinatorialManifold 1 L := hG.of_isPLHomeomorphOn hπ
  obtain ⟨C, hCfin, hCsphere, hCdisjoint, hCcover⟩ := exists_finite_isPLSphere_decomposition L hL
  have hback : e '' L.space = G.space := by
    rw [hLspace]
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      rwa [(hfixed y).mpr (hGr hy)]
    · intro hx
      exact ⟨π x, mem_image_of_mem π hx, (hfixed x).mpr (hGr hx)⟩
  refine ⟨(fun S => e '' S) '' C, hCfin.image _, ?_, ?_, ?_⟩
  · rintro S ⟨D, hD, rfl⟩
    have hDP : IsPolyhedron D := (hCsphere D hD).isPolyhedron
    have he : IsPLHomeomorphOn e D (e '' D) :=
      isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hDP
        ((isPiecewiseAffineOn_of_affine e isOpen_univ).mono_of_isPolyhedron hDP (subset_univ _))
        ⟨fun x hx => mem_image_of_mem e hx, hleft.injective.injOn, fun _ h => h⟩
    exact (hCsphere D hD).of_isPLHomeomorphOn he
  · rintro S ⟨D, hD, rfl⟩ T ⟨F, hF, rfl⟩ hDF
    have hne : D ≠ F := fun h => hDF (congrArg (fun A => e '' A) h)
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    have hzy' : z = y := hleft.injective hzy
    subst z
    exact Set.disjoint_left.mp (hCdisjoint hD hF hne) hy hz
  · rw [← hback, hCcover, image_sUnion]

theorem exists_finite_isPLSphere_decomposition_fiber
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ}
    (hr : ∀ v ∈ K.vertices, ℓ v ≠ r) :
    ∃ C : Set (Set E), C.Finite ∧ (∀ S ∈ C, IsPLSphere 1 S) ∧
      C.PairwiseDisjoint id ∧ K.space ∩ {x | ℓ x = r} = ⋃₀ C := by
  obtain ⟨G, hGfin, hGspace, hG⟩ := exists_isCombinatorialManifold_fiber K hK hdimE ℓ hℓ hr
  let _ : Finite G.faces := hGfin.to_subtype
  obtain ⟨C, hCfin, hCsphere, hCdisjoint, hCspace⟩ :=
    exists_finite_isPLSphere_decomposition_of_subset_fiber G hG hdimE ℓ hℓ
      (r := r) (hGspace.trans_le inter_subset_right)
  exact ⟨C, hCfin, hCsphere, hCdisjoint, hGspace.symm.trans hCspace⟩

theorem levelPolygons_eq_of_finite_disjoint_cover {S : Set E} (ℓ : E → ℝ) (r : ℝ)
    {C : Set (Set E)} (hC : C.Finite) (hCsphere : ∀ T ∈ C, IsPLSphere 1 T)
    (hdisjoint : C.PairwiseDisjoint id) (hcover : S ∩ {x | ℓ x = r} = ⋃₀ C) :
    levelPolygons S ℓ r = C := by
  rw [levelPolygons, hcover]
  exact setOf_isPLSphere_one_subset_sUnion_eq hC hCsphere hdisjoint

theorem finite_levelPolygons_of_ne_vertex_heights
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hr : ∀ v ∈ K.vertices, ℓ v ≠ r) :
    (levelPolygons K.space ℓ r).Finite := by
  obtain ⟨C, hC, hCsphere, hdisjoint, hcover⟩ :=
    exists_finite_isPLSphere_decomposition_fiber K hK hdimE ℓ hℓ hr
  rw [levelPolygons_eq_of_finite_disjoint_cover ℓ r hC hCsphere hdisjoint hcover]
  exact hC

theorem pairwiseDisjoint_levelPolygons_of_ne_vertex_heights
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hr : ∀ v ∈ K.vertices, ℓ v ≠ r) :
    (levelPolygons K.space ℓ r).PairwiseDisjoint id := by
  obtain ⟨C, hC, hCsphere, hdisjoint, hcover⟩ :=
    exists_finite_isPLSphere_decomposition_fiber K hK hdimE ℓ hℓ hr
  rw [levelPolygons_eq_of_finite_disjoint_cover ℓ r hC hCsphere hdisjoint hcover]
  exact hdisjoint

theorem sUnion_levelPolygons_of_ne_vertex_heights
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hr : ∀ v ∈ K.vertices, ℓ v ≠ r) :
    ⋃₀ levelPolygons K.space ℓ r = K.space ∩ {x | ℓ x = r} := by
  obtain ⟨C, hC, hCsphere, hdisjoint, hcover⟩ :=
    exists_finite_isPLSphere_decomposition_fiber K hK hdimE ℓ hℓ hr
  rw [levelPolygons_eq_of_finite_disjoint_cover ℓ r hC hCsphere hdisjoint hcover]
  exact hcover.symm

theorem isPLSphere_one_fiber_iff_isConnected
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hr : ∀ v ∈ K.vertices, ℓ v ≠ r) :
    IsPLSphere 1 (K.space ∩ {x | ℓ x = r}) ↔ IsConnected (K.space ∩ {x | ℓ x = r}) := by
  obtain ⟨C, hC, hCsphere, hdisjoint, hcover⟩ :=
    exists_finite_isPLSphere_decomposition_fiber K hK hdimE ℓ hℓ hr
  rw [hcover]
  exact isPLSphere_one_sUnion_iff_isConnected hC hCsphere hdisjoint

theorem isPLSphere_one_fiber_iff_encard_levelPolygons_eq_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hr : ∀ v ∈ K.vertices, ℓ v ≠ r) :
    IsPLSphere 1 (K.space ∩ {x | ℓ x = r}) ↔ (levelPolygons K.space ℓ r).encard = 1 := by
  obtain ⟨C, hC, hCsphere, hdisjoint, hcover⟩ :=
    exists_finite_isPLSphere_decomposition_fiber K hK hdimE ℓ hℓ hr
  rw [levelPolygons_eq_of_finite_disjoint_cover ℓ r hC hCsphere hdisjoint hcover, hcover]
  exact isPLSphere_one_sUnion_iff_encard_eq_one hC hCsphere hdisjoint
end DifferentialGeometry.Topology.PiecewiseLinear
