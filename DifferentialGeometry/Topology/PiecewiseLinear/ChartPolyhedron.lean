import DifferentialGeometry.Topology.PiecewiseLinear.ChartGlue
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

theorem PLPieceIn.isPolyhedron_inter_preimage_chart_of_isPolyhedron
    {Y : Set X} (T : PLPieceIn E n X Y)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsPolyhedron C) (hCe : C ⊆ e.target) :
    IsPolyhedron (T.complex.space ∩ T.map ⁻¹' (e.symm '' C)) := by
  obtain ⟨ι, hι, D, hD, rfl⟩ := hC
  let _ := hι
  rw [image_iUnion, preimage_iUnion, inter_iUnion]
  exact IsPolyhedron.iUnion fun i => T.isPolyhedron_inter_preimage_chart e he (hD i)
    ((subset_iUnion D i).trans hCe)

theorem PLPieceIn.isPolyhedron_inter_preimage_chart_symm
    {Y : Set X} (T : PLPieceIn E n X Y)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsPolyhedron C) (hCe : C ⊆ e.target) :
    IsPolyhedron (C ∩ e.symm ⁻¹' Y) := by
  have hpre := T.isPolyhedron_inter_preimage_chart_of_isPolyhedron e he hC hCe
  have hsub : T.complex.space ∩ T.map ⁻¹' (e.symm '' C) ⊆
      T.complex.space ∩ T.map ⁻¹' e.source := by
    rintro x ⟨hx, y, hy, hxy⟩
    refine ⟨hx, ?_⟩
    change T.map x ∈ e.source
    rw [← hxy]
    exact e.map_target (hCe hy)
  have hpl := (T.isPiecewiseAffineOn_chart e he).mono_of_isPolyhedron hpre hsub
  have hinj := e.injOn.comp (T.bijOn.injOn.mono inter_subset_left)
    (fun x hx => (hsub hx).2)
  have himage : (e ∘ T.map) '' (T.complex.space ∩ T.map ⁻¹' (e.symm '' C)) =
      C ∩ e.symm ⁻¹' Y := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, z, hz, hzx⟩, rfl⟩
      have heq : e (T.map x) = z := by rw [← hzx, e.right_inv (hCe hz)]
      constructor
      · change e (T.map x) ∈ C
        rwa [heq]
      · change e.symm (e (T.map x)) ∈ Y
        rw [heq, hzx]
        exact T.bijOn.mapsTo hx
    · rintro ⟨hy, hyY⟩
      obtain ⟨x, hx, hxy⟩ := T.bijOn.surjOn hyY
      refine ⟨x, ⟨hx, y, hy, hxy.symm⟩, ?_⟩
      change e (T.map x) = y
      rw [hxy, e.right_inv (hCe hy)]
  rw [← himage]
  exact hpre.image_of_isPiecewiseAffineOn hpl hinj

theorem PLPieceIn.exists_isPolyhedron_chart_neighborhood
    {N C J : Set X} (T : PLPieceIn E n X N)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) (hC : IsCompact C) (hCe : C ⊆ e.source)
    (hCN : C \ J ⊆ interior N) :
    ∃ P : Set (EuclideanSpace ℝ (Fin n)), IsPolyhedron P ∧
      (e '' C) \ (e '' J) ⊆ interior P ∧ P ⊆ e.target ∧ e.symm '' P ⊆ N := by
  have hCt : e '' C ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hCe hx)
  obtain ⟨Q, hQ, hCQ, hQt⟩ := exists_isPolyhedron_neighborhood
    (hC.image_of_continuousOn (e.continuousOn.mono hCe)) e.open_target hCt
  refine ⟨Q ∩ e.symm ⁻¹' N, T.isPolyhedron_inter_preimage_chart_symm e he hQ hQt,
    ?_, inter_subset_left.trans hQt, ?_⟩
  · intro y hy
    rw [interior_inter]
    refine ⟨hCQ hy.1, ?_⟩
    obtain ⟨x, hx, rfl⟩ := hy.1
    have hxJ : x ∉ J := fun hxJ => hy.2 ⟨x, hxJ, rfl⟩
    apply mem_interior_iff_mem_nhds.mpr
    apply (e.continuousAt_symm (e.map_source (hCe hx))).preimage_mem_nhds
    rw [e.left_inv (hCe hx)]
    exact mem_interior_iff_mem_nhds.mp (hCN ⟨hx, hxJ⟩)
  · rintro _ ⟨y, hy, rfl⟩
    exact hy.2

end DifferentialGeometry.Topology.PiecewiseLinear
