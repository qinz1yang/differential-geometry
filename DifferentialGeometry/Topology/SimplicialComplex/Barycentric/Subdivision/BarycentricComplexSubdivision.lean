import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricGeometric
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricCoverage

namespace DifferentialGeometry.Topology.Engulfing

open Set
open scoped BigOperators

variable {E : Type*} [DecidableEq E] [AddCommGroup E] [Module ℝ E]

omit [DecidableEq E] in
theorem isFaceChain.convexHull_chainCentroids_subset {C : Finset (Finset E)}
    (hC : isFaceChain C) (V : Finset E) (hCV : ∀ s ∈ C, s ⊆ V) :
    convexHull ℝ (chainCentroids id C : Set E) ⊆ convexHull ℝ (V : Set E) := by
  classical
  apply convexHull_min _ (convex_convexHull ℝ (V : Set E))
  intro x hx
  obtain ⟨s, hs, rfl⟩ := mem_chainCentroids.mp hx
  exact convexHull_mono (hCV s hs) (s.centroid_mem_convexHull (hC.1 s hs))

theorem isFaceChain.convexHull_chainCentroids_inter_of_complex
    (K : Geometry.SimplicialComplex ℝ E) {C D : Finset (Finset E)}
    (hC : isFaceChain C) (hD : isFaceChain D) (hCne : C.Nonempty) (hDne : D.Nonempty)
    (hCK : ∀ s ∈ C, s ∈ K.faces) (hDK : ∀ s ∈ D, s ∈ K.faces) :
    convexHull ℝ (chainCentroids id C : Set E) ∩ convexHull ℝ (chainCentroids id D : Set E) =
      convexHull ℝ (chainCentroids id (C ∩ D) : Set E) := by
  classical
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  obtain ⟨W, hWD, hDW⟩ := hD.exists_largest hDne
  have hVK := hCK V hVC
  have hWK := hDK W hWD
  let T := V ∩ W
  let C' := C.filter (fun s => s ⊆ T)
  let D' := D.filter (fun s => s ⊆ T)
  have hC' : isFaceChain C' := hC.mono (Finset.filter_subset _ C)
  have hD' : isFaceChain D' := hD.mono (Finset.filter_subset _ D)
  have hC'T : ∀ s ∈ C', s ⊆ T := fun s hs => (Finset.mem_filter.mp hs).2
  have hD'T : ∀ s ∈ D', s ⊆ T := fun s hs => (Finset.mem_filter.mp hs).2
  have hT : AffineIndependent ℝ ((↑) : T → E) :=
    (K.indep hVK).mono (show (T : Set E) ⊆ V from Finset.inter_subset_left)
  apply Set.Subset.antisymm
  · intro x hx
    have hxV := hC.convexHull_chainCentroids_subset V hCV hx.1
    have hxW := hD.convexHull_chainCentroids_subset W hDW hx.2
    have hxT : x ∈ convexHull ℝ (T : Set E) := by
      have h := K.convexHull_inter_convexHull hVK hWK
      have hxVW : x ∈ convexHull ℝ (V : Set E) ∩ convexHull ℝ (W : Set E) := ⟨hxV, hxW⟩
      rw [h] at hxVW
      simpa only [T, Finset.coe_inter] using hxVW
    have hxspan : x ∈ affineSpan ℝ (T : Set E) := convexHull_subset_affineSpan _ hxT
    have hxC' : x ∈ convexHull ℝ (chainCentroids id C' : Set E) := by
      rw [← hC.convexHull_chainCentroids_inter_affineSpan_of_subset V (K.indep hVK) hCV T
        Finset.inter_subset_left]
      exact ⟨hx.1, hxspan⟩
    have hxD' : x ∈ convexHull ℝ (chainCentroids id D' : Set E) := by
      rw [← hD.convexHull_chainCentroids_inter_affineSpan_of_subset W (K.indep hWK) hDW T
        Finset.inter_subset_right]
      exact ⟨hx.2, hxspan⟩
    have hxshared : x ∈ convexHull ℝ (chainCentroids id (C' ∩ D') : Set E) := by
      rw [← hC'.convexHull_chainCentroids_inter_of_subset hD' T hT hC'T hD'T]
      exact ⟨hxC', hxD'⟩
    exact convexHull_mono (chainCentroids_mono id (Finset.inter_subset_inter
      (Finset.filter_subset _ C) (Finset.filter_subset _ D))) hxshared
  · intro x hx
    exact ⟨convexHull_mono (chainCentroids_mono id Finset.inter_subset_left) hx,
      convexHull_mono (chainCentroids_mono id Finset.inter_subset_right) hx⟩

noncomputable def barycentricSubdivision (K : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | ∃ C : Finset (Finset E), C.Nonempty ∧ isFaceChain C ∧
    (∀ t ∈ C, t ∈ K.faces) ∧ chainCentroids id C = s}
  isRelLowerSet_faces := by
    classical
    rintro s ⟨C, hCne, hC, hCK, rfl⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨t, ht⟩ := hCne
      exact ⟨t.centroid ℝ id, mem_chainCentroids.mpr ⟨t, ht, rfl⟩⟩
    · intro b hb hbne
      let D := C.filter (fun t => t.centroid ℝ id ∈ b)
      have hDC : D ⊆ C := Finset.filter_subset _ C
      have himage : chainCentroids id D = b := by
        ext x
        constructor
        · intro hx
          obtain ⟨t, ht, rfl⟩ := mem_chainCentroids.mp hx
          exact (Finset.mem_filter.mp ht).2
        · intro hx
          obtain ⟨t, ht, heq⟩ := mem_chainCentroids.mp (hb hx)
          exact mem_chainCentroids.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, heq ▸ hx⟩, heq⟩
      have hDne : D.Nonempty := by
        obtain ⟨x, hx⟩ := hbne
        rw [← himage] at hx
        obtain ⟨t, ht, -⟩ := mem_chainCentroids.mp hx
        exact ⟨t, ht⟩
      exact ⟨D, hDne, hC.mono hDC, fun t ht => hCK t (hDC ht), himage⟩
  indep := by
    rintro s ⟨C, hCne, hC, hCK, rfl⟩
    obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
    exact hC.affineIndependent_chainCentroids_of_subset V (K.indep (hCK V hVC)) hCV
  inter_subset_convexHull := by
    classical
    rintro s t ⟨C, hCne, hC, hCK, rfl⟩ ⟨D, hDne, hD, hDK, rfl⟩
    rw [hC.convexHull_chainCentroids_inter_of_complex K hD hCne hDne hCK hDK]
    apply convexHull_mono
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_chainCentroids.mp hx
    exact ⟨mem_chainCentroids.mpr ⟨s, (Finset.mem_inter.mp hs).1, rfl⟩,
      mem_chainCentroids.mpr ⟨s, (Finset.mem_inter.mp hs).2, rfl⟩⟩

theorem barycentricSubdivision_space (K : Geometry.SimplicialComplex ℝ E) :
    (barycentricSubdivision K).space = K.space := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨s, ⟨C, hCne, hC, hCK, rfl⟩, hxs⟩ :=
      Geometry.SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
    exact K.convexHull_subset_space (hCK V hVC)
      (hC.convexHull_chainCentroids_subset V hCV hxs)
  · intro x hx
    obtain ⟨V, hVK, hxV⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨a, ha, hasum, hax⟩ := Finset.mem_convexHull'.mp hxV
    obtain ⟨C, hCne, hC, hCV, hCx⟩ := exists_faceChain_of_weights id V a ha hasum
    apply Geometry.SimplicialComplex.mem_space_iff.mpr
    refine ⟨chainCentroids id C, ⟨C, hCne, hC, ?_, rfl⟩, ?_⟩
    · intro t ht
      exact K.down_closed hVK (hCV t ht) (hC.1 t ht)
    · simpa only [id_eq, hax] using hCx

theorem barycentricSubdivision_finite_faces (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) : (barycentricSubdivision K).faces.Finite := by
  classical
  apply ((hK.toFinset.powerset.image (chainCentroids id)).finite_toSet).subset
  rintro s ⟨C, -, -, hCK, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨C, Finset.mem_powerset.mpr ?_, rfl⟩
  intro t ht
  exact hK.mem_toFinset.mpr (hCK t ht)

end DifferentialGeometry.Topology.Engulfing
