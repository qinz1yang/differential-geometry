import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.Star

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def regularNeighborhoodFaces (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    Set (Finset E) :=
  {t ∈ K.faces | ∃ u ∈ K.faces, t ⊆ u ∧ (convexHull ℝ (u : Set E) ∩ A).Nonempty}

def regularNeighborhoodIn (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := regularNeighborhoodFaces K A
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1
  isRelLowerSet_faces := by
    rintro t ⟨ht, u, hu, htu, hA⟩
    exact ⟨K.nonempty_of_mem_faces ht, fun t' ht't ht' =>
      ⟨K.down_closed ht ht't ht', u, hu, ht't.trans htu, hA⟩⟩

theorem mem_regularNeighborhoodIn_faces_iff (K : Geometry.SimplicialComplex ℝ E) (A : Set E)
    {t : Finset E} : t ∈ (regularNeighborhoodIn K A).faces ↔
      t ∈ K.faces ∧ ∃ u ∈ K.faces, t ⊆ u ∧ (convexHull ℝ (u : Set E) ∩ A).Nonempty :=
  Iff.rfl

theorem regularNeighborhoodIn_le (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    regularNeighborhoodIn K A ≤ K :=
  fun _ ht => ht.1

instance (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (A : Set E) :
    Finite (regularNeighborhoodIn K A).faces :=
  ((Set.toFinite K.faces).subset fun _ ht => ht.1).to_subtype

theorem space_regularNeighborhoodIn_subset (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    (regularNeighborhoodIn K A).space ⊆ K.space := by
  intro x hx
  obtain ⟨t, ht, hxt⟩ := (regularNeighborhoodIn K A).mem_space_iff.mp hx
  exact K.convexHull_subset_space ht.1 hxt

theorem closedStar_subset_regularNeighborhoodIn (K : Geometry.SimplicialComplex ℝ E) (A : Set E)
    {x : E} (hx : x ∈ A) : closedStar K x ⊆ (regularNeighborhoodIn K A).space := by
  intro y hy
  unfold closedStar at hy
  rw [mem_iUnion₂] at hy
  obtain ⟨s, ⟨hs, hxs⟩, hys⟩ := hy
  exact (regularNeighborhoodIn K A).convexHull_subset_space
    ⟨hs, s, hs, Finset.Subset.refl s, ⟨x, hxs, hx⟩⟩ hys

theorem regularNeighborhoodIn_mem_nhdsWithin (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (A : Set E) {x : E} (hx : x ∈ A) :
    (regularNeighborhoodIn K A).space ∈ 𝓝[K.space] x :=
  Filter.mem_of_superset (closedStar_mem_nhdsWithin K x)
    (closedStar_subset_regularNeighborhoodIn K A hx)

variable [DecidableEq E]

noncomputable def secondDerived (K : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ E :=
  barycentricSubdivision (barycentricSubdivision K)

theorem secondDerived_isSubdivision (K : Geometry.SimplicialComplex ℝ E) :
    IsSubdivision (secondDerived K) K :=
  (barycentricSubdivision_isSubdivision _).trans (barycentricSubdivision_isSubdivision K)

instance (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Finite (secondDerived K).faces :=
  inferInstanceAs (Finite (barycentricSubdivision (barycentricSubdivision K)).faces)

noncomputable def regularNeighborhood (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    Geometry.SimplicialComplex ℝ E :=
  regularNeighborhoodIn (secondDerived K) A

theorem regularNeighborhood_le (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    regularNeighborhood K A ≤ secondDerived K :=
  regularNeighborhoodIn_le _ _

instance (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (A : Set E) :
    Finite (regularNeighborhood K A).faces :=
  inferInstanceAs (Finite (regularNeighborhoodIn (secondDerived K) A).faces)

theorem space_regularNeighborhood_subset (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    (regularNeighborhood K A).space ⊆ K.space :=
  (space_regularNeighborhoodIn_subset _ _).trans (secondDerived_isSubdivision K).space_eq.subset

theorem regularNeighborhood_mem_nhdsWithin (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (A : Set E) {x : E} (hx : x ∈ A) : (regularNeighborhood K A).space ∈ 𝓝[K.space] x := by
  rw [← (secondDerived_isSubdivision K).space_eq]
  exact regularNeighborhoodIn_mem_nhdsWithin (secondDerived K) A hx

end DifferentialGeometry.Topology.PiecewiseLinear
