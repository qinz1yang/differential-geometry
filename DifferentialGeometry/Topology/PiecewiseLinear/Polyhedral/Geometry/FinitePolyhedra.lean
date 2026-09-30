import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.EnclosingSimplex
import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.SubcomplexUnion
import Mathlib.Analysis.Convex.Caratheodory

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem exists_complex_finite_convexHulls {ι : Type*} [Finite ι] (V : ι → Finset E) :
    ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧
      T.space = ⋃ i, convexHull ℝ (V i : Set E) ∧
      ∀ s ∈ T.faces, ∃ i, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (V i : Set E) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let W : Finset E := Finset.univ.biUnion V
  have hVW (i : ι) : V i ⊆ W := Finset.subset_biUnion_of_mem V (Finset.mem_univ i)
  let I := {s : W.powerset // AffineIndependent ℝ ((↑) : s.1 → E) ∧ ∃ i, s.1 ⊆ V i}
  have hI (i : I) : ∃ j, i.1.1 ⊆ V j := i.2.2
  choose parent hparent using hI
  have hcompact : IsCompact (⋃ i, convexHull ℝ (V i : Set E)) :=
    isCompact_iUnion (fun i => (V i).finite_toSet.isCompact_convexHull ℝ)
  obtain ⟨b, hb⟩ := exists_bounded_subset_interior_simplex hcompact.isBounded
  let K := barycentricComplex b b.ind
  have hK := barycentricComplex_finite_faces b b.ind
  have hKspace : K.space = convexHull ℝ (range b) := barycentricComplex_space_eq b b.ind
  have hinside (j : ι) : convexHull ℝ (V j : Set E) ⊆ K.space := by
    rw [hKspace]
    exact (subset_iUnion (fun i => convexHull ℝ (V i : Set E)) j).trans (hb.trans interior_subset)
  have hdim : ∀ s ∈ K.faces, s.card ≤ Module.finrank ℝ E + 1 := by
    intro s hs
    simpa only [Fintype.card_coe] using (K.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  obtain ⟨L, hL, hspace, _, _, hrestr⟩ := exists_subdivision_containing_simplices K hK
    (fun i : I => i.1.1) (fun i => i.2.1) hdim
  let J : I → SimplicialComplex ℝ E := fun i => vertexRestriction L (convexHull ℝ (i.1.1 : Set E))
  have hJL : ∀ i, (J i).faces ⊆ L.faces := fun _ _ hs => hs.1
  have hJspace (i : I) : (J i).space = convexHull ℝ (i.1.1 : Set E) := by
    change (vertexRestriction L _).space = _
    rw [hrestr, inter_eq_right.mpr ((convexHull_mono (hparent i)).trans (hinside (parent i)))]
  let T := subcomplexUnion L J hJL
  have hTspace : T.space = ⋃ i : I, (J i).space := subcomplexUnion_space L J hJL
  refine ⟨T, subcomplexUnion_finite_faces L J hJL
    (fun i => vertexRestriction_finite_faces L _ hL), ?_, ?_⟩
  · rw [hTspace]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [hJspace i] at hi
      exact mem_iUnion.mpr ⟨parent i, convexHull_mono (hparent i) hi⟩
    · intro x hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      rw [convexHull_eq_union] at hj
      obtain ⟨s, hj⟩ := mem_iUnion.mp hj
      obtain ⟨hs, hj⟩ := mem_iUnion.mp hj
      obtain ⟨hind, hxs⟩ := mem_iUnion.mp hj
      have hsV : s ⊆ V j := hs
      let i : I := ⟨⟨s, Finset.mem_powerset.mpr (hsV.trans (hVW j))⟩, hind, j, hsV⟩
      exact mem_iUnion.mpr ⟨i, (hJspace i).symm ▸ hxs⟩
  · intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    refine ⟨parent i, ?_⟩
    exact (convexHull_min hi.2 (convex_convexHull ℝ _)).trans (convexHull_mono (hparent i))

end DifferentialGeometry.Topology.Engulfing
