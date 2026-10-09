import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.SubcomplexUnion
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.OptimalMap
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricCoverage

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem exists_exceptional_intersection_complex {ι : Type*} [Finite ι]
    (S : Finset E) (hS : AffineIndependent ℝ ((↑) : S → E))
    (V : ι → Finset E) (hV : ∀ i, AffineIndependent ℝ ((↑) : V i → E))
    (A : ι → Set E) {d : ℕ}
    (hinter : ∀ i, convexHull ℝ (S : Set E) ∩ convexHull ℝ (V i : Set E) = A i ∨
      ∃ P : AffineSubspace ℝ E,
        convexHull ℝ (S : Set E) ∩ convexHull ℝ (V i : Set E) ⊆ P ∧
          Module.finrank ℝ P.direction ≤ d) :
    ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧
      (∀ s ∈ T.faces, s.card ≤ d + 1) ∧ T.space ⊆ convexHull ℝ (S : Set E) ∧
      (∀ i, convexHull ℝ (S : Set E) ∩ convexHull ℝ (V i : Set E) ⊆ A i ∪ T.space) ∧
      T.space ⊆ ⋃ i, convexHull ℝ (S : Set E) ∩ convexHull ℝ (V i : Set E) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let K := barycentricSimplex S hS
  have hK : K.faces.Finite := barycentricSimplex_finite_faces S hS
  have hspaceK : K.space = convexHull ℝ (S : Set E) := barycentricSimplex_space_eq S hS
  have hd : ∀ s ∈ K.faces, s.card ≤ Module.finrank ℝ E + 1 := by
    intro s hs
    simpa only [Fintype.card_coe] using (K.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  obtain ⟨L, hL, hspaceL, _, _, hrestr⟩ := exists_subdivision_containing_simplices K hK V hV hd
  let B := {i : ι // convexHull ℝ (S : Set E) ∩ convexHull ℝ (V i : Set E) ≠ A i}
  have hbad (i : B) : ∃ P : AffineSubspace ℝ E,
      convexHull ℝ (S : Set E) ∩ convexHull ℝ (V i : Set E) ⊆ P ∧
        Module.finrank ℝ P.direction ≤ d := (hinter i).resolve_left i.2
  choose P hP hdim using hbad
  let J : B → SimplicialComplex ℝ E := fun i => vertexRestriction L (convexHull ℝ (V i : Set E))
  have hJL : ∀ i, (J i).faces ⊆ L.faces := fun _ _ hs => hs.1
  have hJspace (i : B) : (J i).space =
      convexHull ℝ (S : Set E) ∩ convexHull ℝ (V i : Set E) := by
    change (vertexRestriction L _).space = _
    rw [hrestr, hspaceK]
  have hJdim : ∀ i, ∀ s ∈ (J i).faces, s.card ≤ d + 1 := by
    intro i s hs
    apply (affineIndependent_card_le_of_subset_affineSubspace ((J i).indep hs) (P i) ?_).trans
      (Nat.add_le_add_right (hdim i) 1)
    intro v hv
    apply hP i
    rw [← hJspace i]
    exact (J i).subset_space hs hv
  let T := subcomplexUnion L J hJL
  have hTspace : T.space = ⋃ i : B, (J i).space := subcomplexUnion_space L J hJL
  refine ⟨T, subcomplexUnion_finite_faces L J hJL (fun i => vertexRestriction_finite_faces L _ hL),
    subcomplexUnion_face_card_le L J hJL hJdim, ?_, ?_, ?_⟩
  · rw [hTspace]
    exact iUnion_subset (fun i => by rw [hJspace i]; exact inter_subset_left)
  · intro i x hx
    by_cases heq : convexHull ℝ (S : Set E) ∩ convexHull ℝ (V i : Set E) = A i
    · exact Or.inl (heq ▸ hx)
    · right
      rw [hTspace]
      apply mem_iUnion.mpr
      refine ⟨⟨i, heq⟩, ?_⟩
      rwa [hJspace]
  · rw [hTspace]
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i.1, (hJspace i) ▸ hi⟩

omit [DecidableEq E] in
theorem affineIndependent_finset_image {F : Type*} [DecidableEq F] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Finset E} {w : E → F} (hw : AffineIndependent ℝ (fun v : s => w v)) :
    AffineIndependent ℝ ((↑) : s.image w → F) := by
  classical
  have heq : range (fun v : s => w v) = (s.image w : Set F) := by
    ext y
    simp only [mem_range, Finset.mem_coe, Finset.mem_image]
    exact ⟨fun ⟨v, hv⟩ => ⟨v.1, v.2, hv⟩, fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, h⟩⟩
  have h := hw.range
  rw [heq] at h
  exact h

omit [DecidableEq E] in
theorem exists_exceptional_complex_of_generalPosition {n p q : ℕ} {ι : Type*} [Finite ι]
    (hp : p + 3 ≤ n) (hqp : q ≤ p) (hq : 2 ≤ q)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → EuclideanSpace ℝ (Fin n))
    (hgp : ∀ r : Finset E, (r : Set E) ⊆ K.vertices → r.card ≤ n + 1 →
      AffineIndependent ℝ (fun v : r => w v))
    (s : K.faces) (hs : s.1.card ≤ q + 2)
    (t : ι → K.faces) (ht : ∀ i, (t i).1.card ≤ p + 1) :
    ∃ T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)), T.faces.Finite ∧
      (∀ u ∈ T.faces, u.card ≤ q - 1) ∧ T.space ⊆ convexHull ℝ (w '' (s.1 : Set E)) ∧
      (∀ i, convexHull ℝ (w '' (s.1 : Set E)) ∩ convexHull ℝ (w '' ((t i).1 : Set E)) ⊆
        convexHull ℝ (w '' ((s.1 : Set E) ∩ ((t i).1 : Set E))) ∪ T.space) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hs' : s.1.card ≤ n + 1 := by omega
  have ht' (i : ι) : (t i).1.card ≤ n + 1 := by have := ht i; omega
  have hSind := affineIndependent_finset_image (hgp s.1 (face_vertices_subset K s) hs')
  have hTind (i : ι) := affineIndependent_finset_image
    (hgp (t i).1 (face_vertices_subset K (t i)) (ht' i))
  have hinter (i : ι) :
      convexHull ℝ (s.1.image w : Set (EuclideanSpace ℝ (Fin n))) ∩
        convexHull ℝ ((t i).1.image w : Set (EuclideanSpace ℝ (Fin n))) =
          convexHull ℝ (w '' ((s.1 : Set E) ∩ ((t i).1 : Set E))) ∨
      ∃ P : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)),
        convexHull ℝ (s.1.image w : Set (EuclideanSpace ℝ (Fin n))) ∩
          convexHull ℝ ((t i).1.image w : Set (EuclideanSpace ℝ (Fin n))) ⊆ P ∧
          Module.finrank ℝ P.direction ≤ q - 2 := by
    have h := interpolateVertices_optimal_intersection K hK w hgp s (t i) hs' (ht' i)
    dsimp only at h
    rw [interpolateVertices_image_face, interpolateVertices_image_face] at h
    simp only [Finset.coe_image]
    rcases h with heq | ⟨P, hP, hdim⟩
    · exact Or.inl heq
    · refine Or.inr ⟨P, hP, ?_⟩
      have hti := ht i
      omega
  obtain ⟨T, hT, hdim, hspace, hcover, _⟩ := exists_exceptional_intersection_complex
    (s.1.image w) hSind (fun i => (t i).1.image w) hTind
    (fun i => convexHull ℝ (w '' ((s.1 : Set E) ∩ ((t i).1 : Set E)))) hinter
  refine ⟨T, hT, fun u hu => ?_, ?_, ?_⟩
  · have hd := hdim u hu
    omega
  · simpa only [Finset.coe_image] using hspace
  · simpa only [Finset.coe_image] using hcover

omit [DecidableEq E] in
theorem generalPosition_intersection_eq_of_low_dimension {n p q : ℕ}
    (hp : p + 3 ≤ n) (hqp : q ≤ p) (hq : q ≤ 1)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → EuclideanSpace ℝ (Fin n))
    (hgp : ∀ r : Finset E, (r : Set E) ⊆ K.vertices → r.card ≤ n + 1 →
      AffineIndependent ℝ (fun v : r => w v))
    (s t : K.faces) (hs : s.1.card ≤ q + 2) (ht : t.1.card ≤ p + 1) :
    convexHull ℝ (w '' (s.1 : Set E)) ∩ convexHull ℝ (w '' (t.1 : Set E)) =
      convexHull ℝ (w '' ((s.1 : Set E) ∩ (t.1 : Set E))) := by
  classical
  have h := interpolateVertices_optimal_intersection K hK w hgp s t (by omega) (by omega)
  dsimp only at h
  rw [interpolateVertices_image_face, interpolateVertices_image_face] at h
  rcases h with heq | ⟨P, _, hdim⟩
  · exact heq
  · omega

end DifferentialGeometry.Topology.Engulfing
