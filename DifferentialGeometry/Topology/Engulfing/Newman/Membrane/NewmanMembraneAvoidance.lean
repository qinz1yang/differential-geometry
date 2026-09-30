import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanMembraneIteration

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [DecidableEq E] [DecidableEq (ConeSpace E)]
  {n p q : ℕ} {P : NewmanProblem E M n p (q + 1)} {s : Finset E}

namespace NewmanPreparedMembrane

theorem old_point_mem_attaching_of_mem_simplex (D : NewmanPreparedMembrane P s)
    (y : P.source.space) (hy : (D.oldSourceMap y).1 ∈ D.simplex) :
    y.1 ∈ convexHull ℝ (s : Set E) := by
  have hbase : convexHull ℝ (range D.vertices) ⊆ P.source.space := by
    simpa only [Finset.coe_image, Finset.coe_univ, image_univ] using
      P.source.convexHull_subset_space D.source_face
  have hyI : coneInclusion y.1 ∈ (coneInclusion '' P.source.space) ∩ D.simplex :=
    ⟨⟨y.1, y.2, rfl⟩, hy⟩
  rw [cone_inter_inclusion D.vertices D.independent P.source.space hbase,
    simplexFacet_coneVertices_last] at hyI
  obtain ⟨z, hz, hzy⟩ := hyI
  have heq : z = y.1 := coneInclusion_injective hzy
  have hv : range D.vertices = (s : Set E) := by
    simpa only [Finset.coe_image, Finset.coe_univ, image_univ] using
      congrArg (fun t : Finset E => (t : Set E)) D.vertices_eq
  simpa only [heq, hv] using hz

theorem simplex_fixed_avoids_obstacle (D : NewmanPreparedMembrane P s)
    (havoid : Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle)
    (x : D.source.space) (hx : x.1 ∈ D.simplex)
    (hfixed : x.1 ∈ (coneBaseComplex P.fixed).space) : D.map x ∉ P.obstacle := by
  obtain ⟨y, hy, hxy⟩ := exists_old_point_of_cone_subcomplex P.source P.fixed
    P.fixed_subcomplex D.vertices D.independent D.source_face x hfixed
  have hys := D.old_point_mem_attaching_of_mem_simplex y (hxy.symm ▸ hx)
  rw [← hxy, D.old_exact]
  exact fun hX => disjoint_left.mp havoid ⟨y, hys, rfl⟩ hX

theorem fixed_obstacle_mem_covered (D : NewmanPreparedMembrane P s)
    (havoid : Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle)
    (x : D.source.space) (hx : x.1 ∈ D.membrane)
    (hfixed : x.1 ∈ (coneBaseComplex P.fixed).space) (hX : D.map x ∈ P.obstacle) :
    x.1 ∈ D.covered := by
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact (D.simplex_fixed_avoids_obstacle havoid x hx hfixed hX).elim

namespace AssignedRefinement

variable {D : NewmanPreparedMembrane P s}

theorem simplex_fixed_avoids_obstacle (R : D.AssignedRefinement)
    (havoid : Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle)
    (g : C(R.source.space, M))
    (hfix : ∀ x : R.source.space, x.1 ∈ R.fixed.space → g x = R.map x)
    (x : R.source.space) (hx : x.1 ∈ D.simplex) (hfixed : x.1 ∈ R.fixed.space) :
    g x ∉ P.obstacle := by
  rw [hfix x hfixed, R.map_eq]
  exact D.simplex_fixed_avoids_obstacle havoid ⟨x.1, R.space ▸ x.2⟩ hx
    (R.fixed_space ▸ hfixed)

theorem fixed_obstacle_mem_covered (R : D.AssignedRefinement)
    (havoid : Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle)
    (g : C(R.source.space, M))
    (hfix : ∀ x : R.source.space, x.1 ∈ R.fixed.space → g x = R.map x)
    (x : R.source.space) (hx : x.1 ∈ D.membrane) (hfixed : x.1 ∈ R.fixed.space)
    (hX : g x ∈ P.obstacle) : x.1 ∈ D.covered := by
  apply D.fixed_obstacle_mem_covered havoid ⟨x.1, R.space ▸ x.2⟩ hx
    (R.fixed_space ▸ hfixed)
  rwa [hfix x hfixed, R.map_eq] at hX

theorem fixed_face_obstacle_mem_roof (R : D.AssignedRefinement)
    (havoid : Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle)
    (g : C(R.source.space, M))
    (hfix : ∀ x : R.source.space, x.1 ∈ R.fixed.space → g x = R.map x)
    {C : Set (ConeSpace E)} {V B : Finset (ConeSpace E)}
    (hC : D.covered ⊆ C) (hV : convexHull ℝ (V : Set (ConeSpace E)) ⊆ D.membrane)
    (ha : SimplexAttachment C V B)
    (x : R.source.space) (hx : x.1 ∈ convexHull ℝ (V : Set (ConeSpace E)))
    (hfixed : x.1 ∈ R.fixed.space) (hX : g x ∈ P.obstacle) :
    x.1 ∈ simplexRoof V B :=
  ha.inter_subset_roof ⟨hC (R.fixed_obstacle_mem_covered havoid g hfix x (hV hx) hfixed hX), hx⟩

theorem active_face_fixed_avoids_obstacle (R : D.AssignedRefinement)
    (havoid : Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.obstacle)
    (g : C(R.source.space, M))
    (hfix : ∀ x : R.source.space, x.1 ∈ R.fixed.space → g x = R.map x)
    {V : Finset (ConeSpace E)} (hV : V ∈ R.source.faces)
    (hmem : convexHull ℝ (V : Set (ConeSpace E)) ⊆ D.membrane)
    (hactive : ¬ convexHull ℝ (V : Set (ConeSpace E)) ⊆ D.covered)
    (x : R.source.space) (hx : x.1 ∈ convexHull ℝ (V : Set (ConeSpace E)))
    (hfixed : x.1 ∈ R.fixed.space) : g x ∉ P.obstacle := by
  have hcone := ((D.refined_face_support R.refines hV hmem).resolve_left hactive).1
  exact R.simplex_fixed_avoids_obstacle havoid g hfix x (hcone hx) hfixed

end AssignedRefinement

end NewmanPreparedMembrane

end

end DifferentialGeometry.Topology.Engulfing
