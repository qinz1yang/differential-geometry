import DifferentialGeometry.Topology.SimplicialComplex.Stellar.StellarInvariantSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.SimplexInequalities
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_common_refinement_preserving_expansions
    (K P : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hP : P.faces.Finite)
    (hKP : K.space ⊆ P.space) {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ R : SimplicialComplex ℝ E, R.faces.Finite ∧ R.space = K.space ∧
      simplicialRefines R K ∧ simplicialRefines R P ∧
      (∀ s ∈ R.faces, s.card ≤ d + 1) ∧
      ∀ A C, FiniteSimplexExpansionIn K A C → FiniteSimplexExpansionIn R A C := by
  classical
  let : Fintype P.faces := hP.fintype
  choose F hF using fun s : P.faces =>
    exists_affine_inequalities_of_affineIndependent s.val (P.indep s.property)
  let I := Finset.univ.biUnion F
  obtain ⟨R, hR, hspace, href, hcuts, hdim, hexp⟩ :=
    exists_subdivision_respects_affineHyperplanes_preserving_expansions K hK I id hd
  have hrestr (t : P.faces) :
      (vertexRestriction R (convexHull ℝ (t.val : Set E))).space =
        R.space ∩ convexHull ℝ (t.val : Set E) := by
    rw [hF t]
    exact vertexRestriction_finite_halfspaces R (F t) id (fun f hf =>
      hcuts f (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hf⟩))
  refine ⟨R, hR, hspace, href, ?_, hdim, hexp⟩
  intro s hs
  have hcentR : s.centroid ℝ id ∈ R.space :=
    R.convexHull_subset_space hs (s.centroid_mem_convexHull (R.nonempty_of_mem_faces hs))
  obtain ⟨t, ht, hcentt⟩ := SimplicialComplex.mem_space_iff.mp (hKP (hspace.subset hcentR))
  have hcentJ : s.centroid ℝ id ∈ (vertexRestriction R (convexHull ℝ (t : Set E))).space := by
    rw [hrestr ⟨t, ht⟩]
    exact ⟨hcentR, hcentt⟩
  obtain ⟨u, hu, hcentu⟩ := SimplicialComplex.mem_space_iff.mp hcentJ
  have hsu := face_subset_of_centroid_mem R hs hu.1 hcentu
  refine ⟨t, ht, convexHull_min ?_ (convex_convexHull ℝ _)⟩
  exact fun x hx => hu.2 (hsu hx)

end DifferentialGeometry.Topology.Engulfing
