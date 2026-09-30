import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RelativeTriangulationExistence
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.PolyhedralIntersection

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def boundarySimplexFilling : Prop :=
  ∀ (B : SimplicialComplex ℝ E) (V : Finset E), B.faces.Finite → V.Nonempty →
    AffineIndependent ℝ ((↑) : V → E) →
    (∀ s ∈ B.faces, ∃ i ∈ V,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (V.erase i : Set E)) →
    B.space = finiteSimplexBoundary V →
    ∃ C : SimplicialComplex ℝ E, C.faces.Finite ∧
      C.space = convexHull ℝ (V : Set E) ∧
      (∀ s ∈ C.faces, s.card ≤ V.card) ∧
      ∀ s ∈ C.faces, ∃ t : Finset E, t ⊆ s ∧
        (t ∈ B.faces ∨ t = ∅) ∧
        convexHull ℝ (s : Set E) ∩ finiteSimplexBoundary V = convexHull ℝ (t : Set E)

omit [FiniteDimensional ℝ E] in
theorem exists_relative_refinement_of_boundary_filling
    (hfill : boundarySimplexFilling (E := E))
    (K D J : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hDK : D.faces ⊆ K.faces) (hJ : J.faces.Finite)
    (hJD : simplicialRefines J D) (hJs : J.space = D.space)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧ T.space = K.space ∧
      simplicialRefines T K ∧ J.faces ⊆ T.faces ∧
      ∀ s ∈ T.faces, s.card ≤ d + 1 := by
  let P : SimplicialComplex ℝ E → Prop := fun Q =>
    ∃ T : SimplicialComplex ℝ E, T.faces.Finite ∧ T.space = Q.space ∧
      simplicialRefines T Q ∧ J.faces ⊆ T.faces ∧
      ∀ s ∈ T.faces, s.card ≤ d + 1
  apply finite_complex_relative_induction K D hK hDK P
  · refine ⟨J, hJ, hJs, hJD, subset_rfl, ?_⟩
    intro s hs
    obtain ⟨t, ht, hst⟩ := hJD s hs
    exact ((J.indep hs).card_le_card_of_subset_affineSpan
      (fun x hx => convexHull_subset_affineSpan _ (hst (subset_convexHull ℝ _ hx)))).trans
      (hd t (hDK ht))
  · intro Q hQK hDQ V hV hVD hprevious
    obtain ⟨R, hR, hRs, hRQ₀, hJR, hRd⟩ := hprevious
    have hRQ : simplicialRefines R Q := by
      intro s hs
      obtain ⟨t, ht, hst⟩ := hRQ₀ s hs
      exact ⟨t, ht.1, hst⟩
    let B := vertexRestriction R (convexHull ℝ (V : Set E))
    have hB : B.faces.Finite := vertexRestriction_finite_faces R _ hR
    have hBR : B.faces ⊆ R.faces := fun _ hs => hs.1
    have hBs : B.space = finiteSimplexBoundary V := by
      rw [show B.space = R.space ∩ convexHull ℝ (V : Set E) from
        hRQ.vertexRestriction_space hV.1, hRs,
        erasePrincipalSimplex_inter_simplex Q V hV]
    have hparents : ∀ s ∈ B.faces, ∃ i ∈ V,
        convexHull ℝ (s : Set E) ⊆ convexHull ℝ (V.erase i : Set E) := by
      intro s hs
      obtain ⟨t, ht, hst⟩ := hRQ₀ s hs.1
      have hnot : ¬ V ⊆ t := fun h => ht.2 (hV.2 t ht.1 h)
      obtain ⟨i, hiV, hit⟩ := Finset.not_subset.mp hnot
      refine ⟨i, hiV, ?_⟩
      have hsV : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (V : Set E) :=
        convexHull_min hs.2 (convex_convexHull ℝ _)
      intro x hx
      apply convexHull_mono (show (V : Set E) ∩ (t : Set E) ⊆
        (V.erase i : Set E) from ?_)
        (Q.inter_subset_convexHull hV.1 ht.1 ⟨hsV hx, hst hx⟩)
      intro y hy
      exact Finset.mem_erase.mpr ⟨fun hyi => hit (hyi ▸ hy.2), hy.1⟩
    obtain ⟨C, hC, hCs, hCd, hCboundary⟩ :=
      hfill B V hB (Q.nonempty_of_mem_faces hV.1) (Q.indep hV.1) hparents hBs
    have hcompat : geometricComplexesCompatible R C := by
      apply geometricComplexesCompatible_of_boundary_faces R C B hCs.subset ?_ hBR hCboundary
      rw [hRs, erasePrincipalSimplex_inter_simplex Q V hV]
    let T := geometricComplexUnion R C hcompat
    refine ⟨T, geometricComplexUnion_finite R C hcompat hR hC, ?_, ?_,
      hJR.trans (geometricComplexUnion_left R C hcompat), ?_⟩
    · rw [geometricComplexUnion_space, hRs, hCs,
        erasePrincipalSimplex_space_union Q V hV]
    · apply geometricComplexUnion_refines R C Q hcompat hRQ
      intro s hs
      exact ⟨V, hV.1, fun x hx => hCs ▸ C.convexHull_subset_space hs hx⟩
    · exact geometricComplexUnion_card_le R C hcompat hRd
        (fun s hs => (hCd s hs).trans (hd V (hQK hV.1)))

end

end DifferentialGeometry.Topology.Engulfing
