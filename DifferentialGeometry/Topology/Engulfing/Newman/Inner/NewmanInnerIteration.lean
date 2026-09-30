import DifferentialGeometry.Topology.Engulfing.Newman.Inner.NewmanInnerStep

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] {n p q : ℕ}
    {K L H : SimplicialComplex ℝ E} {F : C(K.space, M)} {X : Set M}
    {raw : E → EuclideanSpace ℝ (Fin n)} {Y : Set E}

theorem NewmanInnerModel.exists_engulfing (d : NewmanInnerModel K L H F X raw Y p)
    (hlower : relativeNewmanAt M n p q) (hqp : q ≤ p)
    (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces) (hHK : H.faces ⊆ K.faces)
    (hd : ∀ s ∈ K.faces, s.card ≤ p + 2)
    (hHd : ∀ s ∈ H.faces, s.card ≤ p + 1)
    (hX : IsClosed X) (hp : p + 3 ≤ n)
    (hdata : hasAdaptedPiecewiseLinearCharts K L F X n p)
    (hfixed : InjOn F (Subtype.val ⁻¹' L.space))
    {U : Set M} (hU : IsOpen U) (hconn : NewmanConnectivity M U p)
    (hstart : X ∪ F '' (Subtype.val ⁻¹' H.space) ⊆ U)
    (hYpoly : isSubcomplexSpace K Y)
    (hYdim : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ Y → s.card ≤ q + 2)
    (hexp : FiniteSimplexExpansionIn K H.space (H.space ∪ Y))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : C(K.space, M)) (G : M ≃ₜ M), d.good g ∧
      EqOn g F (Subtype.val ⁻¹' L.space) ∧
      (∀ x, dist (g x) (F x) < ε) ∧
      X ∪ g '' (Subtype.val ⁻¹' (H.space ∪ (Y ∩ (skeleton K q).space))) ⊆ G '' U ∧
      IsCompact (closure {x | G x ≠ x}) := by
  classical
  obtain ⟨J, hJK, hJspace⟩ := hYpoly
  have hdich (s : Finset E) (hs : s ∈ K.faces)
      (hsHY : convexHull ℝ (s : Set E) ⊆ H.space ∪ Y) :
      convexHull ℝ (s : Set E) ⊆ H.space ∨ convexHull ℝ (s : Set E) ⊆ Y := by
    rw [← hJspace] at hsHY ⊢
    exact (simplicialRefines.refl K).convexHull_subset_or_of_subset_union hHK hJK hs hsHY
  have hstep : mapSkeletalSimplexStep K L X U d.good H.space (H.space ∪ Y) p q := by
    intro C σ B _hCcompact hCpoly hHC _hCK hCp hσ hσd ha hregion g G hg hcover η hη
    rcases hdich σ hσ (subset_union_right.trans hregion) with hσH | hσY
    · refine ⟨g, Homeomorph.refl M, hg, fun _ _ => rfl, ?_, ?_, ?_⟩
      · intro x
        simpa only [dist_self] using hη
      · intro y hy
        apply (show G '' U ⊆ (Homeomorph.refl M) '' (G '' U) from fun z hz => ⟨z, hz, rfl⟩)
        apply hcover
        rcases hy with hy | ⟨x, hx, rfl⟩
        · exact Or.inl hy
        · exact Or.inr ⟨x, hx.elim id (fun hx => hHC (hσH hx.1)), rfl⟩
      · simp
    · obtain ⟨Q, hQK, hQspace, hQd⟩ := hCpoly.exists_of_subset_skeleton hCp
      have hHQ : H.space ⊆ Q.space := by rwa [hQspace]
      have hQHY : Q.space ⊆ H.space ∪ Y := by
        rw [hQspace]
        exact subset_union_left.trans hregion
      have haQ : SimplexAttachment Q.space σ B := by rwa [hQspace]
      have hcoverQ : X ∪ g '' (Subtype.val ⁻¹' Q.space) ⊆ G '' U := by rwa [hQspace]
      obtain ⟨g', G', hg', hfix, hnear, hnew, hcompact⟩ :=
        d.exists_cell_step hlower hqp hK hLK hd hX hp hdata hfixed Q hQK hQd hHQ hQHY
          σ B hσ hσd haQ hσY g hg (G.isOpenMap _ hU) (hconn.image G) hcoverQ hη
      refine ⟨g', G', hg', fun x hx => hfix hx, hnear, ?_, hcompact⟩
      rw [hQspace] at hnew
      exact (union_subset_union_right X (image_mono
        (preimage_mono (union_subset_union_right C inter_subset_left)))).trans hnew
  have hHpoly : isSubcomplexSpace K H.space := .of_faces_subset hHK
  have hHYK : H.space ∪ Y ⊆ K.space :=
    union_subset (subcomplex_space_subset K H hHK)
      (d.block_local.trans (subcomplex_space_subset K d.localComplex d.local_subcomplex))
  have hHsk : H.space ⊆ (skeleton K p).space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact (skeleton K p).convexHull_subset_space ⟨hHK hs, hHd s hs⟩ hxs
  have hbound : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ H.space ∪ Y →
      convexHull ℝ (s : Set E) ⊆ H.space ∨ s.card ≤ q + 2 := by
    intro s hs hsub
    exact (hdich s hs hsub).imp_right (hYdim s hs)
  obtain ⟨g, G, hg, hfix, hnear, hcover, hcompact⟩ :=
    exists_map_engulfing_of_skeletal_expansion K L hK F X U d.good d.good_initial hqp
      hstep hexp (hHpoly.isCompact hK) hHpoly hHYK subset_rfl hHsk hbound hstart hε
  refine ⟨g, G, hg, fun x hx => hfix x hx, hnear, ?_, hcompact⟩
  have heq : skeletalCovered K H.space (H.space ∪ Y) q =
      H.space ∪ (Y ∩ (skeleton K q).space) := by
    ext x
    simp only [skeletalCovered, mem_union, mem_inter_iff]
    tauto
  rwa [heq] at hcover

end DifferentialGeometry.Topology.Engulfing
