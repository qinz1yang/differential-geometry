import DifferentialGeometry.Topology.Homotopy.ConvexProduct
import DifferentialGeometry.Topology.PiecewiseLinear.EulerCellOperations

noncomputable section

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eulerChar_eq_zero_of_isPLHomeomorphOn_prod_Icc
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (J : Geometry.SimplicialComplex ℝ E) [Finite J.faces]
    (A : Geometry.SimplicialComplex ℝ F) [Finite A.faces]
    (hJ : IsPLSphere 1 J.space) {a b : ℝ} (hab : a ≤ b) {f : E × ℝ → F}
    (hf : IsPLHomeomorphOn f (J.space ×ˢ Icc a b) A.space) :
    eulerChar A = 0 := by
  let c : Icc a b := ⟨a, le_rfl, hab⟩
  let e : ContinuousMap.HomotopyEquiv (J.space ×ˢ Icc a b) J.space :=
    (Homeomorph.Set.prod J.space (Icc a b)).toHomotopyEquiv.trans
      (DifferentialGeometry.HomotopyEquiv.productConvex J.space (convex_Icc a b) c)
  calc
    eulerChar A = Homology.eulerChar ℚ (TopCat.of A.space) := eulerChar_eq_singular A ℚ
    _ = Homology.eulerChar ℚ (TopCat.of (J.space ×ˢ Icc a b)) :=
      (Homology.eulerChar_eq_of_homeomorph ℚ hf.homeomorph).symm
    _ = Homology.eulerChar ℚ (TopCat.of J.space) :=
      Homology.eulerChar_eq_of_homotopyEquiv ℚ e
    _ = eulerChar J := (eulerChar_eq_singular J ℚ).symm
    _ = 0 := eulerChar_of_isPLSphere_one J hJ

structure SurfaceSplitAlongPolygon
    (source split : Geometry.SimplicialComplex ℝ E) where
  core : Geometry.SimplicialComplex ℝ E
  collar : Geometry.SimplicialComplex ℝ E
  boundary₀ : Geometry.SimplicialComplex ℝ E
  boundary₁ : Geometry.SimplicialComplex ℝ E
  core_faces_finite : core.faces.Finite
  collar_faces_finite : collar.faces.Finite
  boundary₀_faces_finite : boundary₀.faces.Finite
  boundary₁_faces_finite : boundary₁.faces.Finite
  source_faces : source.faces = core.faces ∪ collar.faces
  core_inter_collar_faces :
    (intersectionComplex core collar).faces = boundary₀.faces ∪ boundary₁.faces
  boundary_faces_disjoint : Disjoint boundary₀.faces boundary₁.faces
  boundary₀_isPLSphere : IsPLSphere 1 boundary₀.space
  boundary₁_isPLSphere : IsPLSphere 1 boundary₁.space
  collarHomeomorph :
    ∃ f : E × ℝ → E,
      IsPLHomeomorphOn f (boundary₀.space ×ˢ Icc (0 : ℝ) 1) collar.space
  splitHomeomorph : ∃ f : E → E, IsPLHomeomorphOn f core.space split.space

namespace SurfaceSplitAlongPolygon

open Classical in
theorem eulerChar_eq [FiniteDimensional ℝ E]
    {source split : Geometry.SimplicialComplex ℝ E}
    [Finite source.faces] [Finite split.faces]
    (h : SurfaceSplitAlongPolygon source split) :
    eulerChar split = eulerChar source := by
  let _ : Finite h.core.faces := h.core_faces_finite.to_subtype
  let _ : Finite h.collar.faces := h.collar_faces_finite.to_subtype
  let _ : Finite h.boundary₀.faces := h.boundary₀_faces_finite.to_subtype
  let _ : Finite h.boundary₁.faces := h.boundary₁_faces_finite.to_subtype
  have hboundary : eulerChar (intersectionComplex h.core h.collar) = 0 := by
    rw [eulerChar_eq_add_of_faces_disjoint_union
      (intersectionComplex h.core h.collar) h.boundary₀ h.boundary₁
      h.core_inter_collar_faces h.boundary_faces_disjoint,
      eulerChar_of_isPLSphere_one h.boundary₀ h.boundary₀_isPLSphere,
      eulerChar_of_isPLSphere_one h.boundary₁ h.boundary₁_isPLSphere, add_zero]
  obtain ⟨f, hf⟩ := h.collarHomeomorph
  have hcollar : eulerChar h.collar = 0 :=
    eulerChar_eq_zero_of_isPLHomeomorphOn_prod_Icc h.boundary₀ h.collar
      h.boundary₀_isPLSphere zero_le_one hf
  obtain ⟨g, hg⟩ := h.splitHomeomorph
  have hsplit : eulerChar h.core = eulerChar split :=
    eulerChar_eq_of_isPLHomeomorphOn h.core split hg
  have hsource := eulerChar_eq_add_sub_of_faces_union source h.core h.collar h.source_faces
  rw [hcollar, hboundary, add_zero, sub_zero, hsplit] at hsource
  exact hsource.symm

end SurfaceSplitAlongPolygon

structure SurfaceSplitAndCap
    (source split result : Geometry.SimplicialComplex ℝ E)
    extends SurfaceSplitAlongPolygon source split where
  cap₀ : Geometry.SimplicialComplex ℝ E
  cap₁ : Geometry.SimplicialComplex ℝ E
  capBoundary₀ : Geometry.SimplicialComplex ℝ E
  capBoundary₁ : Geometry.SimplicialComplex ℝ E
  cap₀_faces_finite : cap₀.faces.Finite
  cap₁_faces_finite : cap₁.faces.Finite
  capBoundary₀_faces_finite : capBoundary₀.faces.Finite
  capBoundary₁_faces_finite : capBoundary₁.faces.Finite
  result_faces : result.faces = (split.faces ∪ cap₀.faces) ∪ cap₁.faces
  split_inter_cap₀_faces :
    (intersectionComplex split cap₀).faces = capBoundary₀.faces
  split_inter_cap₁_faces :
    (intersectionComplex split cap₁).faces = capBoundary₁.faces
  cap_faces_disjoint : Disjoint cap₀.faces cap₁.faces
  cap₀_isPLBall : IsPLBall 2 cap₀.space
  cap₁_isPLBall : IsPLBall 2 cap₁.space
  capBoundary₀_isPLSphere : IsPLSphere 1 capBoundary₀.space
  capBoundary₁_isPLSphere : IsPLSphere 1 capBoundary₁.space

namespace SurfaceSplitAndCap

open Classical in
theorem eulerChar_eq_add_two [FiniteDimensional ℝ E]
    {source split result : Geometry.SimplicialComplex ℝ E}
    [Finite source.faces] [Finite split.faces] [Finite result.faces]
    (h : SurfaceSplitAndCap source split result) :
    eulerChar result = eulerChar source + 2 := by
  let _ : Finite h.cap₀.faces := h.cap₀_faces_finite.to_subtype
  let _ : Finite h.cap₁.faces := h.cap₁_faces_finite.to_subtype
  let _ : Finite h.capBoundary₀.faces := h.capBoundary₀_faces_finite.to_subtype
  let _ : Finite h.capBoundary₁.faces := h.capBoundary₁_faces_finite.to_subtype
  have hsplitResult : eulerChar split = eulerChar source := h.toSurfaceSplitAlongPolygon.eulerChar_eq
  have hsplit₀ : split.faces ⊆ result.faces := by
    rw [h.result_faces]
    exact fun s hs => Or.inl (Or.inl hs)
  have hcap₀Result : h.cap₀.faces ⊆ result.faces := by
    rw [h.result_faces]
    exact fun s hs => Or.inl (Or.inr hs)
  have hcompat : ∀ s ∈ split.faces, ∀ t ∈ h.cap₀.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht
    exact result.inter_subset_convexHull (hsplit₀ hs) (hcap₀Result ht)
  let U := unionComplex split h.cap₀ hcompat
  let _ : Finite U.faces := finite_unionComplex_faces split h.cap₀ hcompat
  have hinter₀ : eulerChar (intersectionComplex split h.cap₀) = 0 := by
    rw [eulerChar_eq_of_faces_eq (intersectionComplex split h.cap₀) h.capBoundary₀
      h.split_inter_cap₀_faces,
      eulerChar_of_isPLSphere_one h.capBoundary₀ h.capBoundary₀_isPLSphere]
  have hcap₀ : eulerChar h.cap₀ = 1 := eulerChar_of_isPLBall h.cap₀ h.cap₀_isPLBall
  have hU : eulerChar U = eulerChar split + 1 := by
    have hU' := eulerChar_eq_add_sub_of_faces_union U split h.cap₀ rfl
    rw [hinter₀, hcap₀, sub_zero] at hU'
    exact hU'
  have hUfaces : U.faces = split.faces ∪ h.cap₀.faces := rfl
  have hinter₁faces :
      (intersectionComplex U h.cap₁).faces = h.capBoundary₁.faces := by
    ext s
    constructor
    · rintro ⟨hs, hs₁⟩
      rw [hUfaces] at hs
      rcases hs with hs | hs
      · have hs' : s ∈ (intersectionComplex split h.cap₁).faces := ⟨hs, hs₁⟩
        rw [h.split_inter_cap₁_faces] at hs'
        exact hs'
      · exact (Set.disjoint_left.mp h.cap_faces_disjoint hs hs₁).elim
    · intro hs
      have hs' : s ∈ (intersectionComplex split h.cap₁).faces := by
        rw [h.split_inter_cap₁_faces]
        exact hs
      exact ⟨by rw [hUfaces]; exact Or.inl hs'.1, hs'.2⟩
  have hinter₁ : eulerChar (intersectionComplex U h.cap₁) = 0 := by
    rw [eulerChar_eq_of_faces_eq (intersectionComplex U h.cap₁) h.capBoundary₁
      hinter₁faces,
      eulerChar_of_isPLSphere_one h.capBoundary₁ h.capBoundary₁_isPLSphere]
  have hcap₁ : eulerChar h.cap₁ = 1 := eulerChar_of_isPLBall h.cap₁ h.cap₁_isPLBall
  have hresultFaces : result.faces = U.faces ∪ h.cap₁.faces := by
    rw [h.result_faces, hUfaces]
  have hresult := eulerChar_eq_add_sub_of_faces_union result U h.cap₁ hresultFaces
  rw [hinter₁, hcap₁, hU, hsplitResult, sub_zero] at hresult
  omega

end SurfaceSplitAndCap

end DifferentialGeometry.Topology.PiecewiseLinear
