import DifferentialGeometry.Topology.PiecewiseLinear.CollarNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_collar_of_boundary_subset
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {S : Set E}
    (hS : IsPolyhedron S) (hSB : S ⊆ (boundaryComplex 3 K).space)
    (hcompl : IsClosed ((boundaryComplex 3 K).space \ S)) :
    ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧ W ⊆ K.space ∧
      W ∈ 𝓝ˢ[K.space] S ∧ IsPLHomeomorphOn ρ (S ×ˢ Icc (0 : ℝ) 1) W ∧
      (∀ x ∈ S, ρ (x, 0) = x) ∧ W ∩ (boundaryComplex 3 K).space = S ∧
      MapsTo ρ (S ×ˢ Ioc (0 : ℝ) 1) (K.space \ (boundaryComplex 3 K).space) := by
  obtain ⟨V, ρ, -, hVK, hVnhds, hρ, hbottom, -, hpositive⟩ := hK.exists_collar K
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let W := ρ '' (S ×ˢ Icc (0 : ℝ) 1)
  let T := ρ '' ((B.space \ S) ×ˢ Icc (0 : ℝ) 1)
  have hprod : IsPolyhedron (S ×ˢ Icc (0 : ℝ) 1) :=
    hS.prod (isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).isPolyhedron
  have hsub : S ×ˢ Icc (0 : ℝ) 1 ⊆ B.space ×ˢ Icc (0 : ℝ) 1 :=
    prod_mono hSB Subset.rfl
  have hρW : IsPLHomeomorphOn ρ (S ×ˢ Icc (0 : ℝ) 1) W := hρ.restrict hprod hsub
  have hWV : W ⊆ V := (image_mono hsub).trans hρ.image_eq.subset
  have hTclosed : IsClosed T := by
    have hcompact : IsCompact (B.space \ S) :=
      (isPolyhedron_space B).isCompact.of_isClosed_subset hcompl sdiff_subset
    exact ((hcompact.prod isCompact_Icc).image_of_continuousOn
      (hρ.isPiecewiseAffineOn.continuousOn.mono (prod_mono sdiff_subset Subset.rfl))).isClosed
  have hST : Disjoint S T := by
    apply disjoint_left.mpr
    rintro x hx ⟨y, hy, hxy⟩
    have heq : y = (x, 0) := hρ.bijOn.injOn ⟨hy.1.1, hy.2⟩
      ⟨hSB hx, by norm_num, by norm_num⟩ (hxy.trans (hbottom x (hSB hx)).symm)
    exact hy.1.2 ((congrArg Prod.fst heq).symm ▸ hx)
  have hWnhds : W ∈ 𝓝ˢ[K.space] S := by
    obtain ⟨O, hO, hBO, hOV⟩ := mem_nhdsSetWithin.mp hVnhds
    refine mem_nhdsSetWithin.mpr ⟨O \ T, hO.sdiff hTclosed,
      fun x hx => ⟨hBO (hSB hx), fun hxT => disjoint_left.mp hST hx hxT⟩, ?_⟩
    rintro x ⟨hxO, hxK⟩
    obtain ⟨y, hy, hxy⟩ := hρ.bijOn.surjOn (hOV ⟨hxO.1, hxK⟩)
    have hyS : y.1 ∈ S := by
      by_contra hyS
      exact hxO.2 ⟨y, ⟨⟨hy.1, hyS⟩, hy.2⟩, hxy⟩
    exact ⟨y, ⟨hyS, hy.2⟩, hxy⟩
  refine ⟨W, ρ, hprod.image_of_isPiecewiseAffineOn hρW.isPiecewiseAffineOn hρW.bijOn.injOn,
    hWV.trans hVK, hWnhds, hρW, fun x hx => hbottom x (hSB hx), ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨⟨y, hy, hxy⟩, hxB⟩
      have heq : y = (x, 0) := hρ.bijOn.injOn (hsub hy)
        ⟨hxB, by norm_num, by norm_num⟩ (hxy.trans (hbottom x hxB).symm)
      have hfst : y.1 = x := congrArg Prod.fst heq
      exact hfst ▸ hy.1
    · intro x hx
      exact ⟨⟨(x, 0), ⟨hx, by norm_num, by norm_num⟩, hbottom x (hSB hx)⟩, hSB hx⟩
  · intro x hx
    exact hpositive ⟨hSB hx.1, hx.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
