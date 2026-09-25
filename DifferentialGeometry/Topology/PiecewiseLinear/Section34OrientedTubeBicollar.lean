import DifferentialGeometry.Topology.PiecewiseLinear.Section34InnerTubeBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.InteriorManifoldComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_oriented_boundary_bicollar
    {K A : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.space ⊆ K.space)
    (hdis : Disjoint A.space (boundaryComplex 3 K).space) :
    ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧
      W ⊆ K.space \ (boundaryComplex 3 K).space ∧
      W ∈ 𝓝ˢ[K.space] (boundaryComplex 3 A).space ∧
      IsPLHomeomorphOn ρ ((boundaryComplex 3 A).space ×ˢ Icc (-1 : ℝ) 1) W ∧
      (∀ x ∈ (boundaryComplex 3 A).space, ρ (x, 0) = x) ∧
      ∀ p ∈ (boundaryComplex 3 A).space ×ˢ Icc (-1 : ℝ) 1,
        ρ p ∈ A.space ↔ 0 ≤ p.2 := by
  obtain ⟨R, hRfin, hR, hRspace⟩ :=
    hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_of_disjoint_boundary
      hA hAK hdis
  let _ : Finite R.faces := hRfin.to_subtype
  let B := (boundaryComplex 3 A).space
  have hBA : B ⊆ A.space := boundaryComplex_space_subset 3 A
  have hBdis : Disjoint B (boundaryComplex 3 K).space := hdis.mono_left hBA
  have hRK : R.space ⊆ K.space := by
    rw [hRspace]
    exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hmeet : A.space ∩ R.space = B := by
    rw [hRspace]
    exact inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K A hK hA hAK hdis
  have hcover : A.space ∪ R.space = K.space := by
    refine Subset.antisymm (union_subset hAK hRK) ?_
    intro x hx
    by_cases hxA : x ∈ A.space
    · exact Or.inl hxA
    · exact Or.inr (hRspace.symm ▸ subset_closure ⟨hx, hxA⟩)
  have hRbd : (boundaryComplex 3 R).space = (boundaryComplex 3 K).space ∪ B := by
    rw [boundaryComplex_space_of_closure_sdiff K A R hK hA hAK hR hRspace,
      hdis.symm.sdiff_eq_left, hBdis.sdiff_eq_left,
      (isPolyhedron_space (boundaryComplex 3 K)).isClosed.closure_eq,
      (isPolyhedron_space (boundaryComplex 3 A)).isClosed.closure_eq]
  have hBR : B ⊆ (boundaryComplex 3 R).space :=
    subset_union_right.trans hRbd.symm.subset
  have hcompl : IsClosed ((boundaryComplex 3 R).space \ B) := by
    rw [hRbd, union_sdiff_right, hBdis.symm.sdiff_eq_left]
    exact (isPolyhedron_space (boundaryComplex 3 K)).isClosed
  have hBpoly : IsPolyhedron B := isPolyhedron_space (boundaryComplex 3 A)
  obtain ⟨WNeg, ρNeg, hWNeg, hWNegR, hWNegn, hρNeg, hNeg, htraceNeg, -⟩ :=
    hR.exists_collar_of_boundary_subset R hBpoly hBR hcompl
  obtain ⟨WPos, ρPos, hWPos, hWPosA, hWPosn, hρPos, hPos, htracePos, -⟩ :=
    hA.exists_collar_of_boundary_subset A hBpoly Subset.rfl (by
      change IsClosed ((boundaryComplex 3 A).space \ (boundaryComplex 3 A).space)
      simp)
  have hWW : WNeg ∩ WPos = B := by
    refine Subset.antisymm (fun x hx => hmeet ▸ ⟨hWPosA hx.2, hWNegR hx.1⟩) ?_
    intro x hx
    exact ⟨(htraceNeg.symm.subset hx).1, (htracePos.symm.subset hx).1⟩
  obtain ⟨ρ, hρ, hzero, hneg, hpos⟩ :=
    exists_isPLHomeomorphOn_prod_Icc_of_collars hBpoly hρNeg hρPos hNeg hPos hWW
  have hWK : WNeg ∪ WPos ⊆ K.space := union_subset (hWNegR.trans hRK) (hWPosA.trans hAK)
  have hWint : WNeg ∪ WPos ⊆ K.space \ (boundaryComplex 3 K).space := by
    intro x hx
    refine ⟨hWK hx, ?_⟩
    intro hxK
    rcases hx with hx | hx
    · exact disjoint_left.mp hBdis
        (htraceNeg.subset ⟨hx, hRbd.symm.subset (Or.inl hxK)⟩) hxK
    · exact disjoint_left.mp hdis (hWPosA hx) hxK
  have hpoint : ∀ x ∈ B, WNeg ∪ WPos ∈ 𝓝[K.space] x := by
    obtain ⟨ONeg, hONeg, hBONeg, hOWNeg⟩ := mem_nhdsSetWithin.mp hWNegn
    obtain ⟨OPos, hOPos, hBOPos, hOWPos⟩ := mem_nhdsSetWithin.mp hWPosn
    intro x hx
    have hnNeg : WNeg ∈ 𝓝[R.space] x := mem_nhdsWithin.mpr ⟨ONeg, hONeg, hBONeg hx, hOWNeg⟩
    have hnPos : WPos ∈ 𝓝[A.space] x := mem_nhdsWithin.mpr ⟨OPos, hOPos, hBOPos hx, hOWPos⟩
    rw [← hcover, nhdsWithin_union, Filter.mem_sup]
    exact ⟨Filter.mem_of_superset hnPos subset_union_right,
      Filter.mem_of_superset hnNeg subset_union_left⟩
  have hnhds : WNeg ∪ WPos ∈ 𝓝ˢ[K.space] B := by
    have hpre : ((↑) : K.space → E) ⁻¹' (WNeg ∪ WPos) ∈
        𝓝ˢ (((↑) : K.space → E) ⁻¹' B) := mem_nhdsSet_iff_forall.mpr fun x hx =>
      preimage_coe_mem_nhds_subtype.mpr (hpoint x hx)
    have h := mem_nhdsSet_subtype_iff_nhdsSetWithin.mp hpre
    rwa [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      inter_eq_right.mpr hWK, inter_eq_right.mpr (hBA.trans hAK)] at h
  refine ⟨WNeg ∪ WPos, ρ, hWNeg.union hWPos, hWint, hnhds, hρ, hzero, ?_⟩
  intro p hp
  constructor
  · intro hpA
    by_contra hn
    have hh := hneg ⟨hp.1, hp.2.1, lt_of_not_ge hn⟩
    exact hh.2 (hmeet ▸ ⟨hpA, hWNegR hh.1⟩)
  · intro ht
    rcases eq_or_lt_of_le ht with ht | ht
    · have heq : p = (p.1, 0) := Prod.ext rfl ht.symm
      rw [heq, hzero p.1 hp.1]
      exact hBA hp.1
    · exact hWPosA (hpos ⟨hp.1, ht, hp.2.2⟩).1

open Classical in
theorem IsPLHomeomorphInto.exists_oriented_bicollar_invFunOn_image
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPLBall 3 P) {N : Set M}
    (hN : IsPolyhedralManifoldWithBoundary (n := 3) 3 N)
    (hNP : N ⊆ interior (u '' P)) :
    ∃ (W : Set (EuclideanSpace ℝ (Fin 3)))
        (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPolyhedron W ∧ W ⊆ interior P ∧
      W ∈ 𝓝ˢ[P] (frontier (Function.invFunOn u P '' N)) ∧
      IsPLHomeomorphOn ρ ((frontier (Function.invFunOn u P '' N)) ×ˢ Icc (-1 : ℝ) 1) W ∧
      (∀ x ∈ frontier (Function.invFunOn u P '' N), ρ (x, 0) = x) ∧
      ∀ p ∈ frontier (Function.invFunOn u P '' N) ×ˢ Icc (-1 : ℝ) 1,
        ρ p ∈ Function.invFunOn u P '' N ↔ 0 ≤ p.2 := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨K, hKfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifoldWithBoundary 3 K :=
    (hKspace.symm ▸ hP).isCombinatorialManifoldWithBoundary
  obtain ⟨A, hAfin, hAspace, hA⟩ :=
    hu.exists_simplicialComplex_invFunOn_image hN (hNP.trans interior_subset)
  let _ : Finite A.faces := hAfin.to_subtype
  have hAint : A.space ⊆ interior P := by
    rw [hAspace]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hu.image_interior.symm.subset (hNP hy)
    rw [← hxy, hu.injOn.leftInvOn_invFunOn (interior_subset hx)]
    exact hx
  have hAK : A.space ⊆ K.space := hAint.trans (interior_subset.trans hKspace.symm.subset)
  have hAdis : Disjoint A.space (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space hK, hKspace]
    exact disjoint_interior_frontier.mono_left hAint
  obtain ⟨W, ρ, hW, hWint, hWnhds, hρ, hzero, hside⟩ :=
    hK.exists_oriented_boundary_bicollar hA hAK hAdis
  rw [← frontier_space_eq_boundaryComplex_space hK, hKspace, self_sdiff_frontier] at hWint
  rw [hKspace, ← frontier_space_eq_boundaryComplex_space hA, hAspace] at hWnhds
  rw [← frontier_space_eq_boundaryComplex_space hA, hAspace] at hρ hzero hside
  exact ⟨W, ρ, hW, hWint, hWnhds, hρ, hzero, hside⟩

omit [FiniteDimensional ℝ E] in
theorem IsPLHomeomorphOn.image_nonnegative_half_of_mem_iff
    {B W T : Set E} {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (-1 : ℝ) 1) W)
    (hside : ∀ p ∈ B ×ˢ Icc (-1 : ℝ) 1, ρ p ∈ T ↔ 0 ≤ p.2) :
    ρ '' (B ×ˢ Icc (0 : ℝ) 1) = W ∩ T := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hp' : p ∈ B ×ˢ Icc (-1 : ℝ) 1 := ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩
    exact ⟨hρ.bijOn.mapsTo hp', (hside p hp').mpr hp.2.1⟩
  · rintro x ⟨hxW, hxT⟩
    obtain ⟨p, hp, rfl⟩ := hρ.bijOn.surjOn hxW
    exact ⟨p, ⟨hp.1, (hside p hp).mp hxT, hp.2.2⟩, rfl⟩

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}

theorem exists_section34_oriented_inner_tube_bicollar
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) (e : Section34EdgeIndex 𝒦 𝒦') :
    ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (u : EuclideanSpace ℝ (Fin 3) → M₁)
        (W : Set (EuclideanSpace ℝ (Fin 3)))
        (ρ : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧ Cc (ends e).1 = u '' P ∧
      IsPolyhedron W ∧ W ⊆ interior P ∧
      W ∈ 𝓝ˢ[P] (frontier (Function.invFunOn u P '' Tn e)) ∧
      IsPLHomeomorphOn ρ
        ((frontier (Function.invFunOn u P '' Tn e)) ×ˢ Icc (-1 : ℝ) 1) W ∧
      (∀ x ∈ frontier (Function.invFunOn u P '' Tn e), ρ (x, 0) = x) ∧
      ρ '' (frontier (Function.invFunOn u P '' Tn e) ×ˢ Icc (0 : ℝ) 1) =
        W ∩ (Function.invFunOn u P '' Tn e) := by
  obtain ⟨P, u, _, _, hP, hu, hCc, hN, -⟩ := exists_section34_inner_tube_bicollar hprep e
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htor, hSnCc, -⟩ := hprep
  have hNP : Tn e ⊆ interior (u '' P) := by
    rw [← hCc]
    exact (htor e).1.trans (interior_mono (hSnCc e _ (Or.inl rfl)))
  obtain ⟨W, ρ, hW, hWint, hn, hρ, hzero, hside⟩ :=
    hu.exists_oriented_bicollar_invFunOn_image hP hN hNP
  exact ⟨P, u, W, ρ, hP, hu, hCc, hW, hWint, hn, hρ, hzero,
    hρ.image_nonnegative_half_of_mem_iff hside⟩

end DifferentialGeometry.Topology.PiecewiseLinear
