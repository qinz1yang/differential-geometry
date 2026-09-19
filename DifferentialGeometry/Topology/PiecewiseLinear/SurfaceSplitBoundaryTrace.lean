/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitEndpointDisk

/-! Boundary traces of derived-neighborhood disks in surface splitting. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
open Classical in
theorem mem_derivedNeighborhood_faces_iff_of_mem_secondDerived_subcomplex
    (K A B : Geometry.SimplicialComplex ℝ E) (hBK : B.faces ⊆ K.faces)
    {u : Finset E} (hu : u ∈ (secondDerived B).faces) :
    u ∈ (derivedNeighborhood K A).faces ↔ u ∈ (derivedNeighborhood B A).faces := by
  classical
  obtain ⟨D, hD, hDne, rfl⟩ := hu
  have hDBK : IsFlag (barycentricSubdivision K) D :=
    hD.of_le (barycentricSubdivision_faces_subset hBK)
  constructor
  · intro hu
    apply (mem_derivedNeighborhood_faces_iff B A).mpr
    refine ⟨D, hD, hDne, ?_, rfl⟩
    intro e he
    have heK : e ∈ (barycentricSubdivision K).faces := hDBK.mem_faces he
    have hvK : {e.centroid ℝ id} ∈ (derivedNeighborhood K A).faces :=
      (derivedNeighborhood K A).down_closed hu
        (Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ he))
        (Finset.singleton_nonempty _)
    exact (singleton_centroid_mem_derivedNeighborhood_iff K A heK).mp hvK
  · rintro ⟨D', hD', hD'ne, hD'A, hD'u⟩
    exact ⟨D', hD'.of_le (barycentricSubdivision_faces_subset hBK), hD'ne,
      hD'A, hD'u⟩

open Classical in
theorem space_inter_closure_sdiff_derivedNeighborhood_eq
    (K A B : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite B.faces]
    (hBK : B.faces ⊆ K.faces) :
    B.space ∩ closure (K.space \ (derivedNeighborhood K A).space) =
      closure (B.space \ (derivedNeighborhood B A).space) := by
  classical
  let K₂ := secondDerived K
  let B₂ := secondDerived B
  let N := derivedNeighborhood K A
  let Q := derivedNeighborhood B A
  let C := subcomplexGeneratedBy K₂ N.facesᶜ
  let T := subcomplexGeneratedBy B₂ Q.facesᶜ
  let _ : Finite K₂.faces := inferInstance
  let _ : Finite B₂.faces := inferInstance
  let _ : Finite C.faces := (subcomplexGeneratedBy_faces_finite K₂ N.facesᶜ).to_subtype
  have hB₂K₂ : B₂.faces ⊆ K₂.faces := secondDerived_faces_subset hBK
  have hNK₂ : N.faces ⊆ K₂.faces := derivedNeighborhood_faces_subset K A
  have hQB₂ : Q.faces ⊆ B₂.faces := derivedNeighborhood_faces_subset B A
  have hCK₂ : C.faces ⊆ K₂.faces := subcomplexGeneratedBy_faces_subset K₂ N.facesᶜ
  have hcomplex : restrict B₂ C.space = T := by
    ext s
    rw [mem_restrict_faces_iff_of_faces_subset K₂ B₂ C hB₂K₂ hCK₂]
    constructor
    · rintro ⟨hsB₂, hsC⟩
      obtain ⟨t, ⟨htK₂, htN⟩, hst, hsne⟩ := hsC
      by_cases hsQ : s ∈ Q.faces
      · obtain ⟨D, hD, hDne, rfl⟩ := htK₂
        obtain ⟨D₀, hD₀, hD₀ne, rfl⟩ := hsB₂
        have hD₀K : IsFlag (barycentricSubdivision K) D₀ :=
          hD₀.of_le (barycentricSubdivision_faces_subset hBK)
        have hD₀D : D₀ ⊆ D := subset_of_image_centroid_subset K hD hD₀K hst
        have hnot : ¬∀ e ∈ D, ∃ σ ∈ A.faces, σ.centroid ℝ id ∈ e := by
          intro h
          exact htN ((mem_derivedNeighborhood_faces_iff_of_flag hD hDne).mpr h)
        push Not at hnot
        obtain ⟨e, heD, heA⟩ := hnot
        have hD₀A : ∀ e ∈ D₀, ∃ σ ∈ A.faces, σ.centroid ℝ id ∈ e :=
          (mem_derivedNeighborhood_faces_iff_of_flag hD₀ hD₀ne).mp hsQ
        obtain ⟨e₀, he₀D₀⟩ := hD₀ne
        have heSub : e ⊆ e₀ := by
          rcases hD.subset_or_subset heD (hD₀D he₀D₀) with he | he
          · exact he
          · obtain ⟨σ, hσA, hσe₀⟩ := hD₀A e₀ he₀D₀
            exact (heA σ hσA (he hσe₀)).elim
        have heB : e ∈ (barycentricSubdivision B).faces :=
          (barycentricSubdivision B).down_closed (hD₀.mem_faces he₀D₀) heSub
            ((barycentricSubdivision K).nonempty_of_mem_faces (hD.mem_faces heD))
        have hflag : IsFlag (barycentricSubdivision B) (insert e D₀) := by
          constructor
          · intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · exact heB
            · exact hD₀.mem_faces hx
          · intro x hx y hy
            apply hD.subset_or_subset
            · rcases Finset.mem_insert.mp hx with rfl | hx
              · exact heD
              · exact hD₀D hx
            · rcases Finset.mem_insert.mp hy with rfl | hy
              · exact heD
              · exact hD₀D hy
        have hvQ : {e.centroid ℝ id} ∉ Q.faces := by
          rw [singleton_centroid_mem_derivedNeighborhood_iff B A heB]
          push Not
          exact heA
        have htB₂ : (insert e D₀).image (fun d => d.centroid ℝ id) ∈ B₂.faces :=
          ⟨insert e D₀, hflag, Finset.insert_nonempty e D₀, rfl⟩
        have htQ : (insert e D₀).image (fun d => d.centroid ℝ id) ∉ Q.faces := by
          intro ht
          apply hvQ
          apply Q.down_closed ht
            (Finset.singleton_subset_iff.mpr
              (Finset.mem_image_of_mem (fun d => d.centroid ℝ id) (Finset.mem_insert_self e D₀)))
          exact Finset.singleton_nonempty _
        refine ⟨(insert e D₀).image (fun d => d.centroid ℝ id), ⟨htB₂, ?_⟩, ?_,
          hsne⟩
        · simpa only [Set.mem_compl_iff] using htQ
        rw [Finset.image_insert]
        exact Finset.subset_insert _ _
      · refine ⟨s, ⟨hsB₂, ?_⟩, Finset.Subset.rfl, hsne⟩
        simpa only [Set.mem_compl_iff] using hsQ
    · rintro ⟨t, ⟨htB₂, htQ⟩, hst, hsne⟩
      have htQ' : t ∉ Q.faces := by simpa only [Set.mem_compl_iff] using htQ
      have htN : t ∉ N.faces := by
        intro htN
        exact htQ' ((mem_derivedNeighborhood_faces_iff_of_mem_secondDerived_subcomplex
          K A B hBK htB₂).mp htN)
      exact ⟨B₂.down_closed htB₂ hst hsne,
        ⟨t, ⟨hB₂K₂ htB₂, htN⟩, hst, hsne⟩⟩
  have hspace : B₂.space ∩ C.space = T.space := by
    rw [← restrict_space_eq_inter_of_faces_subset K₂ B₂ C hB₂K₂ hCK₂, hcomplex]
  rw [← (secondDerived_isSubdivision B).space_eq,
    ← (secondDerived_isSubdivision K).space_eq,
    closure_space_sdiff_space_eq_subcomplexGeneratedBy K₂ K₂ N Subset.rfl hNK₂,
    closure_space_sdiff_space_eq_subcomplexGeneratedBy B₂ B₂ Q Subset.rfl hQB₂]
  exact hspace

open Classical in
theorem derivedNeighborhood_surface_inter_boundaryComplex
    (K A B : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite B.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hB : IsCombinatorialManifoldWithBoundary 2 B)
    (hBK : B.faces ⊆ K.faces) (hAB : A.faces ⊆ B.faces)
    (hNdis : Disjoint (derivedNeighborhood K A).space (boundaryComplex 3 K).space)
    (hQdis : Disjoint (derivedNeighborhood B A).space (boundaryComplex 2 B).space) :
    (derivedNeighborhood B A).space ∩
        (boundaryComplex 3 (derivedNeighborhood K A)).space =
      (boundaryComplex 2 (derivedNeighborhood B A)).space := by
  classical
  let N := derivedNeighborhood K A
  let Q := derivedNeighborhood B A
  let _ : Finite N.faces := (derivedNeighborhood_faces_finite K A).to_subtype
  let _ : Finite Q.faces := (derivedNeighborhood_faces_finite B A).to_subtype
  have hN := hK.derivedNeighborhood A
  have hQ := hB.derivedNeighborhood A
  have hNK : N.space ⊆ K.space := derivedNeighborhood_space_subset K A
  have hQB : Q.space ⊆ B.space := derivedNeighborhood_space_subset B A
  have hQN : Q.space ⊆ N.space := by
    intro x hx
    exact (derivedNeighborhood_space_inter_subcomplex K A B hBK hAB).symm.subset hx |>.1
  have hboundaryN := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary
    K N hK hN hNK hNdis
  have hboundaryQ := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary
    B Q hB hQ hQB hQdis
  have htrace := space_inter_closure_sdiff_derivedNeighborhood_eq K A B hBK
  rw [← hboundaryN, ← hboundaryQ, ← htrace]
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨hxQ, -, hxC⟩
    exact ⟨hxQ, hQB hxQ, hxC⟩
  · rintro ⟨hxQ, -, hxC⟩
    exact ⟨hxQ, hQN hxQ, hxC⟩

open Classical in
theorem
    IsCombinatorialManifold.exists_isSubdivision_disk_pair_with_derivedNeighborhood_boundary_trace
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 3 K) {Δ D₁ D₂ U : Set E}
    (hΔ : IsPLBall 2 Δ) (hD₁ : IsPLBall 2 D₁)
    {r₂ : (Fin 3 → ℝ) → E}
    (hr₂ : IsPLHomeomorphOn r₂ (stdSimplex ℝ (Fin 3)) D₂)
    (hΔintD₂ : Δ ⊆ r₂ '' openSimplex (stdVertices 1))
    (hΔD₁ : Δ ⊆ D₁) (hΔD₂ : Δ ⊆ D₂) (hD₁D₂ : D₁ ∩ D₂ = Δ)
    (hD₁K : D₁ ⊆ K.space) (hD₂K : D₂ ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] Δ) :
    ∃ (R A A₁ A₂ : Geometry.SimplicialComplex ℝ E)
      (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (φ : E → EuclideanSpace ℝ (Fin 2)) (ψ : EuclideanSpace ℝ (Fin 2) → E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ A.faces.Finite ∧ A.space = Δ ∧
      A₁.faces ⊆ R.faces ∧ A₁.faces.Finite ∧ A₁.space = D₁ ∧
      A₂.faces ⊆ R.faces ∧ A₂.faces.Finite ∧ A₂.space = D₂ ∧
      A.faces ⊆ A₁.faces ∧ A.faces ⊆ A₂.faces ∧ A₁.space ∩ A₂.space = A.space ∧
      L.faces.Finite ∧ IsPLBall 2 L.space ∧ IsGlueIso A L φ ψ ∧
      IsPLBall 3 (derivedNeighborhood R A).space ∧
      Δ ⊆ (derivedNeighborhood R A).space ∧
      (derivedNeighborhood R A).space ⊆ K.space ∧
      (derivedNeighborhood R A).space ⊆ U ∧
      (∀ x ∈ Δ, (derivedNeighborhood R A).space ∈ 𝓝[K.space] x) ∧
      IsPLBall 2 (D₂ ∩ (derivedNeighborhood R A).space) ∧
      (D₂ ∩ (derivedNeighborhood R A).space) ∩
          (boundaryComplex 3 (derivedNeighborhood R A)).space =
        (boundaryComplex 2 (derivedNeighborhood A₂ A)).space := by
  classical
  let J := r₂ '' stdSimplexBoundary 2
  have hD₂ : IsPLBall 2 D₂ := ⟨r₂, hr₂⟩
  have hJclosed : IsClosed J := hr₂.isPLSphere_image_stdSimplexBoundary.isPolyhedron.isClosed
  have hΔJ : Δ ⊆ Jᶜ := by
    intro x hx
    have hx' := hΔintD₂ hx
    rw [hr₂.image_openSimplex_stdVertices] at hx'
    exact hx'.2
  have hJnhds : Jᶜ ∈ 𝓝ˢ Δ := mem_nhdsSet_iff_forall.mpr fun x hx =>
    hJclosed.isOpen_compl.mem_nhds (hΔJ hx)
  have hV : U ∩ Jᶜ ∈ 𝓝ˢ[K.space] Δ :=
    Filter.inter_mem hU (Filter.mem_inf_of_left hJnhds)
  obtain ⟨R, A, A₁, A₂, L, φ, ψ, hR, hRfin, hAR, hAfin, hAΔ,
      hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
      hLfin, hL, hIso, hNball, hcontains, hNK, hNV, hnhds, hBball⟩ :=
    hK.isCombinatorialManifoldWithBoundary
      |>.exists_isSubdivision_disk_pair_with_derivedNeighborhood_endpoint_disk
        hΔ hD₁ hD₂ hΔD₁ hΔD₂ hD₁D₂ hD₁K hD₂K hV
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite A₂.faces := hA₂fin.to_subtype
  let N := derivedNeighborhood R A
  let Q := derivedNeighborhood A₂ A
  have hNU : N.space ⊆ U := hNV.trans inter_subset_left
  have hNJ : Disjoint N.space J := by
    apply disjoint_left.mpr
    intro x hxN hxJ
    exact (hNV hxN).2 hxJ
  have hRman : IsCombinatorialManifold 3 R := hK.of_isSubdivision hR
  have hRB : (boundaryComplex 3 R).space = ∅ := by
    change (⋃ t ∈ (boundaryComplex 3 R).faces, convexHull ℝ (t : Set E)) = ∅
    rw [hRman.boundaryComplex_faces_eq_empty]
    simp
  have hNdis : Disjoint N.space (boundaryComplex 3 R).space := by
    rw [hRB]
    exact disjoint_empty N.space
  have hmiddle : D₂ ∩ N.space = Q.space := by
    rw [← hA₂D₂, inter_comm]
    exact derivedNeighborhood_space_inter_subcomplex R A A₂ hA₂R hAA₂
  have hQN : Q.space ⊆ N.space := hmiddle.symm.subset.trans inter_subset_right
  have hA₂boundary : J = (boundaryComplex 2 A₂).space :=
    hr₂.image_stdSimplexBoundary_eq_boundaryComplex A₂ hA₂D₂
  have hQdis : Disjoint Q.space (boundaryComplex 2 A₂).space := by
    rw [← hA₂boundary]
    exact hNJ.mono_left hQN
  have hA₂ball : IsPLBall 2 A₂.space := hA₂D₂.symm ▸ hD₂
  have htrace := derivedNeighborhood_surface_inter_boundaryComplex R A A₂
    hRman.isCombinatorialManifoldWithBoundary
    hA₂ball.isCombinatorialManifoldWithBoundary
    hA₂R hAA₂ hNdis hQdis
  refine ⟨R, A, A₁, A₂, L, φ, ψ, hR, hRfin, hAR, hAfin, hAΔ,
    hA₁R, hA₁fin, hA₁D₁, hA₂R, hA₂fin, hA₂D₂, hAA₁, hAA₂, hmeet,
    hLfin, hL, hIso, hNball, hcontains, hNK, hNU, hnhds, hBball, ?_⟩
  rw [hmiddle]
  exact htrace

end DifferentialGeometry.Topology.PiecewiseLinear
