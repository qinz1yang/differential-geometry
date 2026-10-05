import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.MoiseChainPL

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section ReadBack

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_polyhedralDisk_of_embeddedDisk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {S : NormalSystem E} (A : NormalSystem.EmbeddedDisk S)
    (hSK : S.manifoldComplex.space ⊆ K.space)
    (hBK : S.boundaryNeighborhood.space ⊆ (boundaryComplex 3 K).space)
    {V : Set E} (β : C(S.boundaryNeighborhoodSpace, V)) (hβ : ∀ x, (β x : E) = (x : E))
    {y : V} (hb : β S.basepoint = y)
    (hN : S.normalSubgroup = (⊥ : Subgroup (FundamentalGroup V y)).comap
      (FundamentalGroup.mapOfEq β hb)) :
    ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ K.space ∧
      Δ ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2 ∧
      ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ V,
        ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
          C(r '' stdSimplexBoundary 2, V)).Nullhomotopic := by
  obtain ⟨γ, q, hrange, havoid⟩ :=
    A.exists_boundaryLoop_of_comap β hβ hb (⊥ : Subgroup (FundamentalGroup V y)) hN
  have hpre := A.preimage_boundaryComplex_eq K hK hSK hBK
  obtain ⟨p, hp⟩ := A.isPLBall_domain
  have hfront : (A.map ∘ p) '' stdSimplexBoundary 2 = A.map '' frontier A.domain := by
    rw [image_comp, hp.image_stdSimplexBoundary_eq_frontier]
  have hinter : A.map '' A.domain ∩ (boundaryComplex 3 K).space = A.map '' frontier A.domain := by
    rw [← image_inter_preimage, hpre]
  have hbsub : (A.map ∘ p) '' stdSimplexBoundary 2 ⊆ V := by
    rw [hfront, ← hrange]
    rintro _ ⟨θ, rfl⟩
    exact (γ θ).property
  refine ⟨A.map '' A.domain, A.map ∘ p, hp.trans A.isPLHomeomorphOn,
    (A.mapsTo.mono_right hSK).image_subset, hinter.trans hfront.symm, hbsub, ?_⟩
  intro hnull
  refine havoid ((conjugacyClassMeets_bot_iff_nullhomotopic γ q).mpr ?_)
  refine nullhomotopic_freeLoop_of_inclusion_nullhomotopic hbsub hnull γ fun θ => ?_
  rw [hfront, ← hrange]
  exact ⟨θ, rfl⟩

end ReadBack

open Classical in
theorem exists_polyhedralDisk_of_normalSystemDisk {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdisk : ∀ S : NormalSystem E,
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space → Nonempty (NormalSystem.EmbeddedDisk S))
    (K : Geometry.SimplicialComplex ℝ E) (hKfin : Finite K.faces)
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (hsub : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ K.space)
    (γ : freeLoop (connectedComponentComplex (boundaryComplex 3 K) c).space)
    (hnull : IsNullHomotopic ((⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
      C((connectedComponentComplex (boundaryComplex 3 K) c).space, K.space)).comp γ))
    (hess : ¬ IsNullHomotopic γ) :
    ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ K.space ∧
      Δ ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2 ∧
      ∃ hboundary : r '' stdSimplexBoundary 2 ⊆
          (connectedComponentComplex (boundaryComplex 3 K) c).space,
        ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
          C(r '' stdSimplexBoundary 2,
            (connectedComponentComplex (boundaryComplex 3 K) c).space)).Nullhomotopic := by
  let _ : Finite K.faces := hKfin
  have hVB : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆
      (boundaryComplex 3 K).space :=
    space_mono_of_faces_subset (restrict_faces_subset (boundaryComplex 3 K) _)
  have hVcomp : ∀ z ∈ (connectedComponentComplex (boundaryComplex 3 K) c).space,
      connectedComponentIn (boundaryComplex 3 K).space z =
        (connectedComponentComplex (boundaryComplex 3 K) c).space := fun z hz =>
    (connectedComponentComplex_space_eq_connectedComponentIn (boundaryComplex 3 K) c hz).symm
  obtain ⟨P, f, a, δ, hP, hf, hfmap, hfbd, hδ, hhom⟩ :=
    exists_isPiecewiseAffineOn_fill_of_nullhomotopic K (boundaryComplex 3 K)
      (boundaryComplex_faces_subset 3 K) hVB hsub hVcomp γ hnull
  have hδess : ¬ δ.Nullhomotopic := fun hd =>
    hess (show γ.Nullhomotopic from FreeLoop.nullhomotopic_of_homotopic hhom hd)
  obtain ⟨O, hO, hOV⟩ :=
    exists_isOpen_inter_eq_connectedComponentComplex_space (boundaryComplex 3 K) c
  have hnbhd : (connectedComponentComplex (boundaryComplex 3 K) c).space ∈
      𝓝ˢ[(boundaryComplex 3 K).space] (f '' frontier P) := by
    refine mem_nhdsSetWithin.mpr ⟨O, hO, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (hOV.symm.subset (hfbd hz)).1
    · exact hOV.subset
  obtain ⟨S, hsource, hsubdiv, -, -, -, hproperS, hSB, β, hbase, hβ, -, hNcomap⟩ :=
    exists_normalSystem_of_isPiecewiseAffineOn K hK hP hf hfmap (hfbd.mono_right hVB) hnbhd a δ hδ
      (⊥ : Subgroup (FundamentalGroup
        (connectedComponentComplex (boundaryComplex 3 K) c).space (δ 0)))
      (fun hmeet => hδess ((conjugacyClassMeets_bot_iff_nullhomotopic δ _).mp hmeet))
  have hSK : S.manifoldComplex.space ⊆ K.space := by
    rw [S.manifold_space]
    exact (derivedNeighborhood_space_subset S.ambientComplex S.imageComplex).trans
      hsubdiv.space_eq.subset
  have hproper : S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
      frontier S.sourceComplex.space := hproperS.trans (congrArg frontier hsource.symm)
  exact exists_polyhedralDisk_of_embeddedDisk K hK (Classical.choice (hdisk S hproper)) hSK
    (fun z hz => (hSB hz).1) β hβ hbase hNcomap

end DifferentialGeometry.Topology.PiecewiseLinear
