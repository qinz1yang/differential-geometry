/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurveInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.MoiseChainPL
import DifferentialGeometry.Topology.PiecewiseLinear.TorusMeridian

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_normalSystem_of_component_loop {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hKfin : K.faces.Finite)
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (hsub : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ K.space)
    (γ : freeLoop (connectedComponentComplex (boundaryComplex 3 K) c).space)
    (hnull : ((⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
      C((connectedComponentComplex (boundaryComplex 3 K) c).space, K.space)).comp γ).Nullhomotopic)
    (hess : ¬ γ.Nullhomotopic) :
    ∃ S : NormalSystem E,
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space ∧
      S.basepoint = S.boundaryLoop 0 := by
  let _ : Finite K.faces := hKfin.to_subtype
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
    hess (FreeLoop.nullhomotopic_of_homotopic hhom hd)
  obtain ⟨O, hO, hOV⟩ :=
    exists_isOpen_inter_eq_connectedComponentComplex_space (boundaryComplex 3 K) c
  have hnbhd : (connectedComponentComplex (boundaryComplex 3 K) c).space ∈
      𝓝ˢ[(boundaryComplex 3 K).space] (f '' frontier P) := by
    refine mem_nhdsSetWithin.mpr ⟨O, hO, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (hOV.symm.subset (hfbd hz)).1
    · exact hOV.subset
  obtain ⟨S, hsource, -, -, -, hbase, hproper, -, -⟩ :=
    exists_normalSystem_of_isPiecewiseAffineOn K hK hP hf hfmap (hfbd.mono_right hVB) hnbhd a δ hδ
      (⊥ : Subgroup (FundamentalGroup
        (connectedComponentComplex (boundaryComplex 3 K) c).space (δ 0)))
      (fun hmeet => hδess ((conjugacyClassMeets_bot_iff_nullhomotopic δ _).mp hmeet))
  exact ⟨S, hproper.trans (congrArg frontier hsource.symm), hbase⟩

open Classical in
theorem exists_normalSystem_of_essential_boundary_circle {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    (K : Geometry.SimplicialComplex ℝ E) (hKfin : K.faces.Finite)
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {J : Set E} (hJ : IsPLSphere 1 J)
    (hJb : J ⊆ frontier K.space) (hJK : J ⊆ K.space)
    (hnull : (⟨Set.inclusion hJK, continuous_inclusion hJK⟩ : C(J, K.space)).Nullhomotopic)
    (hess : ¬ (⟨Set.inclusion hJb, continuous_inclusion hJb⟩ :
      C(J, frontier K.space)).Nullhomotopic) :
    ∃ S : NormalSystem E,
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space ∧
      S.basepoint = S.boundaryLoop 0 := by
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨e⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ
  have hdim' : Module.finrank ℝ E = 2 + 1 := by rw [hdim]
  have hfr : frontier K.space = (boundaryComplex 3 K).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank hdim' K hK
  have hJB : J ⊆ (boundaryComplex 3 K).space := hJb.trans hfr.subset
  have hx : (e 0 : E) ∈ (boundaryComplex 3 K).space := hJB (e 0).2
  obtain ⟨c, hc⟩ : ∃ c : ConnectedComponents (boundaryComplex 3 K).space,
      c = ConnectedComponents.mk ⟨(e 0 : E), hx⟩ := ⟨_, rfl⟩
  have hxV : (e 0 : E) ∈ (connectedComponentComplex (boundaryComplex 3 K) c).space := by
    rw [hc, connectedComponentComplex_space]
    exact ⟨⟨_, hx⟩, rfl, rfl⟩
  have hJV : J ⊆ (connectedComponentComplex (boundaryComplex 3 K) c).space := by
    rw [connectedComponentComplex_space_eq_connectedComponentIn _ c hxV]
    exact hJ.isConnected_one.isPreconnected.subset_connectedComponentIn (e 0).2 hJB
  have hVB : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆
      (boundaryComplex 3 K).space :=
    space_mono_of_faces_subset (restrict_faces_subset (boundaryComplex 3 K) _)
  have hsub : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ K.space :=
    hVB.trans (space_mono_of_faces_subset (boundaryComplex_faces_subset 3 K))
  have hVfr : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ frontier K.space :=
    hVB.trans hfr.symm.subset
  refine exists_normalSystem_of_component_loop K hKfin hK c hsub
    ⟨fun θ => ⟨(e θ : E), hJV (e θ).2⟩,
      (continuous_subtype_val.comp e.continuous).subtype_mk _⟩ ?_ ?_
  · have hcomp : (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
        C((connectedComponentComplex (boundaryComplex 3 K) c).space, K.space)).comp
          ⟨fun θ => ⟨(e θ : E), hJV (e θ).2⟩,
            (continuous_subtype_val.comp e.continuous).subtype_mk _⟩ =
        (⟨Set.inclusion hJK, continuous_inclusion hJK⟩ : C(J, K.space)).comp
          (e : C(loopCircle, J)) :=
      ContinuousMap.ext fun _ => rfl
    rw [hcomp]
    exact hnull.comp_left _
  · intro hg
    refine hess ?_
    have h2 := (hg.comp_right (⟨Set.inclusion hVfr, continuous_inclusion hVfr⟩ :
      C((connectedComponentComplex (boundaryComplex 3 K) c).space,
        frontier K.space))).comp_left (e.symm : C(J, loopCircle))
    have h3 : ((⟨Set.inclusion hVfr, continuous_inclusion hVfr⟩ :
        C((connectedComponentComplex (boundaryComplex 3 K) c).space, frontier K.space)).comp
          ⟨fun θ => ⟨(e θ : E), hJV (e θ).2⟩,
            (continuous_subtype_val.comp e.continuous).subtype_mk _⟩).comp
          (e.symm : C(J, loopCircle)) =
        (⟨Set.inclusion hJb, continuous_inclusion hJb⟩ : C(J, frontier K.space)) :=
      ContinuousMap.ext fun y => congrArg (Set.inclusion hJb) (e.apply_symm_apply y)
    rwa [h3] at h2

open Classical in
theorem exists_normalSystem_euclideanSpace_three :
    ∃ S : NormalSystem (EuclideanSpace ℝ (Fin 3)),
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space ∧
      S.basepoint = S.boundaryLoop 0 := by
  obtain ⟨K, J, _Ddisk, _rpar, hKfin, hK, -, -, -, hJ, -, -, -, -, -, -, hJb, hJK, hess,
    hnull, -⟩ := exists_embedded_solid_torus_meridian
  exact exists_normalSystem_of_essential_boundary_circle finrank_euclideanSpace_fin K hKfin hK
    hJ hJb hJK hnull hess

theorem nonempty_normalSystem_euclideanSpace_three :
    Nonempty (NormalSystem (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨S, -⟩ := exists_normalSystem_euclideanSpace_three
  exact ⟨S⟩

end DifferentialGeometry.Topology.PiecewiseLinear
