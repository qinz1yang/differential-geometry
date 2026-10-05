import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPositionInDouble
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DescentStepOrientable
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Covering.OrientableExistence

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_polyhedralDisk_of_normalSystemDisk_of_orientable
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdisk : ∀ S : NormalSystem E, S.IsOrientableManifold →
      S.sourceComplex.space ∩ S.singularMap ⁻¹' S.boundaryComplex.space =
        frontier S.sourceComplex.space → Nonempty (NormalSystem.EmbeddedDisk S))
    (K : Geometry.SimplicialComplex ℝ E) (hKfin : Finite K.faces)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hor : IsOrientable 3 K)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (hsub : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ K.space)
    (γ : freeLoop (connectedComponentComplex (boundaryComplex 3 K) c).space)
    (hnull : ((⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
      C((connectedComponentComplex (boundaryComplex 3 K) c).space, K.space)).comp γ).Nullhomotopic)
    (hess : ¬ γ.Nullhomotopic) :
    ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ K.space ∧ Δ ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2 ∧
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
  have horS : S.IsOrientableManifold := S.isOrientableManifold_of_isSubdivision hK hsubdiv hor
  exact exists_polyhedralDisk_of_embeddedDisk K hK (Classical.choice (hdisk S horS hproper)) hSK
    (fun z hz => (hSB hz).1) β hβ hbase hNcomap

open Classical in
theorem loop_theorem
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hKfin : Finite K.faces)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hor : IsOrientable 3 K)
    (c : ConnectedComponents (boundaryComplex 3 K).space)
    (γ : freeLoop (connectedComponentComplex (boundaryComplex 3 K) c).space)
    (hnull : ((⟨Set.inclusion
      ((space_mono_of_faces_subset (restrict_faces_subset (boundaryComplex 3 K) _)).trans
        (boundaryComplex_space_subset 3 K)), continuous_inclusion _⟩ :
      C((connectedComponentComplex (boundaryComplex 3 K) c).space, K.space)).comp γ).Nullhomotopic)
    (hess : ¬ γ.Nullhomotopic) :
    ∃ (Δ : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ K.space ∧ Δ ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2 ∧
      ∃ hboundary : r '' stdSimplexBoundary 2 ⊆
          (connectedComponentComplex (boundaryComplex 3 K) c).space,
        ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
          C(r '' stdSimplexBoundary 2,
            (connectedComponentComplex (boundaryComplex 3 K) c).space)).Nullhomotopic := by
  let hsub : (connectedComponentComplex (boundaryComplex 3 K) c).space ⊆ K.space :=
    (space_mono_of_faces_subset (restrict_faces_subset (boundaryComplex 3 K) _)).trans
      (boundaryComplex_space_subset 3 K)
  apply exists_polyhedralDisk_of_normalSystemDisk_of_orientable ?_ K hKfin hK hor c hsub γ
    hnull hess
  intro S horS hproperS
  apply exists_embeddedDisk_of_stallings_induction_general_orientable_buffered
    (by
      intro F _ _ _ R hproper hbase horR hnot
      exact R.exists_orientable_doubleCoverReduction hproper hbase horR hnot)
    (by
      intro F _ _ _ M S T R horS hproperT hbaseT hbuffer hdisk
      obtain ⟨D⟩ := hdisk
      exact R.nonempty_embeddedDisk_of_buffered_normalization_of_descent
        (NormalSystem.exists_normal_singular_cell_in_double S)
        (NormalSystem.exists_descending_surgery_in_double S horS) hbuffer D)
    S horS hproperS

end DifferentialGeometry.Topology.PiecewiseLinear
