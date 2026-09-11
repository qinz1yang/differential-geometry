import DifferentialGeometry.Topology.Manifold.OrientationCoverComponents
import DifferentialGeometry.Topology.Manifold.CoveringDiffeomorph



noncomputable section
open Set Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [ConnectedSpace M]

theorem tangentOrientationCover_two_components_diffeomorph
    (hdim : Module.finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n))
    (ho : DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    ∃ U V : TopologicalSpace.Opens (tangentOrientationCover (M := M) hdim),
      (U : Set (tangentOrientationCover (M := M) hdim)).Nonempty ∧ (V : Set (tangentOrientationCover (M := M) hdim)).Nonempty ∧
      Disjoint (U : Set (tangentOrientationCover (M := M) hdim)) (V : Set (tangentOrientationCover (M := M) hdim)) ∧ (U : Set (tangentOrientationCover (M := M) hdim)) ∪ (V : Set (tangentOrientationCover (M := M) hdim)) = univ ∧
      (∀ x ∈ U, connectedComponent x = (U : Set (tangentOrientationCover (M := M) hdim))) ∧
      (∀ x ∈ V, connectedComponent x = (V : Set (tangentOrientationCover (M := M) hdim))) ∧
      (∃ e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U M ∞,
        ∀ x : U, e x = tangentOrientationProjection hdim x) ∧
      (∃ e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) V M ∞,
        ∀ x : V, e x = tangentOrientationProjection hdim x) := by
  let := tangentOrientationChartedSpace (M := M) hdim
  let : Nonempty (tangentOrientationCover (M := M) hdim) :=
    ⟨⟨Classical.choice inferInstance, o (Classical.choice inferInstance)⟩⟩
  obtain ⟨K, hK, hne, hne', ⟨e, he⟩, ⟨e', he'⟩⟩ :=
    DifferentialGeometry.Topology.Covering.exists_two_projection_homeomorphs_of_not_connected
      (tangentOrientationProjection_isCoveringMap hdim)
      (tangentOrientationProjection_isClosedMap hdim) (tangentOrientationDeck hdim)
      (tangentOrientation_fiber_cases hdim)
      (tangentOrientationCover_not_connected_of_compatibleOrientation hdim o ho)
  have hconn : IsConnected K :=
    isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  have hconn' : IsConnected Kᶜ :=
    isConnected_iff_connectedSpace.mpr (e'.connectedSpace_iff.mpr inferInstance)
  let U : TopologicalSpace.Opens (tangentOrientationCover (M := M) hdim) := ⟨K, hK.isOpen⟩
  let V : TopologicalSpace.Opens (tangentOrientationCover (M := M) hdim) := ⟨Kᶜ, hK.compl.isOpen⟩
  refine ⟨U, V, hne, hne', disjoint_compl_right, union_compl_self K, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hK.connectedComponent_subset hx).antisymm (hconn.subset_connectedComponent hx)
  · intro x hx
    exact (hK.compl.connectedComponent_subset hx).antisymm (hconn'.subset_connectedComponent hx)
  · exact ⟨coveringProjectionDiffeomorph
      (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph 𝓘(ℝ, E) U e he,
      fun x => he x⟩
  · exact ⟨coveringProjectionDiffeomorph
      (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph 𝓘(ℝ, E) V e' he',
      fun x => he' x⟩

omit [ConnectedSpace M] in
theorem compatibleOrientation_of_component_diffeomorph
    (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    ∀ (U : TopologicalSpace.Opens (tangentOrientationCover (M := M) hdim))
      (e : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U M ∞),
      (∀ x : U, e x = tangentOrientationProjection hdim x) →
      ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n),
        DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o := by
  let := tangentOrientationChartedSpace (M := M) hdim
  intro U e he
  let s : C(M, tangentOrientationCover (M := M) hdim) :=
    ⟨fun x => (e.symm x : _), continuous_subtype_val.comp e.symm.continuous⟩
  have hs : Function.RightInverse s (tangentOrientationProjection hdim) := fun x =>
    (he (e.symm x)).symm.trans (e.apply_symm_apply x)
  exact ⟨fun x => (s x).snd, (tangentOrientation_section hdim s hs).2⟩

end DifferentialGeometry.Topology.Manifold
