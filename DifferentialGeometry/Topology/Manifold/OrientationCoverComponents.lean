import DifferentialGeometry.Topology.Manifold.OrientationCoverDeck
import DifferentialGeometry.Topology.Covering.DoubleCoverComponents
import DifferentialGeometry.Topology.Covering.SectionSplit
import DifferentialGeometry.Topology.FiberBundle.FiniteClosed
import DifferentialGeometry.Bundle.Orientation.CompatibleSection



noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [local instance] DifferentialGeometry.VectorBundle.orientationTopology


theorem tangentOrientation_fiber_cases (hdim : Module.finrank ℝ E = n)
    (x y : tangentOrientationCover (M := M) hdim)
    (h : tangentOrientationProjection hdim y = tangentOrientationProjection hdim x) :
    y = x ∨ y = tangentOrientationDeck hdim x := by
  rcases x with ⟨x, o⟩
  rcases y with ⟨y, q⟩
  change y = x at h
  subst y
  have hh := (q : Orientation ℝ E (Fin n)).eq_or_eq_neg o (by simpa using hdim.symm)
  rcases hh with hh | hh
  · exact Or.inl (congrArg (fun r => (⟨x, r⟩ : tangentOrientationCover hdim)) hh)
  · exact Or.inr (congrArg (fun r => (⟨x, r⟩ : tangentOrientationCover hdim)) hh)

theorem tangentOrientationProjection_isClosedMap (hdim : Module.finrank ℝ E = n) :
    IsClosedMap (tangentOrientationProjection (M := M) hdim) := by
  let : Fintype (Orientation ℝ E (Fin n)) := Fintype.ofEquiv Bool
    (DifferentialGeometry.VectorBundle.orientationEquivBool
      ((Module.finBasis ℝ E).reindex (finCongr hdim))).symm
  exact DifferentialGeometry.Topology.FiberBundle.isClosedMap_projection_of_finite
    (DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, E) M) hdim)

theorem exists_compatibleOrientation_of_orientationCover_not_connected
    [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = n)
    (hnot : ¬ ConnectedSpace (tangentOrientationCover (M := M) hdim)) :
    ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n),
      DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o := by
  let : Nonempty (tangentOrientationCover (M := M) hdim) :=
    ⟨⟨Classical.choice inferInstance, ((Module.finBasis ℝ E).reindex (finCongr hdim)).orientation⟩⟩
  obtain ⟨s, hs⟩ := DifferentialGeometry.Topology.Covering.exists_section_of_not_connected_double_cover
    (tangentOrientationProjection_isCoveringMap hdim) (tangentOrientationProjection_isClosedMap hdim)
    (tangentOrientationDeck hdim)
    (tangentOrientation_fiber_cases hdim) hnot
  exact ⟨fun x => (s x).snd, (tangentOrientation_section hdim s hs).2⟩

theorem tangentOrientationCover_connected_of_nonorientable
    [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = n)
    (hno : ¬ ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n),
      DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o) :
    ConnectedSpace (tangentOrientationCover (M := M) hdim) := by
  by_contra hn
  exact hno (exists_compatibleOrientation_of_orientationCover_not_connected hdim hn)

theorem tangentOrientationCover_not_connected_of_compatibleOrientation [Nonempty M]
    (hdim : Module.finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n))
    (ho : DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o) :
    ¬ ConnectedSpace (tangentOrientationCover (M := M) hdim) := by
  let s : C(M, tangentOrientationCover (M := M) hdim) :=
    ⟨fun x => ⟨x, o x⟩, DifferentialGeometry.VectorBundle.continuous_section_of_compatibleOrientation
      (tangentBundleCore 𝓘(ℝ, E) M) hdim o ho⟩
  exact DifferentialGeometry.Topology.Covering.not_connected_of_double_cover_section
    (tangentOrientationProjection_isCoveringMap hdim) (tangentOrientationDeck hdim)
    (DifferentialGeometry.VectorBundle.orientationDeck_continuous (tangentBundleCore 𝓘(ℝ, E) M) hdim)
    (tangentOrientationDeck_projects hdim) (tangentOrientationDeck_ne_self hdim)
    (tangentOrientation_fiber_cases hdim) s (fun _ => rfl)

theorem compatibleOrientation_iff_orientationCover_not_connected [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = n) :
    (∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n),
      DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o) ↔
      ¬ ConnectedSpace (tangentOrientationCover (M := M) hdim) :=
  ⟨fun ⟨o, ho⟩ => tangentOrientationCover_not_connected_of_compatibleOrientation hdim o ho,
    exists_compatibleOrientation_of_orientationCover_not_connected hdim⟩

end DifferentialGeometry.Topology.Manifold
