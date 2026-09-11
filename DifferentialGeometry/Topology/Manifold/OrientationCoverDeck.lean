import DifferentialGeometry.Topology.Manifold.OrientationCover
import DifferentialGeometry.Bundle.Orientation.Deck
import DifferentialGeometry.Topology.FiberBundle.Compact

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
attribute [local instance] DifferentialGeometry.VectorBundle.orientationTopology
local instance : DiscreteTopology (Orientation ℝ E (Fin n)) := ⟨rfl⟩


def tangentOrientationDeck (hdim : Module.finrank ℝ E = n) :
    tangentOrientationCover (M := M) hdim → tangentOrientationCover (M := M) hdim :=
  DifferentialGeometry.VectorBundle.orientationDeck (tangentBundleCore 𝓘(ℝ, E) M) hdim

theorem tangentOrientationDeck_involutive (hdim : Module.finrank ℝ E = n) :
    Function.Involutive (tangentOrientationDeck (M := M) hdim) :=
  DifferentialGeometry.VectorBundle.orientationDeck_involutive _ hdim

theorem tangentOrientationDeck_ne_self (hdim : Module.finrank ℝ E = n)
    (z : tangentOrientationCover (M := M) hdim) : tangentOrientationDeck hdim z ≠ z :=
  DifferentialGeometry.VectorBundle.orientationDeck_ne_self _ hdim z

theorem tangentOrientationDeck_projects (hdim : Module.finrank ℝ E = n)
    (z : tangentOrientationCover (M := M) hdim) :
    tangentOrientationProjection hdim (tangentOrientationDeck hdim z) =
      tangentOrientationProjection hdim z := rfl

theorem tangentOrientationDeck_ne_id [Nonempty M] (hdim : Module.finrank ℝ E = n) :
    tangentOrientationDeck (M := M) hdim ≠ id := by
  intro h
  let x : M := Classical.choice inferInstance
  let o := ((Module.finBasis ℝ E).reindex (finCongr hdim)).orientation
  exact tangentOrientationDeck_ne_self hdim (⟨x, o⟩ : tangentOrientationCover hdim)
    (congrFun h ⟨x, o⟩)

theorem tangentOrientationProjection_isLocalDiffeomorph (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (tangentOrientationProjection (M := M) hdim) :=
  covering_projection_isLocalDiffeomorph
    (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph 𝓘(ℝ, E)


theorem tangentOrientationDeck_contMDiff (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (tangentOrientationDeck (M := M) hdim) := by
  let := tangentOrientationChartedSpace (M := M) hdim
  intro z
  apply covering_lift_contMDiffAt
    (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph 𝓘(ℝ, E)
    (DifferentialGeometry.VectorBundle.orientationDeck_continuous (tangentBundleCore 𝓘(ℝ, E) M) hdim).continuousAt
  change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (tangentOrientationProjection hdim) z
  exact (covering_projection_contMDiff
    (tangentOrientationProjection_isCoveringMap hdim).isLocalHomeomorph 𝓘(ℝ, E)).contMDiffAt


def tangentOrientationDeckDiffeomorph (hdim : Module.finrank ℝ E = n) :
    letI := tangentOrientationChartedSpace (M := M) hdim
    tangentOrientationCover (M := M) hdim ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ tangentOrientationCover (M := M) hdim := by
  letI := tangentOrientationChartedSpace (M := M) hdim
  exact {
    toEquiv := {
      toFun := tangentOrientationDeck hdim
      invFun := tangentOrientationDeck hdim
      left_inv := tangentOrientationDeck_involutive hdim
      right_inv := tangentOrientationDeck_involutive hdim
    }
    contMDiff_toFun := tangentOrientationDeck_contMDiff hdim
    contMDiff_invFun := tangentOrientationDeck_contMDiff hdim
  }

theorem tangentOrientationCover_compactSpace [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = n) : CompactSpace (tangentOrientationCover (M := M) hdim) := by
  let : Fintype (Orientation ℝ E (Fin n)) := Fintype.ofEquiv Bool
    (DifferentialGeometry.VectorBundle.orientationEquivBool
      ((Module.finBasis ℝ E).reindex (finCongr hdim))).symm
  exact DifferentialGeometry.Topology.FiberBundle.compactSpace_totalSpace
    (DifferentialGeometry.VectorBundle.orientationCore (tangentBundleCore 𝓘(ℝ, E) M) hdim)

end DifferentialGeometry.Topology.Manifold
