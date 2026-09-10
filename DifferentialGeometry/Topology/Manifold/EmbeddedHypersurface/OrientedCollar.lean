import DifferentialGeometry.Topology.Manifold.Orientation.TopForm
import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.TopFormCollar

open Set Bundle DifferentialGeometry.Topology.Morse Poincare.Topology
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.EmbeddedHypersurface

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ S] [IsManifold J ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem nonempty_smoothTwoSidedCollar_of_orientations {e : S → M}
    (he : Manifold.IsSmoothEmbedding I J ∞ e) (hK : IsCompact (range e))
    (oS : ∀ s : S, _root_.Orientation ℝ (TangentSpace I s) (Fin m))
    (oM : ∀ y : M, _root_.Orientation ℝ (TangentSpace J y) (Fin (m + 1)))
    (hS : DifferentialGeometry.VectorBundle.IsCompatibleOrientation
      (F := MorseModel m) (TangentSpace I) oS)
    (hM : DifferentialGeometry.VectorBundle.IsCompatibleOrientation
      (F := MorseModel (m + 1)) (TangentSpace J) oM) :
    Nonempty (SmoothTwoSidedCollar I J e) := by
  let _ : T2Space S := he.isEmbedding.t2Space
  let _ : CompactSpace S := isCompact_univ_iff.mp
    (he.isEmbedding.isCompact_iff.mpr (by simpa using hK))
  obtain ⟨η, hη, hη0, _⟩ := Poincare.Manifold.Orientation.exists_continuous_tangentTopForm
    I (show Module.finrank ℝ (MorseModel m) = m by simp [MorseModel]) oS hS
  obtain ⟨Ω, hΩ, hΩ0, _⟩ := Poincare.Manifold.Orientation.exists_continuous_tangentTopForm
    J (show Module.finrank ℝ (MorseModel (m + 1)) = m + 1 by simp [MorseModel]) oM hM
  exact nonempty_smoothTwoSidedCollar_of_topForms I J he hK η Ω hη hΩ hη0
    (fun s => hΩ0 (e s))

end Poincare.Manifold.EmbeddedHypersurface
