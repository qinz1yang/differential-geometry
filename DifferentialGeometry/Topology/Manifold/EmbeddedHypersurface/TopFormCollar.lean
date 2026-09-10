import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.TopFormCoorientation
import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.Collar

open Set Bundle DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.EmbeddedHypersurface

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G)
  [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ S] [IsManifold J ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem nonempty_smoothTwoSidedCollar_of_topForms {e : S → M}
    (he : Manifold.IsSmoothEmbedding I J ∞ e) (hK : IsCompact (range e))
    (η : ∀ s : S, TangentSpace I s [⋀^Fin m]→L[ℝ] ℝ)
    (Ω : ∀ y : M, TangentSpace J y [⋀^Fin (m + 1)]→L[ℝ] ℝ)
    (hη : Continuous (fun s => TotalSpace.mk'
      (MorseModel m [⋀^Fin m]→L[ℝ] ℝ) s (η s)))
    (hΩ : Continuous (fun y => TotalSpace.mk'
      (MorseModel (m + 1) [⋀^Fin (m + 1)]→L[ℝ] ℝ) y (Ω y)))
    (hη0 : ∀ s, η s ≠ 0) (hΩ0 : ∀ s, Ω (e s) ≠ 0) :
    Nonempty (SmoothTwoSidedCollar I J e) := by
  let _ : T2Space S := he.isEmbedding.t2Space
  let _ : CompactSpace S := isCompact_univ_iff.mp
    (he.isEmbedding.isCompact_iff.mpr (by simpa using hK))
  obtain ⟨V, hV, _, htrans⟩ := exists_contMDiff_transverse_of_topForms I J he.isImmersion
    η Ω hη hΩ hη0 hΩ0
  exact nonempty_smoothTwoSidedCollar I J he hK V hV.continuous htrans

end DifferentialGeometry.Manifold.EmbeddedHypersurface
