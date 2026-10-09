import DifferentialGeometry.Topology.Manifold.SphereDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

/-!
# Smooth recognition of the two-sphere for surfaces modelled on `Fin k → ℝ`

`Homeomorph.nonempty_diffeomorph_sphere` recognizes a smooth closed surface homeomorphic to `S²` as
diffeomorphic to `S²`, for surfaces modelled on the Euclidean plane `𝓡 2`.  Regular level sets in this
tree (`regularFiberChartedSpace`) are modelled on `Fin k → ℝ`.  Transporting the atlas along a linear
isomorphism `(Fin k → ℝ) ≃L EuclideanSpace ℝ (Fin 2)` (the tree's `chartedSpaceTransHomeomorph`) gives
the same recognition for such surfaces.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology DifferentialGeometry.Manifold

/-- **Smooth `S²` recognition, model `Fin k → ℝ`.** A smooth closed surface modelled on
`Fin 2 → ℝ` (written `Fin k → ℝ` with `k = 2`) that is homeomorphic to the two-sphere is
diffeomorphic to it. -/
theorem nonempty_diffeomorph_sphereTwo_of_homeomorph {k : ℕ} (hk : k = 2) {S : Type*}
    [TopologicalSpace S] [T2Space S] [ChartedSpace (Fin k → ℝ) S]
    [IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ S] (h : S ≃ₜ SphereTwo) :
    Nonempty (S ≃ₘ⟮𝓘(ℝ, Fin k → ℝ), 𝓡 2⟯ SphereTwo) := by
  have hdim : Module.finrank ℝ (Fin k → ℝ) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    simp [hk]
  let L : (Fin k → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) := ContinuousLinearEquiv.ofFinrankEq hdim
  have hcompat : ∀ y, (𝓡 2) (L.toHomeomorph y) = L (𝓘(ℝ, Fin k → ℝ) y) := fun _ => rfl
  let A : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S :=
    chartedSpaceTransHomeomorph (M := S) L.toHomeomorph
  have : IsManifold (𝓡 2) ∞ S :=
    isManifold_transHomeomorph 𝓘(ℝ, Fin k → ℝ) (𝓡 2) L.toHomeomorph L hcompat
  obtain ⟨D⟩ := Homeomorph.nonempty_diffeomorph_sphere h
  have hto : ContMDiff 𝓘(ℝ, Fin k → ℝ) (𝓡 2) ∞ D.symm :=
    (contMDiff_chartedSpaceTransHomeomorph_source_iff 𝓘(ℝ, Fin k → ℝ) (𝓡 2) L.toHomeomorph L
      hcompat (𝓡 2)).mp D.symm.contMDiff
  have hinv : ContMDiff (𝓡 2) 𝓘(ℝ, Fin k → ℝ) ∞ D :=
    (contMDiff_chartedSpaceTransHomeomorph_iff 𝓘(ℝ, Fin k → ℝ) (𝓡 2) L.toHomeomorph L hcompat
      (𝓡 2)).mp D.contMDiff
  exact ⟨{ toEquiv := D.toEquiv.symm
           contMDiff_toFun := hto
           contMDiff_invFun := hinv }⟩

end DifferentialGeometry.Topology.Surface
