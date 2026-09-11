import DifferentialGeometry.Geometry.Comparison.Synge.Weinstein
import DifferentialGeometry.Geometry.Curvature.OrientationCover
import DifferentialGeometry.Topology.Manifold.OrientationCoverOriented
import DifferentialGeometry.Topology.Manifold.OrientationCoverComponents

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.VectorBundle
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

theorem synge_orientable_of_odd_dim {n : ℕ} (hdim : Module.finrank ℝ E = n)
    (hn : 3 ≤ n) (hodd : Odd n) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hsec : HasPositiveSectionalCurvature g) :
    ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin n),
      IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o := by
  by_contra hno
  let := tangentOrientationChartedSpace (M := M) hdim
  let := tangentOrientation_isManifold (M := M) hdim
  let := tangentOrientationCover_t2Space (M := M) hdim
  let := tangentOrientationCover_compactSpace (M := M) hdim
  let := tangentOrientationCover_connected_of_nonorientable hdim hno
  obtain ⟨z, hz⟩ := synge_weinstein_fixed_point hdim (by omega)
    (tangentOrientationMetric g hdim) (hsec.tangentOrientationMetric hdim)
    (tangentOrientationCanonical hdim) (tangentOrientationCanonical_compatible hdim)
    (tangentOrientationDeckDiffeomorph hdim) (tangentOrientationDeck_isometry g hdim)
    (Or.inr ⟨hodd, tangentOrientationDeck_reverses_canonical hdim⟩)
  exact tangentOrientationDeck_ne_self hdim z hz

theorem synge_orientable_three_dim (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hsec : HasPositiveSectionalCurvature g) :
    ∃ o : ∀ x : M, Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin 3),
      IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E)) o :=
  synge_orientable_of_odd_dim hdim le_rfl (by decide) g hsec

end DifferentialGeometry.Geometry
