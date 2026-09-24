import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackSurfaceBounded
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSurfaceClassification

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance surfaceUpgradeSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance surfaceUpgradeTopology : TopologicalSpace F.M := F.topology
private local instance surfaceUpgradeCharted : ChartedSpace H F.M := F.charted
private local instance surfaceUpgradeSmooth : IsManifold I ∞ F.M := F.smooth

theorem KLim.surface_bounded_and_classified
    {kappa : ℝ} (hK : KLim kappa F) (hdim : Module.finrank ℝ E = 2) :
    (∃ C : ℝ, 0 < C ∧ PointedFlowScalarBounded (I := I) F C ∧
      PointedFlowRmNormSqBounded (I := I) F (C ^ 2)) ∧
    IsAncientKappaSolution kappa F ∧
    ∃ T : ℝ, 0 < T ∧ ∃ pi : SphereTwo → F.M,
      IsLocalDiffeomorph (𝓡 2) I ∞ pi ∧ IsCoveringMap pi ∧ Function.Surjective pi ∧
      (∀ t : ℝ, t ≤ 0 → ∀ (x : SphereTwo) (v w : TangentSpace (𝓡 2) x),
        (F.S.family.metric t).inner (pi x)
            (mfderiv (𝓡 2) I pi x v) (mfderiv (𝓡 2) I pi x w) =
          (2 * (T - t)) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w) ∧
      ((∃ d : SphereTwo ≃ₘ⟮𝓡 2, I⟯ F.M, ∀ x : SphereTwo, d x = pi x) ∨
        ∃ d : SphereAntipodalQuotient ≃ₘ⟮𝓡 2, I⟯ F.M,
          ∀ x : SphereTwo, d (SphereAntipodalQuotient.proj x) = pi x) ∧
      (∀ d : SphereTwo ≃ₜ SphereTwo, pi ∘ d = pi →
        d = Homeomorph.refl SphereTwo ∨ ∀ x : SphereTwo, d x = -x) ∧
      (Nonempty (SurfaceOrientation I F.M) →
        ∃ d : SphereTwo ≃ₘ⟮𝓡 2, I⟯ F.M, ∀ x : SphereTwo, d x = pi x) := by
  have hA : IsAncientKappaSolution kappa F := hK.surface_toIsAncientKappaSolution hdim
  exact ⟨hK.surface_exists_global_curvature_bound hdim, hA,
    ancientKappaSurface_two_dimensional_classification F hA hdim⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
